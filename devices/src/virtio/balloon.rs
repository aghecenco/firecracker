// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

use std;
use std::cmp;
use std::io::{self, Write};
use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use memory_model::{GuestAddress, GuestMemory};
use sys_util::EventFd;
use virtio_gen::VIRTIO_F_VERSION_1;

use super::super::{DeviceEventT, EpollHandler, EpollHandlerPayload, Error as DeviceError};
use super::{
    ActivateError, ActivateResult, DescriptorChain, Queue, VirtioDevice, TYPE_BALLOON,
    VIRTIO_MMIO_INT_CONFIG, VIRTIO_MMIO_INT_VRING,
};

#[derive(Debug)]
pub enum BalloonError {
    /// Request to adjust memory size can't provide the number of pages requested.
    NotEnoughPages,
    /// Failure writing the config notification event.
    WritingConfigEvent(io::Error),
}
pub type Result<T> = std::result::Result<T, BalloonError>;

// Balloon has three virt IO queues: Inflate, Deflate, and Stats.
// Stats is currently not used.
const QUEUE_SIZE: u16 = 128;
const QUEUE_SIZES: &[u16] = &[QUEUE_SIZE, QUEUE_SIZE];

const VIRTIO_BALLOON_PFN_SHIFT: u32 = 12;

// The feature bitmap for virtio balloon
const VIRTIO_BALLOON_F_MUST_TELL_HOST: u32 = 0; // Tell before reclaiming pages
const VIRTIO_BALLOON_F_DEFLATE_ON_OOM: u32 = 2; // Deflate balloon on OOM

const INFLATE_QUEUE_EVENT: DeviceEventT = 0;
const DEFLATE_QUEUE_EVENT: DeviceEventT = 0;

// BalloonConfig is modified by the worker and read from the device thread.
#[derive(Default)]
struct BalloonConfig {
    num_pages: AtomicUsize,
    actual_pages: AtomicUsize,
}

fn valid_inflate_desc(desc: &DescriptorChain) -> bool {
    !desc.is_write_only() && desc.len % 4 == 0
}

enum Operation {
    Deflate,
    Inflate,
}

pub struct EpollConfig {
    inflate_queue_token: u64,
    deflate_queue_token: u64,
    epoll_raw_fd: RawFd,
    sender: mpsc::Sender<Box<EpollHandler>>,
}

impl EpollConfig {
    pub fn new(
        first_token: u64,
        epoll_raw_fd: RawFd,
        sender: mpsc::Sender<Box<EpollHandler>>,
    ) -> Self {
        EpollConfig {
            inflate_queue_token: first_token + INFLATE_QUEUE_EVENT as u64,
            deflate_queue_token: first_token + DEFLATE_QUEUE_EVENT as u64,
            epoll_raw_fd,
            sender,
        }
    }
}
struct InflateDeflate {
    queue: Queue,
    queue_evt: EventFd,
}

impl InflateDeflate {
    fn new(queue: Queue, queue_evt: EventFd) -> Self {
        InflateDeflate { queue, queue_evt }
    }
}

struct BalloonEpollHandler {
    deflate: InflateDeflate,
    inflate: InflateDeflate,
    interrupt_evt: EventFd,
    interrupt_status: Arc<AtomicUsize>,
    mem: GuestMemory,
}

impl BalloonEpollHandler {
    fn process_inflate_deflate(&mut self, inflate: bool) -> bool {
        let queue = if inflate {
            &mut self.inflate.queue
        } else {
            &mut self.deflate.queue
        };

        let mut used_desc_heads = [0; QUEUE_SIZE as usize];
        let mut used_count = 0;
        for avail_desc in queue.iter(&self.mem) {
            if inflate && valid_inflate_desc(&avail_desc) {
                let num_addrs = avail_desc.len / 4;
                for i in 0..num_addrs as usize {
                    let addr = match avail_desc.addr.checked_add(i * 4) {
                        Some(a) => a,
                        None => break,
                    };
                    let guest_input: u32 = match self.mem.read_obj_from_addr(addr) {
                        Ok(a) => a,
                        Err(_) => continue,
                    };
                    let guest_address =
                        GuestAddress((guest_input as usize) << VIRTIO_BALLOON_PFN_SHIFT);

                    if self
                        .mem
                        .remove_range(guest_address, 1 << VIRTIO_BALLOON_PFN_SHIFT)
                        .is_err()
                    {
                        warn!("Marking pages unused failed {:?}", guest_address);
                        continue;
                    }
                }
            }

            used_desc_heads[used_count] = avail_desc.index;
            used_count += 1;
        }

        for &desc_index in &used_desc_heads[..used_count] {
            queue.add_used(&self.mem, desc_index, 0);
        }
        used_count > 0
    }

    fn signal_used_queue(&self) {
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
        if let Err(e) = self.interrupt_evt.write(1) {
            error!("Failed to signal used queue: {:?}", e);
        }
    }

    fn signal_config_changed(&self) {
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_CONFIG as usize, Ordering::SeqCst);
        if let Err(e) = self.interrupt_evt.write(1) {
            error!("Failed to signal config change: {:?}", e);
        }
    }

    pub fn inflate_deflate(&mut self, op: Operation) {
        let mut needs_interrupt = false;
        match op {
            Operation::Inflate => {
                if let Err(e) = self.inflate.queue_evt.read() {
                    error!("failed reading inflate queue EventFd: {:?}", e);
                }
                needs_interrupt |= self.process_inflate_deflate(true);
            }
            Operation::Deflate => {
                if let Err(e) = self.deflate.queue_evt.read() {
                    error!("failed reading deflate queue EventFd: {:?}", e);
                }
                needs_interrupt |= self.process_inflate_deflate(false);
            }
        }
        if needs_interrupt {
            self.signal_used_queue();
        }
    }
}

impl EpollHandler for BalloonEpollHandler {
    fn handle_event(
        &mut self,
        device_event: DeviceEventT,
        _: u32,
        _: EpollHandlerPayload,
    ) -> std::result::Result<(), DeviceError> {
        match device_event {
            INFLATE_QUEUE_EVENT => {
                self.process_inflate_deflate(true);
            }
            DEFLATE_QUEUE_EVENT => {
                self.process_inflate_deflate(false);
            }
            _ => panic!("Unknown event type was received."),
        }

        // TODO propagate result
        Ok(())
    }
}

/// Virtio device for memory balloon inflation/deflation.
pub struct Balloon {
    avail_features: u64,
    config: Arc<BalloonConfig>,
    epoll_config: EpollConfig,
    features: u64,
}

impl Balloon {
    /// Create a new virtio balloon device.
    pub fn new(epoll_config: EpollConfig) -> Self {
        Balloon {
            avail_features: 1 << VIRTIO_BALLOON_F_MUST_TELL_HOST
                | 1 << VIRTIO_BALLOON_F_DEFLATE_ON_OOM
                | 1 << VIRTIO_F_VERSION_1 as u64,
            config: Arc::new(BalloonConfig {
                num_pages: AtomicUsize::new(0),
                actual_pages: AtomicUsize::new(0),
            }),
            epoll_config,
            features: 1 << VIRTIO_BALLOON_F_MUST_TELL_HOST
                | 1 << VIRTIO_BALLOON_F_DEFLATE_ON_OOM as u64,
        }
    }
}

impl VirtioDevice for Balloon {
    fn device_type(&self) -> u32 {
        TYPE_BALLOON
    }

    fn queue_max_sizes(&self) -> &[u16] {
        QUEUE_SIZES
    }

    fn read_config(&self, offset: u64, mut data: &mut [u8]) {
        if offset >= 8 {
            return;
        }
        let num_pages = self.config.num_pages.load(Ordering::Relaxed) as u32;
        let actual_pages = self.config.actual_pages.load(Ordering::Relaxed) as u32;
        let mut config = [0u8; 8];
        // These writes can't fail as they fit in the declared array so unwrap is fine.
        (&mut config[0..])
            .write_u32::<LittleEndian>(num_pages)
            .unwrap();
        (&mut config[4..])
            .write_u32::<LittleEndian>(actual_pages)
            .unwrap();
        if let Some(end) = offset.checked_add(data.len() as u64) {
            // This write can't fail, offset and end are checked against the length of config.
            data.write_all(&config[offset as usize..cmp::min(end, 8) as usize])
                .unwrap();
        }
    }

    fn write_config(&mut self, offset: u64, mut data: &[u8]) {
        // Only allow writing to `actual` pages from the guest.
        if offset != 4 || data.len() != 4 {
            return;
        }
        // This read can't fail as it fits in the declared array so unwrap is fine.
        let new_actual: u32 = data.read_u32::<LittleEndian>().unwrap();
        self.config
            .actual_pages
            .store(new_actual as usize, Ordering::Relaxed);
    }

    fn features(&self, page: u32) -> u32 {
        match page {
            // Get the lower 32-bits of the features bitfield.
            0 => self.avail_features as u32,
            // Get the upper 32-bits of the features bitfield.
            1 => (self.avail_features >> 32) as u32,
            _ => {
                warn!("Received request for unknown features page.");
                0u32
            }
        }
    }

    fn ack_features(&mut self, page: u32, value: u32) {
        let mut v = match page {
            0 => value as u64,
            1 => (value as u64) << 32,
            _ => {
                warn!("Cannot acknowledge unknown features page.");
                0u64
            }
        };

        // Check if the guest is ACK'ing a feature that we didn't claim to have.
        let unrequested_features = v & !self.avail_features;
        if unrequested_features != 0 {
            warn!("Received acknowledge request for unknown feature.");

            // Don't count these features as acked.
            v &= !unrequested_features;
        }
        self.features |= v;
    }

    fn activate(
        &mut self,
        mem: GuestMemory,
        interrupt_evt: EventFd,
        status: Arc<AtomicUsize>,
        mut queues: Vec<Queue>,
        mut queue_evts: Vec<EventFd>,
    ) -> ActivateResult {
        if queues.len() != QUEUE_SIZES.len() || queue_evts.len() != QUEUE_SIZES.len() {
            return Err(ActivateError::BadActivate);
        }

        let inflate_queue = queues.remove(0);
        let deflate_queue = queues.remove(0);

        let inflate_queue_evt = queue_evts.remove(0);
        let deflate_queue_evt = queue_evts.remove(0);

        let handler = BalloonEpollHandler {
            deflate: InflateDeflate::new(deflate_queue, deflate_queue_evt),
            inflate: InflateDeflate::new(inflate_queue, inflate_queue_evt),
            interrupt_evt,
            interrupt_status: status,
            mem,
        };

        let inflate_evt_raw_fd = handler.inflate.queue_evt.as_raw_fd();
        let deflate_evt_raw_fd = handler.deflate.queue_evt.as_raw_fd();

        self.epoll_config
            .sender
            .send(Box::new(handler))
            .expect("Failed to send through the channel");

        epoll::ctl(
            self.epoll_config.epoll_raw_fd,
            epoll::ControlOptions::EPOLL_CTL_ADD,
            inflate_evt_raw_fd,
            epoll::Event::new(
                epoll::Events::EPOLLIN,
                self.epoll_config.inflate_queue_token,
            ),
        )
        .map_err(|e| {
            //                METRICS.net.activate_fails.inc();
            ActivateError::EpollCtl(e)
        })?;

        epoll::ctl(
            self.epoll_config.epoll_raw_fd,
            epoll::ControlOptions::EPOLL_CTL_ADD,
            deflate_evt_raw_fd,
            epoll::Event::new(
                epoll::Events::EPOLLIN,
                self.epoll_config.deflate_queue_token,
            ),
        )
        .map_err(|e| {
            //                METRICS.net.activate_fails.inc();
            ActivateError::EpollCtl(e)
        })?;

        Ok(())
    }
}
