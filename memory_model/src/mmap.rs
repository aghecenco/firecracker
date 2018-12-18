// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! The mmap module provides a safe interface to mmap memory and ensures unmap is called when the
//! mmap object leaves scope.

use std;
use std::io::{self, Read, Write};
use std::ptr::null_mut;

use libc;

use DataInit;

/// Errors associated with memory mapping.
#[derive(Debug)]
pub enum Error {
    /// Requested memory out of range.
    InvalidAddress,
    /// Requested memory range spans past the end of the region.
    InvalidRange(usize, usize),
    /// Couldn't read from the given source.
    ReadFromSource(io::Error),
    /// `mmap` returned the given error.
    SystemCallFailed(io::Error),
    /// Writing to memory failed
    WriteToMemory(io::Error),
    /// Reading from memory failed
    ReadFromMemory(io::Error),
}
type Result<T> = std::result::Result<T, Error>;

/// Wraps an anonymous shared memory mapping in the current process.
pub struct MemoryMapping {
    addr: *mut u8,
    size: usize,
}

// Send and Sync aren't automatically inherited for the raw address pointer.
// Accessing that pointer is only done through the stateless interface which
// allows the object to be shared by multiple threads without a decrease in
// safety.
unsafe impl Send for MemoryMapping {}
unsafe impl Sync for MemoryMapping {}

impl MemoryMapping {
    /// Creates an anonymous shared mapping of `size` bytes.
    ///
    /// # Arguments
    /// * `size` - Size of memory region in bytes.
    pub fn new(size: usize) -> Result<MemoryMapping> {
        // This is safe because we are creating an anonymous mapping in a place not already used by
        // any other area in this process.
        let addr = unsafe {
            libc::mmap(
                null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_ANONYMOUS | libc::MAP_SHARED | libc::MAP_NORESERVE,
                -1,
                0,
            )
        };
        if addr == libc::MAP_FAILED {
            return Err(Error::SystemCallFailed(io::Error::last_os_error()));
        }
        Ok(MemoryMapping {
            addr: addr as *mut u8,
            size,
        })
    }

    /// Returns a pointer to the beginning of the memory region.  Should only be
    /// used for passing this region to ioctls for setting guest memory.
    pub fn as_ptr(&self) -> *mut u8 {
        self.addr
    }

    /// Returns the size of the memory region in bytes.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Writes a slice to the memory region at the specified offset.
    /// Returns the number of bytes written.  The number of bytes written can
    /// be less than the length of the slice if there isn't enough room in the
    /// memory region.
    ///
    /// # Examples
    /// * Write a slice at offset 256.
    ///
    /// ```
    /// #   use memory_model::MemoryMapping;
    /// #   let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///     let res = mem_map.write_slice(&[1,2,3,4,5], 256);
    ///     assert!(res.is_ok());
    ///     assert_eq!(res.unwrap(), 5);
    /// ```
    pub fn write_slice(&self, buf: &[u8], offset: usize) -> Result<usize> {
        if offset >= self.size {
            return Err(Error::InvalidAddress);
        }
        unsafe {
            // Guest memory can't strictly be modeled as a slice because it is
            // volatile.  Writing to it with what compiles down to a memcpy
            // won't hurt anything as long as we get the bounds checks right.
            let mut slice: &mut [u8] = &mut self.as_mut_slice()[offset..];
            Ok(slice.write(buf).map_err(Error::WriteToMemory)?)
        }
    }

    /// Reads to a slice from the memory region at the specified offset.
    /// Returns the number of bytes read.  The number of bytes read can
    /// be less than the length of the slice if there isn't enough room in the
    /// memory region.
    ///
    /// # Examples
    /// * Read a slice of size 16 at offset 256.
    ///
    /// ```
    /// #   use memory_model::MemoryMapping;
    /// #   let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///     let buf = &mut [0u8; 16];
    ///     let res = mem_map.read_slice(buf, 256);
    ///     assert!(res.is_ok());
    ///     assert_eq!(res.unwrap(), 16);
    /// ```
    pub fn read_slice(&self, mut buf: &mut [u8], offset: usize) -> Result<usize> {
        if offset >= self.size {
            return Err(Error::InvalidAddress);
        }
        unsafe {
            // Guest memory can't strictly be modeled as a slice because it is
            // volatile.  Writing to it with what compiles down to a memcpy
            // won't hurt anything as long as we get the bounds checks right.
            let slice: &[u8] = &self.as_slice()[offset..];
            Ok(buf.write(slice).map_err(Error::ReadFromMemory)?)
        }
    }

    /// Writes an object to the memory region at the specified offset.
    /// Returns Ok(()) if the object fits, or Err if it extends past the end.
    ///
    /// # Examples
    /// * Write a u64 at offset 16.
    ///
    /// ```
    /// #   use memory_model::MemoryMapping;
    /// #   let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///     let res = mem_map.write_obj(55u64, 16);
    ///     assert!(res.is_ok());
    /// ```
    pub fn write_obj<T: DataInit>(&self, val: T, offset: usize) -> Result<()> {
        unsafe {
            // Guest memory can't strictly be modeled as a slice because it is
            // volatile.  Writing to it with what compiles down to a memcpy
            // won't hurt anything as long as we get the bounds checks right.
            let (end, fail) = offset.overflowing_add(std::mem::size_of::<T>());
            if fail || end > self.size() {
                return Err(Error::InvalidAddress);
            }
            std::ptr::write_volatile(&mut self.as_mut_slice()[offset..] as *mut _ as *mut T, val);
            Ok(())
        }
    }

    /// Reads on object from the memory region at the given offset.
    /// Reading from a volatile area isn't strictly safe as it could change
    /// mid-read.  However, as long as the type T is plain old data and can
    /// handle random initialization, everything will be OK.
    ///
    /// # Examples
    /// * Read a u64 written to offset 32.
    ///
    /// ```
    /// #   use memory_model::MemoryMapping;
    /// #   let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///     let res = mem_map.write_obj(55u64, 32);
    ///     assert!(res.is_ok());
    ///     let num: u64 = mem_map.read_obj(32).unwrap();
    ///     assert_eq!(55, num);
    /// ```
    pub fn read_obj<T: DataInit>(&self, offset: usize) -> Result<T> {
        let (end, fail) = offset.overflowing_add(std::mem::size_of::<T>());
        if fail || end > self.size() {
            return Err(Error::InvalidAddress);
        }
        unsafe {
            // This is safe because by definition Copy types can have their bits
            // set arbitrarily and still be valid.
            Ok(std::ptr::read_volatile(
                &self.as_slice()[offset..] as *const _ as *const T,
            ))
        }
    }

    /// Reads data from a readable object like a File and writes it to guest memory.
    ///
    /// # Arguments
    /// * `mem_offset` - Begin writing memory at this offset.
    /// * `src` - Read from `src` to memory.
    /// * `count` - Read `count` bytes from `src` to memory.
    ///
    /// # Examples
    ///
    /// * Read bytes from /dev/urandom
    ///
    /// ```
    /// # use memory_model::MemoryMapping;
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # fn test_read_random() -> Result<u32, ()> {
    /// #     let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///       let mut file = File::open(Path::new("/dev/urandom")).map_err(|_| ())?;
    ///       mem_map.read_to_memory(32, &mut file, 128).map_err(|_| ())?;
    ///       let rand_val: u32 =  mem_map.read_obj(40).map_err(|_| ())?;
    /// #     Ok(rand_val)
    /// # }
    /// ```
    pub fn read_to_memory<F>(&self, mem_offset: usize, src: &mut F, count: usize) -> Result<()>
    where
        F: Read,
    {
        let (mem_end, fail) = mem_offset.overflowing_add(count);
        if fail || mem_end > self.size() {
            return Err(Error::InvalidRange(mem_offset, count));
        }
        unsafe {
            // It is safe to overwrite the volatile memory. Accessing the guest
            // memory as a mutable slice is OK because nothing assumes another
            // thread won't change what is loaded.
            let dst = &mut self.as_mut_slice()[mem_offset..mem_end];
            src.read_exact(dst).map_err(Error::ReadFromSource)?;
        }
        Ok(())
    }

    /// Writes data from memory to a writable object.
    ///
    /// # Arguments
    /// * `mem_offset` - Begin reading memory from this offset.
    /// * `dst` - Write from memory to `dst`.
    /// * `count` - Read `count` bytes from memory to `src`.
    ///
    /// # Examples
    ///
    /// * Write 128 bytes to /dev/null
    ///
    /// ```
    /// # use memory_model::MemoryMapping;
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # fn test_write_null() -> Result<(), ()> {
    /// #     let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///       let mut file = File::open(Path::new("/dev/null")).map_err(|_| ())?;
    ///       mem_map.write_from_memory(32, &mut file, 128).map_err(|_| ())?;
    /// #     Ok(())
    /// # }
    /// ```
    pub fn write_from_memory<F>(&self, mem_offset: usize, dst: &mut F, count: usize) -> Result<()>
    where
        F: Write,
    {
        let (mem_end, fail) = mem_offset.overflowing_add(count);
        if fail || mem_end > self.size() {
            return Err(Error::InvalidRange(mem_offset, count));
        }
        unsafe {
            // It is safe to read from volatile memory. Accessing the guest
            // memory as a slice is OK because nothing assumes another thread
            // won't change what is loaded.
            let src = &self.as_mut_slice()[mem_offset..mem_end];
            dst.write_all(src).map_err(Error::ReadFromSource)?;
        }
        Ok(())
    }

    /// Uses `madvise` to tell the kernel to remove the specified range.
    ///
    /// Subsequent reads to the pages in the range will return zero bytes.
    ///
    /// # Arguments
    ///
    /// * `mem_offset` - Remove from this offset.
    /// * `count` - Number of bytes to remove.
    ///
    /// # Examples
    ///
    /// * Clear 128 bytes from the 1024 allocated.
    ///
    /// ```
    /// # use memory_model::MemoryMapping;
    /// # fn test_remove_range() -> Result<(), ()> {
    /// #     let mut mem_map = MemoryMapping::new(1024).unwrap();
    ///       mem_map.remove_range(0, 128).map_err(|_| ())?;
    /// #     Ok(())
    /// # }
    /// ```
    pub fn remove_range(&self, mem_offset: usize, count: usize) -> Result<()> {
        self.range_end(mem_offset, count)
            .map_err(|_| Error::InvalidRange(mem_offset, count))?;
        let ret = unsafe {
            // `madvise`-ing away the region is the same as the guest changing it.
            // Next time it is read, it may return zero pages.
            libc::madvise(
                (self.addr as usize + mem_offset) as *mut _,
                count,
                libc::MADV_REMOVE,
            )
        };
        if ret < 0 {
            Err(Error::InvalidRange(mem_offset, count))
        } else {
            Ok(())
        }
    }

    /// Check that `offset` + `count` is valid and return the sum.
    fn range_end(&self, offset: usize, count: usize) -> Result<usize> {
        let mem_end = offset.checked_add(count).ok_or(Error::InvalidAddress)?;
        if mem_end > self.size() {
            return Err(Error::InvalidAddress);
        }
        Ok(mem_end)
    }

    unsafe fn as_slice(&self) -> &[u8] {
        // This is safe because we mapped the area at addr ourselves, so this slice will not
        // overflow. However, it is possible to alias.
        std::slice::from_raw_parts(self.addr, self.size)
    }

    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut_slice(&self) -> &mut [u8] {
        // This is safe because we mapped the area at addr ourselves, so this slice will not
        // overflow. However, it is possible to alias.
        std::slice::from_raw_parts_mut(self.addr, self.size)
    }
}

impl Drop for MemoryMapping {
    fn drop(&mut self) {
        // This is safe because we mmap the area at addr ourselves, and nobody
        // else is holding a reference to it.
        unsafe {
            libc::munmap(self.addr as *mut libc::c_void, self.size);
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate tempfile;

    use self::tempfile::tempfile;

    use super::*;

    use std::fs::File;
    use std::mem;
    use std::path::Path;

    #[test]
    fn basic_map() {
        let m = MemoryMapping::new(1024).unwrap();
        assert_eq!(1024, m.size());
    }

    #[test]
    fn map_invalid_size() {
        let res = MemoryMapping::new(0);
        match res {
            Ok(_) => panic!("should panic!"),
            Err(err) => {
                if let Error::SystemCallFailed(e) = err {
                    assert_eq!(e.raw_os_error(), Some(libc::EINVAL));
                } else {
                    panic!("unexpected error: {:?}", err);
                }
            }
        }
    }

    #[test]
    fn test_write_past_end() {
        let m = MemoryMapping::new(5).unwrap();
        let res = m.write_slice(&[1, 2, 3, 4, 5, 6], 0);
        assert!(res.is_ok());
        assert_eq!(res.unwrap(), 5);
    }

    #[test]
    fn slice_read_and_write() {
        let mem_map = MemoryMapping::new(5).unwrap();
        let sample_buf = [1, 2, 3];
        assert!(mem_map.write_slice(&sample_buf, 5).is_err());
        assert!(mem_map.write_slice(&sample_buf, 2).is_ok());
        let mut buf = [0u8; 3];
        assert!(mem_map.read_slice(&mut buf, 5).is_err());
        assert!(mem_map.read_slice(&mut buf, 2).is_ok());
        assert_eq!(buf, sample_buf);
    }

    #[test]
    fn obj_read_and_write() {
        let mem_map = MemoryMapping::new(5).unwrap();
        assert!(mem_map.write_obj(55u16, 4).is_err());
        assert!(mem_map.write_obj(55u16, core::usize::MAX).is_err());
        assert!(mem_map.write_obj(55u16, 2).is_ok());
        assert_eq!(mem_map.read_obj::<u16>(2).unwrap(), 55u16);
        assert!(mem_map.read_obj::<u16>(4).is_err());
        assert!(mem_map.read_obj::<u16>(core::usize::MAX).is_err());
    }

    #[test]
    fn mem_read_and_write() {
        let mem_map = MemoryMapping::new(5).unwrap();
        assert!(mem_map.write_obj(!0u32, 1).is_ok());
        let mut file = File::open(Path::new("/dev/zero")).unwrap();
        assert!(mem_map
            .read_to_memory(2, &mut file, mem::size_of::<u32>())
            .is_err());
        assert!(mem_map
            .read_to_memory(core::usize::MAX, &mut file, mem::size_of::<u32>())
            .is_err());

        assert!(mem_map
            .read_to_memory(1, &mut file, mem::size_of::<u32>())
            .is_ok());

        let mut f = tempfile().unwrap();
        assert!(mem_map
            .read_to_memory(1, &mut f, mem::size_of::<u32>())
            .is_err());
        format!(
            "{:?}",
            mem_map.read_to_memory(1, &mut f, mem::size_of::<u32>())
        );

        assert_eq!(mem_map.read_obj::<u32>(1).unwrap(), 0);

        let mut sink = Vec::new();
        assert!(mem_map
            .write_from_memory(1, &mut sink, mem::size_of::<u32>())
            .is_ok());
        assert!(mem_map
            .write_from_memory(2, &mut sink, mem::size_of::<u32>())
            .is_err());
        assert!(mem_map
            .write_from_memory(core::usize::MAX, &mut sink, mem::size_of::<u32>())
            .is_err());
        format!(
            "{:?}",
            mem_map.write_from_memory(2, &mut sink, mem::size_of::<u32>())
        );
        assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
    }

    #[test]
    fn mapped_file_read() {
        let mut f = tempfile().unwrap();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert!(f.write_all(sample_buf).is_ok());

        let mem_map = MemoryMapping::from_fd(&f, sample_buf.len()).unwrap();
        let buf = &mut [0u8; 16];
        assert_eq!(mem_map.read_slice(buf, 0).unwrap(), sample_buf.len());
        assert_eq!(buf[0..sample_buf.len()], sample_buf[..]);
    }

    #[test]
    fn test_remove_range() {
        let mem_map = MemoryMapping::new(10).unwrap();

        assert_eq!(
            format!("{:?}", mem_map.remove_range(1, 1)),
            "Err(InvalidRange(1, 1))"
        );
        assert_eq!(
            format!("{:?}", mem_map.remove_range(0, 11)),
            "Err(InvalidRange(0, 11))"
        );

        // Write 42 at offset 0. Assert that reading from offset 0 yields 42.
        assert!(mem_map.write_obj(42u32, 0).is_ok());
        assert_eq!(mem_map.read_obj::<u32>(0).unwrap(), 42);

        // Madvise 4 bytes at offset 0.
        assert!(mem_map.remove_range(0, 4).is_ok());

        // Reading from offset 0 succeeds and yields 0.
        assert_eq!(mem_map.read_obj::<u32>(0).unwrap(), 0);
    }
}
