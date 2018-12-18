// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

#![allow(clippy::all)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub mod virtio_blk;
pub mod virtio_net;
pub mod virtio_ring;

// HACK! This shouldn't go here but I want to compile this thing now
pub const VIRTIO_F_VERSION_1: ::std::os::raw::c_uint = 32;
