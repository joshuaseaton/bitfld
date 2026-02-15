#!/usr/bin/env nu

# Copyright (c) 2026 Joshua Seaton
#
# Use of this source code is governed by a MIT-style
# license that can be found in the LICENSE file or at
# https://opensource.org/licenses/MIT#

cargo test

# Compilation-time tests for usize layouts.
cargo check --test usize-comptime-tests --target i686-unknown-linux-gnu

# Make sure examples compile too.
cargo run --example basic
cargo run --example bitfield-repr
