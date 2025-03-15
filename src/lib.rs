//! Bit-keyed collections
//!
//! #   Organization
//!
//! This crate is composed of multiple top modules:
//!
//! -   The `api` top module contains a selection of vocabulary types and traits.
//! -   The `algorithm` module contains a selection of algorithms built atop this API.
//! -   The `collections` module contains a selection of implementations of bit-keyed collections.
//! -   The `utils` module contains a selection of low-level types upon which the implementations, and algorithms, are
//!     built.
//!
//!
//! #   Key type
//!
//! Bit-keyed collections are keyed by an index, expressed as a `u64`.
//!
//! #### Why not `usize`?
//!
//! While `usize` is the typical index type, it comes with several disadvantages:
//!
//! -   It is only sufficient to index every _byte_ in a program, but not necessarily every _bit_. For example, on a
//!     16-bits platform, `usize` is 16-bits, and can therefore only index 64K elements, while 128K bits only occupy
//!     16 KB of memory.
//! -   It is awkward to convert to/from. For example, it doesn't offer a `From<u32>` implementation, precisely because
//!     such an implementation doesn't exist on 16-bits platforms.
//!
//! #### Why not a platform specific type?
//!
//! While a `u16` would be sufficient on an 8-bits platform, and a `u32` sufficient on a 16-bits platform, using a
//! platform-dependent type comes at a portability cost: code which compiles on one platform where the key is a `u64`
//! unintendedly depend on it being `u64`, and not compile on a platform where the key is a `u32`.
//!
//!
//! #### Why not a generic type?
//!
//! A generic type introduces clutter, blood and tears. Clutter in that _everything_ would suddenly need to be generic,
//! and blood and tears in that a dedicated trait would be required.
//!
//!
//! #### Why `u64`?
//!
//! `u64` is necessary for 32-bits & 64-bits platforms, and doesn't suffer from any of the downsides above.
//!
//! It does mean that on an 8-bits or 16-bits platform the type is larger than necessary, and may not be supported. This
//! an unfortunate trade-off, but one this author is willing to make.

#![cfg_attr(not(test), no_std)]
//  Features (language)
//  Features (library)
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]
//  Lints
#![deny(missing_docs)]
//  This author prefers to keep its test modules close to what they are testing.
#![allow(clippy::items_after_test_module)]

#[cfg(feature = "alloc")]
extern crate alloc;

//pub mod api;
//pub mod collections;
pub mod utils;

//  TODO: complete collections, then introduce algorithms.
