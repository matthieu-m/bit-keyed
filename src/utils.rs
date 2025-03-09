//! Utilities for implementers of bit-keyed collections.

#[cfg(feature = "alloc")]
mod allocator;
mod chunk;
mod chunk_store;
mod error;

pub use chunk::{BitChunk, IndexInChunk, IndexOfChunk};
pub use chunk_store::{BitChunkStore, BitChunkView, TrustedBitChunkStore};
pub use error::BitStoreError;

#[cfg(feature = "alloc")]
pub use chunk_store::dynamic::DynamicBitChunkStore;

#[cfg(feature = "alloc")]
pub(crate) use allocator::BitAllocator;
