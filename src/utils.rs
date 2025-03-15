//! Utilities for implementers of bit-keyed collections.

mod chunk;
// mod chunk_iter;
mod chunk_store;
mod error;
// mod last_chunk_store;

#[cfg(feature = "alloc")]
pub mod alloc;

pub use chunk::{BitChunk, IndexInChunk, IndexOfChunk};
// pub use chunk_iter::{BitChunkIter, BitChunkIterRev};
pub use chunk_store::{BitChunkStore, BitChunkView, TrustedBitChunkStore};
pub use error::BitStoreError;
// pub use last_chunk_store::{LastBitChunkStore, LastBitChunkView};

#[cfg(feature = "alloc")]
pub use chunk_store::dynamic::DynamicBitChunkStore;
