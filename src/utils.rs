//! Utilities for implementers of bit-keyed collections.

mod chunk;
mod chunk_iter;
mod chunk_store;
mod error;
mod last_chunk_store;

#[cfg(feature = "alloc")]
pub mod alloc;

pub use chunk::{BitChunkRaw, IndexInChunkRaw, IndexOfChunkRaw};
pub use chunk_iter::{BitChunkIter, BitChunkIterRev, BitIndexOfChunkIter, BitIndexOfChunkIterRev};
pub use chunk_store::{BitChunkStoreRaw, BitChunkViewRaw, TrustedBitChunkStoreRaw};
pub use error::BitStoreError;
pub use last_chunk_store::{LastBitChunkStoreRaw, LastBitChunkViewRaw};

#[cfg(feature = "alloc")]
pub use chunk_store::dynamic::DynamicBitChunkStore;
