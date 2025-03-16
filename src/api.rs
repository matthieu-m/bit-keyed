//! A set of high-level traits to abstract over the implementation details.

pub mod bit_chunk;
pub mod bit_key;
pub mod bit_set;
pub mod bit_view;

pub use bit_chunk::{BitChunk, BitIndexInChunk, BitIndexOfChunk};
pub use bit_key::BitKey;
pub use bit_set::BitSet;
pub use bit_view::BitView;

pub use crate::utils::BitStoreError;
