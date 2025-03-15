//! A set of high-level traits to abstract over the implementation details.

pub mod bit_key;
pub mod bit_set;

pub use bit_key::BitKey;
pub use bit_set::BitSet;

pub use crate::utils::BitStoreError;
