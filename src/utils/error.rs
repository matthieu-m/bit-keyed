//  Errors.

use core::{error, fmt};

#[cfg(feature = "alloc")]
use crate::utils::alloc::AllocError;

/// An error in setting a bit.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitStoreError;

impl fmt::Display for BitStoreError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str("BitStoreError")
    }
}

impl error::Error for BitStoreError {}

#[cfg(feature = "alloc")]
impl From<AllocError> for BitStoreError {
    fn from(_: AllocError) -> Self {
        Self
    }
}
