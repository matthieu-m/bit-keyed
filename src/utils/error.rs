//  Errors.

use core::{error, fmt};

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
