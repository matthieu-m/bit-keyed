//! A generic key for bit-keyed structures.

use core::hash::Hash;

/// A bit key is an index into a bit-keyed structure.
///
/// The most obvious type is `usize`, however a bit-keyed structures could also be indexed by a strongly-typed wrapper
/// over an integer, or an enum.
pub trait BitKey: Copy + Eq + Hash + Ord {
    /// Returns the key associated to the index.
    ///
    /// It is up to the caller to guarantee that the index is sensible, such as being the result of a prior `into_key`
    /// call. For non-sensible values, this function may panic, or return a non-sensible result.
    fn from_key(key: u64) -> Self;

    /// Returns the index associated to the key.
    fn into_key(self) -> u64;
}

impl BitKey for u8 {
    #[track_caller]
    fn from_key(index: u64) -> Self {
        #[cold]
        fn panic(index: u64) -> ! {
            panic!("Cannot convert {index} to u8");
        }

        index.try_into().unwrap_or_else(|_| panic(index))
    }

    fn into_key(self) -> u64 {
        self.into()
    }
}

impl BitKey for u16 {
    #[track_caller]
    fn from_key(index: u64) -> Self {
        #[cold]
        fn panic(index: u64) -> ! {
            panic!("Cannot convert {index} to u16");
        }

        index.try_into().unwrap_or_else(|_| panic(index))
    }

    fn into_key(self) -> u64 {
        self.into()
    }
}

impl BitKey for u32 {
    #[track_caller]
    fn from_key(index: u64) -> Self {
        #[cold]
        fn panic(index: u64) -> ! {
            panic!("Cannot convert {index} to u32");
        }

        index.try_into().unwrap_or_else(|_| panic(index))
    }

    fn into_key(self) -> u64 {
        self.into()
    }
}

impl BitKey for u64 {
    fn from_key(index: u64) -> Self {
        index
    }

    fn into_key(self) -> u64 {
        self
    }
}

impl BitKey for usize {
    #[track_caller]
    fn from_key(index: u64) -> Self {
        #[cold]
        fn panic(index: u64) -> ! {
            panic!("Cannot convert {index} to usize");
        }

        index.try_into().unwrap_or_else(|_| panic(index))
    }

    #[track_caller]
    fn into_key(self) -> u64 {
        #[cold]
        fn panic(index: usize) -> ! {
            panic!("Cannot convert {index} to u64");
        }

        self.try_into().unwrap_or_else(|_| panic(self))
    }
}
