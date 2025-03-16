//! A chunk of bit-keys.

use core::{
    fmt,
    marker::PhantomData,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign},
};

use crate::{
    api::BitKey,
    utils::{BitChunkRaw, IndexInChunkRaw, IndexOfChunkRaw},
};

/// The index of a chunk, in a sequence of chunks.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitIndexOfChunk<K>(IndexOfChunkRaw, PhantomData<fn(K) -> K>);

impl<K> BitIndexOfChunk<K> {
    /// Creates a typed instance out of a untyped one.
    ///
    /// It is up to the caller to ensure that the values of `K` obtained will be sensible.
    pub const fn from_raw(o: IndexOfChunkRaw) -> Self {
        //  #   Why from `from_raw`?
        //
        //  To emphasize that is an operation which requires a tad more scrutinity than the usual `new`.

        Self(o, PhantomData)
    }

    /// Returns the underlying untyped index.
    pub const fn into_raw(self) -> IndexOfChunkRaw {
        self.0
    }
}

/// The index of a bit in a chunk.
///
/// The index of a bit in a chunk is expected to always be strictly less than 64. No index created by `BitChunkRaw::split`
/// will ever violate this invariant.
///
/// #   Panics
///
/// In Debug, most operations taking an `IndexInChunkRaw` will panic if its value is strictly greater than 63.
///
/// In Release, any high bit will be ignored (masked away).
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitIndexInChunk<K>(IndexInChunkRaw, PhantomData<fn(K) -> K>);

impl<K> BitIndexInChunk<K> {
    /// Creates a typed instance out of a untyped one.
    ///
    /// It is up to the caller to ensure that the values of `K` obtained will be sensible.
    pub const fn from_raw(i: IndexInChunkRaw) -> Self {
        //  #   Why from `from_raw`?
        //
        //  To emphasize that is an operation which requires a tad more scrutinity than the usual `new`.

        Self(i, PhantomData)
    }

    /// Returns the underlying untyped index.
    pub const fn into_raw(self) -> IndexInChunkRaw {
        self.0
    }
}

/// A chunk of bit-keys.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitChunk<K>(BitChunkRaw, PhantomData<fn(K) -> K>);

//
//  Constants.
//

impl<K> BitChunk<K> {
    /// Number of bits in a chunk.
    pub const BITS: u64 = BitChunkRaw::BITS;

    /// An all-zeros bit chunk.
    pub const ALL_ZEROS: Self = Self(BitChunkRaw::ALL_ZEROS, PhantomData);

    /// An all-ones bit chunk.
    pub const ALL_ONES: Self = Self(BitChunkRaw::ALL_ONES, PhantomData);
}

//
//  Static operations.
//

impl<K> BitChunk<K>
where
    K: BitKey,
{
    /// Splits a bit-key into an index-of-chunk/index-in-chunk pair.
    ///
    /// Returns None if the `key` is too large for the index-of-chunk part. This will never happen on 64-bits
    /// platforms -- ie, platforms on which `usize` is 64-bits -- and is otherwise likely to indicate an error.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::api::BitChunk;
    /// let (of_chunk, in_chunk) = BitChunk::<u64>::split(133).expect("no overflow");
    /// let key = BitChunk::<u64>::fuse(of_chunk, in_chunk).expect("no overflow");
    ///
    /// assert_eq!(133, key);
    /// ```
    #[inline]
    pub fn split(key: K) -> Option<(BitIndexOfChunk<K>, BitIndexInChunk<K>)> {
        BitChunkRaw::split(key.into_key()).map(|(o, i)| (BitIndexOfChunk::from_raw(o), BitIndexInChunk::from_raw(i)))
    }

    /// Fuses a pair of index-of-chunk/index-in-chunk pair into a bit-key.
    ///
    /// Returns None if the index-of-chunk is too large for the bit-key. This will never happen for pairs obtained from
    /// `Self::split`, but may happen for user-provided pairs on 64-bits platforms -- ie, platforms on which `usize` is
    /// 64-bits.
    ///
    /// #   Panics
    ///
    /// See `BitIndexInChunk`.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::api::BitChunk;
    /// let (of_chunk, in_chunk) = BitChunk::<u64>::split(133).expect("no overflow");
    /// let key = BitChunk::<u64>::fuse(of_chunk, in_chunk).expect("no overflow");
    ///
    /// assert_eq!(133, key);
    /// ```
    #[inline]
    pub fn fuse(of_chunk: BitIndexOfChunk<K>, in_chunk: BitIndexInChunk<K>) -> Option<K> {
        BitChunkRaw::fuse(of_chunk.0, in_chunk.0).map(K::from_key)
    }
}

//
//  Construction
//
impl<K> BitChunk<K> {
    /// Creates a typed instance out of a untyped one.
    ///
    /// It is up to the caller to ensure that the values of `K` obtained will be sensible.
    pub const fn from_raw(chunk: BitChunkRaw) -> Self {
        //  #   Why from `from_raw`?
        //
        //  To emphasize that is an operation which requires a tad more scrutinity than the usual `new`.

        Self(chunk, PhantomData)
    }
}

//
//  Bit operations.
//

impl<K> BitChunk<K> {
    /// Returns the number of bits set.
    #[inline]
    pub const fn count(&self) -> usize {
        self.0.count()
    }

    /// Returns whether the given bit is set.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    #[inline]
    pub const fn is_set(&self, bit: BitIndexInChunk<K>) -> bool {
        self.0.is_set(bit.0)
    }

    /// Sets a bit.
    ///
    /// Returns whether the bit is newly set, or not.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    #[inline]
    pub const fn set(&mut self, bit: BitIndexInChunk<K>) -> bool {
        self.0.set(bit.0)
    }

    /// Resets a bit.
    ///
    /// Returns whether the bit was set, or not.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    #[inline]
    pub const fn reset(&mut self, bit: BitIndexInChunk<K>) -> bool {
        self.0.reset(bit.0)
    }
}

//
//  Query operations.
//

impl<K> BitChunk<K> {
    /// Returns the number of bits set that are at, or after, the given index.
    #[inline]
    pub const fn count_after(&self, bit: BitIndexInChunk<K>) -> usize {
        self.0.count_after(bit.0)
    }

    /// Returns the number of bits set that are at, or before, the given index.
    #[inline]
    pub const fn count_before(&self, bit: BitIndexInChunk<K>) -> usize {
        self.0.count_before(bit.0)
    }

    /// Returns the index of the next set bit that is at, or after, the given index, if any.
    #[inline]
    pub const fn next_after(&self, bit: BitIndexInChunk<K>) -> Option<BitIndexInChunk<K>> {
        match self.0.next_after(bit.0) {
            Some(i) => Some(BitIndexInChunk::from_raw(i)),
            None => None,
        }
    }

    /// Returns the index of the next set bit that is at, or before, the given index, if any.
    #[inline]
    pub const fn next_before(&self, bit: BitIndexInChunk<K>) -> Option<BitIndexInChunk<K>> {
        match self.0.next_before(bit.0) {
            Some(i) => Some(BitIndexInChunk::from_raw(i)),
            None => None,
        }
    }
}

//
//  Bitwise traits.
//

impl<K> BitAndAssign for BitChunk<K> {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl<K> BitAnd for BitChunk<K> {
    type Output = Self;

    #[inline]
    fn bitand(mut self, rhs: Self) -> Self::Output {
        self &= rhs;
        self
    }
}

impl<K> BitOrAssign for BitChunk<K> {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl<K> BitOr for BitChunk<K> {
    type Output = Self;

    #[inline]
    fn bitor(mut self, rhs: Self) -> Self::Output {
        self |= rhs;
        self
    }
}

impl<K> BitXorAssign for BitChunk<K> {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl<K> BitXor for BitChunk<K> {
    type Output = Self;

    #[inline]
    fn bitxor(mut self, rhs: Self) -> Self::Output {
        self ^= rhs;
        self
    }
}

//
//  Common traits
//

impl<K> fmt::Debug for BitChunk<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:?}", self.0)
    }
}

impl<K> Default for BitChunk<K> {
    fn default() -> Self {
        Self(BitChunkRaw::default(), PhantomData)
    }
}
