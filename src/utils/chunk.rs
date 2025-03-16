//  See `BitChunkRaw` type.
//
//  #   Why a dedicated type?
//
//  Bundling methods on an existing type is possible only by "extension" traits, which then require the user to have
//  these traits in scope to invoke them.
//
//  A dedicated type, on top of avoiding type confusion, is more ergonomic as inherent methods can just be called
//  without any hassle.
//
//
//  #   Why an exposed type?
//
//  Convertion to/from the wrapped integer type would be necessary anyway, thus exposing which type is used regardless.
//
//  If the type is anyway exposed, it may as well be easily accessible.
//
//
//  #   Why `u64`?
//
//  There is a balance to be found. A smaller type means that fewer bits are chunked together, and thus bulk operations
//  are not as effective. A larger type may not be well supported -- looking at you, `u128` -- defeating the purpose of
//  efficient bulk operations, and may possibly impose greater alignment than necessary.
//
//  Since 32-bits & 64-bits CPUs tend to support `u64` natively, and those compose the bulk of platforms targetted by
//  Rust developers, `u64` is therefore the largest well supported type.
//
//  Its alignment may prove annoying, in some cases. Trade-offs, trade-offs, ...

use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

/// A chunk of bits.
///
/// One of the key traits of bit-keyed collections is their ability to effectively compress the presence or absence of
/// elements in the collection down to a single bit. `BitChunkRaw` is a chunk of such bits, and offers efficient methods to
/// manipulate these bits in bulk.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitChunkRaw(pub u64);

/// The index of a chunk, in a sequence of chunks.
///
/// #   Why `usize`?
///
/// In Rust, all slices are indexed by a `usize`, and the `IndexOfChunkRaw` will be used nigh exclusively as an index in
/// slices.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct IndexOfChunkRaw(pub usize);

impl IndexOfChunkRaw {
    /// Returns the incremented index, if any.
    pub fn checked_add(self, offset: usize) -> Option<IndexOfChunkRaw> {
        self.0.checked_add(offset).map(Self)
    }

    /// Returns the decremented index, if any.
    pub fn checked_sub(self, offset: usize) -> Option<IndexOfChunkRaw> {
        self.0.checked_sub(offset).map(Self)
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
///
/// #   Why `u32`?
///
/// In Rust, all shift operations take a `u32` as their right-hand argument, and the `IndexInChunkRaw` will be used nigh
/// exclusively with shift operations.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct IndexInChunkRaw(pub u32);

//
//  Constants.
//

impl BitChunkRaw {
    /// Number of bits in a chunk.
    pub const BITS: u64 = 64;

    /// An all-zeros bit chunk.
    pub const ALL_ZEROS: Self = Self(0);

    /// An all-ones bit chunk.
    pub const ALL_ONES: Self = Self(!0);
}

//
//  Static operations.
//

impl BitChunkRaw {
    /// Splits a bit-key into an index-of-chunk/index-in-chunk pair.
    ///
    /// Returns None if the `key` is too large for the index-of-chunk part. This will never happen on 64-bits
    /// platforms -- ie, platforms on which `usize` is 64-bits -- and is otherwise likely to indicate an error.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::BitChunkRaw;
    /// let (of_chunk, in_chunk) = BitChunkRaw::split(133).expect("no overflow");
    ///
    /// assert_eq!(2, of_chunk.0);
    /// assert_eq!(5, in_chunk.0);
    /// ```
    #[inline]
    pub const fn split(key: u64) -> Option<(IndexOfChunkRaw, IndexInChunkRaw)> {
        //  Compute both / and % close together, so the optimizer fuses both in a single instruction.
        let of_chunk = key / Self::BITS;
        let in_chunk = key % Self::BITS;

        //  FIXME: convert to `.try_into()` when it is const.
        if of_chunk as usize as u64 != of_chunk {
            return None;
        }

        let of_chunk = IndexOfChunkRaw(of_chunk as _);
        let in_chunk = IndexInChunkRaw(in_chunk as _);

        Some((of_chunk, in_chunk))
    }

    /// Fuses a pair of index-of-chunk/index-in-chunk pair into a bit-key.
    ///
    /// Returns None if the index-of-chunk is too large for the bit-key. This will never happen for pairs obtained from
    /// `Self::split`, but may happen for user-provided pairs on 64-bits platforms -- ie, platforms on which `usize` is
    /// 64-bits.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw, IndexOfChunkRaw};
    /// let of_chunk = IndexOfChunkRaw(2);
    /// let in_chunk = IndexInChunkRaw(5);
    ///
    /// let key = BitChunkRaw::fuse(of_chunk, in_chunk).expect("no overflow");
    ///
    /// assert_eq!(133, key);
    /// ```
    #[inline]
    pub const fn fuse(of_chunk: IndexOfChunkRaw, in_chunk: IndexInChunkRaw) -> Option<u64> {
        debug_assert!(in_chunk.0 < Self::BITS as _);

        //  FIXME: convert to `.try_into()` when it is const.
        if of_chunk.0 as u64 as usize != of_chunk.0 {
            return None;
        }

        let of_chunk: u64 = of_chunk.0 as _;
        let in_chunk: u64 = in_chunk.0 as _;

        //  FIXME: convert to `?` when it is const.
        let Some(key) = of_chunk.checked_mul(Self::BITS) else {
            return None;
        };

        //  Mask to ensure the addition doesn't overflow.
        let in_chunk = in_chunk % Self::BITS;

        Some(key + in_chunk)
    }
}

#[cfg(test)]
mod static_tests {
    use super::*;

    #[test]
    fn split_brush() {
        assert_eq!(Some((0, 0)), compute_split(0));
        assert_eq!(Some((0, 1)), compute_split(1));
        assert_eq!(Some((0, 62)), compute_split(62));
        assert_eq!(Some((0, 63)), compute_split(63));

        assert_eq!(Some((1, 0)), compute_split(64));
        assert_eq!(Some((1, 1)), compute_split(65));
        assert_eq!(Some((1, 62)), compute_split(126));
        assert_eq!(Some((1, 63)), compute_split(127));

        assert_eq!(Some((2, 0)), compute_split(128));
    }

    #[test]
    #[cfg(not(target_pointer_width = "64"))]
    fn split_overflow() {
        let highest_of_chunk = usize::MAX as u64;
        assert!(highest_of_chunk < u64::MAX);

        let highest = highest_of_chunk + 63;

        assert_eq!(Some((highest_of_chunk, 63)), compute_split(highest));
        assert_eq!(None, compute_split(highest + 1));
    }

    #[test]
    fn fuse_brush() {
        assert_eq!(Some(0), compute_fuse(0, 0));
        assert_eq!(Some(1), compute_fuse(0, 1));
        assert_eq!(Some(62), compute_fuse(0, 62));
        assert_eq!(Some(63), compute_fuse(0, 63));

        assert_eq!(Some(64), compute_fuse(1, 0));
        assert_eq!(Some(65), compute_fuse(1, 1));
        assert_eq!(Some(126), compute_fuse(1, 62));
        assert_eq!(Some(127), compute_fuse(1, 63));

        assert_eq!(Some(128), compute_fuse(2, 0));
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn fuse_overflow() {
        let highest: usize = u64::MAX.try_into().expect("usize to be 64-bits");

        let highest_of_chunk = highest / 64;

        assert_eq!(Some(highest as u64), compute_fuse(highest_of_chunk, 63));
        assert_eq!(None, compute_fuse(highest_of_chunk + 1, 0));
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn fuse_in_overflow() {
        compute_fuse(0, 64);
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn fuse_in_overflow() {
        for i in 6..32 {
            let overflow: u32 = 1 << i;

            assert_eq!(Some(0), compute_fuse(0, overflow | 0));
            assert_eq!(Some(1), compute_fuse(0, overflow | 1));
            assert_eq!(Some(62), compute_fuse(0, overflow | 62));
            assert_eq!(Some(63), compute_fuse(0, overflow | 63));
        }
    }

    fn compute_split(key: u64) -> Option<(usize, u32)> {
        BitChunkRaw::split(key).map(|(o, i)| (o.0, i.0))
    }

    fn compute_fuse(of_chunk: usize, in_chunk: u32) -> Option<u64> {
        BitChunkRaw::fuse(IndexOfChunkRaw(of_chunk), IndexInChunkRaw(in_chunk))
    }
} // mod static_tests

//
//  Bit operations.
//

impl BitChunkRaw {
    /// Returns the number of bits set.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::BitChunkRaw;
    ///
    /// assert_eq!(0, BitChunkRaw::ALL_ZEROS.count());
    /// assert_eq!(64, BitChunkRaw::ALL_ONES.count());
    /// ```
    #[inline]
    pub const fn count(&self) -> usize {
        self.0.count_ones() as _
    }

    /// Returns whether the given bit is set.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// let chunk = BitChunkRaw(0b1001);
    ///
    /// assert!(chunk.is_set(IndexInChunkRaw(0)));
    /// assert!(chunk.is_set(IndexInChunkRaw(3)));
    ///
    /// for i in (1..=2).chain(4..=63) {
    ///     assert!(!chunk.is_set(IndexInChunkRaw(i)));
    /// }
    /// ```
    #[inline]
    pub const fn is_set(&self, bit: IndexInChunkRaw) -> bool {
        let mask = Self::bit_mask(bit);

        (self.0 & mask) != 0
    }

    /// Sets a bit.
    ///
    /// Returns whether the bit is newly set, or not.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// let mut chunk = BitChunkRaw(0b1001);
    ///
    /// assert!(!chunk.set(IndexInChunkRaw(0)));
    /// assert!(chunk.set(IndexInChunkRaw(2)));
    ///
    /// assert_eq!(0b1101, chunk.0);
    /// ```
    #[inline]
    pub const fn set(&mut self, bit: IndexInChunkRaw) -> bool {
        let mask = Self::bit_mask(bit);

        let result = (self.0 & mask) == 0;

        self.0 |= mask;

        result
    }

    /// Resets a bit.
    ///
    /// Returns whether the bit was set, or not.
    ///
    /// #   Panics
    ///
    /// See `IndexInChunkRaw`.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// let mut chunk = BitChunkRaw(0b1001);
    ///
    /// assert!(chunk.reset(IndexInChunkRaw(0)));
    /// assert!(!chunk.reset(IndexInChunkRaw(2)));
    ///
    /// assert_eq!(0b1000, chunk.0);
    /// ```
    #[inline]
    pub const fn reset(&mut self, bit: IndexInChunkRaw) -> bool {
        let mask = Self::bit_mask(bit);

        let result = (self.0 & mask) != 0;

        self.0 &= !mask;

        result
    }
}

#[cfg(test)]
mod bit_tests {
    use super::*;

    const BITS: u32 = BitChunkRaw::BITS as u32;

    #[test]
    fn is_set_empty() {
        for i in 0..BITS {
            assert!(!BitChunkRaw::ALL_ZEROS.is_set(IndexInChunkRaw(i)), "{i}");
        }
    }

    #[test]
    fn is_set_full() {
        for i in 0..BITS {
            assert!(BitChunkRaw::ALL_ONES.is_set(IndexInChunkRaw(i)), "{i}");
        }
    }

    #[test]
    fn set_empty() {
        for i in 0..BITS {
            let mut chunk = BitChunkRaw::ALL_ZEROS;

            assert!(chunk.set(IndexInChunkRaw(i)), "{i}");
            assert!(chunk.is_set(IndexInChunkRaw(i)), "{i}");
        }
    }

    #[test]
    fn set_full() {
        for i in 0..BITS {
            let mut chunk = BitChunkRaw::ALL_ONES;

            assert!(!chunk.set(IndexInChunkRaw(i)), "{i}");
            assert!(chunk.is_set(IndexInChunkRaw(i)), "{i}");
        }
    }

    #[test]
    fn reset_empty() {
        for i in 0..BITS {
            let mut chunk = BitChunkRaw::ALL_ZEROS;

            assert!(!chunk.reset(IndexInChunkRaw(i)), "{i}");
            assert!(!chunk.is_set(IndexInChunkRaw(i)), "{i}");
        }
    }

    #[test]
    fn reset_full() {
        for i in 0..BITS {
            let mut chunk = BitChunkRaw::ALL_ONES;

            assert!(chunk.reset(IndexInChunkRaw(i)), "{i}");
            assert!(!chunk.is_set(IndexInChunkRaw(i)), "{i}");
        }
    }
} // mod bit_tests

//
//  Query operations.
//

impl BitChunkRaw {
    /// Returns the number of bits set that are at, or after, the given index.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// assert_eq!(0, BitChunkRaw::ALL_ZEROS.count_after(IndexInChunkRaw(0)));
    ///
    /// assert_eq!(64, BitChunkRaw::ALL_ONES.count_after(IndexInChunkRaw(0)));
    /// assert_eq!(1, BitChunkRaw::ALL_ONES.count_after(IndexInChunkRaw(63)));
    /// ```
    #[inline]
    pub const fn count_after(&self, bit: IndexInChunkRaw) -> usize {
        let mask = Self::mask_after(bit);

        (self.0 & mask).count_ones() as _
    }

    /// Returns the number of bits set that are at, or before, the given index.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// assert_eq!(0, BitChunkRaw::ALL_ZEROS.count_before(IndexInChunkRaw(0)));
    ///
    /// assert_eq!(1, BitChunkRaw::ALL_ONES.count_before(IndexInChunkRaw(0)));
    /// assert_eq!(64, BitChunkRaw::ALL_ONES.count_before(IndexInChunkRaw(63)));
    /// ```
    #[inline]
    pub const fn count_before(&self, bit: IndexInChunkRaw) -> usize {
        let mask = Self::mask_before(bit);

        (self.0 & mask).count_ones() as _
    }

    /// Returns the index of the next set bit that is at, or after, the given index, if any.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// assert_eq!(None, BitChunkRaw::ALL_ZEROS.next_after(IndexInChunkRaw(0)));
    ///
    /// assert_eq!(Some(IndexInChunkRaw(0)), BitChunkRaw::ALL_ONES.next_after(IndexInChunkRaw(0)));
    /// ```
    #[inline]
    pub const fn next_after(&self, bit: IndexInChunkRaw) -> Option<IndexInChunkRaw> {
        let mask = Self::mask_after(bit);

        let zeros = (self.0 & mask).trailing_zeros();

        //  FIXME: convert to `.then_some` when it is const.
        if zeros < Self::BITS as _ {
            Some(IndexInChunkRaw(zeros))
        } else {
            None
        }
    }

    /// Returns the index of the next set bit that is at, or before, the given index, if any.
    ///
    /// #   Examples
    ///
    /// ```
    /// #   use bit_keyed::utils::{BitChunkRaw, IndexInChunkRaw};
    /// assert_eq!(None, BitChunkRaw::ALL_ZEROS.next_before(IndexInChunkRaw(63)));
    ///
    /// assert_eq!(Some(IndexInChunkRaw(63)), BitChunkRaw::ALL_ONES.next_before(IndexInChunkRaw(63)));
    /// ```
    #[inline]
    pub const fn next_before(&self, bit: IndexInChunkRaw) -> Option<IndexInChunkRaw> {
        let mask = Self::mask_before(bit);

        let bits = Self::BITS as u32;
        let zeros = (self.0 & mask).leading_zeros();

        //  FIXME: convert to `.then_some` when it is const.
        if zeros < bits {
            Some(IndexInChunkRaw(bits - zeros - 1))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod query_tests {
    use super::*;

    const BITS: u32 = BitChunkRaw::BITS as u32;

    #[test]
    fn count_after_empty() {
        for i in 0..BITS {
            assert_eq!(0, compute_count_after(0, i), "{i}");
        }
    }

    #[test]
    fn count_after_full() {
        for i in 0..BITS {
            assert_eq!(BITS - i, compute_count_after(!0, i), "{i}");
        }
    }

    #[test]
    fn count_before_empty() {
        for i in 0..BITS {
            assert_eq!(0, compute_count_before(0, i), "{i}");
        }
    }

    #[test]
    fn count_before_full() {
        for i in 0..BITS {
            assert_eq!(1 + i, compute_count_before(!0, i), "{i}");
        }
    }

    #[test]
    fn next_after_empty() {
        for i in 0..BITS {
            assert_eq!(None, compute_next_after(0, i), "{i}");
        }
    }

    #[test]
    fn next_after_full() {
        for i in 0..BITS {
            assert_eq!(Some(i), compute_next_after(!0, i), "{i}");
        }
    }

    #[test]
    fn next_before_empty() {
        for i in 0..BITS {
            assert_eq!(None, compute_next_before(0, i), "{i}");
        }
    }

    #[test]
    fn next_before_full() {
        for i in 0..BITS {
            assert_eq!(Some(i), compute_next_before(!0, i), "{i}");
        }
    }

    fn compute_count_after(chunk: u64, bit: u32) -> u32 {
        BitChunkRaw(chunk).count_after(IndexInChunkRaw(bit)) as _
    }

    fn compute_count_before(chunk: u64, bit: u32) -> u32 {
        BitChunkRaw(chunk).count_before(IndexInChunkRaw(bit)) as _
    }

    fn compute_next_after(chunk: u64, bit: u32) -> Option<u32> {
        BitChunkRaw(chunk)
            .next_after(IndexInChunkRaw(bit))
            .map(|in_chunk| in_chunk.0)
    }

    fn compute_next_before(chunk: u64, bit: u32) -> Option<u32> {
        BitChunkRaw(chunk)
            .next_before(IndexInChunkRaw(bit))
            .map(|in_chunk| in_chunk.0)
    }
} // mod query_tests

//
//  Bitwise traits.
//

impl BitAndAssign for BitChunkRaw {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl BitAnd for BitChunkRaw {
    type Output = Self;

    #[inline]
    fn bitand(mut self, rhs: Self) -> Self::Output {
        self &= rhs;
        self
    }
}

impl BitOrAssign for BitChunkRaw {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitOr for BitChunkRaw {
    type Output = Self;

    #[inline]
    fn bitor(mut self, rhs: Self) -> Self::Output {
        self |= rhs;
        self
    }
}

impl BitXorAssign for BitChunkRaw {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl BitXor for BitChunkRaw {
    type Output = Self;

    #[inline]
    fn bitxor(mut self, rhs: Self) -> Self::Output {
        self ^= rhs;
        self
    }
}

#[cfg(test)]
mod bitwise_tests {
    use super::*;

    #[test]
    fn bit_and() {
        const LEFT: u64 = 0b1001;
        const RIGHT: u64 = 0b0001_1000;
        const RESULT: u64 = 0b1000;

        {
            let mut chunk = BitChunkRaw(LEFT);

            chunk &= BitChunkRaw(RIGHT);

            assert_eq!(RESULT, chunk.0);
        }

        assert_eq!(RESULT, (BitChunkRaw(LEFT) & BitChunkRaw(RIGHT)).0);
    }

    #[test]
    fn bit_or() {
        const LEFT: u64 = 0b1001;
        const RIGHT: u64 = 0b0001_1000;
        const RESULT: u64 = 0b0001_1001;

        {
            let mut chunk = BitChunkRaw(LEFT);

            chunk |= BitChunkRaw(RIGHT);

            assert_eq!(RESULT, chunk.0);
        }

        assert_eq!(RESULT, (BitChunkRaw(LEFT) | BitChunkRaw(RIGHT)).0);
    }

    #[test]
    fn bit_xor() {
        const LEFT: u64 = 0b1001;
        const RIGHT: u64 = 0b0001_1000;
        const RESULT: u64 = 0b0001_0001;

        {
            let mut chunk = BitChunkRaw(LEFT);

            chunk ^= BitChunkRaw(RIGHT);

            assert_eq!(RESULT, chunk.0);
        }

        assert_eq!(RESULT, (BitChunkRaw(LEFT) ^ BitChunkRaw(RIGHT)).0);
    }
} // mod bitwise_tests

//
//  Implementation details
//

impl BitChunkRaw {
    //  Mask of the bit.
    #[inline]
    const fn bit_mask(bit: IndexInChunkRaw) -> u64 {
        debug_assert!(bit.0 < Self::BITS as _);

        //  Mask to ensure the shift doesn't overflow.
        let shift = bit.0 % Self::BITS as u32;

        1 << shift
    }

    //  Mask including `bit` and all bits after.
    #[inline]
    const fn mask_after(bit: IndexInChunkRaw) -> u64 {
        let mask = Self::bit_mask(bit) - 1;

        !mask
    }

    //  Mask including `bit` and all bits before.
    #[inline]
    const fn mask_before(bit: IndexInChunkRaw) -> u64 {
        (Self::bit_mask(bit) << 1).wrapping_sub(1)
    }
}
