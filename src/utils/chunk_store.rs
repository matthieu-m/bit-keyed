//  See the various traits.

use core::mem;

use crate::utils::{BitChunkRaw, BitStoreError, IndexOfChunkRaw};

//
//  API
//

/// A trait for read-only access to a collection of `BitChunkRaw`.
///
/// The trait is pre-implemented for `[BitChunkRaw; N]`, and exists to allow for alternative representations, such as
/// compressed sets, or sparse sets.
pub trait BitChunkViewRaw {
    //
    //  Index access
    //

    /// Returns the `BitChunkRaw` at the given index.
    ///
    /// If `index` is unknown, an `ALL_ZEROS` chunk should be returned.
    fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw;

    /// Returns the `BitChunkRaw` at the given index.
    ///
    /// #   Safety
    ///
    /// The caller guarantees that `index` was either returned by a call to `self.first()`, `self.last()`,
    /// `self.next_after(...)`, or `self.next_before(...)`.
    #[inline]
    unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        self.get(index)
    }

    //
    //  Index iteration
    //

    /// Returns the first interesting index, if any.
    ///
    /// All chunks strictly before this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
    /// chunk at this index isn't `ALL_ZEROS` too.
    fn first(&self) -> Option<IndexOfChunkRaw>;

    /// Returns the last interesting index, if any.
    ///
    /// All chunks strictly after this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
    /// chunk at this index isn't `ALL_ZEROS` too.
    fn last(&self) -> Option<IndexOfChunkRaw>;

    /// Returns the next interesting index at or after `index`, if any.
    ///
    /// Returns `None` when all chunks at or after `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is made
    /// that it returns `None` precisely when no further chunks have any set bit.
    fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw>;

    /// Returns the next interesting index at or before `index`, if any.
    ///
    /// Returns `None` when all chunks at or before `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is
    /// made that it returns `None` precisely when no prior chunks have any set bit.
    fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw>;
}

/// A trait for write access to a collection of `BitChunkRaw`.
///
/// The trait is pre-implemented for `[BitChunkRaw; N]`, and exists to allow for alternative representations, such as
/// compressed sets, or sparse sets.
pub trait BitChunkStoreRaw: BitChunkViewRaw {
    /// Sets the `BitChunkRaw` at the given index.
    ///
    /// On success, returns the previous chunk stored at `index`, or `ALL_ZEROS` if no such chunk existed. On error,
    /// `self` is left unchanged.
    ///
    /// Errors may be either transient or permnanent. For example, if the backing store is `[BitChunkRaw; 1]`, then any
    /// attempt to store at index `64` or greater is doomed to fail, whereas if the store is `Vec<BitChunkRaw>`, then any
    /// attempt to store beyond the current capacity of the vector may fail if the memory allocation fails at this point
    /// in time.
    fn set(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError>;

    /// Sets the `BitChunkRaw` at the given index.
    ///
    /// #   Safety
    ///
    /// `index` must be the index of a non `ALL_ZEROS` chunk, prior to this call.
    #[inline]
    unsafe fn set_unchecked(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) {
        let _result = self.set(index, chunk);

        debug_assert!(_result.is_ok());
    }
}

/// A marker trait to guarantee that the store faithfully executes reads & writes.
///
/// #   Safety
///
/// -   Faithful: implementations guarantee that `self.get(index)` return an equal `BitChunkRaw` to the last for which
///     `self.set(index, ...)` succeeded.
/// -   One-pass: implementations guarantee that `self.next_after(index)`, resp. `self.next_before(index)`, return an
///     index that is greater than or equal to `index`, resp. less than or equal to `index`.
pub unsafe trait TrustedBitChunkStoreRaw {}

//
//  Implementation for references.
//

impl<V> BitChunkViewRaw for &V
where
    V: ?Sized + BitChunkViewRaw,
{
    fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        (**self).get(index)
    }

    unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        //  Safety: forwarded.
        unsafe { (**self).get_unchecked(index) }
    }

    fn first(&self) -> Option<IndexOfChunkRaw> {
        (**self).first()
    }

    fn last(&self) -> Option<IndexOfChunkRaw> {
        (**self).last()
    }

    fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        (**self).next_after(index)
    }

    fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        (**self).next_before(index)
    }
}

//  Safety: forward.
unsafe impl<V> TrustedBitChunkStoreRaw for &V where V: ?Sized + BitChunkViewRaw + TrustedBitChunkStoreRaw {}

impl<V> BitChunkViewRaw for &mut V
where
    V: ?Sized + BitChunkViewRaw,
{
    fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        (**self).get(index)
    }

    unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        //  Safety: forwarded.
        unsafe { (**self).get_unchecked(index) }
    }

    fn first(&self) -> Option<IndexOfChunkRaw> {
        (**self).first()
    }

    fn last(&self) -> Option<IndexOfChunkRaw> {
        (**self).last()
    }

    fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        (**self).next_after(index)
    }

    fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        (**self).next_before(index)
    }
}

impl<V> BitChunkStoreRaw for &mut V
where
    V: ?Sized + BitChunkStoreRaw,
{
    fn set(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError> {
        (**self).set(index, chunk)
    }

    unsafe fn set_unchecked(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) {
        //  Safety: forward.
        unsafe { (**self).set_unchecked(index, chunk) };
    }
}

//  Safety: forward.
unsafe impl<V> TrustedBitChunkStoreRaw for &mut V where V: ?Sized + BitChunkStoreRaw + TrustedBitChunkStoreRaw {}

//
//  Implementation for [BitChunkRaw; N].
//

mod array {
    use super::*;

    impl<const N: usize> BitChunkViewRaw for [BitChunkRaw; N] {
        //
        //  Index access
        //

        #[inline]
        fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            <[BitChunkRaw]>::get(self, index.0)
                .copied()
                .unwrap_or(BitChunkRaw::ALL_ZEROS)
        }

        #[inline]
        unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            debug_assert!(index.0 < self.len(), "{} >= {}", index.0, self.len());

            //  Safety:
            //  -   `index.0` is in-bounds, as the caller guarantees that `index` was returned by `self.first()`,
            //      `self.last()`, `self.next_after(...)`, or `self.next_before(...)`, and those methods only return
            //      in-bounds indexes.
            unsafe { *<[BitChunkRaw]>::get_unchecked(self, index.0) }
        }

        //
        //  Index iteration
        //

        #[inline]
        fn first(&self) -> Option<IndexOfChunkRaw> {
            (!self.is_empty()).then_some(IndexOfChunkRaw(0))
        }

        #[inline]
        fn last(&self) -> Option<IndexOfChunkRaw> {
            self.len().checked_sub(1).map(IndexOfChunkRaw)
        }

        #[inline]
        fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            //  Safety:
            //  -   `get_unchecked` relies on this method only returning in-bounds indexes.
            (index.0 < N).then_some(index)
        }

        #[inline]
        fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            Some(index)
        }
    }

    impl<const N: usize> BitChunkStoreRaw for [BitChunkRaw; N] {
        #[inline]
        fn set(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError> {
            let slot = self.get_mut(index.0).ok_or(BitStoreError)?;

            Ok(mem::replace(slot, chunk))
        }
    }

    //  Safety:
    //
    //  -   The implementation of `BitChunkViewRaw` and `BitChunkStoreRaw` is faithful.
    //  -   The implementation of `BitChunkViewRaw` is one-pass.
    unsafe impl<const N: usize> TrustedBitChunkStoreRaw for [BitChunkRaw; N] {}
} // mod array

//
//  Implementation for [BitChunkRaw]
//

mod slice {
    use super::*;

    impl BitChunkViewRaw for [BitChunkRaw] {
        //
        //  Index access
        //

        #[inline]
        fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            <[BitChunkRaw]>::get(self, index.0)
                .copied()
                .unwrap_or(BitChunkRaw::ALL_ZEROS)
        }

        #[inline]
        unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            debug_assert!(index.0 < self.len(), "{} >= {}", index.0, self.len());

            //  Safety:
            //  -   `index.0` is in-bounds, as the caller guarantees that `index` was returned by `self.first()`,
            //      `self.last()`, `self.next_after(...)`, or `self.next_before(...)`, and those methods only return
            //      in-bounds indexes.
            unsafe { *<[BitChunkRaw]>::get_unchecked(self, index.0) }
        }

        //
        //  Index iteration
        //

        #[inline]
        fn first(&self) -> Option<IndexOfChunkRaw> {
            (!self.is_empty()).then_some(IndexOfChunkRaw(0))
        }

        #[inline]
        fn last(&self) -> Option<IndexOfChunkRaw> {
            self.len().checked_sub(1).map(IndexOfChunkRaw)
        }

        #[inline]
        fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            //  Safety:
            //  -   `get_unchecked` relies on this method only returning in-bounds indexes.
            (index.0 < self.len()).then_some(index)
        }

        #[inline]
        fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            Some(index)
        }
    }

    //  Safety:
    //
    //  -   The implementation of `BitChunkViewRaw` and `BitChunkStoreRaw` is faithful.
    //  -   The implementation of `BitChunkViewRaw` is one-pass.
    unsafe impl TrustedBitChunkStoreRaw for [BitChunkRaw] {}
} // mod slice

//
//  DynamicBitChunkStore & Implementation.
//

//  #   Why an inner module?
//
//  1.  It's much easier than annotating every item with `#[cfg(feature = "alloc")]`.
//  2.  `unsafe` is viral up to module boundaries, so best keep it contained.
#[cfg(feature = "alloc")]
pub(crate) mod dynamic {
    use core::{
        alloc::Layout,
        cmp, fmt,
        hash::{Hash, Hasher},
        ptr::NonNull,
    };

    use crate::utils::alloc::{Allocator, Global};

    use super::*;

    /// Heap allocated implementation of a `BitChunkStoreRaw` and related traits.
    pub struct DynamicBitChunkStore<A = Global>
    where
        A: Allocator,
    {
        //  Safety Invariants:
        //  -   Empty Dangling: if an empty slice, it is dangling.
        //  -   Self-Allocated: if not empty, it is allocated by `Self::allocate`.
        //  -   Initialized: if not empty, all `self.0.len()` items of the slice are initialized.
        ptr: NonNull<[BitChunkRaw]>,
        allocator: A,
    }

    //
    //  Creation
    //

    impl DynamicBitChunkStore<Global> {
        /// Returns a new, empty, instance.
        pub const fn new() -> Self {
            Self::new_in(Global)
        }
    }

    impl<A> DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        /// Returns a new, empty, instance.
        pub const fn new_in(allocator: A) -> Self {
            //  Safety Invariant:
            //  -   Empty Dangling: create an empty slice, with a dangling pointer.
            let ptr = NonNull::slice_from_raw_parts(NonNull::dangling(), 0);

            Self { ptr, allocator }
        }
    }

    //
    //  BitSet (inherent)
    //

    impl<A> DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        /// Returns a reference to the underlying slice of chunks.
        #[inline]
        pub const fn chunks(&self) -> &[BitChunkRaw] {
            if self.ptr.is_empty() {
                &[]
            } else {
                //  Safety:
                //  -   The pointer is sufficiently aligned, as per the Safety Invariants.
                //  -   The pointer is currently allocated, as the slice is non-empty, as per the Safety Invariants.
                //  -   No mutable borrow is accessible, as `self` could be borrowed.
                unsafe { self.ptr.as_ref() }
            }
        }

        /// Returns a mutable reference to the underlying slice of chunks.
        #[inline]
        pub const fn chunks_mut(&mut self) -> &mut [BitChunkRaw] {
            if self.ptr.is_empty() {
                &mut []
            } else {
                //  Safety:
                //  -   The pointer is sufficiently aligned, as per the Safety Invariants.
                //  -   The pointer is currently allocated, as the slice is non-empty, as per the Safety Invariants.
                //  -   No borrow is accessible, as `self` could be mutably borrowed.
                unsafe { self.ptr.as_mut() }
            }
        }
    }

    //
    //  BitChunkViewRaw/Store (inherent)
    //

    impl<A> DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        //
        //  Index access
        //

        /// Returns the `BitChunkRaw` at the given index.
        ///
        /// If `index` is unknown, an `ALL_ZEROS` chunk should be returned.
        #[inline]
        pub fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            self.chunks().get(index.0).copied().unwrap_or(BitChunkRaw::ALL_ZEROS)
        }

        /// Returns the `BitChunkRaw` at the given index.
        ///
        /// #   Safety
        ///
        /// The caller guarantees that `index` was either returned by a call to `self.first()`, `self.last()`,
        /// `self.next_after(...)`, or `self.next_before(...)`.
        #[inline]
        pub unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            debug_assert!(index.0 < self.ptr.len(), "{} >= {}", index.0, self.ptr.len());

            //  Safety:
            //  -   `index.0` is in-bounds, as the caller guarantees that `index` was returned by `self.first()`,
            //      `self.last()`, `self.next_after(...)`, or `self.next_before(...)`, and those methods only return
            //      in-bounds indexes.
            unsafe { *self.chunks().get_unchecked(index.0) }
        }

        //
        //  Index iteration
        //

        /// Returns the first interesting index, if any.
        ///
        /// All chunks strictly before this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
        /// chunk at this index isn't `ALL_ZEROS` too.
        #[inline]
        pub fn first(&self) -> Option<IndexOfChunkRaw> {
            (!self.ptr.is_empty()).then_some(IndexOfChunkRaw(0))
        }

        /// Returns the last interesting index, if any.
        ///
        /// All chunks strictly after this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
        /// chunk at this index isn't `ALL_ZEROS` too.
        #[inline]
        pub fn last(&self) -> Option<IndexOfChunkRaw> {
            self.ptr.len().checked_sub(1).map(IndexOfChunkRaw)
        }

        /// Returns the next interesting index at or after `index`, if any.
        ///
        /// Returns `None` when all chunks at or after `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is made
        /// that it returns `None` precisely when no further chunks have any set bit.
        #[inline]
        pub fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            //  Safety:
            //  -   `get_unchecked` relies on this method only returning in-bounds indexes.
            (index.0 < self.ptr.len()).then_some(index)
        }

        /// Returns the next interesting index at or before `index`, if any.
        ///
        /// Returns `None` when all chunks at or before `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is
        /// made that it returns `None` precisely when no prior chunks have any set bit.
        #[inline]
        pub fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            Some(index)
        }

        /// Sets the `BitChunkRaw` at the given index.
        ///
        /// On success, returns the previous chunk stored at `index`, or `ALL_ZEROS` if no such chunk existed. On error,
        /// `self` is left unchanged.
        ///
        /// Errors may be either transient or permnanent. For example, if the backing store is `[BitChunkRaw; 1]`, then any
        /// attempt to store at index `64` or greater is doomed to fail, whereas if the store is `Vec<BitChunkRaw>`, then any
        /// attempt to store beyond the current capacity of the vector may fail if the memory allocation fails at this point
        /// in time.
        #[inline]
        pub fn set(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError> {
            let Some(slot) = self.chunks_mut().get_mut(index.0) else {
                return self.set_slow(index, chunk);
            };

            Ok(mem::replace(slot, chunk))
        }

        /// Sets the `BitChunkRaw` at the given index.
        ///
        /// #   Safety
        ///
        /// `index` must be the index of a non `ALL_ZEROS` chunk, prior to this call.
        #[inline]
        unsafe fn set_unchecked(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) {
            //  Safety:
            //  -   `index` is within bounds, as per pre-condition.
            let slot = unsafe { self.chunks_mut().get_unchecked_mut(index.0) };

            *slot = chunk;
        }
    }

    //
    //  BitChunkViewRaw/Store (trait)
    //

    impl<A> BitChunkViewRaw for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        //
        //  Index access
        //

        #[inline]
        fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            self.get(index)
        }

        #[inline]
        unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
            //  Safety:
            //  -   Forward pre-conditions.
            unsafe { self.get_unchecked(index) }
        }

        //
        //  Index iteration
        //

        #[inline]
        fn first(&self) -> Option<IndexOfChunkRaw> {
            self.first()
        }

        #[inline]
        fn last(&self) -> Option<IndexOfChunkRaw> {
            self.last()
        }

        #[inline]
        fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            self.next_after(index)
        }

        #[inline]
        fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
            self.next_before(index)
        }
    }

    impl<A> BitChunkStoreRaw for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        #[inline]
        fn set(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError> {
            self.set(index, chunk)
        }

        #[inline]
        unsafe fn set_unchecked(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) {
            //  Safety: forward.
            unsafe { self.set_unchecked(index, chunk) }
        }
    }

    //  Safety:
    //
    //  -   The implementation of `BitChunkViewRaw` and `BitChunkStoreRaw` is faithful.
    //  -   The implementation of `BitChunkViewRaw` is one-pass.
    unsafe impl<A> TrustedBitChunkStoreRaw for DynamicBitChunkStore<A> where A: Allocator {}

    //
    //  Common traits
    //

    impl<A> Clone for DynamicBitChunkStore<A>
    where
        A: Allocator + Clone,
    {
        fn clone(&self) -> Self {
            //  Safety:
            //  -   `self.ptr` satisfies the Safety Invariants.
            let ptr = unsafe { Self::clone_raw(&self.allocator, self.ptr, self.ptr.len()) };

            //  Per post-condition of `clone_raw`, `ptr` satisfies the Safety Invariants.
            let ptr = ptr.expect("successful clone");

            let allocator = self.allocator.clone();

            Self { ptr, allocator }
        }
    }

    impl<A> Drop for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn drop(&mut self) {
            //  Safety:
            //  -   Liveness: `ptr` is currently allocated, unless it's empty, as per Safety Invariants.
            //  -   Allocator: `ptr` was allocated by `Self::allocate`, unless it empty, as per Safety Invariants.
            unsafe { Self::deallocate(&self.allocator, self.ptr) }
        }
    }

    impl<A> fmt::Debug for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
            f.debug_tuple("DynamicBitChunkStore").field(&self.chunks()).finish()
        }
    }

    impl<A> Default for DynamicBitChunkStore<A>
    where
        A: Allocator + Default,
    {
        fn default() -> Self {
            Self::new_in(A::default())
        }
    }

    impl<A> Eq for DynamicBitChunkStore<A> where A: Allocator {}

    impl<A> Hash for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn hash<H>(&self, state: &mut H)
        where
            H: Hasher,
        {
            self.chunks().hash(state);
        }
    }

    impl<A> Ord for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn cmp(&self, other: &Self) -> cmp::Ordering {
            if self.ptr.len() > other.ptr.len() {
                return other.cmp(self).reverse();
            }

            let (head, tail) = other.chunks().split_at_checked(self.ptr.len()).unwrap_or((&[], &[]));

            self.chunks().cmp(head).then_with(|| {
                let all_zeroes = tail.iter().all(|c| *c == BitChunkRaw::ALL_ZEROS);

                if all_zeroes {
                    cmp::Ordering::Equal
                } else {
                    cmp::Ordering::Less
                }
            })
        }
    }

    impl<A> PartialEq for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn eq(&self, other: &Self) -> bool {
            if self.ptr.len() > other.ptr.len() {
                return other.eq(self);
            }

            let (head, tail) = other.chunks().split_at_checked(self.ptr.len()).unwrap_or((&[], &[]));

            self.chunks() == head && tail.iter().all(|c| *c == BitChunkRaw::ALL_ZEROS)
        }
    }

    impl<A> PartialOrd for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    //  Safety:
    //  -   Just like a `Vec<BitChunkRaw, A>`.
    unsafe impl<A> Send for DynamicBitChunkStore<A> where A: Allocator + Send {}

    unsafe impl<A> Sync for DynamicBitChunkStore<A> where A: Allocator {}

    //
    //  Utilities implementation.
    //

    impl<A> DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        //  Creates a clone of `old`, with at least `n` or `old.len()` elements, whichever is greater.
        //
        //  #   Safety
        //
        //  -   `old` must satisfy the Safety Invariants.
        //  -   On success, the resulting pointer satisfies the Safety Invariants.
        #[inline(never)]
        unsafe fn clone_raw(
            allocator: &A,
            old: NonNull<[BitChunkRaw]>,
            n: usize,
        ) -> Result<NonNull<[BitChunkRaw]>, BitStoreError> {
            let min_size = cmp::max(old.len(), n);

            let new = Self::allocate(allocator, min_size)?;

            debug_assert!(new.len() >= old.len());

            if !old.is_empty() {
                let new = as_non_null_ptr(new);
                let src = as_non_null_ptr(old);

                //  Safety:
                //  -   `src` is valid for reads of `old.len()` items, as per Initialized Invariant.
                //  -   `new` is valid for writes of `new.len()` items, as per Initialized Invariant, and
                //      `new.len() >= old.len()`.
                //  -   `src` and `new` are properly aligned, as per Self-Allocated Invariant.
                //  -   `src` and `new` do not overlap, as `new` is a fresh allocation.
                unsafe { new.copy_from_nonoverlapping(src, old.len()) };
            }

            //  Safety:
            //  -   `new` satisfies the Safety Invariants.
            Ok(new)
        }

        #[inline(never)]
        fn set_slow(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError> {
            debug_assert!(index.0 >= self.ptr.len(), "spurious");

            let min_size = index.0.checked_add(1).ok_or(BitStoreError)?;

            //  Safety:
            //  -   `self.ptr` satisfies the Safety Invariants.
            //  -   `self.allocator` is its allocator.
            //  -   `min_size` >= `self.ptr.len()`.
            self.ptr = unsafe { Self::grow(&self.allocator, self.ptr, min_size)? };

            //  Safety:
            //  -   `index.0` is strictly less than `self.chunks_mut().len()`, as per `clone_raw`.
            let slot = unsafe { self.chunks_mut().get_unchecked_mut(index.0) };

            //  Must be all zeros, since `index.0` is strictly greater than the original `self.ptr.len()`.
            debug_assert_eq!(BitChunkRaw::ALL_ZEROS, *slot);

            *slot = chunk;

            Ok(BitChunkRaw::ALL_ZEROS)
        }
    }

    //
    //  Allocation implementation.
    //

    impl<A> DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn layout(n: usize) -> Result<Layout, BitStoreError> {
            debug_assert!(n > 0);

            Layout::array::<BitChunkRaw>(n).map_err(|_| BitStoreError)
        }

        //  #   Safety
        //
        //  -   On success, the resulting pointer satisfies the Safety Invariants.
        fn allocate(allocator: &A, n: usize) -> Result<NonNull<[BitChunkRaw]>, BitStoreError> {
            let n = n.checked_next_power_of_two().ok_or(BitStoreError)?;

            let layout = Self::layout(n)?;

            let ptr = allocator.allocate_zeroed(layout)?;

            let ptr = as_non_null_ptr(ptr);

            Ok(NonNull::slice_from_raw_parts(ptr.cast(), n))
        }

        //  #   Safety
        //
        //  -   `old` must satisfy the Safety Invariants.
        //  -   `allocator` must be the allocator used to allocate `old`.
        //  -   `n` must be greater than or equal to `old.len()`.
        //
        //  On success, the resulting pointer satisfies the Safety Invariants.
        unsafe fn grow(
            allocator: &A,
            old: NonNull<[BitChunkRaw]>,
            n: usize,
        ) -> Result<NonNull<[BitChunkRaw]>, BitStoreError> {
            if old.is_empty() {
                return Self::allocate(allocator, n);
            }

            debug_assert!(n >= old.len());

            let n = n.checked_next_power_of_two().ok_or(BitStoreError)?;

            let old_layout = Self::layout(old.len())?;
            let new_layout = Self::layout(n)?;

            let ptr = {
                let old = as_non_null_ptr(old);

                //  Safety:
                //  -   Liveness: `old` is live, as it satifies the Safety Invariants and is non-empty.
                //  -   Selfness: `old` was allocated by `allocator`, as per pre-condition.
                //  -   Layout: `old_layout` matches the layout of `old`, as per the Safety Invariants.
                //  -   Growth: `new_layout.size()` >= `old_layout.size()`, as `n` >= `old.len()`,
                //      `checked_next_power_of_two` result is >= to its argument, and `layout` is monotonically growing.
                unsafe { allocator.grow_zeroed(old.cast(), old_layout, new_layout)? }
            };

            let ptr = as_non_null_ptr(ptr);

            Ok(NonNull::slice_from_raw_parts(ptr.cast(), n))
        }

        //  #   Safety
        //
        //  -   Liveness: `ptr` is currently allocated, unless it's empty.
        //  -   Allocator: `ptr` was allocated by `Self::allocate`, unless it empty.
        unsafe fn deallocate(allocator: &A, ptr: NonNull<[BitChunkRaw]>) {
            //  #   Safety
            //
            //  -   Liveness: `ptr` is currently allocated.
            //  -   Allocator: `ptr` was allocated by `Self::allocate`.
            #[inline(never)]
            unsafe fn do_deallocate<A>(allocator: &A, ptr: NonNull<[BitChunkRaw]>)
            where
                A: Allocator,
            {
                let layout = DynamicBitChunkStore::<A>::layout(ptr.len());

                #[cfg(debug_assertions)]
                let layout = layout.expect("valid layout");

                //  Safety:
                //  -   Valid since `ptr` was allocated by `Self::allocate` as per the Allocator pre-condition,
                //      which cannot succeed without `Self::layout`, a pure function, succeeding.
                #[cfg(not(debug_assertions))]
                let layout = unsafe { layout.unwrap_unchecked() };

                let ptr = as_non_null_ptr(ptr).cast();

                //  Safety:
                //  -   `ptr` is currently allocated, as per Liveness pre-condition.
                //  -   `layout` is the same as used for allocation, as per Allocator pre-condition.
                unsafe { allocator.deallocate(ptr, layout) }
            }

            if ptr.is_empty() {
                return;
            }

            //  Safety:
            //  -   Forward Liveness & Allocator pre-conditions.
            unsafe { do_deallocate(allocator, ptr) };
        }
    }

    //  FIXME: use `NonNull<[T]>::as_non_null_ptr` when stable.
    fn as_non_null_ptr<T>(mut ptr: NonNull<[T]>) -> NonNull<T> {
        //  Not sure if that's properly dereferenceable, despite the 0-size, so special-case it.
        if ptr.is_empty() {
            return NonNull::dangling();
        }

        //  Safety:
        //  -   Formally speaking, the above function should be `unsafe`. That's rather unpalatable for a
        //      work-around for a safe function, so we're going to take a leap of faith.
        //      It's stupid, I hate it, you hate it, we all really need `as_non_null_ptr` to get stabilized.
        let slice = unsafe { ptr.as_mut() };

        let ptr = slice.as_mut_ptr();

        //  Safety:
        //  -   `ptr` was obtained from a `NonNull<[T]>` so it is non-null.
        unsafe { NonNull::new_unchecked(ptr) }
    }
} // mod dynamic

#[cfg(all(feature = "alloc", test))]
mod dynamic_tests {
    use super::*;

    type DynamicBitChunkStore = super::dynamic::DynamicBitChunkStore;

    #[test]
    fn empty() {
        let store = DynamicBitChunkStore::default();

        assert_eq!(BitChunkRaw::ALL_ZEROS, store.get(IndexOfChunkRaw(0)));

        assert_eq!(None, store.first());
        assert_eq!(None, store.last());
    }

    #[test]
    fn single() {
        const SPECIAL: BitChunkRaw = BitChunkRaw(0b1001);
        const SPECIAL_INDEX: usize = 3;

        let mut store = DynamicBitChunkStore::default();

        let previous = store.set(IndexOfChunkRaw(SPECIAL_INDEX), SPECIAL).expect("success");

        assert_eq!(BitChunkRaw::ALL_ZEROS, previous);

        assert_elements(
            &store,
            &[
                BitChunkRaw::ALL_ZEROS,
                BitChunkRaw::ALL_ZEROS,
                BitChunkRaw::ALL_ZEROS,
                SPECIAL,
            ],
        );
    }

    #[test]
    fn clone() {
        const SPECIAL: BitChunkRaw = BitChunkRaw(0b1001);
        const SPECIAL_INDEX: usize = 3;

        let mut store = DynamicBitChunkStore::default();

        store.set(IndexOfChunkRaw(SPECIAL_INDEX), SPECIAL).expect("success");

        let clone = store.clone();

        assert_elements(
            &clone,
            &[
                BitChunkRaw::ALL_ZEROS,
                BitChunkRaw::ALL_ZEROS,
                BitChunkRaw::ALL_ZEROS,
                SPECIAL,
            ],
        );
    }

    #[track_caller]
    fn assert_elements(store: &DynamicBitChunkStore, expected: &[BitChunkRaw]) {
        assert_eq!(Some(IndexOfChunkRaw(0)), store.first(), "first");
        assert_eq!(Some(IndexOfChunkRaw(expected.len() - 1)), store.last(), "last");

        for (index, chunk) in expected.iter().enumerate() {
            assert_eq!(*chunk, store.get(IndexOfChunkRaw(index)), "get({index})");
        }

        for i in 0..expected.len() {
            assert_eq!(
                Some(IndexOfChunkRaw(i)),
                store.next_before(IndexOfChunkRaw(i)),
                "next_before({i})"
            );
            assert_eq!(
                Some(IndexOfChunkRaw(i)),
                store.next_after(IndexOfChunkRaw(i)),
                "next_after({i})"
            );
        }
    }
} // mod dynamic_tests
