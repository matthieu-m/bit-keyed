//  See the various traits.

use core::mem;

use crate::utils::{BitChunk, BitStoreError, IndexOfChunk};

//
//  API
//

/// A trait for read-only access to a collection of `BitChunk`.
///
/// The trait is pre-implemented for `[BitChunk; N]`, and exists to allow for alternative representations, such as
/// compressed sets, or sparse sets.
pub trait BitChunkView {
    //
    //  Index access
    //

    /// Returns the `BitChunk` at the given index.
    ///
    /// If `index` is unknown, an `ALL_ZEROS` chunk should be returned.
    fn get(&self, index: IndexOfChunk) -> BitChunk;

    /// Returns the `BitChunk` at the given index.
    ///
    /// #   Safety
    ///
    /// The caller guarantees that `index` was either returned by a call to `self.first()`, `self.last()`,
    /// `self.next_after(...)`, or `self.next_before(...)`.
    #[inline]
    unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
        self.get(index)
    }

    //
    //  Index iteration
    //

    /// Returns the first interesting index, if any.
    ///
    /// All chunks strictly before this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
    /// chunk at this index isn't `ALL_ZEROS` too.
    fn first(&self) -> Option<IndexOfChunk>;

    /// Returns the last interesting index, if any.
    ///
    /// All chunks strictly after this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
    /// chunk at this index isn't `ALL_ZEROS` too.
    fn last(&self) -> Option<IndexOfChunk>;

    /// Returns the next interesting index at or after `index`, if any.
    ///
    /// Returns `None` when all chunks at or after `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is made
    /// that it returns `None` precisely when no further chunks have any set bit.
    fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk>;

    /// Returns the next interesting index at or before `index`, if any.
    ///
    /// Returns `None` when all chunks at or before `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is
    /// made that it returns `None` precisely when no prior chunks have any set bit.
    fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk>;
}

/// A trait for write access to a collection of `BitChunk`.
///
/// The trait is pre-implemented for `[BitChunk; N]`, and exists to allow for alternative representations, such as
/// compressed sets, or sparse sets.
pub trait BitChunkStore: BitChunkView {
    /// Sets the `BitChunk` at the given index.
    ///
    /// On success, returns the previous chunk stored at `index`, or `ALL_ZEROS` if no such chunk existed. On error,
    /// `self` is left unchanged.
    ///
    /// Errors may be either transient or permnanent. For example, if the backing store is `[BitChunk; 1]`, then any
    /// attempt to store at index `64` or greater is doomed to fail, whereas if the store is `Vec<BitChunk>`, then any
    /// attempt to store beyond the current capacity of the vector may fail if the memory allocation fails at this point
    /// in time.
    fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError>;

    /// Sets the `BitChunk` at the given index.
    ///
    /// #   Safety
    ///
    /// `index` must be the index of a non `ALL_ZEROS` chunk, prior to this call.
    #[inline]
    unsafe fn set_unchecked(&mut self, index: IndexOfChunk, chunk: BitChunk) {
        let _result = self.set(index, chunk);

        debug_assert!(_result.is_ok());
    }
}

/// A marker trait to guarantee that the store faithfully executes reads & writes.
///
/// #   Safety
///
/// -   Faithful: implementations guarantee that `self.get(index)` return an equal `BitChunk` to the last for which
///     `self.set(index, ...)` succeeded.
/// -   One-pass: implementations guarantee that `self.next_after(index)`, resp. `self.next_before(index)`, return an
///     index that is greater than or equal to `index`, resp. less than or equal to `index`.
pub unsafe trait TrustedBitChunkStore {}

//
//  Implementation for references.
//

impl<V> BitChunkView for &V
where
    V: BitChunkView,
{
    fn get(&self, index: IndexOfChunk) -> BitChunk {
        (**self).get(index)
    }

    unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
        //  Safety: forwarded.
        unsafe { (**self).get_unchecked(index) }
    }

    fn first(&self) -> Option<IndexOfChunk> {
        (**self).first()
    }

    fn last(&self) -> Option<IndexOfChunk> {
        (**self).last()
    }

    fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        (**self).next_after(index)
    }

    fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        (**self).next_before(index)
    }
}

//  Safety: forward.
unsafe impl<V> TrustedBitChunkStore for &V where V: BitChunkView + TrustedBitChunkStore {}

impl<V> BitChunkView for &mut V
where
    V: BitChunkView,
{
    fn get(&self, index: IndexOfChunk) -> BitChunk {
        (**self).get(index)
    }

    unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
        //  Safety: forwarded.
        unsafe { (**self).get_unchecked(index) }
    }

    fn first(&self) -> Option<IndexOfChunk> {
        (**self).first()
    }

    fn last(&self) -> Option<IndexOfChunk> {
        (**self).last()
    }

    fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        (**self).next_after(index)
    }

    fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        (**self).next_before(index)
    }
}

impl<V> BitChunkStore for &mut V
where
    V: BitChunkStore,
{
    fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
        (**self).set(index, chunk)
    }

    unsafe fn set_unchecked(&mut self, index: IndexOfChunk, chunk: BitChunk) {
        //  Safety: forward.
        unsafe { (**self).set_unchecked(index, chunk) };
    }
}

//  Safety: forward.
unsafe impl<V> TrustedBitChunkStore for &mut V where V: BitChunkStore + TrustedBitChunkStore {}

//
//  Implementation for [BitChunk; N].
//

mod array {
    use super::*;

    impl<const N: usize> BitChunkView for [BitChunk; N] {
        //
        //  Index access
        //

        #[inline]
        fn get(&self, index: IndexOfChunk) -> BitChunk {
            <[BitChunk]>::get(self, index.0).copied().unwrap_or(BitChunk::ALL_ZEROS)
        }

        #[inline]
        unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
            debug_assert!(index.0 < self.len(), "{} >= {}", index.0, self.len());

            //  Safety:
            //  -   `index.0` is in-bounds, as the caller guarantees that `index` was returned by `self.first()`,
            //      `self.last()`, `self.next_after(...)`, or `self.next_before(...)`, and those methods only return
            //      in-bounds indexes.
            unsafe { *<[BitChunk]>::get_unchecked(self, index.0) }
        }

        //
        //  Index iteration
        //

        #[inline]
        fn first(&self) -> Option<IndexOfChunk> {
            (!self.is_empty()).then_some(IndexOfChunk(0))
        }

        #[inline]
        fn last(&self) -> Option<IndexOfChunk> {
            self.len().checked_sub(1).map(IndexOfChunk)
        }

        #[inline]
        fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            //  Safety:
            //  -   `get_unchecked` relies on this method only returning in-bounds indexes.
            (index.0 < N).then_some(index)
        }

        #[inline]
        fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            Some(index)
        }
    }

    impl<const N: usize> BitChunkStore for [BitChunk; N] {
        #[inline]
        fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
            let slot = self.get_mut(index.0).ok_or(BitStoreError)?;

            Ok(mem::replace(slot, chunk))
        }
    }

    //  Safety:
    //
    //  -   The implementation of `BitChunkView` and `BitChunkStore` is faithful.
    //  -   The implementation of `BitChunkView` is one-pass.
    unsafe impl<const N: usize> TrustedBitChunkStore for [BitChunk; N] {}
} // mod array

//
//  Implementation for DynamicBitChunkStore.
//

#[cfg(all(feature = "alloc", not(feature = "allocator_api")))]
pub(super) mod dynamic {
    use core::cmp;

    use super::dynamic_core::DynamicBitChunkCore;

    use super::*;

    /// Heap allocated implementation of a `BitChunkStore` and related traits.
    ///
    /// The implementation uses exponential growth.
    #[derive(Clone, Debug, Default)]
    pub struct DynamicBitChunkStore(DynamicBitChunkCore<()>);

    impl DynamicBitChunkStore {
        /// Returns a new, empty, instance.
        pub const fn new() -> Self {
            Self(DynamicBitChunkCore::new_in(()))
        }
    }

    //
    //  BitChunkView/Store
    //

    impl BitChunkView for DynamicBitChunkStore {
        //
        //  Index access
        //

        #[inline]
        fn get(&self, index: IndexOfChunk) -> BitChunk {
            self.0.get(index)
        }

        #[inline]
        unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
            //  Safety:
            //  -   Forward pre-conditions.
            unsafe { self.0.get_unchecked(index) }
        }

        //
        //  Index iteration
        //

        #[inline]
        fn first(&self) -> Option<IndexOfChunk> {
            self.0.first()
        }

        #[inline]
        fn last(&self) -> Option<IndexOfChunk> {
            self.0.last()
        }

        #[inline]
        fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            self.0.next_after(index)
        }

        #[inline]
        fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            self.0.next_before(index)
        }
    }

    impl BitChunkStore for DynamicBitChunkStore {
        #[inline]
        fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
            self.0.set(index, chunk)
        }
    }

    //  Safety:
    //
    //  -   The implementation of `BitChunkView` and `BitChunkStore` is faithful.
    //  -   The implementation of `BitChunkView` is one-pass.
    unsafe impl TrustedBitChunkStore for DynamicBitChunkStore {}

    //
    //  Common traits
    //

    impl Eq for DynamicBitChunkStore {}

    impl Ord for DynamicBitChunkStore {
        fn cmp(&self, other: &Self) -> cmp::Ordering {
            self.0.cmp(&other.0)
        }
    }

    impl PartialEq for DynamicBitChunkStore {
        fn eq(&self, other: &Self) -> bool {
            self.0.eq(&other.0)
        }
    }

    impl PartialOrd for DynamicBitChunkStore {
        fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
} // mod dynamic

#[cfg(feature = "allocator_api")]
pub(super) mod dynamic {
    use core::{cmp, fmt};

    use alloc::alloc::{Allocator, Global};

    use crate::utils::allocator::BitAllocatorAdapter;

    use super::dynamic_core::DynamicBitChunkCore;

    use super::*;

    /// Heap allocated implementation of a `BitChunkStore` and related traits.
    ///
    /// The implementation uses exponential growth.
    #[derive(Clone, Default)]
    pub struct DynamicBitChunkStore<A: Allocator = Global>(DynamicBitChunkCore<BitAllocatorAdapter<A>>);

    //
    //  BitChunkView/Store
    //

    impl<A> BitChunkView for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        //
        //  Index access
        //

        #[inline]
        fn get(&self, index: IndexOfChunk) -> BitChunk {
            self.0.get(index)
        }

        #[inline]
        unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
            //  Safety:
            //  -   Forward pre-conditions.
            unsafe { self.0.get_unchecked(index) }
        }

        //
        //  Index iteration
        //

        #[inline]
        fn first(&self) -> Option<IndexOfChunk> {
            self.0.first()
        }

        #[inline]
        fn last(&self) -> Option<IndexOfChunk> {
            self.0.last()
        }

        #[inline]
        fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            self.0.next_after(index)
        }

        #[inline]
        fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            self.0.next_before(index)
        }
    }

    impl<A> BitChunkStore for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        #[inline]
        fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
            self.0.set(index, chunk)
        }
    }

    //  Safety:
    //
    //  -   The implementation of `BitChunkView` and `BitChunkStore` is faithful.
    //  -   The implementation of `BitChunkView` is one-pass.
    unsafe impl<A> TrustedBitChunkStore for DynamicBitChunkStore<A> where A: Allocator {}

    //
    //  Common traits
    //

    impl<A> fmt::Debug for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
            f.debug_tuple("DynamicBitChunkStore").field(&self.0).finish()
        }
    }

    impl<A> Eq for DynamicBitChunkStore<A> where A: Allocator {}

    impl<A> Ord for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn cmp(&self, other: &Self) -> cmp::Ordering {
            self.0.cmp(&other.0)
        }
    }

    impl<A> PartialEq for DynamicBitChunkStore<A>
    where
        A: Allocator,
    {
        fn eq(&self, other: &Self) -> bool {
            self.0.eq(&other.0)
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
} // mod dynamic

#[cfg(all(feature = "alloc", test))]
mod dynamic_tests {
    use super::*;

    #[cfg(not(feature = "allocator_api"))]
    use super::dynamic::DynamicBitChunkStore;

    #[cfg(feature = "allocator_api")]
    type DynamicBitChunkStore = super::dynamic::DynamicBitChunkStore;

    #[test]
    fn empty() {
        let store = DynamicBitChunkStore::default();

        assert_eq!(BitChunk::ALL_ZEROS, store.get(IndexOfChunk(0)));

        assert_eq!(None, store.first());
        assert_eq!(None, store.last());
    }

    #[test]
    fn single() {
        const SPECIAL: BitChunk = BitChunk(0b1001);
        const SPECIAL_INDEX: usize = 3;

        let mut store = DynamicBitChunkStore::default();

        let previous = store.set(IndexOfChunk(SPECIAL_INDEX), SPECIAL).expect("success");

        assert_eq!(BitChunk::ALL_ZEROS, previous);

        assert_elements(
            &store,
            &[BitChunk::ALL_ZEROS, BitChunk::ALL_ZEROS, BitChunk::ALL_ZEROS, SPECIAL],
        );
    }

    #[test]
    fn clone() {
        const SPECIAL: BitChunk = BitChunk(0b1001);
        const SPECIAL_INDEX: usize = 3;

        let mut store = DynamicBitChunkStore::default();

        store.set(IndexOfChunk(SPECIAL_INDEX), SPECIAL).expect("success");

        let clone = store.clone();

        assert_elements(
            &clone,
            &[BitChunk::ALL_ZEROS, BitChunk::ALL_ZEROS, BitChunk::ALL_ZEROS, SPECIAL],
        );
    }

    #[track_caller]
    fn assert_elements(store: &DynamicBitChunkStore, expected: &[BitChunk]) {
        assert_eq!(Some(IndexOfChunk(0)), store.first(), "first");
        assert_eq!(Some(IndexOfChunk(expected.len() - 1)), store.last(), "last");

        for (index, chunk) in expected.iter().enumerate() {
            assert_eq!(*chunk, store.get(IndexOfChunk(index)), "get({index})");
        }

        for i in 0..expected.len() {
            assert_eq!(
                Some(IndexOfChunk(i)),
                store.next_before(IndexOfChunk(i)),
                "next_before({i})"
            );
            assert_eq!(
                Some(IndexOfChunk(i)),
                store.next_after(IndexOfChunk(i)),
                "next_after({i})"
            );
        }
    }
} // mod dynamic_tests

//
//  Helpers for dynamic
//

#[cfg(feature = "alloc")]
mod dynamic_core {
    use core::{alloc::Layout, cmp, fmt, ptr::NonNull};

    use crate::utils::BitAllocator;

    use super::*;

    //  Heap allocated implementation of a `BitChunkStore` and related traits.
    pub(super) struct DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        //  Safety Invariants:
        //  -   Empty Dangling: if an empty slice, it is dangling.
        //  -   Self-Allocated: if not empty, it is allocated by `Self::allocate`.
        //  -   Initialized: if not empty, all `self.0.len()` items of the slice are initialized.
        ptr: NonNull<[BitChunk]>,
        allocator: A,
    }

    impl<A> DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        /// Returns a new, empty, instance.
        pub(super) const fn new_in(allocator: A) -> Self {
            //  Safety Invariant:
            //  -   Empty Dangling: create an empty slice, with a dangling pointer.
            let ptr = NonNull::slice_from_raw_parts(NonNull::dangling(), 0);

            Self { ptr, allocator }
        }
    }

    //
    //  BitChunkView/Store
    //

    impl<A> DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        //
        //  Index access
        //

        #[inline]
        pub(super) fn get(&self, index: IndexOfChunk) -> BitChunk {
            self.as_slice().get(index.0).copied().unwrap_or(BitChunk::ALL_ZEROS)
        }

        #[inline]
        pub(super) unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
            debug_assert!(index.0 < self.ptr.len(), "{} >= {}", index.0, self.ptr.len());

            //  Safety:
            //  -   `index.0` is in-bounds, as the caller guarantees that `index` was returned by `self.first()`,
            //      `self.last()`, `self.next_after(...)`, or `self.next_before(...)`, and those methods only return
            //      in-bounds indexes.
            unsafe { *self.as_slice().get_unchecked(index.0) }
        }

        //
        //  Index iteration
        //

        #[inline]
        pub(super) fn first(&self) -> Option<IndexOfChunk> {
            (!self.ptr.is_empty()).then_some(IndexOfChunk(0))
        }

        #[inline]
        pub(super) fn last(&self) -> Option<IndexOfChunk> {
            self.ptr.len().checked_sub(1).map(IndexOfChunk)
        }

        #[inline]
        pub(super) fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            //  Safety:
            //  -   `get_unchecked` relies on this method only returning in-bounds indexes.
            (index.0 < self.ptr.len()).then_some(index)
        }

        #[inline]
        pub(super) fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
            Some(index)
        }

        #[inline]
        pub(super) fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
            let Some(slot) = self.as_mut_slice().get_mut(index.0) else {
                return self.set_slow(index, chunk);
            };

            Ok(mem::replace(slot, chunk))
        }
    }

    //
    //  Common traits
    //

    impl<A> Clone for DynamicBitChunkCore<A>
    where
        A: BitAllocator + Clone,
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

    impl<A> Drop for DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        fn drop(&mut self) {
            //  Safety:
            //  -   Liveness: `ptr` is currently allocated, unless it's empty, as per Safety Invariants.
            //  -   Allocator: `ptr` was allocated by `Self::allocate`, unless it empty, as per Safety Invariants.
            unsafe { Self::deallocate(&self.allocator, self.ptr) }
        }
    }

    impl<A> fmt::Debug for DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
            f.debug_tuple("DynamicBitChunkCore").field(&self.as_slice()).finish()
        }
    }

    impl<A> Default for DynamicBitChunkCore<A>
    where
        A: BitAllocator + Default,
    {
        fn default() -> Self {
            Self::new_in(A::default())
        }
    }

    impl<A> Eq for DynamicBitChunkCore<A> where A: BitAllocator {}

    impl<A> Ord for DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        fn cmp(&self, other: &Self) -> cmp::Ordering {
            if self.ptr.len() > other.ptr.len() {
                return other.cmp(self).reverse();
            }

            let (head, tail) = other.as_slice().split_at_checked(self.ptr.len()).unwrap_or((&[], &[]));

            self.as_slice().cmp(head).then_with(|| {
                let all_zeroes = tail.iter().all(|c| *c == BitChunk::ALL_ZEROS);

                if all_zeroes {
                    cmp::Ordering::Equal
                } else {
                    cmp::Ordering::Less
                }
            })
        }
    }

    impl<A> PartialEq for DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        fn eq(&self, other: &Self) -> bool {
            if self.ptr.len() > other.ptr.len() {
                return other.eq(self);
            }

            let (head, tail) = other.as_slice().split_at_checked(self.ptr.len()).unwrap_or((&[], &[]));

            self.as_slice() == head && tail.iter().all(|c| *c == BitChunk::ALL_ZEROS)
        }
    }

    impl<A> PartialOrd for DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    //  Safety:
    //  -   Just like a `Vec<BitChunk, A>`.
    unsafe impl<A> Send for DynamicBitChunkCore<A> where A: BitAllocator + Send {}

    unsafe impl<A> Sync for DynamicBitChunkCore<A> where A: BitAllocator {}

    //
    //  Utilities implementation.
    //

    impl<A> DynamicBitChunkCore<A>
    where
        A: BitAllocator,
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
            old: NonNull<[BitChunk]>,
            n: usize,
        ) -> Result<NonNull<[BitChunk]>, BitStoreError> {
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

        #[inline]
        const fn as_slice(&self) -> &[BitChunk] {
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

        #[inline]
        const fn as_mut_slice(&mut self) -> &mut [BitChunk] {
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

        #[inline(never)]
        fn set_slow(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
            debug_assert!(index.0 >= self.ptr.len(), "spurious");

            let min_size = index.0.checked_add(1).ok_or(BitStoreError)?;

            //  Safety:
            //  -   `self.ptr` satisfies the Safety Invariants.
            let new = unsafe { Self::clone_raw(&self.allocator, self.ptr, min_size)? };

            let old = mem::replace(&mut self.ptr, new);

            //  Safety:
            //  -   Liveness: `old` is live or empty, until now, as per the Safety Invariants.
            //  -   Selfness: `old` was allocated by `Self::allocate` or is empty, as per the Safety Invariants.
            unsafe { Self::deallocate(&self.allocator, old) };

            debug_assert!(index.0 < self.as_mut_slice().len());

            //  Safety:
            //  -   `index.0` is strictly less than `self.as_mut_slice().len()`, as per `clone_raw`.
            let slot = unsafe { self.as_mut_slice().get_unchecked_mut(index.0) };

            //  Must be all zeros, since `index.0` is strictly greater than the original `self.ptr.len()`.
            debug_assert_eq!(BitChunk::ALL_ZEROS, *slot);

            *slot = chunk;

            Ok(BitChunk::ALL_ZEROS)
        }
    }

    //
    //  Allocation implementation.
    //

    impl<A> DynamicBitChunkCore<A>
    where
        A: BitAllocator,
    {
        fn layout(n: usize) -> Result<Layout, BitStoreError> {
            debug_assert!(n > 0);

            Layout::array::<BitChunk>(n).map_err(|_| BitStoreError)
        }

        //  #   Safety
        //
        //  -   On success, the resulting pointer satisfies the Safety Invariants.
        fn allocate(allocator: &A, n: usize) -> Result<NonNull<[BitChunk]>, BitStoreError> {
            let n = n.checked_next_power_of_two().ok_or(BitStoreError)?;

            let layout = Self::layout(n)?;

            //  Safety:
            //  -   Layout has a non-zero size, as `checked_next_power_of_two` returns 1 or higher.
            let ptr = unsafe { allocator.allocate_zeroed(layout)? };

            Ok(NonNull::slice_from_raw_parts(ptr.cast(), n))
        }

        //  #   Safety
        //
        //  -   Liveness: `ptr` is currently allocated, unless it's empty.
        //  -   Allocator: `ptr` was allocated by `Self::allocate`, unless it empty.
        unsafe fn deallocate(allocator: &A, ptr: NonNull<[BitChunk]>) {
            //  #   Safety
            //
            //  -   Liveness: `ptr` is currently allocated.
            //  -   Allocator: `ptr` was allocated by `Self::allocate`.
            #[inline(never)]
            unsafe fn do_deallocate<A>(allocator: &A, ptr: NonNull<[BitChunk]>)
            where
                A: BitAllocator,
            {
                let layout = DynamicBitChunkCore::<A>::layout(ptr.len());

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
    fn as_non_null_ptr(mut ptr: NonNull<[BitChunk]>) -> NonNull<BitChunk> {
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
        //  -   `ptr` was obtained from a `NonNull<[BitChunk]>` so it is non-null.
        unsafe { NonNull::new_unchecked(ptr) }
    }
} // mod dynamic_core
