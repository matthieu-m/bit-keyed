//  Implementation of allocator abstraction, depending on enabled features.
//
//  -   If only `alloc` is used, then uses the free-standing `alloc::alloc::{alloc_zeroed, dealloc}`.
//  -   If `allocator_api` is used, then uses the appropriate `Allocator` functions.

use core::{alloc::Layout, ptr::NonNull};

use alloc::alloc;

use crate::utils::BitStoreError;

//  Abstraction over global allocator or `Allocator`.
pub(crate) trait BitAllocator {
    //  Attempts to allocate a block of memory satisfying `layout`.
    //
    //  Returns an error if allocation fails.
    //
    //  The resulting memory should be considered uninitialized.
    //
    //  #   Safety
    //
    //  -   Non-Zero: `layout` must have a non-zero size.
    #[expect(dead_code)]
    unsafe fn allocate(&self, layout: Layout) -> Result<NonNull<u8>, BitStoreError>;

    //  Attempts to allocate a block of memory satisfying `layout`.
    //
    //  Returns an error if allocation fails.
    //
    //  The resulting memory is guaranteed to be zero-initialized.
    //
    //  #   Safety
    //
    //  -   Non-Zero: `layout` must have a non-zero size.
    unsafe fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, BitStoreError>;

    //  Deallocates the block of memory `ptr`, with the given `layout`.
    //
    //  #   Safety
    //
    //  -   Liveness: `ptr` must still be allocated.
    //  -   Selfness: `ptr` must have been allocated by `self`.
    //  -   Layout: `layout` must match the layout passed to `self.allocate(...)` or `self.allocate_zeroed(...)`.
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}

impl BitAllocator for () {
    unsafe fn allocate(&self, layout: Layout) -> Result<NonNull<u8>, BitStoreError> {
        //  Safety:
        //  -   `layout` is non-zero, as per Non-Zero pre-condition.
        let ptr = unsafe { alloc::alloc(layout) };

        NonNull::new(ptr).ok_or(BitStoreError)
    }

    unsafe fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, BitStoreError> {
        //  Safety:
        //  -   `layout` is non-zero, as per Non-Zero pre-condition.
        let ptr = unsafe { alloc::alloc_zeroed(layout) };

        NonNull::new(ptr).ok_or(BitStoreError)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        //  Safety:
        //  -   `ptr` is currently allocated, as per Liveness pre-condition.
        //  -   `ptr` was allocated via this allocator, as per Selfness pre-condition.
        //  -   `layout` matches the layout passed to the allocation function, as per Layout pre-condition.
        unsafe { alloc::dealloc(ptr.as_ptr(), layout) };
    }
}

#[cfg(feature = "allocator_api")]
pub(crate) use adapter::BitAllocatorAdapter;

#[cfg(feature = "allocator_api")]
mod adapter {
    use core::{alloc::Layout, ptr::NonNull};

    use alloc::alloc::{AllocError, Allocator};

    use super::{BitAllocator, BitStoreError};

    //  Wrapper to convert from `Allocator` to `BitAllocator` API.
    #[derive(Clone, Copy, Default)]
    pub(crate) struct BitAllocatorAdapter<A>(A);

    impl<A> BitAllocator for BitAllocatorAdapter<A>
    where
        A: Allocator,
    {
        unsafe fn allocate(&self, layout: Layout) -> Result<NonNull<u8>, BitStoreError> {
            Self::translate(self.0.allocate(layout))
        }

        unsafe fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<u8>, BitStoreError> {
            Self::translate(self.0.allocate_zeroed(layout))
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            //  Safety:
            //  -   `ptr` is currently allocated, as per Liveness pre-condition.
            //  -   `ptr` was allocated via this allocator, as per Selfness pre-condition.
            //  -   `layout` matches the layout passed to the allocation function, as per Layout pre-condition.
            unsafe { self.0.deallocate(ptr, layout) }
        }
    }

    impl<A> BitAllocatorAdapter<A> {
        fn translate(ptr: Result<NonNull<[u8]>, AllocError>) -> Result<NonNull<u8>, BitStoreError> {
            let ptr = ptr.map_err(|_| BitStoreError)?;

            Ok(Self::as_non_null_ptr(ptr))
        }

        //  FIXME: use `NonNull<[T]>::as_non_null_ptr` when stable.
        fn as_non_null_ptr<T>(mut ptr: NonNull<[T]>) -> NonNull<T> {
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
    }
} // mod adapter
