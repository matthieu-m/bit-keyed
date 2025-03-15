//! Shim for unstable allocator API.
//!
//! -   If only `alloc` is used, then duplicates the allocator API.
//! -   If `allocator_api` is used, then forwards the allocator API.

#[cfg(feature = "allocator_api")]
pub use alloc::alloc::{AllocError, Allocator, Global};

#[cfg(not(feature = "allocator_api"))]
pub use shim::{AllocError, Allocator, Global};

#[cfg(not(feature = "allocator_api"))]
pub(super) mod shim {
    use core::{
        alloc::Layout,
        error, fmt,
        ptr::{self, NonNull},
    };

    use alloc::alloc;

    /// The AllocError error indicates an allocation failure that may be due to resource exhaustion or to something
    /// wrong when combining the given input arguments with this allocator.
    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    pub struct AllocError;

    impl fmt::Display for AllocError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
            f.write_str("memory allocation failed")
        }
    }

    impl error::Error for AllocError {}

    /// An implementation of Allocator can allocate, grow, shrink, and deallocate arbitrary blocks of data described via
    /// Layout.
    ///
    /// #   Safety
    ///
    /// -   Liveness: memory blocks that are currently allocated by an allocator must point to valid memory until either
    ///     they are deallocated or the `Allocator` and all its clones are dropped.
    /// -   Independence: moving an allocator must not invalidate memory blocks returned from it.
    /// -   Shallowness: a copied or cloned allocator must behave like the original allocator.
    pub unsafe trait Allocator {
        /// Attempts to allocate a block of memory.
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

        /// Behaves like allocate, but also ensures that the returned memory is zero-initialized.
        fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            let ptr = self.allocate(layout)?;

            {
                let len = ptr.len();
                let ptr = as_non_null_ptr(ptr);

                //  Safety:
                //  -   `ptr.get()` is valid for writes of `ptr.len()`.
                //  -   `ptr.get()` is trivially properly aligned, given its alignment of 1.
                unsafe { ptr.as_ptr().write_bytes(0, len) }
            }

            Ok(ptr)
        }

        /// Deallocates the memory referenced by ptr.
        ///
        /// #   Safety
        ///
        /// -   Liveness: `ptr` must still be allocated.
        /// -   Selfness: `ptr` must have been allocated by `self`.
        /// -   Layout: `layout` must match the layout passed to `self.allocate(...)` or `self.allocate_zeroed(...)`
        ///     when allocating `ptr`.
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);

        /// Attempts to extend the memory block.
        ///
        /// #   Safety
        ///
        /// -   Liveness: `ptr` must still be allocated.
        /// -   Selfness: `ptr` must have been allocated by `self`.
        /// -   Layout: `old_layout` must match the layout passed to `self.allocate(...)` or `self.allocate_zeroed(...)`
        ///     when allocating `ptr`.
        /// -   Growth: `new_layout.size()` must be greater than or equal to `old_layout.size()`.
        unsafe fn grow(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            debug_assert!(new_layout.size() >= old_layout.size());

            let new_ptr = self.allocate(new_layout)?;

            {
                let new_ptr = as_non_null_ptr(new_ptr);

                //  Safety:
                //  -   `ptr` is valid for `old_layout.size()` reads, as per Liveness & Layout pre-conditions.
                //  -   `new_ptr` is valid for `old_layout.size()` writes, as per Layout pre-condition.
                //  -   `ptr` and `new_ptr` point to non-overlapping blocks, as `new_ptr` is freshly allocated.
                unsafe { ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_layout.size()) };

                //  Safety:
                //  -   Liveness: as per Liveness pre-condition.
                //  -   Selfness: as per Selfness pre-condition.
                //  -   Layout: as per Layout pre-condition.
                unsafe { self.deallocate(ptr, old_layout) };
            }

            Ok(new_ptr)
        }

        /// Attempts to extend the memory block.
        ///
        /// #   Safety
        ///
        /// -   Liveness: `ptr` must still be allocated.
        /// -   Selfness: `ptr` must have been allocated by `self`.
        /// -   Layout: `old_layout` must match the layout passed to `self.allocate(...)` or `self.allocate_zeroed(...)`
        ///     when allocating `ptr`.
        /// -   Growth: `new_layout.size()` must be greater than or equal to `old_layout.size()`.
        unsafe fn grow_zeroed(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            debug_assert!(new_layout.size() >= old_layout.size());

            let new_ptr = self.allocate_zeroed(new_layout)?;

            {
                let new_ptr = as_non_null_ptr(new_ptr);

                //  Safety:
                //  -   `ptr` is valid for `old_layout.size()` reads, as per Liveness & Layout pre-conditions.
                //  -   `new_ptr` is valid for `old_layout.size()` writes, as per Layout pre-condition.
                //  -   `ptr` and `new_ptr` point to non-overlapping blocks, as `new_ptr` is freshly allocated.
                unsafe { ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_layout.size()) };

                //  Safety:
                //  -   Liveness: as per Liveness pre-condition.
                //  -   Selfness: as per Selfness pre-condition.
                //  -   Layout: as per Layout pre-condition.
                unsafe { self.deallocate(ptr, old_layout) };
            }

            Ok(new_ptr)
        }

        /// Attempts to shrink the memory block.
        ///
        /// #   Safety
        ///
        /// -   Liveness: `ptr` must still be allocated.
        /// -   Selfness: `ptr` must have been allocated by `self`.
        /// -   Layout: `old_layout` must match the layout passed to `self.allocate(...)` or `self.allocate_zeroed(...)`
        ///     when allocating `ptr`.
        /// -   Shrinkage: `new_layout.size()` must be less than or equal to `old_layout.size()`.
        unsafe fn shrink(
            &self,
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            debug_assert!(new_layout.size() <= old_layout.size());

            let new_ptr = self.allocate_zeroed(new_layout)?;

            {
                let new_ptr = as_non_null_ptr(new_ptr);

                //  Safety:
                //  -   `ptr` is valid for `new_layout.size()` reads, as per Liveness & Shrinkage pre-conditions.
                //  -   `new_ptr` is valid for `new_layout.size()` writes, as per `allocate_zeroed` post-conditions.
                //  -   `ptr` and `new_ptr` point to non-overlapping blocks, as `new_ptr` is freshly allocated.
                unsafe { ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), new_layout.size()) };

                //  Safety:
                //  -   Liveness: as per Liveness pre-condition.
                //  -   Selfness: as per Selfness pre-condition.
                //  -   Layout: as per Layout pre-condition.
                unsafe { self.deallocate(ptr, old_layout) };
            }

            Ok(new_ptr)
        }

        /// Creates a “by reference” adapter for this instance of Allocator.
        fn by_ref(&self) -> &Self
        where
            Self: Sized,
        {
            self
        }
    }

    /// The global memory allocator.
    #[derive(Copy, Clone, Default, Debug)]
    pub struct Global;

    //  Safety:
    //  -   Liveness, Independence, Shallowness: guaranteed by implementation.
    unsafe impl Allocator for Global {
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            self.alloc_impl(layout, false)
        }

        #[inline]
        fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            self.alloc_impl(layout, true)
        }

        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            if layout.size() == 0 {
                return;
            }

            //  Safety:
            //  -   `ptr.as_ptr()` is currently allocated, as per Liveness pre-condition.
            //  -   `ptr.as_ptr()` was allocated by `self`, as per Selfness pre-condition.
            //  -   `layout` matches the layout of `ptr.as_ptr()` as per Layout pre-condition.
            unsafe { alloc::dealloc(ptr.as_ptr(), layout) }
        }
    }

    //
    //  Implementation
    //

    impl Global {
        #[inline]
        fn alloc_impl(&self, layout: Layout, zeroed: bool) -> Result<NonNull<[u8]>, AllocError> {
            if layout.size() == 0 {
                return Ok(NonNull::slice_from_raw_parts(NonNull::dangling(), 0));
            }

            //  Safety:
            //  -   `layout` has a non-zero size.
            let raw_ptr = unsafe {
                if zeroed {
                    alloc::alloc_zeroed(layout)
                } else {
                    alloc::alloc(layout)
                }
            };

            let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;

            Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
        }
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
} // mod shim
