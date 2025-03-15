//  See LastChunkStore.

use core::cell::Cell;

use super::{BitChunk, BitChunkStore, BitChunkView, BitStoreError, IndexOfChunk, TrustedBitChunkStore};

/// Cache of the last accessed chunk.
///
/// Implementers of ChunkView/ChunkStore for which accesses are expensive can use this simple cache to amortize the cost
/// of access. This is mostly useful for iteration.
#[derive(Debug)]
pub struct LastBitChunkView<'a, V> {
    cache: CacheView,
    view: &'a V,
}

impl<'a, V> LastBitChunkView<'a, V> {
    /// Returns a new instance of the LastBitChunkView.
    pub fn new(view: &'a V) -> Self {
        let cache = CacheView::default();

        Self { cache, view }
    }
}

impl<'a, V> Clone for LastBitChunkView<'a, V> {
    fn clone(&self) -> Self {
        let cache = self.cache.clone();
        let view = self.view;

        Self { cache, view }
    }
}

impl<'a, V> BitChunkView for LastBitChunkView<'a, V>
where
    V: BitChunkView,
{
    fn get(&self, index: IndexOfChunk) -> BitChunk {
        self.cache.get(index, self.view)
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
        //  Safety:
        //  -   `index` was returned by a call to either of `self.first()`, `self.last()`, `self.next_after(...)`, or
        //      `self.next_before(...)`, as per pre-conditions.
        unsafe { self.cache.get_unchecked(index, self.view) }
    }

    fn first(&self) -> Option<IndexOfChunk> {
        self.view.first()
    }

    fn last(&self) -> Option<IndexOfChunk> {
        self.view.last()
    }

    fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        self.view.next_after(index)
    }

    fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        self.view.next_before(index)
    }
}

//  #   Safety
//
//  -   Faithful: `CacheView` guarantees that the `BitChunk` returned is a copy of the one matching `V`, and `V` is
//      immutable for the lifetime of `CacheView`.
//  -   One-pass: inherited from `V`.
unsafe impl<'a, V> TrustedBitChunkStore for LastBitChunkView<'a, V> where V: TrustedBitChunkStore {}

/// Cache of the last accessed chunk.
///
/// Implementers of ChunkView/ChunkStore for which accesses are expensive can use this simple cache to amortize the cost
/// of access. This is mostly useful for iteration.
#[derive(Debug)]
pub struct LastBitChunkStore<'a, V> {
    cache: CacheView,
    view: &'a mut V,
}

impl<'a, V> LastBitChunkStore<'a, V> {
    /// Returns a new instance of the LastBitChunkStore.
    pub fn new(view: &'a mut V) -> Self {
        let cache = CacheView::default();

        Self { cache, view }
    }
}

impl<'a, V> BitChunkView for LastBitChunkStore<'a, V>
where
    V: BitChunkView,
{
    fn get(&self, index: IndexOfChunk) -> BitChunk {
        self.cache.get(index, self.view)
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: IndexOfChunk) -> BitChunk {
        //  Safety:
        //  -   `index` was returned by a call to either of `self.first()`, `self.last()`, `self.next_after(...)`, or
        //      `self.next_before(...)`, as per pre-conditions.
        unsafe { self.cache.get_unchecked(index, self.view) }
    }

    fn first(&self) -> Option<IndexOfChunk> {
        self.view.first()
    }

    fn last(&self) -> Option<IndexOfChunk> {
        self.view.last()
    }

    fn next_after(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        self.view.next_after(index)
    }

    fn next_before(&self, index: IndexOfChunk) -> Option<IndexOfChunk> {
        self.view.next_before(index)
    }
}

impl<'a, V> BitChunkStore for LastBitChunkStore<'a, V>
where
    V: BitChunkStore,
{
    fn set(&mut self, index: IndexOfChunk, chunk: BitChunk) -> Result<BitChunk, BitStoreError> {
        self.cache.set(index, chunk, self.view)
    }
}

//  #   Safety
//
//  -   Faithful: `CacheView` guarantees that the `BitChunk` returned is a copy of the one matching `V`.
//  -   One-pass: inherited from `V`.
unsafe impl<'a, V> TrustedBitChunkStore for LastBitChunkStore<'a, V> where V: TrustedBitChunkStore {}

//
//  Implementation
//

#[derive(Clone, Debug, Default)]
struct CacheView {
    index: Cell<Option<IndexOfChunk>>,
    chunk: Cell<BitChunk>,
}

impl CacheView {
    fn get<V>(&self, index: IndexOfChunk, view: &V) -> BitChunk
    where
        V: BitChunkView,
    {
        if self.index.get() == Some(index) {
            return self.chunk.get();
        }

        self.chunk.set(view.get(index));
        self.index.set(Some(index));

        self.chunk.get()
    }

    //  #   Safety
    //
    //  The caller guarantees that `index` was either returned by a call to `self.first()`, `self.last()`,
    //  `self.next_after(...)`, or `self.next_before(...)`.
    unsafe fn get_unchecked<V>(&self, index: IndexOfChunk, view: &V) -> BitChunk
    where
        V: BitChunkView,
    {
        if self.index.get() == Some(index) {
            return self.chunk.get();
        }

        //  Safety:
        //  -   `index` was returned by a call to either of `self.first()`, `self.last()`, `self.next_after(...)`, or
        //      `self.next_before(...)`, as per pre-conditions.
        self.chunk.set(unsafe { view.get_unchecked(index) });
        self.index.set(Some(index));

        self.chunk.get()
    }

    fn set<V>(&mut self, index: IndexOfChunk, chunk: BitChunk, view: &mut V) -> Result<BitChunk, BitStoreError>
    where
        V: BitChunkStore,
    {
        let previous = view.set(index, chunk)?;

        self.index.set(Some(index));
        self.chunk.set(chunk);

        Ok(previous)
    }
}
