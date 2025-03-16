//  See LastChunkStore.

use core::cell::Cell;

use super::{BitChunkRaw, BitChunkStoreRaw, BitChunkViewRaw, BitStoreError, IndexOfChunkRaw, TrustedBitChunkStoreRaw};

/// Cache of the last accessed chunk.
///
/// Implementers of ChunkView/ChunkStore for which accesses are expensive can use this simple cache to amortize the cost
/// of access. This is mostly useful for iteration.
#[derive(Debug)]
pub struct LastBitChunkViewRaw<'a, V> {
    cache: CacheView,
    view: &'a V,
}

impl<'a, V> LastBitChunkViewRaw<'a, V> {
    /// Returns a new instance of the LastBitChunkViewRaw.
    pub fn new(view: &'a V) -> Self {
        let cache = CacheView::default();

        Self { cache, view }
    }
}

impl<'a, V> Clone for LastBitChunkViewRaw<'a, V> {
    fn clone(&self) -> Self {
        let cache = self.cache.clone();
        let view = self.view;

        Self { cache, view }
    }
}

impl<'a, V> BitChunkViewRaw for LastBitChunkViewRaw<'a, V>
where
    V: BitChunkViewRaw,
{
    fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        self.cache.get(index, self.view)
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        //  Safety:
        //  -   `index` was returned by a call to either of `self.first()`, `self.last()`, `self.next_after(...)`, or
        //      `self.next_before(...)`, as per pre-conditions.
        unsafe { self.cache.get_unchecked(index, self.view) }
    }

    fn first(&self) -> Option<IndexOfChunkRaw> {
        self.view.first()
    }

    fn last(&self) -> Option<IndexOfChunkRaw> {
        self.view.last()
    }

    fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        self.view.next_after(index)
    }

    fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        self.view.next_before(index)
    }
}

//  #   Safety
//
//  -   Faithful: `CacheView` guarantees that the `BitChunkRaw` returned is a copy of the one matching `V`, and `V` is
//      immutable for the lifetime of `CacheView`.
//  -   One-pass: inherited from `V`.
unsafe impl<'a, V> TrustedBitChunkStoreRaw for LastBitChunkViewRaw<'a, V> where V: TrustedBitChunkStoreRaw {}

/// Cache of the last accessed chunk.
///
/// Implementers of ChunkView/ChunkStore for which accesses are expensive can use this simple cache to amortize the cost
/// of access. This is mostly useful for iteration.
#[derive(Debug)]
pub struct LastBitChunkStoreRaw<'a, V> {
    cache: CacheView,
    view: &'a mut V,
}

impl<'a, V> LastBitChunkStoreRaw<'a, V> {
    /// Returns a new instance of the LastBitChunkStoreRaw.
    pub fn new(view: &'a mut V) -> Self {
        let cache = CacheView::default();

        Self { cache, view }
    }
}

impl<'a, V> BitChunkViewRaw for LastBitChunkStoreRaw<'a, V>
where
    V: BitChunkViewRaw,
{
    fn get(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        self.cache.get(index, self.view)
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: IndexOfChunkRaw) -> BitChunkRaw {
        //  Safety:
        //  -   `index` was returned by a call to either of `self.first()`, `self.last()`, `self.next_after(...)`, or
        //      `self.next_before(...)`, as per pre-conditions.
        unsafe { self.cache.get_unchecked(index, self.view) }
    }

    fn first(&self) -> Option<IndexOfChunkRaw> {
        self.view.first()
    }

    fn last(&self) -> Option<IndexOfChunkRaw> {
        self.view.last()
    }

    fn next_after(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        self.view.next_after(index)
    }

    fn next_before(&self, index: IndexOfChunkRaw) -> Option<IndexOfChunkRaw> {
        self.view.next_before(index)
    }
}

impl<'a, V> BitChunkStoreRaw for LastBitChunkStoreRaw<'a, V>
where
    V: BitChunkStoreRaw,
{
    fn set(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw) -> Result<BitChunkRaw, BitStoreError> {
        self.cache.set(index, chunk, self.view)
    }
}

//  #   Safety
//
//  -   Faithful: `CacheView` guarantees that the `BitChunkRaw` returned is a copy of the one matching `V`.
//  -   One-pass: inherited from `V`.
unsafe impl<'a, V> TrustedBitChunkStoreRaw for LastBitChunkStoreRaw<'a, V> where V: TrustedBitChunkStoreRaw {}

//
//  Implementation
//

#[derive(Clone, Debug, Default)]
struct CacheView {
    index: Cell<Option<IndexOfChunkRaw>>,
    chunk: Cell<BitChunkRaw>,
}

impl CacheView {
    fn get<V>(&self, index: IndexOfChunkRaw, view: &V) -> BitChunkRaw
    where
        V: BitChunkViewRaw,
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
    unsafe fn get_unchecked<V>(&self, index: IndexOfChunkRaw, view: &V) -> BitChunkRaw
    where
        V: BitChunkViewRaw,
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

    fn set<V>(&mut self, index: IndexOfChunkRaw, chunk: BitChunkRaw, view: &mut V) -> Result<BitChunkRaw, BitStoreError>
    where
        V: BitChunkStoreRaw,
    {
        let previous = view.set(index, chunk)?;

        self.index.set(Some(index));
        self.chunk.set(chunk);

        Ok(previous)
    }
}
