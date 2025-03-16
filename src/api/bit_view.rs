//! View over a bit-keyed structures keys, chunked.

use core::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use crate::{
    api::{BitChunk, BitIndexOfChunk, BitKey},
    utils::BitChunkViewRaw,
};

/// A trait for read-only access to a collection of `BitChunkRaw`.
///
/// The trait is pre-implemented for `[BitChunkRaw; N]`, and exists to allow for alternative representations, such as
/// compressed sets, or sparse sets.
pub trait BitView {
    /// Type of the Key.
    type Key: BitKey;

    //
    //  Index access
    //

    /// Returns the `BitChunkRaw` at the given index.
    ///
    /// If `index` is unknown, an `ALL_ZEROS` chunk should be returned.
    fn get(&self, index: BitIndexOfChunk<Self::Key>) -> BitChunk<Self::Key>;

    /// Returns the `BitChunkRaw` at the given index.
    ///
    /// #   Safety
    ///
    /// The caller guarantees that `index` was either returned by a call to `self.first()`, `self.last()`,
    /// `self.next_after(...)`, or `self.next_before(...)`.
    #[inline]
    unsafe fn get_unchecked(&self, index: BitIndexOfChunk<Self::Key>) -> BitChunk<Self::Key> {
        self.get(index)
    }

    //
    //  Index iteration
    //

    /// Returns the first interesting index, if any.
    ///
    /// All chunks strictly before this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
    /// chunk at this index isn't `ALL_ZEROS` too.
    fn first(&self) -> Option<BitIndexOfChunk<Self::Key>>;

    /// Returns the last interesting index, if any.
    ///
    /// All chunks strictly after this index are guaranteed to be `ALL_ZEROS`, though no guarantee is made that the
    /// chunk at this index isn't `ALL_ZEROS` too.
    fn last(&self) -> Option<BitIndexOfChunk<Self::Key>>;

    /// Returns the next interesting index at or after `index`, if any.
    ///
    /// Returns `None` when all chunks at or after `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is made
    /// that it returns `None` precisely when no further chunks have any set bit.
    fn next_after(&self, index: BitIndexOfChunk<Self::Key>) -> Option<BitIndexOfChunk<Self::Key>>;

    /// Returns the next interesting index at or before `index`, if any.
    ///
    /// Returns `None` when all chunks at or before `index` are guaranteed to be `ALL_ZEROS`, though no guarantee is
    /// made that it returns `None` precisely when no prior chunks have any set bit.
    fn next_before(&self, index: BitIndexOfChunk<Self::Key>) -> Option<BitIndexOfChunk<Self::Key>>;
}

/// Adapter over raw chunks.
pub struct BitViewAdapter<V, K>(V, PhantomData<fn(K) -> K>);

//
//  Construction
//

impl<V, K> BitViewAdapter<V, K> {
    /// Creates an adapter.
    pub const fn from_raw(view: V) -> Self {
        Self(view, PhantomData)
    }

    /// Returns the inner view.
    pub fn into_raw(self) -> V {
        //  FIXME: make `const` when rustc is finally smart enough to realize there's no destructor to call here...

        self.0
    }

    /// Returns a reference to the inner view.
    pub const fn as_raw(&self) -> &V {
        &self.0
    }

    /// Returns a mutable reference to the inner view.
    pub const fn as_raw_mut(&mut self) -> &mut V {
        &mut self.0
    }
}

//
//  BitView
//

impl<V, K> BitView for BitViewAdapter<V, K>
where
    V: BitChunkViewRaw,
    K: BitKey,
{
    type Key = K;

    fn get(&self, index: BitIndexOfChunk<Self::Key>) -> BitChunk<Self::Key> {
        BitChunk::from_raw(self.0.get(index.into_raw()))
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: BitIndexOfChunk<Self::Key>) -> BitChunk<Self::Key> {
        //  Safety: forwarded.
        let chunk = unsafe { self.0.get_unchecked(index.into_raw()) };

        BitChunk::from_raw(chunk)
    }

    fn first(&self) -> Option<BitIndexOfChunk<Self::Key>> {
        self.0.first().map(BitIndexOfChunk::from_raw)
    }

    fn last(&self) -> Option<BitIndexOfChunk<Self::Key>> {
        self.0.last().map(BitIndexOfChunk::from_raw)
    }

    fn next_after(&self, index: BitIndexOfChunk<Self::Key>) -> Option<BitIndexOfChunk<Self::Key>> {
        self.0.next_after(index.into_raw()).map(BitIndexOfChunk::from_raw)
    }

    fn next_before(&self, index: BitIndexOfChunk<Self::Key>) -> Option<BitIndexOfChunk<Self::Key>> {
        self.0.next_before(index.into_raw()).map(BitIndexOfChunk::from_raw)
    }
}

//
//  Common traits.
//

impl<V, K> Clone for BitViewAdapter<V, K>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1)
    }
}

impl<V, K> Copy for BitViewAdapter<V, K> where V: Copy {}

impl<V, K> Eq for BitViewAdapter<V, K> where V: Eq {}

impl<V, K> Hash for BitViewAdapter<V, K>
where
    V: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.0.hash(state);
    }
}

impl<V, K> Ord for BitViewAdapter<V, K>
where
    V: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<V, K> PartialEq for BitViewAdapter<V, K>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<V, K> PartialOrd for BitViewAdapter<V, K>
where
    V: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}
