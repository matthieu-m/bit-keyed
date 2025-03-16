//! Dynamically sized implementation of a bit set.

use core::hash::{Hash, Hasher};

use crate::{
    api::{BitKey, BitSet, BitStoreError, bit_view::BitViewAdapter},
    collections::BitSetCore,
    utils::{
        BitChunkRaw, DynamicBitChunkStore,
        alloc::{Allocator, Global},
    },
};

/// Dynamically sized implementation of a bit set.
#[derive(Clone, Debug)]
pub struct BitSetDynamic<A: Allocator = Global>(BitSetCore<DynamicBitChunkStore<A>>);

//
//  Creation
//

impl BitSetDynamic<Global> {
    /// Creates a new, empty, set.
    pub const fn new() -> Self {
        Self(BitSetCore::new(DynamicBitChunkStore::new()))
    }
}

impl<A> BitSetDynamic<A>
where
    A: Allocator,
{
    /// Creates a new, empty, set.
    pub const fn new_in(allocator: A) -> Self {
        Self(BitSetCore::new(DynamicBitChunkStore::new_in(allocator)))
    }
}

impl<A> Default for BitSetDynamic<A>
where
    A: Allocator + Default,
{
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

//
//  BitSet (inherent)
//

impl<A> BitSetDynamic<A>
where
    A: Allocator,
{
    /// Returns the underlying chunks.
    pub fn chunks(&self) -> BitViewAdapter<&[BitChunkRaw], usize> {
        BitViewAdapter::from_raw(self.0.chunks().chunks())
    }

    /// Returns whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns whether the set contains the key, or not.
    pub fn contains(&self, element: usize) -> bool {
        self.0.contains(element.into_key())
    }

    /// Clears the set, removing all elements.
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Inserts a key in the set.
    ///
    /// Returns:
    ///
    /// -   `Ok(true)`: if the key was successfully inserted.
    /// -   `Ok(false)`: if the key was already present.
    /// -   `Err(_)`: if the key could not be inserted, and wasn't already present.
    pub fn insert(&mut self, element: usize) -> Result<bool, BitStoreError> {
        self.0.insert(element.into_key())
    }

    /// Removes a key from the set, returning whether it is newly removed or not.
    pub fn remove(&mut self, element: usize) -> bool {
        self.0.remove(element.into_key())
    }
}

//
//  BitSet (trait)
//

impl<A> BitSet for BitSetDynamic<A>
where
    A: Allocator,
{
    type Element = usize;

    type BitView<'a>
        = BitViewAdapter<&'a [BitChunkRaw], usize>
    where
        A: 'a;

    fn chunks(&self) -> BitViewAdapter<&[BitChunkRaw], usize> {
        BitViewAdapter::from_raw(self.0.chunks().chunks())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn contains(&self, element: usize) -> bool {
        self.0.contains(element.into_key())
    }

    fn clear(&mut self) {
        self.0.clear();
    }

    fn insert(&mut self, element: usize) -> Result<bool, BitStoreError> {
        self.0.insert(element.into_key())
    }

    fn remove(&mut self, element: usize) -> bool {
        self.0.remove(element.into_key())
    }
}

//
//  Common traits
//

impl<A> Eq for BitSetDynamic<A> where A: Allocator {}

impl<A> Hash for BitSetDynamic<A>
where
    A: Allocator,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.0.hash(state);
    }
}

impl<A> PartialEq for BitSetDynamic<A>
where
    A: Allocator,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
