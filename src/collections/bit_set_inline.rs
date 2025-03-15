//! Inline implementation of a bit set.

use crate::{
    api::{BitKey, BitSet, BitStoreError},
    collections::BitSetCore,
    utils::BitChunk,
};

/// Inline implementation of a bit set.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BitSetInline<const N: usize>(BitSetCore<[BitChunk; N]>);

//
//  Creation
//

impl<const N: usize> BitSetInline<N> {
    /// Creates a new, empty, set.
    pub const fn new() -> Self {
        Self(BitSetCore::new([BitChunk::ALL_ZEROS; N]))
    }
}

impl<const N: usize> Default for BitSetInline<N> {
    fn default() -> Self {
        Self::new()
    }
}

//
//  BitSet (inherent)
//

impl<const N: usize> BitSetInline<N> {
    /// Returns the underlying chunks.
    pub fn chunks(&self) -> &[BitChunk; N] {
        self.0.chunks()
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

impl<const N: usize> BitSet for BitSetInline<N> {
    type Element = usize;

    type ChunkView<'a> = &'a [BitChunk; N];

    fn chunks(&self) -> &[BitChunk; N] {
        self.0.chunks()
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
