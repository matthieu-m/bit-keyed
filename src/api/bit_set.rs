//! A generic bit-keyed set.

use crate::{
    api::{BitKey, BitStoreError},
    utils::BitChunkView,
};

/// A generic bit-keyed set.
///
/// While the index type is generic, it is intended to be just that, an index.
pub trait BitSet {
    /// Type of the elements of the set.
    type Element: BitKey;

    /// Type of the view of the chunks.
    type ChunkView<'a>: BitChunkView + 'a
    where
        Self: 'a;

    /// Returns the underlying chunks.
    fn chunks(&self) -> Self::ChunkView<'_>;

    /// Returns whether the set is empty.
    fn is_empty(&self) -> bool;

    /// Returns the number of elements in the set.
    fn len(&self) -> usize;

    /// Returns whether the set contains the element, or not.
    fn contains(&self, element: Self::Element) -> bool;

    /// Clears the set, removing all elements.
    fn clear(&mut self);

    /// Inserts an element in the set.
    ///
    /// Returns Ok if the element is thereby contained by the set, with an indication of whether it is newly inserted or
    /// not.
    ///
    /// Returns an error if the element could not be inserted.
    fn insert(&mut self, element: Self::Element) -> Result<bool, BitStoreError>;

    /// Removes an element from the set, returning whether it is newly removed or not.
    fn remove(&mut self, element: Self::Element) -> bool;
}
