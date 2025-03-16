//! Core implementation of a bit-keyed set, generic over a chunks store.

use crate::utils::{BitChunkIter, BitChunkRaw, BitChunkStoreRaw, BitStoreError};

/// Core implementation of a bit-keyed set.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitSetCore<S> {
    chunks: S,
}

//
//  Creation
//

impl<S> BitSetCore<S> {
    /// Creates a new set over an existing chunks store.
    pub const fn new(chunks: S) -> Self {
        Self { chunks }
    }
}

impl<S> Default for BitSetCore<S>
where
    S: Default,
{
    fn default() -> Self {
        Self::new(S::default())
    }
}

//
//  BitSet
//

impl<S> BitSetCore<S>
where
    S: BitChunkStoreRaw,
{
    /// Returns the underlying chunks.
    pub fn chunks(&self) -> &S {
        &self.chunks
    }

    /// Returns whether the set is empty.
    pub fn is_empty(&self) -> bool {
        BitChunkIter::new(&self.chunks).all(|(_, chunk)| chunk == BitChunkRaw::ALL_ZEROS)
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        BitChunkIter::new(&self.chunks).map(|(_, chunk)| chunk.count()).sum()
    }

    /// Returns whether the set contains the key, or not.
    pub fn contains(&self, key: u64) -> bool {
        let Some((of_chunk, in_chunk)) = BitChunkRaw::split(key) else {
            return false;
        };

        self.chunks.get(of_chunk).is_set(in_chunk)
    }

    /// Clears the set, removing all elements.
    pub fn clear(&mut self) {
        let mut iter = BitChunkIter::new(&mut self.chunks);

        while let Some((of_chunk, _)) = iter.next() {
            //  May only fail if the chunk isn't already `ALL_ZEROS`, in which case it doesn't matter.
            let _ = iter.view_mut().set(of_chunk, BitChunkRaw::ALL_ZEROS);
        }
    }

    /// Inserts a key in the set.
    ///
    /// Returns:
    ///
    /// -   `Ok(true)`: if the key was successfully inserted.
    /// -   `Ok(false)`: if the key was already present.
    /// -   `Err(_)`: if the key could not be inserted, and wasn't already present.
    pub fn insert(&mut self, key: u64) -> Result<bool, BitStoreError> {
        let Some((of_chunk, in_chunk)) = BitChunkRaw::split(key) else {
            return Err(BitStoreError);
        };

        let mut chunk = self.chunks.get(of_chunk);

        if !chunk.set(in_chunk) {
            return Ok(false);
        }

        self.chunks.set(of_chunk, chunk).map(|_| true)
    }

    /// Removes a key from the set, returning whether it is newly removed or not.
    pub fn remove(&mut self, key: u64) -> bool {
        let Some((of_chunk, in_chunk)) = BitChunkRaw::split(key) else {
            return false;
        };

        let mut chunk = self.chunks.get(of_chunk);

        if !chunk.reset(in_chunk) {
            return false;
        }

        //  Safety:
        //  -   `of_chunk` is the index of a non `ALL_ZEROS` chunk, as `in_chunk` was just reset in `chunk`.
        unsafe { self.chunks.set_unchecked(of_chunk, chunk) };

        true
    }
}
