//  See structs.

use super::{BitChunk, BitChunkView, IndexOfChunk};

/// Forward iterator over a `BitChunkView`.
pub struct BitChunkIter<V> {
    of_chunk: Option<IndexOfChunk>,
    view: V,
}

impl<V> BitChunkIter<V>
where
    V: BitChunkView,
{
    /// Creates a new instance.
    pub fn new(view: V) -> Self {
        let of_chunk = view.first();

        Self { of_chunk, view }
    }

    /// Returns the index of the chunk next returned by `self.next()`, if any.
    pub fn index(&self) -> Option<IndexOfChunk> {
        self.of_chunk
    }
}

impl<V> Iterator for BitChunkIter<V>
where
    V: BitChunkView,
{
    type Item = BitChunk;

    fn next(&mut self) -> Option<Self::Item> {
        let of_chunk = self.of_chunk?;

        //  Safety:
        //  -   `of_chunk` was obtained by either `self.view.first()` or `self.view.next_after(...)`.
        let chunk = unsafe { self.view.get_unchecked(of_chunk) };

        self.of_chunk = of_chunk.checked_add(1).and_then(|i| self.view.next_after(i));

        Some(chunk)
    }
}

/// Backward (reverse) iterator over a `BitChunkView`.
pub struct BitChunkIterRev<V> {
    of_chunk: Option<IndexOfChunk>,
    view: V,
}

impl<V> BitChunkIterRev<V>
where
    V: BitChunkView,
{
    /// Creates a new instance.
    pub fn new(view: V) -> Self {
        let of_chunk = view.last();

        Self { of_chunk, view }
    }

    /// Returns the index of the chunk next returned by `self.next()`, if any.
    pub fn index(&self) -> Option<IndexOfChunk> {
        self.of_chunk
    }
}

impl<V> Iterator for BitChunkIterRev<V>
where
    V: BitChunkView,
{
    type Item = BitChunk;

    fn next(&mut self) -> Option<Self::Item> {
        let of_chunk = self.of_chunk?;

        //  Safety:
        //  -   `of_chunk` was obtained by either `self.view.last()` or `self.view.next_before(...)`.
        let chunk = unsafe { self.view.get_unchecked(of_chunk) };

        self.of_chunk = of_chunk.checked_sub(1).and_then(|i| self.view.next_before(i));

        Some(chunk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        const EMPTY: [BitChunk; 0] = [];
        const EXPECTED: &[BitChunk] = &[];

        assert_eq!(EXPECTED, collect(BitChunkIter::new(EMPTY)));
        assert_eq!(EXPECTED, collect(BitChunkIterRev::new(EMPTY)));
    }

    #[test]
    fn single() {
        const ONE: BitChunk = BitChunk(0b1001);

        const SINGLE: [BitChunk; 1] = [ONE];
        const EXPECTED: &[BitChunk] = &[ONE];

        assert_eq!(EXPECTED, collect(BitChunkIter::new(SINGLE)));
        assert_eq!(EXPECTED, collect(BitChunkIterRev::new(SINGLE)));
    }

    #[test]
    fn trio() {
        const ONE: BitChunk = BitChunk(0b1001);
        const TWO: BitChunk = BitChunk(0b0001);
        const THREE: BitChunk = BitChunk(0b1000);

        const TRIO: [BitChunk; 3] = [ONE, TWO, THREE];
        const EXPECTED_FORWARD: &[BitChunk] = &[ONE, TWO, THREE];
        const EXPECTED_BACKWARD: &[BitChunk] = &[THREE, TWO, ONE];

        assert_eq!(EXPECTED_FORWARD, collect(BitChunkIter::new(TRIO)));
        assert_eq!(EXPECTED_BACKWARD, collect(BitChunkIterRev::new(TRIO)));
    }

    fn collect<I>(iter: I) -> Vec<BitChunk>
    where
        I: Iterator<Item = BitChunk>,
    {
        iter.collect()
    }
} // mod tests
