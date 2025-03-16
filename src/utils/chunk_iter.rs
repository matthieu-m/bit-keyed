//  See structs.

use super::{BitChunkRaw, BitChunkViewRaw, IndexOfChunkRaw};

/// Forward iterator over a `BitChunkViewRaw`.
pub struct BitChunkIter<V> {
    of_chunk: Option<IndexOfChunkRaw>,
    view: V,
}

impl<V> BitChunkIter<V>
where
    V: BitChunkViewRaw,
{
    /// Creates a new instance.
    pub fn new(view: V) -> Self {
        let of_chunk = view.first();

        Self { of_chunk, view }
    }

    /// Returns the underlying view.
    pub fn view(&self) -> &V {
        &self.view
    }

    /// Returns the underlying view.
    pub fn view_mut(&mut self) -> &mut V {
        &mut self.view
    }
}

impl<V> Iterator for BitChunkIter<V>
where
    V: BitChunkViewRaw,
{
    type Item = (IndexOfChunkRaw, BitChunkRaw);

    fn next(&mut self) -> Option<Self::Item> {
        let of_chunk = self.of_chunk?;

        //  Safety:
        //  -   `of_chunk` was obtained by either `self.view.first()` or `self.view.next_after(...)`.
        let chunk = unsafe { self.view.get_unchecked(of_chunk) };

        self.of_chunk = of_chunk.checked_add(1).and_then(|i| self.view.next_after(i));

        Some((of_chunk, chunk))
    }
}

/// Backward (reverse) iterator over a `BitChunkViewRaw`.
pub struct BitChunkIterRev<V> {
    of_chunk: Option<IndexOfChunkRaw>,
    view: V,
}

impl<V> BitChunkIterRev<V>
where
    V: BitChunkViewRaw,
{
    /// Creates a new instance.
    pub fn new(view: V) -> Self {
        let of_chunk = view.last();

        Self { of_chunk, view }
    }

    /// Returns the underlying view.
    pub fn view(&self) -> &V {
        &self.view
    }

    /// Returns the underlying view.
    pub fn view_mut(&mut self) -> &mut V {
        &mut self.view
    }
}

impl<V> Iterator for BitChunkIterRev<V>
where
    V: BitChunkViewRaw,
{
    type Item = (IndexOfChunkRaw, BitChunkRaw);

    fn next(&mut self) -> Option<Self::Item> {
        let of_chunk = self.of_chunk?;

        //  Safety:
        //  -   `of_chunk` was obtained by either `self.view.last()` or `self.view.next_before(...)`.
        let chunk = unsafe { self.view.get_unchecked(of_chunk) };

        self.of_chunk = of_chunk.checked_sub(1).and_then(|i| self.view.next_before(i));

        Some((of_chunk, chunk))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        const EMPTY: [BitChunkRaw; 0] = [];
        const EXPECTED: &[BitChunkRaw] = &[];

        assert_eq!(EXPECTED, collect(BitChunkIter::new(EMPTY)));
        assert_eq!(EXPECTED, collect(BitChunkIterRev::new(EMPTY)));
    }

    #[test]
    fn single() {
        const ONE: BitChunkRaw = BitChunkRaw(0b1001);

        const SINGLE: [BitChunkRaw; 1] = [ONE];
        const EXPECTED: &[BitChunkRaw] = &[ONE];

        assert_eq!(EXPECTED, collect(BitChunkIter::new(SINGLE)));
        assert_eq!(EXPECTED, collect(BitChunkIterRev::new(SINGLE)));
    }

    #[test]
    fn trio() {
        const ONE: BitChunkRaw = BitChunkRaw(0b1001);
        const TWO: BitChunkRaw = BitChunkRaw(0b0001);
        const THREE: BitChunkRaw = BitChunkRaw(0b1000);

        const TRIO: [BitChunkRaw; 3] = [ONE, TWO, THREE];
        const EXPECTED_FORWARD: &[BitChunkRaw] = &[ONE, TWO, THREE];
        const EXPECTED_BACKWARD: &[BitChunkRaw] = &[THREE, TWO, ONE];

        assert_eq!(EXPECTED_FORWARD, collect(BitChunkIter::new(TRIO)));
        assert_eq!(EXPECTED_BACKWARD, collect(BitChunkIterRev::new(TRIO)));
    }

    fn collect<I>(iter: I) -> Vec<BitChunkRaw>
    where
        I: Iterator<Item = (IndexOfChunkRaw, BitChunkRaw)>,
    {
        iter.map(|(_, c)| c).collect()
    }
} // mod tests
