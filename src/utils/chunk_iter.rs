//  See structs.

use super::{BitChunkRaw, BitChunkViewRaw, IndexInChunkRaw, IndexOfChunkRaw};

//
//  In chunk iterators.
//

/// Forward iterator over a `BitChunkRaw`.
#[derive(Clone, Debug)]
pub struct BitInChunkIter {
    next: IndexInChunkRaw,
    chunk: BitChunkRaw,
}

impl BitInChunkIter {
    /// Creates a new iterator.
    pub const fn new(chunk: BitChunkRaw) -> Self {
        let next = IndexInChunkRaw(0);

        Self { next, chunk }
    }

    //  Gives the index.
    fn index(index: IndexInChunkRaw) -> Option<IndexInChunkRaw> {
        (index.0 < BITS_32).then_some(index)
    }
}

impl Iterator for BitInChunkIter {
    type Item = IndexInChunkRaw;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(next) = Self::index(self.next) else {
            return (0, Some(0));
        };

        let count = self.chunk.count_after(next);

        (count, Some(count))
    }

    fn count(self) -> usize {
        let Some(next) = Self::index(self.next) else {
            return 0;
        };

        self.chunk.count_after(next)
    }

    fn next(&mut self) -> Option<Self::Item> {
        let next = Self::index(self.next)?;

        let result = self.chunk.next_after(next);

        self.next.0 = result.map(|i| i.0 + 1).unwrap_or(BITS_32);

        result
    }
}

/// Backward iterator over a `BitChunkRaw`.
#[derive(Clone, Debug)]
pub struct BitInChunkIterRev {
    next: IndexInChunkRaw,
    chunk: BitChunkRaw,
}

impl BitInChunkIterRev {
    /// Creates a new iterator.
    pub const fn new(chunk: BitChunkRaw) -> Self {
        let next = IndexInChunkRaw(BITS_32);

        Self { next, chunk }
    }

    //  Reverses the index.
    fn index(index: IndexInChunkRaw) -> Option<IndexInChunkRaw> {
        index.0.checked_sub(1).map(IndexInChunkRaw)
    }
}

impl Iterator for BitInChunkIterRev {
    type Item = IndexInChunkRaw;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(next) = Self::index(self.next) else {
            return (0, Some(0));
        };

        let count = self.chunk.count_before(next);

        (count, Some(count))
    }

    fn count(self) -> usize {
        let Some(next) = Self::index(self.next) else {
            return 0;
        };

        self.chunk.count_before(next)
    }

    fn next(&mut self) -> Option<Self::Item> {
        let next = Self::index(self.next)?;

        let result = self.chunk.next_before(next);

        self.next.0 = result.map(|i| i.0).unwrap_or(0);

        result
    }
}

//
//  Implementations for in chunks iterators.
//

const BITS_32: u32 = BitChunkRaw::BITS as _;

#[cfg(test)]
mod in_chunk_tests {
    use super::*;

    #[test]
    fn empty() {
        const EMPTY: &[u32] = &[];

        assert_eq!(EMPTY, collect_forward(0));
        assert_eq!(EMPTY, collect_backward(0));
    }

    #[test]
    fn single() {
        const SINGLE: &[u32] = &[1];

        assert_eq!(SINGLE, collect_forward(0b0010));
        assert_eq!(SINGLE, collect_backward(0b0010));
    }

    #[test]
    fn boundaries() {
        const FORWARD: &[u32] = &[0, 63];
        const BACKWARD: &[u32] = &[63, 0];

        assert_eq!(FORWARD, collect_forward(1 << 63 | 1));
        assert_eq!(BACKWARD, collect_backward(1 << 63 | 1));
    }

    fn collect_forward(chunk: u64) -> Vec<u32> {
        BitInChunkIter::new(BitChunkRaw(chunk)).map(|i| i.0).collect()
    }

    fn collect_backward(chunk: u64) -> Vec<u32> {
        BitInChunkIterRev::new(BitChunkRaw(chunk)).map(|i| i.0).collect()
    }
} // in_chunk_tests

//
//  Of chunks iterators.
//

/// Forward iterator over a `BitChunkViewRaw`.
pub struct BitIndexOfChunkIter {
    of_chunk: Option<IndexOfChunkRaw>,
}

impl BitIndexOfChunkIter {
    /// Creates a new instance.
    pub fn new<V>(view: &V) -> Self
    where
        V: BitChunkViewRaw,
    {
        let of_chunk = view.first();

        Self { of_chunk }
    }

    /// Returns the next index.
    pub fn next<V>(&mut self, view: &V) -> Option<IndexOfChunkRaw>
    where
        V: BitChunkViewRaw,
    {
        let of_chunk = self.of_chunk?;

        self.of_chunk = of_chunk.checked_add(1).and_then(|i| view.next_after(i));

        Some(of_chunk)
    }
}

/// Backward (reverse) iterator over a `BitChunkViewRaw`.
pub struct BitIndexOfChunkIterRev {
    of_chunk: Option<IndexOfChunkRaw>,
}

impl BitIndexOfChunkIterRev {
    /// Creates a new instance.
    pub fn new<V>(view: &V) -> Self
    where
        V: BitChunkViewRaw,
    {
        let of_chunk = view.last();

        Self { of_chunk }
    }

    /// Returns the next index.
    pub fn next<V>(&mut self, view: &V) -> Option<IndexOfChunkRaw>
    where
        V: BitChunkViewRaw,
    {
        let of_chunk = self.of_chunk?;

        self.of_chunk = of_chunk.checked_sub(1).and_then(|i| view.next_before(i));

        Some(of_chunk)
    }
}

/// Forward iterator over a `BitChunkViewRaw`.
pub struct BitOfChunkIter<V> {
    index: BitIndexOfChunkIter,
    view: V,
}

impl<V> BitOfChunkIter<V>
where
    V: BitChunkViewRaw,
{
    /// Creates a new instance.
    pub fn new(view: V) -> Self {
        let index = BitIndexOfChunkIter::new(&view);

        Self { index, view }
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

impl<V> Iterator for BitOfChunkIter<V>
where
    V: BitChunkViewRaw,
{
    type Item = (IndexOfChunkRaw, BitChunkRaw);

    fn next(&mut self) -> Option<Self::Item> {
        let of_chunk = self.index.next(&self.view)?;

        //  Safety:
        //  -   `of_chunk` was obtained by either `view.first()` or `view.next_after(...)`.
        let chunk = unsafe { self.view.get_unchecked(of_chunk) };

        Some((of_chunk, chunk))
    }
}

/// Backward (reverse) iterator over a `BitChunkViewRaw`.
pub struct BitOfChunkIterRev<V> {
    index: BitIndexOfChunkIterRev,
    view: V,
}

impl<V> BitOfChunkIterRev<V>
where
    V: BitChunkViewRaw,
{
    /// Creates a new instance.
    pub fn new(view: V) -> Self {
        let index = BitIndexOfChunkIterRev::new(&view);

        Self { index, view }
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

impl<V> Iterator for BitOfChunkIterRev<V>
where
    V: BitChunkViewRaw,
{
    type Item = (IndexOfChunkRaw, BitChunkRaw);

    fn next(&mut self) -> Option<Self::Item> {
        let of_chunk = self.index.next(&self.view)?;

        //  Safety:
        //  -   `of_chunk` was obtained by either `view.last()` or `view.next_before(...)`.
        let chunk = unsafe { self.view.get_unchecked(of_chunk) };

        Some((of_chunk, chunk))
    }
}

#[cfg(test)]
mod of_chunk_tests {
    use super::*;

    #[test]
    fn empty() {
        const EMPTY: [BitChunkRaw; 0] = [];
        const EXPECTED: &[BitChunkRaw] = &[];

        assert_eq!(EXPECTED, collect(BitOfChunkIter::new(EMPTY)));
        assert_eq!(EXPECTED, collect(BitOfChunkIterRev::new(EMPTY)));
    }

    #[test]
    fn single() {
        const ONE: BitChunkRaw = BitChunkRaw(0b1001);

        const SINGLE: [BitChunkRaw; 1] = [ONE];
        const EXPECTED: &[BitChunkRaw] = &[ONE];

        assert_eq!(EXPECTED, collect(BitOfChunkIter::new(SINGLE)));
        assert_eq!(EXPECTED, collect(BitOfChunkIterRev::new(SINGLE)));
    }

    #[test]
    fn trio() {
        const ONE: BitChunkRaw = BitChunkRaw(0b1001);
        const TWO: BitChunkRaw = BitChunkRaw(0b0001);
        const THREE: BitChunkRaw = BitChunkRaw(0b1000);

        const TRIO: [BitChunkRaw; 3] = [ONE, TWO, THREE];
        const EXPECTED_FORWARD: &[BitChunkRaw] = &[ONE, TWO, THREE];
        const EXPECTED_BACKWARD: &[BitChunkRaw] = &[THREE, TWO, ONE];

        assert_eq!(EXPECTED_FORWARD, collect(BitOfChunkIter::new(TRIO)));
        assert_eq!(EXPECTED_BACKWARD, collect(BitOfChunkIterRev::new(TRIO)));
    }

    fn collect<I>(iter: I) -> Vec<BitChunkRaw>
    where
        I: Iterator<Item = (IndexOfChunkRaw, BitChunkRaw)>,
    {
        iter.map(|(_, c)| c).collect()
    }
} // mod of_chunk_tests
