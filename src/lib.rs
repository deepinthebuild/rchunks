use std::iter::{DoubleEndedIterator, ExactSizeIterator};

pub struct RChunksIter<'a, T: 'a> {
    v: &'a [T],
    size: usize,
}

impl<'a, T> Iterator for RChunksIter<'a, T> {
    type Item = &'a [T];

    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let (head, tail) = self.v.split_at(self.v.len().saturating_sub(self.size));
            self.v = head;
            Some(tail)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (quo, rem) = (self.v.len() / self.size, self.v.len() % self.size);

        if rem == 0 {
            (quo, Some(quo))
        } else {
            (quo + 1, Some(quo + 1))
        }
    }
}

impl<'a, T> ExactSizeIterator for RChunksIter<'a, T> {
    fn len(&self) -> usize {
        self.size_hint().0
    }
}

impl<'a, T> DoubleEndedIterator for RChunksIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let rem = self.v.len() % self.size;
            if rem == 0 {
                let (head, tail) = self.v.split_at(self.size);
                self.v = tail;
                Some(head)
            } else {
                let (head, tail) = self.v.split_at(rem);
                self.v = tail;
                Some(head)
            }
        }
    }
}

pub struct RChunksMutIter<'a, T: 'a> {
    v: &'a mut [T],
    size: usize,
}

impl<'a, T> Iterator for RChunksMutIter<'a, T> {
    type Item = &'a mut [T];

    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() {
            None
        } else {
            let sz = self.v.len().saturating_sub(self.size);
            let tmp = std::mem::replace(&mut self.v, &mut []);
            let (head, tail) = tmp.split_at_mut(sz);
            self.v = head;
            Some(tail)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (quo, rem) = (self.v.len() / self.size, self.v.len() % self.size);

        if rem == 0 {
            (quo, Some(quo))
        } else {
            (quo + 1, Some(quo + 1))
        }
    }
}

impl<'a, T> DoubleEndedIterator for RChunksMutIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let rem = self.v.len() % self.size;
            if rem == 0 {
                let tmp = std::mem::replace(&mut self.v, &mut []);
                let (head, tail) = tmp.split_at_mut(self.size);
                self.v = tail;
                Some(head)
            } else {
                let tmp = std::mem::replace(&mut self.v, &mut []);
                let (head, tail) = tmp.split_at_mut(rem);
                self.v = tail;
                Some(head)
            }
        }
    }
}

impl<'a, T> ExactSizeIterator for RChunksMutIter<'a, T> {
    fn len(&self) -> usize {
        self.size_hint().0
    }
}

pub trait RChunks {
    type Item;
    fn rchunks<'a>(&'a self, chunk_size: usize) -> RChunksIter<'a, Self::Item>;

    fn rchunks_mut<'a>(&'a mut self, chunk_size: usize) -> RChunksMutIter<'a, Self::Item>;
}

impl<T> RChunks for [T] {
    type Item = T;
    fn rchunks<'a>(&'a self, chunk_size: usize) -> RChunksIter<'a, Self::Item> {
        assert!(chunk_size != 0, "Size passed to rchunks must be non-zero");
        RChunksIter {
            v: self,
            size: chunk_size,
        }
    }

    fn rchunks_mut<'a>(&'a mut self, chunk_size: usize) -> RChunksMutIter<'a, Self::Item> {
        assert!(chunk_size != 0, "Size passed to rchunks_mut must be non-zero");
        RChunksMutIter {
            v: self,
            size: chunk_size,
        }
    }
}

#[test]
#[should_panic]
fn rchunks_test_0() {
    let _s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut _s_iter = _s.rchunks(0);
}

#[test]
fn rchunks_test_1() {
    let s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut s_iter = s.rchunks(3);

    assert_eq!(s_iter.next().unwrap(), &[7usize, 8, 9]);
    assert_eq!(s_iter.next().unwrap(), &[4usize, 5, 6]);
    assert_eq!(s_iter.next().unwrap(), &[1usize, 2, 3]);
    assert_eq!(s_iter.next().unwrap(), &[0usize]);
    assert!(s_iter.next().is_none());
}

#[test]
fn rchunks_double_ended_test() {
    let s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut s_iter = s.rchunks(3);

    assert_eq!(s_iter.next_back().unwrap(), &[0usize]);
    assert_eq!(s_iter.next().unwrap(), &[7usize, 8, 9]);
    assert_eq!(s_iter.next_back().unwrap(), &[1usize, 2, 3]);
    assert_eq!(s_iter.next().unwrap(), &[4usize, 5, 6]);
    assert!(s_iter.next().is_none());
}

#[test]
fn rchunks_size_hint_test() {
    let s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert_eq!(s.rchunks(3).size_hint(), (4, Some(4)));
}

#[test]
#[should_panic]
fn rchunks_mut_test_0() {
    let mut _s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut _s_iter = _s.rchunks_mut(0);
}

#[test]
fn rchunks_mut_test_1() {
    let mut s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut s_iter = s.rchunks_mut(3);

    assert_eq!(s_iter.next().unwrap(), &[7usize, 8, 9]);
    assert_eq!(s_iter.next().unwrap(), &[4usize, 5, 6]);
    assert_eq!(s_iter.next().unwrap(), &[1usize, 2, 3]);
    assert_eq!(s_iter.next().unwrap(), &[0usize]);
    assert!(s_iter.next().is_none());
}

#[test]
fn rchunks_mut_double_ended_test() {
    let mut s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut s_iter = s.rchunks_mut(3);

    assert_eq!(s_iter.next_back().unwrap(), &[0usize]);
    assert_eq!(s_iter.next().unwrap(), &[7usize, 8, 9]);
    assert_eq!(s_iter.next_back().unwrap(), &[1usize, 2, 3]);
    assert_eq!(s_iter.next().unwrap(), &[4usize, 5, 6]);
    assert!(s_iter.next().is_none());
}

#[test]
fn rchunks_mut_size_hint_test() {
    let mut s = vec![0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert_eq!(s.rchunks_mut(3).size_hint(), (4, Some(4)));
}