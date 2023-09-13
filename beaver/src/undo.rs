//! An array wrapper providing a convenient interface for backtracking changes.

use std::ops::Index;
use std::mem;

pub struct UndoArray<T, const N: usize> {
    array: [T; N],
}

impl<T, const N: usize> UndoArray<T, N> {
    pub fn new(array: [T; N]) -> Self {
        Self { array }
    }

    pub fn with<U>(
        &mut self,
        idx: usize,
        mut value: T,
        f: impl FnOnce(&mut Self) -> U,
    ) -> U {
        mem::swap(&mut self.array[idx], &mut value);
        let result = f(self);
        mem::swap(&mut self.array[idx], &mut value);
        result
    }
}

impl<T, const N: usize> Index<usize> for UndoArray<T, N> {
    type Output = T;

    fn index(&self, idx: usize) -> &T {
        &self.array[idx]
    }
}
