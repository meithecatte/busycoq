use ndarray::{Array, NdIndex, IntoDimension};
use std::cell::Cell;

pub struct Memo<'a, A, D, I> {
    memo: Array<Cell<Option<A>>, D>,
    f: &'a dyn for<'b> Fn(I, &'b Memo<'a, A, D, I>) -> A,
}

impl<'a, A, D, I> Memo<'a, A, D, I>
    where
    A: Copy,
    I: IntoDimension<Dim = D> + NdIndex<D> + Copy,
    D: ndarray::Dimension,
{
    pub fn new(shape: I, f: &'a dyn for<'b> Fn(I, &'b Self) -> A) -> Self {
        Self {
            memo: Array::from_elem(shape, Cell::new(None)),
            f,
        }
    }

    pub fn get(&self, index: I) -> A {
        if self.memo[index].get().is_none() {
            let value = (self.f)(index, self);
            self.memo[index].set(Some(value));
        }

        self.memo[index].get().unwrap()
    }
}
