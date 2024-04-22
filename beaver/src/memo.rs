use ndarray::{Array, NdIndex, IntoDimension};

pub struct Memo<'a, A, D, I> {
    memo: Array<Option<A>, D>,
    f: &'a dyn for<'b> Fn(I, &'b mut Memo<'a, A, D, I>) -> A,
}

impl<'a, A, D, I> Memo<'a, A, D, I>
    where
    A: Copy,
    I: IntoDimension<Dim = D> + NdIndex<D> + Copy,
    D: ndarray::Dimension,
{
    pub fn new(shape: I, f: &'a dyn for<'b> Fn(I, &'b mut Self) -> A) -> Self {
        Self {
            memo: Array::from_elem(shape, None),
            f,
        }
    }

    pub fn get(&mut self, index: I) -> A {
        if let Some(value) = self.memo[index] {
            value
        } else {
            let value = (self.f)(index, self);
            self.memo[index] = Some(value);
            value
        }
    }
}
