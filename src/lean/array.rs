use super::{boxed_usize::BoxedUSize, object::LeanObject, CArray};

/// ```c
/// typedef struct {
///     lean_object   m_header;
///     size_t        m_size;
///     size_t        m_capacity;
///     lean_object * m_data[];
/// } lean_array_object;
/// ```
#[repr(C)]
pub struct LeanArrayObject<T> {
    pub m_header: LeanObject,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: CArray<*const T>,
}

impl<T> LeanArrayObject<T> {
    #[inline]
    pub fn data(&self) -> &[*const T] {
        self.m_data.slice(self.m_size)
    }
}

pub type LeanArrayUSize = LeanArrayObject<BoxedUSize>;

impl LeanArrayUSize {
    pub fn to_vec(&self) -> Vec<usize> {
        let mut vec = Vec::with_capacity(self.m_size);
        for &boxed_usize_ptr in self.data() {
            let boxed_usize = unsafe { &*boxed_usize_ptr };
            vec.push(boxed_usize.value);
        }
        vec
    }
}
