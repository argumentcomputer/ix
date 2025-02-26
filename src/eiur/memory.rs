pub(crate) const NUM_MEM_TABLES: usize = 6;
pub(crate) const MEM_TABLE_SIZES: [usize; NUM_MEM_TABLES] = [2, 3, 4, 5, 6, 8];

#[inline]
#[allow(dead_code)]
pub(crate) fn mem_index_to_size(idx: usize) -> usize {
    MEM_TABLE_SIZES[idx]
}

#[inline]
pub(crate) fn mem_index_from_size(size: usize) -> usize {
    MEM_TABLE_SIZES
        .iter()
        .position(|&i| size == i)
        .unwrap_or_else(|| panic!("There are no mem tables of size {size}"))
}
