/// ```c
/// typedef struct {
///     int      m_rc;
///     unsigned m_cs_sz:16;
///     unsigned m_other:8;
///     unsigned m_tag:8;
/// } lean_object;
/// ```
#[repr(C)]
pub struct LeanObject {
    m_rc: i32,
    packed_bits: u32,
}

impl LeanObject {
    #[inline]
    pub fn m_cs_sz(&self) -> u16 {
        (self.packed_bits & 0xFFFF) as u16
    }

    #[inline]
    pub fn m_other(&self) -> u8 {
        ((self.packed_bits >> 16) & 0xFF) as u8
    }

    #[inline]
    pub fn m_tag(&self) -> u8 {
        ((self.packed_bits >> 24) & 0xFF) as u8
    }
}
