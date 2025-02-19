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
    pub m_rc: i32,
    packed_bits: u32,
}

impl LeanObject {
    #[inline]
    pub fn new(m_rc: i32, m_cs_sz: u16, m_other: u8, m_tag: u8) -> Self {
        let packed_bits = m_cs_sz as u32 | ((m_other as u32) << 16) | ((m_tag as u32) << 24);
        Self { m_rc, packed_bits }
    }

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
