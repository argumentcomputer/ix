use lean_sys::object::LeanByteArray;

#[unsafe(no_mangle)]
extern "C" fn c_u16_to_le_bytes(v: u16) -> LeanByteArray {
  LeanByteArray::from_bytes(&v.to_le_bytes())
}

#[unsafe(no_mangle)]
extern "C" fn c_u32_to_le_bytes(v: u32) -> LeanByteArray {
  LeanByteArray::from_bytes(&v.to_le_bytes())
}

#[unsafe(no_mangle)]
extern "C" fn c_u64_to_le_bytes(v: u64) -> LeanByteArray {
  LeanByteArray::from_bytes(&v.to_le_bytes())
}

#[unsafe(no_mangle)]
extern "C" fn c_usize_to_le_bytes(v: usize) -> LeanByteArray {
  LeanByteArray::from_bytes(&v.to_le_bytes())
}
