pub mod eiur;

use blake3::hash;

#[export_name = "blake3"]
pub extern "C" fn blake3(mem: &mut [u8; 32], len: usize, input: *const u8) {
    unsafe {
        *mem = *hash(std::slice::from_raw_parts(input, len)).as_bytes();
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(1 + 1, 2);
    }
}
