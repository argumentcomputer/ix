use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    underlier::SmallU,
};

use super::to_raw;

#[allow(trivial_numeric_casts)]
#[unsafe(no_mangle)]
extern "C" fn rs_add_u128_in_binary_field(a: &u128, b: &u128, tower_level: u8) -> *const u128 {
    macro_rules! add_for_binary_field {
        (lo, $t:ident) => {{
            let a = $t::new(SmallU::new((*a).try_into().unwrap()));
            let b = $t::new(SmallU::new((*b).try_into().unwrap()));
            let c = a + b;
            to_raw(c.val().val() as u128)
        }};
        (hi, $t:ident) => {{
            let a = $t::new((*a).try_into().unwrap());
            let b = $t::new((*b).try_into().unwrap());
            let c = a + b;
            to_raw(c.val() as u128)
        }};
    }
    match tower_level {
        0 => add_for_binary_field!(lo, B1),
        1 => add_for_binary_field!(lo, B2),
        2 => add_for_binary_field!(lo, B4),
        3 => add_for_binary_field!(hi, B8),
        4 => add_for_binary_field!(hi, B16),
        5 => add_for_binary_field!(hi, B32),
        6 => add_for_binary_field!(hi, B64),
        7 => add_for_binary_field!(hi, B128),
        _ => unreachable!(),
    }
}
