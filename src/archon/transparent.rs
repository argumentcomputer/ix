use binius_core::{
    polynomial::{Error, MultivariatePoly},
    transparent::constant::Constant,
};
use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    Field, TowerField, underlier::WithUnderlier,
};

use super::F;

pub enum Transparent {
    Constant(B128),
    Incremental,
}

impl Transparent {
    #[inline]
    pub(crate) fn tower_level(&self) -> usize {
        match self {
            Self::Constant(b) => b.min_tower_level(),
            Self::Incremental => B64::TOWER_LEVEL,
        }
    }
}

#[derive(Debug)]
pub struct Incremental {
    pub(crate) n_vars: usize,
    pub(crate) tower_level: usize,
}

impl Incremental {
    #[inline]
    pub(crate) fn min_tower_level(height: u64) -> usize {
        // It's impossible to satisfy the evaluation within an underlier for
        // tower levels below 3.
        B64::new(height).min_tower_level().max(3)
    }
}

impl MultivariatePoly<F> for Incremental {
    fn degree(&self) -> usize {
        1
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }

    fn evaluate(&self, query: &[F]) -> Result<F, Error> {
        let n_vars = self.n_vars;
        if query.len() != n_vars {
            binius_utils::bail!(Error::IncorrectQuerySize { expected: n_vars });
        }
        let mut result = F::ZERO;
        let mut coeff = 1;
        for &arg in query {
            result += arg * F::from_underlier(coeff);
            coeff <<= 1;
        }

        Ok(result)
    }

    fn binary_tower_level(&self) -> usize {
        self.tower_level
    }
}

macro_rules! downcast {
    ($t:ident, $b128:ident) => {{
        let Ok(b) = TryInto::<$t>::try_into($b128) else {
            unreachable!();
        };
        b
    }};
}

pub(crate) fn constant_from_b128(b128: B128, n_vars: usize) -> Constant<F> {
    match b128.min_tower_level() {
        0 => Constant::new(n_vars, downcast!(B1, b128)),
        1 => Constant::new(n_vars, downcast!(B2, b128)),
        2 => Constant::new(n_vars, downcast!(B4, b128)),
        3 => Constant::new(n_vars, downcast!(B8, b128)),
        4 => Constant::new(n_vars, downcast!(B16, b128)),
        5 => Constant::new(n_vars, downcast!(B32, b128)),
        6 => Constant::new(n_vars, downcast!(B64, b128)),
        7 => Constant::new(n_vars, b128),
        _ => unreachable!(),
    }
}

pub(crate) fn replicate_within_u128(b128: B128) -> u128 {
    if b128 == B128::ZERO {
        return 0;
    }
    match b128.min_tower_level() {
        0 => u128::MAX,
        1 => replicate_2_bits(downcast!(B2, b128).to_underlier().val()),
        2 => replicate_4_bits(downcast!(B4, b128).to_underlier().val()),
        3 => u128::from_le_bytes([downcast!(B8, b128).to_underlier(); 16]),
        4 => {
            let u16s = [downcast!(B16, b128).to_underlier(); 8];
            unsafe { std::mem::transmute::<[u16; 8], u128>(u16s) }
        }
        5 => {
            let u32s = [downcast!(B32, b128).to_underlier(); 4];
            unsafe { std::mem::transmute::<[u32; 4], u128>(u32s) }
        }
        6 => {
            let u64s = [downcast!(B64, b128).to_underlier(); 2];
            unsafe { std::mem::transmute::<[u64; 2], u128>(u64s) }
        }
        7 => b128.to_underlier(),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn replicate_2_bits(byte: u8) -> u128 {
    let bits = (byte & 0b11) as u128; // Extract the first 2 bits
    bits * 0x55555555555555555555555555555555u128 // Repeat pattern 64 times
}

#[inline(always)]
fn replicate_4_bits(byte: u8) -> u128 {
    let bits = (byte & 0b1111) as u128; // Extract first 4 bits
    bits * 0x11111111111111111111111111111111u128 // Repeat pattern 16 times
}

#[cfg(test)]
mod tests {
    use crate::archon::transparent::{replicate_2_bits, replicate_4_bits};

    #[test]
    fn test_replicate_2_bits() {
        [
            (0b00000000, 0x00000000000000000000000000000000u128),
            (0b00000001, 0x55555555555555555555555555555555u128),
            (0b00000010, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAu128),
            (0b00000011, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFu128),
        ]
        .into_iter()
        .for_each(|(byte, u128)| assert_eq!(replicate_2_bits(byte), u128));
    }

    #[test]
    fn test_replicate_4_bits() {
        [
            (0b00000000, 0x00000000000000000000000000000000u128),
            (0b00000001, 0x11111111111111111111111111111111u128),
            (0b00000010, 0x22222222222222222222222222222222u128),
            (0b00000011, 0x33333333333333333333333333333333u128),
            (0b00000100, 0x44444444444444444444444444444444u128),
            (0b00000101, 0x55555555555555555555555555555555u128),
            (0b00000110, 0x66666666666666666666666666666666u128),
            (0b00000111, 0x77777777777777777777777777777777u128),
            (0b00001000, 0x88888888888888888888888888888888u128),
            (0b00001001, 0x99999999999999999999999999999999u128),
            (0b00001010, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAu128),
            (0b00001011, 0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBu128),
            (0b00001100, 0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCu128),
            (0b00001101, 0xDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDu128),
            (0b00001110, 0xEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEu128),
            (0b00001111, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFu128),
        ]
        .into_iter()
        .for_each(|(byte, u128)| assert_eq!(replicate_4_bits(byte), u128));
    }
}
