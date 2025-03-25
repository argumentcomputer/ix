use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    TowerField,
};

pub enum Transparent {
    Constant(ConstVal),
}

impl Transparent {
    #[inline]
    pub(crate) fn tower_level(&self) -> usize {
        match self {
            Self::Constant(c) => c.tower_level(),
        }
    }
}

pub enum ConstVal {
    B1(B1),
    B2(B2),
    B4(B4),
    B8(B8),
    B16(B16),
    B32(B32),
    B64(B64),
    B128(B128),
}

impl ConstVal {
    #[inline]
    fn tower_level(&self) -> usize {
        match self {
            Self::B1(_) => B1::TOWER_LEVEL,
            Self::B2(_) => B2::TOWER_LEVEL,
            Self::B4(_) => B4::TOWER_LEVEL,
            Self::B8(_) => B8::TOWER_LEVEL,
            Self::B16(_) => B16::TOWER_LEVEL,
            Self::B32(_) => B32::TOWER_LEVEL,
            Self::B64(_) => B64::TOWER_LEVEL,
            Self::B128(_) => B128::TOWER_LEVEL,
        }
    }
}
