pub mod arith_expr;
pub mod canonical;
pub mod circuit;
pub mod precompiles;
pub mod protocol;
pub mod transparent;
pub mod witness;

use binius_core::oracle::{OracleId, ShiftVariant};
use binius_field::BinaryField128b;

use transparent::Transparent;

pub(crate) type F = BinaryField128b;

#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OracleIdx(pub(crate) usize);

impl OracleIdx {
    #[inline]
    pub(crate) fn oracle_id(&self, offset: usize) -> OracleId {
        OracleId::from_index(self.0 + offset)
    }

    #[inline]
    pub(crate) fn val(&self) -> usize {
        self.0
    }

    #[inline]
    pub(crate) fn offset(&mut self, by: usize) {
        self.0 += by
    }
}

impl std::fmt::Display for OracleIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.val(), f)
    }
}

pub enum OracleKind {
    Committed,
    LinearCombination {
        offset: F,
        inner: Vec<(OracleIdx, F)>,
    },
    Packed {
        inner: OracleIdx,
        log_degree: usize,
    },
    Transparent(Transparent),
    StepDown,
    Shifted {
        inner: OracleIdx,
        shift_offset: u32,
        block_bits: usize,
        variant: ShiftVariant,
    },
    Projected {
        inner: OracleIdx,
        mask: u64,
        /// Cached bits for slightly faster circuit compilation
        mask_bits: Vec<F>,
        unprojected_size: usize,
    },
}

pub type ModuleId = usize;

pub struct OracleInfo {
    pub name: String,
    pub tower_level: usize,
    pub kind: OracleKind,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ModuleMode {
    /// An inactive module must be skipped during compilation.
    Inactive,
    /// An active module has a selector column with `height = 1 << log_height`
    /// rows. This column is a `StepDown` oracle with `index = depth <= height`.
    Active { log_height: u8, depth: u64 },
}

impl ModuleMode {
    #[inline]
    pub const fn active(log_height: u8, depth: u64) -> Self {
        Self::Active { log_height, depth }
    }
}
