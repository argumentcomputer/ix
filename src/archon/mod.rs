pub mod arith_expr;
pub mod circuit;
pub mod precompiles;
pub mod protocol;
pub mod transparent;
pub mod witness;

use binius_core::oracle::{OracleId, ShiftVariant};
use binius_field::BinaryField128b;

use transparent::Transparent;

pub(crate) type F = BinaryField128b;

pub enum OracleKind {
    Committed,
    LinearCombination {
        offset: F,
        inner: Vec<(OracleId, F)>,
    },
    Packed {
        inner: OracleId,
        log_degree: usize,
    },
    Transparent(Transparent),
    StepDown,
    Shifted {
        inner: OracleId,
        shift_offset: usize,
        block_bits: usize,
        variant: ShiftVariant,
    },
    Projected {
        inner: OracleId,
        selector: ProjectedSelectorInfo,
        selector_binary: Vec<F>,
    },
}

pub type ModuleId = usize;

pub struct OracleInfo {
    pub name: String,
    pub tower_level: usize,
    pub kind: OracleKind,
}

pub struct ProjectedSelectorInfo {
    pub selector_value: u64,
    pub single_unprojected_len: u64,
}
