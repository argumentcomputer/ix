pub mod arith_expr;
pub mod circuit;
pub mod protocol;
pub mod transparent;
pub mod witness;

use binius_core::oracle::OracleId;
use binius_field::BinaryField128b;

use transparent::Transparent;

pub(crate) type F = BinaryField128b;

pub enum OracleKind {
    Committed,
    LinearCombination {
        offset: F,
        inner: Vec<(OracleId, F)>,
    },
    Transparent(Transparent),
}

pub type ModuleId = usize;

pub struct OracleInfo {
    pub name: String,
    pub tower_level: usize,
    pub kind: OracleKind,
}
