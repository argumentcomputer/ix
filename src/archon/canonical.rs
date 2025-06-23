use binius_core::{constraint_system::channel::FlushDirection, oracle::ShiftVariant};
use binius_field::BinaryField128b;
use binius_utils::checked_arithmetics::log2_strict_usize;

use super::{
    OracleIdx, OracleInfo, OracleKind, RelativeHeight,
    arith_expr::ArithExpr,
    circuit::{ArchonExp, ArchonFlush, ArchonOracleOrConst, CircuitModule, Constraint},
    transparent::Transparent,
};

pub(crate) trait Canonical {
    fn size(&self) -> usize;
    fn write(&self, buffer: &mut Vec<u8>);
}

impl Canonical for usize {
    fn size(&self) -> usize {
        size_of::<usize>()
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        buffer.extend(self.to_le_bytes());
    }
}

impl Canonical for u32 {
    fn size(&self) -> usize {
        size_of::<u32>()
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        buffer.extend(self.to_le_bytes());
    }
}

impl Canonical for u64 {
    fn size(&self) -> usize {
        size_of::<u64>()
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        buffer.extend(self.to_le_bytes());
    }
}

impl Canonical for BinaryField128b {
    fn size(&self) -> usize {
        size_of::<u128>()
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        buffer.extend(self.val().to_le_bytes());
    }
}

impl Canonical for Transparent {
    fn size(&self) -> usize {
        match self {
            Self::Constant(b128) => 1 + Canonical::size(b128),
            Self::Incremental => 1,
        }
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::Constant(b128) => {
                buffer.push(0);
                Canonical::write(b128, buffer);
            }
            Self::Incremental => buffer.push(1),
        }
    }
}

impl Canonical for ShiftVariant {
    fn size(&self) -> usize {
        1
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::CircularLeft => buffer.push(0),
            Self::LogicalLeft => buffer.push(1),
            Self::LogicalRight => buffer.push(2),
        }
    }
}

impl<A: Canonical, B: Canonical> Canonical for (A, B) {
    fn size(&self) -> usize {
        let (a, b) = self;
        Canonical::size(a) + Canonical::size(b)
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        let (a, b) = self;
        Canonical::write(a, buffer);
        Canonical::write(b, buffer);
    }
}

impl<T: Canonical> Canonical for Vec<T> {
    fn size(&self) -> usize {
        self.iter().map(Canonical::size).sum()
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        for t in self {
            Canonical::write(t, buffer);
        }
    }
}

impl Canonical for OracleIdx {
    fn size(&self) -> usize {
        Canonical::size(&self.val())
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        Canonical::write(&self.val(), buffer);
    }
}

impl Canonical for OracleKind {
    fn size(&self) -> usize {
        match self {
            Self::Committed | Self::StepDown => 1,
            Self::LinearCombination { offset, inner } => {
                1 + Canonical::size(offset) + Canonical::size(inner)
            }
            Self::Packed { inner, log_degree } => {
                1 + Canonical::size(inner) + Canonical::size(log_degree)
            }
            Self::Transparent(transparent) => 1 + Canonical::size(transparent),
            Self::Shifted {
                inner,
                shift_offset,
                block_bits,
                variant,
            } => {
                1 + Canonical::size(inner)
                    + Canonical::size(shift_offset)
                    + Canonical::size(block_bits)
                    + Canonical::size(variant)
            }
            Self::Projected {
                inner, selection, ..
            } => 1 + Canonical::size(inner) + Canonical::size(selection) + size_of::<u8>(),
        }
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::Committed => buffer.push(0),
            Self::LinearCombination { offset, inner } => {
                buffer.push(1);
                Canonical::write(offset, buffer);
                Canonical::write(inner, buffer);
            }
            Self::Packed { inner, log_degree } => {
                buffer.push(2);
                Canonical::write(inner, buffer);
                Canonical::write(log_degree, buffer);
            }
            Self::Transparent(transparent) => {
                buffer.push(3);
                Canonical::write(transparent, buffer);
            }
            Self::StepDown => buffer.push(4),
            Self::Shifted {
                inner,
                shift_offset,
                block_bits,
                variant,
            } => {
                buffer.push(5);
                Canonical::write(inner, buffer);
                Canonical::write(shift_offset, buffer);
                Canonical::write(block_bits, buffer);
                Canonical::write(variant, buffer);
            }
            Self::Projected {
                inner,
                selection,
                chunk_size,
                ..
            } => {
                buffer.push(6);
                Canonical::write(inner, buffer);
                Canonical::write(selection, buffer);
                buffer.push(log2_strict_usize(*chunk_size).to_le_bytes()[0]);
            }
        }
    }
}

impl Canonical for RelativeHeight {
    fn size(&self) -> usize {
        match self {
            Self::Base => 1,
            Self::Div2(_) | Self::Mul2(_) => 2,
        }
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::Base => buffer.push(0),
            Self::Div2(x) => {
                buffer.push(1);
                buffer.push(*x);
            }
            Self::Mul2(x) => {
                buffer.push(2);
                buffer.push(*x);
            }
        }
    }
}

impl Canonical for OracleInfo {
    fn size(&self) -> usize {
        let Self {
            name: _,
            tower_level,
            kind,
            relative_height,
        } = self;
        Canonical::size(tower_level) + Canonical::size(kind) + Canonical::size(relative_height)
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        let Self {
            name: _,
            tower_level,
            kind,
            relative_height,
        } = self;
        Canonical::write(tower_level, buffer);
        Canonical::write(kind, buffer);
        Canonical::write(relative_height, buffer);
    }
}

impl Canonical for FlushDirection {
    fn size(&self) -> usize {
        1
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::Push => buffer.push(0),
            Self::Pull => buffer.push(1),
        }
    }
}

impl Canonical for ArchonFlush {
    fn size(&self) -> usize {
        let Self {
            oracles,
            channel_id,
            direction,
            selector,
            multiplicity,
        } = self;
        Canonical::size(oracles)
            + Canonical::size(channel_id)
            + Canonical::size(direction)
            + Canonical::size(selector)
            + Canonical::size(multiplicity)
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        let Self {
            oracles,
            channel_id,
            direction,
            selector,
            multiplicity,
        } = self;
        Canonical::write(oracles, buffer);
        Canonical::write(channel_id, buffer);
        Canonical::write(direction, buffer);
        Canonical::write(selector, buffer);
        Canonical::write(multiplicity, buffer);
    }
}

impl Canonical for ArithExpr {
    fn size(&self) -> usize {
        match self {
            Self::Const(b128) => 1 + Canonical::size(b128),
            Self::Var(v) => 1 + Canonical::size(v),
            Self::Oracle(o) => 1 + Canonical::size(o),
            Self::Add(a, b) | Self::Mul(a, b) => {
                1 + Canonical::size(a.as_ref()) + Canonical::size(b.as_ref())
            }
            Self::Pow(a, e) => 1 + Canonical::size(a.as_ref()) + Canonical::size(e),
        }
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::Const(b128) => {
                buffer.push(0);
                Canonical::write(b128, buffer);
            }
            Self::Var(v) => {
                buffer.push(1);
                Canonical::write(v, buffer);
            }
            Self::Oracle(o) => {
                buffer.push(2);
                Canonical::write(o, buffer);
            }
            Self::Add(a, b) => {
                buffer.push(3);
                Canonical::write(a.as_ref(), buffer);
                Canonical::write(b.as_ref(), buffer);
            }
            Self::Mul(a, b) => {
                buffer.push(4);
                Canonical::write(a.as_ref(), buffer);
                Canonical::write(b.as_ref(), buffer);
            }
            Self::Pow(a, e) => {
                buffer.push(5);
                Canonical::write(a.as_ref(), buffer);
                Canonical::write(e, buffer);
            }
        }
    }
}

impl Canonical for Constraint {
    fn size(&self) -> usize {
        let Self {
            name: _,
            oracle_idxs: oracle_ids,
            composition,
        } = self;
        Canonical::size(oracle_ids) + Canonical::size(composition)
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        let Self {
            name: _,
            oracle_idxs: oracle_ids,
            composition,
        } = self;
        Canonical::write(oracle_ids, buffer);
        Canonical::write(composition, buffer);
    }
}

impl Canonical for ArchonOracleOrConst {
    fn size(&self) -> usize {
        match self {
            Self::Oracle(o) => 1 + Canonical::size(o),
            Self::Const { base, tower_level } => {
                1 + Canonical::size(base) + Canonical::size(tower_level)
            }
        }
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        match self {
            Self::Oracle(o) => {
                buffer.push(0);
                Canonical::write(o, buffer);
            }
            Self::Const { base, tower_level } => {
                buffer.push(1);
                Canonical::write(base, buffer);
                Canonical::write(tower_level, buffer);
            }
        }
    }
}

impl Canonical for ArchonExp {
    fn size(&self) -> usize {
        let Self {
            exp_bits,
            base,
            result,
        } = self;
        Canonical::size(exp_bits) + Canonical::size(base) + Canonical::size(result)
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        let Self {
            exp_bits,
            base,
            result,
        } = self;
        Canonical::write(exp_bits, buffer);
        Canonical::write(base, buffer);
        Canonical::write(result, buffer);
    }
}

impl Canonical for CircuitModule {
    fn size(&self) -> usize {
        let Self {
            module_id,
            oracles,
            flushes,
            constraints,
            non_zero_oracle_idxs,
            exponents,
            namespacer: _,
        } = self;
        Canonical::size(module_id)
            + Canonical::size(oracles.get_ref())
            + Canonical::size(flushes)
            + Canonical::size(constraints)
            + Canonical::size(non_zero_oracle_idxs)
            + Canonical::size(exponents)
    }
    fn write(&self, buffer: &mut Vec<u8>) {
        let Self {
            module_id,
            oracles,
            flushes,
            constraints,
            non_zero_oracle_idxs,
            exponents,
            namespacer: _,
        } = self;
        Canonical::write(module_id, buffer);
        Canonical::write(oracles.get_ref(), buffer);
        Canonical::write(flushes, buffer);
        Canonical::write(constraints, buffer);
        Canonical::write(non_zero_oracle_idxs, buffer);
        Canonical::write(exponents, buffer);
    }
}
