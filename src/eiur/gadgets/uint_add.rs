use anyhow::Result;
use binius_circuits::builder::{witness::Builder, ConstraintSystemBuilder};
use binius_core::oracle::{OracleId, ShiftVariant};
use binius_field::{
    as_packed_field::PackScalar, underlier::UnderlierType, BinaryField1b as B1, TowerField,
};
use binius_macros::arith_expr;
use bytemuck::Pod;
use rayon::prelude::*;

use super::{Gadget, UIntType};

/// Gadget for overflowing addition over unsigned integers
pub struct UIntAdd;

#[derive(Clone, Copy)]
pub struct UIntAddInput {
    pub xin: OracleId,
    pub yin: OracleId,
    pub zout: OracleId,
    pub cout: OracleId,
}

pub struct UIntAddVirtual {
    pub cin: OracleId,
}

impl Gadget for UIntAdd {
    type InputOracles = UIntAddInput;
    type VirtualOracles = UIntAddVirtual;
    type Config = UIntType;

    fn constrain<F: TowerField, U: UnderlierType + PackScalar<F>>(
        builder: &mut ConstraintSystemBuilder<U, F>,
        name: impl ToString,
        input: UIntAddInput,
        enabled: OracleId,
        config: UIntType,
    ) -> Result<UIntAddVirtual> {
        builder.push_namespace(name);
        let UIntAddInput {
            xin,
            yin,
            zout,
            cout,
        } = input;
        let n_vars = config.n_vars();
        let cin = builder.add_shifted("cin", cout, 1, n_vars, ShiftVariant::LogicalLeft)?;

        builder.assert_zero(
            "sum",
            [xin, yin, cin, zout, enabled],
            arith_expr!([xin, yin, cin, zout, enabled] = enabled * (xin + yin + cin - zout))
                .convert_field(),
        );

        builder.assert_zero(
            "carry",
            [xin, yin, cin, cout, enabled],
            arith_expr!(
                [xin, yin, cin, cout, enabled] = enabled * ((xin + cin) * (yin + cin) + cin - cout)
            )
            .convert_field(),
        );

        builder.pop_namespace();
        Ok(UIntAddVirtual { cin })
    }

    /// Populates new columns for `zout`, `cout` and `cin` based on the values
    /// from `xin` and `yin`.
    fn generate_witness<F: TowerField, U: PackScalar<F> + PackScalar<B1> + Pod>(
        builder: &mut Builder<U, F>,
        input: UIntAddInput,
        vrtual: UIntAddVirtual,
        config: UIntType,
    ) -> Result<()> {
        let UIntAddInput {
            xin,
            yin,
            zout,
            cout,
        } = input;
        let UIntAddVirtual { cin } = vrtual;
        macro_rules! witgen {
            ($t:ty, $lsbits:expr) => {
                (
                    builder.get::<B1>(xin)?.as_slice::<$t>(),
                    builder.get::<B1>(yin)?.as_slice::<$t>(),
                    builder.new_column::<B1>(zout).as_mut_slice::<$t>(),
                    builder.new_column::<B1>(cout).as_mut_slice::<$t>(),
                    builder.new_column::<B1>(cin).as_mut_slice::<$t>(),
                )
                    .into_par_iter()
                    .for_each(|(xin, yin, zout, cout, cin)| {
                        let carry;
                        (*zout, carry) = xin.overflowing_add(*yin);
                        *cin = xin ^ yin ^ *zout;
                        *cout = ((carry as $t) << $lsbits) | (*cin >> 1);
                    })
            };
        }
        match config {
            UIntType::U8 => witgen!(u8, 7),
            UIntType::U16 => witgen!(u16, 15),
            UIntType::U32 => witgen!(u32, 31),
            UIntType::U64 => witgen!(u64, 63),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use binius_circuits::builder::{witness::Builder, ConstraintSystemBuilder};
    use binius_core::constraint_system::validate::validate_witness;
    use binius_field::{
        arch::OptimalUnderlier, underlier::SmallU, BinaryField128b, BinaryField1b as B1, TowerField,
    };
    use bumpalo::Bump;
    use proptest::{collection::vec, prelude::*};

    use crate::eiur::{
        binius::witness_builder,
        gadgets::{
            uint_add::{UIntAdd, UIntAddInput, UIntType},
            Gadget,
        },
    };
    const LEN: usize = 16;

    macro_rules! auto_test {
        ($fn:ident, $cfg:expr, $t:ty) => {
            #[test]
            fn $fn() {
                const N_VARS: usize = $cfg.n_vars() + LEN.ilog2() as usize;

                proptest!(|(
                    vec1 in vec(any::<$t>(), LEN),
                    vec2 in vec(any::<$t>(), LEN),
                )| {
                    let mut csb = ConstraintSystemBuilder::<OptimalUnderlier, BinaryField128b>::new();
                    let xin = csb.add_committed("xin", N_VARS, B1::TOWER_LEVEL);
                    let yin = csb.add_committed("yin", N_VARS, B1::TOWER_LEVEL);
                    let cout = csb.add_committed("cout", N_VARS, B1::TOWER_LEVEL);
                    let zout = csb.add_committed("zout", N_VARS, B1::TOWER_LEVEL);
                    let enabled = csb.add_committed("enabled", N_VARS, B1::TOWER_LEVEL);

                    let input = UIntAddInput {xin, yin, zout, cout};
                    let transparent = UIntAdd::constrain(&mut csb, "add", input, enabled, $cfg).unwrap();

                    let cs = csb.build().unwrap();

                    let allocator = Bump::new();
                    let mut wb: Builder<OptimalUnderlier, _> = witness_builder(&allocator, &cs);

                    wb.new_column::<B1>(xin).as_mut_slice().copy_from_slice(&vec1);
                    wb.new_column::<B1>(yin).as_mut_slice().copy_from_slice(&vec2);
                    wb.new_column_with_default(enabled, B1::new(SmallU::new(1)));

                    UIntAdd::generate_witness(&mut wb, input, transparent, $cfg).unwrap();

                    let res = vec1.into_iter().zip(vec2).map(|(a, b)| a.overflowing_add(b).0).collect::<Vec<_>>();
                    prop_assert_eq!(wb.get::<B1>(zout).unwrap().as_slice::<$t>(), &res);

                    let w = wb.build().unwrap();

                    prop_assert!(validate_witness(&cs, &[], &w).is_ok());
                });
            }
        };
    }

    auto_test!(test_add_u8, UIntType::U8, u8);
    auto_test!(test_add_u16, UIntType::U16, u16);
    auto_test!(test_add_u32, UIntType::U32, u32);
    auto_test!(test_add_u64, UIntType::U64, u64);
}
