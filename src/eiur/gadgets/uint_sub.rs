use anyhow::Result;
use binius_circuits::builder::{witness::Builder, ConstraintSystemBuilder};
use binius_core::oracle::OracleId;
use binius_field::BinaryField1b as B1;
use rayon::prelude::*;

use super::{
    uint_add::{UIntAdd, UIntAddInput, UIntAddVirtual},
    Gadget, UIntType,
};

/// Gadget for underflowing subtraction over unsigned integers
pub struct UIntSub;

#[derive(Clone, Copy)]
pub struct UIntSubInput {
    zin: OracleId,
    yin: OracleId,
    cout: OracleId,
    xout: OracleId,
}

pub struct UIntSubVirtual {
    cin: OracleId,
}

impl Gadget for UIntSub {
    type InputOracles = UIntSubInput;
    type VirtualOracles = UIntSubVirtual;
    type Config = UIntType;

    fn constrain(
        builder: &mut ConstraintSystemBuilder,
        name: impl ToString,
        input: UIntSubInput,
        enabled: OracleId,
        config: UIntType,
    ) -> Result<UIntSubVirtual> {
        builder.push_namespace(name);
        let UIntSubInput {
            zin,
            yin,
            cout,
            xout,
        } = input;
        let add_input = UIntAddInput {
            xin: xout,
            yin,
            cout,
            zout: zin,
        };
        let UIntAddVirtual { cin } =
            UIntAdd::constrain(builder, "add", add_input, enabled, config)?;
        builder.pop_namespace();
        Ok(UIntSubVirtual { cin })
    }

    /// Populates new columns for `xout`, `cout` and `cin` based on the values
    /// from `zin` and `yin`.
    fn generate_witness(
        builder: &mut Builder,
        input: UIntSubInput,
        vrtual: UIntSubVirtual,
        config: UIntType,
    ) -> Result<()> {
        let UIntSubInput {
            zin,
            yin,
            cout,
            xout,
        } = input;
        let UIntSubVirtual { cin } = vrtual;
        macro_rules! witgen {
            ($t:ty, $lsbits:expr) => {
                (
                    builder.get::<B1>(zin)?.as_slice::<$t>(),
                    builder.get::<B1>(yin)?.as_slice::<$t>(),
                    builder.new_column::<B1>(xout).as_mut_slice::<$t>(),
                    builder.new_column::<B1>(cout).as_mut_slice::<$t>(),
                    builder.new_column::<B1>(cin).as_mut_slice::<$t>(),
                )
                    .into_par_iter()
                    .for_each(|(zout, yin, xin, cout, cin)| {
                        let carry;
                        (*xin, carry) = (*zout).overflowing_sub(*yin);
                        *cin = (*xin) ^ (*yin) ^ (*zout);
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
    use binius_field::{underlier::SmallU, BinaryField1b as B1, TowerField};
    use bumpalo::Bump;
    use proptest::{collection::vec, prelude::*};

    use crate::eiur::{
        binius::witness_builder,
        gadgets::{
            uint_sub::{UIntSub, UIntSubInput},
            Gadget, UIntType,
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
                    let mut csb = ConstraintSystemBuilder::new();
                    let zin = csb.add_committed("zin", N_VARS, B1::TOWER_LEVEL);
                    let yin = csb.add_committed("yin", N_VARS, B1::TOWER_LEVEL);
                    let cout = csb.add_committed("cout", N_VARS, B1::TOWER_LEVEL);
                    let xout = csb.add_committed("xout", N_VARS, B1::TOWER_LEVEL);
                    let enabled = csb.add_committed("enabled", N_VARS, B1::TOWER_LEVEL);

                    let input = UIntSubInput {zin, yin, cout, xout};
                    let transparent = UIntSub::constrain(&mut csb, "sub", input, enabled, $cfg).unwrap();

                    let cs = csb.build().unwrap();

                    let allocator = Bump::new();
                    let mut wb: Builder = witness_builder(&allocator, &cs);

                    wb.new_column::<B1>(zin).as_mut_slice().copy_from_slice(&vec1);
                    wb.new_column::<B1>(yin).as_mut_slice().copy_from_slice(&vec2);
                    wb.new_column_with_default(enabled, B1::new(SmallU::new(1)));

                    UIntSub::generate_witness(&mut wb, input, transparent, $cfg).unwrap();

                    let res = vec1.into_iter().zip(vec2).map(|(a, b)| a.overflowing_sub(b).0).collect::<Vec<_>>();
                    prop_assert_eq!(wb.get::<B1>(xout).unwrap().as_slice::<$t>(), &res);

                    let w = wb.build().unwrap();

                    prop_assert!(validate_witness(&cs, &[], &w).is_ok());
                });
            }
        };
    }

    auto_test!(test_sub_u8, UIntType::U8, u8);
    auto_test!(test_sub_u16, UIntType::U16, u16);
    auto_test!(test_sub_u32, UIntType::U32, u32);
    auto_test!(test_sub_u64, UIntType::U64, u64);
}
