//! Fixed-arity host calls. Erase the type of the complete register handler,
//! after specializing argument gathering, the provider, and result writes.
use crate::{bytecode::Layout, field::FieldBackend};
use std::sync::Arc;

type Validator<F> = dyn Fn(&[F]) -> Result<(), String> + Send + Sync;
pub(crate) type OutputCheck<F> = Option<Arc<Validator<F>>>;
pub(crate) type RegisterMap<F> =
  dyn Fn(&mut [F], &mut [u64]) -> Result<(), String> + Send + Sync;
pub(crate) type MapCalls<F> = Vec<Option<Arc<RegisterMap<F>>>>;
pub(crate) type RegisterHint<F> =
  dyn Fn(&mut [F]) -> Result<(), String> + Send + Sync;
pub(crate) type MapBinder<F> = dyn Fn(&[usize], &[usize], OutputCheck<F>) -> Option<Arc<RegisterMap<F>>>
  + Send
  + Sync;
pub(crate) type HintBinder<F> = dyn Fn(&[usize], &[usize], OutputCheck<F>) -> Option<Arc<RegisterHint<F>>>
  + Send
  + Sync;

pub(crate) fn output_check<B: FieldBackend>(
  layout: &Layout,
  field: B,
) -> OutputCheck<B::Element> {
  if B::ALL_ELEMENTS_VALID && !layout.has_shape_checks() {
    None
  } else {
    let layout = layout.clone();
    Some(Arc::new(move |output| layout.validate(output, field)))
  }
}

#[inline]
pub(crate) fn bump(counts: &mut [u64], row: usize) -> Result<(), String> {
  let count =
    counts.get_mut(row).ok_or("map override row index out of bounds")?;
  *count = count.checked_add(1).ok_or("map multiplicity overflow")?;
  Ok(())
}

pub(crate) fn map_binder<F, C, const INPUTS: usize, const OUTPUTS: usize>(
  function: Arc<C>,
) -> Arc<MapBinder<F>>
where
  F: Copy + Send + Sync + 'static,
  C: Fn([F; INPUTS]) -> Result<(usize, [F; OUTPUTS]), String>
    + Send
    + Sync
    + 'static,
{
  Arc::new(move |args, dest, check| {
    // Unreachable bytecode may have arbitrary operand widths. Leave those
    // sites on the generic path instead of rejecting an otherwise valid program.
    let args: [usize; INPUTS] = args.try_into().ok()?;
    let dest: [usize; OUTPUTS] = dest.try_into().ok()?;
    let function = function.clone();
    Some(Arc::new(move |registers, counts| {
      // Gather all inputs before writing any output, including aliased
      // operands and destinations. C is still concrete at this point.
      let input = std::array::from_fn(|i| registers[args[i]]);
      let (row, output) = function(input)?;
      if let Some(check) = &check {
        check(&output)?;
      }
      bump(counts, row)?;
      for i in 0..OUTPUTS {
        registers[dest[i]] = output[i];
      }
      Ok(())
    }))
  })
}

pub(crate) fn hint_binder<F, C, const INPUTS: usize, const OUTPUTS: usize>(
  function: Arc<C>,
) -> Arc<HintBinder<F>>
where
  F: Copy + Send + Sync + 'static,
  C: Fn([F; INPUTS]) -> Result<[F; OUTPUTS], String> + Send + Sync + 'static,
{
  Arc::new(move |args, dest, check| {
    let args: [usize; INPUTS] = args.try_into().ok()?;
    let dest: [usize; OUTPUTS] = dest.try_into().ok()?;
    let function = function.clone();
    Some(Arc::new(move |registers| {
      let input = std::array::from_fn(|i| registers[args[i]]);
      let output = function(input)?;
      if let Some(check) = &check {
        check(&output)?;
      }
      for i in 0..OUTPUTS {
        registers[dest[i]] = output[i];
      }
      Ok(())
    }))
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn register_handlers_gather_before_writes_and_check_count_errors() {
    let binder =
      map_binder(Arc::new(|[a, b]: [u64; 2]| Ok(((a + b) as usize, [b, a]))));
    let call = binder(&[0, 1], &[0, 1], None).unwrap();
    let mut registers = [2, 5];
    let mut counts = [0; 8];
    call(&mut registers, &mut counts).unwrap();
    assert_eq!(registers, [5, 2]);
    assert_eq!(counts[7], 1);
    counts[7] = u64::MAX;
    assert!(
      call(&mut registers, &mut counts).unwrap_err().contains("overflow")
    );
    assert_eq!(registers, [5, 2]);
    assert_eq!(counts[7], u64::MAX);
    assert!(
      call(&mut registers, &mut []).unwrap_err().contains("out of bounds")
    );
    assert_eq!(registers, [5, 2]);

    let binder = hint_binder(Arc::new(|[a, b]: [u64; 2]| Ok([b, a])));
    let call = binder(&[0, 1], &[0, 1], None).unwrap();
    call(&mut registers).unwrap();
    assert_eq!(registers, [2, 5]);
  }

  #[test]
  fn native_fields_keep_enum_validation() {
    use crate::{
      bytecode::{Constructor, Enum, Type},
      field::{NativeField, PrimeField},
    };
    use multi_stark::p3_goldilocks::Goldilocks;
    let field = NativeField::<Goldilocks>::new();
    assert!(output_check(&Layout::Field, field).is_none());
    let scalar_check =
      output_check(&Layout::Field, PrimeField::new(97).unwrap()).unwrap();
    assert!(scalar_check(&[97]).is_err());
    let layout = Type::Enum { name: "Choice".into() }
      .layout(
        &[Enum {
          name: "Choice".into(),
          constructors: vec![
            Constructor { name: "None".into(), fields: vec![] },
            Constructor { name: "Some".into(), fields: vec![Type::Field] },
          ],
        }],
        &mut vec![],
      )
      .unwrap();
    for (words, message) in
      [([2, 0], "invalid enum tag"), ([0, 1], "nonzero enum padding")]
    {
      let binder = hint_binder(Arc::new(move |[]: [Goldilocks; 0]| {
        Ok(words.map(|x| field.from_u64(x)))
      }));
      let call = binder(&[], &[0, 1], output_check(&layout, field)).unwrap();
      let mut registers = [field.one(); 2];
      assert!(call(&mut registers).unwrap_err().contains(message));
      assert_eq!(registers, [field.one(); 2]);
    }
  }
}
