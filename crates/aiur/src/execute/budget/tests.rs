use super::*;
use crate::{G, querymap::QueryMap};
use multi_stark::p3_field::PrimeCharacteristicRing;

#[test]
fn child_and_batch_charges_release_on_drop_and_failure() {
  let batch = ExecutionBudget::new(100, "batch".into(), None);
  let a = ExecutionBudget::new(80, "a".into(), Some(batch.clone()));
  let b = ExecutionBudget::new(80, "b".into(), Some(batch.clone()));
  let first = a.charge(70).unwrap();
  assert!(!a.charge(11).err().unwrap().shared);
  assert!(b.charge(40).err().unwrap().shared);
  assert_eq!((a.used(), b.used(), batch.used()), (70, 0, 70));
  drop(first);
  let second = b.charge(80).unwrap();
  assert_eq!(batch.used(), 80);
  drop(second);
  assert_eq!((a.used(), b.used(), batch.used()), (0, 0, 0));
  assert!(
    batch.failure().is_none(),
    "one aborted child must not poison siblings"
  );
}

#[test]
fn map_refuses_growth_before_inserting_or_assigning_a_pointer() {
  let budget = ExecutionBudget::new(1, "tiny".into(), None);
  let mut map = QueryMap::with_budget(1, Some(budget.clone()));
  assert!(map.insert(&[G::ONE], &[G::ZERO], G::ONE).is_err());
  assert_eq!(map.len(), 0);
  assert!(map.get_index_of(&[G::ONE]).is_none());
  assert_eq!(budget.used(), 0);
}

#[test]
fn map_growth_covers_rehash_and_preserves_rows_multiplicities_and_order() {
  let budget = ExecutionBudget::new(1 << 30, "record".into(), None);
  let mut bounded = QueryMap::with_budget(1, Some(budget.clone()));
  let mut reference = QueryMap::new(1);
  for n in 0..10_000 {
    let key = [G::from_usize(n)];
    let out = [G::from_usize(n + 1)];
    bounded.finish(&key, &out, true).unwrap();
    reference.finish(&key, &out, true).unwrap();
    bounded.finish(&key, &out, true).unwrap();
    reference.finish(&key, &out, true).unwrap();
    assert_eq!(bounded.get_index_of(&key), Some(n));
    assert_eq!(bounded.output_at(n), reference.output_at(n));
    assert_eq!(bounded.mult_at(n), reference.mult_at(n));
    assert_eq!(budget.used(), bounded.accounted_bytes());
  }
  assert!(budget.peak() >= budget.used());
  drop(bounded);
  assert_eq!(budget.used(), 0);
}

#[test]
fn dropping_a_record_during_unwind_releases_batch_memory() {
  let batch = ExecutionBudget::new(1 << 30, "batch".into(), None);
  let held = batch.clone();
  let result = std::panic::catch_unwind(move || {
    let record = ExecutionBudget::new(1 << 30, "record".into(), Some(held));
    let mut map = QueryMap::with_budget(0, Some(record));
    map.insert(&[], &[], G::ONE).unwrap();
    panic!("test unwind");
  });
  assert!(result.is_err());
  assert_eq!(batch.used(), 0);
}

#[test]
fn overflowing_requests_are_rejected_without_wrapping_accounting() {
  let budget = ExecutionBudget::new(u64::MAX, "test".into(), None);
  let held = budget.charge(u64::MAX).unwrap();
  assert!(budget.charge(1).is_err());
  assert_eq!(budget.used(), u64::MAX);
  drop(held);
  assert_eq!(budget.used(), 0);
}

#[test]
fn simultaneous_workers_cannot_overreserve_the_shared_budget() {
  let shared = ExecutionBudget::new(100, "batch".into(), None);
  let barrier = std::sync::Barrier::new(16);
  std::thread::scope(|scope| {
    for i in 0..16 {
      let shared = shared.clone();
      let barrier = &barrier;
      scope.spawn(move || {
        let child =
          ExecutionBudget::new(100, i.to_string(), Some(shared.clone()));
        let held = child.charge(10).ok();
        barrier.wait();
        assert!(shared.used() <= 100);
        drop(held);
      });
    }
  });
  assert_eq!(shared.used(), 0);
  assert_eq!(shared.peak(), 100);
}

#[test]
fn interpreter_propagates_counter_widening_limits_from_call_store_load_and_return()
 {
  use crate::{
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
    execute::{ExecError, IOBuffer, QueryRecord},
  };
  let layout =
    FunctionLayout { input_size: 1, selectors: 1, auxiliaries: 0, lookups: 1 };
  for op in [
    Some(Op::Call(1, vec![0], 1, false)),
    Some(Op::Store(vec![0])),
    Some(Op::Load(1, 0)),
    None,
  ] {
    let memory = matches!(op, Some(Op::Store(_) | Op::Load(..)));
    let returning = op.is_none();
    let toplevel = Toplevel {
      functions: vec![
        Function {
          body: Block {
            ops: op.into_iter().collect(),
            ctrl: Ctrl::Return(0, vec![]),
          },
          layout,
          entry: true,
          constrained: true,
        },
        Function {
          body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) },
          layout,
          entry: false,
          constrained: true,
        },
      ],
      memory_sizes: vec![1],
      // Only the interpreter and record budgets are exercised here.
      circuits: vec![],
    };
    let output = if returning { &[][..] } else { &[G::ZERO][..] };
    let mut reference = QueryMap::with_encodings(1, None, true, true);
    reference.insert(&[G::ZERO], output, G::from_u32(u32::MAX)).unwrap();
    let budget = ExecutionBudget::new(
      reference.accounted_bytes() + (1 << 20),
      "counter hit".into(),
      None,
    );
    let mut limited =
      QueryMap::with_encodings(1, Some(budget.clone()), true, true);
    limited.insert(&[G::ZERO], output, G::from_u32(u32::MAX)).unwrap();
    let mut record = QueryRecord::new(&toplevel);
    if memory {
      record.memory_queries[&1] = limited;
    } else {
      record.function_queries[usize::from(!returning)] = limited;
    }
    let before = budget.used();
    let error = toplevel.functions[0]
      .execute(
        0,
        vec![G::ZERO],
        &toplevel,
        &mut record,
        &mut IOBuffer { data: Default::default(), map: Default::default() },
      )
      .unwrap_err();
    assert!(matches!(error, ExecError::ResourceLimit(_)));
    let map = if memory {
      &record.memory_queries[&1]
    } else {
      &record.function_queries[usize::from(!returning)]
    };
    assert_eq!(map.len(), 1);
    assert_eq!(map.mult_at(0), G::from_u32(u32::MAX));
    assert_eq!(budget.used(), before);
    drop(record);
    assert_eq!(budget.used(), 0);
  }
}
