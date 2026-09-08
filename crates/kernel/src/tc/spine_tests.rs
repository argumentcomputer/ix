use super::*;
use crate::mode::{Anon, Meta};
use ix_common::env::{BinderInfo, Name};

fn spine_identity<M: KernelMode>(arity: usize) {
  let head = KExpr::<M>::var(3, M::meta_field(Name::anon()));
  let mut root = head.clone();
  let mut expected = Vec::new();
  for i in 0..arity {
    // Named lambdas make preserving the original occurrences observable
    // in Meta mode too. No interning/canonicalization is part of a spine walk.
    let arg = KExpr::lam(
      M::meta_field(Name::str(Name::anon(), format!("arg{i}"))),
      M::meta_field(BinderInfo::Implicit),
      KExpr::sort(KUniv::zero()),
      KExpr::var(i as u64, M::meta_field(Name::anon())),
    );
    expected.push(arg.clone());
    root = KExpr::app(root, arg);
  }
  let (borrowed_head, borrowed) = borrow_app_spine(&root);
  assert!(borrowed_head.ptr_eq(&head));
  assert_eq!(borrowed.len(), arity);
  assert_eq!(borrowed.spilled(), arity > 8);
  for (a, b) in borrowed.iter().zip(&expected) {
    assert!(a.ptr_eq(b));
  }
  let (owned_head, owned) = collect_app_spine(&root);
  assert!(owned_head.ptr_eq(borrowed_head));
  for (a, b) in owned.iter().zip(&borrowed) {
    assert!(a.ptr_eq(b));
  }

  // Safe while caller-owned roots survive even if the interner is mutated
  // or discarded; the borrow does not reach into that table's storage.
  let mut env = KEnv::<M>::new();
  env.intern.intern_expr(root.clone());
  drop(env);
  assert!(borrowed[arity - 1].ptr_eq(&expected[arity - 1]));
}

#[test]
fn borrowed_spines_preserve_order_identity_and_inline_boundary() {
  for n in [1, 2, 7, 8, 9, 16, 33] {
    spine_identity::<Anon>(n);
    spine_identity::<Meta>(n);
  }
}

#[test]
fn borrowed_empty_spine_preserves_head_without_spilling() {
  fn check<M: KernelMode>() {
    let e = KExpr::<M>::sort(KUniv::zero());
    let (head, args) = borrow_app_spine(&e);
    assert!(std::ptr::eq(head, &e));
    assert!(args.is_empty());
    assert!(!args.spilled());
  }
  check::<Anon>();
  check::<Meta>();
}

#[test]
fn deep_borrowed_spines_are_iterative() {
  std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(|| {
      spine_identity::<Anon>(4096);
      spine_identity::<Meta>(4096);
    })
    .unwrap()
    .join()
    .unwrap();
}
