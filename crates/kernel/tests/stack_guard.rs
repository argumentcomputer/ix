//! Recursion that would outrun the native stack declines instead of
//! crashing the checker.

use ix_common::address::Address;
use ix_common::env::Name;
use ix_kernel::env::KEnv;
use ix_kernel::error::TcError;
use ix_kernel::expr::KExpr;
use ix_kernel::id::KId;
use ix_kernel::ingress::ingress_anon_addr_shallow;
use ix_kernel::level::KUniv;
use ix_kernel::mode::Anon;
use ix_kernel::tc::TypeChecker;
use ixon::env::Env;

type E = KExpr<Anon>;

const BASIS: &[u8] = include_bytes!("fixtures/role_admission/basis.ixe");

fn address_of(env: &Env, dotted: &str) -> Address {
  let name = dotted
    .split('.')
    .fold(Name::anon(), |prefix, part| Name::str(prefix, part.into()));
  env.lookup_name(&name).unwrap_or_else(|| panic!("{dotted} missing")).addr
}

fn cnst(address: &Address, levels: Vec<KUniv<Anon>>) -> E {
  KExpr::cnst(KId::new(address.clone(), ()), levels.into())
}
fn app(f: E, a: E) -> E {
  KExpr::app(f, a)
}
fn lam(ty: E, body: E) -> E {
  KExpr::lam((), (), ty, body)
}

/// `Nat.rec (motive := fun _ => Nat) Nat.zero step n` for each `n`, where
/// `step _ ih := Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ _ =>
/// Nat.zero) ih`: reducing it at `n` reduces the same term at `n - 1` as
/// the major premise of the outer recursor, `n` native levels deep.
fn nested_reduction(env: &Env, n: u64) -> E {
  let nat = address_of(env, "Nat");
  let zero = cnst(&address_of(env, "Nat.zero"), vec![]);
  let rec = address_of(env, "Nat.rec");
  let nat_t = || cnst(&nat, vec![]);
  let one = KUniv::succ(KUniv::zero());
  let recursor = |motive: E, base: E, step: E, major: E| {
    app(app(app(app(cnst(&rec, vec![one.clone()]), motive), base), step), major)
  };
  let motive = || lam(nat_t(), nat_t());
  let constant_step = lam(nat_t(), lam(nat_t(), zero.clone()));
  let step = lam(
    nat_t(),
    lam(
      nat_t(),
      recursor(motive(), zero.clone(), constant_step, KExpr::var(0, ())),
    ),
  );
  let literal = bignat::Nat::from(n);
  let literal_address = Address::hash(&literal.to_le_bytes());
  recursor(motive(), zero.clone(), step, KExpr::nat(literal, literal_address))
}

fn reduce_on_small_stack(n: u64) -> Result<E, String> {
  std::thread::Builder::new()
    .stack_size(16 * 1024 * 1024)
    .spawn(move || {
      let mut input = BASIS;
      let env = Env::get(&mut input).unwrap();
      let mut kenv = KEnv::<Anon>::new();
      for name in ["Nat", "Nat.rec"] {
        assert!(
          ingress_anon_addr_shallow(&mut kenv, &env, &address_of(&env, name))
            .unwrap()
        );
      }
      let term = nested_reduction(&env, n);
      let mut checker = TypeChecker::new(&mut kenv);
      checker.whnf(&term).map_err(|error| match error {
        TcError::StackExhausted => "stack".to_string(),
        other => format!("{other}"),
      })
    })
    .unwrap()
    .join()
    .unwrap()
}

#[test]
fn shallow_nested_reduction_completes() {
  let result = reduce_on_small_stack(100).unwrap();
  assert!(matches!(result.data(), ix_kernel::expr::ExprData::Const(..)));
}

#[test]
fn deep_nested_reduction_declines_instead_of_overflowing() {
  // A million levels need far more than 16 MB of stack; without the guard
  // this aborts the test process with a stack overflow.
  assert_eq!(reduce_on_small_stack(1_000_000).unwrap_err(), "stack");
}
