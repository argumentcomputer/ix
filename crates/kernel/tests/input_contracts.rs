//! Canonical byte-boundary regressions for C+ input-contract conversion.
//! These do not invoke the separate resource validator.

use ix_kernel::error::TcError;
use ix_kernel::ixon_checker::IxonChecker;
use ixon::constant::ConstantInfo;
use ixon::env::Env;
use ixon::expr::Expr;

struct Case {
  name: &'static str,
  envelope: &'static [u8],
  record: &'static [u8],
  address: &'static str,
  declared_input: u8,
  value_input: u8,
  result: u8,
}

macro_rules! case {
  ($name:literal, $address:literal, $declared:expr, $value:expr, $result:expr) => {
    Case {
      name: $name,
      envelope: include_bytes!(concat!(
        "fixtures/input_contracts/",
        $name,
        ".ixe"
      )),
      record: include_bytes!(concat!(
        "fixtures/input_contracts/",
        $name,
        ".const"
      )),
      address: $address,
      declared_input: $declared,
      value_input: $value,
      result: $result,
    }
  };
}

const MANY: Case = case!(
  "many-match",
  "9f57525dcb75ece681f20bbaf3ae34b3707bd2e380208ac9a2da5dfdff6f0d67",
  7,
  7,
  1
);
const LINEAR: Case = case!(
  "linear-match",
  "49953b97a0a191ee7429caae22e82888f711791e527abc5a7c6c9fc662a2efbd",
  5,
  5,
  1
);
const USES: Case = case!(
  "uses-mismatch",
  "cccdb41c603b9f57b65c8e5b41dced4e79b8d33b7467e566865c86b12a01a35a",
  5,
  7,
  1
);
const OWNERSHIP: Case = case!(
  "ownership-mismatch",
  "5a099a47c3c0757d8216e43cdfea8fbb60e94243114045f77dacb8a311d44fea",
  3,
  7,
  1
);
const LOCALITY: Case = case!(
  "locality-mismatch",
  "d1966bf100c57bc5d74bc4fab3837f0d8f52884f9259dedd3a865d5779e676c8",
  15,
  7,
  1
);
const RESULT: Case = case!(
  "result-only-unique",
  "1c6192680f32a84a63b999cc3a61b372bbe3cce6f640c80037539f430d36012c",
  5,
  5,
  0
);

fn check(case: &Case, accepts: bool) {
  assert_eq!(case.envelope.len(), 122);
  assert_eq!(case.record.len(), 15);
  let mut input = case.envelope;
  let decoded = Env::get(&mut input).expect("canonical envelope");
  assert!(input.is_empty());
  assert_eq!(decoded.consts.len(), 1);
  assert!(
    decoded.blobs.is_empty()
      && decoded.named.is_empty()
      && decoded.assumptions.is_empty()
  );
  let address = decoded.consts.iter().next().unwrap().key().clone();
  assert_eq!(address.hex(), case.address);
  let record = decoded.get_const(&address).expect("committed record");
  assert!(record.refs.is_empty() && record.sharing.is_empty());
  assert_eq!(record.commit(), (address.clone(), case.record.to_vec()));
  let ConstantInfo::Defn(definition) = &record.info else {
    panic!("definition fixture")
  };
  let Expr::All(declared, result, domain, codomain) = definition.typ.as_ref()
  else {
    panic!("Pi type")
  };
  let Expr::Lam(value, lambda_domain, body) = definition.value.as_ref() else {
    panic!("identity lambda")
  };
  assert_eq!(declared.to_bits(), case.declared_input);
  assert_eq!(value.to_bits(), case.value_input);
  assert_eq!(result.to_bits(), case.result);
  assert_eq!(domain.as_ref(), &Expr::Sort(0));
  assert_eq!(codomain.as_ref(), &Expr::Sort(0));
  assert_eq!(lambda_domain, domain);
  assert_eq!(body.as_ref(), &Expr::Var(0));
  let mut roundtrip = Vec::new();
  decoded.put(&mut roundtrip).unwrap();
  assert_eq!(roundtrip, case.envelope);
  let result = IxonChecker::new(&decoded).check_const(&address);
  if accepts {
    assert!(result.is_ok(), "{}: {result:?}", case.name);
  } else {
    assert!(
      matches!(&result, Err(TcError::DeclTypeMismatch)),
      "{}: {result:?}",
      case.name
    );
  }
}

#[test]
fn matching_many_input_accepts() {
  check(&MANY, true);
}

#[test]
fn matching_linear_input_accepts() {
  check(&LINEAR, true);
}

#[test]
fn mismatched_input_usage_rejects() {
  check(&USES, false);
}

#[test]
fn mismatched_input_ownership_rejects() {
  check(&OWNERSHIP, false);
}

#[test]
fn mismatched_input_locality_rejects() {
  check(&LOCALITY, false);
}

#[test]
fn result_only_difference_accepts() {
  check(&RESULT, true);
}

#[test]
fn optional_metadata_is_transport_only_and_erasure_preserves_the_verdict() {
  use ix_common::address::Address;
  use ix_common::env::{BinderInfo, DataValue, Name};
  use ix_kernel::ingress::ixon_ingress;
  use ix_kernel::mode::{Anon, Meta};
  use ixon::contract::source::decode;
  use ixon::env::Named;
  use ixon::metadata::{
    ConstantMeta, ConstantMetaInfo, DataValue as WireValue, ExprMeta,
    ExprMetaData,
  };

  for (case, accepts) in [(&MANY, true), (&USES, false)] {
    // A display-only layer is accepted; even an agreeing semantic layer is
    // refused by Meta transport. Neither changes anonymous logical admission.
    for semantic in [None, Some(23), Some(21)] {
      let mut input = case.envelope;
      let env = Env::get(&mut input).unwrap();
      let address = env.consts.iter().next().unwrap().key().clone();
      let name = Name::str(Name::anon(), "ContractProbe".into());
      let name_addr = Address::from_blake3_hash(*name.get_hash());
      env.store_name(name_addr.clone(), name.clone());
      let data = semantic.map_or_else(
        || {
          vec![(
            Name::str(Name::anon(), "display".into()),
            DataValue::OfBool(true),
          )]
        },
        |code| decode(1, code).unwrap().metadata(),
      );
      let kvs = data
        .into_iter()
        .map(|(key, value)| {
          let addr = Address::from_blake3_hash(*key.get_hash());
          env.store_name(addr.clone(), key);
          let value = match value {
            DataValue::OfNat(n) => {
              WireValue::OfNat(env.store_blob(n.to_le_bytes()))
            },
            DataValue::OfBool(b) => WireValue::OfBool(b),
            _ => unreachable!(),
          };
          (addr, value)
        })
        .collect();
      let arena = ExprMeta {
        nodes: vec![
          ExprMetaData::Leaf,
          ExprMetaData::Binder {
            name: name_addr.clone(),
            info: BinderInfo::Default,
            children: [0, 0],
          },
          ExprMetaData::Mdata { mdata: vec![kvs], child: 1 },
        ],
      };
      env.register_name(
        name,
        Named::new(
          address.clone(),
          ConstantMeta::new(ConstantMetaInfo::Def {
            name: name_addr,
            lvls: vec![],
            all: vec![],
            ctx: vec![],
            arena,
            type_root: 2,
            value_root: 1,
          }),
        ),
      );
      let mut bytes = Vec::new();
      env.put(&mut bytes).unwrap();
      let mut input = bytes.as_slice();
      let full = Env::get(&mut input).unwrap();
      assert!(input.is_empty());
      assert_eq!(full.get_const(&address).unwrap().commit().1, case.record);
      let meta = ixon_ingress::<Meta>(&full);
      if semantic.is_some() {
        assert!(
          matches!(&meta, Err(error) if error.contains("semantic contracts cannot come from optional metadata")),
          "{:?}",
          meta.err()
        );
      } else {
        assert!(meta.is_ok(), "{:?}", meta.err());
      }
      assert!(ixon_ingress::<Anon>(&full).is_ok());
      assert_eq!(
        IxonChecker::new(&full).check_const(&address).is_ok(),
        accepts
      );
      // get_anon intentionally leaves the optional metadata section unread.
      let anon = Env::get_anon(&mut bytes.as_slice()).unwrap();
      assert!(anon.named.is_empty());
      assert_eq!(anon.get_const(&address).unwrap().commit().1, case.record);
      assert_eq!(
        IxonChecker::new(&anon).check_const(&address).is_ok(),
        accepts
      );
    }
  }
}
#[test]
fn raw_contracted_inductive_keeps_the_existing_recursor_synthesis_policy() {
  use ix_kernel::constant::KConst;
  use ix_kernel::env::KEnv;
  use ix_kernel::expr::ExprData;
  use ix_kernel::id::KId;
  use ix_kernel::mode::Anon;
  use ix_kernel::tc::TypeChecker;
  use ixon::constant::{
    Constant, Inductive, MutConst, Recursor, indc_proj_constant,
  };
  use ixon::contract::{BinderContract, ValueContract};
  use ixon::univ::Univ;

  // A raw empty family (A : Type) : Type with a linear input is not a
  // source-compiler fixture. Its recursor is written independently here.
  // Generated telescope binders keep the ordinary defaults, matching
  // IxC's replacePisPw/pisToLamsPw; no new recursor schema is introduced.
  for (rec_input, result, accepts) in
    [(7, 1, true), (5, 1, false), (7, 0, true)]
  {
    let env = Env::new();
    let family = Constant::with_tables(
      ConstantInfo::Muts(vec![MutConst::Indc(Inductive {
        is_unsafe: false,
        lvls: 0,
        params: 1,
        indices: 0,
        typ: Expr::all_contract(
          BinderContract::from_bits(5).unwrap(),
          ValueContract::shared(),
          Expr::sort(1),
          Expr::sort(1),
        ),
        ctors: vec![],
      })]),
      vec![],
      vec![],
      vec![Univ::zero(), Univ::succ(Univ::zero())],
    );
    let family_block = family.commit().0;
    env.store_const(family_block.clone(), family);
    let projection = indc_proj_constant(0, family_block.clone());
    let family_addr = projection.commit().0;
    env.store_const(family_addr.clone(), projection);
    let applied_family =
      |i| Expr::app(Expr::reference(0, vec![]), Expr::var(i));
    let motive = Expr::all(applied_family(0), Expr::sort(2));
    let typ = Expr::all_contract(
      BinderContract::from_bits(rec_input).unwrap(),
      ValueContract::from_bits(result).unwrap(),
      Expr::sort(1),
      Expr::all(
        motive,
        Expr::all(applied_family(1), Expr::app(Expr::var(1), Expr::var(0))),
      ),
    );
    let recursor = Constant::with_tables(
      ConstantInfo::Recr(Recursor {
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 0,
        typ,
        rules: vec![],
      }),
      vec![],
      vec![family_addr.clone()],
      vec![Univ::zero(), Univ::succ(Univ::zero()), Univ::var(0)],
    );
    let rec_addr = recursor.commit().0;
    env.store_const(rec_addr.clone(), recursor);
    let mut bytes = Vec::new();
    env.put(&mut bytes).unwrap();
    let mut input = bytes.as_slice();
    let decoded = Env::get(&mut input).unwrap();
    assert!(input.is_empty());
    let mut kernel = KEnv::<Anon>::new();
    let mut tc = TypeChecker::new_with_lazy_anon(&mut kernel, &decoded);
    let family_id = KId::new(family_addr.clone(), ());
    let KConst::Indc { ty, .. } = tc.get_const(&family_id).unwrap() else {
      panic!("raw family must remain an inductive")
    };
    assert!(
      matches!(ty.data(), ExprData::All(_, _, c, _, _, _, _) if c.to_bits() == 5)
    );
    tc.check_const(&family_id).unwrap();
    let generated =
      tc.env.recursor_cache.get(&KId::new(family_block, ())).unwrap();
    assert_eq!(generated.len(), 1);
    assert!(
      matches!(generated[0].ty.data(), ExprData::All(_, _, c, r, _, _, _)
      if *c == BinderContract::default() && *r == ValueContract::shared())
    );
    let mut checker = IxonChecker::new(&decoded);
    checker.check_const(&family_addr).unwrap();
    let verdict = checker.check_const(&rec_addr);
    if accepts {
      assert!(verdict.is_ok(), "{verdict:?}");
    } else {
      // Selection requires a complete type match before the later per-rule
      // checks, so a changed input leaves no matching generated recursor.
      let expected = format!(
        "check_recursor: no generated recursor for major {}",
        &family_addr.hex()[..8]
      );
      assert!(
        matches!(&verdict, Err(TcError::Other(message)) if message == &expected),
        "{verdict:?}"
      );
    }
  }
}
