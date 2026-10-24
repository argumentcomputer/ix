//! Test-only FFI to the Rust clique transport library
//! (`ix_compile::compile::pass3::clique`), which the compiler does not call
//! yet: the plan of a definition clique (`plan_clique`), the rows of a
//! transported plan (`row::rows_of`) and the bounds table, for the
//! `clique-rust-parity` suite (`Tests/Ix/Compile/Clique/RustParity.lean`) to
//! compare with Lean's `Ix.Compile.Pass.Clique.planClique`, `rowsOf` and
//! `bounds` on the same input.
//!
//! The outcome crosses as plain Lean data, the structures `RsDecl` and
//! `RsOutcome` of the suite (layouts below), so the suite compares every
//! field of Rust's [`CliqueOutcome`] with Lean's; the rows cross as
//! `Ix.ConstantInfo`s.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{Env, Name};
use ix_compile::compile::pass3::clique::basic::Decl;
use ix_compile::compile::pass3::clique::bounds::bounds;
use ix_compile::compile::pass3::clique::plan::{CliqueOutcome, OrderSource};
use ix_compile::compile::pass3::clique::plan_clique::plan_clique;
use ix_compile::compile::pass3::clique::row::rows_of;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanCtor, LeanExcept, LeanOwned, LeanProd, LeanRef,
  LeanString,
};
use rustc_hash::FxHashMap;

use crate::builder::LeanBuildCache;
use crate::lean::{LeanIxConstantInfo, LeanIxExpr, LeanIxName};

lean_ffi::lean_inductive! {
  /// The suite's `RsDecl`, a library declaration ([`Decl`]):
  /// `{ name : Ix.Name, levelParams : Array Ix.Name, type value : Ix.Expr,
  /// isThm : Bool }` (four object fields, then the `Bool` as a byte).
  LeanRsCliqueDecl [ { num_obj: 4, num_8: 1 } ];
}

/// The number of object fields of the suite's `RsOutcome` (no scalars).
const OUTCOME_FIELDS: usize = 15;

/// A [`Decl`] as the suite's `RsDecl`.
fn build_decl(
  cache: &mut LeanBuildCache,
  d: &Decl,
) -> LeanRsCliqueDecl<LeanOwned> {
  let obj = LeanRsCliqueDecl::alloc(0);
  obj.set_obj(0, LeanIxName::build(cache, &d.name));
  obj.set_obj(1, LeanIxName::build_array(cache, &d.level_params));
  obj.set_obj(2, LeanIxExpr::build(cache, &d.typ));
  obj.set_obj(3, LeanIxExpr::build(cache, &d.value));
  obj.set_num_8(0, u8::from(d.is_thm));
  obj
}

/// An array of Lean objects built from `xs`.
fn build_array<T>(
  xs: &[T],
  mut f: impl FnMut(&T) -> LeanOwned,
) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(xs.len());
  for (i, x) in xs.iter().enumerate() {
    arr.set(i, f(x));
  }
  arr
}

/// The fields of an outcome, in the order of the suite's `RsOutcome`; the
/// fields a variant does not have stay empty.
#[derive(Default)]
struct Fields {
  tag: u64,
  reason: String,
  encoding: &'static str,
  cause: &'static str,
  source: Option<OrderSource>,
}

/// Rust's outcome as the suite's `RsOutcome`:
///
/// ```text
/// structure RsOutcome where
///   tag : Nat              -- 0 notEncoded, 1 unchanged, 2 baseline, 3 transported
///   reason : String        -- notEncoded and baseline: the reason; else ""
///   encoding : String      -- unchanged, baseline, transported: Encoding.tag; else ""
///   cause : String         -- baseline: Cause.tag; else ""
///   all : Array Ix.Name    -- transported (as every field below but the source's)
///   sigma : Array Nat
///   classes : Array (Array Ix.Name)
///   sourceTag : String     -- unchanged, transported: OrderSource.tag; else ""
///   sourceDescribe : String  -- unchanged, transported: OrderSource.describe
///   members : Array RsDecl -- the member map, in pretty-name order
///   canon : Array (RsDecl × Ix.Name)
///   functionals : Array Ix.Name
///   causes : Array (Ix.Name × String × String)  -- constant, Cause.tag, reason
///   aliases : Array (Ix.Name × Ix.Name)
///   record : String        -- CliquePlan.record
/// ```
fn build_outcome(o: &CliqueOutcome) -> LeanOwned {
  let mut cache = LeanBuildCache::new();
  let ctor = LeanCtor::alloc(0, OUTCOME_FIELDS, 0);
  let (fields, plan) = match o {
    CliqueOutcome::NotEncoded(why) => {
      (Fields { tag: 0, reason: why.clone(), ..Fields::default() }, None)
    },
    CliqueOutcome::Unchanged(enc, src) => (
      Fields {
        tag: 1,
        encoding: enc.tag(),
        source: Some(src.clone()),
        ..Fields::default()
      },
      None,
    ),
    CliqueOutcome::Baseline(enc, cause, why) => (
      Fields {
        tag: 2,
        reason: why.clone(),
        encoding: enc.tag(),
        cause: cause.tag(),
        source: None,
      },
      None,
    ),
    CliqueOutcome::Transported(p) => (
      Fields {
        tag: 3,
        encoding: p.encoding.tag(),
        source: Some(p.source.clone()),
        ..Fields::default()
      },
      Some(p),
    ),
  };
  ctor.set(0, LeanOwned::from_nat_u64(fields.tag));
  ctor.set(1, LeanString::new(&fields.reason));
  ctor.set(2, LeanString::new(fields.encoding));
  ctor.set(3, LeanString::new(fields.cause));
  let (src_tag, src_describe) = match &fields.source {
    Some(s) => (s.tag(), s.describe()),
    None => ("", String::new()),
  };
  ctor.set(7, LeanString::new(src_tag));
  ctor.set(8, LeanString::new(&src_describe));
  match plan {
    None => {
      for i in [4, 5, 6, 9, 10, 11, 12, 13] {
        ctor.set(i, LeanArray::alloc(0));
      }
      ctor.set(14, LeanString::new(""));
    },
    Some(p) => {
      ctor.set(4, LeanIxName::build_array(&mut cache, &p.all));
      ctor
        .set(5, build_array(&p.sigma, |&s| LeanOwned::from_nat_u64(s as u64)));
      ctor.set(
        6,
        build_array(&p.classes, |c| {
          LeanIxName::build_array(&mut cache, c).into()
        }),
      );
      let mut members: Vec<&Decl> = p.members.values().collect();
      members.sort_by_cached_key(|d| d.name.pretty());
      ctor.set(9, build_array(&members, |d| build_decl(&mut cache, d).into()));
      ctor.set(
        10,
        build_array(&p.canon, |(d, src)| {
          let decl = build_decl(&mut cache, d);
          LeanProd::new(decl, LeanIxName::build(&mut cache, src)).into()
        }),
      );
      ctor.set(11, LeanIxName::build_array(&mut cache, &p.functionals));
      ctor.set(
        12,
        build_array(&p.causes, |(n, c, why)| {
          let rest =
            LeanProd::new(LeanString::new(c.tag()), LeanString::new(why));
          LeanProd::new(LeanIxName::build(&mut cache, n), rest).into()
        }),
      );
      ctor.set(
        13,
        build_array(&p.aliases, |(m, r)| {
          let m = LeanIxName::build(&mut cache, m);
          LeanProd::new(m, LeanIxName::build(&mut cache, r)).into()
        }),
      );
      ctor.set(14, LeanString::new(&p.record()));
    },
  }
  ctor.into()
}

/// FFI: Rust's plan of a clique.
///
/// Lean signature:
/// `@[extern "rs_clique_plan"]
///  opaque rsCliquePlan : @& Array Ix.ConstantInfo →
///    @& Array (Ix.Name × Address) → @& Array Ix.Name → @& Array Ix.Name →
///    Except String RsOutcome`
///
/// `consts` is the whole input (a name absent from it is absent to
/// `plan_clique`), `addrs` the address lookup (a name absent from it has no
/// address), then the clique (`all`, Lean's order) and its carried equation
/// lemmas. The error is a decoding failure (an address that is not 32
/// bytes); the plan itself is total.
#[unsafe(no_mangle)]
pub extern "C" fn rs_clique_plan(
  consts: LeanArray<LeanBorrowed<'_>>,
  addrs: LeanArray<LeanBorrowed<'_>>,
  all: LeanArray<LeanBorrowed<'_>>,
  carried: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  match decode_input("rs_clique_plan", &consts, &addrs) {
    Ok((env, table)) => {
      let addr = |n: &Name| table.get(n).cloned();
      let all = LeanIxName::decode_array(all);
      let carried = LeanIxName::decode_array(carried);
      let outcome = plan_clique(&env, &addr, &all, &carried);
      LeanExcept::ok(build_outcome(&outcome))
    },
    Err(e) => LeanExcept::error_string(&e),
  }
}

/// FFI: Rust's rows of a clique, the encoding copies and the equation rows
/// (`rows_of`) of Rust's plan (`plan_clique`), as `Ix.ConstantInfo`s.
///
/// Lean signature:
/// `@[extern "rs_clique_rows"]
///  opaque rsCliqueRows : @& Array Ix.ConstantInfo →
///    @& Array (Ix.Name × Address) → @& Array Ix.Name → @& Array Ix.Name →
///    Except String (Array Ix.ConstantInfo × Array Ix.ConstantInfo)`
///
/// The input is [`rs_clique_plan`]'s. The error is a decoding failure, a
/// plan that is not transported (`rs_clique_rows: the plan is not
/// transported: …`, with [`CliqueOutcome::tag`]), or the rows' refusal
/// (`rows_of`'s text, Lean's `rowsOf`'s); a transported plan of another
/// encoding has no copies and no rows.
#[unsafe(no_mangle)]
pub extern "C" fn rs_clique_rows(
  consts: LeanArray<LeanBorrowed<'_>>,
  addrs: LeanArray<LeanBorrowed<'_>>,
  all: LeanArray<LeanBorrowed<'_>>,
  carried: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let (env, table) = match decode_input("rs_clique_rows", &consts, &addrs) {
    Ok(input) => input,
    Err(e) => return LeanExcept::error_string(&e),
  };
  let addr = |n: &Name| table.get(n).cloned();
  let all = LeanIxName::decode_array(all);
  let carried = LeanIxName::decode_array(carried);
  let plan = match plan_clique(&env, &addr, &all, &carried) {
    CliqueOutcome::Transported(p) => p,
    o => {
      return LeanExcept::error_string(&format!(
        "rs_clique_rows: the plan is not transported: {}",
        o.tag()
      ));
    },
  };
  let lookup = |n: &Name| env.get(n).map(|e| e.cloned());
  match rows_of(&lookup, &plan) {
    Ok((copies, rows)) => {
      let mut cache = LeanBuildCache::new();
      let copies = build_array(&copies, |ci| {
        LeanIxConstantInfo::build(&mut cache, ci).into()
      });
      let rows = build_array(&rows, |ci| {
        LeanIxConstantInfo::build(&mut cache, ci).into()
      });
      LeanExcept::ok(LeanProd::new(copies, rows))
    },
    Err(e) => LeanExcept::error_string(&e),
  }
}

/// The input of the plan and rows FFIs: the constants as an environment
/// (a name absent from them is absent to the library) and the address
/// table; an error names `what` and an address that is not 32 bytes.
fn decode_input(
  what: &str,
  consts: &LeanArray<LeanBorrowed<'_>>,
  addrs: &LeanArray<LeanBorrowed<'_>>,
) -> Result<(Arc<Env>, FxHashMap<Name, Address>), String> {
  let mut env = Env::default();
  for c in consts.iter() {
    let info = LeanIxConstantInfo(c).decode();
    env.insert(info.get_name().clone(), info);
  }
  let mut table: FxHashMap<Name, Address> = FxHashMap::default();
  for pair in addrs.iter() {
    let pair = pair.as_ctor();
    let name = LeanIxName(pair.get(0)).decode();
    let bytes = pair.get(1).as_byte_array();
    match Address::from_slice(bytes.as_bytes()) {
      Ok(a) => {
        table.insert(name, a);
      },
      Err(_) => {
        return Err(format!(
          "{what}: the address of {} has {} bytes, not 32",
          name.pretty(),
          bytes.len()
        ));
      },
    }
  }
  Ok((Arc::new(env), table))
}

/// FFI: the clique transport's bounds by their Lean names, in the order of
/// Lean's `Ix.Compile.Pass.Clique.bounds`.
///
/// Lean signature:
/// `@[extern "rs_clique_bounds"]
///  opaque rsCliqueBounds : Unit → Array (String × Nat)`
#[unsafe(no_mangle)]
pub extern "C" fn rs_clique_bounds(_unit: LeanOwned) -> LeanArray<LeanOwned> {
  build_array(&bounds(), |&(name, value)| {
    LeanProd::new(LeanString::new(name), LeanOwned::from_nat_u64(value as u64))
      .into()
  })
}
