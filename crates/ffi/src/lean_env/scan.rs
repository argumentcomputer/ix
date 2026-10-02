//! The compile's setup scan read straight from the Lean objects.
//!
//! [`ix_compile::graph::setup_scan`] fetches every constant through the
//! environment, which decodes the whole Lean expression into
//! `ix_common::Expr` (one blake3 hash and one allocation per node), runs
//! three walks over it and drops it. [`LeanScanner`] runs the same three
//! walks over the `Lean.Expr` objects themselves, decoding only names:
//!
//! - **References** (`out_refs`): every `Const` name and `Proj` type name
//!   reachable from the constant's expressions, plus the inductive's
//!   constructors, the constructor's inductive, and the recursor rules'
//!   constructors. A set union, so a node reached twice adds nothing.
//! - **Source contracts**: whether some `Mdata` key lies in the reserved
//!   `ix.source.binder` namespace. A disjunction over `Mdata` nodes.
//! - **Semantic contracts**
//!   ([`ix_compile::semantic_contract::inspect_constant`]): every `Mdata`
//!   node with a reserved `ix.contract` key must carry a well-formed
//!   frame on the binder it annotates; the result says whether there is
//!   one, and only definitions, theorems, opaques and axioms may have one.
//! - **Groundedness** ([`ix_compile::ground::ground_const_check`]): no
//!   free or meta variable, no universe metavariable, every universe
//!   parameter declared, every `Const`/`Proj` name present, every
//!   constructor of an inductive present as a constructor, and no bound
//!   variable escaping its binders.
//!
//! Each walk visits subterms through a set keyed by **address**, where
//! the decoded walks key on the structural hash. Every property above is
//! a union or conjunction over the subterms reached, and a node's
//! contribution depends only on its own structure, so expanding two
//! equal subterms at different addresses twice changes the work, not
//! the result. The one depth-dependent check, bound variables, uses
//! Lean's cached `looseBVarRange` of each root instead of a walk keyed
//! on (depth, subterm): a root has no escaping bound variable exactly
//! when its range is 0. Lean computes the range exactly as the maximum
//! over its bound variables of (index − binder depth + 1), and
//! `lean_expr_mk_data` aborts the process (`lean_internal_panic`) on a
//! range of 2^20 or more instead of storing a truncated one.
//!
//! **Errors take the decoding path.** The decoded walks stop at the first
//! problem and report it, so which error a constant reports depends on
//! their traversal order. Whenever this scan meets anything that makes
//! one of the checks fail, or any shape it does not expect, it gives up
//! on the constant and returns [`scan_constant`] of the decoded constant
//! instead, so every error is the reference error, by construction. On
//! well-formed input the fallback never runs.

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use lean_ffi::include::{self, lean_object};
use lean_ffi::object::{LeanBorrowed, LeanRef};
use rustc_hash::FxHashSet;

use ix_common::env::{DataValue, Env, Name};
use ix_compile::graph::{
  ConstScan, ConstScanner, NameSet, is_source_contract_key, scan_constant,
};
use ix_compile::semantic_contract::{self, Kind};

use super::{Cache, GlobalCache, LeanConstants, decode_name};

type Obj = *mut lean_object;

// Raw reads of constructor objects. The walks below read a few billion
// nodes on Mathlib, and lean.h's inline accessors are out-of-line calls
// from Rust; the layout is lean.h's `lean_object` header
// (`m_rc: i32, m_cs_sz: 16, m_other: 8, m_tag: 8`) followed by the
// object fields, checked against lean.h once per constant in `scan`.

fn is_scalar(o: Obj) -> bool {
  o as usize & 1 == 1
}

/// `lean_ptr_tag`. `o` must be a live non-scalar object.
#[inline]
unsafe fn tag(o: Obj) -> u8 {
  unsafe { *o.cast::<u8>().add(7) }
}

/// `lean_ctor_get(o, i)`. `o` must be a live constructor object with
/// more than `i` object fields.
#[inline]
unsafe fn field(o: Obj, i: usize) -> Obj {
  unsafe { *o.cast::<Obj>().add(1 + i) }
}

fn borrowed<'a>(o: Obj) -> LeanBorrowed<'a> {
  unsafe { LeanBorrowed::from_raw(o) }
}

/// Elements of a `List`, by raw pointer.
fn list(mut cell: Obj) -> impl Iterator<Item = Obj> {
  std::iter::from_fn(move || {
    if is_scalar(cell) {
      return None;
    }
    // SAFETY: a non-scalar `List` cell is `cons head tail`.
    let (head, tail) = unsafe { (field(cell, 0), field(cell, 1)) };
    cell = tail;
    Some(head)
  })
}

// `Lean.ConstantInfo` and `Lean.Expr` constructor tags.
const AXIOM: u8 = 0;
const DEFN: u8 = 1;
const THM: u8 = 2;
const OPAQUE: u8 = 3;
const INDUCT: u8 = 5;
const CTOR: u8 = 6;
const REC: u8 = 7;

// Tags 1 and 2 are `fvar` and `mvar`, which are ungrounded.
const BVAR: u8 = 0;
const SORT: u8 = 3;
const CONST: u8 = 4;
const APP: u8 = 5;
const LAM: u8 = 6;
const FORALL: u8 = 7;
const LET: u8 = 8;
const LIT: u8 = 9;
const MDATA: u8 = 10;
const PROJ: u8 = 11;

/// The fast scan gave up on a constant; the decoding path computes its
/// scan.
#[derive(Debug)]
pub struct Fallback;

/// Per-thread scratch space, reused across constants.
#[derive(Default)]
struct Scratch {
  /// Interior expression nodes already expanded, by address.
  visited: FxHashSet<usize>,
  /// Universe level nodes already checked, by address.
  levels: FxHashSet<usize>,
  /// `Const` and `Proj` name objects met, by address.
  names: FxHashSet<usize>,
  stack: Vec<Obj>,
  level_stack: Vec<Obj>,
}

impl Scratch {
  /// Empty the sets for the next constant. Clearing costs the table's
  /// capacity, so a table grown by a large constant is dropped instead.
  fn reset(&mut self) {
    const KEEP: usize = 1 << 12;
    for set in [&mut self.visited, &mut self.levels, &mut self.names] {
      if set.capacity() > KEEP {
        *set = FxHashSet::default();
      } else {
        set.clear();
      }
    }
    self.stack.clear();
    self.level_stack.clear();
  }
}

thread_local! {
  static SCRATCH: RefCell<Scratch> = RefCell::new(Scratch::default());
}

/// One constant's walk state.
struct Walker<'a> {
  global: &'a GlobalCache,
  s: &'a mut Scratch,
  /// The constant's `levelParams` list, decoded on first use.
  univ_list: Obj,
  univs: Option<Vec<Name>>,
  source_contract: bool,
  semantic: bool,
}

impl Walker<'_> {
  fn univ_declared(&mut self, name: &Name) -> bool {
    let (global, univ_list) = (self.global, self.univ_list);
    self
      .univs
      .get_or_insert_with(|| {
        list(univ_list).map(|n| decode_name(borrowed(n), global)).collect()
      })
      .contains(name)
  }

  /// `ground_level`: every parameter declared, no metavariable.
  ///
  /// SAFETY: `level` is a live `Lean.Level`.
  unsafe fn check_level(&mut self, level: Obj) -> Result<(), Fallback> {
    self.s.level_stack.push(level);
    while let Some(l) = self.s.level_stack.pop() {
      // A scalar level is `zero`, as in `decode_level`.
      if is_scalar(l) || !self.s.levels.insert(l as usize) {
        continue;
      }
      unsafe {
        match tag(l) {
          // succ
          1 => self.s.level_stack.push(field(l, 0)),
          // max, imax
          2 | 3 => {
            self.s.level_stack.push(field(l, 0));
            self.s.level_stack.push(field(l, 1));
          },
          // param
          4 => {
            let name = decode_name(borrowed(field(l, 0)), self.global);
            if !self.univ_declared(&name) {
              return Err(Fallback);
            }
          },
          // mvar, or a shape the decoder rejects
          _ => return Err(Fallback),
        }
      }
    }
    Ok(())
  }

  /// One `Mdata` node: its keys feed the source-contract flag and, when
  /// one is a reserved `ix.contract` key, the semantic frame check.
  ///
  /// SAFETY: `e` is a live `Lean.Expr.mdata`.
  unsafe fn mdata(&mut self, e: Obj) -> Result<(), Fallback> {
    let kv = unsafe { field(e, 0) };
    let mut reserved = false;
    for pair in list(kv) {
      let key = decode_name(borrowed(unsafe { field(pair, 0) }), self.global);
      self.source_contract |= is_source_contract_key(&key);
      reserved |= semantic_contract::reserved(&key);
    }
    if reserved {
      let mut cache = Cache::new(self.global);
      let data: Vec<(Name, DataValue)> = list(kv)
        .map(|pair| super::decode_name_data_value(borrowed(pair), &mut cache))
        .collect();
      let contract =
        semantic_contract::read(&data).map_err(|_error| Fallback)?;
      let binder = match contract.kind {
        Kind::Lam => LAM,
        Kind::All => FORALL,
        Kind::Let => LET,
      };
      if unsafe { tag(field(e, 1)) } != binder {
        return Err(Fallback);
      }
      self.semantic = true;
    }
    Ok(())
  }

  /// Walk one root expression (a type, value or recursor rule).
  ///
  /// SAFETY: `root` is a live `Lean.Expr`.
  unsafe fn walk(&mut self, root: Obj) -> Result<(), Fallback> {
    // Bound variables: the root's cached `looseBVarRange` (bits 44..64
    // of `Expr.Data`) is 0 exactly when none escapes.
    if unsafe { include::lean_expr_data(root) } >> 44 != 0 {
      return Err(Fallback);
    }
    self.s.stack.push(root);
    while let Some(e) = self.s.stack.pop() {
      unsafe {
        match tag(e) {
          BVAR | LIT => {},
          SORT => self.check_level(field(e, 0))?,
          CONST => {
            self.s.names.insert(field(e, 0) as usize);
            for level in list(field(e, 1)) {
              self.check_level(level)?;
            }
          },
          APP | LAM | FORALL | LET | MDATA | PROJ
            if !self.s.visited.insert(e as usize) => {},
          APP => {
            self.s.stack.push(field(e, 0));
            self.s.stack.push(field(e, 1));
          },
          LAM | FORALL => {
            self.s.stack.push(field(e, 1));
            self.s.stack.push(field(e, 2));
          },
          LET => {
            self.s.stack.push(field(e, 1));
            self.s.stack.push(field(e, 2));
            self.s.stack.push(field(e, 3));
          },
          MDATA => {
            self.mdata(e)?;
            self.s.stack.push(field(e, 1));
          },
          PROJ => {
            self.s.names.insert(field(e, 0) as usize);
            self.s.stack.push(field(e, 2));
          },
          // `fvar` and `mvar` (ungrounded), or a shape the decoder rejects.
          _ => return Err(Fallback),
        }
      }
    }
    Ok(())
  }
}

/// [`ConstScanner`] over the Lean objects of a compile's environment.
pub struct LeanScanner {
  constants: Arc<LeanConstants>,
  /// Constants handed to the decoding path.
  fallbacks: AtomicUsize,
}

impl LeanScanner {
  pub(super) fn new(constants: Arc<LeanConstants>) -> Self {
    Self { constants, fallbacks: AtomicUsize::new(0) }
  }

  /// How many constants took the decoding path so far.
  pub fn fallbacks(&self) -> usize {
    self.fallbacks.load(Ordering::Relaxed)
  }

  /// How many constants the environment has decoded so far, by any
  /// reader (repeats included).
  pub fn decodes(&self) -> usize {
    self.constants.decodes()
  }

  /// The fast scan alone: `Some(Err(Fallback))` where
  /// [`ConstScanner::scan`] takes the decoding path.
  pub fn scan_fast(
    &self,
    name: &Name,
    env: &Env,
  ) -> Option<Result<ConstScan, Fallback>> {
    let info = self.constants.info(name)?.as_raw();
    // The raw header reads agree with lean.h's accessors.
    assert_eq!(
      unsafe { tag(info) },
      unsafe { include::lean_ptr_tag(info) },
      "lean_object header layout"
    );
    Some(SCRATCH.with_borrow_mut(|s| {
      s.reset();
      // SAFETY: `info` is a live `Lean.ConstantInfo`, kept alive by
      // `self.constants`.
      unsafe { self.scan_info(info, env, s) }
    }))
  }

  /// SAFETY: `info` is a live `Lean.ConstantInfo`.
  unsafe fn scan_info(
    &self,
    info: Obj,
    env: &Env,
    s: &mut Scratch,
  ) -> Result<ConstScan, Fallback> {
    let global = &self.constants.global;
    let kind = unsafe { tag(info) };
    if kind > REC {
      return Err(Fallback);
    }
    unsafe {
      let val = field(info, 0);
      // ConstantVal: name, levelParams, type.
      let cval = field(val, 0);
      let mut walker = Walker {
        global,
        s,
        univ_list: field(cval, 1),
        univs: None,
        source_contract: false,
        semantic: false,
      };
      // The roots every reference walk shares: the type, the value of a
      // definition, theorem or opaque, and the recursor rules'
      // right-hand sides.
      walker.walk(field(cval, 2))?;
      match kind {
        DEFN | THM | OPAQUE => walker.walk(field(val, 1))?,
        REC => {
          for rule in list(field(val, 6)) {
            walker.walk(field(rule, 2))?;
          }
        },
        _ => {},
      }
      let Walker { source_contract, semantic, s, .. } = walker;
      // Only definitions, theorems, opaques and axioms may carry
      // semantic frames.
      if semantic && !matches!(kind, AXIOM | DEFN | THM | OPAQUE) {
        return Err(Fallback);
      }
      let mut deps = NameSet::default();
      deps.reserve(s.names.len());
      for &name in &s.names {
        let name = decode_name(borrowed(name as Obj), global);
        if !env.contains_key(&name) {
          return Err(Fallback);
        }
        deps.insert(name);
      }
      let mut ind_group = None;
      match kind {
        INDUCT => {
          // InductiveVal: cnst, numParams, numIndices, all, ctors, …
          for ctor in list(field(val, 4)) {
            let ctor = decode_name(borrowed(ctor), global);
            match self.constants.info(&ctor) {
              Some(info) if tag(info.as_raw()) == CTOR => {},
              _ => return Err(Fallback),
            }
            deps.insert(ctor);
          }
          let all: Vec<Name> = list(field(val, 3))
            .map(|n| decode_name(borrowed(n), global))
            .collect();
          ind_group = all.first().cloned().map(|first| (first, all));
        },
        // ConstructorVal: cnst, induct, …
        CTOR => {
          deps.insert(decode_name(borrowed(field(val, 1)), global));
        },
        // RecursorRule: ctor, nfields, rhs.
        REC => {
          for rule in list(field(val, 6)) {
            deps.insert(decode_name(borrowed(field(rule, 0)), global));
          }
        },
        _ => {},
      }
      Ok(ConstScan {
        deps,
        source_contract,
        semantic: Ok(semantic),
        ground: Ok(()),
        ind_group,
      })
    }
  }
}

impl ConstScanner for LeanScanner {
  fn scan(&self, name: &Name, env: &Env) -> Option<ConstScan> {
    match self.scan_fast(name, env)? {
      Ok(scan) => Some(scan),
      Err(Fallback) => {
        self.fallbacks.fetch_add(1, Ordering::Relaxed);
        let constant = env.get(name)?;
        Some(scan_constant(&constant, env))
      },
    }
  }
}

/// Compare the scan over the Lean objects with the decoding scan on a
/// Lean environment: every constant's [`ConstScan`], then every
/// [`ix_compile::graph::SetupScan`] field.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_setup_scan_compare"]
/// opaque rsSetupScanCompare : @& List (Lean.Name × Lean.ConstantInfo) → IO String
/// ```
/// Returns a summary, or fails with the first difference.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_setup_scan_compare(
  list: lean_ffi::object::LeanList<LeanBorrowed<'_>>,
) -> lean_ffi::object::LeanIOResult<lean_ffi::object::LeanOwned> {
  use ix_compile::graph::{
    compare_const_scans, compare_setup_scans, setup_scan, setup_scan_with,
  };
  use lean_ffi::object::{LeanIOResult, LeanString};
  use rayon::prelude::*;

  let (names, constants) = LeanConstants::index(list);
  let env = constants.clone().into_lazy_env(names, 1 << 14);
  let scanner = LeanScanner::new(constants);
  let keys: Vec<&Name> = env.keys().collect();
  // Per constant: (fast scan accepted, reference had an error), or the
  // first difference.
  let per_constant: Result<Vec<(bool, bool)>, String> = keys
    .par_iter()
    .map(|name| {
      let reference = env.get(name).map(|c| scan_constant(&c, &env));
      let fast = scanner.scan_fast(name, &env);
      match (fast, reference) {
        (None, None) => Ok((true, false)),
        (Some(fast), Some(reference)) => {
          let errored =
            reference.semantic.is_err() || reference.ground.is_err();
          if let Ok(fast) = &fast {
            compare_const_scans(fast, &reference)
              .map_err(|diff| format!("{}: {diff}", name.pretty()))?;
          }
          if fast.is_err() && !errored {
            return Err(format!(
              "{}: the fast scan gave up on a constant without errors",
              name.pretty()
            ));
          }
          Ok((fast.is_ok(), errored))
        },
        (fast, reference) => Err(format!(
          "{}: present to the fast scan: {}, to the reference: {}",
          name.pretty(),
          fast.is_some(),
          reference.is_some()
        )),
      }
    })
    .collect();
  let per_constant = match per_constant {
    Ok(results) => results,
    Err(diff) => return LeanIOResult::error_string(&diff),
  };
  let fast = setup_scan_with(&env, &scanner);
  let reference = setup_scan(&env);
  if let Err(diff) = compare_setup_scans(&fast, &reference) {
    return LeanIOResult::error_string(&diff);
  }
  let accepted = per_constant.iter().filter(|(ok, _)| *ok).count();
  let errored = per_constant.iter().filter(|(_, err)| *err).count();
  let summary = format!(
    "{} constants: {accepted} scanned without decoding, {errored} with errors \
     (decoded; {} decoding fallbacks in the assembled scan); {} out_refs, {} \
     in_refs, {} ungrounded, {} inductive groups, {} source contracts, \
     semantic sources {:?}",
    keys.len(),
    scanner.fallbacks(),
    fast.graph.out_refs.len(),
    fast.graph.in_refs.len(),
    fast.immediate_ungrounded.len(),
    fast.ind_groups.len(),
    fast.source_contracts.len(),
    fast.semantic_sources.as_ref().map(Vec::len).map_err(|e| format!("{e:?}")),
  );
  LeanIOResult::ok(LeanString::new(&summary))
}
