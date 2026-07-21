/-
  Ix.AuxGen.ExprUtils: shared expression manipulation utilities for
  auxiliary generation.

  Pure-manipulation half of Rust
  `crates/compile/src/compile/aux_gen/expr_utils.rs`: FVar-based expression
  construction (create fresh free variables, open forall telescopes, build
  expressions using FVar references, abstract back into de Bruijn binder
  chains with `mkForall`/`mkLambda`), plus substitution, shifting, and
  universe manipulation helpers used across the recursor/below/brecOn
  generators.

  The kernel-backed half of expr_utils.rs (TcScope, kenv ingress,
  `decompose_inductive_type`, `kexpr_to_lean`, `to_kexpr_static`, the
  WHNF source-name restore machinery) is intentionally NOT here — it is a
  separate milestone that bridges to `Ix.Tc`.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Level.mkMax`, ...)
  so the embedded blake3 hashes stay bit-identical with the Rust compiler.
-/
module

public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Ix.AuxGen

/-- Local error channel for `Ix.AuxGen`. Mirrors the slice of Rust
    `ixon::CompileError` these utilities can actually produce.
    `Ix.AuxGen` must not import `Ix.CompileM` (dependency direction:
    CompileM will import AuxGen), so the shape is re-declared here. -/
inductive AuxGenError where
  /-- Mirrors Rust `CompileError::UnsupportedExpr { desc }`. -/
  | unsupportedExpr (desc : String)
  deriving Repr, Inhabited

instance : ToString AuxGenError where
  toString
    | .unsupportedExpr desc => s!"unsupported expression: {desc}"

/-- Memoization cache for expression rewriters. Rust uses
    `FxHashMap<blake3::Hash, LeanExpr>` keyed on the node's content hash;
    `Ix.Expr`'s `BEq`/`Hashable` instances are hash-based
    (Environment.lean:295-300), so keying on the `Expr` itself is the
    faithful mirror. -/
abbrev ExprCache := Std.HashMap Expr Expr

/-! ## FVar infrastructure -/

/-- Mirrors Rust `LocalDecl` (aux_gen/expr_utils.rs:31).

    A local declaration: FVar name, binder metadata, and domain type.
    Used to accumulate binder information while building expressions in
    FVar space. The `fvarName` is a unique identifier; `binderName` is
    the cosmetic name that appears in the final forall/lambda chain. -/
structure LocalDecl where
  fvarName : Name
  binderName : Name
  domain : Expr
  info : Lean.BinderInfo
  deriving Repr, Nonempty, Inhabited

/-- Mirrors Rust `fresh_fvar` (aux_gen/expr_utils.rs:39).

    Create a fresh FVar with a unique name derived from `pfx` and `idx`.
    The naming scheme — a single `Name.str` component `"_{pfx}_{idx}"` on
    the anonymous name — is load-bearing for hash equality with the Rust
    compiler (`Name::str(Name::anon(), format!("_{}_{}", prefix, idx))`). -/
def freshFVar (pfx : String) (idx : Nat) : Name × Expr :=
  let name := Name.mkStr .mkAnon s!"_{pfx}_{idx}"
  let fvar := Expr.mkFVar name
  (name, fvar)

/-! ## Inductive recursor-structural decomposition

Rust `decompose_inductive_type` (aux_gen/expr_utils.rs:121) is
kernel-backed (it interleaves `TcScope::whnf_lean` between peeling steps)
and is NOT ported here — kernel-bridge milestone. Only its pure result
shape is declared so downstream data plumbing can be ported ahead of it. -/

/-- Mirrors Rust `IndRecInfo` (aux_gen/expr_utils.rs:63).

    Per-inductive recursor-structural info, derived from the stored type by
    WHNF-peeling params and indices. Binders use FVars (via `LocalDecl`) so
    the result can be embedded in any outer binder chain without de-Bruijn
    shifting. Produced by the (not yet ported) `decompose_inductive_type`. -/
structure IndRecInfo where
  /-- Index binders after WHNF-peeling. -/
  indices : Array LocalDecl
  /-- Major premise `(t : I params indices)`. -/
  major : LocalDecl
  deriving Repr, Nonempty, Inhabited

/-! ## Expression utilities (aux_gen/expr_utils.rs:1473) -/

/-- Mirrors Rust `mk_const` (aux_gen/expr_utils.rs:1478).
    Create a `Const` expression with the given name and universe levels. -/
def mkConst (name : Name) (univs : Array Level) : Expr :=
  Expr.mkConst name univs

/-- Mirrors Rust `decompose_apps` (aux_gen/expr_utils.rs:1509).
    Decompose an application spine: `f a1 a2 ... an` → `(f, #[a1, ..., an])`. -/
def decomposeApps (expr : Expr) : Expr × Array Expr := Id.run do
  let mut args : Array Expr := #[]
  let mut cur := expr
  repeat
    match cur with
    | .app f a _ =>
      args := args.push a
      cur := f
    | _ => break
  return (cur, args.reverse)

/-- Mirrors Rust `count_foralls` (aux_gen/expr_utils.rs:1521).
    Count the number of leading forall binders in an expression. -/
def countForalls (expr : Expr) : Nat := Id.run do
  let mut n := 0
  let mut cur := expr
  repeat
    match cur with
    | .forallE _ _ body _ _ =>
      n := n + 1
      cur := body
    | _ => break
  return n

/-- Mirrors Rust `mk_app_n` (aux_gen/expr_utils.rs:1536).
    Apply an expression to a sequence of arguments: `f a1 a2 ... an`. -/
def mkAppN (f : Expr) (args : Array Expr) : Expr :=
  args.foldl Expr.mkApp f

/-! ## BVar shifting (aux_gen/expr_utils.rs:801) -/

/-- Mirrors Rust `shift_vars` (aux_gen/expr_utils.rs:809).

    Shift BVars UP by `amount` for BVars >= `cutoff`. Used internally by
    `instantiateRevAt` when substituting args under inner binders (each
    args element is re-shifted by the current depth). -/
partial def shiftVars (expr : Expr) (amount : Nat) (cutoff : Nat) : Expr :=
  if amount == 0 then expr
  else match expr with
  | .bvar i _ =>
    if i >= cutoff then Expr.mkBVar (i + amount) else expr
  | .app f a _ =>
    Expr.mkApp (shiftVars f amount cutoff) (shiftVars a amount cutoff)
  | .lam n t b bi _ =>
    Expr.mkLam n (shiftVars t amount cutoff) (shiftVars b amount (cutoff + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (shiftVars t amount cutoff) (shiftVars b amount (cutoff + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (shiftVars t amount cutoff) (shiftVars v amount cutoff)
      (shiftVars b amount (cutoff + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (shiftVars e amount cutoff)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (shiftVars e amount cutoff)
  | _ => expr

/-! ## Instantiation: BVar -> replacement (aux_gen/expr_utils.rs:591) -/

/-- Mirrors Rust `instantiate1_at` (aux_gen/expr_utils.rs:605). -/
partial def instantiate1At (body : Expr) (replacement : Expr) (depth : Nat) : Expr :=
  match body with
  | .bvar i _ =>
    if i == depth then replacement
    else if i > depth then Expr.mkBVar (i - 1)
    else body
  | .app f a _ =>
    Expr.mkApp (instantiate1At f replacement depth) (instantiate1At a replacement depth)
  | .lam n t b bi _ =>
    Expr.mkLam n (instantiate1At t replacement depth)
      (instantiate1At b replacement (depth + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (instantiate1At t replacement depth)
      (instantiate1At b replacement (depth + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (instantiate1At t replacement depth)
      (instantiate1At v replacement depth)
      (instantiate1At b replacement (depth + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (instantiate1At e replacement depth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (instantiate1At e replacement depth)
  | _ => body

/-- Mirrors Rust `instantiate1` (aux_gen/expr_utils.rs:601).

    Lean's `instantiate1`: replace BVar(0) with `replacement`, decrement
    BVar(i>0) by 1 (removing a binder level). The replacement is NOT
    shifted — it's inserted as-is at the substitution depth. -/
def instantiate1 (body : Expr) (replacement : Expr) : Expr :=
  instantiate1At body replacement 0

/-- Mirrors Rust `instantiate_rev_at` (aux_gen/expr_utils.rs:674). -/
partial def instantiateRevAt (body : Expr) (args : Array Expr) (depth : Nat) : Expr :=
  let n := args.size
  match body with
  | .bvar i _ =>
    if i >= depth then
      let ridx := i - depth
      if ridx < n then
        -- Replace with args[ridx], shifted up by depth for the binders we're under.
        shiftVars args[ridx]! depth 0
      else
        -- Free BVar past our substitution range: decrement by n.
        Expr.mkBVar (i - n)
    else
      -- Bound by an expression-internal binder — unchanged.
      body
  | .app f a _ =>
    Expr.mkApp (instantiateRevAt f args depth) (instantiateRevAt a args depth)
  | .lam name t b bi _ =>
    Expr.mkLam name (instantiateRevAt t args depth)
      (instantiateRevAt b args (depth + 1)) bi
  | .forallE name t b bi _ =>
    Expr.mkForallE name (instantiateRevAt t args depth)
      (instantiateRevAt b args (depth + 1)) bi
  | .letE name t v b nd _ =>
    Expr.mkLetE name (instantiateRevAt t args depth)
      (instantiateRevAt v args depth)
      (instantiateRevAt b args (depth + 1)) nd
  | .proj name i e _ =>
    Expr.mkProj name i (instantiateRevAt e args depth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (instantiateRevAt e args depth)
  | _ => body

/-- Mirrors Rust `instantiate_rev` (aux_gen/expr_utils.rs:667).

    Multi-argument reverse instantiation: replace BVar(0)..BVar(n-1) with
    `args[0]..args[n-1]` simultaneously, and decrement BVar(i >= n) by n.
    Unlike `instantiate1`, the substituted argument's loose BVars are
    LIFTED by the binder depth at each site. -/
def instantiateRev (body : Expr) (args : Array Expr) : Expr :=
  if args.isEmpty then body
  else instantiateRevAt body args 0

/-- Mirrors Rust `instantiate_pi_params` (aux_gen/expr_utils.rs:741).

    Peel `n` forall binders and substitute their variables with `args`.
    Matches Lean C++ `instantiate_pi_params` (`inductive.cpp:954-960`).
    (Rust guards with `debug_assert!(args.len() >= n)` — a release no-op —
    not replicated here.) -/
def instantiatePiParams (typ : Expr) (n : Nat) (args : Array Expr) : Expr := Id.run do
  let mut cur := typ
  for i in [0:Nat.min n args.size] do
    let arg := args[i]!
    match cur with
    | .forallE _ _ body _ _ =>
      cur := instantiate1 body arg
    | _ => break
  return cur

/-- Mirrors Rust `instantiate_spec_with_fvars` (aux_gen/expr_utils.rs:791).

    Convert spec_params from BVar form to FVar form: `BVar(i) →
    param_fvars[n_params - 1 - i]` for i < n_params, `BVar(i) →
    BVar(i - n_params)` otherwise. Implemented as a single
    `instantiateRev` call with a reversed param vector; relies on
    `paramFVars` being closed (FVars are by construction closed). -/
def instantiateSpecWithFVars (specParams : Array Expr) (paramFVars : Array Expr) :
    Array Expr :=
  -- Reverse once; `instantiateRev` expects `args[i]` to replace `BVar(i)`,
  -- but our convention is `BVar(0) = innermost = paramFVars[n-1]`.
  let reversed := paramFVars.reverse
  specParams.map (fun sp => instantiateRev sp reversed)

/-! ## Universe substitution (aux_gen/expr_utils.rs:859)

The `Level` smart-simplifying constructors below mirror the Rust
`ix_common::env::Level` methods (`crates/common/src/env.rs`), which
`subst_level` depends on. They are ported here because `Ix.Environment`
only carries the raw hash-building constructors. -/

/-- Mirrors Rust `Level::peel_succ` (common/src/env.rs:424).
    Peel a chain of `Succ` constructors: returns `(base, n)` where
    `level == Succ^n(base)` and `base` is not a `Succ`. -/
def levelPeelSucc (l : Level) : Level × Nat := Id.run do
  let mut cur := l
  let mut n : Nat := 0
  repeat
    match cur with
    | .succ inner _ =>
      n := n + 1
      cur := inner
    | _ => break
  return (cur, n)

/-- Mirrors Rust `Level::explicit_offset` (common/src/env.rs:434).
    `some (base, n)` iff the level is an explicit numeral `Succ^n(Zero)`. -/
def levelExplicitOffset (l : Level) : Option (Level × Nat) :=
  let (base, n) := levelPeelSucc l
  match base with
  | .zero _ => some (base, n)
  | _ => none

/-- Mirrors Rust `Level::max_smart` (common/src/env.rs:356).

    Smart `max x y` constructor mirroring the kernel's `KUniv::max`.
    Applies Lean-style level simplifications so substituted levels match
    the canonical form the kernel sees post-ingress: `max(a,a)=a`, zero
    absorption, same-base offset, and `Max` absorption. -/
def levelMaxSmart (x y : Level) : Level := Id.run do
  if let (some (_, ox), some (_, oy)) := (levelExplicitOffset x, levelExplicitOffset y) then
    -- Both explicit numerals (Succ^n(Zero)): take the larger.
    return if ox >= oy then x else y
  if x == y then
    return x
  if let .zero _ := x then
    return y
  if let .zero _ := y then
    return x
  -- max(a, max(a, b')) = max(a, b'), max(a, max(b', a)) = max(b', a)
  if let .max bl br _ := y then
    if bl == x || br == x then
      return y
  -- max(max(a', b), b) = max(a', b), max(max(b, a'), b) = max(b, a')
  if let .max al ar _ := x then
    if al == y || ar == y then
      return x
  -- Same base, different offsets: succ^n(x) vs succ^m(x) → take larger.
  let (baseX, offX) := levelPeelSucc x
  let (baseY, offY) := levelPeelSucc y
  if baseX == baseY then
    return if offX >= offY then x else y
  return Level.mkMax x y

/-- Mirrors Rust `Level::imax_smart` (common/src/env.rs:398).

    Smart `imax x y` constructor mirroring the kernel's `KUniv::imax`:
    when `y` is provably never zero (succ-headed), `imax = max`;
    `imax(_, 0) = 0`; `imax(0, b) = b`; `imax(1, b) = b`; `imax(a, a) = a`. -/
def levelImaxSmart (x y : Level) : Level := Id.run do
  -- y "never zero" cases: succ-headed levels are always > 0, so
  -- imax(a, succ _) = max(a, succ _).
  if let .succ _ _ := y then
    return levelMaxSmart x y
  if let .zero _ := y then
    return y -- imax(a, 0) = 0
  if let .zero _ := x then
    return y -- imax(0, b) = b
  -- imax(1, b) = b
  if let .succ inner _ := x then
    if let .zero _ := inner then
      return y
  if x == y then
    return x
  return Level.mkIMax x y

/-- Mirrors Rust `subst_level` (aux_gen/expr_utils.rs:922).

    Substitute universe parameters in a level. Uses the smart constructors
    `levelMaxSmart` and `levelImaxSmart` so that substituting away
    parameters produces the same canonical form the kernel sees
    post-ingress — without this normalization, compile-side and
    kernel-side would disagree on whether two structurally-different aux
    types (e.g. `Sort 1` vs `Sort (max 1 1)`) are equivalent. -/
partial def substLevel (lvl : Level) (params : Array Name) (univs : Array Level) : Level :=
  match lvl with
  | .zero _ | .mvar _ _ => lvl
  | .succ l _ => Level.mkSucc (substLevel l params univs)
  | .max a b _ =>
    levelMaxSmart (substLevel a params univs) (substLevel b params univs)
  | .imax a b _ =>
    levelImaxSmart (substLevel a params univs) (substLevel b params univs)
  | .param name _ => Id.run do
    for i in [0:params.size] do
      if params[i]! == name && i < univs.size then
        return univs[i]!
    return lvl

/-- Mirrors Rust `subst_levels` (aux_gen/expr_utils.rs:864).
    Substitute universe parameters in expressions. -/
partial def substLevels (expr : Expr) (params : Array Name) (univs : Array Level) : Expr :=
  if params.isEmpty || univs.isEmpty then expr
  else match expr with
  | .sort lvl _ => Expr.mkSort (substLevel lvl params univs)
  | .const name us _ =>
    Expr.mkConst name (us.map (substLevel · params univs))
  | .app f a _ =>
    Expr.mkApp (substLevels f params univs) (substLevels a params univs)
  | .lam n t b bi _ =>
    Expr.mkLam n (substLevels t params univs) (substLevels b params univs) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (substLevels t params univs) (substLevels b params univs) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (substLevels t params univs) (substLevels v params univs)
      (substLevels b params univs) nd
  | .proj n i e _ =>
    Expr.mkProj n i (substLevels e params univs)
  | .mdata md e _ =>
    Expr.mkMData md (substLevels e params univs)
  | _ => expr

/-! ## Diagnostics -/

mutual
/-- Mirrors Rust `Level::pretty` (common/src/env.rs:471).

    Human-readable representation of a universe level. Collapses chains of
    `Succ` into numeric literals and uses Lean-style syntax: `0`, `1`,
    `u`, `max u v`, `imax u v`, `?m`. Only used by `describeExprHead`
    diagnostics (not hash-load-bearing). -/
partial def levelPretty (l : Level) : String :=
  -- Peel Succ chains into a base + offset.
  let (base, offset) := levelPeelSucc l
  match base with
  | .zero _ => s!"{offset}"
  | .param name _ =>
    if offset == 0 then name.pretty
    else Id.run do
      -- u+1 → just show the additions
      let mut acc := name.pretty
      for _ in [0:offset] do
        acc := s!"{acc}+1"
      return acc
  | .mvar name _ =>
    if offset == 0 then s!"?{name.pretty}"
    else Id.run do
      let mut acc := s!"?{name.pretty}"
      for _ in [0:offset] do
        acc := s!"{acc}+1"
      return acc
  | .max a b _ =>
    if offset == 0 then s!"max {levelPrettyAtom a} {levelPrettyAtom b}"
    else Id.run do
      -- Succ(Max): wrap in parens
      let mut acc := levelPretty base
      for _ in [0:offset] do
        acc := s!"({acc})+1"
      return acc
  | .imax a b _ =>
    if offset == 0 then s!"imax {levelPrettyAtom a} {levelPrettyAtom b}"
    else Id.run do
      -- Succ(Imax): wrap in parens
      let mut acc := levelPretty base
      for _ in [0:offset] do
        acc := s!"({acc})+1"
      return acc
  | .succ .. => unreachable! -- Succ was already peeled.

/-- Mirrors Rust `Level::pretty_atom` (common/src/env.rs:519).
    Parenthesise compound levels (max, imax) so they can appear as
    arguments without ambiguity. -/
partial def levelPrettyAtom (l : Level) : String :=
  match l with
  | .max .. | .imax .. => s!"({levelPretty l})"
  | _ => levelPretty l
end

/-- Mirrors Rust `describe_expr_head` (aux_gen/expr_utils.rs:358).

    Short tag describing the head of an expression, for use in diagnostic
    messages. -/
def describeExprHead (e : Expr) : String :=
  match e with
  | .bvar i _ => s!"Bvar({i})"
  | .fvar n _ => s!"Fvar({n.pretty})"
  | .mvar n _ => s!"Mvar({n.pretty})"
  | .sort l _ => s!"Sort({levelPretty l})"
  | .const n _ _ => s!"Const({n.pretty})"
  | .app .. => "App"
  | .lam .. => "Lam"
  | .forallE .. => "ForallE"
  | .letE .. => "LetE"
  | .proj .. => "Proj"
  | .mdata .. => "Mdata"
  | .lit .. => "Lit"

/-! ## Telescopes (aux_gen/expr_utils.rs:254) -/

/-- Mirrors Rust `forall_telescope` (aux_gen/expr_utils.rs:277).

    Open N leading foralls of `expr`, replacing each BVar(0) with a fresh
    FVar. Returns the FVars, their declarations (outermost-first, suitable
    for `mkForall`/`mkLambda`), and the remaining body.

    `Mdata` wrappers on the forall spine are transparently peeled (and
    dropped) — Lean's own `forallTelescope` looks through them via WHNF.

    If the expression has fewer than `n` leading foralls, the returned
    `decls` is short. Callers indexing by position MUST verify
    `decls.size == n` before indexing; prefer `forallTelescopeExact` when
    a precise arity is required. -/
def forallTelescope (expr : Expr) (n : Nat) (pfx : String) (startIdx : Nat) :
    Array Expr × Array LocalDecl × Expr := Id.run do
  let mut fvars : Array Expr := #[]
  let mut decls : Array LocalDecl := #[]
  let mut cur := expr
  for i in [0:n] do
    -- Peel any Mdata wrappers before matching — they're structural no-ops.
    repeat
      match cur with
      | .mdata _ inner _ => cur := inner
      | _ => break
    match cur with
    | .forallE name dom body bi _ =>
      let (fvName, fv) := freshFVar pfx (startIdx + i)
      decls := decls.push
        { fvarName := fvName, binderName := name, domain := dom, info := bi }
      fvars := fvars.push fv
      cur := instantiate1 body fv
    | _ => break
  return (fvars, decls, cur)

/-- Mirrors Rust `forall_telescope_exact` (aux_gen/expr_utils.rs:318).

    Like `forallTelescope`, but errors if fewer than `n` foralls are
    peeled. `context` is a short human-readable tag (e.g.
    `"build_below_def"`); `what` describes what arity `n` was expected to
    count. Error channel: Rust returns `ixon::CompileError::UnsupportedExpr`;
    here the local `AuxGenError.unsupportedExpr` with the same message. -/
def forallTelescopeExact (expr : Expr) (n : Nat) (pfx : String) (startIdx : Nat)
    (context : String) (what : String) :
    Except AuxGenError (Array Expr × Array LocalDecl × Expr) :=
  let (fvars, decls, body) := forallTelescope expr n pfx startIdx
  if decls.size != n then
    -- Include enough context to pinpoint the shape problem: every peeled
    -- binder name plus the kind of node that blocked further peeling.
    let binderList := decls.toList.map fun d =>
      s!"{d.binderName.pretty}:{describeExprHead d.domain}"
    .error (.unsupportedExpr
      (s!"{context}: expected {n} leading foralls ({what}), got {decls.size}. " ++
       s!"Peeled binders (name:domain_kind): [{", ".intercalate binderList}]. " ++
       s!"Stopped at body kind: {describeExprHead body}. " ++
       "This is either a mismatch between the recursor's structural " ++
       "metadata and its actual type, or an unexpected binder shape " ++
       "(let/mdata/etc.) that forall_telescope doesn't peel through."))
  else
    .ok (fvars, decls, body)

/-- Mirrors Rust `instantiate_fvars_in_domain` (aux_gen/expr_utils.rs:1291).
    Domain is already in FVar form from `instantiate1` calls — identity. -/
def instantiateFVarsInDomain (dom : Expr) (_fvars : Array Expr)
    (_decls : Array LocalDecl) : Expr :=
  dom

/-- Mirrors Rust `lambda_telescope` (aux_gen/expr_utils.rs:1261).

    Open lambda binders into FVars (matching `forallTelescope` but for
    lambdas). NOTE the deliberate asymmetry with `forallTelescope`: the
    Rust lambda telescope does NOT peel `Mdata` wrappers — preserved here. -/
def lambdaTelescope (expr : Expr) (n : Nat) (pfx : String) (offset : Nat) :
    Array Expr × Array LocalDecl × Expr := Id.run do
  let mut fvars : Array Expr := #[]
  let mut decls : Array LocalDecl := #[]
  let mut cur := expr
  for i in [0:n] do
    match cur with
    | .lam name dom body bi _ =>
      let (fvName, fv) := freshFVar pfx (offset + i)
      let cleanDom := instantiateFVarsInDomain dom fvars decls
      decls := decls.push
        { fvarName := fvName, binderName := name, domain := cleanDom, info := bi }
      fvars := fvars.push fv
      cur := instantiate1 body fv
    | _ => break
  return (fvars, decls, cur)

/-! ## Abstraction: FVar -> BVar (aux_gen/expr_utils.rs:375) -/

/-- Mirrors Rust `abstract_fvar` (aux_gen/expr_utils.rs:387).

    Abstract a single FVar: replace all occurrences of `fvar fvarName`
    with `bvar depth`, and increment all existing BVars >= depth. This is
    the inverse of `instantiate1`. Prefer `batchAbstract` or
    `mkForall`/`mkLambda` which abstract all FVars in a single pass. -/
partial def abstractFVar (expr : Expr) (fvarName : Name) (depth : Nat) : Expr :=
  match expr with
  | .fvar n _ =>
    if n == fvarName then Expr.mkBVar depth else expr
  | .bvar i _ =>
    if i >= depth then Expr.mkBVar (i + 1) else expr
  | .app f a _ =>
    Expr.mkApp (abstractFVar f fvarName depth) (abstractFVar a fvarName depth)
  | .lam n t b bi _ =>
    Expr.mkLam n (abstractFVar t fvarName depth)
      (abstractFVar b fvarName (depth + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (abstractFVar t fvarName depth)
      (abstractFVar b fvarName (depth + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (abstractFVar t fvarName depth)
      (abstractFVar v fvarName depth)
      (abstractFVar b fvarName (depth + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (abstractFVar e fvarName depth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (abstractFVar e fvarName depth)
  | _ => expr

/-- Mirrors Rust `batch_abstract` (aux_gen/expr_utils.rs:518).

    Single-pass FVar→BVar abstraction for an entire binder telescope.
    Replaces all FVars (identified by `fvarMap`: FVar name → binder
    position, 0 = outermost) with the correct BVar indices in one walk,
    and shifts existing free BVars to account for the new binders.

    - `scopeDepth`: how many of our binders are in scope at this point
      (body: k; domain D_j: j).
    - `internalDepth`: expression-internal binder depth, starts at 0.
    - FVar at binder position `i`: `BVar((scopeDepth - 1 - i) + internalDepth)`.
    - Free BVar(n) where `n >= internalDepth`: shifted to `BVar(n + scopeDepth)`. -/
partial def batchAbstract (expr : Expr) (fvarMap : Std.HashMap Name Nat)
    (scopeDepth : Nat) (internalDepth : Nat) : Expr :=
  -- Fast path: no binders to abstract.
  if scopeDepth == 0 then expr
  else match expr with
  | .fvar name _ =>
    match fvarMap.get? name with
    | some pos =>
      if pos < scopeDepth then
        Expr.mkBVar ((scopeDepth - 1 - pos) + internalDepth)
      else
        -- FVar not yet in scope (e.g., a forward reference in a domain
        -- to a binder declared later). Leave as-is.
        expr
    | none =>
      -- FVar not in our telescope — leave as-is.
      expr
  | .bvar i _ =>
    if i >= internalDepth then
      -- Free BVar: shift up by scopeDepth to make room for our binders.
      Expr.mkBVar (i + scopeDepth)
    else
      -- Bound by an expression-internal binder — unchanged.
      expr
  | .app f a _ =>
    Expr.mkApp (batchAbstract f fvarMap scopeDepth internalDepth)
      (batchAbstract a fvarMap scopeDepth internalDepth)
  | .lam n t b bi _ =>
    Expr.mkLam n (batchAbstract t fvarMap scopeDepth internalDepth)
      (batchAbstract b fvarMap scopeDepth (internalDepth + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (batchAbstract t fvarMap scopeDepth internalDepth)
      (batchAbstract b fvarMap scopeDepth (internalDepth + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (batchAbstract t fvarMap scopeDepth internalDepth)
      (batchAbstract v fvarMap scopeDepth internalDepth)
      (batchAbstract b fvarMap scopeDepth (internalDepth + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (batchAbstract e fvarMap scopeDepth internalDepth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (batchAbstract e fvarMap scopeDepth internalDepth)
  -- Sort, Const, MVar, Lit — no FVars or BVars to process.
  | _ => expr

/-- Mirrors Rust `BinderKind` (aux_gen/expr_utils.rs:453). Constructor
    names deviate (`Forall`/`Lambda` → `forallE`/`lambda`) because
    `forall` is a Lean keyword. -/
inductive BinderKind where
  | forallE
  | lambda

/-- Mirrors Rust `mk_binder_chain` (aux_gen/expr_utils.rs:459).
    Shared implementation for `mkForall` and `mkLambda`. -/
def mkBinderChain (body : Expr) (binders : Array LocalDecl) (kind : BinderKind) :
    Expr := Id.run do
  let k := binders.size
  if k == 0 then
    return body
  -- Build FVar name → binder position map (0 = outermost).
  let mut fvarMap : Std.HashMap Name Nat := {}
  for i in [0:k] do
    fvarMap := fvarMap.insert binders[i]!.fvarName i
  -- Abstract body: all k binders in scope.
  let mut result := batchAbstract body fvarMap k 0
  -- Build binder chain from innermost to outermost.
  for j' in [0:k] do
    let j := k - 1 - j'
    let decl := binders[j]!
    -- Domain D_j: only binders 0..j-1 are in scope (scopeDepth = j).
    -- Binder j's domain is NOT under binder j itself — only the body is.
    let domain := batchAbstract decl.domain fvarMap j 0
    result := match kind with
      | .forallE => Expr.mkForallE decl.binderName domain result decl.info
      | .lambda => Expr.mkLam decl.binderName domain result decl.info
  return result

/-- Mirrors Rust `mk_forall` (aux_gen/expr_utils.rs:440).

    Build a forall chain by batch-abstracting all FVars in a single pass
    per sub-expression. `binders` is outermost-first. -/
def mkForall (body : Expr) (binders : Array LocalDecl) : Expr :=
  mkBinderChain body binders .forallE

/-- Mirrors Rust `mk_lambda` (aux_gen/expr_utils.rs:447).
    Same semantics as `mkForall` but produces `λ (x : T), body`. -/
def mkLambda (body : Expr) (binders : Array LocalDecl) : Expr :=
  mkBinderChain body binders .lambda

/-! ## Beta-reduction (aux_gen/expr_utils.rs:1300) -/

/-- Mirrors Rust `beta_reduce` (aux_gen/expr_utils.rs:1312).

    HEAD-ONLY beta reduction: reduces redexes on the outer application
    spine only; does NOT recurse into lambda/forall/let bodies,
    projections, or non-head subexpressions. Lean's kernel follows the
    same policy when constructing recursor types for nested inductives —
    a full recursive walk would eliminate `(λ_. T) arg` shapes that Lean
    preserves in the stored recursor and break alpha-congruence. -/
def betaReduce (expr : Expr) : Expr := Id.run do
  match expr with
  | .app .. =>
    -- Collect the application spine, reducing redexes as they surface.
    let mut head := expr
    let mut args : Array Expr := #[]
    repeat
      match head with
      | .app f a _ =>
        args := args.push a
        head := f
      | _ => break
    args := args.reverse
    -- Now `head` is a non-App; try to reduce `head args[0]` into head.
    let mut i := 0
    repeat
      if i < args.size then
        match head with
        | .lam _ _ body _ _ =>
          head := instantiate1 body args[i]!
          i := i + 1
        | _ => break
      else
        break
    -- Re-apply remaining args.
    let mut result := head
    for a in args[i:] do
      result := Expr.mkApp result a
    return result
  -- Non-App: no top-level redex to reduce.
  | _ => return expr

/-! ## Nested universe rewriting (aux_gen/expr_utils.rs:1361) -/

/-- Mirrors Rust `expr_mentions_any_name` (aux_gen/nested.rs:1609).

    Check if any `Const` or `Proj` name in `expr` is in `names`. Ported
    here (rather than a future Nested.lean) because
    `rewriteNestedConstLevelsWalk` depends on it. -/
def exprMentionsAnyName (expr : Expr) (names : Std.HashSet Name) : Bool := Id.run do
  if names.isEmpty then
    return false
  let mut stack : Array Expr := #[expr]
  repeat
    if let some e := stack.back? then
      stack := stack.pop
      match e with
      | .const n _ _ =>
        if names.contains n then
          return true
      | .app f a _ =>
        stack := stack.push f
        stack := stack.push a
      | .lam _ t b _ _ | .forallE _ t b _ _ =>
        stack := stack.push t
        stack := stack.push b
      | .letE _ t v b _ _ =>
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
      | .proj typeName _ val _ =>
        if names.contains typeName then
          return true
        stack := stack.push val
      | .mdata _ inner _ =>
        stack := stack.push inner
      -- BVar, FVar, MVar, Sort, Lit — no constant names.
      | _ => pure ()
    else
      break
  return false

mutual
/-- Mirrors Rust `rewrite_nested_const_levels_cached` (aux_gen/expr_utils.rs:1390).

    Targeted rewrite of nested type universe levels in constructor fields:
    for each application `Const(auxName, levels) args...` where `auxName`
    is an auxiliary flat member AND at least one of the first `nParams`
    args references a block member, rewrites the Const's levels to the
    occurrence level args. Non-nested occurrences are left unchanged.

    The Rust caller-managed `&mut FxHashMap<blake3::Hash, LeanExpr>` cache
    becomes `StateM ExprCache`. The cache must only be reused across calls
    whose `auxInfo` and `blockNames` are identical. -/
partial def rewriteNestedConstLevelsCached (expr : Expr)
    (auxInfo : Std.HashMap Name (Nat × Array Level))
    (blockNames : Std.HashSet Name) : StateM ExprCache Expr := do
  if let some cached := (← get).get? expr then
    return cached
  let result ← rewriteNestedConstLevelsWalk expr auxInfo blockNames
  modify (·.insert expr result)
  return result

/-- Mirrors Rust `rewrite_nested_const_levels_walk` (aux_gen/expr_utils.rs:1406). -/
partial def rewriteNestedConstLevelsWalk (expr : Expr)
    (auxInfo : Std.HashMap Name (Nat × Array Level))
    (blockNames : Std.HashSet Name) : StateM ExprCache Expr := do
  -- Try to decompose as an application of an auxiliary Const.
  let (head, args) := decomposeApps expr
  if let .const name levels _ := head then
    if let some (nParams, newLevels) := auxInfo.get? name then
      let hasNestedRef := args.any (exprMentionsAnyName · blockNames) 0 nParams
      if hasNestedRef && newLevels.size == levels.size then
        -- Rewrite head levels and recurse into args.
        let newHead := Expr.mkConst name newLevels
        let mut result := newHead
        for a in args do
          result := Expr.mkApp result
            (← rewriteNestedConstLevelsCached a auxInfo blockNames)
        return result
  -- Not a rewritable app — recurse into sub-expressions.
  match expr with
  | .app f a _ =>
    return Expr.mkApp (← rewriteNestedConstLevelsCached f auxInfo blockNames)
      (← rewriteNestedConstLevelsCached a auxInfo blockNames)
  | .lam n t b bi _ =>
    return Expr.mkLam n (← rewriteNestedConstLevelsCached t auxInfo blockNames)
      (← rewriteNestedConstLevelsCached b auxInfo blockNames) bi
  | .forallE n t b bi _ =>
    return Expr.mkForallE n (← rewriteNestedConstLevelsCached t auxInfo blockNames)
      (← rewriteNestedConstLevelsCached b auxInfo blockNames) bi
  | .letE n t v b nd _ =>
    return Expr.mkLetE n (← rewriteNestedConstLevelsCached t auxInfo blockNames)
      (← rewriteNestedConstLevelsCached v auxInfo blockNames)
      (← rewriteNestedConstLevelsCached b auxInfo blockNames) nd
  | .proj n i e _ =>
    return Expr.mkProj n i (← rewriteNestedConstLevelsCached e auxInfo blockNames)
  | .mdata md e _ =>
    return Expr.mkMData md (← rewriteNestedConstLevelsCached e auxInfo blockNames)
  | _ => return expr
end

/-! ## More expression utilities -/

/-- Mirrors Rust `consume_type_annotations` (aux_gen/expr_utils.rs:1492).

    Strip type annotation wrappers from a type expression, matching Lean's
    `Expr.consumeTypeAnnotations`: `outParam α` / `semiOutParam α` /
    `optParam α default` / `autoParam α tactic` → recurse on `α`. -/
partial def consumeTypeAnnotations (e : Expr) : Expr :=
  let (head, args) := decomposeApps e
  match head with
  | .const name _ _ =>
    let n := name.pretty
    if (n == "outParam" || n == "semiOutParam") && args.size == 1 then
      -- outParam.{u} (α : Sort u) := α — strip and recurse
      consumeTypeAnnotations args[0]!
    else if (n == "optParam" || n == "autoParam") && args.size == 2 then
      -- optParam.{u} (α : Sort u) (default : α) := α — strip to first arg
      consumeTypeAnnotations args[0]!
    else e
  | _ => e

/-- Mirrors Rust `subst_fvar` (aux_gen/expr_utils.rs:1552).

    Substitute all occurrences of `fvar fvarName` with `replacement`.
    Unlike `abstractFVar` (which replaces FVar with BVar), this replaces
    FVar with an arbitrary expression. -/
partial def substFVar (expr : Expr) (fvarName : Name) (replacement : Expr) : Expr :=
  match expr with
  | .fvar n _ =>
    if n == fvarName then replacement else expr
  | .app f a _ =>
    Expr.mkApp (substFVar f fvarName replacement) (substFVar a fvarName replacement)
  | .lam n t b bi _ =>
    Expr.mkLam n (substFVar t fvarName replacement)
      (substFVar b fvarName replacement) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (substFVar t fvarName replacement)
      (substFVar b fvarName replacement) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (substFVar t fvarName replacement)
      (substFVar v fvarName replacement)
      (substFVar b fvarName replacement) nd
  | .proj n i e _ =>
    Expr.mkProj n i (substFVar e fvarName replacement)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (substFVar e fvarName replacement)
  | _ => expr

/-- Mirrors Rust `replace_const_names_cached` (aux_gen/expr_utils.rs:1623).

    Replace `Const` names and `Proj` type names appearing as keys in `map`
    with their values, with a caller-managed memoization cache (`StateM
    ExprCache` here, `&mut FxHashMap<blake3::Hash, _>` in Rust). The cache
    must only be reused for calls with identical `map`. -/
partial def replaceConstNamesCached (expr : Expr)
    (map : Std.HashMap Name Name) : StateM ExprCache Expr := do
  if map.isEmpty then
    return expr
  if let some cached := (← get).get? expr then
    return cached
  let result ← match expr with
    | .const name lvls _ =>
      let newName := (map.get? name).getD name
      pure (Expr.mkConst newName lvls)
    | .app f a _ =>
      pure (Expr.mkApp (← replaceConstNamesCached f map)
        (← replaceConstNamesCached a map))
    | .forallE n d b bi _ =>
      pure (Expr.mkForallE n (← replaceConstNamesCached d map)
        (← replaceConstNamesCached b map) bi)
    | .lam n d b bi _ =>
      pure (Expr.mkLam n (← replaceConstNamesCached d map)
        (← replaceConstNamesCached b map) bi)
    | .letE n t v b nd _ =>
      pure (Expr.mkLetE n (← replaceConstNamesCached t map)
        (← replaceConstNamesCached v map)
        (← replaceConstNamesCached b map) nd)
    | .proj typeName idx e _ =>
      let newTypeName := (map.get? typeName).getD typeName
      pure (Expr.mkProj newTypeName idx (← replaceConstNamesCached e map))
    | .mdata kvs e _ =>
      pure (Expr.mkMData kvs (← replaceConstNamesCached e map))
    -- BVar, FVar, MVar, Sort, Lit — no constant names to replace.
    | _ => pure expr
  modify (·.insert expr result)
  return result

/-- Mirrors Rust `replace_const_names` (aux_gen/expr_utils.rs:1605).

    Convenience wrapper around `replaceConstNamesCached` that owns a fresh
    cache. (Rust gates this under `#[cfg(test)]`; production callers manage
    their own cache for reuse across many calls with the same `map`.) -/
def replaceConstNames (expr : Expr) (map : Std.HashMap Name Name) : Expr :=
  if map.isEmpty then expr
  else (replaceConstNamesCached expr map).run' {}

/-- Mirrors Rust `find_motive_fvar` (aux_gen/expr_utils.rs:1684).

    Check if the head of `dom` (after peeling foralls) is one of the given
    `motiveFVars`. Returns `some classIndex` if matched. -/
def findMotiveFVar (dom : Expr) (motiveFVars : Array Expr) : Option Nat := Id.run do
  let mut ty := dom
  repeat
    match ty with
    | .forallE _ _ body _ _ =>
      ty := body
    | _ =>
      let (head, _) := decomposeApps ty
      if let .fvar name _ := head then
        for j in [0:motiveFVars.size] do
          if let .fvar mn _ := motiveFVars[j]! then
            if name == mn then
              return some j
      return none
  return none -- unreachable: the non-forall arm always returns

/-! ## Pure helpers shared with the kernel-backed half

These are pure expression predicates/collectors whose only Rust callers
live in the kernel-backed half of expr_utils.rs (WHNF source-name
restoration, on-demand kenv ingress). Ported now so the kernel-bridge
milestone can consume them. -/

/-- Mirrors Rust `expr_has_bvar` (aux_gen/expr_utils.rs:3025). -/
partial def exprHasBVar (expr : Expr) : Bool :=
  match expr with
  | .bvar .. => true
  | .app f a _ => exprHasBVar f || exprHasBVar a
  | .forallE _ d b _ _ | .lam _ d b _ _ => exprHasBVar d || exprHasBVar b
  | .letE _ t v b _ _ => exprHasBVar t || exprHasBVar v || exprHasBVar b
  | .proj _ _ v _ | .mdata _ v _ => exprHasBVar v
  | _ => false

/-- Mirrors Rust `strip_mdata_ref` (aux_gen/expr_utils.rs:3127).
    Peel all outer `mdata` wrappers. -/
partial def stripMdataRef (expr : Expr) : Expr :=
  match expr with
  | .mdata _ inner _ => stripMdataRef inner
  | _ => expr

/-- Mirrors Rust `source_name_hint_candidate` (aux_gen/expr_utils.rs:2780). -/
def sourceNameHintCandidate (expr : Expr) : Bool :=
  match expr with
  | .app .. | .proj .. => true
  | _ => false

/-- Mirrors Rust `collect_lean_const_refs` (aux_gen/expr_utils.rs:3235).

    Collect every `Const` name and `Proj` type name in `expr` into `out`.
    Rust threads `&mut FxHashSet<Name>`; here the set is passed in and the
    extended set returned. -/
def collectLeanConstRefs (expr : Expr) (out : Std.HashSet Name) : Std.HashSet Name :=
  Id.run do
    let mut out := out
    let mut stack : Array Expr := #[expr]
    repeat
      if let some e := stack.back? then
        stack := stack.pop
        match e with
        | .const name _ _ =>
          out := out.insert name
        | .app f a _ =>
          stack := stack.push f
          stack := stack.push a
        | .forallE _ d b _ _ | .lam _ d b _ _ =>
          stack := stack.push d
          stack := stack.push b
        | .letE _ t v b _ _ =>
          stack := stack.push t
          stack := stack.push v
          stack := stack.push b
        | .proj typeName _ e' _ =>
          out := out.insert typeName
          stack := stack.push e'
        | .mdata _ e' _ =>
          stack := stack.push e'
        | _ => pure ()
      else
        break
    return out

/-! ## Restore: replace auxiliary const refs with original nested
expressions (aux_gen/expr_utils.rs:949) -/

/-- Mirrors Rust `RestoreStateCache` (aux_gen/expr_utils.rs:989).
    Block-scoped cached state, populated lazily on the first `restore`. -/
structure RestoreStateCache where
  /-- `auxName → nested instantiated with the per-call subst FVars`. -/
  auxRestored : Std.HashMap Name Expr
  /-- `auxInd name → (origHeadLevels, origIndArgs)` from decomposing the
      restored nested expression, for the aux-ctor restoration path. -/
  auxDecomp : Std.HashMap Name (Array Level × Array Expr)
  /-- Walk memoization shared across every `restore` call on this context. -/
  walkCache : ExprCache

instance : Inhabited RestoreStateCache := ⟨{}, {}, {}⟩

/-- Mirrors Rust `RestoreCtx` (aux_gen/expr_utils.rs:958).

    Context for restoring auxiliary const references back to original
    nested inductive applications. Rust holds the lazily-populated cache
    in a `RefCell`; here `restore` returns the updated context alongside
    the result (explicit state-passing) — reuse the returned context to
    keep the block-scoped caches warm. -/
structure RestoreCtx where
  /-- `auxName → nestedExpr`: the original nested application with block
      param FVars. -/
  auxToNested : Std.HashMap Name Expr
  /-- `auxCtorName → (origCtorName, origIndName)`. -/
  auxCtorMap : Std.HashMap Name (Name × Name)
  /-- `auxRecName → canonicalRecName`. -/
  auxRecMap : Std.HashMap Name Name
  /-- Block-param FVars used during expansion. -/
  blockParamFVars : Array Expr
  /-- Number of block parameters. -/
  nParams : Nat
  /-- Lazily-initialised block-scoped cache (Rust: `RefCell<Option<_>>`).
      Safe to share across calls: `forallTelescope`/`lambdaTelescope`
      allocate FVars via the deterministic `freshFVar "rp" i` scheme, so
      the substitution is identical for every `restore` call. -/
  cached : Option RestoreStateCache := none

namespace RestoreCtx

/-- Mirrors Rust `RestoreCtx::new` (aux_gen/expr_utils.rs:1018). -/
def new (auxToNested : Std.HashMap Name Expr)
    (auxCtorMap : Std.HashMap Name (Name × Name))
    (auxRecMap : Std.HashMap Name Name)
    (blockParamFVars : Array Expr) (nParams : Nat) : RestoreCtx :=
  { auxToNested, auxCtorMap, auxRecMap, blockParamFVars, nParams, cached := none }

/-- Mirrors Rust `RestoreCtx::ensure_cache` (aux_gen/expr_utils.rs:1042).

    Lazily initialise the cached per-aux substitution + walk cache. The
    cache is keyed implicitly on `(nParams, auxToNested, blockParamFVars)`
    — all inherent to the `RestoreCtx` — so entries populated by one call
    remain valid for every subsequent call on the same context. -/
def ensureCache (ctx : RestoreCtx) : RestoreCtx := Id.run do
  if ctx.cached.isSome then
    return ctx
  -- Canonical telescope FVars: every real `restore` call peels via
  -- `forallTelescope`/`lambdaTelescope`, which allocate via the
  -- deterministic `freshFVar "rp" i` — so these are the exact FVars every
  -- call sees after peeling.
  let asFVars : Array Expr := (Array.range ctx.nParams).map (fun i => (freshFVar "rp" i).2)
  let substFVars : Array Expr := asFVars.reverse
  let mut bpFVarMap : Std.HashMap Name Nat := {}
  for i in [0:ctx.blockParamFVars.size] do
    match ctx.blockParamFVars[i]! with
    | .fvar n _ => bpFVarMap := bpFVarMap.insert n i
    | _ => pure ()
  let mut auxRestored : Std.HashMap Name Expr := {}
  let mut auxDecomp : Std.HashMap Name (Array Level × Array Expr) := {}
  for (auxName, nested) in ctx.auxToNested do
    let abstracted := batchAbstract nested bpFVarMap ctx.nParams 0
    let restored := instantiateRev abstracted substFVars
    let (origHead, origArgs) := decomposeApps restored
    if let .const _ origLevels _ := origHead then
      auxDecomp := auxDecomp.insert auxName (origLevels, origArgs)
    auxRestored := auxRestored.insert auxName restored
  return { ctx with
    cached := some { auxRestored, auxDecomp, walkCache := {} } }

mutual
/-- Mirrors Rust `RestoreState::replace_walk` (aux_gen/expr_utils.rs:1138).
    Memoizes on the expression's structural hash (hash-keyed `ExprCache`). -/
partial def replaceWalk (ctx : RestoreCtx) (e : Expr) :
    StateM RestoreStateCache Expr := do
  if let some cached := (← get).walkCache.get? e then
    return cached
  let result ← replaceWalkUncached ctx e
  modify fun c => { c with walkCache := c.walkCache.insert e result }
  return result

/-- Mirrors Rust `RestoreState::replace_walk_uncached`
    (aux_gen/expr_utils.rs:1148). -/
partial def replaceWalkUncached (ctx : RestoreCtx) (e : Expr) :
    StateM RestoreStateCache Expr := do
  -- Check for bare Const matching auxRecMap (recursor rename).
  if let .const name levels _ := e then
    if let some newName := ctx.auxRecMap.get? name then
      return Expr.mkConst newName levels
  -- Check for application whose head is an aux type or aux constructor.
  let (head, args) := decomposeApps e
  if let .const name levels _ := head then
    -- Case 1: aux type reference → replace with original nested app.
    if let some restored := (← get).auxRestored.get? name then
      let n := ctx.nParams
      -- (Rust debug_asserts args.len() >= n — release no-op.)
      -- Apply remaining args (indices past params).
      let mut result := restored
      for i in [n:args.size] do
        result := Expr.mkApp result (← replaceWalk ctx args[i]!)
      return result
    -- Case 2: aux constructor reference → rename and restore. Matches C++
    -- restore_nested lines 852-866: look up the nested expression for the
    -- constructor's aux inductive, decompose it to get the original ind's
    -- Const (with levels), then rename the constructor and apply the
    -- original ind's params + remaining args.
    if let some (origCtor, auxInd) := ctx.auxCtorMap.get? name then
      if let some (origLevels, origIndArgs) := (← get).auxDecomp.get? auxInd then
        -- Build: orig_ctor.{I_lvls} spec_params remaining_args
        let newFn := Expr.mkConst origCtor origLevels
        let mut result := newFn
        for a in origIndArgs do
          result := Expr.mkApp result a
        for i in [ctx.nParams:args.size] do
          result := Expr.mkApp result (← replaceWalk ctx args[i]!)
        return result
      -- Fallback: just rename the const and recurse args. In practice
      -- never hit, but kept for defensive parity with Rust.
      let newHead := Expr.mkConst origCtor levels
      let mut result := newHead
      for a in args do
        result := Expr.mkApp result (← replaceWalk ctx a)
      return result
    -- Case 3: aux rec name in application position.
    if let some newName := ctx.auxRecMap.get? name then
      let newHead := Expr.mkConst newName levels
      let mut result := newHead
      for a in args do
        result := Expr.mkApp result (← replaceWalk ctx a)
      return result
  -- No match — recurse into sub-expressions.
  match e with
  | .app f a _ =>
    return Expr.mkApp (← replaceWalk ctx f) (← replaceWalk ctx a)
  | .lam n t b bi _ =>
    return Expr.mkLam n (← replaceWalk ctx t) (← replaceWalk ctx b) bi
  | .forallE n t b bi _ =>
    return Expr.mkForallE n (← replaceWalk ctx t) (← replaceWalk ctx b) bi
  | .letE n t v b nd _ =>
    return Expr.mkLetE n (← replaceWalk ctx t) (← replaceWalk ctx v)
      (← replaceWalk ctx b) nd
  | .proj n i val _ =>
    return Expr.mkProj n i (← replaceWalk ctx val)
  | .mdata md inner _ =>
    return Expr.mkMData md (← replaceWalk ctx inner)
  | _ => return e
end

/-- Mirrors Rust `RestoreCtx::restore` (aux_gen/expr_utils.rs:1097).

    Restore a complete expression (type or value) by peeling params,
    walking the body to replace aux references, and re-wrapping. Matches
    C++ `restore_nested` (`inductive.cpp:828-872`).

    Deviation from Rust: the `RefCell`-held cache becomes explicit state —
    the updated context is returned and should be threaded into subsequent
    `restore` calls to preserve the block-scoped memoization. -/
def restore (ctx : RestoreCtx) (expr : Expr) : Expr × RestoreCtx :=
  if ctx.auxToNested.isEmpty && ctx.auxCtorMap.isEmpty && ctx.auxRecMap.isEmpty then
    (expr, ctx)
  else Id.run do
    let ctx := ctx.ensureCache
    -- Peel nParams Pi or Lambda binders, creating fresh locals. These
    -- coincide with the FVars used by `ensureCache` to precompute
    -- `auxRestored`.
    let isPi := match expr with
      | .forallE .. => true
      | _ => false
    let (_asFVars, asDecls, body) :=
      if isPi then forallTelescope expr ctx.nParams "rp" 0
      else lambdaTelescope expr ctx.nParams "rp" 0
    let cache := ctx.cached.get! -- ensureCache guarantees initialisation
    let (restoredBody, cache) := ((replaceWalk ctx body).run cache).run
    let ctx := { ctx with cached := some cache }
    let result :=
      if isPi then mkForall restoredBody asDecls
      else mkLambda restoredBody asDecls
    return (result, ctx)

end RestoreCtx

end Ix.AuxGen

end
