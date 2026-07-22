/-
  Ix.Ground: groundedness checking for Lean environment constants.

  Pure-Lean port of Rust `crates/compile/src/ground.rs` (compiler
  alignment). A constant is "grounded" if all its references resolve to
  known constants, all bound variables are in scope, and no metavariables
  remain. Ungroundedness propagates through the reference graph: if A
  references ungrounded B, then A is also ungrounded.

  Map types: the reverse-reference graph parameter uses `Map Name (Set
  Name)` — the `Ix.Common` aliases for `Std.HashMap` / `Std.HashSet` —
  which is exactly the shape `Ix.GraphM` produces (`GraphM.env : ... →
  Map Ix.Name (Set Ix.Name)`) and mirrors Rust `RefMap =
  FxHashMap<Name, FxHashSet<Name>>` (crates/compile/src/graph.rs:30).

  Determinism contract (vs Rust rayon parallelism): the immediate scan
  checks each constant independently, so the RESULT SET of ungrounded
  names (and the error kind of each immediately-ungrounded constant) is
  independent of iteration order — in Rust (par_iter) and here
  (sequential) alike. Transitive `ref` attribution payloads depend on
  worklist pop order and are NOT contract-stable; see
  `proliferateUngrounded`.
-/
module

public import Ix.Common
public import Ix.Environment
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Ix

/-- Reason a constant failed groundedness checking. Mirrors Rust
    `GroundError` (ground.rs:26).

    The Rust `Indc` payload is boxed (`Box<(InductiveVal,
    Option<ConstantInfo>)>`) purely to keep the enum small; here the
    payload is carried inline. `idx` mirrors Rust `Idx(Nat)` — declared
    in the enum but never constructed inside ground.rs itself. -/
inductive GroundError where
  /-- A universe level parameter or metavariable is not in scope. -/
  | level (l : Level) (univs : Array Name)
  /-- A referenced constant does not exist in the environment (or is
      itself ungrounded, for transitively-attributed errors). -/
  | ref (n : Name)
  /-- An expression-level metavariable was encountered. -/
  | mvar (e : Expr)
  /-- A free or out-of-scope bound variable was encountered. -/
  | var (e : Expr) (binds : Nat)
  /-- An inductive type's constructor is missing (`none`) or has the
      wrong kind (`some <non-ctor constant>`). -/
  | indc (val : InductiveVal) (info : Option ConstantInfo)
  /-- An invalid de Bruijn index. -/
  | idx (n : Nat)
  deriving Repr

instance : Inhabited GroundError := ⟨.idx 0⟩

/-- Payload-free tag for a `GroundError`. Lean-side addition (no Rust
    counterpart): transitive `ref` attributions depend on worklist pop
    order (see `proliferateUngrounded`), so tests and cross-impl
    comparisons should compare kinds, not payloads. -/
inductive GroundErrorKind where
  | level | ref | mvar | var | indc | idx
  deriving BEq, Repr, Inhabited

/-- The payload-free kind tag of this error. -/
def GroundError.kind : GroundError → GroundErrorKind
  | .level .. => .level
  | .ref .. => .ref
  | .mvar .. => .mvar
  | .var .. => .var
  | .indc .. => .indc
  | .idx .. => .idx

/-- Per-constant traversal caches. Mirrors Rust `GroundState`
    (ground.rs:110, `#[derive(Default)]`).

    NOTE the expr cache keys on `(binder-depth, expr)` — the same
    expression reached at a different de Bruijn depth is re-checked. The
    univ cache keys on the level alone, which is sound because `univs`
    is fixed for the lifetime of one `GroundState` (a fresh state is
    created per constant in `groundConstCheck`). Both `Ix.Expr` and
    `Ix.Level` hash/compare by their embedded blake3 address, matching
    the Rust `Hash`/`Eq` behavior. -/
structure GroundState where
  exprCache : Std.HashSet (Nat × Expr)
  univCache : Std.HashSet Level

/-- Mirrors Rust `GroundState::default()`. -/
def GroundState.init : GroundState := ⟨{}, {}⟩

instance : Inhabited GroundState := ⟨.init⟩

/-- Checking monad: Rust threads `&mut GroundState` and returns
    `Result<(), GroundError>`; here `StateT GroundState (Except
    GroundError)`. On `throw` the state is discarded — observationally
    identical to Rust, because an error aborts the whole per-constant
    check and the state is local to (and dropped by)
    `groundConstCheck`. -/
abbrev GroundM := StateT GroundState (Except GroundError)

/-- Level parameters of a constant. Mirrors Rust `const_univs`
    (ground.rs:97, private in Rust). -/
def constUnivs : ConstantInfo → Array Name
  | .axiomInfo val => val.cnst.levelParams
  | .defnInfo val => val.cnst.levelParams
  | .thmInfo val => val.cnst.levelParams
  | .opaqueInfo val => val.cnst.levelParams
  | .quotInfo val => val.cnst.levelParams
  | .inductInfo val => val.cnst.levelParams
  | .ctorInfo val => val.cnst.levelParams
  | .recInfo val => val.cnst.levelParams

/-- Ground-check a universe level against the in-scope parameter list.
    Mirrors Rust `ground_level` (ground.rs:221, private in Rust):
    cache-hit returns Ok, cache insert happens BEFORE the match;
    `param` not in `univs` and `mvar` both fail with `.level`. -/
partial def groundLevel (level : Level) (univs : Array Name) : GroundM Unit := do
  let key := level
  if (← get).univCache.contains key then
    return ()
  modify fun stt => { stt with univCache := stt.univCache.insert key }
  match level with
  | .zero _ => pure ()
  | .succ x _ => groundLevel x univs
  | .max x y _ | .imax x y _ =>
    groundLevel x univs
    groundLevel y univs
  | .param n _ =>
    if !univs.contains n then
      throw (.level level univs)
  | .mvar _ _ =>
    throw (.level level univs)

/-- Ground-check an expression. Mirrors Rust `ground_expr`
    (ground.rs:166, private in Rust).

    Traversal/cache semantics preserved exactly:
    - cache key is `(binds, expr)`; hit returns Ok, insert happens
      BEFORE the match (even for exprs that then fail);
    - `mdata` recurses at the SAME depth;
    - `bvar idx` fails with `.var expr binds` when `idx >= binds`;
    - `const`: all level args are checked BEFORE the env lookup;
    - `lam`/`forallE`: type at `binds`, body at `binds + 1`;
    - `letE`: type and value at `binds`, body at `binds + 1`;
    - `proj`: env lookup BEFORE recursing into the struct;
    - `lit` is grounded; `mvar` fails with `.mvar`; `fvar` fails with
      `.var expr binds`. -/
partial def groundExpr (expr : Expr) (env : Environment) (univs : Array Name)
    (binds : Nat) : GroundM Unit := do
  let key := (binds, expr)
  if (← get).exprCache.contains key then
    return ()
  modify fun stt => { stt with exprCache := stt.exprCache.insert key }
  match expr with
  | .mdata _ e _ => groundExpr e env univs binds
  | .bvar idx _ =>
    if idx >= binds then
      throw (.var expr binds)
  | .sort level _ => groundLevel level univs
  | .const name levels _ =>
    for level in levels do
      groundLevel level univs
    if !env.consts.contains name then
      throw (.ref name)
  | .app f a _ =>
    groundExpr f env univs binds
    groundExpr a env univs binds
  | .lam _ t b _ _ | .forallE _ t b _ _ =>
    groundExpr t env univs binds
    groundExpr b env univs (binds + 1)
  | .letE _ t v b _ _ =>
    groundExpr t env univs binds
    groundExpr v env univs binds
    groundExpr b env univs (binds + 1)
  | .proj name _ e _ =>
    if !env.consts.contains name then
      throw (.ref name)
    groundExpr e env univs binds
  | .lit _ _ => pure ()
  | .mvar _ _ => throw (.mvar expr)
  | .fvar _ _ => throw (.var expr binds)

/-- Ground-check one decoded constant. Mirrors Rust `ground_const`
    (ground.rs:116, private in Rust).

    Order preserved exactly: `defn`/`thm`/`opaque` check type THEN
    value; `inductInfo` checks that every listed ctor exists in the env
    AND is a `ctorInfo` (failing with `.indc val ci` where `ci` is the
    looked-up constant, `none` if missing) BEFORE grounding its own
    type; `recInfo` grounds every rule's rhs BEFORE its own type. -/
def groundConst (constant : ConstantInfo) (env : Environment)
    (univs : Array Name) (binds : Nat) : GroundM Unit := do
  match constant with
  | .axiomInfo val =>
    groundExpr val.cnst.type env univs binds
  | .defnInfo val =>
    groundExpr val.cnst.type env univs binds
    groundExpr val.value env univs binds
  | .thmInfo val =>
    groundExpr val.cnst.type env univs binds
    groundExpr val.value env univs binds
  | .opaqueInfo val =>
    groundExpr val.cnst.type env univs binds
    groundExpr val.value env univs binds
  | .quotInfo val =>
    groundExpr val.cnst.type env univs binds
  | .inductInfo val =>
    for ctor in val.ctors do
      let ci := env.consts.get? ctor
      match ci with
      | some (.ctorInfo _) => pure ()
      | _ => throw (.indc val ci)
    groundExpr val.cnst.type env univs binds
  | .ctorInfo val =>
    groundExpr val.cnst.type env univs binds
  | .recInfo val =>
    for rule in val.rules do
      groundExpr rule.rhs env univs binds
    groundExpr val.cnst.type env univs binds

/-- Per-constant groundedness check, for callers that already hold a
    decoded constant and check as part of a wider pass. Mirrors Rust
    `ground_const_check` (ground.rs:66): fresh `GroundState` per
    constant, starting at binder depth 0. -/
def groundConstCheck (constant : ConstantInfo) (env : Environment) :
    Except GroundError Unit :=
  let univs := constUnivs constant
  (groundConst constant env univs 0).run' GroundState.init

/-- Spread ungroundedness from the immediately-ungrounded set through
    the reverse-reference graph: anything referencing an ungrounded
    constant is itself ungrounded. Mirrors Rust `proliferate_ungrounded`
    (ground.rs:78): a stack worklist seeded with the immediate error
    keys; popping `popped` inserts `.ref popped` for each in-ref not
    already in the map (vacant-entry semantics — existing entries,
    including all immediate errors, are never overwritten) and pushes it.

    CONTRACT STABILITY: the resulting SET of ungrounded names — and the
    error of every immediately-ungrounded constant — is independent of
    seed/pop order (a name is added iff it transitively references an
    immediately-ungrounded name). The `.ref` ATTRIBUTION payload of a
    transitively-added name is whichever ungrounded dependency happened
    to pop first, which depends on hash-map key order and stack
    discipline; it differs between Rust and Lean (and between runs of
    neither in general). Consumers must not rely on transitive
    attribution payloads — compare kinds (`GroundError.kind`) instead. -/
def proliferateUngrounded (ungrounded : Map Name GroundError)
    (inRefs : Map Name (Set Name)) : Map Name GroundError := Id.run do
  let mut ungrounded := ungrounded
  let mut stack : Array Name := ungrounded.keysArray
  repeat
    match stack.back? with
    | none => break
    | some popped =>
      stack := stack.pop
      match inRefs.get? popped with
      | none => pure ()
      | some inRefSet =>
        for inRef in inRefSet do
          if !ungrounded.contains inRef then
            ungrounded := ungrounded.insert inRef (.ref popped)
            stack := stack.push inRef
  return ungrounded

/-- Checks every constant in `env` for groundedness and returns a map of
    all ungrounded names. Mirrors Rust `ground_consts` (ground.rs:45):
    first collects immediately ungrounded constants (Rust: rayon
    par_iter over `env.keys()`; here: a sequential pass over
    `env.consts` — each constant is checked independently against a
    fresh `GroundState`, so the resulting map does not depend on
    iteration order), then propagates ungroundedness transitively
    through `inRefs` (the reverse reference graph). -/
def groundConsts (env : Environment) (inRefs : Map Name (Set Name)) :
    Map Name GroundError := Id.run do
  let mut ungrounded : Map Name GroundError := {}
  for (name, constant) in env.consts do
    match groundConstCheck constant env with
    | .error err => ungrounded := ungrounded.insert name err
    | .ok _ => pure ()
  return proliferateUngrounded ungrounded inRefs

end Ix

end
