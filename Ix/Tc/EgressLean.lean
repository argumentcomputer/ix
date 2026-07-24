module

public import Ix.Tc.Ingress
public import Ix.Environment

/-!
Mirror: crates/compile/src/kernel_egress.rs (the `lean_egress` /
`egress_constant` / `egress_expr` / `egress_level` half, Meta mode)

Kernel → Lean egress: convert `KConst .meta` back to the LEON environment
mirror (`Ix.ConstantInfo` / `Ix.Expr` / `Ix.Level`, per-node Blake3
hashes). Meta mode only — it needs real names and binder infos.

- Levels egress by structural recursion (`param idx → levelParams[idx]`,
  anon fallback — Rust parity).
- Expressions egress on an explicit stack machine (Init-scale terms
  overflow default runtime stacks; Rust runs the recursive converter on
  big stacks). The per-constant memo keys on the metadata-aware
  `metaAddr` (`ExprInfo.metaAddr`) — a semantic-address key would return
  a metadata-different twin's egression.
- `fvar` is a hard error: egress runs on closed expressions only.
- mdata layers re-wrap innermost-first (Rust: reverse-fold).
- `Indc` egress stubs `numNested`/`isRec`/`isReflexive` (Rust computes
  them in `lean_egress` stage 2; the roundtrip comparison never reads
  them — `compare_envs` checks type/value/rule hashes only).

The comparator half (`compareLeanCI`, `findDiff`) mirrors
`crates/ffi/src/kernel.rs::{compare_envs, find_diff}` semantics: compare
content hashes — type always, value for defn/thm/opaque, per-rule RHS for
recursors — and walk to the first structural divergence for messages.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap)

/-- `Ix.DefinitionSafety` → `Lean.DefinitionSafety` (LEON stores the Lean
    enum). -/
def safetyToLean : Ix.DefinitionSafety → Lean.DefinitionSafety
  | .unsaf => .unsafe | .safe => .safe | .part => .partial

/-- `Ix.QuotKind` → `Lean.QuotKind`. -/
def quotKindToLean : Ix.QuotKind → Lean.QuotKind
  | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind

/-! ### Level egress -/

/-- Convert a kernel universe to an `Ix.Level` (Rust `egress_level`). -/
def egressLevel (levelParams : Array Name) : KUniv .«meta» → Ix.Level
  | .zero _ => Ix.Level.mkZero
  | .succ inner _ => Ix.Level.mkSucc (egressLevel levelParams inner)
  | .max a b _ =>
    Ix.Level.mkMax (egressLevel levelParams a) (egressLevel levelParams b)
  | .imax a b _ =>
    Ix.Level.mkIMax (egressLevel levelParams a) (egressLevel levelParams b)
  | .param idx _ _ =>
    -- Positional index resolves through the constant's level params
    -- (anon fallback on OOB — Rust parity). The node's own stored name is
    -- display metadata; the positional name is authoritative.
    Ix.Level.mkParam ((levelParams[idx.toNat]?).getD Ix.Name.mkAnon)

def egressLevels (levelParams : Array Name) (us : Array (KUniv .«meta»)) :
    Array Ix.Level :=
  us.map (egressLevel levelParams)

/-! ### Expression egress (explicit stack machine) -/

/-- Egress frames. `*Done` frames carry the metadata needed to rebuild the
    node once children are on the value stack, plus the node's mdata
    layers for the innermost-first re-wrap. -/
inductive LFrame where
  | process (e : KExpr .«meta»)
  | appDone (mdata : Array MData)
  | lamDone (name : Name) (bi : Lean.BinderInfo) (mdata : Array MData)
  | allDone (name : Name) (bi : Lean.BinderInfo) (mdata : Array MData)
  | letDone (name : Name) (nd : Bool) (mdata : Array MData)
  | prjDone (name : Name) (field : UInt64) (mdata : Array MData)
  | cacheAt (addr : Address)
  deriving Inhabited

/-- Re-wrap an egressed node with its mdata layers, innermost first (Rust:
    reverse-fold over `expr.mdata()`). -/
def applyMDataLayers (mdata : Array MData) (e : Ix.Expr) : Ix.Expr :=
  mdata.foldr (init := e) fun layer acc => Ix.Expr.mkMData layer acc

/-- Convert a kernel expression to an `Ix.Expr` (Rust `egress_expr`),
    iterative. The cache is per-constant, keyed by the metadata-aware
    `metaAddr` — the semantic address would collapse metadata-different
    twins (`ExprInfo.metaAddr`). -/
def egressExpr (levelParams : Array Name)
    (cache : HashMap Address Ix.Expr) (root : KExpr .«meta») :
    Except IngressErr (Ix.Expr × HashMap Address Ix.Expr) := do
  let mut cache := cache
  let mut stack : Array LFrame := #[.process root]
  let mut values : Array Ix.Expr := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process e =>
      if let some cached := cache[e.info.metaAddr]? then
        values := values.push cached
        continue
      let mdata := e.mdata
      match e with
      | .var idx _ _ =>
        values := values.push
          (applyMDataLayers mdata (Ix.Expr.mkBVar idx.toNat))
        -- Leaves are cheap; cache only via the parent path (Rust caches
        -- every node — do the same for exactness).
        cache := cache.insert e.info.metaAddr
          (applyMDataLayers mdata (Ix.Expr.mkBVar idx.toNat))
      | .fvar id _ _ =>
        throw s!"egressExpr: unexpected FVar({id}) — abstract back to \
                 de Bruijn before exporting"
      | .sort u _ =>
        let out := applyMDataLayers mdata
          (Ix.Expr.mkSort (egressLevel levelParams u))
        values := values.push out
        cache := cache.insert e.info.metaAddr out
      | .const id us _ =>
        let out := applyMDataLayers mdata
          (Ix.Expr.mkConst id.name (egressLevels levelParams us))
        values := values.push out
        cache := cache.insert e.info.metaAddr out
      | .app f a _ =>
        stack := stack.push (.cacheAt e.info.metaAddr) |>.push (.appDone mdata)
          |>.push (.process a) |>.push (.process f)
      | .lam name bi ty body _ =>
        stack := stack.push (.cacheAt e.info.metaAddr) |>.push (.lamDone name bi mdata)
          |>.push (.process body) |>.push (.process ty)
      | .all name bi ty body _ =>
        stack := stack.push (.cacheAt e.info.metaAddr) |>.push (.allDone name bi mdata)
          |>.push (.process body) |>.push (.process ty)
      | .letE name ty val body nd _ =>
        stack := stack.push (.cacheAt e.info.metaAddr) |>.push (.letDone name nd mdata)
          |>.push (.process body) |>.push (.process val)
          |>.push (.process ty)
      | .prj id field val _ =>
        stack := stack.push (.cacheAt e.info.metaAddr)
          |>.push (.prjDone id.name field mdata) |>.push (.process val)
      | .nat n _ _ =>
        let out := applyMDataLayers mdata (Ix.Expr.mkLit (.natVal n))
        values := values.push out
        cache := cache.insert e.info.metaAddr out
      | .str s _ _ =>
        let out := applyMDataLayers mdata (Ix.Expr.mkLit (.strVal s))
        values := values.push out
        cache := cache.insert e.info.metaAddr out
    | .appDone mdata =>
      let a := values.back!; values := values.pop
      let f := values.back!; values := values.pop
      values := values.push (applyMDataLayers mdata (Ix.Expr.mkApp f a))
    | .lamDone name bi mdata =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push
        (applyMDataLayers mdata (Ix.Expr.mkLam name ty body bi))
    | .allDone name bi mdata =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push
        (applyMDataLayers mdata (Ix.Expr.mkForallE name ty body bi))
    | .letDone name nd mdata =>
      let body := values.back!; values := values.pop
      let val := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push
        (applyMDataLayers mdata (Ix.Expr.mkLetE name ty val body nd))
    | .prjDone name field mdata =>
      let val := values.back!; values := values.pop
      values := values.push
        (applyMDataLayers mdata (Ix.Expr.mkProj name field.toNat val))
    | .cacheAt addr =>
      cache := cache.insert addr values.back!
  match values.back? with
  | some v =>
    if values.size != 1 then
      throw s!"egressExpr: unbalanced value stack ({values.size} values)"
    return (v, cache)
  | none => throw "egressExpr: empty result stack"

/-! ### Constant egress -/

/-- Convert a kernel constant to an `Ix.ConstantInfo` (Rust
    `egress_constant`). -/
def egressConstant (kc : KConst .«meta») : Except IngressErr Ix.ConstantInfo := do
  match kc with
  | .defn name levelParams kind safety hints _ ty val leanAll _ =>
    let (etype, cache) ← egressExpr levelParams {} ty
    let (evalue, _) ← egressExpr levelParams cache val
    let cnst : Ix.ConstantVal := { name, levelParams, type := etype }
    let all := leanAll.map (·.name)
    match kind with
    | .defn => return .defnInfo { cnst, value := evalue, hints, safety := safetyToLean safety, all }
    | .thm => return .thmInfo { cnst, value := evalue, all }
    | .opaq =>
      return .opaqueInfo { cnst, value := evalue,
                           isUnsafe := safety == .unsaf, all }
  | .axio name levelParams isUnsafe _ ty =>
    let (etype, _) ← egressExpr levelParams {} ty
    return .axiomInfo { cnst := { name, levelParams, type := etype }, isUnsafe }
  | .quot name levelParams kind _ ty =>
    let (etype, _) ← egressExpr levelParams {} ty
    return .quotInfo
      { cnst := { name, levelParams, type := etype }, kind := quotKindToLean kind }
  | .indc name levelParams _ params indices isUnsafe _ _ ty ctors leanAll =>
    let (etype, _) ← egressExpr levelParams {} ty
    return .inductInfo {
      cnst := { name, levelParams, type := etype }
      numParams := params.toNat, numIndices := indices.toNat
      all := leanAll.map (·.name), ctors := ctors.map (·.name)
      isUnsafe
      -- Stage-2 stubs (Rust recomputes in `lean_egress`; the roundtrip
      -- comparison never reads these).
      numNested := 0, isRec := false, isReflexive := false }
  | .ctor name levelParams isUnsafe _ induct cidx params fields ty =>
    let (etype, _) ← egressExpr levelParams {} ty
    return .ctorInfo {
      cnst := { name, levelParams, type := etype }
      induct := induct.name, cidx := cidx.toNat
      numParams := params.toNat, numFields := fields.toNat, isUnsafe }
  | .recr name levelParams k isUnsafe _ params indices motives minors _ _ ty
      rules leanAll =>
    let (etype, cache) ← egressExpr levelParams {} ty
    let mut cache := cache
    let mut erules : Array Ix.RecursorRule := Array.mkEmpty rules.size
    for r in rules do
      let (rhs, cache') ← egressExpr levelParams cache r.rhs
      cache := cache'
      erules := erules.push
        { ctor := r.ctor, nfields := r.fields.toNat, rhs }
    return .recInfo {
      cnst := { name, levelParams, type := etype }
      all := leanAll.map (·.name)
      numParams := params.toNat, numIndices := indices.toNat
      numMotives := motives.toNat, numMinors := minors.toNat
      rules := erules, k, isUnsafe }

/-! ### Comparator (Rust `compare_envs` / `find_diff` semantics) -/

/-- Walk two `Ix.Expr`s to the first structural divergence, returning a
    short path description (iterative; mirrors `find_diff`'s role as a
    failure-message generator). -/
def findDiff (a b : Ix.Expr) : String := Id.run do
  let kindOf : Ix.Expr → String
    | .bvar .. => "bvar" | .fvar .. => "fvar" | .mvar .. => "mvar"
    | .sort .. => "sort" | .const .. => "const" | .app .. => "app"
    | .lam .. => "lam" | .forallE .. => "forallE" | .letE .. => "letE"
    | .lit .. => "lit" | .mdata .. => "mdata" | .proj .. => "proj"
  let mut stack : Array (Ix.Expr × Ix.Expr × String) := #[(a, b, "")]
  let mut steps := 0
  while !stack.isEmpty && steps < 100000 do
    steps := steps + 1
    let (x, y, path) := stack.back!
    stack := stack.pop
    if x.getHash == y.getHash then
      continue
    match x, y with
    | .app f1 a1 _, .app f2 a2 _ =>
      stack := stack.push (a1, a2, path ++ ".arg")
        |>.push (f1, f2, path ++ ".fn")
    | .lam n1 t1 b1 bi1 _, .lam n2 t2 b2 bi2 _ =>
      if n1 != n2 then
        return s!"{path}: lam binder name '{n1}' vs '{n2}'"
      if bi1 != bi2 then
        return s!"{path}: lam binder info differs"
      stack := stack.push (b1, b2, path ++ ".body")
        |>.push (t1, t2, path ++ ".ty")
    | .forallE n1 t1 b1 bi1 _, .forallE n2 t2 b2 bi2 _ =>
      if n1 != n2 then
        return s!"{path}: forall binder name '{n1}' vs '{n2}'"
      if bi1 != bi2 then
        return s!"{path}: forall binder info differs"
      stack := stack.push (b1, b2, path ++ ".body")
        |>.push (t1, t2, path ++ ".ty")
    | .letE n1 t1 v1 b1 nd1 _, .letE n2 t2 v2 b2 nd2 _ =>
      if n1 != n2 then
        return s!"{path}: let binder name '{n1}' vs '{n2}'"
      if nd1 != nd2 then
        return s!"{path}: let nonDep {nd1} vs {nd2}"
      stack := stack.push (b1, b2, path ++ ".body")
        |>.push (v1, v2, path ++ ".val") |>.push (t1, t2, path ++ ".ty")
    | .mdata m1 e1 _, .mdata m2 e2 _ =>
      if m1 != m2 then
        return s!"{path}: mdata payload differs"
      stack := stack.push (e1, e2, path ++ ".mdata")
    | .proj n1 i1 e1 _, .proj n2 i2 e2 _ =>
      if n1 != n2 || i1 != i2 then
        return s!"{path}: proj head '{n1}'.{i1} vs '{n2}'.{i2}"
      stack := stack.push (e1, e2, path ++ ".proj")
    | .const n1 us1 _, .const n2 us2 _ =>
      if n1 != n2 then
        return s!"{path}: const '{n1}' vs '{n2}'"
      if us1.size != us2.size then
        return s!"{path}: const '{n1}' level count {us1.size} vs {us2.size}"
      return s!"{path}: const '{n1}' levels differ"
    | .sort u1 _, .sort u2 _ =>
      let _ := u1; let _ := u2
      return s!"{path}: sort levels differ"
    | x, y =>
      return s!"{path}: {kindOf x} vs {kindOf y}"
  return "(no structural divergence found — hash-only difference?)"

/-- Compare the canonicalized original against the kernel-egressed
    constant with `compare_envs` semantics: type hash always; value hash
    for defn/thm/opaque; per-rule RHS hashes for recursors. `none` = match. -/
def compareLeanCI (original egressed : Ix.ConstantInfo) : Option String := Id.run do
  let oc := original.getCnst
  let ec := egressed.getCnst
  if oc.type.getHash != ec.type.getHash then
    return some s!"type mismatch: {findDiff oc.type ec.type}"
  let valOf : Ix.ConstantInfo → Option Ix.Expr
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | .opaqueInfo v => some v.value
    | _ => none
  match valOf original, valOf egressed with
  | some ov, some ev =>
    if ov.getHash != ev.getHash then
      return some s!"value mismatch: {findDiff ov ev}"
  | some _, none => return some "value present in original only"
  | none, some _ => return some "value present in egressed only"
  | none, none => pure ()
  match original, egressed with
  | .recInfo ov, .recInfo ev =>
    if ov.rules.size != ev.rules.size then
      return some s!"rule count {ov.rules.size} vs {ev.rules.size}"
    for h : i in [0:ov.rules.size] do
      let orr := ov.rules[i]
      let some err := ev.rules[i]?
        | return some s!"rule {i} missing in egressed"
      if orr.rhs.getHash != err.rhs.getHash then
        return some s!"rule {i} ({orr.ctor}) rhs mismatch: \
                       {findDiff orr.rhs err.rhs}"
  | .recInfo _, other =>
    return some s!"kind mismatch: recursor vs {reprStr other |>.take 30}"
  | _, _ => pure ()
  return none

end Ix.Tc

end
end
