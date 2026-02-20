/-
  Kernel DecompileM: Kernel.Expr/ConstantInfo → Lean.Expr/ConstantInfo decompilation.

  Used for roundtrip validation: Lean.Environment → Ixon.Env → Kernel.Env → Lean.ConstantInfo.
  Comparing the roundtripped Lean.ConstantInfo against the original catches conversion bugs.
-/
import Ix.Kernel.Types

namespace Ix.Kernel.Decompile

/-! ## Name conversion -/

/-- Convert Ix.Name to Lean.Name by stripping embedded hashes. -/
def ixNameToLean : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str parent s _ => .str (ixNameToLean parent) s
  | .num parent n _ => .num (ixNameToLean parent) n

/-! ## Level conversion -/

/-- Convert a Kernel.Level back to Lean.Level.
    Level param names are synthetic (`u_0`, `u_1`, ...) since Convert.lean
    stores `default` for both param names and levelParams. -/
partial def decompileLevel (levelParams : Array Ix.Name) : Level .meta → Lean.Level
  | .zero => .zero
  | .succ l => .succ (decompileLevel levelParams l)
  | .max l₁ l₂ => .max (decompileLevel levelParams l₁) (decompileLevel levelParams l₂)
  | .imax l₁ l₂ => .imax (decompileLevel levelParams l₁) (decompileLevel levelParams l₂)
  | .param idx name =>
    let ixName := if name != default then name
      else if h : idx < levelParams.size then levelParams[idx]
      else Ix.Name.mkStr Ix.Name.mkAnon s!"u_{idx}"
    .param (ixNameToLean ixName)

/-! ## Expression conversion -/

@[inline] def kernelExprPtr (e : Expr .meta) : USize := unsafe ptrAddrUnsafe e

/-- Convert a Kernel.Expr back to Lean.Expr with pointer-based caching.
    Known lossy fields:
    - `letE.nonDep` is always `true` (lost in Kernel conversion)
    - Binder names/info come from metadata (may be `default` if missing) -/
partial def decompileExprCached (levelParams : Array Ix.Name) (e : Expr .meta)
    : StateM (Std.HashMap USize Lean.Expr) Lean.Expr := do
  let ptr := kernelExprPtr e
  if let some cached := (← get).get? ptr then return cached
  let result ← match e with
    | .bvar idx _ => pure (.bvar idx)
    | .sort lvl => pure (.sort (decompileLevel levelParams lvl))
    | .const _addr levels name =>
      pure (.const (ixNameToLean name) (levels.toList.map (decompileLevel levelParams)))
    | .app fn arg => do
      let f ← decompileExprCached levelParams fn
      let a ← decompileExprCached levelParams arg
      pure (.app f a)
    | .lam ty body name bi => do
      let t ← decompileExprCached levelParams ty
      let b ← decompileExprCached levelParams body
      pure (.lam (ixNameToLean name) t b bi)
    | .forallE ty body name bi => do
      let t ← decompileExprCached levelParams ty
      let b ← decompileExprCached levelParams body
      pure (.forallE (ixNameToLean name) t b bi)
    | .letE ty val body name => do
      let t ← decompileExprCached levelParams ty
      let v ← decompileExprCached levelParams val
      let b ← decompileExprCached levelParams body
      pure (.letE (ixNameToLean name) t v b true)
    | .lit lit => pure (.lit lit)
    | .proj _typeAddr idx struct typeName => do
      let s ← decompileExprCached levelParams struct
      pure (.proj (ixNameToLean typeName) idx s)
  modify (·.insert ptr result)
  pure result

def decompileExpr (levelParams : Array Ix.Name) (e : Expr .meta) : Lean.Expr :=
  (decompileExprCached levelParams e |>.run {}).1

/-! ## ConstantInfo conversion -/

/-- Convert Kernel.DefinitionSafety to Lean.DefinitionSafety. -/
def decompileSafety : DefinitionSafety → Lean.DefinitionSafety
  | .safe => .safe
  | .unsafe => .unsafe
  | .partial => .partial

/-- Convert Kernel.ReducibilityHints to Lean.ReducibilityHints. -/
def decompileHints : ReducibilityHints → Lean.ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h

/-- Synthetic level params: `[u_0, u_1, ..., u_{n-1}]`. -/
def syntheticLevelParams (n : Nat) : List Lean.Name :=
  (List.range n).map fun i => .str .anonymous s!"u_{i}"

/-- Convert a Kernel.ConstantInfo (.meta) back to Lean.ConstantInfo.
    Name fields are resolved directly from the MetaField name fields
    on the sub-structures (allNames, ctorNames, inductName, ctorName). -/
def decompileConstantInfo (ci : ConstantInfo .meta) : Lean.ConstantInfo :=
  let cv := ci.cv
  let lps := syntheticLevelParams cv.numLevels
  let lpArr := cv.levelParams  -- Array Ix.Name
  let decompTy := decompileExpr lpArr cv.type
  let decompVal (e : Expr .meta) := decompileExpr lpArr e
  let name := ixNameToLean cv.name
  match ci with
  | .axiomInfo v =>
    .axiomInfo {
      name, levelParams := lps, type := decompTy, isUnsafe := v.isUnsafe
    }
  | .defnInfo v =>
    .defnInfo {
      name, levelParams := lps, type := decompTy
      value := decompVal v.value
      hints := decompileHints v.hints
      safety := decompileSafety v.safety
    }
  | .thmInfo v =>
    .thmInfo {
      name, levelParams := lps, type := decompTy
      value := decompVal v.value
    }
  | .opaqueInfo v =>
    .opaqueInfo {
      name, levelParams := lps, type := decompTy
      value := decompVal v.value, isUnsafe := v.isUnsafe
    }
  | .quotInfo v =>
    let leanKind : Lean.QuotKind := match v.kind with
      | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind
    .quotInfo {
      name, levelParams := lps, type := decompTy, kind := leanKind
    }
  | .inductInfo v =>
    .inductInfo {
      name, levelParams := lps, type := decompTy
      numParams := v.numParams, numIndices := v.numIndices
      isRec := v.isRec, isUnsafe := v.isUnsafe, isReflexive := v.isReflexive
      all := v.allNames.toList.map ixNameToLean
      ctors := v.ctorNames.toList.map ixNameToLean
      numNested := v.numNested
    }
  | .ctorInfo v =>
    .ctorInfo {
      name, levelParams := lps, type := decompTy
      induct := ixNameToLean v.inductName
      cidx := v.cidx, numParams := v.numParams, numFields := v.numFields
      isUnsafe := v.isUnsafe
    }
  | .recInfo v =>
    .recInfo {
      name, levelParams := lps, type := decompTy
      all := v.allNames.toList.map ixNameToLean
      numParams := v.numParams, numIndices := v.numIndices
      numMotives := v.numMotives, numMinors := v.numMinors
      k := v.k, isUnsafe := v.isUnsafe
      rules := v.rules.toList.map fun r => {
        ctor := ixNameToLean r.ctorName
        nfields := r.nfields
        rhs := decompVal r.rhs
      }
    }

/-! ## Structural comparison -/

@[inline] def leanExprPtr (e : Lean.Expr) : USize := unsafe ptrAddrUnsafe e

structure ExprPtrPair where
  a : USize
  b : USize
  deriving Hashable, BEq

/-- Compare two Lean.Exprs structurally, ignoring binder names and binder info.
    Uses pointer-pair caching to avoid exponential blowup on shared subexpressions.
    Returns `none` if structurally equal, `some (path, lhs, rhs)` on first mismatch. -/
partial def exprStructEq (a b : Lean.Expr) (path : String := "")
    : StateM (Std.HashSet ExprPtrPair) (Option (String × String × String)) := do
  let ptrA := leanExprPtr a
  let ptrB := leanExprPtr b
  if ptrA == ptrB then return none
  let pair := ExprPtrPair.mk ptrA ptrB
  if (← get).contains pair then return none
  let result ← match a, b with
  | .bvar i, .bvar j =>
    pure (if i == j then none else some (path, s!"bvar({i})", s!"bvar({j})"))
  | .sort l₁, .sort l₂ =>
    pure (if Lean.Level.isEquiv l₁ l₂ then none else some (path, s!"sort", s!"sort"))
  | .const n₁ ls₁, .const n₂ ls₂ =>
    pure (if n₁ != n₂ then some (path, s!"const({n₁})", s!"const({n₂})")
    else if ls₁.length != ls₂.length then
      some (path, s!"const({n₁}) {ls₁.length} lvls", s!"const({n₂}) {ls₂.length} lvls")
    else none)
  | .app f₁ a₁, .app f₂ a₂ => do
    match ← exprStructEq f₁ f₂ (path ++ ".app.fn") with
    | some m => pure (some m)
    | none => exprStructEq a₁ a₂ (path ++ ".app.arg")
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ => do
    match ← exprStructEq t₁ t₂ (path ++ ".lam.ty") with
    | some m => pure (some m)
    | none => exprStructEq b₁ b₂ (path ++ ".lam.body")
  | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ => do
    match ← exprStructEq t₁ t₂ (path ++ ".pi.ty") with
    | some m => pure (some m)
    | none => exprStructEq b₁ b₂ (path ++ ".pi.body")
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => do
    match ← exprStructEq t₁ t₂ (path ++ ".let.ty") with
    | some m => pure (some m)
    | none => match ← exprStructEq v₁ v₂ (path ++ ".let.val") with
      | some m => pure (some m)
      | none => exprStructEq b₁ b₂ (path ++ ".let.body")
  | .lit l₁, .lit l₂ =>
    pure (if l₁ == l₂ then none
    else
      let showLit : Lean.Literal → String
        | .natVal n => s!"natLit({n})"
        | .strVal s => s!"strLit({s})"
      some (path, showLit l₁, showLit l₂))
  | .proj t₁ i₁ s₁, .proj t₂ i₂ s₂ =>
    if t₁ != t₂ then pure (some (path, s!"proj({t₁}.{i₁})", s!"proj({t₂}.{i₂})"))
    else if i₁ != i₂ then pure (some (path, s!"proj.idx({i₁})", s!"proj.idx({i₂})"))
    else exprStructEq s₁ s₂ (path ++ ".proj.struct")
  | .mdata _ e₁, _ => exprStructEq e₁ b path
  | _, .mdata _ e₂ => exprStructEq a e₂ path
  | _, _ =>
    let tag (e : Lean.Expr) : String := match e with
      | .bvar _ => "bvar" | .sort _ => "sort" | .const .. => "const"
      | .app .. => "app" | .lam .. => "lam" | .forallE .. => "forallE"
      | .letE .. => "letE" | .lit .. => "lit" | .proj .. => "proj"
      | .fvar .. => "fvar" | .mvar .. => "mvar" | .mdata .. => "mdata"
    pure (some (path, tag a, tag b))
  if result.isNone then modify (·.insert pair)
  pure result

/-- Compare two Lean.ConstantInfos structurally. Returns list of mismatches. -/
def constInfoStructEq (a b : Lean.ConstantInfo)
    : Array (String × String × String) :=
  let check : StateM (Std.HashSet ExprPtrPair) (Array (String × String × String)) := do
    let mut mismatches : Array (String × String × String) := #[]
    -- Compare types
    if let some m ← exprStructEq a.type b.type "type" then
      mismatches := mismatches.push m
    -- Compare values if both have them
    match a.value?, b.value? with
    | some va, some vb =>
      if let some m ← exprStructEq va vb "value" then
        mismatches := mismatches.push m
    | none, some _ => mismatches := mismatches.push ("value", "none", "some")
    | some _, none => mismatches := mismatches.push ("value", "some", "none")
    | none, none => pure ()
    return mismatches
  (check.run {}).1

end Ix.Kernel.Decompile
