import Ix.CanonM
import Ix.LeanIngress
import Ix.CompileCert.CanonUnivScope

/-! # The `CanonM` correspondence

`Ix.CanonM` turns Lean's terms into `Ix.Expr`s. Its output is the input of
both `Ix.Cert.compile` and Source mode (`Ix.LeanIngress`), so the
certification statements (`Ix.Cert.Statement`) are about an
`Ix.Environment`. This file states what ties that environment to Lean's. It
is an interpretation bridge, not a step of `CompileCorrect`'s proof: both
sides of `CompileCorrect` read the same `Ix.Environment`.

1. **The specification** (`nameS`, `levelS`, `syntaxS`, `exprS`, `constS`):
   the structural conversion, with the same smart constructors (so the same
   hash fields) and no cache.
2. **`CanonMCorrect`, C1: stated, not proved.** `canonName`, `canonLevel`,
   `canonExpr` and `canonConst` compute the specification from every state
   they reach (`CanonChunkCorrect`: so does `canonChunk`). It is *not
   provable for today's `Ix.CanonM`*. A pointer-cache hit is keyed by
   `ptrAddrUnsafe`, which is opaque in the logic, and a hash-cache hit is
   keyed by the stored BLAKE3 field. Neither hit is confirmed against its
   input, and `canonSyntax` is `partial`. It becomes provable once every hit
   is confirmed, as `Ix.LeanIngress.ingressExprsShared` confirms its memo
   (compiler queue CQ2.26). Only `ingressExpr_canonExpr` uses it, as a
   hypothesis.
3. **The Source reading** (`leanExpr`; proved: `ingressExpr_exprS`):
   Source mode's reading of the specification's term is a direct structural
   function of Lean's term. It reads no hash and no cache, under the
   numbering `σ ∘ nameS`.
4. **The numbering** (`numbering_nameS`, proved under `HashEqAgrees`):
   `Numbering.pos` compares `Ix.Name`s by their hash fields, so it equals
   the direct numbering only where that comparison agrees with name
   equality on the constant's level-parameter names. A structural
   comparison in `Numbering.pos` removes the premise (CQ2.25).
5. **Universes** (`universeBridge`, proved under `HashEqAgrees`). Ixon's
   reading of the canonical compiled universe of `levelS l` has the value of
   Lean's level `l`, read directly. It composes CT-12's
   `Ix.CompileCert.CanonUnivScope.convCanon_eval` (`universe_bridge`) with
   `UnivMeaningS` (proved: `univMeaningS`), the pure half of CQ2.8's
   `UniverseMeaning`, about `compileUnivS`: the cache-free universe
   compiler, which stands in for `compileUniv`. That `compileUniv` computes
   it is CQ2.8's exact-key work.
-/

namespace Ix.Cert.Canon

open Ix.Kernel (LevelParam)
open Ix.LeanIngress (ExprError KExpr KLevel)

/-! ## 1. The specification of `Ix.CanonM` -/

/-- `canonName` without its caches. -/
def nameS : Lean.Name → Ix.Name
  | .anonymous => .mkAnon
  | .str p s => .mkStr (nameS p) s
  | .num p n => .mkNat (nameS p) n

/-- `canonLevel` without its caches. -/
def levelS : Lean.Level → Ix.Level
  | .zero => .mkZero
  | .succ u => .mkSucc (levelS u)
  | .max u v => .mkMax (levelS u) (levelS v)
  | .imax u v => .mkIMax (levelS u) (levelS v)
  | .param n => .mkParam (nameS n)
  | .mvar m => .mkMvar (nameS m.name)

def preresolvedS : Lean.Syntax.Preresolved → Ix.SyntaxPreresolved
  | .namespace n => .namespace (nameS n)
  | .decl n aliases => .decl (nameS n) aliases.toArray

/-- `canonSyntax` (a `partial def` in `Ix.CanonM`), as a total function. -/
def syntaxS : Lean.Syntax → Ix.Syntax
  | .missing => .missing
  | .node info kind args =>
    .node (Ix.CanonM.canonSourceInfo info) (nameS kind) (args.map syntaxS)
  | .atom info val => .atom (Ix.CanonM.canonSourceInfo info) val
  | .ident info rawVal val pre =>
    .ident (Ix.CanonM.canonSourceInfo info) (Ix.CanonM.canonSubstring rawVal) (nameS val)
      (pre.toArray.map preresolvedS)

def dataValueS : Lean.DataValue → Ix.DataValue
  | .ofString s => .ofString s
  | .ofBool b => .ofBool b
  | .ofName n => .ofName (nameS n)
  | .ofNat n => .ofNat n
  | .ofInt i => .ofInt (Ix.CanonM.canonInt i)
  | .ofSyntax s => .ofSyntax (syntaxS s)

/-- `canonMData` without its caches: the entries in order. -/
def mdataS (d : Lean.MData) : Array (Ix.Name × Ix.DataValue) :=
  (d.entries.map fun (n, v) => (nameS n, dataValueS v)).toArray

/-- `canonExpr` without its caches. -/
def exprS : Lean.Expr → Ix.Expr
  | .bvar i => .mkBVar i
  | .fvar x => .mkFVar (nameS x.name)
  | .mvar x => .mkMVar (nameS x.name)
  | .sort u => .mkSort (levelS u)
  | .const n us => .mkConst (nameS n) (us.map levelS).toArray
  | .app f a => .mkApp (exprS f) (exprS a)
  | .lam n t b bi => .mkLam (nameS n) (exprS t) (exprS b) bi
  | .forallE n t b bi => .mkForallE (nameS n) (exprS t) (exprS b) bi
  | .letE n t v b nd => .mkLetE (nameS n) (exprS t) (exprS v) (exprS b) nd
  | .lit l => .mkLit l
  | .mdata d e => .mkMData (mdataS d) (exprS e)
  | .proj s i e => .mkProj (nameS s) i (exprS e)

def constValS (cv : Lean.ConstantVal) : Ix.ConstantVal :=
  { name := nameS cv.name, levelParams := (cv.levelParams.map nameS).toArray, type := exprS cv.type }

/-- `canonConst` without its caches. -/
def constS : Lean.ConstantInfo → Ix.ConstantInfo
  | .axiomInfo v => .axiomInfo { cnst := constValS v.toConstantVal, isUnsafe := v.isUnsafe }
  | .defnInfo v => .defnInfo
      { cnst := constValS v.toConstantVal, value := exprS v.value, hints := v.hints,
        safety := v.safety, all := (v.all.map nameS).toArray }
  | .thmInfo v => .thmInfo
      { cnst := constValS v.toConstantVal, value := exprS v.value, all := (v.all.map nameS).toArray }
  | .opaqueInfo v => .opaqueInfo
      { cnst := constValS v.toConstantVal, value := exprS v.value, isUnsafe := v.isUnsafe,
        all := (v.all.map nameS).toArray }
  | .quotInfo v => .quotInfo { cnst := constValS v.toConstantVal, kind := v.kind }
  | .inductInfo v => .inductInfo
      { cnst := constValS v.toConstantVal, numParams := v.numParams, numIndices := v.numIndices,
        all := (v.all.map nameS).toArray, ctors := (v.ctors.map nameS).toArray,
        numNested := v.numNested, isRec := v.isRec, isUnsafe := v.isUnsafe,
        isReflexive := v.isReflexive }
  | .ctorInfo v => .ctorInfo
      { cnst := constValS v.toConstantVal, induct := nameS v.induct, cidx := v.cidx,
        numParams := v.numParams, numFields := v.numFields, isUnsafe := v.isUnsafe }
  | .recInfo v => .recInfo
      { cnst := constValS v.toConstantVal, all := (v.all.map nameS).toArray,
        numParams := v.numParams, numIndices := v.numIndices, numMotives := v.numMotives,
        numMinors := v.numMinors,
        rules := (v.rules.map fun r => { ctor := nameS r.ctor, nfields := r.nfields, rhs := exprS r.rhs }).toArray,
        k := v.k, isUnsafe := v.isUnsafe }

/-! ## 2. `CanonM` computes the specification (C1: stated, not proved)

These are statements (`def … : Prop`), not theorems, and nothing proves them:
they are unprovable for today's `Ix.CanonM` (the module docstring, item 2).
The fix that makes them provable is CQ2.26. -/

section Production
open Ix.CanonM

/-- The states `Ix.CanonM` reaches from the empty state through any sequence
of its conversions. `canonChunk`, `canonEnv` and the compile driver's
streamed canon (`Ix.CompileDriver`) thread one state through many
constants. -/
inductive Reachable : CanonState → Prop
  | empty : Reachable {}
  | name {s : CanonState} (n : Lean.Name) : Reachable s → Reachable (Id.run ((canonName n).run s)).2
  | level {s : CanonState} (l : Lean.Level) : Reachable s → Reachable (Id.run ((canonLevel l).run s)).2
  | expr {s : CanonState} (e : Lean.Expr) : Reachable s → Reachable (Id.run ((canonExpr e).run s)).2
  | const {s : CanonState} (c : Lean.ConstantInfo) : Reachable s →
      Reachable (Id.run ((canonConst c).run s)).2

/-- **The CanonM correspondence, computational half (C1, stated only).**
From every reachable state, the conversions return the specification.
Unprovable for today's `Ix.CanonM`. Its caches answer a hit with the value stored under
`ptrAddrUnsafe` of the input (opaque, so not injective in the logic), or
under the stored BLAKE3 field (not injective), without comparing.
`canonSyntax` is also `partial`. -/
def CanonMCorrect : Prop :=
  ∀ s, Reachable s →
    (∀ n, (Id.run ((canonName n).run s)).1 = nameS n) ∧
    (∀ l, (Id.run ((canonLevel l).run s)).1 = levelS l) ∧
    (∀ e, (Id.run ((canonExpr e).run s)).1 = exprS e) ∧
    (∀ c, (Id.run ((canonConst c).run s)).1 = constS c)

/-- What Source mode and the compile driver actually run: a chunk of
constants through one state. Stated only, like `CanonMCorrect`. -/
def CanonChunkCorrect : Prop :=
  ∀ chunk : Array (Lean.Name × Lean.ConstantInfo),
    canonChunk chunk = chunk.map fun (n, c) => (nameS n, constS c)

end Production

/-! ## 3. Source mode reads Lean's term directly -/

/-- Lean's name as the checker's name (what `ingressName` gives on
`nameS`). -/
def leanName : Lean.Name → Ix.Kernel.Name
  | .anonymous => .anonymous
  | .str p s => .str (leanName p) s
  | .num p n => .num (leanName p) n

def leanKey (n : Lean.Name) : Ix.Kernel.Key .source := Ix.Kernel.Key.ofName (leanName n)

def leanLevel (σ : Lean.Name → LevelParam) : Lean.Level → Except ExprError KLevel
  | .zero => pure .zero
  | .succ u => return .succ (← leanLevel σ u)
  | .max u v => return .max (← leanLevel σ u) (← leanLevel σ v)
  | .imax u v => return .imax (← leanLevel σ u) (← leanLevel σ v)
  | .param n => pure (.param (σ n))
  | .mvar m => throw (.levelMVar (leanName m.name))

/-- `Ix.SemanticContract.hasMetadata`, on Lean's metadata. -/
def hasContractLean (d : Lean.MData) : Bool :=
  d.entries.any fun (n, _) => Ix.SemanticContract.key.isPrefixOf n

/-- `Ix.SemanticContract.read`, on Lean's metadata. -/
def readContractLean (md : Lean.MData) : Except String Ix.SemanticContract.Contract := do
  let data := md.entries.toArray
  if data.size != 3 then throw "malformed semantic contract frame"
  let mut version : Option Nat := none
  let mut kind : Option Nat := none
  let mut code : Option Nat := none
  for (name, value) in data do
    -- `dataValueS v` is `.ofNat k` exactly when `v` is `.ofNat k`
    let .ofNat value := dataValueS value | throw "semantic contract fields must be natural numbers"
    if name == Ix.SemanticContract.key && version.isNone then version := some value
    else if name == `ix.contract.kind && kind.isNone then kind := some value
    else if name == `ix.contract.code && code.isNone then code := some value
    else throw "unknown or duplicate semantic contract field"
  unless version == some 3 do throw "unsupported semantic contract version"
  let some kindValue := kind | throw "missing semantic contract kind"
  let some codeValue := code | throw "missing semantic contract code"
  Ix.SemanticContract.decode kindValue codeValue

/-- `Ix.LeanIngress.withContract`, on a Lean binder. -/
def withContractLean (c : Ix.SemanticContract.Contract) (e : Lean.Expr) (x : KExpr) :
    Except ExprError KExpr :=
  match c.kind, e, x with
  | .lam, .lam .., .lam t b m => pure (.lam t b { m with contract := c.binder })
  | .all, .forallE .., .forallE t b m =>
    pure (.forallE t b { m with contract := c.binder, result := c.result })
  | .letE, .letE .., .letE t v b l =>
    pure (.letE t v b { contract := { l.contract with binder := c.binder, kind := c.letKind } })
  | _, _, _ => throw (.contract "semantic contract is not attached to its original binder")

def leanMData (d : Lean.MData) (e : Lean.Expr) (x : Except ExprError KExpr) :
    Except ExprError KExpr :=
  if hasContractLean d then do
    let c ← (readContractLean d).mapError .contract
    withContractLean c e (← x)
  else x

/-- **Lean's term as Source mode's term**, read directly: no hash, no cache,
no `Ix.Expr`. -/
def leanExpr (σ : Lean.Name → LevelParam) : Lean.Expr → Except ExprError KExpr
  | .bvar i => pure (Ix.Kernel.Expr.mkBvar i)
  | .fvar x => throw (.fvar (leanName x.name))
  | .mvar x => throw (.mvar (leanName x.name))
  | .sort u => return .sort (← leanLevel σ u)
  | .const n us => return .const (leanKey n) (← us.mapM (leanLevel σ))
  | .app f a => return .app (← leanExpr σ f) (← leanExpr σ a)
  | .lam _ t b _ => return .lam (← leanExpr σ t) (← leanExpr σ b) { pw := .never }
  | .forallE _ t b _ => return .forallE (← leanExpr σ t) (← leanExpr σ b) { pw := .never }
  | .letE _ t v b nd =>
    return .letE (← leanExpr σ t) (← leanExpr σ v) (← leanExpr σ b) { contract := .lean nd }
  | .lit (.natVal n) => pure (.lit (.natVal n))
  | .lit (.strVal s) => pure (.lit (.strVal s))
  | .mdata d e => leanMData d e (leanExpr σ e)
  | .proj s i e => return .proj (leanKey s) i (← leanExpr σ e)

/-! ### Proofs -/

theorem ingressName_nameS (n : Lean.Name) : Ix.LeanIngress.ingressName (nameS n) = leanName n := by
  induction n with
  | anonymous => rfl
  | str p s ih =>
    simp only [nameS, leanName, Ix.Name.mkStr, Id.run, Ix.LeanIngress.ingressName, ih]
  | num p k ih =>
    simp only [nameS, leanName, Ix.Name.mkNat, Id.run, Ix.LeanIngress.ingressName, ih]

theorem ingressKey_nameS (n : Lean.Name) : Ix.LeanIngress.ingressKey (nameS n) = leanKey n := by
  simp only [Ix.LeanIngress.ingressKey, leanKey, ingressName_nameS]

theorem toLeanName_nameS (n : Lean.Name) : Ix.SemanticContract.toLeanName (nameS n) = n := by
  induction n with
  | anonymous => rfl
  | str p s ih =>
    simp only [nameS, Ix.Name.mkStr, Id.run, Ix.SemanticContract.toLeanName, ih]
  | num p k ih =>
    simp only [nameS, Ix.Name.mkNat, Id.run, Ix.SemanticContract.toLeanName, ih]

theorem ingressLevel_levelS (σ : Ix.Name → LevelParam) (l : Lean.Level) :
    Ix.LeanIngress.ingressLevel σ (levelS l) = leanLevel (σ ∘ nameS) l := by
  induction l with
  | zero => rfl
  | succ u ih =>
    simp only [levelS, leanLevel, Ix.Level.mkSucc, Id.run, Ix.LeanIngress.ingressLevel, ih]
  | max u v ihu ihv =>
    simp only [levelS, leanLevel, Ix.Level.mkMax, Id.run, Ix.LeanIngress.ingressLevel, ihu, ihv]
  | imax u v ihu ihv =>
    simp only [levelS, leanLevel, Ix.Level.mkIMax, Id.run, Ix.LeanIngress.ingressLevel, ihu, ihv]
  | param n =>
    simp only [levelS, leanLevel, Ix.Level.mkParam, Id.run, Ix.LeanIngress.ingressLevel,
      Function.comp_apply]
  | mvar m =>
    simp only [levelS, leanLevel, Ix.Level.mkMvar, Id.run, Ix.LeanIngress.ingressLevel,
      ingressName_nameS]

theorem levels_mapM (σ : Ix.Name → LevelParam) (us : List Lean.Level) :
    (us.map levelS).mapM (Ix.LeanIngress.ingressLevel σ) =
      us.mapM (leanLevel (σ ∘ nameS)) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [List.map_cons, List.mapM_cons, ingressLevel_levelS, ih]

theorem hasMetadata_mdataS (d : Lean.MData) :
    Ix.SemanticContract.hasMetadata (mdataS d) = hasContractLean d := by
  simp [Ix.SemanticContract.hasMetadata, mdataS, hasContractLean, Ix.SemanticContract.reserved,
    Function.comp_def, toLeanName_nameS]

theorem read_mdataS (d : Lean.MData) :
    Ix.SemanticContract.read (mdataS d) = readContractLean d := by
  unfold Ix.SemanticContract.read readContractLean mdataS
  simp only [List.size_toArray, List.length_map, List.forIn_toArray, List.forIn_map,
    toLeanName_nameS]
  rfl

/-- `Id`'s bind is application (the smart constructors hash in `Id`). -/
theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

theorem withContract_exprS (c : Ix.SemanticContract.Contract) (e : Lean.Expr) (x : KExpr) :
    Ix.LeanIngress.withContract c (exprS e) x = withContractLean c e x := by
  cases e
  case lit l =>
    cases l <;> cases hk : c.kind <;> cases x <;>
      simp [Ix.LeanIngress.withContract, withContractLean, exprS, hk, Id.run, Ix.Expr.mkLit]
  all_goals
    cases hk : c.kind <;> cases x <;>
      simp [Ix.LeanIngress.withContract, withContractLean, exprS, hk, Id.run, idBind,
        Ix.Expr.mkLam, Ix.Expr.mkForallE, Ix.Expr.mkLetE, Ix.Expr.mkBVar, Ix.Expr.mkFVar,
        Ix.Expr.mkMVar, Ix.Expr.mkSort, Ix.Expr.mkConst, Ix.Expr.mkApp, Ix.Expr.mkMData,
        Ix.Expr.mkProj]

/-- **The CanonM correspondence, Source half** (proved): Source mode's
reading of the specification's term is the direct reading of Lean's term,
under the numbering seen through `nameS`. -/
theorem ingressExpr_exprS (σ : Ix.Name → LevelParam) (e : Lean.Expr) :
    Ix.LeanIngress.ingressExpr σ (exprS e) = leanExpr (σ ∘ nameS) e := by
  induction e with
  | bvar i => rfl
  | fvar x =>
    simp only [exprS, leanExpr, Ix.Expr.mkFVar, Id.run, Ix.LeanIngress.ingressExpr,
      ingressName_nameS]
  | mvar x =>
    simp only [exprS, leanExpr, Ix.Expr.mkMVar, Id.run, Ix.LeanIngress.ingressExpr,
      ingressName_nameS]
  | sort u =>
    simp only [exprS, leanExpr, Ix.Expr.mkSort, Id.run, Ix.LeanIngress.ingressExpr,
      ingressLevel_levelS]
  | const n us =>
    simp only [exprS, leanExpr, Ix.Expr.mkConst, Id.run, idBind, Ix.LeanIngress.ingressExpr,
      ingressKey_nameS, levels_mapM]
  | app f a ihf iha =>
    simp only [exprS, leanExpr, Ix.Expr.mkApp, Id.run, Ix.LeanIngress.ingressExpr, ihf, iha]
  | lam n t b bi iht ihb =>
    simp only [exprS, leanExpr, Ix.Expr.mkLam, Id.run, Ix.LeanIngress.ingressExpr, iht, ihb]
  | forallE n t b bi iht ihb =>
    simp only [exprS, leanExpr, Ix.Expr.mkForallE, Id.run, Ix.LeanIngress.ingressExpr, iht, ihb]
  | letE n t v b nd iht ihv ihb =>
    simp only [exprS, leanExpr, Ix.Expr.mkLetE, Id.run, Ix.LeanIngress.ingressExpr, iht, ihv, ihb]
  | lit l => cases l <;> rfl
  | mdata d e ih =>
    simp only [exprS, leanExpr, Ix.Expr.mkMData, Id.run, idBind, Ix.LeanIngress.ingressExpr, ih,
      Ix.LeanIngress.ingressMData, leanMData, hasMetadata_mdataS, read_mdataS, withContract_exprS]
  | proj s i e ih =>
    simp only [exprS, leanExpr, Ix.Expr.mkProj, Id.run, Ix.LeanIngress.ingressExpr,
      ingressKey_nameS, ih]

/-- With the computational half, Source mode reads what `CanonM` produced as
Lean's own term. -/
theorem ingressExpr_canonExpr (hc : CanonMCorrect) {s : Ix.CanonM.CanonState}
    (hs : Reachable s) (σ : Ix.Name → LevelParam) (e : Lean.Expr) :
    Ix.LeanIngress.ingressExpr σ (Id.run ((Ix.CanonM.canonExpr e).run s)).1 =
      leanExpr (σ ∘ nameS) e := by
  rw [(hc s hs).2.2.1 e, ingressExpr_exprS]

/-! ## 4. The numbering -/

/-- `Numbering.pos`, over Lean's names (structural equality). -/
def leanPos (names : Array Lean.Name) (large : Bool) (n : Lean.Name) : LevelParam :=
  match names.findIdx? (· == n) with
  | none => names.size
  | some 0 => if large then names.size - 1 else 0
  | some (i + 1) => if large then i else i + 1

/-- On a constant's level-parameter names, `BEq Ix.Name` (which compares
hash fields only) agrees with name equality. A run-time check per constant
can establish it. It fails only on a BLAKE3 collision between name encodings. -/
def HashEqAgrees (names : Array Lean.Name) : Prop :=
  ∀ m ∈ names, ∀ n, (nameS m == nameS n) = (m == n)

theorem findIdx_nameS (l : List Lean.Name) (n : Lean.Name)
    (h : ∀ m ∈ l, (nameS m == nameS n) = (m == n)) :
    l.findIdx? ((· == nameS n) ∘ nameS) = l.findIdx? (· == n) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findIdx?_cons, List.findIdx?_cons, Function.comp_apply, h a (by simp),
      ih (fun m hm => h m (by simp [hm]))]

/-- **The numbering** (proved): Source mode's numbering of `CanonM`'s names
is the direct numbering of Lean's, wherever the hash comparison agrees with
name equality. A structural comparison in `Numbering.pos` would make this
unconditional. -/
theorem numbering_nameS (names : Array Lean.Name) (large : Bool) (h : HashEqAgrees names)
    (n : Lean.Name) :
    Ix.LeanIngress.Numbering.pos ⟨names.map nameS, large⟩ (nameS n) = leanPos names large n := by
  rcases names with ⟨l⟩
  have hl : ∀ m ∈ l, (nameS m == nameS n) = (m == n) := fun m hm => h m (by simpa using hm) n
  have key : (Array.map nameS ⟨l⟩).findIdx? (· == nameS n) = (⟨l⟩ : Array Lean.Name).findIdx? (· == n) := by
    rw [Array.findIdx?_map]
    simpa using findIdx_nameS l n hl
  simp only [Ix.LeanIngress.Numbering.pos, leanPos, Array.size_map]
  rw [key]
  rfl

/-! ## 5. Universes: composing with CT-12

The Ixon side is CT-12's: `Ix.CompileCert.univEval` is the value of a wire
universe, and `Ix.CompileCert.CanonUnivScope.convCanon_eval` says that the
certified reader's reading of a canonical universe has the raw universe's
value. -/

open Ix.CompileCert (univEval)

/-- `Ix.CompileM.compileUniv` without its cache, under the context `ctx` of
the constant's level-parameter names (positional, compared by `BEq Ix.Name`
as `compileUniv` compares them). That `compileUniv` computes it, from a
cache with exact keys, is CQ2.8's (`UniverseMeaning`/`UniverseExact`). -/
def compileUnivS (ctx : List Ix.Name) : Ix.Level → Option Ixon.Univ
  | .zero _ => some .zero
  | .succ l _ => (compileUnivS ctx l).map .succ
  | .max l r _ => do return .max (← compileUnivS ctx l) (← compileUnivS ctx r)
  | .imax l r _ => do return .imax (← compileUnivS ctx l) (← compileUnivS ctx r)
  | .param n _ => (ctx.idxOf? n).map fun i => .var i.toUInt64
  | .mvar _ _ => none

/-- The cache-free compile keeps the value that Source mode reads (a member's
own parameters, `large = false`): the pure half of CQ2.8's
`UniverseMeaning`, over `Ix.Level`. Proved below (`univMeaningS`), by a
structural induction: the parameter case is `idxOf? = findIdx? (· == n)`
under a `UInt64` bound. -/
def UnivMeaningS : Prop :=
  ∀ (ctx : Array Ix.Name), ctx.size < UInt64.size →
    ∀ (l : Ix.Level) (u : Ixon.Univ) (k : KLevel) (φ : LevelParam → Nat),
      compileUnivS ctx.toList l = some u →
      Ix.LeanIngress.ingressLevel (Ix.LeanIngress.Numbering.pos ⟨ctx, false⟩) l = .ok k →
      univEval (fun i => φ i.toNat) u = Ix.Kernel.Level.eval φ k

/-- **The universe bridge from Lean**: Ixon's reading of the canonical
compiled universe of a Lean level has the value of the level read directly
from Lean. Stated for a member's own parameters (`param = id`,
`large = false`). A large eliminator's (`recParam`) is the same with the
shifted numbering. -/
def UniverseBridge : Prop :=
  ∀ (ps : Array Lean.Name), ps.size < UInt64.size → HashEqAgrees ps →
    ∀ (l : Lean.Level) (u : Ixon.Univ) (k : KLevel) (φ : LevelParam → Nat),
      compileUnivS (ps.map nameS).toList (levelS l) = some u →
      leanLevel (leanPos ps false) l = .ok k →
      Ix.Kernel.Level.eval φ (Ix.Kernel.Reader.convUniv id (Ixon.canonUniv u)) =
        Ix.Kernel.Level.eval φ k

/-- **The composition** (proved): CT-12's `convCanon_eval` and the pure
universe meaning give the universe bridge from Lean, through
`ingressLevel_levelS` and `numbering_nameS`. -/
theorem universe_bridge (hmean : UnivMeaningS) : UniverseBridge := by
  intro ps hsize hagree l u k φ hc hk
  rw [Ix.CompileCert.CanonUnivScope.convCanon_eval id φ u]
  have hσ : (Ix.LeanIngress.Numbering.pos ⟨ps.map nameS, false⟩ ∘ nameS) = leanPos ps false :=
    funext fun n => numbering_nameS ps false hagree n
  have hk' : Ix.LeanIngress.ingressLevel (Ix.LeanIngress.Numbering.pos ⟨ps.map nameS, false⟩)
      (levelS l) = .ok k := by
    rw [ingressLevel_levelS, hσ]; exact hk
  exact hmean (ps.map nameS) (by simpa using hsize) (levelS l) u k φ hc hk'

/-! ### The pure universe meaning, proved -/

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `Numbering.pos` of a member's own parameters (`large = false`) is the
position `idxOf?` finds, as `compileUnivS` numbers a parameter. -/
theorem pos_of_idxOf (ctx : Array Ix.Name) (n : Ix.Name) {i : Nat}
    (found : ctx.toList.idxOf? n = some i) :
    Ix.LeanIngress.Numbering.pos ⟨ctx, false⟩ n = i := by
  rcases ctx with ⟨l⟩
  have h : l.findIdx? (· == n) = some i := found
  unfold Ix.LeanIngress.Numbering.pos
  simp only [List.findIdx?_toArray, h]
  cases i <;> rfl

/-- **The pure universe meaning** (proved): the cache-free compile keeps the
value that Source mode reads, by structural induction on the level. -/
theorem univMeaningS : UnivMeaningS := by
  intro ctx hsize l
  induction l with
  | zero h =>
    intro u k φ hc hk
    cases hc
    cases hk
    rfl
  | succ l h ih =>
    intro u k φ hc hk
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨x, hx, hk⟩ := except_bind_ok hk
    cases hk
    simp only [univEval, Ix.Kernel.Level.eval, ih v x φ hv hx]
  | max l r h ihl ihr =>
    intro u k φ hc hk
    simp only [compileUnivS, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
    obtain ⟨a, ha, b, hb, hc⟩ := hc
    cases hc
    obtain ⟨x, hx, hk⟩ := except_bind_ok hk
    obtain ⟨y, hy, hk⟩ := except_bind_ok hk
    cases hk
    simp only [univEval, Ix.Kernel.Level.eval, ihl a x φ ha hx, ihr b y φ hb hy]
  | imax l r h ihl ihr =>
    intro u k φ hc hk
    simp only [compileUnivS, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
    obtain ⟨a, ha, b, hb, hc⟩ := hc
    cases hc
    obtain ⟨x, hx, hk⟩ := except_bind_ok hk
    obtain ⟨y, hy, hk⟩ := except_bind_ok hk
    cases hk
    simp only [univEval, Ix.Kernel.Level.eval, ihl a x φ ha hx, ihr b y φ hb hy]
  | param n h =>
    intro u k φ hc hk
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hc
    cases hk
    have bound : i < ctx.size := by
      have := (List.findIdx?_eq_some_iff_getElem.mp hi).1
      simpa using this
    simp only [univEval, Ix.Kernel.Level.eval, pos_of_idxOf ctx n hi]
    rw [UInt64.toNat_ofNat_of_lt' (by omega)]
  | mvar n h =>
    intro u k φ hc hk
    cases hc

/-- **The universe bridge from Lean** (proved): `universe_bridge` with the
pure universe meaning discharged. Its only premises are the context bound
and `HashEqAgrees` on the constant's level-parameter names. -/
theorem universeBridge : UniverseBridge := universe_bridge univMeaningS

end Ix.Cert.Canon
