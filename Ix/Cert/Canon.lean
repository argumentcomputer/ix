import Ix.CanonM
import Ix.LeanIngress
import Ix.CompileCert.CanonUnivScope
import Ix.CompileCert.UniverseMeaning

/-! # The `CanonM` correspondence

`Ix.CanonM` turns Lean's terms into `Ix.Expr`s. Its output is the input of
both `Ix.Cert.compile` and Source mode (`Ix.LeanIngress`), so the
certification statements (`Ix.Cert.Statement`) are about an
`Ix.Environment`. This file states what ties that environment to Lean's. It
is an interpretation bridge, not a step of `CompileCorrect`'s proof: both
sides of `CompileCorrect` read the same `Ix.Environment`.

1. **The specification** (`nameS`, `levelS`, `syntaxS`, `exprS`, `constS`):
   the structural conversion, with the same smart constructors (so the same
   hash fields) and no cache. It is defined in `Ix.CanonM` (under this
   namespace), so that the memo's entries carry their proofs.
2. **`CanonMCorrect`: proved** (`canonMCorrect`, `canonChunkCorrect`).
   `canonName`, `canonLevel`, `canonExpr` and `canonConst` compute the
   specification from every state, and `canonChunk` maps it over its chunk
   (`CanonChunkCorrect`). `Ix.CanonM` keeps one pointer memo
   per kind whose entries carry the proof that their image is the
   specification's, and confirms each hit with `withPtrEq`, as
   `Ix.LeanIngress.ingressExprsShared` confirms its memo. It has no
   hash-keyed cache, and `canonSyntax` is total. So `ingressExpr_canonExpr`
   holds from every state, without a hypothesis.
3. **The Source reading** (`leanExpr`; proved: `ingressExpr_exprS`):
   Source mode's reading of the specification's term is a direct structural
   function of Lean's term. It reads no hash and no cache, under the
   numbering `σ ∘ nameS`.
4. **The numbering** (`numbering_nameS`, proved): `Numbering.pos` compares
   `Ix.Name`s structurally (`Ix.Name.beqRaw`), so it is the direct
   numbering of Lean's names, with no hypothesis.
5. **Universes** (`universeBridge`, proved, under the wire's bound only).
   Ixon's reading of the canonical compiled universe of `levelS l` has the
   value of Lean's level `l`, read directly. It composes 
   `Ix.CompileCert.CanonUnivScope.convCanon_eval` (`universe_bridge`) with
   `UnivMeaningS` (proved: `univMeaningS`), the pure half of the
   `UniverseMeaning`, about `compileUnivS`: the cache-free universe
   compiler. `compileUniv` computes it wherever the context fits the wire
   (`lower_eq_compileUnivS`, with
   `Ix.CompileCert.UniverseMeaning.compileUniv_exact`).
-/

namespace Ix.Cert.Canon

open Ix.Kernel (LevelParam)
open Ix.LeanIngress (ExprError KExpr KLevel)

/-! ## 1. The specification of `Ix.CanonM`

`nameS`, `levelS`, `preresolvedS`, `syntaxS`, `dataValueS`, `mdataS`,
`exprS`, `constValS` and `constS`: the conversions without their memo, with
the same smart constructors (so the same hash fields). They are defined
beside the conversions, in the module `Ix.CanonM`, under this namespace, so
that the memo's entries can carry their proofs. -/

/-- `canonConst`'s action on `Lean.AxiomVal`, without its memo. -/
def axiomValS (v : Lean.AxiomVal) : Ix.AxiomVal :=
  { cnst := constValS v.toConstantVal, isUnsafe := v.isUnsafe }

/-- `canonConst`'s action on `Lean.DefinitionVal`, without its memo. -/
def defnValS (v : Lean.DefinitionVal) : Ix.DefinitionVal :=
  { cnst := constValS v.toConstantVal, value := exprS v.value, hints := v.hints,
    safety := v.safety, all := (v.all.map nameS).toArray }

/-- `canonConst`'s action on `Lean.TheoremVal`, without its memo. -/
def thmValS (v : Lean.TheoremVal) : Ix.TheoremVal :=
  { cnst := constValS v.toConstantVal, value := exprS v.value, all := (v.all.map nameS).toArray }

/-- `canonConst`'s action on `Lean.OpaqueVal`, without its memo. -/
def opaqueValS (v : Lean.OpaqueVal) : Ix.OpaqueVal :=
  { cnst := constValS v.toConstantVal, value := exprS v.value, isUnsafe := v.isUnsafe,
    all := (v.all.map nameS).toArray }

/-- `canonConst`'s action on `Lean.QuotVal`, without its memo. -/
def quotValS (v : Lean.QuotVal) : Ix.QuotVal :=
  { cnst := constValS v.toConstantVal, kind := v.kind }

/-- `canonConst`'s action on `Lean.InductiveVal`, without its memo. -/
def inductValS (v : Lean.InductiveVal) : Ix.InductiveVal :=
  { cnst := constValS v.toConstantVal, numParams := v.numParams, numIndices := v.numIndices,
    all := (v.all.map nameS).toArray, ctors := (v.ctors.map nameS).toArray,
    numNested := v.numNested, isRec := v.isRec, isUnsafe := v.isUnsafe,
    isReflexive := v.isReflexive }

/-- `canonConst`'s action on `Lean.ConstructorVal`, without its memo. -/
def ctorValS (v : Lean.ConstructorVal) : Ix.ConstructorVal :=
  { cnst := constValS v.toConstantVal, induct := nameS v.induct, cidx := v.cidx,
    numParams := v.numParams, numFields := v.numFields, isUnsafe := v.isUnsafe }

/-- `canonConst`'s action on `Lean.RecursorRule`, without its memo. -/
def recRuleS (r : Lean.RecursorRule) : Ix.RecursorRule :=
  { ctor := nameS r.ctor, nfields := r.nfields, rhs := exprS r.rhs }

/-- `canonConst`'s action on `Lean.RecursorVal`, without its memo. -/
def recValS (v : Lean.RecursorVal) : Ix.RecursorVal :=
  { cnst := constValS v.toConstantVal, all := (v.all.map nameS).toArray,
    numParams := v.numParams, numIndices := v.numIndices, numMotives := v.numMotives,
    numMinors := v.numMinors, rules := (v.rules.map recRuleS).toArray,
    k := v.k, isUnsafe := v.isUnsafe }

@[simp] theorem constS_axiomInfo (v : Lean.AxiomVal) :
    constS (.axiomInfo v) = .axiomInfo (axiomValS v) := rfl

@[simp] theorem constS_defnInfo (v : Lean.DefinitionVal) :
    constS (.defnInfo v) = .defnInfo (defnValS v) := rfl

@[simp] theorem constS_thmInfo (v : Lean.TheoremVal) :
    constS (.thmInfo v) = .thmInfo (thmValS v) := rfl

@[simp] theorem constS_opaqueInfo (v : Lean.OpaqueVal) :
    constS (.opaqueInfo v) = .opaqueInfo (opaqueValS v) := rfl

@[simp] theorem constS_quotInfo (v : Lean.QuotVal) :
    constS (.quotInfo v) = .quotInfo (quotValS v) := rfl

@[simp] theorem constS_inductInfo (v : Lean.InductiveVal) :
    constS (.inductInfo v) = .inductInfo (inductValS v) := rfl

@[simp] theorem constS_ctorInfo (v : Lean.ConstructorVal) :
    constS (.ctorInfo v) = .ctorInfo (ctorValS v) := rfl

@[simp] theorem constS_recInfo (v : Lean.RecursorVal) :
    constS (.recInfo v) = .recInfo (recValS v) := rfl

/-! ## 2. `CanonM` computes the specification (proved)

`Ix.CanonM`'s memo entries carry the proof that their image is the
specification's, and a hit is confirmed by identity (`withPtrEq`), whose
pure meaning decides that the stored source is the input. So every
conversion returns the specification from every state, whatever the
addresses are: the memo changes only how much is recomputed. -/

section Production
open Ix.CanonM

theorem canonName_run (n : Lean.Name) (s : CanonState) :
    (Id.run ((canonName n).run s)).1 = nameS n :=
  (Id.run ((canonNameS n).run s)).1.2

theorem canonLevel_run (l : Lean.Level) (s : CanonState) :
    (Id.run ((canonLevel l).run s)).1 = levelS l :=
  (Id.run ((canonLevelS l).run s)).1.2

theorem canonExpr_run (e : Lean.Expr) (s : CanonState) :
    (Id.run ((canonExpr e).run s)).1 = exprS e :=
  (Id.run ((canonExprS e).run s)).1.2

theorem canonConst_run (c : Lean.ConstantInfo) (s : CanonState) :
    (Id.run ((canonConst c).run s)).1 = constS c :=
  (Id.run ((canonConstS c).run s)).1.2

/-- **The CanonM correspondence, computational half (proved:
`canonMCorrect`).** From every state, the conversions return the
specification. -/
def CanonMCorrect : Prop :=
  ∀ s : CanonState,
    (∀ n, (Id.run ((canonName n).run s)).1 = nameS n) ∧
    (∀ l, (Id.run ((canonLevel l).run s)).1 = levelS l) ∧
    (∀ e, (Id.run ((canonExpr e).run s)).1 = exprS e) ∧
    (∀ c, (Id.run ((canonConst c).run s)).1 = constS c)

theorem canonMCorrect : CanonMCorrect := fun s =>
  ⟨fun n => canonName_run n s, fun l => canonLevel_run l s, fun e => canonExpr_run e s,
    fun c => canonConst_run c s⟩

/-- What Source mode and the compile driver actually run: a chunk of
constants through one state (proved: `canonChunkCorrect`). -/
def CanonChunkCorrect : Prop :=
  ∀ chunk : Array (Lean.Name × Lean.ConstantInfo),
    canonChunk chunk = chunk.map fun (n, c) => (nameS n, constS c)

/-- A state monad's map whose every step returns `g x`, from every state,
returns `xs.map g`. -/
theorem list_mapM_run {σ α β : Type} (f : α → StateT σ Id β) (g : α → β)
    (hf : ∀ x s, (Id.run ((f x).run s)).1 = g x) :
    ∀ (xs : List α) (s : σ), (Id.run ((xs.mapM f).run s)).1 = xs.map g := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    simp only [List.mapM_cons, StateT.run_bind, Id.run_bind, StateT.run_pure, Id.run_pure, hf,
      ih, List.map_cons]

theorem canonChunkCorrect : CanonChunkCorrect := by
  intro chunk
  have hf : ∀ (p : Lean.Name × Lean.ConstantInfo) (s : CanonState),
      (Id.run (((fun (p : Lean.Name × Lean.ConstantInfo) => do
        let name' ← canonName p.1
        let const' ← canonConst p.2
        pure (name', const') : Lean.Name × Lean.ConstantInfo → CanonM _) p).run s)).1 =
        (nameS p.1, constS p.2) := by
    intro p s
    simp only [StateT.run_bind, Id.run_bind, StateT.run_pure, Id.run_pure, canonName_run,
      canonConst_run]
  unfold canonChunk
  rw [Array.mapM_eq_mapM_toList]
  simp only [StateT.run'_eq, StateT.run_map, Id.run_map]
  rw [list_mapM_run _ _ hf]
  rcases chunk with ⟨l⟩
  simp

theorem mem_canonChunk_iff (chunk : Array (Lean.Name × Lean.ConstantInfo))
    (p : Ix.Name × Ix.ConstantInfo) :
    p ∈ canonChunk chunk ↔ ∃ nc ∈ chunk, (nameS nc.1, constS nc.2) = p := by
  rw [canonChunkCorrect chunk, Array.mem_map]

theorem mem_canonChunk_of_mem {chunk : Array (Lean.Name × Lean.ConstantInfo)}
    {n : Lean.Name} {c : Lean.ConstantInfo} (h : (n, c) ∈ chunk) :
    (nameS n, constS c) ∈ canonChunk chunk :=
  (mem_canonChunk_iff chunk (nameS n, constS c)).mpr ⟨(n, c), h, rfl⟩

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
    return .letE (← leanExpr σ t) (← leanExpr σ v) (← leanExpr σ b) { nonDep := nd }
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

/-- Source mode reads what `CanonM` produced, from every state, as Lean's own
term (by canonicalization and ingress correctness). -/
theorem ingressExpr_canonExpr (s : Ix.CanonM.CanonState) (σ : Ix.Name → LevelParam)
    (e : Lean.Expr) :
    Ix.LeanIngress.ingressExpr σ (Id.run ((Ix.CanonM.canonExpr e).run s)).1 =
      leanExpr (σ ∘ nameS) e := by
  rw [canonExpr_run, ingressExpr_exprS]

/-! ## 4. The numbering -/

/-- `Numbering.pos`, over Lean's names (structural equality). -/
def leanPos (names : Array Lean.Name) (large : Bool) (n : Lean.Name) : LevelParam :=
  match names.findIdx? (· == n) with
  | none => names.size
  | some 0 => if large then names.size - 1 else 0
  | some (i + 1) => if large then i else i + 1

/-- `nameS` is injective: `toLeanName` inverts it. -/
theorem nameS_inj {m n : Lean.Name} (h : nameS m = nameS n) : m = n := by
  rw [← toLeanName_nameS m, ← toLeanName_nameS n, h]

/-- The structural comparison of `CanonM`'s names is Lean's name equality. -/
theorem beqRaw_nameS (m n : Lean.Name) : Ix.Name.beqRaw (nameS m) (nameS n) = (m == n) := by
  by_cases same : m = n
  · subst same
    simp [Ix.Name.beqRaw_iff.mpr rfl]
  · have differ : Ix.Name.beqRaw (nameS m) (nameS n) = false := by
      cases found : Ix.Name.beqRaw (nameS m) (nameS n)
      · rfl
      · exact absurd (nameS_inj (Ix.Name.beqRaw_iff.mp found)) same
    rw [differ]
    simp [same]

theorem findIdx_nameS (l : List Lean.Name) (n : Lean.Name) :
    l.findIdx? ((Ix.Name.beqRaw · (nameS n)) ∘ nameS) = l.findIdx? (· == n) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findIdx?_cons, List.findIdx?_cons, Function.comp_apply, beqRaw_nameS a n, ih]

/-- **The numbering** (proved): Source mode's numbering of `CanonM`'s names
is the direct numbering of Lean's. `Numbering.pos` compares names
structurally, so no hash agreement is assumed. -/
theorem numbering_nameS (names : Array Lean.Name) (large : Bool) (n : Lean.Name) :
    Ix.LeanIngress.Numbering.pos ⟨names.map nameS, large⟩ (nameS n) = leanPos names large n := by
  rcases names with ⟨l⟩
  have key : (Array.map nameS ⟨l⟩).findIdx? (Ix.Name.beqRaw · (nameS n)) =
      (⟨l⟩ : Array Lean.Name).findIdx? (· == n) := by
    rw [Array.findIdx?_map]
    simpa using findIdx_nameS l n
  simp only [Ix.LeanIngress.Numbering.pos, leanPos, Array.size_map]
  rw [key]
  rfl

theorem list_find?_canon (l : List (Lean.Name × Lean.ConstantInfo)) (n : Lean.Name) :
    (l.map fun (m, c) => (nameS m, constS c)).find? (fun p => Ix.Name.beqRaw p.1 (nameS n)) =
      (l.find? (fun p => p.1 == n)).map (fun (m, c) => (nameS m, constS c)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨m, c⟩
    simp only [List.map_cons, List.find?_cons, beqRaw_nameS m n]
    cases m == n <;> simp [ih]

theorem find?_canonChunk (chunk : Array (Lean.Name × Lean.ConstantInfo)) (n : Lean.Name) :
    (Ix.CanonM.canonChunk chunk).find? (fun p => Ix.Name.beqRaw p.1 (nameS n)) =
      (chunk.find? (fun p => p.1 == n)).map (fun (m, c) => (nameS m, constS c)) := by
  rcases chunk with ⟨l⟩
  rw [canonChunkCorrect]
  simpa using list_find?_canon l n

/-! ### Direct Lean constant and declaration-group readers -/

/-- `Numbering.params`, over Lean's level-parameter names. -/
def leanParams (lps : List Lean.Name) (large : Bool := false) : List LevelParam :=
  lps.map (leanPos lps.toArray large)

theorem numbering_pos_nameS (lps : List Lean.Name) (large : Bool) :
    (Ix.LeanIngress.Numbering.pos ⟨(lps.map nameS).toArray, large⟩ ∘ nameS) =
      leanPos lps.toArray large := by
  have h : (lps.map nameS).toArray = lps.toArray.map nameS := by simp
  rw [h]
  funext n
  exact numbering_nameS lps.toArray large n

theorem numbering_params_nameS (lps : List Lean.Name) (large : Bool := false) :
    (Ix.LeanIngress.Numbering.mk (lps.map nameS).toArray large).params =
      leanParams lps large := by
  unfold Ix.LeanIngress.Numbering.params leanParams
  show ((lps.map nameS).map (Ix.LeanIngress.Numbering.pos ⟨(lps.map nameS).toArray, large⟩)) =
    lps.map (leanPos lps.toArray large)
  rw [List.map_map, numbering_pos_nameS]

@[simp] theorem numbering_beq_self (σ : Ix.LeanIngress.Numbering) : (σ == σ) = true := by
  show (σ.large == σ.large && σ.names.isEqv σ.names Ix.Name.beqRaw) = true
  rw [Bool.and_eq_true, Array.isEqv_iff_rel]
  exact ⟨by cases σ.large <;> rfl, rfl, fun _ _ => Ix.Name.beqRaw_iff.mpr rfl⟩

theorem exprsOf_singleton (σ : Ix.LeanIngress.Numbering) (e : Ix.Expr) :
    Ix.LeanIngress.exprsOf #[(σ, e)] =
      match Ix.LeanIngress.ingressExpr σ.pos e with
      | .ok k => .ok #[k]
      | .error err => .error (.malformed s!"source term: {err}") := by
  unfold Ix.LeanIngress.exprsOf
  simp only [Ix.LeanIngress.ingressExprs, List.forIn_toArray, List.forIn_cons, List.forIn_nil,
    List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  cases Ix.LeanIngress.ingressExpr σ.pos e with
  | error err => rfl
  | ok k =>
    simp only [Ix.LeanIngress.nameExprs_eq]
    rfl

theorem exprsOf_pair (σ : Ix.LeanIngress.Numbering) (e₁ e₂ : Ix.Expr) :
    Ix.LeanIngress.exprsOf #[(σ, e₁), (σ, e₂)] =
      match do
        let k₁ ← Ix.LeanIngress.ingressExpr σ.pos e₁
        let k₂ ← Ix.LeanIngress.ingressExpr σ.pos e₂
        pure #[k₁, k₂] with
      | .ok ks => .ok ks
      | .error err => .error (.malformed s!"source term: {err}") := by
  unfold Ix.LeanIngress.exprsOf
  simp only [Ix.LeanIngress.ingressExprs, List.forIn_toArray, List.forIn_cons, List.forIn_nil,
    numbering_beq_self, ↓reduceIte, Array.toList_push, List.cons_append, List.nil_append,
    List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  cases Ix.LeanIngress.ingressExpr σ.pos e₁ with
  | error err => rfl
  | ok k₁ =>
    cases Ix.LeanIngress.ingressExpr σ.pos e₂ with
    | error err => rfl
    | ok k₂ =>
      simp only [Ix.LeanIngress.nameExprs_eq]
      rfl

@[simp] theorem constValS_levelParams (cv : Lean.ConstantVal) :
    (constValS cv).levelParams = (cv.levelParams.map nameS).toArray := rfl

/-- Source-mode reading of an `Ix.ConstantVal`. -/
def ingressConstantVal (cv : Ix.ConstantVal) (large : Bool := false) :
    Except ExprError (Ix.Kernel.ConstantVal .source) := do
  let σ : Ix.LeanIngress.Numbering := ⟨cv.levelParams, large⟩
  let ty ← Ix.LeanIngress.ingressExpr σ.pos cv.type
  pure ⟨Ix.LeanIngress.ingressKey cv.name, σ.params, ty⟩

/-- Direct Source-mode reading of a `Lean.ConstantVal`, without `Ix.ConstantVal`. -/
def leanConstantVal (cv : Lean.ConstantVal) (large : Bool := false) :
    Except ExprError (Ix.Kernel.ConstantVal .source) := do
  let ty ← leanExpr (leanPos cv.levelParams.toArray large) cv.type
  pure ⟨leanKey cv.name, leanParams cv.levelParams large, ty⟩

theorem ingressConstantVal_constValS (cv : Lean.ConstantVal) (large : Bool := false) :
    ingressConstantVal (constValS cv) large = leanConstantVal cv large := by
  simp only [ingressConstantVal, leanConstantVal, constValS, ingressKey_nameS,
    numbering_params_nameS, ingressExpr_exprS, numbering_pos_nameS]

/-- Direct Source-mode conversion of a `Lean.AxiomVal`. -/
def leanAxiomVal (v : Lean.AxiomVal) :
    Except Ix.Kernel.Reader.ReadError Ix.LeanIngress.Converted := do
  if v.isUnsafe then throw (.declined "unsafe axiom")
  match leanConstantVal v.toConstantVal false with
  | .ok cv => pure (.axiom cv)
  | .error err => throw (.malformed s!"source term: {err}")

theorem convertAxiom_axiomValS (v : Lean.AxiomVal) :
    Ix.LeanIngress.convert (.axiom (axiomValS v)) = leanAxiomVal v := by
  unfold Ix.LeanIngress.convert leanAxiomVal axiomValS
  rw [← ingressConstantVal_constValS v.toConstantVal false]
  unfold ingressConstantVal
  cases v.isUnsafe
  · simp only [Bool.false_eq_true, ↓reduceIte, exprsOf_singleton, bind, Except.bind, pure,
      Except.pure]
    cases Ix.LeanIngress.ingressExpr
      (Ix.LeanIngress.Numbering.pos ⟨(constValS v.toConstantVal).levelParams, false⟩)
      (constValS v.toConstantVal).type <;> rfl
  · rfl

/-- Direct Source-mode conversion of a `Lean.QuotVal`. -/
def leanQuotVal (v : Lean.QuotVal) :
    Except Ix.Kernel.Reader.ReadError Ix.LeanIngress.Converted :=
  match leanConstantVal v.toConstantVal false with
  | .ok cv => .ok (.quot (Ix.LeanIngress.quotKindOf v.kind) cv)
  | .error err => .error (.malformed s!"source term: {err}")

theorem convertQuotient_quotValS (v : Lean.QuotVal) :
    Ix.LeanIngress.convert (.quot (quotValS v)) = leanQuotVal v := by
  unfold Ix.LeanIngress.convert leanQuotVal quotValS
  rw [← ingressConstantVal_constValS v.toConstantVal false]
  unfold ingressConstantVal
  simp only [exprsOf_singleton, bind, Except.bind, pure, Except.pure]
  cases Ix.LeanIngress.ingressExpr
    (Ix.LeanIngress.Numbering.pos ⟨(constValS v.toConstantVal).levelParams, false⟩)
    (constValS v.toConstantVal).type <;> rfl

/-- Source-mode reading of an `Ix.DefinitionVal` as a `DefMember`. -/
def ingressDefinitionVal (v : Ix.DefinitionVal) :
    Except ExprError Ix.LeanIngress.DefMember := do
  let cv ← ingressConstantVal v.cnst false
  let val ← Ix.LeanIngress.ingressExpr (Ix.LeanIngress.Numbering.pos ⟨v.cnst.levelParams, false⟩) v.value
  pure ⟨cv, val, .defn, Ix.LeanIngress.safetyOf v.safety, Ix.LeanIngress.hintOf v.hints⟩

/-- Direct Source-mode reading of a `Lean.DefinitionVal` as a `DefMember`. -/
def leanDefinitionVal (v : Lean.DefinitionVal) :
    Except ExprError Ix.LeanIngress.DefMember := do
  let cv ← leanConstantVal v.toConstantVal false
  let val ← leanExpr (leanPos v.levelParams.toArray false) v.value
  pure ⟨cv, val, .defn, Ix.LeanIngress.safetyOf v.safety, Ix.LeanIngress.hintOf v.hints⟩

theorem ingressDefinitionVal_defnValS (v : Lean.DefinitionVal) :
    ingressDefinitionVal (defnValS v) = leanDefinitionVal v := by
  simp only [ingressDefinitionVal, leanDefinitionVal, defnValS, ingressConstantVal_constValS,
    constValS_levelParams, ingressExpr_exprS, numbering_pos_nameS]

set_option linter.unusedSimpArgs false in
theorem convertDefinitions_singleton (ci : Ix.ConstantInfo)
    (kind : Ix.DefKind) (safety : Ix.DefinitionSafety)
    (hint : Ix.Kernel.ReducibilityHint) (val : Ix.Expr)
    (hs : Ix.LeanIngress.definitionShape ci = some (kind, safety, hint))
    (hv : Ix.LeanIngress.definitionValue ci = some val) :
    Ix.LeanIngress.convertDefinitions #[ci] =
      match (do
        let cv ← ingressConstantVal ci.getCnst false
        let v' ← Ix.LeanIngress.ingressExpr
          (Ix.LeanIngress.Numbering.pos ⟨ci.getCnst.levelParams, false⟩) val
        pure (Ix.LeanIngress.DefMember.mk cv v' kind safety hint) :
          Except ExprError Ix.LeanIngress.DefMember) with
      | .ok m => .ok (.definitions #[m])
      | .error err => .error (.malformed s!"source term: {err}") := by
  simp [Ix.LeanIngress.convertDefinitions, hs, hv, ingressConstantVal, exprsOf_pair]
  cases Ix.LeanIngress.ingressExpr
    (Ix.LeanIngress.Numbering.pos ⟨ci.getCnst.levelParams, false⟩) ci.getCnst.type with
  | error err => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  | ok k₁ =>
    cases Ix.LeanIngress.ingressExpr
      (Ix.LeanIngress.Numbering.pos ⟨ci.getCnst.levelParams, false⟩) val with
    | error err => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    | ok k₂ => simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem convertDefinitions_defnValS (v : Lean.DefinitionVal) :
    Ix.LeanIngress.convertDefinitions #[.defnInfo (defnValS v)] =
      match leanDefinitionVal v with
      | .ok m => .ok (.definitions #[m])
      | .error err => .error (.malformed s!"source term: {err}") := by
  rw [← ingressDefinitionVal_defnValS]
  exact convertDefinitions_singleton (.defnInfo (defnValS v)) _ _ _ _ rfl rfl

/-- Source-mode reading of an `Ix.TheoremVal` as a `DefMember`. -/
def ingressTheoremVal (v : Ix.TheoremVal) :
    Except ExprError Ix.LeanIngress.DefMember := do
  let cv ← ingressConstantVal v.cnst false
  let val ← Ix.LeanIngress.ingressExpr (Ix.LeanIngress.Numbering.pos ⟨v.cnst.levelParams, false⟩) v.value
  pure ⟨cv, val, .thm, .safe, .opaque⟩

/-- Direct Source-mode reading of a `Lean.TheoremVal` as a `DefMember`. -/
def leanTheoremVal (v : Lean.TheoremVal) :
    Except ExprError Ix.LeanIngress.DefMember := do
  let cv ← leanConstantVal v.toConstantVal false
  let val ← leanExpr (leanPos v.levelParams.toArray false) v.value
  pure ⟨cv, val, .thm, .safe, .opaque⟩

theorem ingressTheoremVal_thmValS (v : Lean.TheoremVal) :
    ingressTheoremVal (thmValS v) = leanTheoremVal v := by
  simp only [ingressTheoremVal, leanTheoremVal, thmValS, ingressConstantVal_constValS,
    constValS_levelParams, ingressExpr_exprS, numbering_pos_nameS]

theorem convertDefinitions_thmValS (v : Lean.TheoremVal) :
    Ix.LeanIngress.convertDefinitions #[.thmInfo (thmValS v)] =
      match leanTheoremVal v with
      | .ok m => .ok (.definitions #[m])
      | .error err => .error (.malformed s!"source term: {err}") := by
  rw [← ingressTheoremVal_thmValS]
  exact convertDefinitions_singleton (.thmInfo (thmValS v)) _ _ _ _ rfl rfl

/-- Source-mode reading of an `Ix.OpaqueVal` as a `DefMember`. -/
def ingressOpaqueVal (v : Ix.OpaqueVal) :
    Except ExprError Ix.LeanIngress.DefMember := do
  let cv ← ingressConstantVal v.cnst false
  let val ← Ix.LeanIngress.ingressExpr (Ix.LeanIngress.Numbering.pos ⟨v.cnst.levelParams, false⟩) v.value
  pure ⟨cv, val, .opaq, if v.isUnsafe then .unsaf else .safe, .opaque⟩

/-- Direct Source-mode reading of a `Lean.OpaqueVal` as a `DefMember`. -/
def leanOpaqueVal (v : Lean.OpaqueVal) :
    Except ExprError Ix.LeanIngress.DefMember := do
  let cv ← leanConstantVal v.toConstantVal false
  let val ← leanExpr (leanPos v.levelParams.toArray false) v.value
  pure ⟨cv, val, .opaq, if v.isUnsafe then .unsaf else .safe, .opaque⟩

theorem ingressOpaqueVal_opaqueValS (v : Lean.OpaqueVal) :
    ingressOpaqueVal (opaqueValS v) = leanOpaqueVal v := by
  simp only [ingressOpaqueVal, leanOpaqueVal, opaqueValS, ingressConstantVal_constValS,
    constValS_levelParams, ingressExpr_exprS, numbering_pos_nameS]
  rfl

theorem convertDefinitions_opaqueValS (v : Lean.OpaqueVal) :
    Ix.LeanIngress.convertDefinitions #[.opaqueInfo (opaqueValS v)] =
      match leanOpaqueVal v with
      | .ok m => .ok (.definitions #[m])
      | .error err => .error (.malformed s!"source term: {err}") := by
  rw [← ingressOpaqueVal_opaqueValS]
  exact convertDefinitions_singleton (.opaqueInfo (opaqueValS v)) _ _ _ _ rfl rfl

/-- Source-mode reading of an `Ix.InductiveVal`'s header and counts. -/
def ingressInductiveVal (v : Ix.InductiveVal) :
    Except ExprError (Ix.Kernel.ConstantVal .source × Nat × Nat) := do
  let cv ← ingressConstantVal v.cnst false
  pure (cv, v.numParams, v.numIndices)

/-- Direct Source-mode reading of a `Lean.InductiveVal`'s header and counts. -/
def leanInductiveVal (v : Lean.InductiveVal) :
    Except ExprError (Ix.Kernel.ConstantVal .source × Nat × Nat) := do
  let cv ← leanConstantVal v.toConstantVal false
  pure (cv, v.numParams, v.numIndices)

theorem ingressInductiveVal_inductValS (v : Lean.InductiveVal) :
    ingressInductiveVal (inductValS v) = leanInductiveVal v := by
  simp only [ingressInductiveVal, leanInductiveVal, inductValS, ingressConstantVal_constValS]

/-- Source-mode reading of an `Ix.ConstructorVal`. -/
def ingressConstructorVal (c : Ix.ConstructorVal) :
    Except ExprError (Ix.Kernel.ConstantVal .source × Nat × Nat) := do
  let cv ← ingressConstantVal c.cnst false
  pure (cv, c.numParams, c.numFields)

/-- Direct Source-mode reading of a `Lean.ConstructorVal`. -/
def leanConstructorVal (c : Lean.ConstructorVal) :
    Except ExprError (Ix.Kernel.ConstantVal .source × Nat × Nat) := do
  let cv ← leanConstantVal c.toConstantVal false
  pure (cv, c.numParams, c.numFields)

theorem ingressConstructorVal_ctorValS (c : Lean.ConstructorVal) :
    ingressConstructorVal (ctorValS c) = leanConstructorVal c := by
  simp only [ingressConstructorVal, leanConstructorVal, ctorValS, ingressConstantVal_constValS]

/-- Source-mode reading of an `Ix.RecursorRule` under level-parameter numbering `σ`. -/
def ingressRecursorRule (σ : Ix.LeanIngress.Numbering) (r : Ix.RecursorRule) :
    Except ExprError (Ix.Kernel.RecRule .source) := do
  let rhs ← Ix.LeanIngress.ingressExpr σ.pos r.rhs
  pure ⟨Ix.LeanIngress.ingressKey r.ctor, r.nfields, 0, .inert, rhs, false, false, false⟩

/-- Direct Source-mode reading of a `Lean.RecursorRule` under level parameters `lps` and
large-eliminator flag `large`. -/
def leanRecursorRule (lps : List Lean.Name) (large : Bool) (r : Lean.RecursorRule) :
    Except ExprError (Ix.Kernel.RecRule .source) := do
  let rhs ← leanExpr (leanPos lps.toArray large) r.rhs
  pure ⟨leanKey r.ctor, r.nfields, 0, .inert, rhs, false, false, false⟩

theorem ingressRecursorRule_recRuleS (lps : List Lean.Name) (large : Bool)
    (r : Lean.RecursorRule) :
    ingressRecursorRule ⟨(lps.map nameS).toArray, large⟩ (recRuleS r) =
      leanRecursorRule lps large r := by
  simp only [ingressRecursorRule, leanRecursorRule, recRuleS, ingressExpr_exprS,
    numbering_pos_nameS, ingressKey_nameS]

/-! ## 5. Universes: composing with canonical universe evaluation

The Ixon side is the canonical universe semantics: `Ix.CompileCert.univEval` is the value of a wire
universe, and `Ix.CompileCert.CanonUnivScope.convCanon_eval` says that the
certified reader's reading of a canonical universe has the raw universe's
value. -/

open Ix.CompileCert (univEval)

/-- `Ix.CompileM.compileUniv` without its cache, under the context `ctx` of
the constant's level-parameter names (positional, compared structurally,
`Ix.Name.beqRaw`, as `Ix.LeanIngress.Numbering.pos` compares them). `compileUniv` compares names structurally too and checks the wire bound
(`Ix.CompileCert.UniverseMeaning.lower`); the two agree where the context fits
the wire (`lower_eq_compileUnivS`). -/
def compileUnivS (ctx : List Ix.Name) : Ix.Level → Option Ixon.Univ
  | .zero _ => some .zero
  | .succ l _ => (compileUnivS ctx l).map .succ
  | .max l r _ => do return .max (← compileUnivS ctx l) (← compileUnivS ctx r)
  | .imax l r _ => do return .imax (← compileUnivS ctx l) (← compileUnivS ctx r)
  | .param n _ => (ctx.findIdx? (Ix.Name.beqRaw · n)).map fun i => .var i.toUInt64
  | .mvar _ _ => none

/-- The cache-free compile keeps the value that Source mode reads (a member's
own parameters, `large = false`): the pure half of the
`UniverseMeaning`, over `Ix.Level`. Proved below (`univMeaningS`), by a
structural induction: the parameter case is the structural `findIdx?` of both
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
  ∀ (ps : Array Lean.Name), ps.size < UInt64.size →
    ∀ (l : Lean.Level) (u : Ixon.Univ) (k : KLevel) (φ : LevelParam → Nat),
      compileUnivS (ps.map nameS).toList (levelS l) = some u →
      leanLevel (leanPos ps false) l = .ok k →
      Ix.Kernel.Level.eval φ (Ix.Kernel.Reader.convUniv id (Ixon.canonUniv u)) =
        Ix.Kernel.Level.eval φ k

/-- **The composition** (proved): `convCanon_eval` and the pure
universe meaning give the universe bridge from Lean, through
`ingressLevel_levelS` and `numbering_nameS`. -/
theorem universe_bridge (hmean : UnivMeaningS) : UniverseBridge := by
  intro ps hsize l u k φ hc hk
  rw [Ix.CompileCert.CanonUnivScope.convCanon_eval id φ u]
  have hσ : (Ix.LeanIngress.Numbering.pos ⟨ps.map nameS, false⟩ ∘ nameS) = leanPos ps false :=
    funext fun n => numbering_nameS ps false n
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
position the structural `findIdx?` finds, as `compileUnivS` numbers a parameter. -/
theorem pos_of_findIdx (ctx : Array Ix.Name) (n : Ix.Name) {i : Nat}
    (found : ctx.toList.findIdx? (Ix.Name.beqRaw · n) = some i) :
    Ix.LeanIngress.Numbering.pos ⟨ctx, false⟩ n = i := by
  rcases ctx with ⟨l⟩
  have h : l.findIdx? (Ix.Name.beqRaw · n) = some i := found
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
    simp only [univEval, Ix.Kernel.Level.eval, pos_of_findIdx ctx n hi]
    rw [UInt64.toNat_ofNat_of_lt' (by omega)]
  | mvar n h =>
    intro u k φ hc hk
    cases hc

/-- **The universe bridge from Lean** (proved): `universe_bridge` with the
pure universe meaning discharged. Its only premise is the context bound. -/
theorem universeBridge : UniverseBridge := universe_bridge univMeaningS

/-! ### `compileUniv` computes the cache-free compile

`Ix.CompileM.compileUniv` computes the exact positional lowering
`Ix.CompileCert.UniverseMeaning.lower` from every exact memo
(`compileUniv_exact`): parameters at their first structural position, under
the wire's `UInt64` bound. Where the context fits the wire, that is
`compileUnivS`, so the universe bridge is about `compileUniv`'s own output. -/

/-- The compiler's structural name equality is the ingress's. -/
theorem nameEq_eq_beqRaw (a b : Ix.Name) :
    Ix.Compile.ExactKey.nameEq a b = Ix.Name.beqRaw a b := by
  cases found : Ix.Name.beqRaw a b
  · cases exact : Ix.Compile.ExactKey.nameEq a b
    · rfl
    · have := Ix.Name.beqRaw_iff.mpr ((Ix.Compile.ExactKey.nameEq_iff a b).mp exact)
      rw [found] at this
      cases this
  · exact (Ix.Compile.ExactKey.nameEq_iff a b).mpr (Ix.Name.beqRaw_iff.mp found)

/-- **The exact lowering is the cache-free compile** on a context that fits
the wire. -/
theorem lower_eq_compileUnivS (ctx : List Ix.Name) (fits : ctx.length ≤ UInt64.size)
    (l : Ix.Level) :
    Ix.CompileCert.UniverseMeaning.lower ctx l = compileUnivS ctx l := by
  induction l with
  | zero h => rfl
  | succ l h ih =>
    show (Ix.CompileCert.UniverseMeaning.lower ctx l >>= fun u => pure (Ixon.Univ.succ u)) =
      (compileUnivS ctx l).map .succ
    rw [ih]
    cases compileUnivS ctx l <;> rfl
  | max l r h ihl ihr =>
    show (Ix.CompileCert.UniverseMeaning.lower ctx l >>= fun u =>
        Ix.CompileCert.UniverseMeaning.lower ctx r >>= fun v => pure (Ixon.Univ.max u v)) =
      (compileUnivS ctx l >>= fun u => compileUnivS ctx r >>= fun v => pure (Ixon.Univ.max u v))
    rw [ihl, ihr]
  | imax l r h ihl ihr =>
    show (Ix.CompileCert.UniverseMeaning.lower ctx l >>= fun u =>
        Ix.CompileCert.UniverseMeaning.lower ctx r >>= fun v => pure (Ixon.Univ.imax u v)) =
      (compileUnivS ctx l >>= fun u => compileUnivS ctx r >>= fun v => pure (Ixon.Univ.imax u v))
    rw [ihl, ihr]
  | param n h =>
    have same : Ix.Compile.ExactKey.nameIndex n ctx = ctx.findIdx? (Ix.Name.beqRaw · n) := by
      unfold Ix.Compile.ExactKey.nameIndex
      congr 1
      funext m
      exact nameEq_eq_beqRaw m n
    show (Ix.Compile.ExactKey.nameIndex n ctx >>= fun index =>
        if index < UInt64.size then some (Ixon.Univ.var index.toUInt64) else none) =
      (ctx.findIdx? (Ix.Name.beqRaw · n)).map fun i => Ixon.Univ.var i.toUInt64
    rw [same]
    cases found : ctx.findIdx? (Ix.Name.beqRaw · n) with
    | none => rfl
    | some i =>
      have inside : i < ctx.length := (List.findIdx?_eq_some_iff_getElem.mp found).1
      have bounded : i < UInt64.size := Nat.lt_of_lt_of_le inside fits
      show (if i < UInt64.size then some (Ixon.Univ.var i.toUInt64) else none) = some (.var i.toUInt64)
      simp only [bounded, ↓reduceIte]
  | mvar n h => rfl

end Ix.Cert.Canon
