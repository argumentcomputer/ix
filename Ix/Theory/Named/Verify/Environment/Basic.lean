/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.LocalContext
import Ix.Theory.Named.Typing.EnvLemmas

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

/-- The step an abstract environment takes when `ci`, modelled by `ci'`, is added.

At safety levels where the declaration is visible the constant is added; where it is not, the
environment is unchanged, matching `TrEnv'.ignore`. Stating this rather than just `venv ≤ venv'`
is what lets a caller see *which* constant a step added. -/
def VEnv.AddConst (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VConstant) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    TrConstant safety venv ci ci' ∧ ci'.WF venv ∧ venv.addConst ci.name ci' = some venv'
  else
    venv' = venv

theorem VEnv.AddConst.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddConst venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddConst at H; split at H
  · exact addConst_le H.2.2
  · exact H ▸ VEnv.LE.rfl

/-- As `VEnv.AddConst`, for a definition: the constant is added and then its defining equation,
matching `TrEnv'.defn`. -/
def VEnv.AddDef (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VDefVal) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    ∃ base, TrDefVal safety venv ci ci' ∧ ci'.WF venv ∧
      venv.addConst ci.name ci'.toVConstant = some base ∧
      venv' = base.addDefEq ci'.toDefEq
  else
    venv' = venv

theorem VEnv.AddDef.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddDef venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddDef at H; split at H
  · obtain ⟨base, _, _, hadd, rfl⟩ := H
    exact (addConst_le hadd).trans (VEnv.addDefEq_le ..)
  · exact H ▸ VEnv.LE.rfl

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H

/-! ## Inductive-environment alignment -/

/-- The three kinds of constants emitted by an inductive declaration. The
role is tracked explicitly so an alignment witness cannot stand in a
definition or axiom where the kernel emits inductive metadata. -/
inductive InductConstantKind where
  | induct
  | ctor
  | recursor

def InductConstantKind.Matches : InductConstantKind → ConstantInfo → Prop
  | .induct, .inductInfo _ => True
  | .ctor, .ctorInfo _ => True
  | .recursor, .recInfo _ => True
  | _, _ => False

theorem InductConstantKind.Matches.value?_eq_none
    {kind : InductConstantKind} {ci : ConstantInfo}
    (H : InductConstantKind.Matches kind ci) : ci.value? = none := by
  cases kind <;> cases ci <;> simp_all [InductConstantKind.Matches, ConstantInfo.value?]

/-- One insertion shared by the implementation `ConstMap` and Theory `VEnv`.
The translated constant is checked in the Theory environment immediately
before insertion. -/
structure AddInductConstant (kind : InductConstantKind)
    (m₁ : ConstMap) (env₁ : VEnv) (ci' : VConstVal)
    (m₂ : ConstMap) (env₂ : VEnv) where
  info : ConstantInfo
  kind_eq : kind.Matches info
  tr : TrConstVal .safe env₁ info ci'
  map_fresh : m₁.find? ci'.name = none
  env_add : env₁.addConst ci'.name ci'.toVConstant = some env₂
  map_add : m₂ = m₁.insert ci'.name info

/-- List-fold alignment for the constructor constants of a block. -/
inductive AddInductConstants (kind : InductConstantKind) :
    ConstMap → VEnv → List VConstVal → ConstMap → VEnv → Type where
  | nil : AddInductConstants kind m env [] m env
  | cons :
    AddInductConstant kind m₁ env₁ ci m₂ env₂ →
    AddInductConstants kind m₂ env₂ cis m₃ env₃ →
    AddInductConstants kind m₁ env₁ (ci :: cis) m₃ env₃

/-- A reusable witness for the defeq tail of an environment transaction. -/
structure AddDefEqs (env₁ : VEnv) (dfs : List VDefEq) (env₂ : VEnv) : Prop where
  fold_eq : dfs.foldl VEnv.addDefEq env₁ = env₂

/-- The generated recursor represented as a named Theory constant. -/
def inductRecVal (decl : VInductDecl) (ty : VInductiveType) : VConstVal :=
  ⟨VInductDecl.recConstRec decl.uvars ty.name decl.nparams ty, .str ty.name "rec"⟩

/-- The exact mixed recursor represented as a named Theory constant. -/
def inductGenerationRecVal {decl : VInductDecl}
    (generation : decl.GenerationChecked) : VConstVal :=
  ⟨generation.recursor, .str generation.block.sourceType.name "rec"⟩

/-- The implementation recursor metadata carries the same K-like reduction
flag retained by Theory generation. Keeping this separate from `TrConstant`
prevents a type-correct recursor with the wrong reduction behavior from
satisfying an inductive alignment trace. -/
def RecursorKMatches (info : ConstantInfo) (kTarget : Bool) : Prop :=
  match info with
  | .recInfo rec => rec.k = kTarget
  | _ => False

instance (info : ConstantInfo) (kTarget : Bool) :
    Decidable (RecursorKMatches info kTarget) := by
  cases info <;> simp [RecursorKMatches] <;> infer_instance

/-- Data-bearing trace of a complete normalized inductive transaction: one
`inductInfo`, the constructor `ctorInfo`s in declaration order, one `recInfo`,
and finally the generated Theory iota equations. The retained generation
certificate owns both the raw declaration inserted into the Theory environment
and the checked normalization view used to generate the recursor and rules. -/
structure AddInductTrace (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) where
  generation : decl.GenerationChecked
  generation_wf : generation.WF env₁
  typeMap : ConstMap
  typeEnv : VEnv
  ctorMap : ConstMap
  ctorEnv : VEnv
  recEnv : VEnv
  addType : AddInductConstant .induct m₁ env₁
    generation.block.sourceType.toVConstVal typeMap typeEnv
  addCtors : AddInductConstants .ctor typeMap typeEnv
    generation.block.sourceType.ctors ctorMap ctorEnv
  addRec : AddInductConstant .recursor ctorMap ctorEnv
    (inductGenerationRecVal generation) m₂ recEnv
  recK : RecursorKMatches addRec.info generation.kTarget
  addRules : AddDefEqs recEnv generation.generatedRules env₂

/-- Proposition-valued environment alignment, preserving the public shape of
the original placeholder while hiding the intermediate transaction states. -/
def AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  Nonempty (AddInductTrace m₁ env₁ decl m₂ env₂)

/-- Every implementation recursor stored by a block replay retains the
K-like flag computed by the block generator. -/
def RecursorMapKMatches (m : ConstMap) (recursors : List VConstVal)
    (kTarget : Bool) : Prop :=
  ∀ recursor ∈ recursors, ∃ info,
    m.find? recursor.name = some info ∧ RecursorKMatches info kTarget

/-- Data-bearing alignment trace for a complete mutual inductive block.
Families, globally flattened constructors, and recursors are each inserted
as a list phase, followed only after all recursors exist by the flattened
rule phase. -/
structure AddInductBlockTrace
    (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) where
  generation : decl.BlockGenerationChecked
  blockEnv : VEnv
  generation_wf : generation.WF env₁ blockEnv
  typeMap : ConstMap
  typeEnv : VEnv
  ctorMap : ConstMap
  ctorEnv : VEnv
  recEnv : VEnv
  addTypes : AddInductConstants .induct m₁ env₁
    decl.blockTypeConstants typeMap typeEnv
  addCtors : AddInductConstants .ctor typeMap typeEnv
    decl.blockConstructorConstants ctorMap ctorEnv
  addRecs : AddInductConstants .recursor ctorMap ctorEnv
    generation.recursors m₂ recEnv
  recK : RecursorMapKMatches m₂ generation.recursors generation.kTarget
  addRules : AddDefEqs recEnv generation.generatedRules env₂

/-- Proposition-valued alignment for a complete mutual block. -/
def AddInductBlock (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  Nonempty (AddInductBlockTrace m₁ env₁ decl m₂ env₂)

/-- Data-bearing alignment trace for a nested inductive declaration: the
source families and constructors are the stored payload, followed by the
restored recursors and restored rules.  The implementation map receives
only restored metadata; no auxiliary constant appears in either the map or
the Theory environment. -/
structure AddInductNestedTrace
    (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) where
  nested : decl.NestedBlockChecked
  nested_wf : nested.WF env₁
  typeMap : ConstMap
  typeEnv : VEnv
  ctorMap : ConstMap
  ctorEnv : VEnv
  recEnv : VEnv
  addTypes : AddInductConstants .induct m₁ env₁
    decl.blockTypeConstants typeMap typeEnv
  addCtors : AddInductConstants .ctor typeMap typeEnv
    decl.blockConstructorConstants ctorMap ctorEnv
  addRecs : AddInductConstants .recursor ctorMap ctorEnv
    nested.recursors m₂ recEnv
  recK : RecursorMapKMatches m₂ nested.recursors nested.generation.kTarget
  addRules : AddDefEqs recEnv nested.generatedRules env₂

/-- Proposition-valued alignment for a nested declaration. -/
def AddInductNested (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  Nonempty (AddInductNestedTrace m₁ env₁ decl m₂ env₂)

theorem AddInductConstants.to_foldlM :
    AddInductConstants kind m₁ env₁ cis m₂ env₂ →
    List.foldlM (fun env (ci : VConstVal) => env.addConst ci.name ci.toVConstant) env₁ cis =
      some env₂
  | .nil => rfl
  | .cons h hrest => by
    rw [List.foldlM_cons, h.env_add]
    exact hrest.to_foldlM

theorem AddInductConstant.fresh
    (H : AddInductConstant kind m₁ env₁ ci m₂ env₂) : env₁.constants ci.name = none :=
  VEnv.addConst_fresh H.env_add

theorem AddInductConstant.lookup
    (H : AddInductConstant kind m₁ env₁ ci m₂ env₂) :
    env₂.constants ci.name = some ci.toVConstant :=
  VEnv.addConst_self H.env_add

theorem AddInductConstant.le
    (H : AddInductConstant kind m₁ env₁ ci m₂ env₂) : env₁ ≤ env₂ :=
  VEnv.addConst_le H.env_add

theorem AddInductConstants.le :
    AddInductConstants kind m₁ env₁ cis m₂ env₂ → env₁ ≤ env₂
  | .nil => .rfl
  | .cons h hrest => h.le.trans hrest.le

theorem AddInductConstants.lookup :
    (H : AddInductConstants kind m₁ env₁ cis m₂ env₂) →
      ∀ ci ∈ cis, env₂.constants ci.name = some ci.toVConstant
  | .nil, _, hmem => nomatch hmem
  | .cons h hrest, ci, hmem => by
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact hrest.le.constants h.lookup
    · exact hrest.lookup ci hmem

theorem AddInductConstants.fresh :
    (H : AddInductConstants kind m₁ env₁ cis m₂ env₂) →
      ∀ ci ∈ cis, env₁.constants ci.name = none
  | .nil, _, hmem => nomatch hmem
  | .cons h hrest, ci, hmem => by
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact h.fresh
    · exact h.le.constants_none (hrest.fresh ci hmem)

theorem AddDefEqs.to_add (H : AddDefEqs env₁ dfs env₂) :
    dfs.foldl VEnv.addDefEq env₁ = env₂ := H.fold_eq

theorem AddDefEqs.le (H : AddDefEqs env₁ dfs env₂) : env₁ ≤ env₂ := by
  rw [← H.fold_eq]
  exact (VInductDecl.rulesFold_spec dfs env₁).1

theorem AddDefEqs.lookup (H : AddDefEqs env₁ dfs env₂)
    (hdf : df ∈ dfs) : env₂.defeqs df := by
  rw [← H.fold_eq]
  exact (VInductDecl.rulesFold_spec dfs env₁).2 df hdf

theorem AddInductTrace.to_addInductGeneration
    (H : AddInductTrace m₁ env₁ decl m₂ env₂) :
    env₁.addInductGeneration H.generation = some env₂ := by
  have hrec :
      H.ctorEnv.addConst
        (.str H.generation.block.sourceType.name "rec")
        H.generation.recursor = some H.recEnv := by
    simpa [inductGenerationRecVal] using H.addRec.env_add
  simp [VEnv.addInductGeneration, H.addType.env_add,
    H.addCtors.to_foldlM, hrec, H.addRules.to_add]

theorem AddInductBlockTrace.to_addInductBlockGeneration
    (H : AddInductBlockTrace m₁ env₁ decl m₂ env₂) :
    env₁.addInductBlockGeneration H.generation = some env₂ := by
  simp [VEnv.addInductBlockGeneration, H.addTypes.to_foldlM,
    H.addCtors.to_foldlM, H.addRecs.to_foldlM, H.addRules.to_add]

theorem AddInductNestedTrace.to_addInductNested
    (H : AddInductNestedTrace m₁ env₁ decl m₂ env₂) :
    env₁.addInductNested H.nested = some env₂ := by
  simp [VEnv.addInductNested, H.addTypes.to_foldlM,
    H.addCtors.to_foldlM, H.addRecs.to_foldlM, H.addRules.to_add]

/-- Recover the exact certified normalized Theory transaction represented by
an implementation metadata replay. This replaces the old, false-for-aliases
claim that every replay must pass the identity-only `VEnv.addInduct` wrapper. -/
nonrec theorem AddInduct.to_addInduct
    (H : AddInduct m₁ env₁ decl m₂ env₂) :
    ∃ generation : decl.GenerationChecked,
      generation.WF env₁ ∧
        env₁.addInductGeneration generation = some env₂ := by
  rcases H with ⟨H⟩
  exact ⟨H.generation, H.generation_wf, H.to_addInductGeneration⟩

nonrec theorem AddInduct.le (H : AddInduct m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := by
  obtain ⟨generation, -, hadd⟩ := H.to_addInduct
  rcases VEnv.addInductGeneration_trace hadd with ⟨trace⟩
  exact trace.le

/-- Recover the exact block-wide Theory transaction represented by an
implementation metadata replay. -/
theorem AddInductBlock.to_addInductBlock
    (H : AddInductBlock m₁ env₁ decl m₂ env₂) :
    ∃ (generation : decl.BlockGenerationChecked) (blockEnv : VEnv),
      generation.WF env₁ blockEnv ∧
        env₁.addInductBlockGeneration generation = some env₂ := by
  rcases H with ⟨H⟩
  exact ⟨H.generation, H.blockEnv, H.generation_wf,
    H.to_addInductBlockGeneration⟩

theorem AddInductBlock.le
    (H : AddInductBlock m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := by
  obtain ⟨generation, -, -, hadd⟩ := H.to_addInductBlock
  rcases VEnv.addInductBlockGeneration_trace hadd with ⟨trace⟩
  exact trace.le

/-- Recover the exact nested Theory transaction represented by an
implementation metadata replay. -/
theorem AddInductNested.to_addInductNested
    (H : AddInductNested m₁ env₁ decl m₂ env₂) :
    ∃ nested : decl.NestedBlockChecked,
      nested.WF env₁ ∧ env₁.addInductNested nested = some env₂ := by
  rcases H with ⟨H⟩
  exact ⟨H.nested, H.nested_wf, H.to_addInductNested⟩

theorem AddInductNested.le
    (H : AddInductNested m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := by
  obtain ⟨nested, -, hadd⟩ := H.to_addInductNested
  exact VEnv.addInductNested_le hadd

/- The projection relation is now a concrete Theory proposition, so merely
mentioning `TrExprS` no longer contaminates these projection-free roots with
the deferred structural-law sorries. -/
#guard_named_axioms Ix.Theory.Named.AddInductTrace.to_addInductGeneration [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInduct.to_addInduct [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInduct.le [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductBlockTrace.to_addInductBlockGeneration [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductBlock.to_addInductBlock [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductBlock.le [propext, Classical.choice, Quot.sound]

/-- Insert a whole block of definitions into the constant map. -/
def insertDefs (C : ConstMap) (cis : List DefinitionVal) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name (.defnInfo ci)) C

variable (safety : DefinitionSafety) (env env' : VEnv) in
/-- Translation data for a mutual block: the headers are translated against the environment
before the block is added, the values against the environment that already has every constant
of the block, mirroring the kernel adding them all as axioms first. -/
def TrDefBlock (cis : List DefinitionVal) (cis' : List VDefVal) : Prop :=
  List.Forall₂ (fun ci ci' =>
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal ∧
    TrExprS env' ci.levelParams [] ci.value ci'.value) cis cis'

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  /-- A mutual block, and an unsafe definition as the one-element case. -/
  | mutualDef {cis : List DefinitionVal} {cis' : List VDefVal} :
    TrDefBlock safety env env' cis cis' →
    -- the block's names are distinct; `addMutual` checks this, as does lean4#14632
    (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci' ∈ cis', ci'.toVConstant.WF env) →
    env.addConsts cis' = some env' →
    (∀ ci' ∈ cis', ci'.WF env') →
    TrEnv' C Q env →
    TrEnv' (insertDefs C cis) Q (env'.addDefEqs cis')
  | thm {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  /-- Internal kernel-checking stage for one inductive metadata constant.
  Lean checks a family and its constructors in environments that exist before
  the complete block transaction. Keeping this stage explicit lets the
  verified WHNF/defeq checker run in exactly those environments; final
  environment replay continues to use the atomic `induct` constructor below.
  -/
  | inductStaging {ci' : VConstVal} :
    AddInductConstant kind C env ci' C' env' →
    ci'.toVConstant.WF env →
    TrEnv' C Q env →
    TrEnv' C' Q env'
  | induct :
    AddInduct C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'
  | inductBlock :
    AddInductBlock C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'
  | inductNested :
    AddInductNested C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'
  /-- Register a Theory structure-eta descriptor without changing the host
  constant map.  Host eligibility and exact view alignment are retained by
  `StructureEtaArtifact`; this history step records only the checked Theory
  capability and its subject-reduction certificate. -/
  | structEta :
    rule.WF env →
    TrEnv' C Q env →
    TrEnv' C Q (env.addStructEta rule)

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | mutualDef _ _ _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutualDef h2 h3 h4⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | inductStaging h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom h2 h1.env_add⟩
  | induct h1 _ ih =>
    have ⟨_, H⟩ := ih
    obtain ⟨generation, hgen, hadd⟩ := h1.to_addInduct
    exact ⟨_, H.decl <| .induct hgen hadd⟩
  | inductBlock h1 _ ih =>
    have ⟨_, H⟩ := ih
    obtain ⟨generation, blockEnv, hgen, hadd⟩ :=
      h1.to_addInductBlock
    exact ⟨_, H.decl <| .inductBlock (blockEnv := blockEnv) hgen hadd⟩
  | inductNested h1 _ ih =>
    have ⟨_, H⟩ := ih
    obtain ⟨nested, hwf, hadd⟩ := h1.to_addInductNested
    exact ⟨_, H.decl <| .inductNested hwf hadd⟩
  | structEta hrule _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.structEta hrule⟩

#guard_named_axioms Ix.Theory.Named.TrEnv'.wf [propext, Classical.choice, Quot.sound]
