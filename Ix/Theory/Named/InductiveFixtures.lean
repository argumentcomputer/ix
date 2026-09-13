/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Inductive
import Ix.Theory.Named.Meta
import Ix.Theory.Named.Typing.InductiveLemmas
import Ix.Theory.Named.Typing.Meta

open Ix.Theory (VLevel)

/-! Adequacy fixtures for `VEnv.addInduct` (stage 3): run the generator on
hand-written declarations and check the output against the real kernel's
constants, translated by the `vconst`/`vdefeq` macros. A mismatch in
telescope order, universe conventions, or de Bruijn arithmetic fails these
`rfl`s. -/

namespace Ix.Theory.Named
namespace InductiveFixtures
open VInductDecl

/-- Permute the universe parameters of a translated constant. The `vconst`
and `vdefeq` macros number universes by occurrence order (declaration
levels first), while the kernel's recursors put the elimination level
first; these fixtures compare via the explicit permutation. -/
private def permC (ci : VConstant) (ls : List VLevel) : VConstant :=
  ⟨ci.uvars, ci.type.instL ls⟩

private def permE (df : VDefEq) (ls : List VLevel) : VDefEq :=
  ⟨df.uvars, df.lhs.instL ls, df.rhs.instL ls, df.type.instL ls⟩

/-! ## Nat -/

def natType : VInductiveType where
  name := ``Nat
  uvars := 0
  type := vexpr(Type)
  ctors := [⟨vconst(type_of% @Nat.zero), ``Nat.zero⟩, ⟨vconst(type_of% @Nat.succ), ``Nat.succ⟩]

def natDecl : VInductDecl := ⟨0, 0, [natType]⟩

example : natDecl.stage3 = true := rfl

/-- The shared checked analysis retains the normalized declaration data that
generation and verification consume. -/
def natChecked : natDecl.Checked := natDecl.checked?.get (by decide)

/-- Identity normalization packages the existing raw-normal-form path without
changing its analyzer result. -/
def natNormalizedChecked : NormalizedChecked natDecl :=
  (identityChecked? natDecl).get (by decide)

def natGenerationChecked : GenerationChecked natDecl :=
  (identityGeneration? natDecl).get (by decide)

/-- The public block descriptor specializes to the same singleton metadata. -/
def natBlockGenerationChecked : BlockGenerationChecked natDecl :=
  (identityBlockGeneration? natDecl).get (by decide)

example : natNormalizedChecked.normalization.view = natDecl := rfl
example : natNormalizedChecked.checked.type = natType := rfl
example : (normalizedChecked? natDecl natDecl).isSome = true := rfl
example : (identityChecked? natDecl).isSome = natDecl.checked?.isSome :=
  identityChecked?_isSome natDecl
example : natGenerationChecked.block = natNormalizedChecked := rfl
example : natGenerationChecked.block.ctorPairs.length = 2 := rfl
example : natGenerationChecked.motiveType = natChecked.motiveType := rfl
example : natGenerationChecked.minorTypes = natChecked.minorTypes := rfl
example : natGenerationChecked.recursor = natChecked.recursor := rfl
example : natGenerationChecked.generatedRules = natChecked.generatedRules := rfl

example : natChecked.type = natType := rfl
example : natChecked.params = [] := rfl
example : natChecked.indices = [] := rfl
example : natChecked.resultLevel = .succ .zero := rfl
example : natChecked.elimination = .large := rfl
example : natChecked.kTarget = false := rfl
example : natGenerationChecked.kTarget = false := rfl
example : natChecked.constructors.length = 2 := rfl
example : natChecked.constructors[1].recursive.length = 1 := rfl
example : natChecked.constructors[1].recursive[0].fieldIndex = 0 := rfl
example : natChecked.constructors[1].recursive[0].binders = [] := rfl
example : natChecked.recursor = recConst 0 ``Nat 0 natType := rfl
example : natChecked.generatedRules = rules 0 ``Nat 0 natType := rfl
example : natChecked.type.type.LevelWF natDecl.uvars := natChecked.type_levelWF
example : ∀ c ∈ natChecked.type.ctors, c.type.LevelWF natDecl.uvars :=
  fun _ hc => natChecked.ctor_levelWF hc

/-- The generated recursor is exactly the kernel's `Nat.rec`. -/
example : recConst 0 ``Nat 0 natType = vconst(type_of% @Nat.rec) := rfl

/-- The generated iota rules are exactly the kernel's reduction rules for
`Nat.rec`, phrased as closed lambda-telescope defeqs like `quotDefEq`. -/
example : (rules 0 ``Nat 0 natType)[0]? =
    some (vdefeq(motive z s => @Nat.rec motive z s .zero ≡ z)) := rfl

example : (rules 0 ``Nat 0 natType)[1]? =
    some (vdefeq(motive z s n => @Nat.rec motive z s (.succ n) ≡ s n (@Nat.rec motive z s n))) :=
  rfl

example : (VEnv.empty.addInduct natDecl).isSome = true := rfl

example : (VEnv.empty.addInduct natDecl).map (·.constants ``Nat) =
    some (some natType.toVConstant) := rfl

example : (VEnv.empty.addInduct natDecl).map (·.constants ``Nat.rec) =
    some (some (recConst 0 ``Nat 0 natType)) := rfl

/-- The successor iota rule is registered in the output environment. -/
example : ∀ env', VEnv.empty.addInduct natDecl = some env' →
    env'.defeqs (rule 0 ``Nat 0 natType 1 ⟨vconst(type_of% @Nat.succ), ``Nat.succ⟩) := by
  rintro env' ⟨⟩; exact .inl rfl

/-! ## Bool -/

def boolType : VInductiveType where
  name := ``Bool
  uvars := 0
  type := vexpr(Type)
  ctors := [⟨vconst(type_of% @Bool.false), ``Bool.false⟩, ⟨vconst(type_of% @Bool.true), ``Bool.true⟩]

def boolDecl : VInductDecl := ⟨0, 0, [boolType]⟩

example : boolDecl.stage3 = true := rfl

example : recConst 0 ``Bool 0 boolType = vconst(type_of% @Bool.rec) := rfl

example : (rules 0 ``Bool 0 boolType)[0]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .false ≡ f)) := rfl

example : (rules 0 ``Bool 0 boolType)[1]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .true ≡ t)) := rfl

/-! ## Unit/Empty edge shapes

`Unit` is a reducible alias for `PUnit` on this Lean revision, so the actual
one-constructor kernel metadata is recorded under `PUnit`. Together with
`Empty`, these fixtures exercise the one- and zero-constructor generation
paths without inventing an alias-level recursor that the kernel does not
declare. -/

def punitType : VInductiveType where
  name := ``PUnit
  uvars := 1
  type := vconst(type_of% @PUnit).type
  ctors := [⟨vconst(type_of% @PUnit.unit), ``PUnit.unit⟩]

def punitDecl : VInductDecl := ⟨1, 0, [punitType]⟩

example : punitDecl.stage3 = true := rfl

def punitChecked : punitDecl.Checked := punitDecl.checked?.get (by decide)

def punitGenerationChecked : GenerationChecked punitDecl :=
  (identityGeneration? punitDecl).get (by decide)

example : punitChecked.params = [] := rfl
example : punitChecked.indices = [] := rfl
example : punitChecked.resultLevel = .param 0 := rfl
example : punitChecked.elimination = .large := rfl
example : punitChecked.kTarget = false := rfl
example : punitChecked.constructors.length = 1 := rfl
example : punitChecked.constructors[0].fields = [] := rfl
example : punitChecked.constructors[0].recursive = [] := rfl
example : punitGenerationChecked.block.ctorPairs.length = 1 := rfl
example : punitGenerationChecked.minorTypes.length = 1 := rfl
example : punitGenerationChecked.generatedRules.length = 1 := rfl

/-- The one-constructor recursor retains the fresh elimination universe before
the source universe, and its sole minor occurs before the major. -/
example : punitGenerationChecked.recursor =
    permC (vconst(type_of% @PUnit.rec)) [.param 1, .param 0] := rfl

example : punitGenerationChecked.generatedRules[0]? =
    some (permE
      (vdefeq((motive : PUnit.{u} → Sort v) unit =>
        @PUnit.rec.{v, u} motive unit @PUnit.unit.{u} ≡ unit))
      [.param 1, .param 0]) := rfl

theorem punitDecl_wf : punitDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = punitType :=
    List.mem_singleton.1 (by simpa [punitDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change True
    trivial
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    constructor
    · change True
      trivial
    · exact .nil

def punitEnv : VEnv :=
  (VEnv.empty.addInduct punitDecl).get (by decide)

/-- The public checked transaction and the normalized generation core are the
same computation for this identity-normalized edge fixture. -/
example : VEnv.empty.addInduct punitDecl =
    VEnv.empty.addInductGeneration punitGenerationChecked := rfl

theorem punitEnv_ordered : punitEnv.Ordered :=
  VEnv.addInductGeneration_WF .empty
    ((punitChecked.wf_of_decl punitDecl_wf).identityGeneration .empty) rfl

def emptyType : VInductiveType where
  name := ``Empty
  uvars := 0
  type := vconst(type_of% @Empty).type
  ctors := []

def emptyDecl : VInductDecl := ⟨0, 0, [emptyType]⟩

example : emptyDecl.stage3 = true := rfl

def emptyChecked : emptyDecl.Checked := emptyDecl.checked?.get (by decide)

def emptyGenerationChecked : GenerationChecked emptyDecl :=
  (identityGeneration? emptyDecl).get (by decide)

def emptyBlockGenerationChecked : BlockGenerationChecked emptyDecl :=
  (identityBlockGeneration? emptyDecl).get (by decide)

example : emptyChecked.params = [] := rfl
example : emptyChecked.indices = [] := rfl
example : emptyChecked.resultLevel = .succ .zero := rfl
example : emptyChecked.elimination = .large := rfl
example : emptyChecked.kTarget = false := rfl
example : emptyChecked.constructors = [] := rfl
example : emptyGenerationChecked.block.ctorPairs = [] := rfl
example : emptyGenerationChecked.minorTypes = [] := rfl
example : emptyGenerationChecked.generatedRules = [] := rfl

/-- Empty elimination has a motive and major but no constructor minor. -/
example : emptyGenerationChecked.recursor =
    vconst(type_of% @Empty.rec) := rfl

theorem emptyDecl_wf : emptyDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = emptyType :=
    List.mem_singleton.1 (by simpa [emptyDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change True
    trivial
  · intro c hc
    simp [emptyType] at hc

def emptyEnv : VEnv :=
  (VEnv.empty.addInduct emptyDecl).get (by decide)

example : VEnv.empty.addInduct emptyDecl =
    VEnv.empty.addInductGeneration emptyGenerationChecked := rfl

theorem emptyEnv_ordered : emptyEnv.Ordered :=
  VEnv.addInductGeneration_WF .empty
    ((emptyChecked.wf_of_decl emptyDecl_wf).identityGeneration .empty) rfl

/-! ## List: one parameter, a dependent field, direct recursion -/

def listType : VInductiveType where
  name := ``List
  uvars := 1
  type := vconst(type_of% @List).type
  ctors := [⟨vconst(type_of% @List.nil), ``List.nil⟩, ⟨vconst(type_of% @List.cons), ``List.cons⟩]

def listDecl : VInductDecl := ⟨1, 1, [listType]⟩

example : listDecl.stage3 = true := rfl

/-- The generated recursor is exactly the kernel's `List.rec`, with the
occurrence-ordered `vconst` universes permuted to the kernel's
elimination-level-first convention. -/
example : recConst 1 ``List 1 listType =
    permC (vconst(type_of% @List.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``List 1 listType)[0]? =
    some (permE (vdefeq(α motive n c => @List.rec α motive n c (@List.nil α) ≡ n))
      [.param 1, .param 0]) := rfl

example : (rules 1 ``List 1 listType)[1]? =
    some (permE (vdefeq(α motive n c hd tl =>
        @List.rec α motive n c (@List.cons α hd tl) ≡
          c hd tl (@List.rec α motive n c tl)))
      [.param 1, .param 0]) := rfl

example : (VEnv.empty.addInduct listDecl).isSome = true := rfl

/-! ## Prod: two parameters, no recursion -/

def prodType : VInductiveType where
  name := ``Prod
  uvars := 2
  type := vconst(type_of% @Prod).type
  ctors := [⟨vconst(type_of% @Prod.mk), ``Prod.mk⟩]

def prodDecl : VInductDecl := ⟨2, 2, [prodType]⟩

example : prodDecl.stage3 = true := rfl

example : recConst 2 ``Prod 2 prodType =
    permC (vconst(type_of% @Prod.rec)) [.param 1, .param 2, .param 0] := rfl

example : (rules 2 ``Prod 2 prodType)[0]? =
    some (permE (vdefeq(α β motive mk a b =>
        @Prod.rec α β motive mk (@Prod.mk α β a b) ≡ mk a b))
      [.param 1, .param 2, .param 0]) := rfl

/-! ## Option: one parameter, two constructors -/

def optionType : VInductiveType where
  name := ``Option
  uvars := 1
  type := vconst(type_of% @Option).type
  ctors := [⟨vconst(type_of% @Option.none), ``Option.none⟩,
    ⟨vconst(type_of% @Option.some), ``Option.some⟩]

def optionDecl : VInductDecl := ⟨1, 1, [optionType]⟩

example : optionDecl.stage3 = true := rfl

example : recConst 1 ``Option 1 optionType =
    permC (vconst(type_of% @Option.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``Option 1 optionType)[0]? =
    some (permE (vdefeq(α motive n s => @Option.rec α motive n s (@Option.none α) ≡ n))
      [.param 1, .param 0]) := rfl

example : (rules 1 ``Option 1 optionType)[1]? =
    some (permE (vdefeq(α motive n s a => @Option.rec α motive n s (@Option.some α a) ≡ s a))
      [.param 1, .param 0]) := rfl

/-! ## Eq: parameters, one index, Prop-valued with subsingleton
elimination -/

def eqType : VInductiveType where
  name := ``Eq
  uvars := 1
  type := vconst(type_of% @Eq).type
  ctors := [⟨vconst(type_of% @Eq.refl), ``Eq.refl⟩]

def eqDecl : VInductDecl := ⟨1, 2, [eqType]⟩

example : eqDecl.stage3 = true := rfl

def eqChecked : eqDecl.Checked := eqDecl.checked?.get (by decide)

def eqGenerationChecked : GenerationChecked eqDecl :=
  (identityGeneration? eqDecl).get (by decide)

example : eqChecked.params = [.sort (.param 0), .bvar 0] := rfl
example : eqChecked.indices = [.bvar 1] := rfl
example : eqChecked.resultLevel = .zero := rfl
example : eqChecked.elimination = .large := rfl
example : eqChecked.kTarget = true := rfl
example : eqGenerationChecked.kTarget = true := rfl
example : eqChecked.constructors[0].resultIndices = [.bvar 0] := rfl
example : eqChecked.recursor = recConst 1 ``Eq 2 eqType := rfl
example : eqGenerationChecked.motiveType = eqChecked.motiveType := rfl
example : eqGenerationChecked.minorTypes = eqChecked.minorTypes := rfl
example : eqGenerationChecked.recursor = eqChecked.recursor := rfl
example : eqGenerationChecked.generatedRules = eqChecked.generatedRules := rfl

/-- The generated recursor is exactly the kernel's `Eq.rec`. -/
example : recConst 1 ``Eq 2 eqType =
    permC (vconst(type_of% @Eq.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``Eq 2 eqType)[0]? =
    some (permE (vdefeq(α a motive r =>
      @Eq.rec α a motive r a (@Eq.refl α a) ≡ r)) [.param 1, .param 0]) := rfl

example : (VEnv.empty.addInduct eqDecl).isSome = true := rfl

/-! ## HEq: two indices, one of them a sort -/

def heqType : VInductiveType where
  name := ``HEq
  uvars := 1
  type := vconst(type_of% @HEq).type
  ctors := [⟨vconst(type_of% @HEq.refl), ``HEq.refl⟩]

def heqDecl : VInductDecl := ⟨1, 2, [heqType]⟩

example : heqDecl.stage3 = true := rfl

example : recConst 1 ``HEq 2 heqType =
    permC (vconst(type_of% @HEq.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``HEq 2 heqType)[0]? =
    some (permE (vdefeq((α : Sort u) (a : α)
        (motive : {β : Sort u} → (b : β) → HEq a b → Sort v)
        (r : @motive α a (@HEq.refl α a)) =>
      @HEq.rec α a (@motive) r α a (@HEq.refl α a) ≡ r)) [.param 1, .param 0]) := rfl

/-! ## IndexedVec: recursive occurrence at a changing index -/

inductive IndexedVec (α : Type u) : Nat → Type u where
  | nil : IndexedVec α Nat.zero
  | cons {n} : α → IndexedVec α n → IndexedVec α (Nat.succ n)

def indexedVecType : VInductiveType where
  name := ``IndexedVec
  uvars := 1
  type := vconst(type_of% @IndexedVec).type
  ctors := [⟨vconst(type_of% @IndexedVec.nil), ``IndexedVec.nil⟩,
    ⟨vconst(type_of% @IndexedVec.cons), ``IndexedVec.cons⟩]

def indexedVecDecl : VInductDecl := ⟨1, 1, [indexedVecType]⟩

example : indexedVecDecl.stage3 = true := rfl

def indexedVecChecked : indexedVecDecl.Checked :=
  indexedVecDecl.checked?.get (by decide)

def indexedVecGenerationChecked : GenerationChecked indexedVecDecl :=
  (identityGeneration? indexedVecDecl).get (by decide)

example : indexedVecChecked.params = [.sort (.succ (.param 0))] := rfl
example : indexedVecChecked.indices = [.const ``Nat []] := rfl
example : indexedVecChecked.resultLevel = .succ (.param 0) := rfl
example : indexedVecChecked.elimination = .large := rfl
example : indexedVecChecked.constructors.length = 2 := rfl
example : indexedVecChecked.constructors[1].fields.length = 3 := rfl
example : indexedVecChecked.constructors[1].recursive.length = 1 := rfl
example : indexedVecChecked.constructors[1].recursive[0].fieldIndex = 2 := rfl
example : indexedVecChecked.constructors[1].recursive[0].binders = [] := rfl
example : indexedVecChecked.constructors[1].recursive[0].targetType = 0 := rfl
example : indexedVecChecked.constructors[1].recursive[0].indices = [.bvar 1] := rfl
example : indexedVecChecked.constructors[1].resultIndices =
    [VExpr.app (VExpr.const ``Nat.succ []) (VExpr.bvar 2)] := rfl
example : indexedVecChecked.recursor =
    recConst 1 ``IndexedVec 1 indexedVecType := rfl
example : indexedVecChecked.generatedRules =
    rules 1 ``IndexedVec 1 indexedVecType := rfl
example : indexedVecGenerationChecked.motiveType =
    indexedVecChecked.motiveType := rfl
example : indexedVecGenerationChecked.minorTypes =
    indexedVecChecked.minorTypes := rfl
example : indexedVecGenerationChecked.recursor =
    indexedVecChecked.recursor := rfl
example : indexedVecGenerationChecked.generatedRules =
    indexedVecChecked.generatedRules := rfl

/-- Semantic clients can migrate from the legacy declaration-level contract
to the normalized descriptor without re-analyzing its syntax. -/
example {env : VEnv} (h : indexedVecDecl.WF env) :
    indexedVecChecked.WF env :=
  indexedVecChecked.wf_of_decl h

/-- The descriptor contract remains definitionally compatible with existing
preservation clients while that migration is in progress. -/
example {env : VEnv} (h : indexedVecChecked.WF env) :
    indexedVecDecl.WF env :=
  indexedVecChecked.to_declWF rfl h

example : recConst 1 ``IndexedVec 1 indexedVecType =
    permC (vconst(type_of% @IndexedVec.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``IndexedVec 1 indexedVecType)[0]? =
    some (permE (vdefeq((α : Type u)
      (motive : (n : Nat) → IndexedVec α n → Sort v)
      (nil : motive Nat.zero (@IndexedVec.nil α))
      (cons : {n : Nat} → (a : α) → (as : IndexedVec α n) →
        motive n as → motive (Nat.succ n) (@IndexedVec.cons α n a as)) =>
      @IndexedVec.rec α motive nil (@cons) Nat.zero (@IndexedVec.nil α) ≡ nil))
      [.param 1, .param 0]) := rfl

example : (rules 1 ``IndexedVec 1 indexedVecType)[1]? =
    some (permE (vdefeq((α : Type u)
      (motive : (n : Nat) → IndexedVec α n → Sort v)
      (nil : motive Nat.zero (@IndexedVec.nil α))
      (cons : {n : Nat} → (a : α) → (as : IndexedVec α n) →
        motive n as → motive (Nat.succ n) (@IndexedVec.cons α n a as))
      (n : Nat) (a : α) (as : IndexedVec α n) =>
      @IndexedVec.rec α motive nil (@cons) (Nat.succ n)
          (@IndexedVec.cons α n a as) ≡
        @cons n a as (@IndexedVec.rec α motive nil (@cons) n as)))
      [.param 1, .param 0]) := rfl

example : (VEnv.empty.addInduct indexedVecDecl).isSome = true := rfl

/-- Consumers obtain constructor lookup without unfolding the transactional
constructor fold. -/
example : ∀ env', VEnv.empty.addInduct indexedVecDecl = some env' →
    env'.constants ``IndexedVec.cons = some indexedVecType.ctors[1].toVConstant := by
  intro env' hadd
  exact VEnv.addInduct_ctor_lookup hadd (.head _) (.tail _ (.head _))

/-- The complete all-or-nothing postcondition is available from the same
successful call. -/
example : ∀ env', VEnv.empty.addInduct indexedVecDecl = some env' →
    VEnv.AddInductSuccess VEnv.empty env' indexedVecDecl :=
  fun _ => VEnv.addInduct_success

/-- The transaction certificate exposes the exact block-generation result for
ix-like consumers without re-running structural analysis. -/
example : ∀ env', VEnv.empty.addInduct indexedVecDecl = some env' →
    ∃ generation,
      indexedVecDecl.identityBlockGeneration? = some generation :=
  fun _ => VEnv.addInduct_generation

/-! ## Acc: recursive argument beneath a Pi telescope

`Acc.intro`'s recursive field is a function taking two arguments, and its
induction hypothesis is itself a two-argument function. This fixture exercises
the complete public checked/generation/transaction path, not a side generator. -/

def accType : VInductiveType where
  name := ``Acc
  uvars := 1
  type := vconst(type_of% @Acc).type
  ctors := [⟨vconst(type_of% @Acc.intro), ``Acc.intro⟩]

def accDecl : VInductDecl := ⟨1, 2, [accType]⟩

example : accDecl.stage3 = true := rfl

def accChecked : accDecl.Checked := accDecl.checked?.get (by decide)

def accGenerationChecked : GenerationChecked accDecl :=
  (identityGeneration? accDecl).get (by decide)

def accBlockGenerationChecked : BlockGenerationChecked accDecl :=
  (identityBlockGeneration? accDecl).get (by decide)

def accRecArgs : List RecArg :=
  recArgs 1 ``Acc 2 1 (ctorFields (VExpr.dropN 2 accType.ctors[0].type))

example : (ctorFields (VExpr.dropN 2 accType.ctors[0].type)).length = 2 := rfl
example : accRecArgs.length = 1 := rfl
example : accRecArgs[0].fieldIndex = 1 := rfl
example : accRecArgs[0].binders.length = 2 := rfl
example : accRecArgs[0].targetType = 0 := rfl
example : accRecArgs[0].indices = [.bvar 1] := rfl
example : accChecked.type = accType := rfl
example : accChecked.constructors[0].recursive = accRecArgs := rfl
example : accChecked.recursor = recConstRec 1 ``Acc 2 accType := rfl
example : accChecked.generatedRules = rulesRec 1 ``Acc 2 accType := rfl
example : accGenerationChecked.motiveType = accChecked.motiveType := rfl
example : accGenerationChecked.minorTypes = accChecked.minorTypes := rfl
example : accGenerationChecked.recursor = accChecked.recursor := rfl
example : accGenerationChecked.generatedRules = accChecked.generatedRules := rfl

/-- The generalized recursor type is definitionally the kernel's `Acc.rec`,
including its functional induction hypothesis. -/
example : recConstRec 1 ``Acc 2 accType =
    permC (vconst(type_of% @Acc.rec)) [.param 1, .param 0] := rfl

/-- The generalized iota RHS recurs under both binders of the recursive
function argument, exactly as Lean's kernel rule does. -/
example : (rulesRec 1 ``Acc 2 accType)[0]? =
    some (permE (vdefeq((α : Sort u) (r : α → α → Prop)
      (motive : (a : α) → Acc r a → Sort v)
      (intro : (a : α) → (h : (b : α) → r b a → Acc r b) →
        ((b : α) → (hba : r b a) → motive b (h b hba)) →
        motive a (@Acc.intro α r a h))
      (a : α) (h : (b : α) → r b a → Acc r b) =>
      @Acc.rec α r motive intro a (@Acc.intro α r a h) ≡
        intro a h (fun b hba => @Acc.rec α r motive intro b (h b hba))))
      [.param 1, .param 0]) := rfl

/-- Recursive-Pi declarations now run through the same all-or-nothing public
transaction as direct recursive declarations. -/
example : (VEnv.empty.addInduct accDecl).isSome = true := rfl

example : (VEnv.empty.addInduct accDecl).map (·.constants ``Acc.rec) =
    some (some (recConstRec 1 ``Acc 2 accType)) := rfl

example : ∀ env', VEnv.empty.addInduct accDecl = some env' →
    env'.defeqs (ruleRec 1 ``Acc 2 accType 0 accType.ctors[0]) := by
  intro env' hadd
  apply VEnv.addInduct_rule_mem hadd
    (generation := accBlockGenerationChecked) rfl
  change ruleRec 1 ``Acc 2 accType 0 accType.ctors[0] ∈
    accBlockGenerationChecked.generatedRules
  exact .head _

example : ∀ env', VEnv.empty.addInduct accDecl = some env' →
    VEnv.AddInductSuccess VEnv.empty env' accDecl :=
  fun _ => VEnv.addInduct_success

/-- `Acc` satisfies the semantic declaration contract, including the
impredicative-Prop exception for its universe-polymorphic index field and the
typed telescope beneath its recursive Pi argument. -/
theorem accDecl_wf : accDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = accType := List.mem_singleton.1 (by simpa [accDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change VEnv.empty.OnTel 1 []
      [.sort (.param 0),
        .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
        .bvar 1]
    exact ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, trivial⟩⟩⟩
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    constructor
    · change fieldsWF 1 ``Acc 2 VEnv.empty .zero [.bvar 1]
        [.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort (.param 0)] 0
        [.bvar 1,
          .forallE (.bvar 2)
            (.forallE (.app (.app (.bvar 2) (.bvar 0)) (.bvar 1))
              (.app (.app (.app (.const ``Acc [.param 0]) (.bvar 4)) (.bvar 3))
                (.bvar 1)))]
      refine ⟨?_, ?_, ?_⟩
      · exact .inr (.inr ⟨rfl, .param 0, by type_tac, .inl rfl⟩)
      · intro h
        change false = true at h
        contradiction
      · dsimp only [fieldsWF]
        refine ⟨?_, ?_, trivial⟩
        · refine .inr (.inl ⟨accRecArgs[0], rfl, ?_, ?_⟩)
          · decide
          · change
              VEnv.empty.OnTel 1
                  [.bvar 1,
                    .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
                    .sort (.param 0)]
                  [.bvar 2, .app (.app (.bvar 2) (.bvar 0)) (.bvar 1)] ∧
                VEnv.empty.SpineWF 1
                  [.app (.app (.bvar 2) (.bvar 0)) (.bvar 1), .bvar 2,
                    .bvar 1,
                    .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
                    .sort (.param 0)]
                  (.forallE (.bvar 4) (.sort .zero)) [.bvar 1] (.sort .zero)
            constructor
            · exact ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, trivial⟩⟩
            · exact .cons (by type_tac) .nil
        · intro h
          change false = true at h
          contradiction
    · change VEnv.empty.SpineWF 1
        [.forallE (.bvar 2)
            (.forallE (.app (.app (.bvar 2) (.bvar 0)) (.bvar 1))
              (.app (.app (.app (.const ``Acc [.param 0]) (.bvar 4)) (.bvar 3))
                (.bvar 1))),
          .bvar 1,
          .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
          .sort (.param 0)]
        (.forallE (.bvar 3) (.sort .zero)) [.bvar 1] (.sort .zero)
      exact .cons (by type_tac) .nil

/-- The concrete public Acc transaction preserves environment order. -/
def accEnv : VEnv := (VEnv.empty.addInduct accDecl).get (by decide)

example : accEnv.Ordered :=
  VEnv.addInductGeneration_WF .empty
    ((accChecked.wf_of_decl accDecl_wf).identityGeneration .empty) rfl

/-- A collision at the generated recursor name still rejects the whole Acc
transaction; no recursive-Pi special case bypasses freshness. -/
def accRecCollisionEnv : VEnv :=
  (VEnv.empty.addConst ``Acc.rec ⟨0, .sort .zero⟩).get (by decide)

example : accRecCollisionEnv.addInduct accDecl = none :=
  VEnv.addInduct_eq_none_of_rec_present
    (generation := accBlockGenerationChecked) rfl (.head _) ⟨_, rfl⟩

/-! ## AnnotatedPi: recursive Pi normalization below a constructor field

Lean retains `outParam` in the constructor's raw recursive-function domain,
while inductive analysis consumes it before recognizing the recursive target.
This fixture combines the annotation and recursive-Pi seams in one declaration
and keeps the raw binder syntax in generated artifacts. -/

inductive AnnotatedPi : Type where
  | mk : ((p : outParam Prop) → AnnotatedPi) → AnnotatedPi

def outParamDefEq : VDefEq :=
  vdefeq(@outParam ≡ fun (α : Sort u) => α)

def outParamConstEnv : VEnv :=
  (VEnv.empty.addConst ``outParam (vconst(type_of% @outParam))).get
    (by decide)

def outParamEnv : VEnv := outParamConstEnv.addDefEq outParamDefEq

theorem outParamConstant_wf :
    (vconst(type_of% @outParam) : VConstant).WF VEnv.empty := by
  exact ⟨_, VEnv.HasType.forallE
    (VEnv.HasType.sort (by decide))
    (VEnv.HasType.sort (by decide))⟩

theorem outParamConstEnv_ordered : outParamConstEnv.Ordered := by
  apply VEnv.Ordered.const VEnv.Ordered.empty
    (ci := vconst(type_of% @outParam))
  · exact outParamConstant_wf
  · rfl

theorem outParamEnv_ordered : outParamEnv.Ordered := by
  apply VEnv.Ordered.defeq outParamConstEnv_ordered
  constructor
  · exact VEnv.HasType.const0 rfl
      (outParamConstant_wf.mono
        (VEnv.addConst_le (by rfl :
          VEnv.empty.addConst ``outParam (vconst(type_of% @outParam)) =
            some outParamConstEnv)))
  · exact VEnv.HasType.lam
      (VEnv.HasType.sort (by decide))
      (VEnv.HasType.bvar .zero)

def annotatedPiRawType : VInductiveType where
  name := ``AnnotatedPi
  uvars := 0
  type := vconst(type_of% @AnnotatedPi).type
  ctors := [⟨vconst(type_of% @AnnotatedPi.mk), ``AnnotatedPi.mk⟩]

def annotatedPiRawDecl : VInductDecl := ⟨0, 0, [annotatedPiRawType]⟩

def annotatedPiViewCtor : VConstVal where
  name := ``AnnotatedPi.mk
  uvars := 0
  type := .forallE
    (.forallE (.sort .zero) (.const ``AnnotatedPi []))
    (.const ``AnnotatedPi [])

def annotatedPiViewType : VInductiveType :=
  { annotatedPiRawType with ctors := [annotatedPiViewCtor] }

def annotatedPiViewDecl : VInductDecl := ⟨0, 0, [annotatedPiViewType]⟩

example : annotatedPiRawType.ctors[0].type =
    .forallE
      (.forallE
        (.app (.const ``outParam [.succ .zero]) (.sort .zero))
        (.const ``AnnotatedPi []))
      (.const ``AnnotatedPi []) := rfl

example : annotatedPiViewDecl.checked?.isSome = true := rfl
example : normalizationShape annotatedPiRawDecl annotatedPiViewDecl = true :=
  rfl

def annotatedPiNormalization : Normalization annotatedPiRawDecl where
  view := annotatedPiViewDecl
  shape_eq := rfl

def annotatedPiViewChecked : annotatedPiViewDecl.Checked :=
  annotatedPiViewDecl.checked?.get (by decide)

def annotatedPiBlock : NormalizedChecked annotatedPiRawDecl :=
  annotatedPiNormalization.check?.get (by decide)

def annotatedPiGenerationChecked : GenerationChecked annotatedPiRawDecl :=
  annotatedPiBlock.generation?.get (by decide)

def annotatedPiRecArg : RecArg where
  fieldIndex := 0
  binders := [.sort .zero]
  targetType := 0
  indices := []

example : annotatedPiViewChecked.constructors[0].recursive =
    [annotatedPiRecArg] := rfl

example : annotatedPiGenerationChecked.block.ctorPairs[0].rawFields 0 =
    [.forallE
      (.app (.const ``outParam [.succ .zero]) (.sort .zero))
      (.const ``AnnotatedPi [])] := rfl

example : annotatedPiGenerationChecked.recursor =
    vconst(type_of% @AnnotatedPi.rec) := rfl

example : annotatedPiGenerationChecked.generatedRules[0].rhs =
    (vdefeq((motive : AnnotatedPi → Sort u)
      (mk : (f : (p : outParam Prop) → AnnotatedPi) →
        ((p : Prop) → motive (f p)) → motive (@AnnotatedPi.mk f))
      (f : (p : outParam Prop) → AnnotatedPi) =>
      @AnnotatedPi.rec motive mk (@AnnotatedPi.mk f) ≡
        mk f (fun p => @AnnotatedPi.rec motive mk (f p)))).rhs := rfl

/-- The normalized recursive-Pi view is semantically well formed without
using the annotation definition; the raw-to-view bridge is supplied later by
the exact checker candidate. -/
theorem annotatedPiViewDecl_wf : annotatedPiViewDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = annotatedPiViewType :=
    List.mem_singleton.1 (by simpa [annotatedPiViewDecl] using hty)
  subst ty
  refine ⟨by trivial, ?_⟩
  intro c hc
  have hc' : c = annotatedPiViewCtor :=
    List.mem_singleton.1 (by simpa [annotatedPiViewType] using hc)
  subst c
  constructor
  · change fieldsWF 0 ``AnnotatedPi 0 VEnv.empty (.succ .zero) [] [] 0
      [.forallE (.sort .zero) (.const ``AnnotatedPi [])]
    refine ⟨?_, ?_, trivial⟩
    · right
      left
      refine ⟨annotatedPiRecArg, ?_, ?_, ?_⟩
      · rfl
      · simp [annotatedPiRecArg]
      · exact ⟨⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩, .nil⟩
    · intro h
      change false = true at h
      contradiction
  · change VEnv.empty.SpineWF 0
      [.forallE (.sort .zero) (.const ``AnnotatedPi [])]
      (.sort (.succ .zero)) [] (.sort (.succ .zero))
    exact .nil

theorem annotatedPiViewChecked_wf :
    annotatedPiViewChecked.WF outParamEnv := by
  apply VInductDecl.Checked.WF.mono
    ((VEnv.addConst_le (by rfl :
      VEnv.empty.addConst ``outParam (vconst(type_of% @outParam)) =
        some outParamConstEnv)).trans VEnv.addDefEq_le)
  exact annotatedPiViewChecked.wf_of_decl annotatedPiViewDecl_wf

/-! ## AnnotatedParam: definitionally equal constructor parameters

Family validation consumes the `outParam` annotation before recording its
parameter local. Constructor metadata retains the annotation, so the ordinary
validator must use definitional equality rather than syntax when it checks the
constructor's parameter prefix. -/

inductive AnnotatedParam (alpha : outParam Type) : Type where
  | mk : AnnotatedParam alpha

def annotatedParamRawType : VInductiveType where
  name := ``AnnotatedParam
  uvars := 0
  type := vconst(type_of% @AnnotatedParam).type
  ctors := [⟨vconst(type_of% @AnnotatedParam.mk), ``AnnotatedParam.mk⟩]

def annotatedParamRawDecl : VInductDecl :=
  ⟨0, 1, [annotatedParamRawType]⟩

def annotatedParamViewCtor : VConstVal where
  name := ``AnnotatedParam.mk
  uvars := 0
  type := .forallE (.sort (.succ .zero))
    (.app (.const ``AnnotatedParam []) (.bvar 0))

def annotatedParamViewType : VInductiveType where
  name := ``AnnotatedParam
  uvars := 0
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  ctors := [annotatedParamViewCtor]

def annotatedParamViewDecl : VInductDecl :=
  ⟨0, 1, [annotatedParamViewType]⟩

example : annotatedParamRawType.type =
    .forallE
      (.app (.const ``outParam [.succ (.succ .zero)])
        (.sort (.succ .zero)))
      (.sort (.succ .zero)) := rfl

example : annotatedParamRawType.ctors[0].type =
    .forallE
      (.app (.const ``outParam [.succ (.succ .zero)])
        (.sort (.succ .zero)))
      (.app (.const ``AnnotatedParam []) (.bvar 0)) := rfl

example : annotatedParamViewDecl.checked?.isSome = true := rfl
example : normalizationShape annotatedParamRawDecl annotatedParamViewDecl =
    true := rfl

def annotatedParamNormalization : Normalization annotatedParamRawDecl where
  view := annotatedParamViewDecl
  shape_eq := rfl

def annotatedParamViewChecked : annotatedParamViewDecl.Checked :=
  annotatedParamViewDecl.checked?.get (by decide)

def annotatedParamBlock : NormalizedChecked annotatedParamRawDecl :=
  annotatedParamNormalization.check?.get (by decide)

def annotatedParamGenerationChecked :
    GenerationChecked annotatedParamRawDecl :=
  annotatedParamBlock.generation?.get (by decide)

example : annotatedParamGenerationChecked.recursor =
    vconst(type_of% @AnnotatedParam.rec) := rfl

example : annotatedParamGenerationChecked.generatedRules[0]? =
    some (vdefeq((alpha : Type)
      (motive : AnnotatedParam alpha → Sort u)
      (mk : motive (@AnnotatedParam.mk alpha)) =>
      @AnnotatedParam.rec alpha motive mk (@AnnotatedParam.mk alpha) ≡ mk)) := rfl

/-- The raw parameter domain retained by kernel metadata before annotation
consumption. -/
def annotatedParamRawDomain : VExpr :=
  .app (.const ``outParam [.succ (.succ .zero)])
    (.sort (.succ .zero))

/-- The stored `outParam Type` parameter and the checked `Type` parameter are
definitionally equal in the exact pre-declaration environment. -/
theorem annotatedParamRawDomain_defeq :
    outParamEnv.IsDefEq 0 [] annotatedParamRawDomain
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  have hfn : outParamEnv.IsDefEq 0 []
      (.const ``outParam [.succ (.succ .zero)])
      (.lam (.sort (.succ (.succ .zero))) (.bvar 0))
      (.forallE (.sort (.succ (.succ .zero)))
        (.sort (.succ (.succ .zero)))) := by
    simpa [outParamDefEq, VExpr.instL, VLevel.inst] using
      (VEnv.IsDefEq.extra (env := outParamEnv) (uvars := 0) (Γ := [])
        (df := outParamDefEq) (ls := [.succ (.succ .zero)])
        (by simp [outParamEnv, VEnv.addDefEq])
        (by simp; decide) rfl)
  have harg : outParamEnv.HasType 0 []
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    VEnv.HasType.sort (by decide)
  exact (VEnv.IsDefEq.appDF hfn harg).trans
    (VEnv.IsDefEq.beta (VEnv.HasType.bvar .zero) harg)

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.annotatedParamRawDomain_defeq [propext, Quot.sound]

/-- The annotation-consumed declaration accepted by the structural analyzer
has the ordinary direct semantic interpretation. -/
theorem annotatedParamViewDecl_wf :
    annotatedParamViewDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = annotatedParamViewType :=
    List.mem_singleton.1 (by
      simpa [annotatedParamViewDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change VEnv.OnTel VEnv.empty 0 [] [.sort (.succ .zero)]
    exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · intro c hc
    have hc' : c = annotatedParamViewCtor :=
      List.mem_singleton.1 (by
        simpa [annotatedParamViewType] using hc)
    subst c
    exact ⟨trivial, .nil⟩

/-- Exact Theory environment after staging the stored family constant. -/
def annotatedParamTypeEnv : VEnv :=
  (outParamEnv.addConst annotatedParamRawType.name
    annotatedParamRawType.toVConstant).get (by decide)

theorem annotatedParamTypeEnv_ordered :
    annotatedParamTypeEnv.Ordered := by
  have hbody : outParamEnv.HasType 0 [annotatedParamRawDomain]
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    VEnv.HasType.sort (by decide)
  apply VEnv.Ordered.const (n := annotatedParamRawType.name)
    (ci := annotatedParamRawType.toVConstant)
    outParamEnv_ordered
  · exact ⟨.imax (.succ (.succ .zero)) (.succ (.succ .zero)),
      VEnv.HasType.forallE
        (VEnv.IsDefEq.hasType annotatedParamRawDomain_defeq).1 hbody⟩
  · rfl

private theorem annotatedParamFamilyApp_hasType (domain : VExpr)
    (hdomain : annotatedParamTypeEnv.HasType 0 [domain]
      (.bvar 0) annotatedParamRawDomain) :
    annotatedParamTypeEnv.HasType 0 [domain]
      (.app (.const ``AnnotatedParam []) (.bvar 0))
      (.sort (.succ .zero)) := by
  apply VEnv.HasType.app
    (A := annotatedParamRawDomain) (B := .sort (.succ .zero))
  · simpa [annotatedParamRawType, annotatedParamRawDomain,
        VExpr.instL, VLevel.inst] using
      VEnv.HasType.const (env := annotatedParamTypeEnv) (U := 0)
        (Γ := [domain]) (c := ``AnnotatedParam)
        (ci := annotatedParamRawType.toVConstant) (ls := [])
        (VEnv.addConst_self (show
          outParamEnv.addConst annotatedParamRawType.name
            annotatedParamRawType.toVConstant =
              some annotatedParamTypeEnv from rfl))
        (by simp) rfl
  · exact hdomain

theorem annotatedParamRawCtorBody_hasType :
    annotatedParamTypeEnv.HasType 0 [annotatedParamRawDomain]
      (.app (.const ``AnnotatedParam []) (.bvar 0))
      (.sort (.succ .zero)) := by
  apply annotatedParamFamilyApp_hasType
  simpa [annotatedParamRawDomain, VExpr.liftN] using
    (VEnv.HasType.bvar (env := annotatedParamTypeEnv) (U := 0)
      (Lookup.zero (Γ := []) (ty := annotatedParamRawDomain)))

theorem annotatedParamCheckedCtorBody_hasType :
    annotatedParamTypeEnv.HasType 0 [.sort (.succ .zero)]
      (.app (.const ``AnnotatedParam []) (.bvar 0))
      (.sort (.succ .zero)) := by
  apply annotatedParamFamilyApp_hasType
  have hb : annotatedParamTypeEnv.HasType 0 [.sort (.succ .zero)]
      (.bvar 0) (.sort (.succ .zero)) := by
    simpa [VExpr.liftN] using
      (VEnv.HasType.bvar (env := annotatedParamTypeEnv) (U := 0)
        (Lookup.zero (Γ := []) (ty := .sort (.succ .zero))))
  have hd := annotatedParamRawDomain_defeq.mono
    (VEnv.addConst_le (show
      outParamEnv.addConst annotatedParamRawType.name
        annotatedParamRawType.toVConstant =
          some annotatedParamTypeEnv from rfl))
  exact (hd.weak0 annotatedParamTypeEnv_ordered).symm.defeq hb

/-- The raw family and constructor metadata are semantically related to the
annotation-consumed analyzer view at their exact declaration stages. -/
theorem annotatedParamNormalization_wf :
    annotatedParamNormalization.WF outParamEnv := by
  refine ⟨annotatedParamRawType, annotatedParamViewType,
    rfl, rfl, ?_, ?_⟩
  · have hbody : outParamEnv.HasType 0 [annotatedParamRawDomain]
        (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
      VEnv.HasType.sort (by decide)
    exact ⟨_, VEnv.IsDefEq.forallEDF
      annotatedParamRawDomain_defeq hbody⟩
  · intro envT hadd
    have henv : envT = annotatedParamTypeEnv := by
      have : some envT = some annotatedParamTypeEnv :=
        hadd.symm.trans (show
          outParamEnv.addConst annotatedParamRawType.name
            annotatedParamRawType.toVConstant =
              some annotatedParamTypeEnv from rfl)
      exact Option.some.inj this
    subst envT
    exact .cons ⟨_, VEnv.IsDefEq.forallEDF
      (annotatedParamRawDomain_defeq.mono
        (VEnv.addConst_le (show
          outParamEnv.addConst annotatedParamRawType.name
            annotatedParamRawType.toVConstant =
              some annotatedParamTypeEnv from rfl)))
      annotatedParamRawCtorBody_hasType⟩ .nil

theorem annotatedParamViewChecked_wf :
    annotatedParamViewChecked.WF outParamEnv := by
  apply VInductDecl.Checked.WF.mono
    ((VEnv.addConst_le (by rfl :
      VEnv.empty.addConst ``outParam (vconst(type_of% @outParam)) =
        some outParamConstEnv)).trans VEnv.addDefEq_le)
  exact annotatedParamViewChecked.wf_of_decl annotatedParamViewDecl_wf

/-- The mixed generation value uses the checked parameter for emitted
recursor binders while retaining the raw constructor surface, and all four
raw/view telescope/result obligations hold in their respective contexts. -/
theorem annotatedParamGenerationChecked_wf :
    annotatedParamGenerationChecked.WF outParamEnv := by
  refine {
    blockWF := ⟨annotatedParamNormalization_wf,
      annotatedParamViewChecked_wf⟩
    familyTel := ?_
    familyResult := ?_
    ctors := ?_ }
  · change outParamEnv.TelDefEq 0 [] [annotatedParamRawDomain]
      [.sort (.succ .zero)]
    exact ⟨⟨_, annotatedParamRawDomain_defeq⟩, trivial⟩
  · exact VEnv.HasType.sort (by decide)
  · intro envT hadd ctor hctor
    have henv : envT = annotatedParamTypeEnv := by
      have : some envT = some annotatedParamTypeEnv :=
        hadd.symm.trans (show
          outParamEnv.addConst annotatedParamRawType.name
            annotatedParamRawType.toVConstant =
              some annotatedParamTypeEnv from rfl)
      exact Option.some.inj this
    subst envT
    change ctor ∈ [⟨annotatedParamRawType.ctors[0],
      annotatedParamViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    refine {
      declaredTel := ⟨⟨_, annotatedParamRawDomain_defeq.mono
        (VEnv.addConst_le (show
          outParamEnv.addConst annotatedParamRawType.name
            annotatedParamRawType.toVConstant =
              some annotatedParamTypeEnv from rfl))⟩, trivial⟩
      declaredResult := annotatedParamRawCtorBody_hasType
      emittedTel := ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
      emittedResult := annotatedParamCheckedCtorBody_hasType }

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.annotatedParamGenerationChecked_wf [propext, Quot.sound]

/-! ## Explicit normalization boundary

Lean stores reducible aliases in inductive metadata even though
`checkInductiveTypes`, positivity, and recursive-argument recognition inspect
their WHNF. These kernel-accepted declarations demonstrate why raw metadata
cannot simply be assumed normalized. Their explicit views exercise the new
environment-independent `Normalization` boundary; semantic defeq evidence and
raw-syntax-preserving artifact generation remain separate obligations.
-/

abbrev TypeFamilyAlias := Type

inductive AliasFormer : TypeFamilyAlias where
  | mk : AliasFormer

def aliasFormerRawType : VInductiveType where
  name := ``AliasFormer
  uvars := 0
  type := vconst(type_of% @AliasFormer).type
  ctors := [⟨vconst(type_of% @AliasFormer.mk), ``AliasFormer.mk⟩]

def aliasFormerRawDecl : VInductDecl := ⟨0, 0, [aliasFormerRawType]⟩

example : aliasFormerRawType.type = .const ``TypeFamilyAlias [] := rfl
example : aliasFormerRawDecl.checked? = none := rfl

def aliasFormerViewType : VInductiveType :=
  { aliasFormerRawType with type := .sort (.succ .zero) }

def aliasFormerViewDecl : VInductDecl := ⟨0, 0, [aliasFormerViewType]⟩

example : aliasFormerViewDecl.checked?.isSome = true := rfl
example : normalizationShape aliasFormerRawDecl aliasFormerViewDecl = true := rfl

def aliasFormerNormalization : Normalization aliasFormerRawDecl where
  view := aliasFormerViewDecl
  shape_eq := rfl

def aliasFormerViewChecked : aliasFormerViewDecl.Checked :=
  aliasFormerViewDecl.checked?.get (by decide)

def aliasFormerBlock : NormalizedChecked aliasFormerRawDecl :=
  aliasFormerNormalization.check?.get (by decide)

def aliasFormerGenerationChecked : GenerationChecked aliasFormerRawDecl :=
  aliasFormerBlock.generation?.get (by decide)

example : aliasFormerNormalization.accepted = true := rfl
example : (normalizedChecked? aliasFormerRawDecl aliasFormerViewDecl).isSome = true := rfl
example : aliasFormerBlock.checked.type = aliasFormerViewType := rfl
example : aliasFormerGenerationChecked.recursor =
    vconst(type_of% @AliasFormer.rec) := rfl
example : aliasFormerGenerationChecked.generatedRules[0]? =
    some (vdefeq(motive mk =>
      @AliasFormer.rec motive mk AliasFormer.mk ≡ mk)) := rfl
example : ∃ raw,
    aliasFormerRawDecl.types = [raw] ∧
    raw.name = aliasFormerBlock.checked.type.name ∧
    raw.uvars = aliasFormerBlock.checked.type.uvars ∧
    List.Forall₂ CtorHeaderEq raw.ctors aliasFormerBlock.checked.type.ctors :=
  aliasFormerBlock.source_anatomy

def typeFamilyAliasDefEq : VDefEq := vdefeq(TypeFamilyAlias ≡ Type)

def typeFamilyAliasConstEnv : VEnv :=
  (VEnv.empty.addConst ``TypeFamilyAlias
    (vconst(type_of% @TypeFamilyAlias))).get (by decide)

def typeFamilyAliasEnv : VEnv :=
  typeFamilyAliasConstEnv.addDefEq typeFamilyAliasDefEq

theorem typeFamilyAliasConstant_wf :
    (vconst(type_of% @TypeFamilyAlias) : VConstant).WF
      VEnv.empty := by
  exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem typeFamilyAliasConstEnv_ordered :
    typeFamilyAliasConstEnv.Ordered := by
  apply VEnv.Ordered.const VEnv.Ordered.empty
    (ci := vconst(type_of% @TypeFamilyAlias))
  · exact typeFamilyAliasConstant_wf
  · rfl

theorem typeFamilyAliasEnv_ordered :
    typeFamilyAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq typeFamilyAliasConstEnv_ordered
  constructor
  · exact VEnv.HasType.const0 rfl
      (typeFamilyAliasConstant_wf.mono
        (VEnv.addConst_le (by rfl :
          VEnv.empty.addConst ``TypeFamilyAlias
            (vconst(type_of% @TypeFamilyAlias)) =
              some typeFamilyAliasConstEnv)))
  · exact VEnv.HasType.sort (by decide)

/-- The explicit family-type view is not merely shape-compatible: the stored
alias and its WHNF are definitionally equal in the pre-environment, and the
unchanged constructor remains equal after inserting the raw family constant.
-/
theorem aliasFormerNormalization_wf :
    aliasFormerNormalization.WF typeFamilyAliasEnv := by
  refine ⟨aliasFormerRawType, aliasFormerViewType, rfl, rfl, ?_, ?_⟩
  · refine ⟨_, .extra (df := typeFamilyAliasDefEq) (ls := []) ?_
      (fun _ h => nomatch h) rfl⟩
    simp [typeFamilyAliasEnv, VEnv.addDefEq]
  · intro envT hadd
    exact .cons
      ⟨_, .constDF (VEnv.addConst_self hadd) (by simp) (by simp) rfl .nil⟩
      .nil

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerNormalization_wf [propext, Quot.sound]

/-- The normalized view is a semantically well-formed direct declaration in
the same pre-environment. -/
theorem aliasFormerViewDecl_wf :
    aliasFormerViewDecl.WF typeFamilyAliasEnv := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = aliasFormerViewType :=
    List.mem_singleton.1 (by simpa [aliasFormerViewDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · trivial
  · intro c hc
    have hc' : c = aliasFormerRawType.ctors[0] :=
      List.mem_singleton.1 (by
        simpa [aliasFormerViewType, aliasFormerRawType] using hc)
    subst c
    exact ⟨trivial, .nil⟩

/-- The paired block carries both the semantic normalization certificate and
the checked normalized view required by downstream generation. -/
theorem aliasFormerBlock_wf : aliasFormerBlock.WF typeFamilyAliasEnv := by
  refine ⟨aliasFormerNormalization_wf, ?_⟩
  change aliasFormerViewChecked.WF typeFamilyAliasEnv
  exact aliasFormerViewChecked.wf_of_decl aliasFormerViewDecl_wf

theorem aliasFormerGenerationChecked_wf :
    aliasFormerGenerationChecked.WF typeFamilyAliasEnv := by
  refine {
    blockWF := aliasFormerBlock_wf
    familyTel := by trivial
    familyResult := ?_
    ctors := ?_ }
  · change typeFamilyAliasEnv.IsDefEq 0 []
      (.const ``TypeFamilyAlias []) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero)))
    exact .extra (df := typeFamilyAliasDefEq) (ls := [])
      (by simp [typeFamilyAliasEnv, VEnv.addDefEq])
      (fun _ h => nomatch h) rfl
  · intro envT hadd ctor hctor
    change ctor ∈
      [⟨aliasFormerRawType.ctors[0], aliasFormerViewChecked.constructors[0]⟩]
      at hctor
    obtain rfl := List.mem_singleton.1 hctor
    have hfamily₀ : envT.HasType 0 []
        (.const aliasFormerGenerationChecked.block.sourceType.name [])
        (aliasFormerGenerationChecked.block.sourceType.type.instL []) :=
      .const (VEnv.addConst_self hadd) (by simp) (by rfl)
    change envT.HasType 0 [] (.const ``AliasFormer [])
      (.const ``TypeFamilyAlias []) at hfamily₀
    have halias₀ : typeFamilyAliasEnv.IsDefEq 0 []
        (.const ``TypeFamilyAlias []) (.sort (.succ .zero))
        (.sort (.succ (.succ .zero))) :=
      .extra (df := typeFamilyAliasDefEq) (ls := [])
        (by simp [typeFamilyAliasEnv, VEnv.addDefEq])
        (fun _ h => nomatch h) rfl
    have halias := halias₀.mono (VEnv.addConst_le hadd)
    have hfamily : envT.IsDefEq 0 []
        (.const ``AliasFormer []) (.const ``AliasFormer [])
        (.sort (.succ .zero)) :=
      halias.defeq hfamily₀
    exact {
      declaredTel := by trivial
      declaredResult := hfamily
      emittedTel := by trivial
      emittedResult := hfamily }

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerBlock_wf [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerGenerationChecked_wf [propext, Quot.sound]

/-- The non-identity family-alias case executes the same normalized
transaction used by the public identity wrapper. -/
def aliasFormerFinalEnv : VEnv :=
  (typeFamilyAliasEnv.addInductGeneration
    aliasFormerGenerationChecked).get (by decide)

theorem aliasFormer_addInductGeneration :
    typeFamilyAliasEnv.addInductGeneration
      aliasFormerGenerationChecked =
        some aliasFormerFinalEnv := rfl

theorem aliasFormerFinalEnv_trace :
    Nonempty (VEnv.AddInductGenerationTrace
      typeFamilyAliasEnv aliasFormerFinalEnv
      aliasFormerGenerationChecked) :=
  VEnv.addInductGeneration_trace aliasFormer_addInductGeneration

theorem aliasFormerFinalEnv_le :
    typeFamilyAliasEnv ≤ aliasFormerFinalEnv := by
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.le

theorem aliasFormerFinalEnv_family_fresh :
    typeFamilyAliasEnv.constants ``AliasFormer = none := by
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.family_fresh

theorem aliasFormerFinalEnv_family_lookup :
    aliasFormerFinalEnv.constants ``AliasFormer =
      some aliasFormerRawType.toVConstant := by
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.family_lookup

theorem aliasFormerFinalEnv_ctor_fresh :
    ∀ c ∈ aliasFormerRawType.ctors,
      typeFamilyAliasEnv.constants c.name = none := by
  intro c hc
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.ctor_fresh hc

theorem aliasFormerFinalEnv_ctor_lookup :
    ∀ c ∈ aliasFormerRawType.ctors,
      aliasFormerFinalEnv.constants c.name =
        some c.toVConstant := by
  intro c hc
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.ctor_lookup hc

theorem aliasFormerFinalEnv_rec_fresh :
    typeFamilyAliasEnv.constants ``AliasFormer.rec = none := by
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.rec_fresh

theorem aliasFormerFinalEnv_rec_lookup :
    aliasFormerFinalEnv.constants ``AliasFormer.rec =
      some (vconst(type_of% @AliasFormer.rec)) := by
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.rec_lookup

theorem aliasFormerFinalEnv_rule_mem :
    ∀ df ∈ aliasFormerGenerationChecked.generatedRules,
      aliasFormerFinalEnv.defeqs df := by
  intro df hdf
  rcases aliasFormerFinalEnv_trace with ⟨H⟩
  exact H.rule_mem hdf

theorem aliasFormerFinalEnv_iota_mem :
    aliasFormerFinalEnv.defeqs
      (vdefeq(motive mk =>
        @AliasFormer.rec motive mk AliasFormer.mk ≡ mk)) := by
  apply aliasFormerFinalEnv_rule_mem
  exact .head _

theorem aliasFormerFinalEnv_ordered :
    aliasFormerFinalEnv.Ordered :=
  VEnv.addInductGeneration_WF
    typeFamilyAliasEnv_ordered
    aliasFormerGenerationChecked_wf
    aliasFormer_addInductGeneration

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerFinalEnv_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerFinalEnv_family_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerFinalEnv_ctor_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerFinalEnv_rec_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerFinalEnv_iota_mem [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasFormerFinalEnv_ordered [propext, Classical.choice, Quot.sound]

abbrev RecAlias (α : Sort u) := α

inductive AliasRec : Type where
  | mk : RecAlias AliasRec → AliasRec

def aliasRecRawType : VInductiveType where
  name := ``AliasRec
  uvars := 0
  type := vconst(type_of% @AliasRec).type
  ctors := [⟨vconst(type_of% @AliasRec.mk), ``AliasRec.mk⟩]

def aliasRecRawDecl : VInductDecl := ⟨0, 0, [aliasRecRawType]⟩

def aliasRecRawField : VExpr :=
  (VExpr.const ``RecAlias [.succ .zero]).app (VExpr.const ``AliasRec [])

example : ctorFields aliasRecRawType.ctors[0].type = [aliasRecRawField] := rfl
example : aliasRecRawDecl.checked? = none := rfl

def aliasRecViewCtor : VConstVal :=
  { aliasRecRawType.ctors[0] with
    type := .forallE (.const ``AliasRec []) (.const ``AliasRec []) }

def aliasRecViewType : VInductiveType :=
  { aliasRecRawType with ctors := [aliasRecViewCtor] }

def aliasRecViewDecl : VInductDecl := ⟨0, 0, [aliasRecViewType]⟩

example : aliasRecViewDecl.checked?.isSome = true := rfl
example : normalizationShape aliasRecRawDecl aliasRecViewDecl = true := rfl

def aliasRecNormalization : Normalization aliasRecRawDecl where
  view := aliasRecViewDecl
  shape_eq := rfl

def aliasRecViewChecked : aliasRecViewDecl.Checked :=
  aliasRecViewDecl.checked?.get (by decide)

def aliasRecBlock : NormalizedChecked aliasRecRawDecl :=
  aliasRecNormalization.check?.get (by decide)

def aliasRecGenerationChecked : GenerationChecked aliasRecRawDecl :=
  aliasRecBlock.generation?.get (by decide)

example : aliasRecNormalization.accepted = true := rfl
example : (normalizedChecked? aliasRecRawDecl aliasRecViewDecl).isSome = true := rfl
example : aliasRecBlock.checked.type = aliasRecViewType := rfl
example : ∃ raw,
    aliasRecRawDecl.types = [raw] ∧
    raw.name = aliasRecBlock.checked.type.name ∧
    raw.uvars = aliasRecBlock.checked.type.uvars ∧
    List.Forall₂ CtorHeaderEq raw.ctors aliasRecBlock.checked.type.ctors :=
  aliasRecBlock.source_anatomy
example : aliasRecViewChecked.constructors[0].fields = [.const ``AliasRec []] := rfl
example : aliasRecViewChecked.constructors[0].recursive.length = 1 := rfl
example : aliasRecViewChecked.constructors[0].recursive[0].binders = [] := rfl
example : aliasRecGenerationChecked.block.ctorPairs[0].rawFields 0 =
    [aliasRecRawField] := rfl
example : (ctorFields aliasRecGenerationChecked.minorTypes[0])[0]? =
    some aliasRecRawField := rfl
example : aliasRecGenerationChecked.recursor =
    vconst(type_of% @AliasRec.rec) := rfl
example : aliasRecGenerationChecked.generatedRules[0]? =
    some (vdefeq(motive mk a =>
      @AliasRec.rec motive mk (@AliasRec.mk a) ≡
        mk a (@AliasRec.rec motive mk a))) := rfl

def recAliasDefEq : VDefEq :=
  vdefeq(@RecAlias ≡ fun (α : Sort u) => α)

def recAliasConstEnv : VEnv :=
  (VEnv.empty.addConst ``RecAlias (vconst(type_of% @RecAlias))).get (by decide)

def recAliasEnv : VEnv := recAliasConstEnv.addDefEq recAliasDefEq

theorem recAliasConstant_wf :
    (vconst(type_of% @RecAlias) : VConstant).WF VEnv.empty := by
  apply VEnv.IsType.forallE
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem recAliasConstEnv_ordered :
    recAliasConstEnv.Ordered := by
  apply VEnv.Ordered.const VEnv.Ordered.empty
    (ci := vconst(type_of% @RecAlias))
  · exact recAliasConstant_wf
  · rfl

theorem recAliasEnv_ordered :
    recAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq recAliasConstEnv_ordered
  constructor
  · exact VEnv.HasType.const0 rfl
      (recAliasConstant_wf.mono
        (VEnv.addConst_le (by rfl :
          VEnv.empty.addConst ``RecAlias
            (vconst(type_of% @RecAlias)) =
              some recAliasConstEnv)))
  · exact VEnv.HasType.lam
      (VEnv.HasType.sort (by decide))
      (VEnv.HasType.bvar .zero)

/-- The raw aliased field and the normalized recursive target are
definitionally equal after the raw family constant has been inserted. -/
theorem aliasRecField_defeq {envT : VEnv}
    (hadd : recAliasEnv.addConst ``AliasRec aliasRecRawType.toVConstant =
      some envT) :
    envT.IsDefEq 0 [] aliasRecRawField (.const ``AliasRec [])
      (.sort (.succ .zero)) := by
  have hlookup :
      envT.constants ``AliasRec = some aliasRecRawType.toVConstant :=
    VEnv.addConst_self hadd
  have hfamily : envT.HasType 0 [] (.const ``AliasRec [])
      (.sort (.succ .zero)) :=
    .constDF hlookup (fun _ h => nomatch h) (fun _ h => nomatch h) rfl .nil
  have hdelta : envT.IsDefEq 0 []
      (.const ``RecAlias [.succ .zero])
      (.lam (.sort (.succ .zero)) (.bvar 0))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := by
    apply VEnv.IsDefEq.extra
      (df := recAliasDefEq) (ls := [.succ .zero]) (Γ := [])
    · exact (VEnv.addConst_le hadd).defeqs (by
        simp [recAliasEnv, VEnv.addDefEq])
    · intro l hl
      simp only [List.mem_singleton] at hl
      subst l
      decide
    · rfl
  have happ := VEnv.IsDefEq.appDF hdelta hfamily
  have hbeta : envT.IsDefEq 0 []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.const ``AliasRec []))
      (.const ``AliasRec []) (.sort (.succ .zero)) :=
    .beta (.bvar .zero) hfamily
  exact happ.trans hbeta

/-- The raw family result remains well typed under the raw aliased field
binder. -/
theorem aliasRecResult_hasType {envT : VEnv}
    (hadd : recAliasEnv.addConst ``AliasRec aliasRecRawType.toVConstant =
      some envT) :
    envT.HasType 0 [aliasRecRawField] (.const ``AliasRec [])
      (.sort (.succ .zero)) :=
  .constDF (VEnv.addConst_self hadd) (fun _ h => nomatch h)
    (fun _ h => nomatch h) rfl .nil

/-- Field WHNF is also justified semantically. The constructor comparison is
staged after insertion of the raw `AliasRec` family constant, and derives
`RecAlias AliasRec ≡ AliasRec` by delta, application congruence, and beta.
-/
theorem aliasRecNormalization_wf :
    aliasRecNormalization.WF recAliasEnv := by
  refine ⟨aliasRecRawType, aliasRecViewType, rfl, rfl, ?_, ?_⟩
  · exact ⟨_, by type_tac⟩
  · intro envT hadd
    exact .cons
      ⟨_, .forallEDF (aliasRecField_defeq hadd)
        (aliasRecResult_hasType hadd)⟩
      .nil

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecNormalization_wf [propext, Quot.sound]

/-- The normalized direct-recursive view satisfies the semantic declaration
contract independently of the raw aliased field syntax. -/
theorem aliasRecViewDecl_wf : aliasRecViewDecl.WF recAliasEnv := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = aliasRecViewType :=
    List.mem_singleton.1 (by simpa [aliasRecViewDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · trivial
  · intro c hc
    have hc' : c = aliasRecViewCtor :=
      List.mem_singleton.1 (by simpa [aliasRecViewType] using hc)
    subst c
    refine ⟨?_, .nil⟩
    exact ⟨.inl rfl, fun _ => .nil, trivial⟩

/-- Recursive-field recognition is certified on the normalized view while the
paired block continues to retain the raw aliased constructor syntax. -/
theorem aliasRecBlock_wf : aliasRecBlock.WF recAliasEnv := by
  refine ⟨aliasRecNormalization_wf, ?_⟩
  change aliasRecViewChecked.WF recAliasEnv
  exact aliasRecViewChecked.wf_of_decl aliasRecViewDecl_wf

theorem aliasRecGenerationChecked_wf :
    aliasRecGenerationChecked.WF recAliasEnv := by
  refine {
    blockWF := aliasRecBlock_wf
    familyTel := by trivial
    familyResult := by
      exact .sortDF (by decide) (by decide) rfl
    ctors := ?_ }
  intro envT hadd ctor hctor
  change recAliasEnv.addConst ``AliasRec aliasRecRawType.toVConstant =
    some envT at hadd
  change ctor ∈
    [⟨aliasRecRawType.ctors[0], aliasRecViewChecked.constructors[0]⟩]
    at hctor
  obtain rfl := List.mem_singleton.1 hctor
  have hfield := aliasRecField_defeq hadd
  have hresult := aliasRecResult_hasType hadd
  exact {
    declaredTel := ⟨⟨_, hfield⟩, trivial⟩
    declaredResult := hresult
    emittedTel := ⟨⟨_, hfield⟩, trivial⟩
    emittedResult := hresult }

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecBlock_wf [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecGenerationChecked_wf [propext, Quot.sound]

/-- The recursive-field alias case preserves the raw aliased constructor
binder while using the normalized view to generate recursion artifacts. -/
def aliasRecFinalEnv : VEnv :=
  (recAliasEnv.addInductGeneration
    aliasRecGenerationChecked).get (by decide)

theorem aliasRec_addInductGeneration :
    recAliasEnv.addInductGeneration aliasRecGenerationChecked =
      some aliasRecFinalEnv := rfl

theorem aliasRecFinalEnv_trace :
    Nonempty (VEnv.AddInductGenerationTrace
      recAliasEnv aliasRecFinalEnv aliasRecGenerationChecked) :=
  VEnv.addInductGeneration_trace aliasRec_addInductGeneration

theorem aliasRecFinalEnv_le :
    recAliasEnv ≤ aliasRecFinalEnv := by
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.le

theorem aliasRecFinalEnv_family_fresh :
    recAliasEnv.constants ``AliasRec = none := by
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.family_fresh

theorem aliasRecFinalEnv_family_lookup :
    aliasRecFinalEnv.constants ``AliasRec =
      some aliasRecRawType.toVConstant := by
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.family_lookup

theorem aliasRecFinalEnv_ctor_fresh :
    ∀ c ∈ aliasRecRawType.ctors,
      recAliasEnv.constants c.name = none := by
  intro c hc
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.ctor_fresh hc

theorem aliasRecFinalEnv_ctor_lookup :
    ∀ c ∈ aliasRecRawType.ctors,
      aliasRecFinalEnv.constants c.name =
        some c.toVConstant := by
  intro c hc
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.ctor_lookup hc

theorem aliasRecFinalEnv_rec_fresh :
    recAliasEnv.constants ``AliasRec.rec = none := by
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.rec_fresh

theorem aliasRecFinalEnv_rec_lookup :
    aliasRecFinalEnv.constants ``AliasRec.rec =
      some (vconst(type_of% @AliasRec.rec)) := by
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.rec_lookup

theorem aliasRecFinalEnv_rule_mem :
    ∀ df ∈ aliasRecGenerationChecked.generatedRules,
      aliasRecFinalEnv.defeqs df := by
  intro df hdf
  rcases aliasRecFinalEnv_trace with ⟨H⟩
  exact H.rule_mem hdf

theorem aliasRecFinalEnv_iota_mem :
    aliasRecFinalEnv.defeqs
      (vdefeq(motive mk a =>
        @AliasRec.rec motive mk (@AliasRec.mk a) ≡
          mk a (@AliasRec.rec motive mk a))) := by
  apply aliasRecFinalEnv_rule_mem
  exact .head _

theorem aliasRecFinalEnv_ordered :
    aliasRecFinalEnv.Ordered :=
  VEnv.addInductGeneration_WF
    recAliasEnv_ordered
    aliasRecGenerationChecked_wf
    aliasRec_addInductGeneration

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecFinalEnv_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecFinalEnv_family_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecFinalEnv_ctor_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecFinalEnv_rec_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecFinalEnv_iota_mem [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.aliasRecFinalEnv_ordered [propext, Classical.choice, Quot.sound]

/-! ## Normalization differential matrix

The isolated `AliasFormer` and `AliasRec` fixtures above establish that Lean
retains reducible aliases at family results and direct recursive targets.  The
single indexed declaration below covers every remaining normalization
position in one real kernel payload: parameter and index domains, ordinary
fields, direct recursion, recursion hidden behind a Pi-producing alias, and
beta/let redexes retained in alias definitions.  Its view is deliberately
written out so changes to either Lean's stored metadata or the Theory
normalizer fail by computation.
-/

abbrev MatrixBetaAlias (alpha : Sort u) :=
  (fun type : Sort u => type) alpha

abbrev MatrixLetAlias (alpha : Sort u) :=
  let type := alpha
  type

abbrev MatrixPiAlias (alpha : Sort u) := (proof : Prop) → alpha

abbrev MatrixIndexAlias
    (index : TypeFamilyAlias) : TypeFamilyAlias := index

inductive NormalizationMatrix (alpha : TypeFamilyAlias) :
    TypeFamilyAlias → Type 1 where
  | mk (index : TypeFamilyAlias)
      (ordinary : RecAlias Prop)
      (beta : MatrixBetaAlias Prop)
      (letBound : MatrixLetAlias Prop)
      (direct : RecAlias
        (NormalizationMatrix alpha (MatrixIndexAlias index)))
      (piHidden : MatrixPiAlias
        (NormalizationMatrix alpha (MatrixIndexAlias index)))
      (betaRecursive : MatrixBetaAlias
        (NormalizationMatrix alpha (MatrixIndexAlias index)))
      (letRecursive : MatrixLetAlias
        (NormalizationMatrix alpha (MatrixIndexAlias index))) :
      NormalizationMatrix alpha (MatrixIndexAlias index)

def normalizationMatrixRawType : VInductiveType where
  name := ``NormalizationMatrix
  uvars := 0
  type := vconst(type_of% @NormalizationMatrix).type
  ctors := [⟨vconst(type_of% @NormalizationMatrix.mk),
    ``NormalizationMatrix.mk⟩]

def normalizationMatrixRawDecl : VInductDecl :=
  ⟨0, 1, [normalizationMatrixRawType]⟩

def normalizationMatrixTarget (alpha index : VExpr) : VExpr :=
  (VExpr.const ``NormalizationMatrix []).app alpha |>.app
    ((VExpr.const ``MatrixIndexAlias []).app index)

def normalizationMatrixViewCtorType : VExpr :=
  .forallE (.sort (.succ .zero)) <|
  .forallE (.sort (.succ .zero)) <|
  .forallE (.sort .zero) <|
  .forallE (.sort .zero) <|
  .forallE (.sort .zero) <|
  .forallE (normalizationMatrixTarget (.bvar 4) (.bvar 3)) <|
  .forallE (.forallE (.sort .zero)
    (normalizationMatrixTarget (.bvar 6) (.bvar 5))) <|
  .forallE (normalizationMatrixTarget (.bvar 6) (.bvar 5)) <|
  .forallE (normalizationMatrixTarget (.bvar 7) (.bvar 6)) <|
  normalizationMatrixTarget (.bvar 8) (.bvar 7)

def normalizationMatrixViewCtor : VConstVal :=
  { normalizationMatrixRawType.ctors[0] with
    type := normalizationMatrixViewCtorType }

def normalizationMatrixViewType : VInductiveType :=
  { normalizationMatrixRawType with
    type := .forallE (.sort (.succ .zero))
      (.forallE (.sort (.succ .zero))
        (.sort (.succ (.succ .zero))))
    ctors := [normalizationMatrixViewCtor] }

def normalizationMatrixViewDecl : VInductDecl :=
  ⟨0, 1, [normalizationMatrixViewType]⟩

example : normalizationMatrixRawType.type =
    (VExpr.const ``TypeFamilyAlias []).forallE
      ((VExpr.const ``TypeFamilyAlias []).forallE
        (VExpr.sort (.succ (.succ .zero)))) := rfl

example : normalizationMatrixRawType.ctors[0].type =
    vconst(type_of% @NormalizationMatrix.mk).type := rfl

example : normalizationMatrixRawDecl.checked? = none := rfl
example : normalizationMatrixViewDecl.checked?.isSome = true := rfl
example : normalizationShape normalizationMatrixRawDecl
    normalizationMatrixViewDecl = true := rfl

def normalizationMatrixNormalization :
    Normalization normalizationMatrixRawDecl where
  view := normalizationMatrixViewDecl
  shape_eq := rfl

def normalizationMatrixViewChecked :
    normalizationMatrixViewDecl.Checked :=
  normalizationMatrixViewDecl.checked?.get (by decide)

def normalizationMatrixBlock :
    NormalizedChecked normalizationMatrixRawDecl :=
  normalizationMatrixNormalization.check?.get (by decide)

def normalizationMatrixGenerationChecked :
    GenerationChecked normalizationMatrixRawDecl :=
  normalizationMatrixBlock.generation?.get (by decide)

example : normalizationMatrixNormalization.accepted = true := rfl
example : (normalizedChecked? normalizationMatrixRawDecl
    normalizationMatrixViewDecl).isSome = true := rfl
example : normalizationMatrixBlock.checked.type =
    normalizationMatrixViewType := rfl
example : normalizationMatrixViewChecked.params =
    [.sort (.succ .zero)] := rfl
example : normalizationMatrixViewChecked.indices =
    [.sort (.succ .zero)] := rfl
example : normalizationMatrixViewChecked.constructors[0].fields.length = 8 :=
  rfl
example : normalizationMatrixViewChecked.constructors[0].recursive.length = 4 :=
  rfl
example : normalizationMatrixViewChecked.constructors[0].recursive.map
    (fun position => (position.fieldIndex, position.binders.length)) =
      [(4, 0), (5, 1), (6, 0), (7, 0)] := rfl
example : normalizationMatrixGenerationChecked.recursor =
    vconst(type_of% @NormalizationMatrix.rec) := rfl
example : normalizationMatrixGenerationChecked.generatedRules[0]? =
    some (vdefeq(alpha motive mk index ordinary beta letBound direct
      piHidden betaRecursive letRecursive =>
      @NormalizationMatrix.rec alpha motive mk (MatrixIndexAlias index)
          (@NormalizationMatrix.mk alpha index ordinary beta letBound direct
            piHidden betaRecursive letRecursive) ≡
        mk index ordinary beta letBound direct piHidden betaRecursive
          letRecursive
          (@NormalizationMatrix.rec alpha motive mk
            (MatrixIndexAlias index) direct)
          (fun proof => @NormalizationMatrix.rec alpha motive mk
            (MatrixIndexAlias index) (piHidden proof))
          (@NormalizationMatrix.rec alpha motive mk
            (MatrixIndexAlias index) betaRecursive)
          (@NormalizationMatrix.rec alpha motive mk
            (MatrixIndexAlias index) letRecursive))) := rfl
example : normalizationMatrixGenerationChecked.generatedRules.length = 1 := rfl

/-! The semantic pre-environment contains the exact reducible definitions
whose WHNFs justify the normalized descriptor.  Each abbreviation is added
as a constant followed by its delta equation so the final transaction uses
the same staged environment discipline as ordinary declarations. -/

def normalizationMatrixRecAliasConstEnv : VEnv :=
  (typeFamilyAliasEnv.addConst ``RecAlias
    (vconst(type_of% @RecAlias))).get (by decide)

def normalizationMatrixRecAliasEnv : VEnv :=
  normalizationMatrixRecAliasConstEnv.addDefEq recAliasDefEq

theorem normalizationMatrixRecAliasEnv_ordered :
    normalizationMatrixRecAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq
  · apply VEnv.Ordered.const (n := ``RecAlias)
      (ci := vconst(type_of% @RecAlias))
      (env' := normalizationMatrixRecAliasConstEnv)
      typeFamilyAliasEnv_ordered
    · exact ⟨_, by type_tac⟩
    · rfl
  · have hlookup : normalizationMatrixRecAliasConstEnv.constants
        ``RecAlias = some (vconst(type_of% @RecAlias)) := rfl
    constructor <;> type_tac

def matrixBetaAliasDefEq : VDefEq :=
  vdefeq(@MatrixBetaAlias ≡ fun (alpha : Sort u) =>
    (fun type : Sort u => type) alpha)

def normalizationMatrixBetaAliasConstEnv : VEnv :=
  (normalizationMatrixRecAliasEnv.addConst ``MatrixBetaAlias
    (vconst(type_of% @MatrixBetaAlias))).get (by decide)

def normalizationMatrixBetaAliasEnv : VEnv :=
  normalizationMatrixBetaAliasConstEnv.addDefEq matrixBetaAliasDefEq

theorem normalizationMatrixBetaAliasEnv_ordered :
    normalizationMatrixBetaAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq
  · apply VEnv.Ordered.const (n := ``MatrixBetaAlias)
      (ci := vconst(type_of% @MatrixBetaAlias))
      (env' := normalizationMatrixBetaAliasConstEnv)
      normalizationMatrixRecAliasEnv_ordered
    · exact ⟨_, by type_tac⟩
    · rfl
  · have hlookup : normalizationMatrixBetaAliasConstEnv.constants
        ``MatrixBetaAlias = some (vconst(type_of% @MatrixBetaAlias)) := rfl
    constructor <;> type_tac

def matrixLetAliasDefEq : VDefEq :=
  vdefeq(@MatrixLetAlias ≡ fun (alpha : Sort u) =>
    let type := alpha
    type)

def normalizationMatrixLetAliasConstEnv : VEnv :=
  (normalizationMatrixBetaAliasEnv.addConst ``MatrixLetAlias
    (vconst(type_of% @MatrixLetAlias))).get (by decide)

def normalizationMatrixLetAliasEnv : VEnv :=
  normalizationMatrixLetAliasConstEnv.addDefEq matrixLetAliasDefEq

theorem normalizationMatrixLetAliasEnv_ordered :
    normalizationMatrixLetAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq
  · apply VEnv.Ordered.const (n := ``MatrixLetAlias)
      (ci := vconst(type_of% @MatrixLetAlias))
      (env' := normalizationMatrixLetAliasConstEnv)
      normalizationMatrixBetaAliasEnv_ordered
    · exact ⟨_, by type_tac⟩
    · rfl
  · have hlookup : normalizationMatrixLetAliasConstEnv.constants
        ``MatrixLetAlias = some (vconst(type_of% @MatrixLetAlias)) := rfl
    constructor <;> type_tac

def matrixPiAliasDefEq : VDefEq :=
  vdefeq(@MatrixPiAlias ≡ fun (alpha : Sort u) =>
    (proof : Prop) → alpha)

def normalizationMatrixPiAliasConstEnv : VEnv :=
  (normalizationMatrixLetAliasEnv.addConst ``MatrixPiAlias
    (vconst(type_of% @MatrixPiAlias))).get (by decide)

def normalizationMatrixPiAliasEnv : VEnv :=
  normalizationMatrixPiAliasConstEnv.addDefEq matrixPiAliasDefEq

theorem normalizationMatrixPiAliasEnv_ordered :
    normalizationMatrixPiAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq
  · apply VEnv.Ordered.const (n := ``MatrixPiAlias)
      (ci := vconst(type_of% @MatrixPiAlias))
      (env' := normalizationMatrixPiAliasConstEnv)
      normalizationMatrixLetAliasEnv_ordered
    · exact ⟨_, by type_tac⟩
    · rfl
  · have hlookup : normalizationMatrixPiAliasConstEnv.constants
        ``MatrixPiAlias = some (vconst(type_of% @MatrixPiAlias)) := rfl
    constructor
    · type_tac
    · apply VEnv.HasType.lam
      · exact VEnv.HasType.sort (by decide)
      · apply VEnv.IsDefEq.defeq
          (VEnv.IsDefEq.sortDF
            (l := .imax (.succ .zero) (.param 0))
            (l' := .param 0) (by decide) (by decide) (by
              rw [VLevel.equiv_def]
              intro ls
              simp only [VLevel.eval, Nat.zero_add]
              let n := ls.getD 0 0
              change Lean.Nat.imax 1 n = n
              by_cases h : n = 0
              · simp [Lean.Nat.imax, h]
              · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
                simp [Lean.Nat.imax, h, Nat.max_eq_right hn]))
        exact VEnv.HasType.forallE
          (VEnv.HasType.sort (by decide))
          (VEnv.HasType.bvar (.succ .zero))

def matrixIndexAliasDefEq : VDefEq :=
  vdefeq(MatrixIndexAlias ≡ fun index : TypeFamilyAlias => index)

def normalizationMatrixIndexAliasConstEnv : VEnv :=
  (normalizationMatrixPiAliasEnv.addConst ``MatrixIndexAlias
    (vconst(type_of% @MatrixIndexAlias))).get (by decide)

def normalizationMatrixAliasEnv : VEnv :=
  normalizationMatrixIndexAliasConstEnv.addDefEq matrixIndexAliasDefEq

theorem normalizationMatrixAliasEnv_ordered :
    normalizationMatrixAliasEnv.Ordered := by
  apply VEnv.Ordered.defeq
  · apply VEnv.Ordered.const (n := ``MatrixIndexAlias)
      (ci := vconst(type_of% @MatrixIndexAlias))
      (env' := normalizationMatrixIndexAliasConstEnv)
      normalizationMatrixPiAliasEnv_ordered
    · have hfamily : normalizationMatrixPiAliasEnv.constants
          ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
      exact ⟨_, by type_tac⟩
    · rfl
  · have hfamily : normalizationMatrixIndexAliasConstEnv.constants
        ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
    have hlookup : normalizationMatrixIndexAliasConstEnv.constants
        ``MatrixIndexAlias = some (vconst(type_of% @MatrixIndexAlias)) := rfl
    constructor <;> type_tac

theorem normalizationMatrixRecAliasEnv_le_betaAliasEnv :
    normalizationMatrixRecAliasEnv ≤ normalizationMatrixBetaAliasEnv :=
  (VEnv.addConst_le (by rfl : normalizationMatrixRecAliasEnv.addConst
    ``MatrixBetaAlias (vconst(type_of% @MatrixBetaAlias)) =
      some normalizationMatrixBetaAliasConstEnv)).trans VEnv.addDefEq_le

theorem normalizationMatrixBetaAliasEnv_le_letAliasEnv :
    normalizationMatrixBetaAliasEnv ≤ normalizationMatrixLetAliasEnv :=
  (VEnv.addConst_le (by rfl : normalizationMatrixBetaAliasEnv.addConst
    ``MatrixLetAlias (vconst(type_of% @MatrixLetAlias)) =
      some normalizationMatrixLetAliasConstEnv)).trans VEnv.addDefEq_le

theorem normalizationMatrixLetAliasEnv_le_piAliasEnv :
    normalizationMatrixLetAliasEnv ≤ normalizationMatrixPiAliasEnv :=
  (VEnv.addConst_le (by rfl : normalizationMatrixLetAliasEnv.addConst
    ``MatrixPiAlias (vconst(type_of% @MatrixPiAlias)) =
      some normalizationMatrixPiAliasConstEnv)).trans VEnv.addDefEq_le

theorem normalizationMatrixPiAliasEnv_le_aliasEnv :
    normalizationMatrixPiAliasEnv ≤ normalizationMatrixAliasEnv :=
  (VEnv.addConst_le (by rfl : normalizationMatrixPiAliasEnv.addConst
    ``MatrixIndexAlias (vconst(type_of% @MatrixIndexAlias)) =
      some normalizationMatrixIndexAliasConstEnv)).trans VEnv.addDefEq_le

theorem normalizationMatrixRecAliasEnv_le_aliasEnv :
    normalizationMatrixRecAliasEnv ≤ normalizationMatrixAliasEnv :=
  normalizationMatrixRecAliasEnv_le_betaAliasEnv.trans <|
    normalizationMatrixBetaAliasEnv_le_letAliasEnv.trans <|
      normalizationMatrixLetAliasEnv_le_piAliasEnv.trans
        normalizationMatrixPiAliasEnv_le_aliasEnv

theorem typeFamilyAliasEnv_le_normalizationMatrixAliasEnv :
    typeFamilyAliasEnv ≤ normalizationMatrixAliasEnv := by
  exact ((VEnv.addConst_le (by rfl : typeFamilyAliasEnv.addConst ``RecAlias
    (vconst(type_of% @RecAlias)) =
      some normalizationMatrixRecAliasConstEnv)).trans VEnv.addDefEq_le).trans
        normalizationMatrixRecAliasEnv_le_aliasEnv

theorem normalizationMatrix_typeFamilyAliasDefEq_mem :
    normalizationMatrixAliasEnv.defeqs typeFamilyAliasDefEq :=
  typeFamilyAliasEnv_le_normalizationMatrixAliasEnv.defeqs
    VEnv.addDefEq_self

theorem normalizationMatrix_recAliasDefEq_mem :
    normalizationMatrixAliasEnv.defeqs recAliasDefEq :=
  normalizationMatrixRecAliasEnv_le_aliasEnv.defeqs VEnv.addDefEq_self

theorem normalizationMatrix_betaAliasDefEq_mem :
    normalizationMatrixAliasEnv.defeqs matrixBetaAliasDefEq :=
  (normalizationMatrixBetaAliasEnv_le_letAliasEnv.trans <|
    normalizationMatrixLetAliasEnv_le_piAliasEnv.trans
      normalizationMatrixPiAliasEnv_le_aliasEnv).defeqs VEnv.addDefEq_self

theorem normalizationMatrix_letAliasDefEq_mem :
    normalizationMatrixAliasEnv.defeqs matrixLetAliasDefEq :=
  (normalizationMatrixLetAliasEnv_le_piAliasEnv.trans
    normalizationMatrixPiAliasEnv_le_aliasEnv).defeqs VEnv.addDefEq_self

theorem normalizationMatrix_piAliasDefEq_mem :
    normalizationMatrixAliasEnv.defeqs matrixPiAliasDefEq :=
  normalizationMatrixPiAliasEnv_le_aliasEnv.defeqs VEnv.addDefEq_self

theorem normalizationMatrixTypeFamily_defeq {env : VEnv} {U : Nat}
    {Γ : List VExpr} (henv : normalizationMatrixAliasEnv ≤ env) :
    env.IsDefEq U Γ (VExpr.const ``TypeFamilyAlias [])
      (VExpr.sort (.succ .zero))
      (VExpr.sort (.succ (.succ .zero))) := by
  exact .extra (df := typeFamilyAliasDefEq) (ls := [])
    (henv.defeqs normalizationMatrix_typeFamilyAliasDefEq_mem)
    (fun _ h => nomatch h) rfl

theorem normalizationMatrixRecAlias_app_defeq {env : VEnv} {U : Nat}
    {Γ : List VExpr} {u : VLevel} {A : VExpr} (hu : u.WF U)
    (henv : normalizationMatrixAliasEnv ≤ env)
    (hA : env.HasType U Γ A (VExpr.sort u)) :
    env.IsDefEq U Γ ((VExpr.const ``RecAlias [u]).app A) A
      (VExpr.sort u) := by
  have hdelta : env.IsDefEq U Γ (VExpr.const ``RecAlias [u])
      (VExpr.lam (VExpr.sort u) (VExpr.bvar 0))
      (VExpr.forallE (VExpr.sort u) (VExpr.sort u)) :=
    .extra (df := recAliasDefEq) (ls := [u])
      (henv.defeqs normalizationMatrix_recAliasDefEq_mem)
      (by simpa using hu) rfl
  have hbeta := VEnv.IsDefEq.beta (VEnv.IsDefEq.bvar .zero) hA
  exact (VEnv.IsDefEq.appDF hdelta hA).trans (by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta)

theorem normalizationMatrixBetaAlias_app_defeq {env : VEnv} {U : Nat}
    {Γ : List VExpr} {u : VLevel} {A : VExpr} (hu : u.WF U)
    (henv : normalizationMatrixAliasEnv ≤ env)
    (hA : env.HasType U Γ A (VExpr.sort u)) :
    env.IsDefEq U Γ ((VExpr.const ``MatrixBetaAlias [u]).app A) A
      (VExpr.sort u) := by
  have hdelta : env.IsDefEq U Γ (VExpr.const ``MatrixBetaAlias [u])
      (VExpr.lam (VExpr.sort u)
        ((VExpr.lam (VExpr.sort u) (VExpr.bvar 0)).app (VExpr.bvar 0)))
      (VExpr.forallE (VExpr.sort u) (VExpr.sort u)) :=
    .extra (df := matrixBetaAliasDefEq) (ls := [u])
      (henv.defeqs normalizationMatrix_betaAliasDefEq_mem)
      (by simpa using hu) rfl
  have hbody : env.HasType U (VExpr.sort u :: Γ)
      ((VExpr.lam (VExpr.sort u) (VExpr.bvar 0)).app (VExpr.bvar 0))
      (VExpr.sort u) :=
    VEnv.HasType.app
      (VEnv.HasType.lam (VEnv.HasType.sort hu) (VEnv.HasType.bvar .zero))
      (VEnv.HasType.bvar .zero)
  have houterBeta := VEnv.IsDefEq.beta hbody hA
  have houter := (VEnv.IsDefEq.appDF hdelta hA).trans (by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN] using houterBeta)
  have hinnerBeta := VEnv.IsDefEq.beta (VEnv.IsDefEq.bvar .zero) hA
  exact houter.trans (by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN] using hinnerBeta)

theorem normalizationMatrixLetAlias_app_defeq {env : VEnv} {U : Nat}
    {Γ : List VExpr} {u : VLevel} {A : VExpr} (hu : u.WF U)
    (henv : normalizationMatrixAliasEnv ≤ env)
    (hA : env.HasType U Γ A (VExpr.sort u)) :
    env.IsDefEq U Γ ((VExpr.const ``MatrixLetAlias [u]).app A) A
      (VExpr.sort u) := by
  have hdelta : env.IsDefEq U Γ (VExpr.const ``MatrixLetAlias [u])
      (VExpr.lam (VExpr.sort u) (VExpr.bvar 0))
      (VExpr.forallE (VExpr.sort u) (VExpr.sort u)) :=
    .extra (df := matrixLetAliasDefEq) (ls := [u])
      (henv.defeqs normalizationMatrix_letAliasDefEq_mem)
      (by simpa using hu) rfl
  have hbeta := VEnv.IsDefEq.beta (VEnv.IsDefEq.bvar .zero) hA
  exact (VEnv.IsDefEq.appDF hdelta hA).trans (by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta)

private theorem normalizationMatrix_one_imax_equiv (u : VLevel) :
    .imax (.succ .zero) u ≈ u := by
  rw [VLevel.equiv_def]
  intro ls
  simp only [VLevel.eval, Nat.zero_add]
  let n := u.eval ls
  change Lean.Nat.imax 1 n = n
  by_cases h : n = 0
  · simp [Lean.Nat.imax, h]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    simp [Lean.Nat.imax, h, Nat.max_eq_right hn]

theorem normalizationMatrixPiAlias_app_defeq {env : VEnv} {U : Nat}
    {Γ : List VExpr} {u : VLevel} {A : VExpr} (hu : u.WF U)
    (henv : normalizationMatrixAliasEnv ≤ env)
    (hA : env.HasType U Γ A (VExpr.sort u)) :
    env.IsDefEq U Γ ((VExpr.const ``MatrixPiAlias [u]).app A)
      (VExpr.forallE (VExpr.sort .zero) A.lift) (VExpr.sort u) := by
  have hdelta : env.IsDefEq U Γ (VExpr.const ``MatrixPiAlias [u])
      (VExpr.lam (VExpr.sort u)
        (VExpr.forallE (VExpr.sort .zero) (VExpr.bvar 1)))
      (VExpr.forallE (VExpr.sort u) (VExpr.sort u)) :=
    .extra (df := matrixPiAliasDefEq) (ls := [u])
      (henv.defeqs normalizationMatrix_piAliasDefEq_mem)
      (by simpa using hu) rfl
  have hbody : env.HasType U (VExpr.sort u :: Γ)
      (VExpr.forallE (VExpr.sort .zero) (VExpr.bvar 1))
      (VExpr.sort u) := by
    apply VEnv.IsDefEq.defeq
      (VEnv.IsDefEq.sortDF
        (l := .imax (.succ .zero) u) (l' := u)
        ⟨trivial, hu⟩ hu (normalizationMatrix_one_imax_equiv u))
    exact VEnv.HasType.forallE (VEnv.HasType.sort (by trivial))
      (VEnv.HasType.bvar (.succ .zero))
  have hbeta := VEnv.IsDefEq.beta hbody hA
  exact (VEnv.IsDefEq.appDF hdelta hA).trans (by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta)

theorem normalizationMatrixIndexAlias_app_hasType {env : VEnv} {U : Nat}
    {Γ : List VExpr} {index : VExpr}
    (henv : normalizationMatrixAliasEnv ≤ env)
    (hindex : env.HasType U Γ index (VExpr.sort (.succ .zero))) :
    env.HasType U Γ ((VExpr.const ``MatrixIndexAlias []).app index)
      (VExpr.sort (.succ .zero)) := by
  have hfn : env.HasType U Γ (VExpr.const ``MatrixIndexAlias [])
      ((VExpr.const ``TypeFamilyAlias []).forallE
        (VExpr.const ``TypeFamilyAlias [])) :=
    .constDF (henv.constants (by rfl : normalizationMatrixAliasEnv.constants
        ``MatrixIndexAlias = some (vconst(type_of% @MatrixIndexAlias))))
      (fun _ h => nomatch h) (fun _ h => nomatch h) rfl .nil
  have hindexRaw := (normalizationMatrixTypeFamily_defeq henv).defeq' hindex
  exact (normalizationMatrixTypeFamily_defeq henv).defeq
    (VEnv.HasType.app hfn hindexRaw)

theorem normalizationMatrixTarget_hasType {env : VEnv} {U : Nat}
    {Γ : List VExpr} {alpha index : VExpr}
    (henv : normalizationMatrixAliasEnv ≤ env)
    (hfamily : env.constants ``NormalizationMatrix =
      some normalizationMatrixRawType.toVConstant)
    (halpha : env.HasType U Γ alpha (VExpr.const ``TypeFamilyAlias []))
    (hindex : env.HasType U Γ index (VExpr.const ``TypeFamilyAlias [])) :
    env.HasType U Γ (normalizationMatrixTarget alpha index)
      (VExpr.sort (.succ (.succ .zero))) := by
  have hfn : env.HasType U Γ (VExpr.const ``NormalizationMatrix [])
      (VExpr.forallE (VExpr.const ``TypeFamilyAlias [])
        (VExpr.forallE (VExpr.const ``TypeFamilyAlias [])
          (VExpr.sort (.succ (.succ .zero))))) :=
    .constDF hfamily (fun _ h => nomatch h) (fun _ h => nomatch h)
      rfl .nil
  have hindexFn : env.HasType U Γ (VExpr.const ``MatrixIndexAlias [])
      ((VExpr.const ``TypeFamilyAlias []).forallE
        (VExpr.const ``TypeFamilyAlias [])) :=
    .constDF (henv.constants (by rfl : normalizationMatrixAliasEnv.constants
        ``MatrixIndexAlias = some (vconst(type_of% @MatrixIndexAlias))))
      (fun _ h => nomatch h) (fun _ h => nomatch h) rfl .nil
  exact VEnv.HasType.app (VEnv.HasType.app hfn halpha)
    (VEnv.HasType.app hindexFn hindex)

theorem normalizationMatrixNormalization_wf :
    normalizationMatrixNormalization.WF normalizationMatrixAliasEnv := by
  refine ⟨normalizationMatrixRawType, normalizationMatrixViewType,
    rfl, rfl, ?_, ?_⟩
  · refine ⟨VExpr.sort (.imax (.succ (.succ .zero))
        (.imax (.succ (.succ .zero))
          (.succ (.succ (.succ .zero))))), ?_⟩
    change normalizationMatrixAliasEnv.IsDefEq 0 []
      ((VExpr.const ``TypeFamilyAlias []).forallE
        ((VExpr.const ``TypeFamilyAlias []).forallE
          (VExpr.sort (.succ (.succ .zero)))))
      ((VExpr.sort (.succ .zero)).forallE
        ((VExpr.sort (.succ .zero)).forallE
          (VExpr.sort (.succ (.succ .zero)))))
      (VExpr.sort (.imax (.succ (.succ .zero))
        (.imax (.succ (.succ .zero))
          (.succ (.succ (.succ .zero))))))
    apply VEnv.IsDefEq.forallEDF
    · exact normalizationMatrixTypeFamily_defeq .rfl
    · apply VEnv.IsDefEq.forallEDF
      · exact normalizationMatrixTypeFamily_defeq .rfl
      · exact VEnv.IsDefEq.sortDF (by decide) (by decide) rfl
  · intro envT hadd
    have henv : normalizationMatrixAliasEnv ≤ envT :=
      VEnv.addConst_le hadd
    have htypeFamily : envT.constants ``TypeFamilyAlias =
        some (vconst(type_of% @TypeFamilyAlias)) :=
      henv.constants (by rfl)
    have hrecAlias : envT.constants ``RecAlias =
        some (vconst(type_of% @RecAlias)) :=
      henv.constants (by rfl)
    have hbetaAlias : envT.constants ``MatrixBetaAlias =
        some (vconst(type_of% @MatrixBetaAlias)) :=
      henv.constants (by rfl)
    have hletAlias : envT.constants ``MatrixLetAlias =
        some (vconst(type_of% @MatrixLetAlias)) :=
      henv.constants (by rfl)
    have hpiAlias : envT.constants ``MatrixPiAlias =
        some (vconst(type_of% @MatrixPiAlias)) :=
      henv.constants (by rfl)
    have hindexAlias : envT.constants ``MatrixIndexAlias =
        some (vconst(type_of% @MatrixIndexAlias)) :=
      henv.constants (by rfl)
    have hfamily : envT.constants ``NormalizationMatrix =
        some normalizationMatrixRawType.toVConstant :=
      VEnv.addConst_self hadd
    exact .cons ⟨_, by
      apply VEnv.IsDefEq.forallEDF
      · exact normalizationMatrixTypeFamily_defeq henv
      · apply VEnv.IsDefEq.forallEDF
        · exact normalizationMatrixTypeFamily_defeq henv
        · apply VEnv.IsDefEq.forallEDF
          · exact normalizationMatrixRecAlias_app_defeq
              (by decide) henv (by type_tac)
          · apply VEnv.IsDefEq.forallEDF
            · exact normalizationMatrixBetaAlias_app_defeq
                (by decide) henv (by type_tac)
            · apply VEnv.IsDefEq.forallEDF
              · exact normalizationMatrixLetAlias_app_defeq
                  (by decide) henv (by type_tac)
              · apply VEnv.IsDefEq.forallEDF
                · exact normalizationMatrixRecAlias_app_defeq
                    (by decide) henv (by type_tac)
                · apply VEnv.IsDefEq.forallEDF
                  · exact normalizationMatrixPiAlias_app_defeq
                      (by decide) henv (by type_tac)
                  · apply VEnv.IsDefEq.forallEDF
                    · exact normalizationMatrixBetaAlias_app_defeq
                        (by decide) henv (by type_tac)
                    · apply VEnv.IsDefEq.forallEDF
                      · exact normalizationMatrixLetAlias_app_defeq
                          (by decide) henv (by type_tac)
                      · type_tac⟩ .nil

theorem normalizationMatrixViewChecked_wf :
    normalizationMatrixViewChecked.WF normalizationMatrixAliasEnv := by
  refine ⟨?_, ?_⟩
  · change normalizationMatrixAliasEnv.OnTel 0 []
      [VExpr.sort (.succ .zero), VExpr.sort (.succ .zero)]
    exact ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, trivial⟩⟩
  · intro c hc
    change c ∈ [normalizationMatrixViewCtor] at hc
    have hc' : c = normalizationMatrixViewCtor :=
      List.mem_singleton.1 hc
    subst c
    constructor
    · change fieldsWF 0 ``NormalizationMatrix 1
        normalizationMatrixAliasEnv (.succ (.succ .zero))
        [VExpr.sort (.succ .zero)] [VExpr.sort (.succ .zero)] 0
        [VExpr.sort (.succ .zero), VExpr.sort .zero,
          VExpr.sort .zero, VExpr.sort .zero,
          normalizationMatrixTarget (.bvar 4) (.bvar 3),
          (VExpr.sort .zero).forallE
            (normalizationMatrixTarget (.bvar 6) (.bvar 5)),
          normalizationMatrixTarget (.bvar 6) (.bvar 5),
          normalizationMatrixTarget (.bvar 7) (.bvar 6)]
      refine ⟨?_, ?_, ?_⟩
      · exact .inr (.inr ⟨rfl, .succ (.succ .zero), by type_tac,
          .inr (VLevel.le_refl _)⟩)
      · intro h
        change false = true at h
        contradiction
      · refine ⟨?_, ?_, ?_⟩
        · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
            .inr VLevel.le_succ⟩)
        · intro h
          change false = true at h
          contradiction
        · refine ⟨?_, ?_, ?_⟩
          · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
              .inr VLevel.le_succ⟩)
          · intro h
            change false = true at h
            contradiction
          · refine ⟨?_, ?_, ?_⟩
            · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
                .inr VLevel.le_succ⟩)
            · intro h
              change false = true at h
              contradiction
            · refine ⟨?_, ?_, ?_⟩
              · exact .inl rfl
              · intro _
                exact .cons
                  (normalizationMatrixIndexAlias_app_hasType .rfl
                    (by type_tac)) .nil
              · refine ⟨?_, ?_, ?_⟩
                · refine .inr (.inl ⟨_, rfl, by decide, ?_⟩)
                  constructor
                  · exact ⟨⟨_, by type_tac⟩, trivial⟩
                  · exact .cons
                      (normalizationMatrixIndexAlias_app_hasType .rfl
                        (by type_tac)) .nil
                · intro h
                  change false = true at h
                  contradiction
                · refine ⟨?_, ?_, ?_⟩
                  · exact .inl rfl
                  · intro _
                    exact .cons
                      (normalizationMatrixIndexAlias_app_hasType .rfl
                        (by type_tac)) .nil
                  · refine ⟨?_, ?_, trivial⟩
                    · exact .inl rfl
                    · intro _
                      exact .cons
                        (normalizationMatrixIndexAlias_app_hasType .rfl
                          (by type_tac)) .nil
    · exact .cons
        (normalizationMatrixIndexAlias_app_hasType .rfl (by type_tac)) .nil

theorem normalizationMatrixBlock_wf :
    normalizationMatrixBlock.WF normalizationMatrixAliasEnv :=
  ⟨normalizationMatrixNormalization_wf,
    normalizationMatrixViewChecked_wf⟩

theorem normalizationMatrixGenerationChecked_wf :
    normalizationMatrixGenerationChecked.WF normalizationMatrixAliasEnv := by
  refine {
    blockWF := normalizationMatrixBlock_wf
    familyTel := ?_
    familyResult := ?_
    ctors := ?_ }
  · refine ⟨⟨_, normalizationMatrixTypeFamily_defeq .rfl⟩, ?_⟩
    exact ⟨⟨_, normalizationMatrixTypeFamily_defeq .rfl⟩, trivial⟩
  · exact VEnv.IsDefEq.sortDF (by decide) (by decide) rfl
  · intro envT hadd ctor hctor
    change ctor ∈
      [⟨normalizationMatrixRawType.ctors[0],
        normalizationMatrixViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    have henv : normalizationMatrixAliasEnv ≤ envT :=
      VEnv.addConst_le hadd
    have hfamily : envT.constants ``NormalizationMatrix =
        some normalizationMatrixRawType.toVConstant :=
      VEnv.addConst_self hadd
    have hindexAlias : envT.constants ``MatrixIndexAlias =
        some (vconst(type_of% @MatrixIndexAlias)) :=
      henv.constants (by rfl)
    refine {
      declaredTel := ?_
      declaredResult := ?_
      emittedTel := ?_
      emittedResult := ?_ }
    · refine ⟨⟨_, normalizationMatrixTypeFamily_defeq henv⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixTypeFamily_defeq henv⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixRecAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixBetaAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixLetAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixRecAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixPiAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixBetaAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      exact ⟨⟨_, normalizationMatrixLetAlias_app_defeq
        (by decide) henv (by type_tac)⟩, trivial⟩
    · exact normalizationMatrixTarget_hasType henv hfamily
        (by type_tac) (by type_tac)
    · refine ⟨⟨_, by type_tac⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixTypeFamily_defeq henv⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixRecAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixBetaAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixLetAlias_app_defeq
        (by decide) henv (by type_tac)⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixRecAlias_app_defeq
        (by decide) henv (by
          exact normalizationMatrixTarget_hasType henv hfamily
            ((normalizationMatrixTypeFamily_defeq henv).defeq'
              (by type_tac))
            (by type_tac))⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixPiAlias_app_defeq
        (by decide) henv (by
          exact normalizationMatrixTarget_hasType henv hfamily
            ((normalizationMatrixTypeFamily_defeq henv).defeq'
              (by type_tac))
            (by type_tac))⟩, ?_⟩
      refine ⟨⟨_, normalizationMatrixBetaAlias_app_defeq
        (by decide) henv (by
          exact normalizationMatrixTarget_hasType henv hfamily
            ((normalizationMatrixTypeFamily_defeq henv).defeq'
              (by type_tac))
            (by type_tac))⟩, ?_⟩
      exact ⟨⟨_, normalizationMatrixLetAlias_app_defeq
        (by decide) henv (by
          exact normalizationMatrixTarget_hasType henv hfamily
            ((normalizationMatrixTypeFamily_defeq henv).defeq'
              (by type_tac))
            (by type_tac))⟩, trivial⟩
    · exact normalizationMatrixTarget_hasType henv hfamily
        ((normalizationMatrixTypeFamily_defeq henv).defeq'
          (by type_tac))
        (by type_tac)

def normalizationMatrixFinalEnv : VEnv :=
  (normalizationMatrixAliasEnv.addInductGeneration
    normalizationMatrixGenerationChecked).get (by decide)

theorem normalizationMatrix_addInductGeneration :
    normalizationMatrixAliasEnv.addInductGeneration
      normalizationMatrixGenerationChecked =
        some normalizationMatrixFinalEnv := rfl

theorem normalizationMatrixFinalEnv_trace :
    Nonempty (VEnv.AddInductGenerationTrace normalizationMatrixAliasEnv
      normalizationMatrixFinalEnv normalizationMatrixGenerationChecked) :=
  VEnv.addInductGeneration_trace normalizationMatrix_addInductGeneration

theorem normalizationMatrixFinalEnv_family_lookup :
    normalizationMatrixFinalEnv.constants ``NormalizationMatrix =
      some normalizationMatrixRawType.toVConstant := by
  rcases normalizationMatrixFinalEnv_trace with ⟨H⟩
  exact H.family_lookup

theorem normalizationMatrixFinalEnv_ctor_lookup :
    normalizationMatrixFinalEnv.constants ``NormalizationMatrix.mk =
      some normalizationMatrixRawType.ctors[0].toVConstant := by
  rcases normalizationMatrixFinalEnv_trace with ⟨H⟩
  exact H.ctor_lookup (.head _)

theorem normalizationMatrixFinalEnv_rec_lookup :
    normalizationMatrixFinalEnv.constants ``NormalizationMatrix.rec =
      some (vconst(type_of% @NormalizationMatrix.rec)) := by
  rcases normalizationMatrixFinalEnv_trace with ⟨H⟩
  exact H.rec_lookup

theorem normalizationMatrixFinalEnv_iota_mem :
    normalizationMatrixFinalEnv.defeqs
      (vdefeq(alpha motive mk index ordinary beta letBound direct
        piHidden betaRecursive letRecursive =>
        @NormalizationMatrix.rec alpha motive mk (MatrixIndexAlias index)
            (@NormalizationMatrix.mk alpha index ordinary beta letBound direct
              piHidden betaRecursive letRecursive) ≡
          mk index ordinary beta letBound direct piHidden betaRecursive
            letRecursive
            (@NormalizationMatrix.rec alpha motive mk
              (MatrixIndexAlias index) direct)
            (fun proof => @NormalizationMatrix.rec alpha motive mk
              (MatrixIndexAlias index) (piHidden proof))
            (@NormalizationMatrix.rec alpha motive mk
              (MatrixIndexAlias index) betaRecursive)
            (@NormalizationMatrix.rec alpha motive mk
              (MatrixIndexAlias index) letRecursive))) := by
  rcases normalizationMatrixFinalEnv_trace with ⟨H⟩
  apply H.rule_mem
  exact .head _

theorem normalizationMatrixFinalEnv_ordered :
    normalizationMatrixFinalEnv.Ordered :=
  VEnv.addInductGeneration_WF normalizationMatrixAliasEnv_ordered
    normalizationMatrixGenerationChecked_wf
    normalizationMatrix_addInductGeneration

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.normalizationMatrixNormalization_wf [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.normalizationMatrixViewChecked_wf [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.normalizationMatrixGenerationChecked_wf [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.normalizationMatrixFinalEnv_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.normalizationMatrixFinalEnv_iota_mem [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.normalizationMatrixFinalEnv_ordered [propext, Classical.choice, Quot.sound]

/-! ## Checked-analysis rejection fixtures -/

/-
The next three declarations are kernel-side differential fixtures for the
recursive-Pi rejection branches. `#guard_msgs` checks the actual elaborator /
kernel outcome while rolling the failed declaration back, so the VExpr
fixtures below can independently exercise the Theory analyzer and public
transaction.
-/

namespace KernelDifferential

/--
error: (kernel) arg #1 of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.KernelRejectRecDomain.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs (whitespace := lax) in
inductive KernelRejectRecDomain : Type where
  | mk : (KernelRejectRecDomain → KernelRejectRecDomain) → KernelRejectRecDomain

/--
error: Mismatched inductive type parameter in
  KernelRejectRecTarget β
The provided argument
  β
is not definitionally equal to the expected parameter
  α

Note: The value of parameter `α` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs (whitespace := lax) in
inductive KernelRejectRecTarget (α : Type) : Type where
  | mk : ((β : Type) → KernelRejectRecTarget β) → KernelRejectRecTarget α

/--
error: (kernel) arg #1 of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.KernelRejectRecIndex.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs (whitespace := lax) in
inductive KernelRejectRecIndex : Type → Type where
  | mk : ((n : Nat) → KernelRejectRecIndex (KernelRejectRecIndex Nat)) →
    KernelRejectRecIndex Nat

end KernelDifferential

/-- A recursive function argument may not mention the family in one of its
binder domains. This is the raw-VExpr counterpart of
`KernelRejectRecDomain`. -/
def recDomainTypeName : Name := .mkSimple "RecDomainFixture"

def recDomainCtorName : Name := .str recDomainTypeName "mk"

def recDomainField : VExpr :=
  .forallE (.const recDomainTypeName []) (.const recDomainTypeName [])

def recDomainType : VInductiveType where
  name := recDomainTypeName
  uvars := 0
  type := .sort (.succ .zero)
  ctors := [⟨⟨0, .forallE recDomainField (.const recDomainTypeName [])⟩,
    recDomainCtorName⟩]

def recDomainDecl : VInductDecl := ⟨0, 0, [recDomainType]⟩

example : namesOK recDomainType = true := rfl
example : closedOK recDomainType = true := rfl
example : levelsOK 0 recDomainType = true := rfl
example : typeFormerOK 0 recDomainType = true := rfl
example : largeElim 0 recDomainTypeName 0 0 recDomainType = true := rfl
example : recTarget? 0 recDomainTypeName 0 0 0 recDomainField = none := rfl
example : stage3Field 0 recDomainTypeName 0 0 0 recDomainField = false := rfl
example : stage3DirectCore 0 0 recDomainType = false := rfl
example : recDomainDecl.checked? = none := rfl
example : VEnv.empty.addInduct recDomainDecl = none := rfl

/-- A recursive target below a Pi must retain the declaration's fixed
parameters. Here the terminal target uses the locally bound `β` instead of
the outer parameter, matching `KernelRejectRecTarget`. -/
def recTargetTypeName : Name := .mkSimple "RecTargetFixture"

def recTargetCtorName : Name := .str recTargetTypeName "mk"

def recTargetField : VExpr :=
  .forallE (.sort (.succ .zero))
    ((VExpr.const recTargetTypeName []).app (VExpr.bvar 0))

def recTargetType : VInductiveType where
  name := recTargetTypeName
  uvars := 0
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  ctors := [⟨⟨0,
    .forallE (.sort (.succ .zero))
      (.forallE recTargetField
        ((VExpr.const recTargetTypeName []).app (VExpr.bvar 1)))⟩,
    recTargetCtorName⟩]

def recTargetDecl : VInductDecl := ⟨0, 1, [recTargetType]⟩

example : namesOK recTargetType = true := rfl
example : closedOK recTargetType = true := rfl
example : levelsOK 0 recTargetType = true := rfl
example : typeFormerOK 1 recTargetType = true := rfl
example : largeElim 0 recTargetTypeName 1 0 recTargetType = true := rfl
example : isRecField 0 recTargetTypeName 1 0 1
    ((VExpr.const recTargetTypeName []).app (VExpr.bvar 0)) = false := rfl
example : recTarget? 0 recTargetTypeName 1 0 0 recTargetField = none := rfl
example : stage3Field 0 recTargetTypeName 1 0 0 recTargetField = false := rfl
example : stage3DirectCore 0 1 recTargetType = false := rfl
example : recTargetDecl.checked? = none := rfl
example : VEnv.empty.addInduct recTargetDecl = none := rfl

/-- Recursive target indices must be free of the family. The inner
`RecIndexFixture Nat` occurs inside the outer recursive target's index,
matching `KernelRejectRecIndex`. -/
def recIndexTypeName : Name := .mkSimple "RecIndexFixture"

def recIndexCtorName : Name := .str recIndexTypeName "mk"

def recIndexTarget : VExpr :=
  (VExpr.const recIndexTypeName []).app
    ((VExpr.const recIndexTypeName []).app (VExpr.const ``Nat []))

def recIndexField : VExpr := .forallE (VExpr.const ``Nat []) recIndexTarget

def recIndexType : VInductiveType where
  name := recIndexTypeName
  uvars := 0
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  ctors := [⟨⟨0,
    .forallE recIndexField
      ((VExpr.const recIndexTypeName []).app (VExpr.const ``Nat []))⟩,
    recIndexCtorName⟩]

def recIndexDecl : VInductDecl := ⟨0, 0, [recIndexType]⟩

example : namesOK recIndexType = true := rfl
example : closedOK recIndexType = true := rfl
example : levelsOK 0 recIndexType = true := rfl
example : typeFormerOK 0 recIndexType = true := rfl
example : largeElim 0 recIndexTypeName 0 1 recIndexType = true := rfl
example : isRecField 0 recIndexTypeName 0 1 1 recIndexTarget = false := rfl
example : recTarget? 0 recIndexTypeName 0 1 0 recIndexField = none := rfl
example : stage3Field 0 recIndexTypeName 0 1 0 recIndexField = false := rfl
example : stage3DirectCore 0 0 recIndexType = false := rfl
example : recIndexDecl.checked? = none := rfl
example : VEnv.empty.addInduct recIndexDecl = none := rfl

/-- The old direct-recursion shape alone admits duplicate constructor names;
the shared I2 descriptor rejects the block before a partial transaction. -/
def duplicateCtorTypeName : Name := .mkSimple "DuplicateCtorFixture"

def duplicateCtorName : Name := .str duplicateCtorTypeName "mk"

def duplicateCtorType : VInductiveType where
  name := duplicateCtorTypeName
  uvars := 0
  type := VExpr.sort (.succ .zero)
  ctors := [⟨⟨0, VExpr.const duplicateCtorTypeName []⟩, duplicateCtorName⟩,
    ⟨⟨0, VExpr.const duplicateCtorTypeName []⟩, duplicateCtorName⟩]

def duplicateCtorDecl : VInductDecl := ⟨0, 0, [duplicateCtorType]⟩

example : stage3DirectCore 0 0 duplicateCtorType = true := rfl
example : namesOK duplicateCtorType = false := rfl
example : duplicateCtorDecl.checked? = none := rfl
example : VEnv.empty.addInduct duplicateCtorDecl = none := rfl

/-- Internal uniqueness covers collisions between different generated roles,
not only two constructors with the same name. -/
def typeCtorAliasName : Name := .mkSimple "TypeCtorAliasFixture"

def typeCtorAliasType : VInductiveType where
  name := typeCtorAliasName
  uvars := 0
  type := VExpr.sort (.succ .zero)
  ctors := [⟨⟨0, VExpr.const typeCtorAliasName []⟩, typeCtorAliasName⟩]

def typeCtorAliasDecl : VInductDecl := ⟨0, 0, [typeCtorAliasType]⟩

example : stage3DirectCore 0 0 typeCtorAliasType = true := rfl
example : namesOK typeCtorAliasType = false := rfl
example : typeCtorAliasDecl.checked? = none := rfl

def ctorRecAliasTypeName : Name := .mkSimple "CtorRecAliasFixture"

def ctorRecAliasType : VInductiveType where
  name := ctorRecAliasTypeName
  uvars := 0
  type := VExpr.sort (.succ .zero)
  ctors := [⟨⟨0, VExpr.const ctorRecAliasTypeName []⟩,
    .str ctorRecAliasTypeName "rec"⟩]

def ctorRecAliasDecl : VInductDecl := ⟨0, 0, [ctorRecAliasType]⟩

example : stage3DirectCore 0 0 ctorRecAliasType = true := rfl
example : namesOK ctorRecAliasType = false := rfl
example : ctorRecAliasDecl.checked? = none := rfl

/-- A constructor result with a loose index variable has the expected direct
head/spine shape, but is not legal closed kernel metadata. -/
def looseIndexTypeName : Name := .mkSimple "LooseIndexFixture"

def looseIndexCtorName : Name := .str looseIndexTypeName "mk"

def looseIndexType : VInductiveType where
  name := looseIndexTypeName
  uvars := 0
  type := VExpr.forallE (VExpr.const ``Nat []) (VExpr.sort (.succ .zero))
  ctors := [⟨⟨0, (VExpr.const looseIndexTypeName []).app (.bvar 0)⟩,
    looseIndexCtorName⟩]

def looseIndexDecl : VInductDecl := ⟨0, 0, [looseIndexType]⟩

example : stage3DirectCore 0 0 looseIndexType = true := rfl
example : closedOK looseIndexType = false := rfl
example : looseIndexDecl.checked? = none := rfl
example : VEnv.empty.addInduct looseIndexDecl = none := rfl

/-- The family type is checked before its own constant exists. A self
occurrence hidden in a parameter domain must therefore be rejected even when
the constructor result has the otherwise expected head and parameter spine. -/
def selfParamTypeName : Name := .mkSimple "SelfParamFixture"

def selfParamCtorName : Name := .str selfParamTypeName "mk"

def selfParamType : VInductiveType where
  name := selfParamTypeName
  uvars := 0
  type := VExpr.forallE (VExpr.const selfParamTypeName []) (VExpr.sort (.succ .zero))
  ctors := [⟨⟨0, VExpr.forallE (VExpr.const selfParamTypeName [])
    ((VExpr.const selfParamTypeName []).app (.bvar 0))⟩, selfParamCtorName⟩]

def selfParamDecl : VInductDecl := ⟨0, 1, [selfParamType]⟩

example : typeFormerOK 1 selfParamType = false := rfl
example : closedOK selfParamType = true := rfl
example : levelsOK 0 selfParamType = true := rfl
example : selfParamDecl.checked? = none := rfl
example : VEnv.empty.addInduct selfParamDecl = none := rfl

/-- An out-of-range universe can hide in a parameter while the result sort and
direct constructor shape remain valid. `levelsOK` checks the complete metadata
rather than only the result. -/
def badParamLevelTypeName : Name := .mkSimple "BadParamLevelFixture"

def badParamLevelCtorName : Name := .str badParamLevelTypeName "mk"

def badParamLevelType : VInductiveType where
  name := badParamLevelTypeName
  uvars := 0
  type := VExpr.forallE (VExpr.sort (.param 0)) (VExpr.sort (.succ .zero))
  ctors := [⟨⟨0, VExpr.forallE (VExpr.sort (.param 0))
    ((VExpr.const badParamLevelTypeName []).app (.bvar 0))⟩, badParamLevelCtorName⟩]

def badParamLevelDecl : VInductDecl := ⟨0, 1, [badParamLevelType]⟩

example : stage3DirectCore 0 1 badParamLevelType = true := rfl
example : closedOK badParamLevelType = true := rfl
example : levelsOK 0 badParamLevelType = false := rfl
example : badParamLevelDecl.checked? = none := rfl
example : VEnv.empty.addInduct badParamLevelDecl = none := rfl

/-- Constructor fields receive the same full universe-range check. -/
def badCtorLevelTypeName : Name := .mkSimple "BadCtorLevelFixture"

def badCtorLevelCtorName : Name := .str badCtorLevelTypeName "mk"

def badCtorLevelType : VInductiveType where
  name := badCtorLevelTypeName
  uvars := 0
  type := VExpr.sort (.succ .zero)
  ctors := [⟨⟨0, VExpr.forallE (VExpr.sort (.param 0))
    (VExpr.const badCtorLevelTypeName [])⟩, badCtorLevelCtorName⟩]

def badCtorLevelDecl : VInductDecl := ⟨0, 0, [badCtorLevelType]⟩

example : stage3DirectCore 0 0 badCtorLevelType = true := rfl
example : closedOK badCtorLevelType = true := rfl
example : levelsOK 0 badCtorLevelType = false := rfl
example : badCtorLevelDecl.checked? = none := rfl
example : VEnv.empty.addInduct badCtorLevelDecl = none := rfl

/-- A non-sort family result never reaches descriptor construction. -/
def nonSortResultTypeName : Name := .mkSimple "NonSortResultFixture"

def nonSortResultType : VInductiveType where
  name := nonSortResultTypeName
  uvars := 0
  type := VExpr.const ``Nat []
  ctors := []

def nonSortResultDecl : VInductDecl := ⟨0, 0, [nonSortResultType]⟩

example : stage3DirectCore 0 0 nonSortResultType = false := rfl
example : nonSortResultDecl.checked? = none := rfl
example : VEnv.empty.addInduct nonSortResultDecl = none := rfl

/-- A constructor must return the family being declared, not merely any
well-formed closed type. -/
def wrongCtorHeadTypeName : Name := .mkSimple "WrongCtorHeadFixture"

def wrongCtorHeadCtorName : Name := .str wrongCtorHeadTypeName "mk"

def wrongCtorHeadType : VInductiveType where
  name := wrongCtorHeadTypeName
  uvars := 0
  type := VExpr.sort (.succ .zero)
  ctors := [⟨⟨0, VExpr.const ``Nat []⟩, wrongCtorHeadCtorName⟩]

def wrongCtorHeadDecl : VInductDecl := ⟨0, 0, [wrongCtorHeadType]⟩

example : stage3DirectCore 0 0 wrongCtorHeadType = false := rfl
example : wrongCtorHeadDecl.checked? = none := rfl
example : VEnv.empty.addInduct wrongCtorHeadDecl = none := rfl

/-- Constructor result parameters must be the declaration's parameter
variables in order, not arbitrary closed expressions of a plausible shape. -/
def wrongParamSpineTypeName : Name := .mkSimple "WrongParamSpineFixture"

def wrongParamSpineCtorName : Name := .str wrongParamSpineTypeName "mk"

def wrongParamSpineType : VInductiveType where
  name := wrongParamSpineTypeName
  uvars := 0
  type := VExpr.forallE (VExpr.sort (.succ .zero)) (VExpr.sort (.succ .zero))
  ctors := [⟨⟨0, VExpr.forallE (VExpr.sort (.succ .zero))
    ((VExpr.const wrongParamSpineTypeName []).app (.sort .zero))⟩,
    wrongParamSpineCtorName⟩]

def wrongParamSpineDecl : VInductDecl := ⟨0, 1, [wrongParamSpineType]⟩

example : stage3DirectCore 0 1 wrongParamSpineType = false := rfl
example : wrongParamSpineDecl.checked? = none := rfl
example : VEnv.empty.addInduct wrongParamSpineDecl = none := rfl

/-- `nparams` cannot exceed the actual leading pi telescope. -/
def shortParamDecl : VInductDecl := ⟨0, 1, [natType]⟩

example : stage3DirectCore 0 1 natType = false := rfl
example : shortParamDecl.checked? = none := rfl
example : VEnv.empty.addInduct shortParamDecl = none := rfl

/-- Declaration, family, and constructor universe counts must agree even when
the expressions themselves happen not to mention a level parameter. -/
def badTypeUvars : VInductiveType := { natType with uvars := 1 }
def badTypeUvarsDecl : VInductDecl := ⟨0, 0, [badTypeUvars]⟩

example : stage3DirectCore 0 0 badTypeUvars = false := rfl
example : badTypeUvarsDecl.checked? = none := rfl

def badCtorUvarsType : VInductiveType :=
  { natType with ctors := [{ natType.ctors[0] with uvars := 1 }, natType.ctors[1]] }
def badCtorUvarsDecl : VInductDecl := ⟨0, 0, [badCtorUvarsType]⟩

example : stage3DirectCore 0 0 badCtorUvarsType = false := rfl
example : badCtorUvarsDecl.checked? = none := rfl

/-! Environment-relative collisions are checked transactionally, after the
environment-independent descriptor has established internal `Nodup`. -/

def ctorCollisionEnv : VEnv :=
  (VEnv.empty.addConst ``Nat.zero ⟨0, .sort .zero⟩).get (by decide)

example : ctorCollisionEnv.constants ``Nat.zero = some ⟨0, .sort .zero⟩ := rfl
example : ctorCollisionEnv.addInduct natDecl = none :=
  VEnv.addInduct_eq_none_of_ctor_present (.head _) (.head _) ⟨_, rfl⟩

def recCollisionEnv : VEnv :=
  (VEnv.empty.addConst ``Nat.rec ⟨0, .sort .zero⟩).get (by decide)

example : recCollisionEnv.constants ``Nat.rec = some ⟨0, .sort .zero⟩ := rfl
example : recCollisionEnv.addInduct natDecl = none :=
  VEnv.addInduct_eq_none_of_rec_present
    (generation := natBlockGenerationChecked) rfl (.head _) ⟨_, rfl⟩

/-! ## Small elimination -/

/-- `Or` is the canonical small-elimination family: its motive remains in
`Prop`, so the generated recursor introduces no fresh universe parameter. -/
def orType : VInductiveType where
  name := ``Or
  uvars := 0
  type := vconst(type_of% @Or).type
  ctors := [⟨vconst(type_of% @Or.inl), ``Or.inl⟩,
    ⟨vconst(type_of% @Or.inr), ``Or.inr⟩]

def orDecl : VInductDecl := ⟨0, 2, [orType]⟩

def orChecked : orDecl.Checked := orDecl.checked?.get (by decide)

example : orDecl.stage3 = true := rfl
example : orChecked.elimination = .small := rfl
example : orChecked.kTarget = false := rfl
example : orChecked.recursor.uvars = 0 := rfl
example : orChecked.recursor = vconst(type_of% @Or.rec) := rfl
example : orChecked.generatedRules[0]? =
    some (vdefeq(a b motive inl inr h =>
      @Or.rec a b motive inl inr (@Or.inl a b h) ≡ inl h)) := rfl
example : orChecked.generatedRules[1]? =
    some (vdefeq(a b motive inl inr h =>
      @Or.rec a b motive inl inr (@Or.inr a b h) ≡ inr h)) := rfl
example : (VEnv.empty.addInduct orDecl).isSome = true := rfl

/-- `And` is the canonical singleton-Prop exception: both constructor fields
are proofs, so Lean legitimately gives it a large eliminator with one fresh
universe parameter. -/
def andType : VInductiveType where
  name := ``And
  uvars := 0
  type := vconst(type_of% @And).type
  ctors := [⟨vconst(type_of% @And.intro), ``And.intro⟩]

def andDecl : VInductDecl := ⟨0, 2, [andType]⟩

def andChecked : andDecl.Checked := andDecl.checked?.get (by decide)

example : andDecl.stage3 = true := rfl
example : andChecked.elimination = .large := rfl
/-- Large elimination and K eligibility are independent: `And` has the
singleton-proof elimination exception, but its constructor has fields. -/
example : andChecked.kTarget = false := rfl
example : andChecked.recursor.uvars = 1 := rfl
example : andChecked.recursor = vconst(type_of% @And.rec) := rfl
example : andChecked.generatedRules[0]? =
    some (vdefeq(a b motive intro left right =>
      @And.rec a b motive intro (@And.intro a b left right) ≡
        intro left right)) := rfl
example : (VEnv.empty.addInduct andDecl).isSome = true := rfl

/-! ## Conservativity: malformed declarations and name collisions refuse. -/

/-- A name collision rejects the whole transaction. -/
example (env : VEnv) (h : env.contains ``Nat) : env.addInduct natDecl = none :=
  VEnv.addInduct_eq_none_of_type_present (.head _) h
