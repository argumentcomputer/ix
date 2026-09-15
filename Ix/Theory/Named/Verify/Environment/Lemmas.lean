/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Std.SMap
import Ix.Theory.Named.Reference.Declaration
import Ix.Theory.Named.Verify.Environment.Basic

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstVal.sf_mono (hsf : safety ≤ safety')
    (H : TrConstVal safety' env ci ci') : TrConstVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

theorem TrDefVal.sf_mono (hsf : safety ≤ safety')
    (H : TrDefVal safety' env ci ci') : TrDefVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

/- The former blanket `TrEnv'.sf_mono` was deleted at the v4.33
reconciliation: upstream's new `TrEnv'.ignore` constructor makes lowering the
safety mode of an arbitrary translation unsound (a declaration skipped at a
strict mode must be translated, not skipped, at a laxer one). Fixture
environments that need every safety mode now state their `TrEnv'` derivations
parametrically in `safety` instead. -/

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  | structEta : Aligned C venv → Aligned C (venv.addStructEta rule)

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih
  | structEta _ ih => exact ih

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih
  | structEta _ ih => exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem AddInductConstant.map_wf
    (H : AddInductConstant kind C₁ env₁ ci C₂ env₂) (wf : C₁.WF) : C₂.WF := by
  rw [H.map_add]
  exact wf.insert _ _ H.map_fresh

/-- The implementation metadata inserted by one inductive-constant step is
still available at that step's output boundary. -/
theorem AddInductConstant.map_lookup
    (H : AddInductConstant kind C₁ env₁ ci C₂ env₂)
    (wf : C₁.WF) : C₂.find? ci.name = some H.info := by
  simp [H.map_add, wf.find?_insert]

/-- An inductive-metadata insertion preserves every lookup already present in
the input map.  Freshness rules out the only key at which `insert` could
replace that entry. -/
theorem AddInductConstant.preserve_map_lookup
    (H : AddInductConstant kind C₁ env₁ ci' C₂ env₂)
    (wf : C₁.WF) {name : Name} {info : ConstantInfo}
    (hlookup : C₁.find? name = some info) :
    C₂.find? name = some info := by
  rw [H.map_add, wf.find?_insert]
  split
  · rename_i heq
    have hname : ci'.name = name := by simpa using heq
    subst name
    have hfresh := H.map_fresh
    rw [hlookup] at hfresh
    contradiction
  · exact hlookup

theorem InductConstantKind.Matches.deltaValue?_eq_none
    {kind : InductConstantKind} {ci : ConstantInfo}
    (H : InductConstantKind.Matches kind ci) : ci.deltaValue? = none := by
  cases kind <;> cases ci <;>
    simp_all [InductConstantKind.Matches, ConstantInfo.deltaValue?]

/-- An inductive metadata insertion cannot introduce a declaration body.
Consequently, any value-bearing entry in the result map was already present
in the input map. -/
theorem AddInductConstant.old_of_value
    (H : AddInductConstant kind C₁ env₁ ci' C₂ env₂) (wf : C₁.WF)
    (hout : C₂.find? name = some ci) (hv : ci.deltaValue? = some v) :
    C₁.find? name = some ci := by
  rw [H.map_add, wf.find?_insert] at hout
  split at hout
  · cases hout
    have hnone := InductConstantKind.Matches.deltaValue?_eq_none H.kind_eq
    simp_all
  · exact hout

theorem AddInductConstants.map_wf :
    AddInductConstants kind C₁ env₁ cis C₂ env₂ → C₁.WF → C₂.WF
  | .nil, wf => wf
  | .cons h hrest, wf => hrest.map_wf (h.map_wf wf)

/-- A whole insertion fold preserves every lookup from its input map. -/
theorem AddInductConstants.preserve_map_lookup
    (H : AddInductConstants kind C₁ env₁ cis C₂ env₂)
    (wf : C₁.WF) {name : Name} {info : ConstantInfo}
    (hlookup : C₁.find? name = some info) :
    C₂.find? name = some info := by
  induction H with
  | nil => exact hlookup
  | cons h hrest ih =>
    exact ih (h.map_wf wf) (h.preserve_map_lookup wf hlookup)

/-- Final-map evidence for any member of an inductive metadata fold.  The
result retains the exact implementation object, its role tag, and its
translation against the final Theory environment. -/
theorem AddInductConstants.translated_lookup
    (H : AddInductConstants kind C₁ env₁ cis C₂ env₂)
    (wf : C₁.WF) {ci : VConstVal} (hmem : ci ∈ cis) : ∃ info,
      C₂.find? ci.name = some info ∧
      kind.Matches info ∧ TrConstVal .safe env₂ info ci := by
  induction H with
  | nil => contradiction
  | cons h hrest ih =>
    rcases List.mem_cons.1 hmem with rfl | hmem
    · refine ⟨h.info, ?_, h.kind_eq, ?_⟩
      exact hrest.preserve_map_lookup (h.map_wf wf) (h.map_lookup wf)
      exact h.tr.mono (h.le.trans hrest.le)
    · exact ih (h.map_wf wf) hmem

theorem AddInductConstants.old_of_value :
    (H : AddInductConstants kind C₁ env₁ cis C₂ env₂) → C₁.WF →
    C₂.find? name = some ci → ci.deltaValue? = some v → C₁.find? name = some ci
  | .nil, _, hout, _ => hout
  | .cons h hrest, wf, hout, hv =>
    h.old_of_value wf (hrest.old_of_value (h.map_wf wf) hout hv) hv

/-! ## Final translated metadata inventories -/

/-- Final-map and final-environment evidence for the family emitted by a
singleton inductive replay. -/
theorem AddInductTrace.type_translated_lookup
    (H : AddInductTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF) :
    ∃ info,
      C₂.find? H.generation.block.sourceType.name = some info ∧
      InductConstantKind.induct.Matches info ∧
      TrConstVal .safe env₂ info H.generation.block.sourceType.toVConstVal := by
  refine ⟨H.addType.info, ?_, H.addType.kind_eq, ?_⟩
  · exact H.addRec.preserve_map_lookup
      (H.addCtors.map_wf (H.addType.map_wf wf))
      (H.addCtors.preserve_map_lookup (H.addType.map_wf wf)
        (H.addType.map_lookup wf))
  · exact H.addType.tr.mono
      (H.addType.le.trans <| H.addCtors.le.trans <|
        H.addRec.le.trans H.addRules.le)

/-- Final-map and final-environment evidence for every constructor emitted by
a singleton inductive replay. -/
theorem AddInductTrace.constructor_translated_lookup
    (H : AddInductTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ H.generation.block.sourceType.ctors) :
    ∃ info,
      C₂.find? constructor.name = some info ∧
      InductConstantKind.ctor.Matches info ∧
      TrConstVal .safe env₂ info constructor := by
  obtain ⟨info, hlookup, hkind, htr⟩ :=
    H.addCtors.translated_lookup (H.addType.map_wf wf) hconstructor
  exact ⟨info,
    H.addRec.preserve_map_lookup (H.addCtors.map_wf (H.addType.map_wf wf)) hlookup,
    hkind, htr.mono (H.addRec.le.trans H.addRules.le)⟩

/-- Final-map and final-environment evidence for the recursor emitted by a
singleton inductive replay. -/
theorem AddInductTrace.recursor_translated_lookup
    (H : AddInductTrace C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) : ∃ info,
      C₂.find? (inductGenerationRecVal H.generation).name = some info ∧
      InductConstantKind.recursor.Matches info ∧
      TrConstVal .safe env₂ info (inductGenerationRecVal H.generation) := by
  exact ⟨H.addRec.info, H.addRec.map_lookup
      (H.addCtors.map_wf (H.addType.map_wf wf)), H.addRec.kind_eq,
    H.addRec.tr.mono (H.addRec.le.trans H.addRules.le)⟩

/-- Final translated lookup for every source family in a mutual block. -/
theorem AddInductBlockTrace.family_translated_lookup
    (H : AddInductBlockTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {family : VInductiveType} (hfamily : family ∈ decl.types) : ∃ info,
      C₂.find? family.name = some info ∧
      InductConstantKind.induct.Matches info ∧
      TrConstVal .safe env₂ info family.toVConstVal := by
  have hmember : family.toVConstVal ∈ decl.blockTypeConstants :=
    List.mem_map.2 ⟨family, hfamily, rfl⟩
  obtain ⟨info, hlookup, hkind, htr⟩ :=
    H.addTypes.translated_lookup wf hmember
  exact ⟨info,
    H.addRecs.preserve_map_lookup
      (H.addCtors.map_wf (H.addTypes.map_wf wf))
      (H.addCtors.preserve_map_lookup (H.addTypes.map_wf wf) hlookup),
    hkind, htr.mono (H.addCtors.le.trans <| H.addRecs.le.trans H.addRules.le)⟩

/-- Final translated lookup for every flattened constructor in a mutual
block. -/
theorem AddInductBlockTrace.constructor_translated_lookup
    (H : AddInductBlockTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ decl.blockConstructorConstants) : ∃ info,
      C₂.find? constructor.name = some info ∧
      InductConstantKind.ctor.Matches info ∧
      TrConstVal .safe env₂ info constructor := by
  obtain ⟨info, hlookup, hkind, htr⟩ :=
    H.addCtors.translated_lookup (H.addTypes.map_wf wf) hconstructor
  exact ⟨info,
    H.addRecs.preserve_map_lookup
      (H.addCtors.map_wf (H.addTypes.map_wf wf)) hlookup,
    hkind, htr.mono (H.addRecs.le.trans H.addRules.le)⟩

/-- Final translated lookup for every generated recursor in a mutual block. -/
theorem AddInductBlockTrace.recursor_translated_lookup
    (H : AddInductBlockTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {recursor : VConstVal} (hrecursor : recursor ∈ H.generation.recursors) :
    ∃ info,
      C₂.find? recursor.name = some info ∧
      InductConstantKind.recursor.Matches info ∧
      TrConstVal .safe env₂ info recursor := by
  obtain ⟨info, hlookup, hkind, htr⟩ := H.addRecs.translated_lookup
    (H.addCtors.map_wf (H.addTypes.map_wf wf)) hrecursor
  exact ⟨info, hlookup, hkind, htr.mono H.addRules.le⟩

/-- Final translated lookup for every source family in a nested replay. -/
theorem AddInductNestedTrace.family_translated_lookup
    (H : AddInductNestedTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {family : VInductiveType} (hfamily : family ∈ decl.types) : ∃ info,
      C₂.find? family.name = some info ∧
      InductConstantKind.induct.Matches info ∧
      TrConstVal .safe env₂ info family.toVConstVal := by
  have hmember : family.toVConstVal ∈ decl.blockTypeConstants :=
    List.mem_map.2 ⟨family, hfamily, rfl⟩
  obtain ⟨info, hlookup, hkind, htr⟩ :=
    H.addTypes.translated_lookup wf hmember
  exact ⟨info,
    H.addRecs.preserve_map_lookup
      (H.addCtors.map_wf (H.addTypes.map_wf wf))
      (H.addCtors.preserve_map_lookup (H.addTypes.map_wf wf) hlookup),
    hkind, htr.mono (H.addCtors.le.trans <| H.addRecs.le.trans H.addRules.le)⟩

/-- Final translated lookup for every source constructor in a nested replay. -/
theorem AddInductNestedTrace.constructor_translated_lookup
    (H : AddInductNestedTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ decl.blockConstructorConstants) : ∃ info,
      C₂.find? constructor.name = some info ∧
      InductConstantKind.ctor.Matches info ∧
      TrConstVal .safe env₂ info constructor := by
  obtain ⟨info, hlookup, hkind, htr⟩ :=
    H.addCtors.translated_lookup (H.addTypes.map_wf wf) hconstructor
  exact ⟨info,
    H.addRecs.preserve_map_lookup
      (H.addCtors.map_wf (H.addTypes.map_wf wf)) hlookup,
    hkind, htr.mono (H.addRecs.le.trans H.addRules.le)⟩

/-- Final translated lookup for every restored recursor in a nested replay. -/
theorem AddInductNestedTrace.recursor_translated_lookup
    (H : AddInductNestedTrace C₁ env₁ decl C₂ env₂) (wf : C₁.WF)
    {recursor : VConstVal} (hrecursor : recursor ∈ H.nested.recursors) : ∃ info,
      C₂.find? recursor.name = some info ∧
      InductConstantKind.recursor.Matches info ∧
      TrConstVal .safe env₂ info recursor := by
  obtain ⟨info, hlookup, hkind, htr⟩ := H.addRecs.translated_lookup
    (H.addCtors.map_wf (H.addTypes.map_wf wf)) hrecursor
  exact ⟨info, hlookup, hkind, htr.mono H.addRules.le⟩

theorem AddInduct.map_wf (H : AddInduct C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) : C₂.WF := by
  rcases H with ⟨H⟩
  exact H.addRec.map_wf <| H.addCtors.map_wf <| H.addType.map_wf wf

theorem AddInduct.old_of_value (H : AddInduct C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) (hout : C₂.find? name = some ci) (hv : ci.deltaValue? = some v) :
    C₁.find? name = some ci := by
  rcases H with ⟨H⟩
  have wfType := H.addType.map_wf wf
  have wfCtors := H.addCtors.map_wf wfType
  exact H.addType.old_of_value wf
    (H.addCtors.old_of_value wfType (H.addRec.old_of_value wfCtors hout hv) hv) hv

theorem AddInductBlock.map_wf
    (H : AddInductBlock C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) : C₂.WF := by
  rcases H with ⟨H⟩
  exact H.addRecs.map_wf <| H.addCtors.map_wf <|
    H.addTypes.map_wf wf

theorem AddInductBlock.old_of_value
    (H : AddInductBlock C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) (hout : C₂.find? name = some ci)
    (hv : ci.deltaValue? = some v) : C₁.find? name = some ci := by
  rcases H with ⟨H⟩
  have wfTypes := H.addTypes.map_wf wf
  have wfCtors := H.addCtors.map_wf wfTypes
  exact H.addTypes.old_of_value wf
    (H.addCtors.old_of_value wfTypes
      (H.addRecs.old_of_value wfCtors hout hv) hv) hv

theorem AddInductNested.map_wf
    (H : AddInductNested C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) : C₂.WF := by
  rcases H with ⟨H⟩
  exact H.addRecs.map_wf <| H.addCtors.map_wf <|
    H.addTypes.map_wf wf

theorem AddInductNested.old_of_value
    (H : AddInductNested C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) (hout : C₂.find? name = some ci)
    (hv : ci.deltaValue? = some v) : C₁.find? name = some ci := by
  rcases H with ⟨H⟩
  have wfTypes := H.addTypes.map_wf wf
  have wfCtors := H.addCtors.map_wf wfTypes
  exact H.addTypes.old_of_value wf
    (H.addCtors.old_of_value wfTypes
      (H.addRecs.old_of_value wfCtors hout hv) hv) hv

theorem Aligned.addInductConstant
    (wf : Aligned safety C₁ env₁)
    (H : AddInductConstant kind C₁ env₁ ci C₂ env₂) : Aligned safety C₂ env₂ := by
  rw [H.map_add]
  exact wf.const H.map_fresh (H.tr.1.sf_mono DefinitionSafety.le_safe)
    H.env_add H.tr.2

theorem Aligned.addInductConstants :
    AddInductConstants kind C₁ env₁ cis C₂ env₂ →
      Aligned safety C₁ env₁ → Aligned safety C₂ env₂
  | .nil, wf => wf
  | .cons h hrest, wf =>
    Aligned.addInductConstants hrest (wf.addInductConstant h)

theorem Aligned.addDefEqFold : ∀ (dfs : List VDefEq),
    Aligned safety C env → Aligned safety C (dfs.foldl VEnv.addDefEq env)
  | [], wf => wf
  | _ :: dfs, wf => addDefEqFold dfs wf.defeq

theorem Aligned.addInduct (H : AddInduct C₁ env₁ decl C₂ env₂)
    (wf : Aligned safety C₁ env₁) : Aligned safety C₂ env₂ := by
  rcases H with ⟨H⟩
  rw [← H.addRules.to_add]
  have wfType := wf.addInductConstant H.addType
  have wfCtors := wfType.addInductConstants H.addCtors
  have wfRec := wfCtors.addInductConstant H.addRec
  exact wfRec.addDefEqFold _

theorem Aligned.addInductBlock
    (H : AddInductBlock C₁ env₁ decl C₂ env₂)
    (wf : Aligned safety C₁ env₁) : Aligned safety C₂ env₂ := by
  rcases H with ⟨H⟩
  rw [← H.addRules.to_add]
  have wfTypes := wf.addInductConstants H.addTypes
  have wfCtors := wfTypes.addInductConstants H.addCtors
  have wfRecs := wfCtors.addInductConstants H.addRecs
  exact wfRecs.addDefEqFold _

theorem Aligned.addInductNested
    (H : AddInductNested C₁ env₁ decl C₂ env₂)
    (wf : Aligned safety C₁ env₁) : Aligned safety C₂ env₂ := by
  rcases H with ⟨H⟩
  rw [← H.addRules.to_add]
  have wfTypes := wf.addInductConstants H.addTypes
  have wfCtors := wfTypes.addInductConstants H.addCtors
  have wfRecs := wfCtors.addInductConstants H.addRecs
  exact wfRecs.addDefEqFold _

#guard_named_axioms Ix.Theory.Named.Aligned.addInduct [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.Aligned.addInductBlock [propext, Classical.choice, Quot.sound]

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Ix.Theory.Named.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Ix.Theory.Named.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Ix.Theory.Named.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h
  | inductStaging h _ _ ih => exact ih.addInductConstant h
  | induct h _ ih => exact ih.addInduct h
  | inductBlock h _ ih => exact ih.addInductBlock h
  | inductNested h _ ih => exact ih.addInductNested h
  | structEta _ _ ih => exact ih.structEta

/- Since the v4.33 reconciliation the `mutualDef` arm routes through
`insertDefs`, whose `SMap` reasoning uses the classified persistent-map
container contracts; the closure is pinned so any further growth is
reviewed. -/
#guard_named_axioms Ix.Theory.Named.TrEnv'.aligned [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩
  | structEta h1 ih =>
    let ⟨_, h1, h2⟩ := ih h
    exact ⟨_, h1, h2.mono VEnv.addStructEta_le⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩
  | structEta h1 ih =>
    let ⟨h1, h2⟩ := ih h hs
    exact ⟨h1, h2.mono VEnv.addStructEta_le⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem VEnv.addDefEqs_le : ∀ {cis' : List VDefVal} {venv : VEnv}, venv ≤ venv.addDefEqs cis'
  | [], _ => .rfl
  | ci :: cis, venv => by
    show venv ≤ VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis
    exact VEnv.addDefEq_le.trans VEnv.addDefEqs_le

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Ix.Theory.Named.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | inductStaging h1 _ H ih =>
    exact (ih (h1.old_of_value H.map_wf h hv)).mono h1.le
  | induct h1 H ih =>
    exact (ih (h1.old_of_value H.map_wf h hv)).mono h1.le
  | inductBlock h1 H ih =>
    exact (ih (h1.old_of_value H.map_wf h hv)).mono h1.le
  | inductNested h1 H ih =>
    exact (ih (h1.old_of_value H.map_wf h hv)).mono h1.le
  | structEta _ H ih =>
    exact (ih h).mono VEnv.addStructEta_le

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv
