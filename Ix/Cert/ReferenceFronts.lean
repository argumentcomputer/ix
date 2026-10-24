import Ix.Cert.ConversionValues
import IxC.Kernel.Verify.Rename.UnionRun

/-! # Exact definition fronts in an accepted ordered stream

The same accepting fuel witnesses the indexed prefix, declaration and
suffix. The actual header/value fronts determine the annotated definition,
and the successful suffix preserves its exact lookup in the final env.
No source-form typing or model of an unrelated prefix is supplied here.
-/

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics

universe w
variable {md : Mode}

/-- Proof-only output of the actual accepted stream. Its prefix and final
stored body are tied to one declaration index and one real fuel witness. -/
def DefinitionFrontAt (ev : Evidences md) (ds : List (Declaration md)) (envA : Env md)
    (i : Nat) (cv : Ix.Kernel.ConstantVal md) (raw : Ix.Kernel.Expr md) (hint : ReducibilityHint)
    (F : Nat) (before : Env md) (expected checked : Ix.Kernel.Expr md) : Prop :=
  let step := checkDecl .verified (fueledOps .verified F) ev
  let after : Env md :=
    ⟨.defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked hint :: before.consts⟩
  ds[i]? = some (.defnDecl cv raw hint) ∧
  checkDeclsPure .verified (fueledOps .verified F) ev ds = .ok envA ∧
  (ds.take i).foldlM step Env.empty = .ok before ∧
  step before (.defnDecl cv raw hint) = .ok after ∧
  (ds.drop (i + 1)).foldlM step after = .ok envA ∧
  ConstantValRun .verified F before cv expected ∧
  ValueFrontRun .verified F before cv raw expected checked ∧
  envA.find? cv.name = some (.defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked hint)

/-- Every actual definition index has its exact reference-prefix front,
including generated definitions and native-operation declaration checks.
The suffix preserves the computed body, not just an install skeleton. -/
theorem reference_definition_front_at
    {ev : Evidences md} {ds : List (Declaration md)} {envA : Env md}
    {i : Nat} {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (accepted : Cached.AcceptsRef .verified ev ds envA)
    (atDecl : ds[i]? = some (.defnDecl cv raw hint)) :
    ∃ F before expected checked,
      DefinitionFrontAt ev ds envA i cv raw hint F before expected checked := by
  obtain ⟨F, whole⟩ := accepted
  obtain ⟨bound, atValue⟩ := List.getElem?_eq_some_iff.mp atDecl
  have split : ds = ds.take i ++ .defnDecl cv raw hint :: ds.drop (i + 1) := by
    have eq := List.take_append_drop i ds
    rw [List.drop_eq_getElem_cons bound, atValue] at eq
    exact eq.symm
  have run := whole
  unfold checkDeclsPure at run
  rw [split] at run
  obtain ⟨before, prefixRun, rest⟩ := foldlM_append_ok run
  rw [List.foldlM_cons] at rest
  cases stepRun : checkDecl .verified (fueledOps .verified F) ev before (.defnDecl cv raw hint) with
  | error err => rw [stepRun] at rest; exact nomatch rest
  | ok after =>
    rw [stepRun] at rest
    change (ds.drop (i + 1)).foldlM (checkDecl .verified (fueledOps .verified F) ev) after = .ok envA at rest
    obtain ⟨expected, checked, header, value, installed, _, _⟩ := declDefnRun_of stepRun
    have immediate : after.find? cv.name =
        some (.defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked hint) := by
      rw [installed]
      simp only [Env.find?_cons, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal, ↓reduceIte]
    have growth := foldlM_checkDecl_post .verified (fueledOps .verified F) ev
      (ds.drop (i + 1)) after envA rest
    refine ⟨F, before, expected, checked, atDecl, whole, prefixRun, ?_, ?_, header, value,
      growth.persist immediate⟩
    · exact installed ▸ stepRun
    · exact installed ▸ rest

/-- Accepted fuel witnesses need not be equal. The exact stream prefix
and its final stored annotated definition determine the same front data. -/
theorem DefinitionFrontAt.unique
    {ev : Evidences md} {ds : List (Declaration md)} {envA B1 B2 : Env md}
    {i F1 F2 : Nat} {cv : Ix.Kernel.ConstantVal md} {raw T1 T2 V1 V2 : Ix.Kernel.Expr md}
    {hint : ReducibilityHint}
    (a : DefinitionFrontAt ev ds envA i cv raw hint F1 B1 T1 V1)
    (b : DefinitionFrontAt ev ds envA i cv raw hint F2 B2 T2 V2) :
    B1 = B2 ∧ T1 = T2 ∧ V1 = V2 := by
  obtain ⟨_, _, preA, _, _, _, _, storedA⟩ := a
  obtain ⟨_, _, preB, _, _, _, _, storedB⟩ := b
  have same := Option.some.inj (storedA.symm.trans storedB)
  exact ⟨checkDeclsFrom_deterministic preA preB,
    congrArg (fun c : Ix.Kernel.ConstantInfo md => c.toConstantVal.type) same,
    (Ix.Kernel.ConstantInfo.defnInfo.inj same).2.1⟩

/-- The EXACT stored checked body denotes this constant under every
supplied FINAL model. No prefix model or interpretation is chosen. -/
theorem DefinitionFrontAt.denotes {V : Type w} [SetTheory V]
    {ev : Evidences md} {ds : List (Declaration md)} {envA before : Env md}
    {i F : Nat} {cv : Ix.Kernel.ConstantVal md} {raw expected checked : Ix.Kernel.Expr md}
    {hint : ReducibilityHint}
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (M : Cached.StrongModel V envA) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.model.cval envA φ ρ checked (M.model.cval cv.name φ) := by
  obtain ⟨_, _, _, _, _, _, _, stored⟩ := front
  exact M.defn_value (Semantics.Env.find?_mem stored) φ ρ

/-- ONE actual prepared ordered stream and its evidence supply the front
family for EVERY definition index, including generated declarations. The
witnesses are reused from the given reference acceptance, before any model
is supplied. Source-form typing, changed-caller readback/Translate/image
provenance and final-model transport to these prefixes remain separate. -/
theorem ixon_definition_fronts
    {binding : Admission.Binding} {limits : Admission.Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (accepted : IxonAcceptsRef binding limits ixe S order envA) :
    ClosureOrder ixe S order ∧
    ∃ t pre ev ds,
      Admission.admitBinding Address.admissionHash binding = .ok t ∧
      Reader.preludeFor t = .ok pre ∧
      Admission.prepareWith Address.admissionHash binding pre limits
        (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe) = .ok (ev, ds) ∧
      Cached.AcceptsRef .verified ev ds.toList envA ∧
      ∀ (i : Nat) (cv : Ix.Kernel.ConstantVal .anon) (raw : Ix.Kernel.Expr .anon)
        (hint : ReducibilityHint),
        ds.toList[i]? = some (.defnDecl cv raw hint) →
        ∃ F before expected checked,
          DefinitionFrontAt ev ds.toList envA i cv raw hint F before expected checked := by
  obtain ⟨ordered, t, pre, ev, ds, admitted, prelude, prepared, run⟩ := accepted
  refine ⟨ordered, t, pre, ev, ds, admitted, prelude, prepared, run, ?_⟩
  intro i cv raw hint atDecl
  exact reference_definition_front_at run atDecl

end Ix.Cert.ReferenceFronts
