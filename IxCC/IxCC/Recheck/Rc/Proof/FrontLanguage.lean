import IxCC.Recheck.Rc.Types
import IxCC.Recheck.Rc.Proof.SourceFir
import IxCC.Recheck.Rc.Proof.RetainedReplay
import IxCC.Rt.Proof.Lang

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Lang Obs Result)
open IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc.Procs

def Front.source (f : Front) : Sem.Viewed Lam.Erase.Proof.CheckedProgram :=
  ⟨⟨f.src, f.checked⟩, f.view⟩

def Front.loaded (f : Front) (model : Rt.Model) : Rt.Loaded :=
  Rt.Loaded.ofLowered f.cfg.base f.lowered f.tys model

/-- Conditional only on the already-retained source value witness: a result
accepted by the source view is exactly the observed target value. Rejected
views impose the existing source-stuck behavior. -/
def ViewedFirRel (f : Front) (root : Nat) (logical : Fir.Val) (observed : Option Obs) : Prop :=
  ∀ source, SourceFirWitness f.anf source logical →
    Result.Refines Eq (Sem.viewResult f.view root source) (.ok observed)

theorem returned_view {f : Front} {root : Nat} {logical : Fir.Val}
    {P : Cfg.Rc.Program} {pairs : List (Nat × Cfg.Fun)} {program : Lir.Program}
    {origin : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {context base limit : Lir.Word} {regionBytes : Nat}
    (returned : Returned P pairs program origin addresses external context base limit regionBytes logical)
    (entry : Rt.Entry) (typeEq : entry.ty = f.tys root) :
    ViewedFirRel f root logical
      (entry.observe (regionBytes / 8) [returned.word] returned.memory) := by
  intro source witness
  unfold Front.view treeViewOf Sem.viewResult Rt.Entry.observe
  rw [typeEq]
  dsimp only
  cases type : f.tys root with
  | none => exact .ok rfl
  | some pair =>
    obtain ⟨signature, ty⟩ := pair
    cases source with
    | none => exact .stuck
    | some source =>
      cases viewed : Readback.treeView f.anf.ctors signature ty source with
      | none => simp only [Option.bind_some, viewed, Option.map_none]; exact .stuck
      | some observed =>
        simp only [Option.bind_some, viewed, Option.map_some]
        exact .ok (witness.observe returned viewed).symm

/-- Compose the retained checked source relation with the physical loaded
relation. The whole driver theorem supplies `physical`; it is not a field
of the executable admission contract. -/
theorem source_view_refines_of_fir {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (accepted : runFront cfg P cert = .ok f) (model : Rt.Model)
    (physical : ∀ input : Nat × List Nat,
      Sem.Behaviour.Refines (ViewedFirRel f input.1)
        (Lang.behaviour f.fir input) (Lang.behaviour (f.loaded model) input)) :
    Sem.RefinesOn (f.Covered cert) f.source (f.loaded model) := by
  intro input hi
  rw [Sem.Viewed.behaviour_eq]
  have composed := (source_fir_retained accepted input hi).trans (physical input)
  change Sem.Behaviour.Refines Eq
    ((Lang.behaviour (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) input).then
      fun value => Sem.viewResult f.view input.1 (Lang.obs value))
    (Lang.behaviour (f.loaded model) input)
  generalize Lang.behaviour (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) input = sourceBehavior
    at composed ⊢
  generalize Lang.behaviour (f.loaded model) input = targetBehavior at composed ⊢
  cases composed with
  | terminates related =>
    obtain ⟨logical, witness, observed⟩ := related
    exact (observed _ witness).toBehaviour
  | diverges => exact .diverges
  | trap => exact .trap
  | stuck => exact .stuck
  | resource failure => exact .resource failure

end IxCC.Recheck.RcReplay
