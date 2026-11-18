import IxVMRefinement.Decl.TwinRec
import IxVMRefinement.Decl.VerifiedRunMap
import IxC.Kernel.Verify.Inductives.TwinRun
import IxC.Kernel.Model.NoRecBlock
import Ix.IxVM.Consistency.StoredCheck

/-! # IxC's twin record at the positional package, from a run of IxC's twin check

`NativeTwin.check` is IxC's executable check of a second recursor block against the recursors an
environment stores: each member's front door, a stored canonical recursor above it (`WrapRel`
from the canonical type to the member's checked type, and from each canonical rule, renamed to
the member's peers, to the member's checked rule), its model companion copied, and the rules'
stages. A successful run gives IxC's record at the package of runs (`NativeTwin.check_semantic`);
every judgement of a verified run has a rules-tier derivation (`verifiedRunMap`), and a
rules-tier derivation is one of the positional package (`DeclRecTwinRunJ.to_twinPos`). So a run
of the check that is accepted gives the record the twin step concludes
(`declRecTwinRunJ_twinPos_of_check`), and a closed instance is proved by evaluating the check.

The check accepts only where each canonical member is above the second record's
(`Facts.lean`, `CanonAbove`); where the second record's member is above the canonical one it
declines, and the record then needs a typed generated rule, which this route does not give. -/

namespace IxVM.Refinement.Typing.TwinFamily

open Ix.Kernel (Env ConstantInfo ConstantVal RecRule fueledOps)
open Ix.Kernel.Semantics (Judgements DeclRecTwinRunJ ConstantValCheckJ TwinRuleJ)
open IxVM.Refinement.Decl (JudgementsMap verifiedRunMap twinPosRulesJ)

/-- A map of judgement packages carries IxC's twin record. -/
theorem declRecTwinRunJ_map {md : Ix.Kernel.Mode} {J K : Judgements md}
    (M : JudgementsMap J K) {env env₂ : Env md} {block : List (ConstantInfo md)}
    (h : DeclRecTwinRunJ J env block env₂) : DeclRecTwinRunJ K env block env₂ := by
  obtain ⟨ws, f, hne, hblk, rfl, hnd, hfr, hf, hall⟩ := h
  refine ⟨ws, f, hne, hblk, rfl, hnd, hfr, hf, fun w hw => ?_⟩
  obtain ⟨⟨ty', hrun, hcv⟩, hlf, hfkC, hlps, hmod, ⟨tyG, htw1, htw2, htgen⟩, hlenW, hrules⟩ :=
    hall w hw
  refine ⟨⟨ty', M.constantValRun hrun, hcv⟩, hlf, hfkC, hlps, hmod, ⟨tyG, htw1, htw2, ?_⟩,
    hlenW, ?_⟩
  · rcases htgen with h | ⟨t1, t2, t3, t4, sty, hinf⟩
    · exact Or.inl h
    · exact Or.inr ⟨t1, t2, t3, t4, sty, M.infer hinf⟩
  · refine forall₂_imp hrules fun p rC hr => ?_
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      rhsG, hw1, hw2, hgen⟩ := hr
    refine ⟨h1, h2, h3, h4, M.annot h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      rhsG, hw1, hw2, ?_⟩
    rcases hgen with h | ⟨g1, g2, g3, g4, rty, hinf⟩
    · exact Or.inl h
    · exact Or.inr ⟨g1, g2, g3, g4, rty, M.infer hinf⟩
where
  forall₂_imp {α β : Type} {R S : α → β → Prop} :
      ∀ {l₁ : List α} {l₂ : List β}, Ix.Kernel.Semantics.Forall₂ R l₁ l₂ →
        (∀ a b, R a b → S a b) → Ix.Kernel.Semantics.Forall₂ S l₁ l₂
    | _, _, .nil, _ => .nil
    | _, _, .cons hab hr, h => .cons (h _ _ hab) (forall₂_imp hr h)

/-- **IxC's twin record at the positional package, from an accepted run of IxC's twin check** at
the verified mode. -/
theorem declRecTwinRunJ_twinPos_of_check {fuel : Nat} {env env₂ : Env .anon}
    {block : List (ConstantInfo .anon)}
    (h : Ix.Kernel.NativeTwin.check (fueledOps .verified fuel) env block = .ok env₂) :
    DeclRecTwinRunJ twinPosRulesJ env block env₂ :=
  Decl.DeclRecTwinRunJ.to_twinPos
    (declRecTwinRunJ_map (verifiedRunMap fuel) (Ix.Kernel.NativeTwin.check_semantic h))

/-- Whether a run of IxC's twin check is accepted. -/
def twinCheckAccepts (fuel : Nat) (env : Env .anon) (block : List (ConstantInfo .anon)) : Bool :=
  match Ix.Kernel.NativeTwin.check (fueledOps .verified fuel) env block with
  | .ok _ => true
  | .error _ => false

/-- **An accepted run, evaluated, gives IxC's twin record at the positional package.** -/
theorem declRecTwinRunJ_twinPos_of_accepts {fuel : Nat} {env : Env .anon}
    {block : List (ConstantInfo .anon)} (h : twinCheckAccepts fuel env block = true) :
    ∃ env₂, DeclRecTwinRunJ twinPosRulesJ env block env₂ := by
  unfold twinCheckAccepts at h
  split at h
  · rename_i env₂ hrun
    exact ⟨env₂, declRecTwinRunJ_twinPos_of_check hrun⟩
  · cases h

/-- Whether a run of IxC's twin check is accepted, and after it each member of the block is
stored as a constant that stores it (`IxVM.Consistency.storedAsCheck`) and has a model
companion. -/
def twinStepCheck (fuel : Nat) (env : Env .anon) (block : List (ConstantInfo .anon)) : Bool :=
  match Ix.Kernel.NativeTwin.check (fueledOps .verified fuel) env block with
  | .ok env₂ => block.all fun ci =>
      (match env₂.find? ci.name with
        | some c => (IxVM.Consistency.storedAsCheck fuel c ci).isSome
        | none => false) &&
      (match env₂.find? (Ix.Kernel.auxKey ci.name .model) with
        | some (.defnInfo _ _ _) => true
        | _ => false)
  | .error _ => false

/-- **The second, third and fourth conjuncts of the twin step's target, from an evaluated
check**: IxC's twin record at the positional package, each member stored after the step as a
constant that stores it, and a model companion at each member. -/
theorem twinStep_of_check {fuel : Nat} {env : Env .anon} {block : List (ConstantInfo .anon)}
    (h : twinStepCheck fuel env block = true) :
    ∃ env₂, DeclRecTwinRunJ twinPosRulesJ env block env₂ ∧
      (∀ ci ∈ block, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci) ∧
      (∀ ci ∈ block, Ix.Kernel.Model.HasModel env₂ ci.name) := by
  unfold twinStepCheck at h
  split at h
  · rename_i env₂ hrun
    have hall := List.all_eq_true.mp h
    refine ⟨env₂, declRecTwinRunJ_twinPos_of_check hrun, fun ci hci => ?_, fun ci hci => ?_⟩
    · have hc : (_ && _) = true := hall ci hci
      simp only [Bool.and_eq_true] at hc
      have h1 := hc.1
      split at h1
      · rename_i c hfc
        exact ⟨c, hfc, IxVM.Consistency.storedAs_of_check h1⟩
      · cases h1
    · have hc : (_ && _) = true := hall ci hci
      simp only [Bool.and_eq_true] at hc
      have h2 := hc.2
      split at h2
      · rename_i cvm mval hint hfm
        exact ⟨cvm, mval, hint, hfm⟩
      · cases h2
  · cases h

end IxVM.Refinement.Typing.TwinFamily
