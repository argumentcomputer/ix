import Aiur.Circuit.CheckerSoundness
import Aiur.Circuit.ForestBalance
import Mathlib.Data.List.OfFn

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F] {system : System F} {rom : WireROM F}

private def ForestTrace (system : System F) (rom : WireROM F) (roots : List (Message F)) : Prop :=
  ∃ rows claims, system.inspectRows rom rows = .ok claims ∧
    Balance.Forest (fun c => decide (system.MapClaim c)) roots claims

private theorem ForestTrace.append {left right : List (Message F)}
    (a : ForestTrace system rom left) (b : ForestTrace system rom right) :
    ForestTrace system rom (left ++ right) := by
  obtain ⟨rowsA, claimsA, inspectedA, balancedA⟩ := a
  obtain ⟨rowsB, claimsB, inspectedB, balancedB⟩ := b
  refine ⟨rowsA ++ rowsB, claimsA ++ claimsB, ?_, Balance.forest_append balancedA balancedB⟩
  change rowsA.mapM _ = _ at inspectedA
  change rowsB.mapM _ = _ at inspectedB
  simp [System.inspectRows, List.mapM_append, inspectedA, inspectedB, bind, Except.bind, pure, Except.pure]

/-- Flatten a proof to a checked forest. A static claim may be discharged directly,
even if the supplied tree happened to prove it using a chip with the same name. -/
private theorem Derivation.forestTrace {root : Message F} (tree : Derivation system rom root) :
    ForestTrace system rom [root] := by
  induction tree using Derivation.rec
    (motive_2 := fun roots _ => ForestTrace system rom roots) with
  | node chip row lookup valid children ih =>
      by_cases static : system.MapClaim (chip.receive row)
      · exact ⟨[], [], rfl, Balance.forest_static (by simp [static])⟩
      · obtain ⟨rows, claims, inspected, balanced⟩ := ih
        refine ⟨row :: rows, (chip.receive row, chip.premises row) :: claims, ?_,
          Balance.forest_node (by simp [static]) balanced⟩
        have checked := System.inspectRow_iff.mpr ⟨chip, lookup, valid, rfl⟩
        change rows.mapM _ = _ at inspected
        simp [System.inspectRows, List.mapM_cons, checked, inspected, bind, Except.bind, pure, Except.pure]
  | table member => exact ⟨[], [], rfl, Balance.forest_static (by simp [member])⟩
  | nil => exact ⟨[], [], rfl, Balance.forest_nil _⟩
  | cons _ _ head tail => exact head.append tail

theorem Derivation.check_complete {root : Message F} (tree : Derivation system rom root)
    (context : system.checkContext rom root = .ok ()) :
    ∃ rows, system.check rom root rows = .ok () := by
  obtain ⟨rows, claims, inspected, balanced⟩ := tree.forestTrace
  exact ⟨rows, System.check_iff.mpr ⟨context, claims, inspected, balanced⟩⟩

theorem System.check_derives_iff {root : Message F}
    (context : system.checkContext rom root = .ok ()) :
    (∃ rows, system.check rom root rows = .ok ()) ↔ Derives system rom root := by
  constructor
  · rintro ⟨rows, checked⟩; exact system.check_sound checked
  · rintro ⟨tree⟩; exact tree.check_complete context

/-- Extract the chip rows; static leaves need no row. -/
def RuleInstance.chipRows : List (RuleInstance system rom) → List (Row F)
  | [] => []
  | .node _ row _ _ :: rules => row :: chipRows rules
  | .table _ _ :: rules => chipRows rules

def RuleInstance.chipClaims : List (RuleInstance system rom) → List (RuleClaims (Message F))
  | [] => []
  | rule@(.node _ _ _ _) :: rules => rule.claims :: chipClaims rules
  | .table _ _ :: rules => chipClaims rules

theorem RuleInstance.inspect_chipRows (rules : List (RuleInstance system rom)) :
    system.inspectRows rom (chipRows rules) = .ok (chipClaims rules) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      cases rule with
      | table claim member => exact ih
      | node chip row lookup valid =>
          have checked := System.inspectRow_iff.mpr ⟨chip, lookup, valid, rfl⟩
          change (chipRows rules).mapM _ = _ at ih
          simp [chipRows, chipClaims, RuleInstance.claims, RuleInstance.conclusion, RuleInstance.premises,
            System.inspectRows, List.mapM_cons, checked, ih, bind, Except.bind, pure, Except.pure]

theorem RuleInstance.chipClaims_origin {rules : List (RuleInstance system rom)}
    {claim : RuleClaims (Message F)} (member : claim ∈ chipClaims rules) :
    ∃ rule ∈ rules, rule.claims = claim := by
  induction rules with
  | nil => simp [chipClaims] at member
  | cons rule rules ih =>
      cases rule with
      | table c known =>
          obtain ⟨r, present, same⟩ := ih member
          exact ⟨r, by simp [present], same⟩
      | node chip row lookup valid =>
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, by simp, rfl⟩
          · obtain ⟨r, present, same⟩ := ih member
            exact ⟨r, by simp [present], same⟩

theorem RuleInstance.dynamic_mem_chipClaims {rules : List (RuleInstance system rom)}
    {rule : RuleInstance system rom} (member : rule ∈ rules)
    (dynamic : ¬system.MapClaim rule.conclusion) : rule.claims ∈ chipClaims rules := by
  induction rules with
  | nil => simp at member
  | cons head rules ih =>
      rcases List.mem_cons.mp member with rfl | member
      · cases rule with
        | node chip row lookup valid => simp [chipClaims]
        | table claim known => exact (dynamic known).elim
      · have present := ih member
        cases head <;> simp [chipClaims, present]

theorem System.inspectRows_weigh {rows : List (Row F)} {claims : List (RuleClaims (Message F))}
    (inspected : system.inspectRows rom rows = .ok claims) (demands : List (Message F)) :
    ∃ weighted, system.inspectWeightedRows rom weighted = .ok (Balance.weigh demands claims) := by
  have related := mapM_ok_iff.mp inspected
  clear inspected
  induction related generalizing demands with
  | nil => exact ⟨[], rfl⟩
  | @cons row claim rows claims head _ ih =>
      obtain ⟨weighted, inspected⟩ := ih (demands.filter (fun c => decide (c ≠ claim.1)))
      refine ⟨⟨row, Accumulator.value (Accumulator.requires demands) claim.1⟩ :: weighted, ?_⟩
      apply mapM_ok_iff.mpr
      apply List.Forall₂.cons
      · simp [head, bind, Except.bind, pure, Except.pure]
      · exact mapM_ok_iff.mp inspected

/-- Every closed graph has an exact integer trace, including graphs with cycles.
The constructed provide weights count demands and are nonnegative. -/
theorem MemoDerivation.check_complete {root : Message F} (graph : MemoDerivation system rom root)
    (context : system.checkContext rom root = .ok ()) :
    ∃ rows, system.checkMemo rom root rows = .ok () := by
  let rules := List.ofFn graph.node
  let claims := RuleInstance.chipClaims rules
  let demands := Balance.required (fun c => decide (system.MapClaim c)) root claims
  have covered : ∀ claim ∈ demands, ∃ provider ∈ claims, provider.1 = claim := by
    intro claim member
    obtain ⟨used, dynamic⟩ := List.mem_filter.mp member
    have dynamic : ¬system.MapClaim claim := by simpa using dynamic
    have provided : ∃ i, (graph.node i).conclusion = claim := by
      rcases List.mem_cons.mp used with rfl | used
      · exact ⟨graph.root, graph.root_claim⟩
      · obtain ⟨source, member, premise⟩ := List.mem_flatMap.mp used
        obtain ⟨rule, present, same⟩ := RuleInstance.chipClaims_origin member
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
        have premise : claim ∈ (graph.node i).premises := by simpa [← same, RuleInstance.claims] using premise
        exact graph.premise_mem i premise
    obtain ⟨i, same⟩ := provided
    exact ⟨(graph.node i).claims,
      RuleInstance.dynamic_mem_chipClaims (List.mem_ofFn.mpr ⟨i, rfl⟩) (by simpa [same] using dynamic), same⟩
  obtain ⟨weighted, inspected⟩ := System.inspectRows_weigh (RuleInstance.inspect_chipRows rules) demands
  exact ⟨weighted, System.checkMemo_iff.mpr ⟨context, Balance.weigh demands claims, inspected,
    Balance.weigh_balanced covered⟩⟩

theorem System.checkMemo_derives_iff {root : Message F}
    (context : system.checkContext rom root = .ok ()) :
    (∃ rows, system.checkMemo rom root rows = .ok ()) ↔ MemoDerives system rom root := by
  constructor
  · rintro ⟨rows, checked⟩; exact system.checkMemo_sound checked
  · rintro ⟨graph⟩; exact graph.check_complete context

end Aiur.Circuit
