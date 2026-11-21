import Aiur.Optimized.Basic
import Aiur.Circuit.RuleTranslation

deriving instance DecidableEq for Aiur.Circuit.Send
deriving instance DecidableEq for Aiur.Circuit.MemoryLookup
deriving instance DecidableEq for Aiur.Circuit.Chip

namespace Aiur.Circuit

def Chip.rename (rename : String → String) (chip : Chip F) : Chip F :=
  { chip with
    name := rename chip.name
    sends := chip.sends.map fun send => { send with channel := rename send.channel } }

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
@[simp] theorem Chip.rename_wellFormed (rename : String → String) (chip : Chip F) :
    (chip.rename rename).wellFormed = chip.wellFormed := by
  simp [Chip.rename, Chip.wellFormed, List.all_map, Function.comp_def]
  rfl

omit [DecidableEq F] in
@[simp] theorem Chip.rename_validRow (rename : String → String) (chip : Chip F)
    (rom : WireROM F) (row : Row F) :
    (chip.rename rename).ValidRow rom row ↔ chip.ValidRow rom row := by
  unfold Chip.ValidRow
  rw [Chip.rename_wellFormed]
  rfl

omit [DecidableEq F] in
@[simp] theorem Chip.rename_receive (rename : String → String) (chip : Chip F) (row : Row F) :
    (chip.rename rename).receive row = (chip.receive row).rename rename := rfl

@[simp] theorem Chip.rename_premises (rename : String → String) (chip : Chip F) (row : Row F) :
    (chip.rename rename).premises row = (chip.premises row).map (Message.rename rename) := by
  simp only [Chip.rename, Chip.premises, List.filterMap_map, List.map_filterMap, Function.comp_def]
  congr 1
  funext send
  split <;> rfl

omit [DecidableEq F] in
@[simp] theorem Chip.validRow_relabel (chip : Chip F) (rom : WireROM F) (row : Row F) (name : String) :
    chip.ValidRow rom { row with chip := name } ↔ chip.ValidRow rom row := Iff.rfl

omit [DecidableEq F] in
@[simp] theorem Chip.receive_relabel (chip : Chip F) (row : Row F) (name : String) :
    chip.receive { row with chip := name } = chip.receive row := rfl

@[simp] theorem Chip.premises_relabel (chip : Chip F) (row : Row F) (name : String) :
    chip.premises { row with chip := name } = chip.premises row := rfl

omit [Field F] [DecidableEq F] in
theorem System.findChip_name {system : System F} {name : String} {chip : Chip F}
    (found : system.findChip? name = some chip) : chip.name = name := by
  have h := List.find?_some (p := fun c : Chip F => c.name == name) found
  exact beq_iff_eq.mp h

end Aiur.Circuit

namespace Aiur.Optimized.Dedup

open Circuit
variable {F : Type} [Field F] [DecidableEq F]

def rename (representatives : List (String × String)) (name : String) : String :=
  ((representatives.find? (·.1 == name)).map Prod.snd).getD name

/-- A finite, decidable certificate, checked after partition refinement.
No claim about refinement heuristics is trusted by the semantic proof. -/
def Certificate (source target : Circuit.System F) (representatives : List (String × String))
    (entries : List String) : Prop :=
  (∀ pair ∈ representatives, (source.findChip? pair.1).isSome = true ∧
    (source.findChip? pair.2).isSome = true) ∧
  (∀ chip ∈ source.chips, target.findChip? (rename representatives chip.name) =
    some (chip.rename (rename representatives))) ∧
  (∀ chip ∈ target.chips, (source.findChip? chip.name).isSome = true) ∧
  target.mapClaims = source.mapClaims ∧
  (∀ claim ∈ source.mapClaims, source.findChip? claim.channel = none) ∧
  target.enums = source.enums ∧
  checkChips [] source.chips = .ok () ∧ checkChips [] target.chips = .ok () ∧
  (∀ entry ∈ entries, rename representatives entry = entry)

private theorem isEqv_decide_iff [DecidableEq α] (left right : List α) :
    left.isEqv right (fun a b => decide (a = b)) = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [List.isEqv]
  | cons a left ih => cases right <;> simp [List.isEqv, ih]

/-- A full byte table supplies hundreds of thousands of map claims. Use the
tail-recursive comparison for that list, with exactly the same equality test. -/
instance (source target : Circuit.System F) (representatives : List (String × String)) (entries : List String) :
    Decidable (Certificate source target representatives entries) := by
  letI : Decidable (target.mapClaims = source.mapClaims) :=
    decidable_of_iff (target.mapClaims.isEqv source.mapClaims (fun a b => decide (a = b)) = true)
      (isEqv_decide_iff _ _)
  unfold Certificate
  infer_instance

theorem rename_eq_self {pairs : List (String × String)} {name : String}
    (absent : ∀ pair ∈ pairs, pair.1 ≠ name) : rename pairs name = name := by
  have h : pairs.find? (·.1 == name) = none := List.find?_eq_none.mpr (by simpa using absent)
  simp [rename, h]

theorem rename_preimage {pairs : List (String × String)} {name result : String}
    (same : rename pairs name = result) : name ∈ pairs.map Prod.fst ++ [result] := by
  by_cases h : name ∈ pairs.map Prod.fst
  · simp [h]
  · have unchanged : rename pairs name = name := rename_eq_self (by
      intro pair member equal
      exact h (List.mem_map.mpr ⟨pair, member, equal⟩))
    simp [← same, unchanged]

omit [Field F] [DecidableEq F] in
theorem finite_fibers (pairs : List (String × String)) (message : Message F) :
    Finite {claim : Message F // claim.rename (rename pairs) = message} := by
  let candidates := (pairs.map Prod.fst ++ [message.channel]).map fun name =>
    ({ message with channel := name } : Message F)
  have bounded : {claim : Message F | claim.rename (rename pairs) = message} ⊆ {claim | claim ∈ candidates} := by
    intro claim same
    have name := congrArg Message.channel same
    have args := congrArg Message.args same
    have result := congrArg Message.result same
    apply List.mem_map.mpr
    refine ⟨claim.channel, rename_preimage name, ?_⟩
    cases claim
    cases message
    simp_all [Message.rename]
  exact (candidates.finite_toSet.subset bounded).to_subtype

namespace Certificate

variable {source target : Circuit.System F} {pairs : List (String × String)} {entries : List String}

omit [DecidableEq F] in
theorem outside (checked : Certificate source target pairs entries) {name : String}
    (absent : source.findChip? name = none) : rename pairs name = name :=
  rename_eq_self (by
    intro pair member equal
    have present := (checked.1 pair member).1
    simp [equal, absent] at present)

omit [DecidableEq F] in
theorem lookup (checked : Certificate source target pairs entries) (name : String) :
    target.findChip? (rename pairs name) = (source.findChip? name).map (Chip.rename (rename pairs)) := by
  cases found : source.findChip? name with
  | some chip =>
      have shape := checked.2.1 chip (List.mem_of_find?_eq_some found)
      simpa [source.findChip_name found] using shape
  | none =>
      rw [checked.outside found]
      cases selected : target.findChip? name with
      | none => rfl
      | some chip =>
          have present := checked.2.2.1 chip (List.mem_of_find?_eq_some selected)
          simp [target.findChip_name selected, found] at present

omit [DecidableEq F] in
theorem static_fixed (checked : Certificate source target pairs entries) {claim : Message F}
    (member : source.MapClaim claim) : claim.rename (rename pairs) = claim := by
  have unchanged := checked.outside (checked.2.2.2.2.1 claim member)
  cases claim
  simp_all [Message.rename]

omit [DecidableEq F] in
theorem static_iff (checked : Certificate source target pairs entries) (claim : Message F) :
    target.MapClaim (claim.rename (rename pairs)) ↔ source.MapClaim claim := by
  have static := checked.2.2.2.1
  constructor
  · intro member
    have old : source.MapClaim (claim.rename (rename pairs)) := by
      simpa only [System.MapClaim, static] using member
    have absent := checked.2.2.2.2.1 _ old
    have original : source.findChip? claim.channel = none := by
      cases found : source.findChip? claim.channel with
      | none => rfl
      | some chip =>
          have selected := checked.lookup claim.channel
          simp only [found, Option.map_some] at selected
          have present := checked.2.2.1 _ (List.mem_of_find?_eq_some selected)
          simp only [Chip.rename] at present
          rw [System.findChip_name found] at present
          change source.findChip? (rename pairs claim.channel) = none at absent
          simp [absent] at present
    have fixed : claim.rename (rename pairs) = claim := by
      cases claim
      simp_all [Message.rename, checked.outside original]
    simpa only [fixed] using old
  · intro member
    simpa only [System.MapClaim, static, checked.static_fixed member] using member

theorem ruleTranslation (checked : Certificate source target pairs entries) :
    source.RuleTranslation target (rename pairs) where
  forward rom rule := by
    cases rule with
    | node chip row found valid =>
        let newRow : Row F := { row with chip := rename pairs row.chip }
        have selected : target.findChip? newRow.chip = some (chip.rename (rename pairs)) := by
          simp [newRow, checked.lookup, found]
        refine ⟨.node (chip.rename (rename pairs)) newRow selected ?_, ?_, ?_⟩
        · simpa [newRow] using valid
        · simp [RuleInstance.conclusion, newRow]
        · simp [RuleInstance.premises, newRow]
    | table claim member =>
        exact ⟨.table (claim.rename (rename pairs)) ((checked.static_iff claim).mpr member), rfl, rfl⟩
  backward rom rule claim same := by
    cases rule with
    | node chip row found valid =>
        have names : rename pairs claim.channel = chip.name := congrArg Message.channel same
        have selected : target.findChip? (rename pairs claim.channel) = some chip := by
          simpa [names, target.findChip_name found] using found
        rw [checked.lookup] at selected
        cases original : source.findChip? claim.channel with
        | none => simp [original] at selected
        | some old =>
            have shape : old.rename (rename pairs) = chip := by simpa [original] using selected
            subst chip
            let oldRow : Row F := { row with chip := claim.channel }
            refine ⟨.node old oldRow original ?_, ?_, ?_⟩
            · simpa [oldRow] using valid
            · have args := congrArg Message.args same
              have result := congrArg Message.result same
              have name := source.findChip_name original
              change old.receive oldRow = claim
              cases claim with
              | mk channel inputs output =>
                  change old.name = channel at name
                  change inputs = (old.receive oldRow).args at args
                  change output = (old.receive oldRow).result at result
                  simp only [Chip.receive, name, args, result]
            · simp [RuleInstance.premises, oldRow]
    | table message member =>
        have old : source.MapClaim claim := (checked.static_iff claim).mp (by simpa [same, RuleInstance.conclusion] using member)
        exact ⟨.table claim old, rfl, rfl⟩

theorem context (checked : Certificate source target pairs entries) (rom : WireROM F) (root : Message F) :
    target.checkContext rom (root.rename (rename pairs)) = source.checkContext rom root := by
  obtain ⟨_, _, _, _, _, enums, sourceChips, targetChips, _⟩ := checked
  simp only [System.checkContext, Message.rename, enums, sourceChips, targetChips]

theorem derives_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F} :
    Derives source rom root ↔ Derives target rom (root.rename (rename pairs)) :=
  checked.ruleTranslation.derives_iff

theorem memoDerives_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F} :
    MemoDerives source rom root ↔ MemoDerives target rom (root.rename (rename pairs)) :=
  checked.ruleTranslation.memoDerives_iff (finite_fibers pairs)

theorem acyclic_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F} :
    (∃ graph : MemoDerivation source rom root, graph.Acyclic) ↔
      (∃ graph : MemoDerivation target rom (root.rename (rename pairs)), graph.Acyclic) :=
  checked.ruleTranslation.acyclic_iff (finite_fibers pairs)

/-- Deduplication preserves existential accepted traces, including malformed
contexts (which both sides reject). No assumptions about recursion are needed. -/
theorem check_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F} :
    (∃ rows, source.check rom root rows = .ok ()) ↔
      (∃ rows, target.check rom (root.rename (rename pairs)) rows = .ok ()) := by
  constructor
  · rintro ⟨rows, accepted⟩
    have context := (System.check_iff.mp accepted).1
    exact (target.check_derives_iff (by rwa [checked.context])).mpr
      (checked.derives_iff.mp (source.check_sound accepted))
  · rintro ⟨rows, accepted⟩
    have context := (System.check_iff.mp accepted).1
    rw [checked.context] at context
    exact (source.check_derives_iff context).mpr
      (checked.derives_iff.mpr (target.check_sound accepted))

theorem checkMemo_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F} :
    (∃ rows, source.checkMemo rom root rows = .ok ()) ↔
      (∃ rows, target.checkMemo rom (root.rename (rename pairs)) rows = .ok ()) := by
  constructor
  · rintro ⟨rows, accepted⟩
    have context := (System.checkMemo_iff.mp accepted).1
    exact (target.checkMemo_derives_iff (by rwa [checked.context])).mpr
      (checked.memoDerives_iff.mp (source.checkMemo_sound accepted))
  · rintro ⟨rows, accepted⟩
    have context := (System.checkMemo_iff.mp accepted).1
    rw [checked.context] at context
    exact (source.checkMemo_derives_iff context).mpr
      (checked.memoDerives_iff.mpr (target.checkMemo_sound accepted))

omit [DecidableEq F] in
theorem entry_fixed (checked : Certificate source target pairs entries) {root : Message F}
    (entry : root.channel ∈ entries) : root.rename (rename pairs) = root := by
  have fixed := checked.2.2.2.2.2.2.2.2 root.channel entry
  cases root
  simp_all [Message.rename]

theorem check_entry_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F}
    (entry : root.channel ∈ entries) :
    (∃ rows, source.check rom root rows = .ok ()) ↔ (∃ rows, target.check rom root rows = .ok ()) := by
  simpa only [checked.entry_fixed entry] using checked.check_iff (rom := rom) (root := root)

theorem checkMemo_entry_iff (checked : Certificate source target pairs entries) {rom : WireROM F} {root : Message F}
    (entry : root.channel ∈ entries) :
    (∃ rows, source.checkMemo rom root rows = .ok ()) ↔ (∃ rows, target.checkMemo rom root rows = .ok ()) := by
  simpa only [checked.entry_fixed entry] using checked.checkMemo_iff (rom := rom) (root := root)

end Certificate
end Aiur.Optimized.Dedup
