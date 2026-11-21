import Aiur.Optimized.Depth.Basic
import Aiur.LayoutComposition
import Aiur.TableChecking
import Mathlib.Tactic.Ring

/-!
# Row-local rule of the depth pass

`compileChip` keeps constraints and memory lookups, so an assignment is valid
for the depth chip exactly when it is valid for the original chip. The provided
message gains the depth word; every original send keeps its position and
enable and gains its callee's depth word; limb range checks follow. Erasing the
depth words recovers the original conclusion and premises.

The static range maps bound every limb, which bounds the gap of each
intra-SCC premise below `2 ^ cfg.bits`.
-/

namespace Aiur.Optimized.Depth

open Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- The message a send contributes when enabled. `Chip.requirements` filters with it. -/
def enabled (a : Var → F) (send : Send F) : Option (Message F) :=
  if send.enable.denote a = 1 then some (send.message a) else none

theorem requirements_eq (chip : Chip F) (a : Var → F) :
    chip.requirements a = chip.sends.filterMap (enabled a) := rfl

/-! ## Certificate facts -/

/-- Everything the soundness proof reads from `certify`. -/
structure Facts (cfg : Config) (source : System F) : Prop where
  nodup : cfg.names.Nodup
  chipName : ∀ chip ∈ source.chips, chip.name ∉ cfg.names
  sendName : ∀ chip ∈ source.chips, ∀ send ∈ chip.sends, send.channel ∉ cfg.names
  mapName : ∀ map ∈ source.maps, map.name ∉ cfg.names
  mapInput : ∀ map ∈ source.maps, map.input ∉ cfg.names
  mapOutput : ∀ map ∈ source.maps, map.output ∉ cfg.names
  mapPlain : ∀ map ∈ source.maps, cfg.recursive map.name = false
  tableName : ∀ table ∈ source.tables, table.name ∉ cfg.names
  formed : ∀ chip ∈ source.chips, chip.wellFormed = true
  length : ∀ chip ∈ source.chips, (cfg.plan chip.name).slots.length = chip.sends.length
  slot : ∀ chip ∈ source.chips, ∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
    slotOK cfg source chip.name pair.1 pair.2 = true

theorem Certified.facts {cfg : Config} {source : System F} (certified : Certified cfg source) :
    Facts cfg source := by
  simp only [Certified, certify, fresh, chipOK, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at certified
  obtain ⟨⟨⟨⟨nodup, chips⟩, maps⟩, tables⟩, each⟩ := certified
  exact {
    nodup
    chipName := fun chip member => (chips chip member).1
    sendName := fun chip member => (chips chip member).2
    mapName := fun map member => (maps map member).1.1.1
    mapInput := fun map member => (maps map member).1.1.2
    mapOutput := fun map member => (maps map member).1.2
    mapPlain := fun map member => (maps map member).2
    tableName := tables
    formed := fun chip member => (each chip member).1.1
    length := fun chip member => (each chip member).1.2
    slot := fun chip member => (each chip member).2 }

/-- The kind of a certified slot matches its callee, and equal rank needs a depth word. -/
theorem slot_spec {cfg : Config} {source : System F} {caller : String} {send : Send F}
    {kind : SlotKind} (ok : slotOK cfg source caller send kind = true) :
    (kind = .plain ↔ cfg.recursive send.channel = false) ∧
    ∀ callee, source.findChip? send.channel = some callee →
      ((kind = .plain ∨ kind = .external) ∧ cfg.rank send.channel < cfg.rank caller) ∨
      ((kind = .exact ∨ kind = .gap) ∧ cfg.recursive caller = true ∧
        cfg.rank send.channel = cfg.rank caller) := by
  unfold slotOK at ok
  cases found : source.findChip? send.channel with
  | none =>
      simp only [found, decide_eq_true_eq] at ok
      exact ⟨by simp [ok.1, ok.2], fun _ member => by cases member⟩
  | some callee =>
      simp only [found] at ok
      refine ⟨?_, fun _ _ => ?_⟩ <;> cases kind <;> simp_all

/-! ## Messages -/

@[simp] theorem extend_enable (send : Send F) (word : Option (ArithExpr F)) :
    (Send.extend send word).enable = send.enable := by
  cases word <;> rfl

@[simp] theorem extend_channel (send : Send F) (word : Option (ArithExpr F)) (a : Var → F) :
    ((Send.extend send word).message a).channel = send.channel := by
  cases word <;> rfl

theorem extend_message (send : Send F) (word : ArithExpr F) (a : Var → F) :
    (Send.extend send (some word)).message a =
      ⟨send.channel, (send.message a).args ++ [⟨.field, [word.denote a]⟩], (send.message a).result⟩ := by
  simp [Send.extend, Send.message, WireValue.map]

theorem depthWord_extend (send : Send F) (word : ArithExpr F) (a : Var → F) :
    depthWord ((Send.extend send (some word)).message a) = word.denote a := by
  simp [extend_message, depthWord]

theorem erase_extend (cfg : Config) (send : Send F) (word : ArithExpr F) (a : Var → F)
    (recursive : cfg.recursive send.channel = true) :
    erase cfg ((Send.extend send (some word)).message a) = send.message a := by
  rw [extend_message]
  simp only [erase, recursive, ↓reduceIte, List.dropLast_concat]
  rfl

theorem erase_plain (cfg : Config) (message : Message F)
    (plain : cfg.recursive message.channel = false) : erase cfg message = message := by
  simp [erase, plain]

/-- One slot, enabled or not, erases to the original slot. -/
theorem enabled_erase (cfg : Config) (depth : ArithExpr F) (a : Var → F) (send : Send F)
    (kind : SlotKind) (column : Nat) (kindOK : kind = .plain ↔ cfg.recursive send.channel = false) :
    (enabled a (Send.extend send (extra cfg.limbs depth kind column))).map (erase cfg) =
      enabled a send := by
  unfold enabled
  rw [extend_enable]
  by_cases on : send.enable.denote a = 1
  · simp only [on, if_true, Option.map]
    congr 1
    cases kind with
    | plain => exact erase_plain cfg _ (kindOK.mp rfl)
    | exact | gap | external =>
        apply erase_extend
        cases recursive : cfg.recursive send.channel
        · exact absurd (kindOK.mpr recursive) (by simp)
        · rfl
  · simp [on]

theorem mainSends_erase (cfg : Config) (depth : ArithExpr F) (a : Var → F) :
    ∀ (column : Nat) (pairs : List (Send F × SlotKind)),
      (∀ pair ∈ pairs, (pair.2 = .plain ↔ cfg.recursive pair.1.channel = false)) →
      ((mainSends cfg.limbs depth column pairs).filterMap (enabled a)).map (erase cfg) =
        (pairs.map Prod.fst).filterMap (enabled a)
  | _, [] => fun _ => rfl
  | column, (send, kind) :: rest => fun kinds => by
      have tail := mainSends_erase cfg depth a (column + kind.width cfg.limbs) rest
        (fun pair member => kinds pair (List.mem_cons_of_mem _ member))
      have head := enabled_erase cfg depth a send kind column (kinds (send, kind) List.mem_cons_self)
      simp only [mainSends, List.map_cons, List.filterMap_cons]
      cases slot : enabled a (Send.extend send (extra cfg.limbs depth kind column)) with
      | none =>
          simp only [slot, Option.map] at head
          simp only [← head, tail]
      | some message =>
          simp only [slot, Option.map] at head
          simp only [← head, List.map_cons, tail]

/-- An enabled premise of the rewritten sends comes from one original slot. A
gap slot's limb checks are premises of the same row. -/
theorem mainSends_mem (limbs : List Nat) (depth : ArithExpr F) (a : Var → F) :
    ∀ (column : Nat) (pairs : List (Send F × SlotKind)) (premise : Message F),
      premise ∈ (mainSends limbs depth column pairs).filterMap (enabled a) →
      ∃ send kind position, (send, kind) ∈ pairs ∧ send.enable.denote a = 1 ∧
        premise = (Send.extend send (extra limbs depth kind position)).message a ∧
        (kind = .gap → ∀ check ∈ (limbChecks limbs position send.enable).filterMap (enabled a),
          check ∈ (rangeSends limbs column pairs).filterMap (enabled a))
  | _, [], _, member => by simp [mainSends] at member
  | column, (send, kind) :: rest, premise, member => by
      simp only [mainSends, List.filterMap_cons] at member
      cases slot : enabled a (Send.extend send (extra limbs depth kind column)) with
      | some message =>
          rw [slot] at member
          rcases List.mem_cons.mp member with rfl | member
          · unfold enabled at slot
            rw [extend_enable] at slot
            by_cases on : send.enable.denote a = 1
            · simp only [on, if_true, Option.some.injEq] at slot
              refine ⟨send, kind, column, List.mem_cons_self, on, slot.symm, ?_⟩
              intro gap check present
              simp only [rangeSends, gap, if_true, List.filterMap_append, List.mem_append]
              exact Or.inl present
            · simp [on] at slot
          · obtain ⟨send', kind', position, pair, on, same, checks⟩ :=
              mainSends_mem limbs depth a _ rest premise member
            refine ⟨send', kind', position, List.mem_cons_of_mem _ pair, on, same, ?_⟩
            intro gap check present
            simp only [rangeSends, List.filterMap_append, List.mem_append]
            exact Or.inr (checks gap check present)
      | none =>
          rw [slot] at member
          obtain ⟨send', kind', position, pair, on, same, checks⟩ :=
            mainSends_mem limbs depth a _ rest premise member
          refine ⟨send', kind', position, List.mem_cons_of_mem _ pair, on, same, ?_⟩
          intro gap check present
          simp only [rangeSends, List.filterMap_append, List.mem_append]
          exact Or.inr (checks gap check present)

@[simp] theorem rangeSend_enable (width column : Nat) (enable : ArithExpr F) :
    (rangeSend width column enable).enable = enable := rfl

theorem rangeSend_message (width column : Nat) (enable : ArithExpr F) (a : Var → F) :
    (rangeSend width column enable).message a = rangeMessage width (a column) := by
  simp [rangeSend, rangeMessage, Send.message, WireValue.map, unitWire, Scalar.Circuit.ArithExpr.denote]

theorem limbChecks_channel (a : Var → F) :
    ∀ (limbs : List Nat) (column : Nat) (enable : ArithExpr F) (check : Message F),
      check ∈ (limbChecks limbs column enable).filterMap (enabled a) →
      ∃ width ∈ limbs, check.channel = rangeName width
  | [], _, _, _, member => by simp [limbChecks] at member
  | width :: widths, column, enable, check, member => by
      simp only [limbChecks, List.filterMap_cons] at member
      cases slot : enabled a (rangeSend width column enable) with
      | none =>
          simp only [slot] at member
          obtain ⟨w, inside, same⟩ := limbChecks_channel a widths (column + 1) enable check member
          exact ⟨w, List.mem_cons_of_mem _ inside, same⟩
      | some message =>
          simp only [slot] at member
          rcases List.mem_cons.mp member with same | member
          · unfold enabled at slot
            split at slot
            · cases slot
              exact ⟨width, List.mem_cons_self, by rw [same]; rfl⟩
            · cases slot
          · obtain ⟨w, inside, same⟩ := limbChecks_channel a widths (column + 1) enable check member
            exact ⟨w, List.mem_cons_of_mem _ inside, same⟩

theorem rangeSends_channel (a : Var → F) (limbs : List Nat) :
    ∀ (column : Nat) (pairs : List (Send F × SlotKind)) (check : Message F),
      check ∈ (rangeSends limbs column pairs).filterMap (enabled a) →
      ∃ width ∈ limbs, check.channel = rangeName width
  | _, [], _, member => by simp [rangeSends] at member
  | column, (send, kind) :: rest, check, member => by
      simp only [rangeSends, List.filterMap_append, List.mem_append] at member
      rcases member with member | member
      · split at member
        · exact limbChecks_channel a limbs column send.enable check member
        · simp at member
      · exact rangeSends_channel a limbs _ rest check member

/-- Range-checked limbs make the gap a natural number below `2 ^ limbs.sum`. -/
theorem gap_value (a : Var → F) (claim : Message F → Prop) :
    ∀ (limbs : List Nat),
      (∀ width ∈ limbs, ∀ x, claim (rangeMessage width x) → ∃ n : Nat, n < 2 ^ width ∧ x = (n : F)) →
      ∀ (column : Nat) (enable : ArithExpr F), enable.denote a = 1 →
      (∀ check ∈ (limbChecks limbs column enable).filterMap (enabled a), claim check) →
      ∃ n : Nat, n < 2 ^ limbs.sum ∧ (gapExpr limbs column).denote a = (n : F)
  | [], _, _, _, _, _ => ⟨0, by simp, by simp [gapExpr, Scalar.Circuit.ArithExpr.denote]⟩
  | width :: widths, ranged, column, enable, on, checked => by
      have first : claim (rangeMessage width (a column)) := by
        apply checked
        simp only [limbChecks, List.filterMap_cons, enabled, rangeSend_enable, on, ↓reduceIte,
          rangeSend_message]
        exact List.mem_cons_self
      obtain ⟨low, lowBound, lowValue⟩ := ranged width List.mem_cons_self _ first
      obtain ⟨high, highBound, highValue⟩ := gap_value a claim widths
        (fun w inside => ranged w (List.mem_cons_of_mem _ inside)) (column + 1) enable on
        (fun check present => checked check (by
          simp only [limbChecks, List.filterMap_cons, enabled, rangeSend_enable, on, ↓reduceIte]
          exact List.mem_cons_of_mem _ present))
      refine ⟨low + 2 ^ width * high, ?_, ?_⟩
      · have : 2 ^ width * (high + 1) ≤ 2 ^ width * 2 ^ widths.sum :=
          Nat.mul_le_mul_left _ highBound
        rw [List.sum_cons, Nat.pow_add]
        calc low + 2 ^ width * high < 2 ^ width + 2 ^ width * high := by omega
          _ = 2 ^ width * (high + 1) := by ring
          _ ≤ 2 ^ width * 2 ^ widths.sum := this
      · simp only [gapExpr, Scalar.Circuit.ArithExpr.denote]
        change a column + _ * (gapExpr widths (column + 1)).denote a = _
        rw [highValue, lowValue]
        push_cast
        ring

/-! ## Conclusions -/

theorem compileChip_receive (limbs : List Nat) (plan : ChipPlan) (chip : Chip F) (row : Row F) :
    (compileChip limbs plan chip).receive row =
      if plan.recursive then
        ⟨chip.name, (chip.receive row).args ++ [⟨.field, [row.assignment chip.numVars]⟩],
          (chip.receive row).result⟩
      else chip.receive row := by
  unfold compileChip Chip.receive
  split <;> simp [WireValue.map]

theorem compileChip_erase (cfg : Config) (chip : Chip F) (row : Row F) :
    erase cfg ((compileChip cfg.limbs (cfg.plan chip.name) chip).receive row) = chip.receive row := by
  rw [compileChip_receive]
  by_cases recursive : (cfg.plan chip.name).recursive = true
  · simp [recursive, erase, Config.recursive, Chip.receive]
  · simp only [recursive, if_false, Bool.false_eq_true]
    exact erase_plain cfg _ (by simpa [Config.recursive, Chip.receive] using recursive)

theorem compileChip_depthWord (limbs : List Nat) (plan : ChipPlan) (chip : Chip F) (row : Row F)
    (recursive : plan.recursive = true) :
    depthWord ((compileChip limbs plan chip).receive row) = row.assignment chip.numVars := by
  rw [compileChip_receive]
  simp [recursive, depthWord]

theorem compileChip_premises (limbs : List Nat) (plan : ChipPlan) (chip : Chip F) (row : Row F) :
    (compileChip limbs plan chip).premises row =
      (mainSends limbs (.var chip.numVars) (plan.base chip) (chip.sends.zip plan.slots)).filterMap
          (enabled row.assignment) ++
        (rangeSends limbs (plan.base chip) (chip.sends.zip plan.slots)).filterMap
          (enabled row.assignment) := by
  simp only [Chip.premises, compileChip, List.filterMap_append]
  rfl

/-! ## The rule lemma -/

/-- Constraints and memory lookups are unchanged. -/
theorem compileChip_valid (limbs : List Nat) (plan : ChipPlan) (chip : Chip F) (rom : WireROM F)
    (a : Var → F) : (compileChip limbs plan chip).ValidAssignment rom a ↔ chip.ValidAssignment rom a :=
  Iff.rfl

theorem compileChip_conclusion (cfg : Config) (chip : Chip F) (a : Var → F) :
    erase cfg ((compileChip cfg.limbs (cfg.plan chip.name) chip).conclusion a) = chip.conclusion a := by
  unfold compileChip Chip.conclusion
  by_cases recursive : (cfg.plan chip.name).recursive = true
  · simp [recursive, erase, Config.recursive, WireValue.map]
  · simp only [recursive, if_false, Bool.false_eq_true]
    exact erase_plain cfg _ (by simpa [Config.recursive] using recursive)

/-- Completeness half: any values in the new columns extend a valid original
assignment to a valid depth assignment with the same erased conclusion and
premises. Honest provers choose `d` and the limbs so that the range checks hold. -/
theorem compileChip_lift (cfg : Config) (chip : Chip F) (formed : chip.wellFormed = true)
    (kinds : ∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
      (pair.2 = .plain ↔ cfg.recursive pair.1.channel = false))
    (length : (cfg.plan chip.name).slots.length = chip.sends.length)
    (rom : WireROM F) (a b : Var → F) (agree : ∀ id < chip.numVars, a id = b id) :
    ((compileChip cfg.limbs (cfg.plan chip.name) chip).ValidAssignment rom b ↔
        chip.ValidAssignment rom a) ∧
      erase cfg ((compileChip cfg.limbs (cfg.plan chip.name) chip).conclusion b) = chip.conclusion a ∧
      ((mainSends cfg.limbs (.var chip.numVars) ((cfg.plan chip.name).base chip)
          (chip.sends.zip (cfg.plan chip.name).slots)).filterMap (enabled b)).map (erase cfg) =
        chip.requirements a := by
  have same := chip.agree (a := a) (b := b)
    (fun id member => agree id (chip.wellFormed_variables formed id member)) rom
  refine ⟨same.1.symm, (compileChip_conclusion cfg chip b).trans same.2.1.symm, ?_⟩
  rw [mainSends_erase cfg _ b _ _ kinds, List.map_fst_zip (by rw [length])]
  exact same.2.2.symm

/-- Soundness half: a depth row is an original row once depth words are
erased; its remaining premises are limb range checks. -/
theorem compileChip_localRule (cfg : Config) (chip : Chip F) (formed : chip.wellFormed = true)
    (kinds : ∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
      (pair.2 = .plain ↔ cfg.recursive pair.1.channel = false))
    (length : (cfg.plan chip.name).slots.length = chip.sends.length)
    {rom : WireROM F} {root : Message F} {premises : List (Message F)}
    (rule : (compileChip cfg.limbs (cfg.plan chip.name) chip).LocalRule rom root premises) :
    ∃ main ranges, premises = main ++ ranges ∧
      chip.LocalRule rom (erase cfg root) (main.map (erase cfg)) ∧
      ∀ check ∈ ranges, ∃ width ∈ cfg.limbs, check.channel = rangeName width := by
  obtain ⟨row, _, valid, rootEq, premisesEq⟩ := rule
  have finite := chip.finiteAssignment formed row.assignment rom
  simp only at finite
  obtain ⟨validIff, conclusion, requirements⟩ :=
    compileChip_lift cfg chip formed kinds length rom row.assignment row.assignment (fun _ _ => rfl)
  refine ⟨_, _, premisesEq.symm.trans (compileChip_premises _ _ _ _), ?_,
    fun check member => rangeSends_channel _ _ _ _ check member⟩
  refine ⟨Row.ofAssignment chip.name chip.numVars row.assignment, rfl,
    ⟨formed, Row.ofAssignment_length _ _ _, finite.1.mp (validIff.mp ⟨valid.2.2.1, valid.2.2.2⟩)⟩, ?_, ?_⟩
  · rw [← finite.2.1, ← conclusion, ← rootEq]
    rfl
  · rw [← finite.2.2, requirements]

end Aiur.Optimized.Depth
