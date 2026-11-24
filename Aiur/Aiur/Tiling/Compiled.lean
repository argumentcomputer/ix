import Aiur.Tiling.Goldilocks

/-!
# Static facts of the compiled depth system

The composed theorems take two static hypotheses about the depth system
`Depth.system cfg prepared.system`: `Shaped.check` (call shapes, map shapes,
packed memory, channel ids) and `checkContext` (well-formed chips, a
well-formed public root). This file derives them from the compiler's own
certificates:

* `Physical.Prepared` (`compatible`, the deduplication certificate,
  `faithful`, `mapShaped`): every physical chip is a renamed erased chip, so
  its inputs, output, chip calls and memory values are packed
  (`Erasure.pack`), chip calls carry the callee's word counts, and map calls
  and map claims carry the map's declared shape;
* `Depth.Certified`: the depth pass appends one `field` word to the inputs of
  a recursive chip and to every call into one, adds range calls to fresh
  maps, and keeps every column in bounds.

What remains are facts about the public root (its channel is a chip and is
not recursive) and the injectivity and bound of `idOf` on channel names.
-/

namespace Aiur.Tiling.Compiled

open Aiur.Circuit
open Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Depth chips are well formed -/

section DepthFormed

open Depth

omit [Field F] [DecidableEq F] in
theorem send_inBounds_mono {send : Send F} {before after : Nat}
    (increase : before ≤ after) (bound : send.inBounds before = true) :
    send.inBounds after = true := by
  simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at bound ⊢
  exact ⟨⟨fun x hx => lt_of_lt_of_le (bound.1.1 x hx) increase,
    Scalar.Circuit.ArithExpr.inBounds_mono increase bound.1.2⟩,
    fun expr member => Scalar.Circuit.ArithExpr.inBounds_mono increase (bound.2 expr member)⟩

omit [Field F] [DecidableEq F] in
theorem nextColumn_ge (limbs : List Nat) :
    ∀ (column : Nat) (pairs : List (Send F × SlotKind)), column ≤ nextColumn limbs column pairs
  | _, [] => le_refl _
  | column, (_, kind) :: rest =>
      le_trans (Nat.le_add_right column (kind.width limbs)) (nextColumn_ge limbs _ rest)

omit [DecidableEq F] in
theorem gapExpr_inBounds :
    ∀ (limbs : List Nat) (column bound : Nat), column + limbs.length ≤ bound →
      (gapExpr (F := F) limbs column).inBounds bound = true
  | [], _, _, _ => rfl
  | _ :: limbs, column, bound, h => by
      have tail := gapExpr_inBounds limbs (column + 1) bound (by simp at h; omega)
      have here : column < bound := by simp at h; omega
      simp [gapExpr, Scalar.Circuit.ArithExpr.inBounds, tail, here]

omit [DecidableEq F] in
theorem limbChecks_inBounds :
    ∀ (limbs : List Nat) (column bound : Nat) (enable : ArithExpr F),
      column + limbs.length ≤ bound → enable.inBounds bound = true →
      ∀ s ∈ limbChecks limbs column enable, s.inBounds bound = true
  | [], _, _, _, _, _, s, hs => by simp [limbChecks] at hs
  | _ :: limbs, column, bound, enable, h, he, s, hs => by
      simp only [limbChecks, List.mem_cons] at hs
      rcases hs with rfl | hs
      · have here : column < bound := by simp at h; omega
        simp [rangeSend, Send.inBounds, unitWire, he, Scalar.Circuit.ArithExpr.inBounds, here]
      · exact limbChecks_inBounds limbs (column + 1) bound enable (by simp at h; omega) he s hs

omit [DecidableEq F] in
theorem limbChecks_channel :
    ∀ (limbs : List Nat) (column : Nat) (enable : ArithExpr F),
      ∀ s ∈ limbChecks limbs column enable, ∃ w ∈ limbs, s.channel = rangeName w
  | [], _, _, s, hs => by simp [limbChecks] at hs
  | w :: limbs, column, enable, s, hs => by
      simp only [limbChecks, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨w, by simp, rfl⟩
      · obtain ⟨w', hw', e⟩ := limbChecks_channel limbs (column + 1) enable s hs
        exact ⟨w', by simp [hw'], e⟩

/-- A depth slot's word stays in bounds: the caller's depth column for
`exact`/`gap` slots (a recursive caller), the slot's own columns otherwise. -/
theorem extra_inBounds (limbs : List Nat) (numVars column bound : Nat) (kind : SlotKind)
    (depthIn : kind = .exact ∨ kind = .gap → numVars < bound)
    (columns : column + kind.width limbs ≤ bound) :
    ∀ word ∈ extra limbs (.var numVars : ArithExpr F) kind column, word.inBounds bound = true := by
  intro word hw
  cases kind with
  | plain => simp [extra] at hw
  | exact =>
      simp only [extra, Option.mem_def, Option.some.injEq] at hw
      subst hw
      have := depthIn (Or.inl rfl)
      simp [Scalar.Circuit.ArithExpr.inBounds, this]
  | gap =>
      simp only [extra, Option.mem_def, Option.some.injEq] at hw
      subst hw
      simp only [SlotKind.width] at columns
      have := depthIn (Or.inr rfl)
      have gap := gapExpr_inBounds (F := F) limbs column bound columns
      simp [Scalar.Circuit.ArithExpr.inBounds, this, gap]
  | external =>
      simp only [extra, Option.mem_def, Option.some.injEq] at hw
      subst hw
      simp only [SlotKind.width] at columns
      have here : column < bound := by omega
      simp [Scalar.Circuit.ArithExpr.inBounds, here]

theorem extend_inBounds {send : Send F} {bound : Nat} {word : Option (ArithExpr F)}
    (h : send.inBounds bound = true) (hw : ∀ w ∈ word, w.inBounds bound = true) :
    (Send.extend send word).inBounds bound = true := by
  cases word with
  | none => exact h
  | some w =>
      simp only [Send.extend, Send.inBounds, Bool.and_eq_true, List.all_eq_true, List.flatMap_append,
        List.mem_append] at h ⊢
      refine ⟨h.1, ?_⟩
      rintro x (hx | hx)
      · exact h.2 x hx
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hx
        subst hx
        exact hw _ rfl

/-- Every send of the depth chip is in bounds, given the slots' certificate. -/
theorem sends_inBounds (limbs : List Nat) (numVars bound : Nat) :
    ∀ (column : Nat) (pairs : List (Send F × SlotKind)),
      nextColumn limbs column pairs ≤ bound →
      (∀ p ∈ pairs, p.1.inBounds bound = true) →
      (∀ p ∈ pairs, p.2 = .exact ∨ p.2 = .gap → numVars < bound) →
      (∀ s ∈ mainSends limbs (.var numVars : ArithExpr F) column pairs, s.inBounds bound = true) ∧
      (∀ s ∈ rangeSends (F := F) limbs column pairs, s.inBounds bound = true)
  | _, [], _, _, _ => by simp [mainSends, rangeSends]
  | column, (send, kind) :: rest, next, formed, depthIn => by
      have tail := sends_inBounds limbs numVars bound (column + kind.width limbs) rest
        (by simpa [nextColumn] using next) (fun p hp => formed p (by simp [hp]))
        (fun p hp => depthIn p (by simp [hp]))
      have here : column + kind.width limbs ≤ bound :=
        le_trans (nextColumn_ge limbs _ rest) (by simpa [nextColumn] using next)
      have sendIn := formed (send, kind) (by simp)
      constructor
      · intro s hs
        simp only [mainSends, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact extend_inBounds sendIn
            (extra_inBounds limbs numVars column bound kind (depthIn (send, kind) (by simp)) here)
        · exact tail.1 s hs
      · intro s hs
        simp only [rangeSends, List.mem_append] at hs
        rcases hs with hs | hs
        · split at hs
          · subst kind
            simp only [SlotKind.width] at here
            have enable : send.enable.inBounds bound = true := by
              simp only [Send.inBounds, Bool.and_eq_true] at sendIn
              exact sendIn.1.2
            exact limbChecks_inBounds limbs column bound send.enable here enable s hs
          · simp at hs
        · exact tail.2 s hs

theorem compileChip_wellFormed (cfg : Depth.Config) (source : Circuit.System F) (chip : Chip F)
    (ok : chipOK cfg source chip = true) :
    (compileChip cfg.limbs (cfg.plan chip.name) chip).wellFormed = true := by
  simp only [chipOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨formed, slots⟩, slotsOk⟩ := ok
  set plan := cfg.plan chip.name
  set pairs := chip.sends.zip plan.slots
  set bound := nextColumn cfg.limbs (plan.base chip) pairs
  have base : plan.base chip ≤ bound := nextColumn_ge _ _ _
  have grow : chip.numVars ≤ bound := le_trans (by unfold ChipPlan.base; split <;> omega) base
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at formed
  obtain ⟨⟨⟨⟨inputs, output⟩, constraints⟩, sends⟩, memory⟩ := formed
  have depthIn : ∀ p ∈ pairs, p.2 = .exact ∨ p.2 = .gap → chip.numVars < bound := by
    rintro ⟨send, kind⟩ hp kindIs
    have ok := slotsOk (send, kind) hp
    have recursive : plan.recursive = true := by
      unfold slotOK at ok
      rcases kindIs with e | e <;> simp only at e <;> subst e <;> split at ok <;>
        first | exact (of_decide_eq_true ok).1 | simp at ok
    have : plan.base chip = chip.numVars + 1 := by simp [ChipPlan.base, recursive]
    omega
  have sendsIn := sends_inBounds cfg.limbs chip.numVars bound (plan.base chip) pairs le_rfl
    (fun p hp => send_inBounds_mono grow (sends p.1 (List.of_mem_zip hp).1)) depthIn
  simp only [compileChip, Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_append]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x hx
    refine decide_eq_true ?_
    try simp only [List.mem_flatMap] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    split at ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact lt_of_lt_of_le (inputs x (List.mem_flatMap.mpr ⟨a, ha, hxa⟩)) grow
      · have : plan.base chip = chip.numVars + 1 := by simp [ChipPlan.base, *]
        simp only [List.mem_singleton] at ha
        subst ha
        simp only [List.mem_singleton] at hxa
        subst hxa
        exact lt_of_lt_of_le (by omega : chip.numVars < plan.base chip) base
    · exact lt_of_lt_of_le (inputs x (List.mem_flatMap.mpr ⟨a, ha, hxa⟩)) grow
  · exact fun x hx => Scalar.Circuit.ArithExpr.inBounds_mono grow (output x hx)
  · exact fun x hx => Scalar.Circuit.ArithExpr.inBounds_mono grow (constraints x hx)
  · rintro s (hs | hs)
    · exact sendsIn.1 s hs
    · exact sendsIn.2 s hs
  · intro m hm
    have := memory m hm
    simp only [MemoryLookup.inBounds, Bool.and_eq_true, List.all_eq_true] at this ⊢
    exact ⟨⟨Scalar.Circuit.ArithExpr.inBounds_mono grow this.1.1,
      Scalar.Circuit.ArithExpr.inBounds_mono grow this.1.2⟩,
      fun x hx => Scalar.Circuit.ArithExpr.inBounds_mono grow (this.2 x hx)⟩

theorem system_wellFormed {cfg : Depth.Config} {source : Circuit.System F} (certified : Certified cfg source)
    (names : (source.chips.map Chip.name).Nodup) : (Depth.system cfg source).WellFormed := by
  simp only [Certified, certify, Bool.and_eq_true, List.all_eq_true] at certified
  refine ⟨?_, ?_⟩
  · simpa [Depth.system, List.map_map, Function.comp_def, compileChip] using names
  · intro c hc
    simp only [Depth.system, List.mem_map] at hc
    obtain ⟨chip, member, rfl⟩ := hc
    exact compileChip_wellFormed cfg source chip (certified.2 chip member)

end DepthFormed

/-! ## Packed wires -/

section Packed

omit [Field F] [DecidableEq F] in
theorem shape_pack (words : List α) :
    Erasure.shape (Erasure.pack words) = (.tuple (List.replicate words.length .field), words.length) := by
  simp [Erasure.shape, Erasure.pack]

omit [Field F] [DecidableEq F] in
theorem length_flatMap_words (values : List (WireValue α)) :
    ((values.map Erasure.shape).map Prod.snd).sum = (values.flatMap WireValue.words).length := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih]
      rfl

theorem layout_fields (decls : Declarations) (n : Nat) :
    decls.layout (.tuple (List.replicate n .field)) = .ok (.tuple (List.replicate n .field)) := by
  apply Declarations.layout_tuple
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (Declarations.layout_field decls) ih

theorem decodeList_fields : ∀ words : List F,
    Layout.decodeList (List.replicate words.length .field) words = some (words.map Value.field)
  | [] => by simp [Layout.decodeList]
  | w :: words => by
      rw [List.length_cons, List.replicate_succ, Layout.decodeList]
      simp [Layout.width, Layout.decode, decodeList_fields words]

theorem pack_decode (decls : Declarations) (words : List F) :
    (Erasure.pack words).decode decls = some (.tuple (words.map Value.field)) := by
  have typed : Value.hasType decls (.tuple (words.map Value.field) : Value F)
      (.tuple (List.replicate words.length .field)) = true := by
    simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · simp only [Value.type, List.map_map]
      congr 1
      induction words with
      | nil => rfl
      | cons w rest ih => simp [Value.type, ih, List.replicate_succ]
    · simp [Value.wellFormed, List.all_map, Function.comp_def]
  simp [WireValue.decode, Erasure.pack, layout_fields, Except.toOption, decodeList_fields, Layout.decode,
    typed]

theorem pack_pointerFree (decls : Declarations) (n : Nat) :
    Ty.pointerFree decls (.tuple (List.replicate n .field)) = true := by
  simp [Ty.pointerFree, layout_fields, Layout.pointerFree, List.all_map]

end Packed

/-! ## Physical chips -/

section Prepared

omit [Field F] [DecidableEq F] in
theorem findChip_of_mem {sys : Circuit.System F} (names : (sys.chips.map Chip.name).Nodup)
    {c : Chip F} (hc : c ∈ sys.chips) : sys.findChip? c.name = some c := by
  unfold System.findChip?
  cases h : sys.chips.find? (·.name == c.name) with
  | none => exact absurd (List.find?_eq_none.mp h c hc) (by simp)
  | some c' =>
      have mem := List.mem_of_find?_eq_some h
      have name : c'.name = c.name := System.findChip_name (system := sys) h
      exact congrArg some (List.inj_on_of_nodup_map names mem hc name)

variable {artifact : Artifact F} (prepared : Physical.Prepared artifact)

theorem prepared_nodup : (prepared.system.chips.map Chip.name).Nodup :=
  (checkChips_iff.mp prepared.merged.certificate.2.2.2.2.2.2.2.1).1

/-- Every physical chip is a renamed erased chip of the typed artifact. -/
theorem prepared_chip {c : Chip F} (hc : c ∈ prepared.system.chips) :
    ∃ a ∈ artifact.system.chips,
      c = (Erasure.chip artifact.system a).rename (Dedup.rename prepared.merged.representatives) := by
  have h := prepared.faithful c hc
  rw [Erasure.system_findChip] at h
  cases found : artifact.system.findChip? c.name with
  | none => simp [found] at h
  | some a =>
      simp only [found, Option.map_some, Option.some.injEq] at h
      exact ⟨a, List.mem_of_find?_eq_some found, h.symm⟩

theorem prepared_callee {ch : String} {t : Chip F} (found : artifact.system.findChip? ch = some t) :
    prepared.system.findChip? (Dedup.rename prepared.merged.representatives ch) =
      some ((Erasure.chip artifact.system t).rename (Dedup.rename prepared.merged.representatives)) := by
  have h := prepared.merged.certificate.lookup ch
  rw [Erasure.system_findChip, found] at h
  simpa [Physical.Prepared.system] using h

theorem prepared_name {c : Chip F} (hc : c ∈ prepared.system.chips) :
    (artifact.system.findChip? c.name).isSome = true := by
  have h := prepared.merged.certificate.2.2.1 c hc
  rw [Erasure.system_findChip] at h
  simpa using h

theorem prepared_outside {ch : String} (absent : artifact.system.findChip? ch = none) :
    Dedup.rename prepared.merged.representatives ch = ch :=
  prepared.merged.certificate.outside (by rw [Erasure.system_findChip, absent]; rfl)

theorem prepared_mapClaims : prepared.system.mapClaims = artifact.system.mapClaims := by
  have h := prepared.merged.certificate.2.2.2.1
  simp only [Physical.Prepared.system]
  rw [h]
  rfl

theorem prepared_enums : prepared.system.enums = artifact.system.enums :=
  prepared.merged.certificate.2.2.2.2.2.1

include prepared in
theorem prepared_claim_channel {mc : Message F} (hmc : mc ∈ artifact.system.mapClaims) :
    artifact.system.findChip? mc.channel = none := by
  have h := prepared.merged.certificate.2.2.2.2.1 mc hmc
  rw [Erasure.system_findChip] at h
  simpa using h

/-- A call of a physical chip into a physical chip carries the callee's signature. -/
theorem prepared_call {c : Chip F} (hc : c ∈ prepared.system.chips) {s : Send F} (hs : s ∈ c.sends)
    {T : Chip F} (hT : T ∈ prepared.system.chips) (name : T.name = s.channel) :
    (s.args.map Erasure.shape, Erasure.shape s.result) = Erasure.signature T := by
  obtain ⟨a, ha, rfl⟩ := prepared_chip prepared hc
  simp only [Chip.rename, Erasure.chip, List.map_map, List.mem_map, Function.comp_def] at hs
  obtain ⟨s0, hs0, rfl⟩ := hs
  cases found : artifact.system.findChip? s0.channel with
  | none =>
      have dyn : Erasure.dynamic artifact.system s0.channel = false := by simp [Erasure.dynamic, found]
      have same : Erasure.send artifact.system s0 = s0 := by simp [Erasure.send, dyn]
      rw [same, prepared_outside prepared found] at name
      have := prepared_name prepared hT
      rw [name, found] at this
      simp at this
  | some t =>
      have dyn : Erasure.dynamic artifact.system s0.channel = true := by simp [Erasure.dynamic, found]
      have callee := prepared_callee prepared found
      have send : Erasure.send artifact.system s0 =
          { s0 with args := [Erasure.pack (s0.args.flatMap WireValue.words)],
                    result := Erasure.pack s0.result.words } := by simp [Erasure.send, dyn]
      rw [send] at name ⊢
      have self := findChip_of_mem (prepared_nodup prepared) hT
      rw [name, callee, Option.some.injEq] at self
      subst self
      have sig := prepared.compatible.1 a ha s0 (by simpa using hs0) t found
      simp only [Erasure.signature, Prod.mk.injEq] at sig
      have args := congrArg (fun l => (l.map Prod.snd).sum) sig.1
      simp only [length_flatMap_words] at args
      have result := congrArg Prod.snd sig.2
      simp only [Erasure.shape] at result
      simp only [Erasure.signature, Chip.rename, Erasure.chip, List.map_cons, List.map_nil,
        shape_pack, args, Erasure.pack_words]
      rw [result]

/-- Memory values of a physical chip are packed. -/
theorem prepared_memory {c : Chip F} (hc : c ∈ prepared.system.chips) {m : MemoryLookup F}
    (hm : m ∈ c.memory) : m.value.type = .tuple (List.replicate m.value.words.length .field) := by
  obtain ⟨a, _, rfl⟩ := prepared_chip prepared hc
  simp only [Chip.rename, Erasure.chip, List.mem_map] at hm
  obtain ⟨m0, _, rfl⟩ := hm
  simp [Erasure.memory, Erasure.pack]

/-- A call of a physical chip to a channel that is not a chip is a call of the typed artifact. -/
theorem prepared_static_call {c : Chip F} (hc : c ∈ prepared.system.chips) {s : Send F} (hs : s ∈ c.sends)
    (absent : artifact.system.findChip? s.channel = none) :
    ∃ a ∈ artifact.system.chips, s ∈ a.sends := by
  obtain ⟨a, ha, rfl⟩ := prepared_chip prepared hc
  simp only [Chip.rename, Erasure.chip, List.map_map, List.mem_map, Function.comp_def] at hs
  obtain ⟨s0, hs0, rfl⟩ := hs
  cases found : artifact.system.findChip? s0.channel with
  | none =>
      have dyn : Erasure.dynamic artifact.system s0.channel = false := by simp [Erasure.dynamic, found]
      have same : Erasure.send artifact.system s0 = s0 := by simp [Erasure.send, dyn]
      refine ⟨a, ha, ?_⟩
      simp only [same, prepared_outside prepared found]
      exact hs0
  | some t =>
      have dyn : Erasure.dynamic artifact.system s0.channel = true := by simp [Erasure.dynamic, found]
      have callee := prepared_callee prepared found
      have : (Erasure.send artifact.system s0).channel = s0.channel := by
        simp [Erasure.send, dyn]
      simp only [this] at absent
      have mem := List.mem_of_find?_eq_some callee
      have named := System.findChip_name callee
      have := prepared_name prepared mem
      rw [named, absent] at this
      simp at this

end Prepared

/-! ## The depth system -/

section DepthShape

open Depth

omit [DecidableEq F] in
theorem mem_mainSends {limbs : List Nat} {depth : ArithExpr F} :
    ∀ {column : Nat} {pairs : List (Send F × SlotKind)} {s : Send F},
      s ∈ mainSends limbs depth column pairs →
      ∃ p ∈ pairs, ∃ col, s = Send.extend p.1 (extra limbs depth p.2 col)
  | _, [], _, hs => by simp [mainSends] at hs
  | column, (send, kind) :: rest, s, hs => by
      simp only [mainSends, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨(send, kind), by simp, column, rfl⟩
      · obtain ⟨p, hp, col, e⟩ := mem_mainSends hs
        exact ⟨p, by simp [hp], col, e⟩

omit [Field F] [DecidableEq F] in
theorem mem_limbChecks : ∀ {limbs : List Nat} {column : Nat} {enable : ArithExpr F} {s : Send F},
    s ∈ limbChecks limbs column enable →
      ∃ w ∈ limbs, ∃ col, s = rangeSend w col enable
  | [], _, _, _, hs => by simp [limbChecks] at hs
  | w :: limbs, column, enable, s, hs => by
      simp only [limbChecks, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨w, by simp, column, rfl⟩
      · obtain ⟨w', hw', col, e⟩ := mem_limbChecks hs
        exact ⟨w', by simp [hw'], col, e⟩

omit [Field F] [DecidableEq F] in
theorem mem_rangeSends {limbs : List Nat} :
    ∀ {column : Nat} {pairs : List (Send F × SlotKind)} {s : Send F},
      s ∈ rangeSends limbs column pairs → ∃ w ∈ limbs, ∃ col, ∃ enable : ArithExpr F,
        s = rangeSend w col enable
  | _, [], _, hs => by simp [rangeSends] at hs
  | column, (send, kind) :: rest, s, hs => by
      simp only [rangeSends, List.mem_append] at hs
      rcases hs with hs | hs
      · split at hs
        · obtain ⟨w, hw, col, e⟩ := mem_limbChecks hs
          exact ⟨w, hw, col, _, e⟩
        · simp at hs
      · exact mem_rangeSends hs

omit [Field F] [DecidableEq F] in
theorem rangeName_mem {cfg : Depth.Config} {w : Nat} (hw : w ∈ cfg.limbs) : rangeName w ∈ cfg.names := by
  simp only [Config.names, List.mem_flatMap]
  exact ⟨w, List.mem_dedup.mpr hw, by simp [rangeNames]⟩

structure Fresh (cfg : Depth.Config) (source : Circuit.System F) : Prop where
  nodup : cfg.names.Nodup
  chips : ∀ c ∈ source.chips, c.name ∉ cfg.names
  sends : ∀ c ∈ source.chips, ∀ s ∈ c.sends, s.channel ∉ cfg.names
  maps : ∀ m ∈ source.maps, m.name ∉ cfg.names ∧ m.input ∉ cfg.names ∧ m.output ∉ cfg.names
  tables : ∀ t ∈ source.tables, t.name ∉ cfg.names

theorem fresh_of {cfg : Depth.Config} {source : Circuit.System F} (certified : Certified cfg source) :
    Fresh cfg source := by
  simp only [Certified, certify, fresh, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at certified
  obtain ⟨⟨⟨⟨nodup, chips⟩, maps⟩, tables⟩, _⟩ := certified
  exact ⟨nodup, fun c hc => (chips c hc).1, fun c hc => (chips c hc).2,
    fun m hm => ⟨(maps m hm).1.1.1, (maps m hm).1.1.2, (maps m hm).1.2⟩, tables⟩

theorem depth_chip {cfg : Depth.Config} {source : Circuit.System F} {D : Chip F}
    (hD : D ∈ (Depth.system cfg source).chips) :
    ∃ c ∈ source.chips, D = compileChip cfg.limbs (cfg.plan c.name) c := by
  simpa [Depth.system, eq_comm] using hD

omit [Field F] [DecidableEq F] in
theorem rangeNames_ne {cfg : Depth.Config} (nodup : cfg.names.Nodup) {w w' : Nat}
    (hw : w ∈ cfg.limbs.dedup) (hw' : w' ∈ cfg.limbs.dedup) :
    rangeUnits w' ≠ rangeInputs w ∧ rangeInputs w' ≠ rangeUnits w := by
  have parts := List.nodup_flatMap.mp nodup
  by_cases same : w = w'
  · subst same
    have := parts.1 w hw
    exact ⟨fun e => by simp [rangeNames, e] at this, fun e => by simp [rangeNames, e] at this⟩
  · haveI : Std.Symm (Function.onFun List.Disjoint rangeNames) := ⟨fun _ _ h => h.symm⟩
    have disjoint := parts.2.forall hw hw' same
    constructor
    · intro e
      exact disjoint (a := rangeInputs w) (by simp [rangeNames]) (by simp [rangeNames, ← e])
    · intro e
      exact disjoint (a := rangeUnits w) (by simp [rangeNames]) (by simp [rangeNames, ← e])

omit [Field F] [DecidableEq F] in
theorem encodeMapEntry_channel [NatCast F] [Zero F] {decls : Declarations} {name : String}
    {e : MapEntry F} {mc : Message F} (h : encodeMapEntry decls name e = some mc) : mc.channel = name := by
  simp only [encodeMapEntry] at h
  cases ha : List.mapM (fun value => Value.encode decls value.toValue) e.args <;>
    cases hr : Value.encode decls e.result.toValue <;> simp [ha, hr, bind, Option.bind, pure] at h
  rw [← h]

omit [DecidableEq F] in
theorem rangeTables_find_none {cfg : Depth.Config} {n : String} (hn : n ∉ cfg.names) :
    (cfg.limbs.dedup.flatMap (rangeTables (F := F))).find? (·.name == n) = none := by
  apply List.find?_eq_none.mpr
  intro t ht
  simp only [List.mem_flatMap, rangeTables, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at ht
  obtain ⟨w, hw, rfl | rfl⟩ := ht
  · intro e
    apply hn
    rw [← beq_iff_eq.mp e]
    simp only [Config.names, List.mem_flatMap]
    exact ⟨w, hw, by simp [rangeNames, rangeInputTable]⟩
  · intro e
    apply hn
    rw [← beq_iff_eq.mp e]
    simp only [Config.names, List.mem_flatMap]
    exact ⟨w, hw, by simp [rangeNames, rangeUnitTable]⟩

/-- A map claim of the depth system is a claim of the source system, or a
range claim of shape `([field], ())` on one of the pass's fresh names. -/
theorem depth_claim {cfg : Depth.Config} {source : Circuit.System F} (fr : Fresh cfg source)
    {mc : Message F} (h : mc ∈ (Depth.system cfg source).mapClaims) :
    (mc.channel ∉ cfg.names ∧ mc ∈ source.mapClaims) ∨
      (mc.channel ∈ cfg.names ∧ Erasure.messageShape mc = ([(.field, 1)], (.tuple [], 0))) := by
  unfold System.mapClaims at h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨map, hmap, e, he, enc⟩ := h
  have channel := encodeMapEntry_channel enc
  simp only [Depth.system, List.mem_append, List.mem_map] at hmap
  rcases hmap with hmap | ⟨w, hw, rfl⟩
  · have fresh := fr.maps map hmap
    left
    refine ⟨channel ▸ fresh.1, ?_⟩
    unfold System.mapClaims
    simp only [List.mem_flatMap, List.mem_filterMap]
    refine ⟨map, hmap, e, ?_, enc⟩
    have tables : ∀ n ∉ cfg.names,
        (source.tables ++ cfg.limbs.dedup.flatMap (rangeTables (F := F))).find? (·.name == n) =
          source.tables.find? (·.name == n) := by
      intro n hn
      rw [List.find?_append, rangeTables_find_none hn, Option.or_none]
    simpa only [Depth.system, Program.mapEntries, Program.mapRows, Program.findTable?,
      tables _ fresh.2.1, tables _ fresh.2.2] using he
  · right
    refine ⟨channel ▸ rangeName_mem (List.mem_dedup.mp hw), ?_⟩
    have found : ∀ (n : String) (t : Table F), n ∈ rangeNames w →
        (source.tables ++ cfg.limbs.dedup.flatMap (rangeTables (F := F))).find? (·.name == n) = some t →
        t.name = n ∧ ∃ w' ∈ cfg.limbs.dedup, t = rangeInputTable w' ∨ t = rangeUnitTable w' := by
      intro n t hn ht
      have name : t.name = n := by simpa using List.find?_some ht
      have nameIn : n ∈ cfg.names := by
        simp only [Config.names, List.mem_flatMap]; exact ⟨w, hw, hn⟩
      refine ⟨name, ?_⟩
      rcases List.mem_append.mp (List.mem_of_find?_eq_some ht) with ht' | ht'
      · exact absurd (name ▸ nameIn) (fr.tables t ht')
      · simp only [List.mem_flatMap, rangeTables, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at ht'
        exact ht'
    have inputs : ∀ t, (source.tables ++ cfg.limbs.dedup.flatMap (rangeTables (F := F))).find?
        (·.name == rangeInputs w) = some t → ∃ w', t = rangeInputTable w' := by
      intro t ht
      obtain ⟨name, w', hw', rfl | rfl⟩ := found _ t (by simp [rangeNames]) ht
      · exact ⟨w', rfl⟩
      · simp only [rangeUnitTable] at name
        exact absurd name (rangeNames_ne fr.nodup hw hw').1
    have units : ∀ t, (source.tables ++ cfg.limbs.dedup.flatMap (rangeTables (F := F))).find?
        (·.name == rangeUnits w) = some t → ∃ w', t = rangeUnitTable w' := by
      intro t ht
      obtain ⟨name, w', hw', rfl | rfl⟩ := found _ t (by simp [rangeNames]) ht
      · simp only [rangeInputTable] at name
        exact absurd name (rangeNames_ne fr.nodup hw hw').2
      · exact ⟨w', rfl⟩
    simp only [Program.mapEntries, Program.mapRows, Program.findTable?, Depth.system, rangeDecl] at he
    split at he
    · obtain ⟨wi, hwi⟩ := inputs _ (by assumption)
      obtain ⟨wo, hwo⟩ := units _ (by assumption)
      subst hwi hwo
      simp only [List.mem_filterMap] at he
      obtain ⟨⟨a, b⟩, hab, he⟩ := he
      have ha := (List.of_mem_zip hab).1
      have hb := (List.of_mem_zip hab).2
      simp only [rangeInputTable, rangeUnitTable, List.mem_map, List.mem_range] at ha hb
      obtain ⟨n, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp only [Option.some.injEq] at he
      subst he
      have unit := layout_fields (Depth.system cfg source).enums 0
      simp only [List.replicate_zero] at unit
      simp [encodeMapEntry, Value.encode, Constant.toValue, bind, Option.bind, Value.type,
        Declarations.layout_field, unit, Value.mapAddress, Layout.encode, Except.toOption, Value.wellFormed,
        Layout.encodeList] at enc
      subst enc
      simp [Erasure.messageShape, Erasure.shape]
    · simp at he
end DepthShape

section ClaimChannels

open Depth

omit [DecidableEq F] in
/-- A map claim is on the channel of one of the system's maps. -/
theorem claim_channel {sys : Circuit.System F} {mc : Message F} (h : mc ∈ sys.mapClaims) :
    mc.channel ∈ sys.maps.map MapDecl.name := by
  unfold System.mapClaims at h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨map, hmap, _, _, enc⟩ := h
  exact List.mem_map.mpr ⟨map, hmap, (encodeMapEntry_channel enc).symm⟩

/-- A map claim of the depth system is on a channel of the compiled program's
maps or on a range map of one of the depth limbs. -/
theorem depth_claim_channel {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {mc : Message F}
    (h : mc ∈ (Depth.system cfg prepared.system).mapClaims) :
    mc.channel ∈ compiled.inlined.program.maps.map MapDecl.name ∨
      ∃ w ∈ cfg.limbs, mc.channel = rangeName w := by
  have fr := fresh_of certified
  rcases depth_claim fr h with ⟨_, member⟩ | ⟨inside, _⟩
  · left
    have unmerged : compiled.artifact.system.mapClaims = compiled.artifact.unmerged.mapClaims :=
      compiled.artifact.deduplication.2.2.2.1
    rw [prepared_mapClaims, unmerged] at member
    have := claim_channel member
    rwa [(compile_stages compiled.compiled).2.2.2.2.2] at this
  · right
    have channel := claim_channel h
    simp only [Depth.system, List.map_append, List.mem_append, List.map_map, List.mem_map,
      Function.comp_def] at channel
    rcases channel with ⟨map, hmap, e⟩ | ⟨w, hw, e⟩
    · exact absurd (e ▸ inside) (fr.maps map hmap).1
    · exact ⟨w, List.mem_dedup.mp hw, e.symm⟩

/-- `claimsIn` of `Ixa.ids_ofChip` for the depth system: every claim channel is
among `claims` when the compiled program's map names and the range maps of
the depth limbs are. -/
theorem claimsIn_of_maps {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {claims : List String}
    (maps : ∀ m ∈ compiled.inlined.program.maps, m.name ∈ claims)
    (ranges : ∀ w ∈ cfg.limbs, rangeName w ∈ claims) :
    ∀ mc ∈ (Depth.system cfg prepared.system).mapClaims, mc.channel ∈ claims := by
  intro mc h
  rcases depth_claim_channel compiled prepared certified h with named | ⟨w, hw, e⟩
  · obtain ⟨m, hm, e⟩ := List.mem_map.mp named
    exact e ▸ maps m hm
  · exact e ▸ ranges w hw

end ClaimChannels

/-! ## `Shaped` and `checkContext` of the depth system -/

section Static

open Depth

omit [DecidableEq F] in
theorem extend_args (send : Send F) (word : Option (ArithExpr F)) :
    (Send.extend send word).args.map Erasure.shape =
      send.args.map Erasure.shape ++ (if word.isSome then [(.field, 1)] else []) ∧
    (Send.extend send word).result = send.result ∧ (Send.extend send word).channel = send.channel := by
  cases word <;> simp [Send.extend, Erasure.shape]

omit [DecidableEq F] in
theorem compileChip_signature (limbs : List Nat) (plan : ChipPlan) (c : Chip F) :
    Erasure.signature (compileChip limbs plan c) =
      (c.inputs.map Erasure.shape ++ (if plan.recursive then [(.field, 1)] else []),
        Erasure.shape c.output) := by
  unfold compileChip Erasure.signature
  split <;> simp_all [Erasure.shape]

omit [DecidableEq F] in
theorem extra_isSome (limbs : List Nat) (depth : ArithExpr F) (kind : SlotKind) (column : Nat) :
    (extra limbs depth kind column).isSome = decide (kind ≠ .plain) := by
  cases kind <;> rfl

variable {artifact : Artifact F} (prepared : Physical.Prepared artifact) {cfg : Depth.Config}
  (certified : Depth.Certified cfg prepared.system)

include certified in
theorem slot_of_send {c : Chip F} (hc : c ∈ prepared.system.chips) {p : Send F × SlotKind}
    (hp : p ∈ c.sends.zip (cfg.plan c.name).slots) : slotOK cfg prepared.system c.name p.1 p.2 = true := by
  simp only [Certified, certify, Bool.and_eq_true, List.all_eq_true] at certified
  have := certified.2 c hc
  simp only [chipOK, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2 p hp

include certified in
/-- Call shapes of the depth system: every call into a chip carries its signature. -/
theorem depth_calls : ∀ D ∈ (Depth.system cfg prepared.system).chips, ∀ s ∈ D.sends,
    ∀ D' ∈ (Depth.system cfg prepared.system).chips, D'.name = s.channel →
      (s.args.map Erasure.shape, Erasure.shape s.result) = Erasure.signature D' := by
  have fr := fresh_of certified
  intro D hD s hs D' hD' name
  obtain ⟨c, hc, rfl⟩ := depth_chip hD
  obtain ⟨c', hc', rfl⟩ := depth_chip hD'
  simp only [compileChip] at name
  simp only [compileChip, List.mem_append] at hs
  rcases hs with hs | hs
  · obtain ⟨p, hp, col, rfl⟩ := mem_mainSends hs
    obtain ⟨args, result, channel⟩ := extend_args p.1 (extra cfg.limbs (.var c.numVars) p.2 col)
    rw [channel] at name
    have sendIn := (List.of_mem_zip hp).1
    have base := prepared_call prepared hc sendIn hc' name
    have found : prepared.system.findChip? p.1.channel = some c' := by
      rw [← name]; exact findChip_of_mem (prepared_nodup prepared) hc'
    have slot := slot_of_send prepared certified hc hp
    have same : (extra cfg.limbs (.var c.numVars : ArithExpr F) p.2 col).isSome = (cfg.plan c'.name).recursive := by
      rw [extra_isSome]
      unfold slotOK at slot
      rw [found] at slot
      simp only [Config.recursive, name] at slot ⊢
      obtain ⟨sp, k⟩ := p
      cases k <;> simp only at slot ⊢ <;>
        first
        | exact ((of_decide_eq_true slot).1).symm
        | exact ((of_decide_eq_true slot).2.1).symm
    rw [compileChip_signature, args, result, ← same]
    simp only [Erasure.signature, Prod.mk.injEq] at base
    rw [base.1, base.2]
  · obtain ⟨w, hw, _, _, rfl⟩ := mem_rangeSends hs
    exact absurd (name ▸ rangeName_mem hw) (fr.chips c' hc')

theorem depth_memory : ∀ D ∈ (Depth.system cfg prepared.system).chips, ∀ m ∈ D.memory,
    m.value.type = .tuple (List.replicate m.value.words.length .field) := by
  intro D hD m hm
  obtain ⟨c, hc, rfl⟩ := depth_chip hD
  exact prepared_memory prepared hc hm

include certified in
/-- Map shapes of the depth system: every call to a map has the shape of that map's claims. -/
theorem depth_maps : ∀ D ∈ (Depth.system cfg prepared.system).chips, ∀ s ∈ D.sends,
    ∀ mc ∈ (Depth.system cfg prepared.system).mapClaims, mc.channel = s.channel →
      Erasure.messageShape mc = (s.args.map Erasure.shape, Erasure.shape s.result) := by
  have fr := fresh_of certified
  intro D hD s hs mc hmc channel
  obtain ⟨c, hc, rfl⟩ := depth_chip hD
  simp only [compileChip, List.mem_append] at hs
  rcases depth_claim fr hmc with ⟨outside, member⟩ | ⟨inside, shape⟩
  · rcases hs with hs | hs
    · obtain ⟨p, hp, col, rfl⟩ := mem_mainSends hs
      obtain ⟨args, result, sendChannel⟩ := extend_args p.1 (extra cfg.limbs (.var c.numVars) p.2 col)
      rw [sendChannel] at channel
      rw [prepared_mapClaims] at member
      have absent := prepared_claim_channel prepared member
      rw [channel] at absent
      have notChip : prepared.system.findChip? p.1.channel = none := by
        cases found : prepared.system.findChip? p.1.channel with
        | none => rfl
        | some c' =>
            have := prepared_name prepared (List.mem_of_find?_eq_some found)
            rw [System.findChip_name found, absent] at this
            simp at this
      have slot := slot_of_send prepared certified hc hp
      have plain : p.2 = .plain := by
        unfold slotOK at slot
        rw [notChip] at slot
        simp only [decide_eq_true_eq] at slot
        exact slot.1
      have none : (extra cfg.limbs (.var c.numVars : ArithExpr F) p.2 col).isSome = false := by
        rw [extra_isSome, plain]; rfl
      rw [args, result, none]
      simp only [Bool.false_eq_true, ite_false, List.append_nil]
      obtain ⟨a, ha, hsa⟩ := prepared_static_call prepared hc (List.of_mem_zip hp).1 absent
      obtain ⟨map, hmap, mapName, mapShape⟩ := prepared.mapShaped.1 mc member
      rw [mapShape]
      exact (prepared.mapShaped.2 a ha p.1 hsa map hmap (mapName.trans channel)).symm
    · obtain ⟨w, hw, _, _, rfl⟩ := mem_rangeSends hs
      exact absurd (channel ▸ rangeName_mem hw) outside
  · rcases hs with hs | hs
    · obtain ⟨p, hp, col, rfl⟩ := mem_mainSends hs
      obtain ⟨_, _, sendChannel⟩ := extend_args p.1 (extra cfg.limbs (.var c.numVars) p.2 col)
      rw [sendChannel] at channel
      exact absurd (channel ▸ inside) (fr.sends c hc p.1 (List.of_mem_zip hp).1)
    · obtain ⟨w, hw, _, _, rfl⟩ := mem_rangeSends hs
      rw [shape]
      simp [rangeSend, unitWire, Erasure.shape]

/-- The public root of a non-recursive entry chip is the flattened typed claim. -/
theorem root_eq {name : String} {wires : List (WireValue F)} {output : WireValue F} {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message artifact.system ⟨name, wires, output⟩)
    (entryPlain : cfg.recursive name = false) (entryChip : (artifact.system.findChip? name).isSome = true) :
    root = ⟨name, [Erasure.pack (wires.flatMap WireValue.words)], Erasure.pack output.words⟩ := by
  have dyn : Erasure.dynamic artifact.system name = true := entryChip
  have channel : root.channel = name := by
    have := congrArg Message.channel rooted
    unfold Depth.erase at this
    split at this <;> simpa [Erasure.message, dyn, Erasure.flatten] using this
  unfold Depth.erase at rooted
  rw [channel, entryPlain] at rooted
  simpa [Erasure.message, dyn, Erasure.flatten] using rooted

include certified in
/-- `Shaped` over any chips of the depth system, except the two name facts about `idOf`. -/
theorem shaped_of_compiled_on {chips : List (Chip F)}
    (sub : ∀ c ∈ chips, c ∈ (Depth.system cfg prepared.system).chips)
    {name : String} (entry : name ∈ artifact.entries)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed artifact.system ⟨name, wires, output⟩) {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message artifact.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false) (entryChip : (artifact.system.findChip? name).isSome = true)
    (idOf : String → Nat) (bound : Nat)
    (ids : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, idOf x = idOf y → x = y)
    (idBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) chips root, idOf x < bound) :
    Bridge.Shaped (Depth.system cfg prepared.system) chips idOf root bound := by
  have single := sub
  have rootIs := root_eq rooted entryPlain entryChip
  obtain ⟨t, found⟩ := Option.isSome_iff_exists.mp entryChip
  refine ⟨fun c hc s hs c' hc' e => depth_calls prepared certified c (single c hc) s hs c' (single c' hc') e,
    fun c hc s hs mc hmc e => depth_maps prepared certified c (single c hc) s hs mc hmc e,
    ?_, ?_, fun c hc m hm => depth_memory prepared c (single c hc) m hm, ids, idBound⟩
  · intro D hD e
    obtain ⟨c, hc, rfl⟩ := depth_chip (single D hD)
    simp only [compileChip] at e
    rw [rootIs] at e
    simp only at e
    have fixed : Dedup.rename prepared.merged.representatives name = name :=
      prepared.merged.certificate.2.2.2.2.2.2.2.2 name entry
    have callee := prepared_callee prepared found
    rw [fixed, ← e, findChip_of_mem (prepared_nodup prepared) hc, Option.some.injEq] at callee
    subst callee
    have plain : (cfg.plan ((Erasure.chip artifact.system t).rename
        (Dedup.rename prepared.merged.representatives)).name).recursive = false := by
      rw [e]; exact entryPlain
    rw [compileChip_signature, plain, rootIs]
    have sig := signed t found
    simp only [Erasure.messageShape, Erasure.signature, Prod.mk.injEq] at sig
    have args := congrArg (fun l => (l.map Prod.snd).sum) sig.1
    simp only [length_flatMap_words] at args
    have result := congrArg Prod.snd sig.2
    simp only [Erasure.shape] at result
    simp [Erasure.messageShape, Chip.rename, Erasure.chip, shape_pack, args, result]
  · intro mc hmc e
    rcases depth_claim (fresh_of certified) hmc with ⟨_, member⟩ | ⟨inside, _⟩
    · rw [prepared_mapClaims] at member
      have absent := prepared_claim_channel prepared member
      rw [e, rootIs] at absent
      simp [found] at absent
    · exact absurd (e ▸ inside) outside

include certified in
/-- `Shaped`, except the two name facts about `idOf`, from the compiler's certificates. -/
theorem shaped_of_compiled {id : String → Except String Nat} {plan : Grouping.Plan (Depth.system cfg prepared.system) id}
    {name : String} (entry : name ∈ artifact.entries)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed artifact.system ⟨name, wires, output⟩) {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message artifact.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false) (entryChip : (artifact.system.findChip? name).isSome = true)
    (idOf : String → Nat) (bound : Nat)
    (ids : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (idBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound) :
    Bridge.Shaped (Depth.system cfg prepared.system) plan.singles idOf root bound :=
  shaped_of_compiled_on prepared certified (fun c hc => List.mem_of_find?_eq_some (plan.certificate.1 c hc))
    entry signed rooted outside entryPlain entryChip idOf bound ids idBound

include certified in
/-- `checkContext` of the depth system with the empty ROM (the composed theorems
replace the ROM by the trace's), from the compiler's certificates. -/
theorem context_of_compiled {name : String} {wires : List (WireValue F)} {output : WireValue F}
    {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message artifact.system ⟨name, wires, output⟩)
    (entryPlain : cfg.recursive name = false) (entryChip : (artifact.system.findChip? name).isSome = true) :
    (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok () := by
  rw [root_eq rooted entryPlain entryChip]
  refine System.checkContext_iff.mpr ⟨?_, ?_, ?_, system_wellFormed certified (prepared_nodup prepared)⟩
  · refine ⟨?_, ⟨_, pack_decode _ _⟩⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨_, pack_decode _ _⟩
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact pack_pointerFree _ _
  · exact Erasure.rawROM_valid (by intro a ha; simp at ha)

end Static

/-! ## The wide stage without static hypotheses -/

section Wide

omit [Field F] [DecidableEq F] in
theorem Shaped.check_of [Field F] [DecidableEq F] {source : Circuit.System F} {chips : List (Chip F)}
    {idOf : String → Nat} {root : Message F} {bound : Nat}
    (h : Bridge.Shaped source chips idOf root bound) :
    Bridge.Shaped.check source chips idOf root bound = true := by
  simp only [Bridge.Shaped.check, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, h.memory⟩, ?_⟩, h.idBound⟩
  · intro c hc s hs c' hc'
    by_cases e : c'.name = s.channel
    · exact Or.inr (h.calls c hc s hs c' hc' e)
    · exact Or.inl e
  · intro c hc s hs mc hmc
    by_cases e : mc.channel = s.channel
    · exact Or.inr (h.maps c hc s hs mc hmc e)
    · exact Or.inl e
  · intro c hc
    by_cases e : c.name = root.channel
    · exact Or.inr (h.rootChip c hc e)
    · exact Or.inl e
  · intro mc hmc
    by_cases e : mc.channel = root.channel
    · exact Or.inr (h.rootMaps mc hmc e)
    · exact Or.inl e
  · intro x hx y hy
    by_cases e : idOf x = idOf y
    · exact Or.inr (h.ids x hx y hy e)
    · exact Or.inl e

open Bridge

/-- A `for` loop whose body only yields ran its body successfully on every item. -/
theorem forIn_yield_ok {ε α : Type} {f : α → PUnit → Except ε (ForInStep PUnit)} :
    ∀ {items : List α}, forIn items PUnit.unit f = .ok PUnit.unit →
      (∀ x s, f x PUnit.unit = .ok s → s = .yield PUnit.unit) →
      ∀ x ∈ items, ∃ s, f x PUnit.unit = .ok s
  | [], _, _, x, hx => by simp at hx
  | y :: ys, h, yields, x, hx => by
      rw [List.forIn_cons] at h
      cases hy : f y PUnit.unit with
      | error e => simp [hy, bind, Except.bind] at h
      | ok s =>
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨s, hy⟩
          · obtain rfl := yields y s hy
            simp only [hy, bind, Except.bind] at h
            exact forIn_yield_ok h yields x hx

/-- `compile` rejects an entry that names no function. -/
theorem compile_entry_function {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : Optimized.compile program entries config = .ok artifact)
    {name : String} (entry : name ∈ entries) : (program.findFunction? name).isSome = true := by
  unfold Optimized.compile at compiled
  dsimp only at compiled
  split at compiled
  · simp [bind, Except.bind] at compiled
  · simp only [pure_bind] at compiled
    obtain ⟨⟨⟩, _, rest₁⟩ := except_bind_ok.mp compiled
    obtain ⟨⟨⟩, loop, _⟩ := except_bind_ok.mp rest₁
    obtain ⟨_, step⟩ := forIn_yield_ok loop (by
      intro x s h
      split at h
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      · cases e : Except.mapError reprStr (checkEntry program x) <;>
          simp [e, bind, Except.bind, pure, Except.pure] at h
        exact h.symm) name entry
    cases found : program.findFunction? name with
    | some _ => rfl
    | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at step

/-- Every entry of a compiled artifact is a chip of it: its function's chip,
which deduplication keeps under its own name. -/
theorem compile_entry_chip {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : Optimized.compile program entries config = .ok artifact)
    {name : String} (entry : name ∈ entries) : (artifact.system.findChip? name).isSome = true := by
  obtain ⟨_, found⟩ := Option.isSome_iff_exists.mp (compile_entry_function compiled entry)
  obtain ⟨chip, lookup, _⟩ := compile_find_function compiled found
  have image := artifact.deduplication.2.1 chip (List.mem_of_find?_eq_some lookup)
  have fixed := artifact.deduplication.2.2.2.2.2.2.2.2 name
    (by rw [(compile_stages compiled).2.2.1]; exact entry)
  rw [Circuit.System.findChip_name lookup, fixed] at image
  simp [image]

/-- `Shaped.check` and `checkContext` of the depth system, from the compiled
artifact: what remains is that the entry is not recursive, and the injectivity
and bound of `idOf` on the channel names. -/
theorem static_of_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    {name : String} (entry : name ∈ entries)
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (idOf : String → Nat) {bound : Nat}
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound) :
    Bridge.Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true ∧
      (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok () := by
  have entry' : name ∈ compiled.artifact.entries := by
    rw [(compile_stages compiled.compiled).2.2.1]; exact entry
  have entryChip := compile_entry_chip compiled.compiled entry
  exact ⟨Shaped.check_of (shaped_of_compiled prepared certified entry' signed rooted outside entryPlain
      entryChip idOf bound chanIds chanBound),
    context_of_compiled prepared certified rooted entryPlain entryChip⟩

/-- `Periodic.narrow_heap_sound_compact` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem narrow_heap_sound_compact_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded F} (ok : S.check = true)
    {units : List (Chip F × Option (Unroll F))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : F → Nat} {tables : List (Periodic.Compact F)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result :=
  Periodic.narrow_heap_sound_compact compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk mapsIn
    capacity small tags codesBound labels shadowBound lookups ids parts
    characteristic (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 req req2 enablesOk tall tallT rows balanced

/-- `Periodic.mixed_heap_sound` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem mixed_heap_sound_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded F} (ok : S.check = true)
    {units : List (Chip F × Option (Unroll F))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : F → Nat} {tables : List (Periodic.Compact F)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {wideUnits : List (Periodic.WideUnit F)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : Periodic.checkMixed S idOf ν tables wideUnits = true)
    (capacity : Bridge.capacityRowsU units S.system + Periodic.mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system + Periodic.mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + Periodic.mixedPartCount wideUnits < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    {mainW : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : Periodic.WideUnit F), wideUnits[t]? = some u → ∀ r < u.rows,
      Scalar.Circuit.Satisfies (u.circuit idOf S.buses S.width).constraints (u.assign (mainW t) r))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      Periodic.mixedLedger S idOf wideUnits mainW + S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result :=
  Periodic.mixed_heap_sound compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk mapsIn
    wideIn wideOk capacity small tags codesBound labels shadowBound lookups ids parts
    characteristic (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 req req2 enablesOk tall tallT rows rowsW balanced

/-- `WideStage.wide_heap_sound_insts` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem wide_heap_sound_insts_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip F × (Scalar.Circuit.Var → F))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : Bridge.lookupCount insts < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  WideStage.wide_heap_sound_insts compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf chipsIn instsHold capacity widths romCaps small tags
    lookups characteristic (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 enablesOk balanced

/-- `WideStage.wide_heap_sound` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem wide_heap_sound_compiled {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  WideStage.wide_heap_sound compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf chipsIn unrolled capacity widths romCaps small tags lookups
    characteristic (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 enablesOk holds balanced

end Wide

/-! ## The Goldilocks instances without static hypotheses -/

section GoldilocksCompiled

open Aiur.Library.U32.Goldilocks (modulus)

local notation "GF" => ZMod modulus

open Bridge

/-- `Goldilocks.narrow_heap_sound_compact_goldilocks` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem narrow_heap_sound_compact_goldilocks_compiled {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → GF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → GF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result :=
  Goldilocks.narrow_heap_sound_compact_goldilocks compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk mapsIn
    capacity hbound tags codesBound labels shadowBound lookups ids parts
    hbits (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 req req2 enablesOk tall tallT rows balanced

/-- `Goldilocks.mixed_heap_sound_goldilocks` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem mixed_heap_sound_goldilocks_compiled {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {wideUnits : List (Periodic.WideUnit GF)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : Periodic.checkMixed S idOf ν tables wideUnits = true)
    (capacity : Bridge.capacityRowsU units S.system + Periodic.mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system + Periodic.mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + Periodic.mixedPartCount wideUnits < bound)
    (hbits : cfg.bits ≤ 24)
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → GF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → GF}
    {mainW : Nat → Nat → Nat → GF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : Periodic.WideUnit GF), wideUnits[t]? = some u → ∀ r < u.rows,
      Scalar.Circuit.Satisfies (u.circuit idOf S.buses S.width).constraints (u.assign (mainW t) r))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      Periodic.mixedLedger S idOf wideUnits mainW + S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result :=
  Goldilocks.mixed_heap_sound_goldilocks compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk mapsIn
    wideIn wideOk capacity hbound tags codesBound labels shadowBound lookups ids parts
    hbits (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 req req2 enablesOk tall tallT rows rowsW balanced

/-- `Goldilocks.wide_heap_sound_insts_goldilocks` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem wide_heap_sound_insts_goldilocks_compiled {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip GF × (Scalar.Circuit.Var → GF))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : Bridge.lookupCount insts < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  Goldilocks.wide_heap_sound_insts_goldilocks compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf chipsIn instsHold capacity widths romCaps hbound tags
    lookups hbits (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 enablesOk balanced

/-- `Goldilocks.wide_heap_sound_goldilocks` with `shaped` and `context` from the
compiled artifact (`static_of_compiled`). -/
theorem wide_heap_sound_goldilocks_compiled {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  Goldilocks.wide_heap_sound_goldilocks compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf chipsIn unrolled capacity widths romCaps hbound tags lookups
    hbits (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).1
    (static_of_compiled compiled prepared certified plan entry signed rooted outside entryPlain idOf chanIds chanBound).2 enablesOk holds balanced

end GoldilocksCompiled

end Aiur.Tiling.Compiled
