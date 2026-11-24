import Aiur.Optimized.Grouping.Payload

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

deriving instance DecidableEq for Lookup
deriving instance DecidableEq for Member

def Member.project (m : Member F) (v : Nat) : Polynomial F := .var (m.columns[v]?.getD 0)

def Implied (constraints : List (Polynomial F)) (p : Polynomial F) : Prop :=
  p.Identical (.const 0) ∨ ∃ q ∈ constraints, p.Identical q

instance (constraints : List (Polynomial F)) (p : Polynomial F) : Decidable (Implied constraints p) := by
  unfold Implied
  infer_instance

theorem Implied.sound {cs : List (Polynomial F)} {p : Polynomial F} (h : Implied cs p)
    (a : Nat → F) (valid : Satisfies cs a) : p.denote a = 0 := by
  rcases h with h | ⟨q, hq, same⟩
  · exact h.denote a
  · exact (same.denote a).trans (valid q hq)

/-- A cheap structural filter; coefficients are deliberately ignored so this
does not require a hashing interface on the field. Collisions still undergo
the full polynomial comparison and have no bearing on correctness. -/
def equationKey : Polynomial F → UInt64
  | .const _ => 1
  | .var v => v.toUInt64 * 1099511628211 + 3
  | .add a b => ((equationKey a * 1099511628211) ^^^ equationKey b) + 5
  | .sub a b => ((equationKey a * 1099511628211) ^^^ equationKey b) + 7
  | .mul a b => ((equationKey a * 1099511628211) ^^^ equationKey b) + 11

/-- Normalize and fingerprint source equations once per member. The key only
filters comparisons; the proposition remains full polynomial equality. -/
def allImpliedDecidable (cs ps : List (Polynomial F)) (replacement : Nat → Polynomial F) :
    Decidable (∀ p ∈ ps, Implied cs (p.subst replacement)) := by
  let normalized := cs.map fun q => (equationKey q.normalForm, q.normalForm)
  let wanted := ps.map fun p =>
    let n := (p.subst replacement).normalForm
    (equationKey n, n)
  apply decidable_of_iff (∀ p ∈ wanted,
    p.2 = Polynomial.normalForm (.const (0 : F)) ∨
      ∃ q ∈ normalized, p.1 = q.1 ∧ p.2 = q.2)
  simp only [wanted, List.forall_mem_map]
  simp [normalized, Implied, Polynomial.Identical, eq_comm]
  constructor
  · intro h p hp
    rcases h p hp with h | ⟨q, hq, _, same⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, hq, same⟩
  · intro h p hp
    rcases h p hp with h | ⟨q, hq, same⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, hq, congrArg equationKey same, same⟩

/-- Whether any physical slot for member `m` compacts more than one logical lookup. -/
def Member.hasCompacted (m : Member F) : Bool :=
  (List.range m.numLookups).any fun i => (m.bucket (m.slotIndex i)).length > 1

/-- Check one intra-chip compacted slot (`(m.bucket s).length > 1`) for logical
lookup `idx` on payload positions `2 .. minLen - 1`. -/
def Member.CompactedSlotCheck (ctx : ExclCtx F) (g : Layout F) (m : Member F)
    (left right : Nat → Polynomial F) (idx : Nat) (minLen : Nat) : Prop :=
  let s := m.slotIndex idx
  let B := m.bucket s
  let slot := g.slot s
  ((rename m.columns (m.rawPayloadAt idx).1).subst left).Identical ((m.rawPayloadAt idx).1.subst right) ∧
  (∀ k ∈ B, ctx.isBool (m.rawPayloadAt k).1 = true) ∧
  ctx.allPairwiseExcl (B.map fun k => (m.rawPayloadAt k).1) = true ∧
  minLen ≤ slot.args.length ∧
  ∀ w ∈ List.range minLen, 2 ≤ w →
    ((word slot.args w).subst left).Identical
      ((sum (B.map fun k => ctx.gatedWord (m.rawPayloadAt k).1 (word (m.rawPayloadAt k).2 w))).subst right)

instance (ctx : ExclCtx F) (g : Layout F) (m : Member F)
    (left right : Nat → Polynomial F) (idx : Nat) (minLen : Nat) :
    Decidable (m.CompactedSlotCheck ctx g left right idx minLen) := by
  unfold Member.CompactedSlotCheck
  infer_instance

/-- Decidable payload check supporting both uncompacted (exact `Identical`) and
`C2`-compacted (mutually-exclusive `gatedWord` superposition) slots. -/
def Member.PayloadCheckWith (ctx : ExclCtx F) (g : Layout F) (m : Member F)
    (left right : Nat → Polynomial F) : Prop :=
  let source := ofChip m.origin
  mapMessage Polynomial.simplify (mapMessage (Polynomial.subst left) (decodeMessage source.root g.receive)) =
    mapMessage Polynomial.simplify (mapMessage (Polynomial.subst right) source.root) ∧
  (∀ entry ∈ source.calls.zipIdx,
    let ((origEnable, call), i) := entry
    let s := m.slotIndex i
    let slot := g.slot s
    if (m.bucket s).length ≤ 1 then
      (slot.enable.subst left).Identical (origEnable.subst right) ∧
      mapMessage Polynomial.simplify (mapMessage (Polynomial.subst left) (decodeMessage call slot.args)) =
        mapMessage Polynomial.simplify (mapMessage (Polynomial.subst right) call)
    else
      m.CompactedSlotCheck ctx g left right i
        (2 + (call.args.flatMap WireValue.words).length + call.result.words.length)) ∧
  (∀ entry ∈ source.cells.zipIdx,
    let ((origEnable, addr, value), i) := entry
    let idx := source.calls.length + i
    let s := m.slotIndex idx
    let slot := g.slot s
    if (m.bucket s).length ≤ 1 then
      (slot.enable.subst left).Identical (origEnable.subst right) ∧
      ((word slot.args 2).subst left).Identical (addr.subst right) ∧
      (WireValue.mk value.type ((slot.args.drop 3).take value.words.length)).map
          (Polynomial.simplify ∘ Polynomial.subst left) =
        value.map (Polynomial.simplify ∘ Polynomial.subst right)
    else
      m.CompactedSlotCheck ctx g left right idx (3 + value.words.length))

instance (ctx : ExclCtx F) (g : Layout F) (m : Member F)
    (left right : Nat → Polynomial F) :
    Decidable (m.PayloadCheckWith ctx g left right) := by
  unfold Member.PayloadCheckWith
  infer_instance

def Member.PayloadCheck (g : Layout F) (m : Member F) (left right : Nat → Polynomial F) : Prop :=
  if m.hasCompacted then
    m.PayloadCheckWith (ExclCtx.ofConstraints m.origin.constraints) g left right
  else
    ((g.view m).subst left).Identical ((ofChip m.origin).subst right)

instance (g : Layout F) (m : Member F) (left right : Nat → Polynomial F) :
    Decidable (m.PayloadCheck g left right) := by
  unfold Member.PayloadCheck
  split <;> infer_instance

private theorem mapMessage_denote_of_simplify {m₁ m₂ : Message (Polynomial F)}
    {left right : Nat → Polynomial F}
    (h : mapMessage Polynomial.simplify (mapMessage (Polynomial.subst left) m₁) =
         mapMessage Polynomial.simplify (mapMessage (Polynomial.subst right) m₂)) (a : Nat → F) :
    mapMessage (fun p => p.denote (fun v => (left v).denote a)) m₁ =
      mapMessage (fun p => p.denote (fun v => (right v).denote a)) m₂ := by
  have hd := congrArg (mapMessage (fun p => p.denote a)) h
  simpa [mapMessage_map, Function.comp_def, Polynomial.denote_simplify, Polynomial.denote_subst] using hd

private theorem wireValue_denote_of_simplify {v₁ v₂ : WireValue (Polynomial F)}
    {left right : Nat → Polynomial F}
    (h : v₁.map (Polynomial.simplify ∘ Polynomial.subst left) =
         v₂.map (Polynomial.simplify ∘ Polynomial.subst right)) (a : Nat → F) :
    v₁.map (fun p => p.denote (fun v => (left v).denote a)) =
      v₂.map (fun p => p.denote (fun v => (right v).denote a)) := by
  have hd := congrArg (WireValue.map (fun p => p.denote a)) h
  simpa [WireValue.map_map, Function.comp_def, Polynomial.denote_simplify, Polynomial.denote_subst] using hd

private theorem compactedSlot_eval {ctx : ExclCtx F} {g : Layout F} {m : Member F}
    {left right : Nat → Polynomial F} {idx minLen : Nat}
    (hctx : ctx.Valid m.origin.constraints)
    (hidx : idx < m.numLookups)
    (hcheck : m.CompactedSlotCheck ctx g left right idx minLen)
    {a : Nat → F} (origCons : Satisfies m.origin.constraints (fun v => (right v).denote a)) :
    let a' := fun v => (left v).denote a
    let b := fun v => (right v).denote a
    (rename m.columns (m.rawPayloadAt idx).1).denote a' = (m.rawPayloadAt idx).1.denote b ∧
    ((m.rawPayloadAt idx).1.denote b = 1 →
      ∀ w, 2 ≤ w → w < minLen →
        (word (g.slot (m.slotIndex idx)).args w).denote a' = (word (m.rawPayloadAt idx).2 w).denote b) := by
  obtain ⟨hen, hbool, hexcl, _, hwords⟩ := hcheck
  set a' := fun v => (left v).denote a
  set b := fun v => (right v).denote a
  have henEq : (rename m.columns (m.rawPayloadAt idx).1).denote a' = (m.rawPayloadAt idx).1.denote b := by
    simpa [a', b, Polynomial.denote_subst] using hen.denote a
  refine ⟨henEq, fun h1 w hw2 hwlt => ?_⟩
  have hmem : idx ∈ m.bucket (m.slotIndex idx) := by
    simp [Member.bucket, bucketOf, Member.slotIndex, List.mem_filter, List.mem_range, hidx]
  have hwId := (hwords w (List.mem_range.mpr hwlt) hw2).denote a
  simp only [Polynomial.denote_subst] at hwId
  rcases ctx.allPairwiseExcl_cases hctx hbool hexcl origCons with ⟨hall0, _, _⟩ | ⟨k0, hk0mem, hk01, hrest0, _, hgate1⟩
  · have := hall0 idx hmem
    rw [h1] at this
    exact absurd this one_ne_zero
  · have hk0eq : k0 = idx := by
      by_contra hne
      have := hrest0 idx hmem (Ne.symm hne)
      rw [h1] at this
      exact one_ne_zero this
    subst hk0eq
    have hg := hgate1 (fun k => word (m.rawPayloadAt k).2 w)
    exact hwId.trans hg

private theorem mem_zipIdx_of_lt {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi, i) ∈ xs.zipIdx := by
  have hlen : i < xs.zipIdx.length := by simpa using hi
  have hget : xs.zipIdx[i]'hlen = (xs[i]'hi, i) := by simp
  rw [← hget]
  exact List.getElem_mem hlen

theorem Member.PayloadCheck.sound {g : Layout F} {m : Member F}
    {left right : Nat → Polynomial F}
    (h : m.PayloadCheck g left right) (a : Nat → F)
    (origCons : Satisfies m.origin.constraints (fun v => (right v).denote a)) :
    ((g.view m).denote (fun v => (left v).denote a)).ActiveEquiv
      ((ofChip m.origin).denote (fun v => (right v).denote a)) := by
  unfold Member.PayloadCheck at h
  split at h
  · set ctx := ExclCtx.ofConstraints m.origin.constraints
    have hctx : ctx.Valid m.origin.constraints := ExclCtx.ofConstraints_valid _
    set a' := fun v => (left v).denote a
    set b := fun v => (right v).denote a
    obtain ⟨hroot, hcalls, hcells⟩ := h
    refine ⟨mapMessage_denote_of_simplify hroot a, ?_, ?_⟩
    · apply List.forall₂_iff_get.mpr
      refine ⟨by simp [Layout.view, Payload.denote, Payload.map, ofChip], ?_⟩
      intro i hi1 hi2
      have hi : i < m.origin.sends.length := by
        simpa [Payload.denote, Payload.map, ofChip] using hi2
      have hmem : (((ofChip m.origin).calls[i]'(by simpa [ofChip] using hi)), i) ∈
          (ofChip m.origin).calls.zipIdx :=
        mem_zipIdx_of_lt (ofChip m.origin).calls (by simpa [ofChip] using hi)
      have hci := hcalls _ hmem
      set sObj := m.origin.sends[i]'hi
      set call : Message (Polynomial F) := ⟨sObj.channel, sObj.args, sObj.result.map .var⟩
      set s := m.slotIndex i
      set slot := g.slot s
      simp only [ofChip, List.getElem_map] at hci
      simp only [Layout.view, Payload.denote, Payload.map, ofChip, List.get_eq_getElem,
        List.getElem_map, List.getElem_zipIdx, zero_add]
      change (if (m.bucket s).length ≤ 1 then slot.enable else rename m.columns sObj.enable).denote a' =
          sObj.enable.denote b ∧
        ((if (m.bucket s).length ≤ 1 then slot.enable else rename m.columns sObj.enable).denote a' = 1 →
          mapMessage (fun p => p.denote a') (decodeMessage call slot.args) =
            mapMessage (fun p => p.denote b) call)
      by_cases hle : (m.bucket s).length ≤ 1
      · have hci' : (Polynomial.subst left slot.enable).Identical (Polynomial.subst right sObj.enable) ∧
            mapMessage Polynomial.simplify (mapMessage (Polynomial.subst left) (decodeMessage call slot.args)) =
              mapMessage Polynomial.simplify (mapMessage (Polynomial.subst right) call) := by
          simpa only [s, slot, sObj, call, hle, ↓reduceIte] using hci
        simp only [hle, ↓reduceIte]
        refine ⟨?_, fun _ => mapMessage_denote_of_simplify hci'.2 a⟩
        simpa [a', b, Polynomial.denote_subst] using hci'.1.denote a
      · have hci' : m.CompactedSlotCheck ctx g left right i
            (2 + (call.args.flatMap WireValue.words).length + call.result.words.length) := by
          simpa only [s, slot, sObj, call, hle, ↓reduceIte] using hci
        simp only [hle, ↓reduceIte]
        have hidx : i < m.numLookups := Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
        have hraw : m.rawPayloadAt i =
            (sObj.enable, [.const 0, .const 0] ++ sObj.args.flatMap WireValue.words ++ sObj.result.words.map .var) := by
          simp [Member.rawPayloadAt, hi, sObj]
        obtain ⟨henEq, hwordsEq⟩ := compactedSlot_eval hctx hidx hci' origCons
        rw [hraw] at henEq hwordsEq
        dsimp only at henEq hwordsEq
        refine ⟨henEq, fun hen1 => ?_⟩
        rw [henEq] at hen1
        rw [mapMessage_decodeMessage]
        have hminLen : 2 + (call.args.flatMap WireValue.words).length + call.result.words.length ≤ slot.args.length :=
          hci'.2.2.2.1
        refine decodeMessage_of_prefix call (mapMessage (fun p => p.denote b) call) rfl
          (by simp [mapMessage, List.map_map, Function.comp_def, Erasure.shape, WireValue.map])
          (by simp [mapMessage, List.flatMap_map, WireValue.map, List.length_flatMap])
          rfl
          (by simp [mapMessage, WireValue.map])
          (slot.args.map fun p => p.denote a')
          (by
            simp only [List.length_map, List.length_append, mapMessage, List.flatMap_map,
              WireValue.map, List.length_flatMap, List.map_map]
            simpa [call, Nat.add_assoc] using hminLen)
          (fun j hj => ?_)
        have hwlt : 2 + j < 2 + (call.args.flatMap WireValue.words).length + call.result.words.length := by
          simp only [List.length_append, mapMessage, List.flatMap_map, WireValue.map,
            List.length_flatMap, List.map_map, List.length_map] at hj ⊢
          omega
        have hweq : (word slot.args (2 + j)).denote a' =
            (word ([.const (0 : F), .const 0] ++ sObj.args.flatMap WireValue.words ++
              sObj.result.words.map .var) (2 + j)).denote b :=
          hwordsEq hen1 (2 + j) (by omega) hwlt
        have hslotLt : 2 + j < slot.args.length := Nat.lt_of_lt_of_le hwlt hminLen
        have hlhs : (word slot.args (2 + j)).denote a' = (slot.args[2 + j]'hslotLt).denote a' := by
          simp [word, hslotLt]
        have hpay : ((call.args.flatMap WireValue.words ++ call.result.words).map fun p => p.denote b) =
            ((mapMessage (fun p => p.denote b) call).args.flatMap WireValue.words ++
              (mapMessage (fun p => p.denote b) call).result.words) := by
          simp [mapMessage, List.map_append, List.flatMap_map, List.map_flatMap, WireValue.map]
        have hrawLt : 2 + j < ([Polynomial.const (0 : F), Polynomial.const 0] ++
            sObj.args.flatMap WireValue.words ++ sObj.result.words.map Polynomial.var).length := by
          simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
          simpa [call, Nat.add_assoc] using hwlt
        have hrhs : (word ([.const (0 : F), .const 0] ++ sObj.args.flatMap WireValue.words ++
            sObj.result.words.map .var) (2 + j)).denote b =
            ((mapMessage (fun p => p.denote b) call).args.flatMap WireValue.words ++
              (mapMessage (fun p => p.denote b) call).result.words)[j]'hj := by
          simp only [word, List.getElem?_eq_getElem hrawLt, Option.getD_some]
          have hget2 : (([Polynomial.const (0 : F), Polynomial.const 0] ++
              (sObj.args.flatMap WireValue.words ++ sObj.result.words.map Polynomial.var)) :
              List (Polynomial F))[2 + j]'(by rw [← List.append_assoc]; exact hrawLt) =
              (call.args.flatMap WireValue.words ++ call.result.words)[j]'(by
                simp only [List.length_append, List.length_map, call] at hwlt ⊢; omega) := by
            rw [List.getElem_append_right (by simp)]
            simp [call]
          have hget2' : ([.const (0 : F), .const 0] ++ sObj.args.flatMap WireValue.words ++
              sObj.result.words.map .var)[2 + j]'hrawLt =
              (call.args.flatMap WireValue.words ++ call.result.words)[j]'(by
                simp only [List.length_append, List.length_map, call] at hwlt ⊢; omega) := by
            simpa [List.append_assoc] using hget2
          rw [hget2']
          have hmapGet := List.getElem_map (f := fun p : Polynomial F => p.denote b)
            (l := call.args.flatMap WireValue.words ++ call.result.words) (i := j)
            (h := by simp only [List.length_append, List.length_map, call] at hwlt ⊢; omega)
          rw [← hmapGet]
          congr 1
        simp only [List.getElem_map]
        rw [← hlhs, hweq, hrhs]
    · apply List.forall₂_iff_get.mpr
      refine ⟨by simp [Layout.view, Payload.denote, Payload.map, ofChip], ?_⟩
      intro i hi1 hi2
      have hi : i < m.origin.memory.length := by
        simpa [Payload.denote, Payload.map, ofChip] using hi2
      have hmem : (((ofChip m.origin).cells[i]'(by simpa [ofChip] using hi)), i) ∈
          (ofChip m.origin).cells.zipIdx :=
        mem_zipIdx_of_lt (ofChip m.origin).cells (by simpa [ofChip] using hi)
      have hci := hcells _ hmem
      set memObj := m.origin.memory[i]'hi
      set idx := m.origin.sends.length + i
      set s := m.slotIndex idx
      set slot := g.slot s
      simp only [ofChip, List.getElem_map, List.length_map] at hci
      simp only [Layout.view, Payload.denote, Payload.map, ofChip, List.get_eq_getElem,
        List.getElem_map, List.getElem_zipIdx, zero_add, List.length_map]
      change (if (m.bucket s).length ≤ 1 then slot.enable else rename m.columns memObj.enable).denote a' =
          memObj.enable.denote b ∧
        ((if (m.bucket s).length ≤ 1 then slot.enable else rename m.columns memObj.enable).denote a' = 1 →
          (word slot.args 2).denote a' = memObj.address.denote b ∧
          WireValue.map (fun p => p.denote a') ⟨memObj.value.type, (slot.args.drop 3).take memObj.value.words.length⟩ =
            WireValue.map (fun p => p.denote b) memObj.value)
      by_cases hle : (m.bucket s).length ≤ 1
      · have hci' : (Polynomial.subst left slot.enable).Identical (Polynomial.subst right memObj.enable) ∧
            (Polynomial.subst left (word slot.args 2)).Identical (Polynomial.subst right memObj.address) ∧
            (WireValue.mk memObj.value.type ((slot.args.drop 3).take memObj.value.words.length)).map
                (Polynomial.simplify ∘ Polynomial.subst left) =
              memObj.value.map (Polynomial.simplify ∘ Polynomial.subst right) := by
          simpa only [idx, s, slot, memObj, hle, ↓reduceIte] using hci
        simp only [hle, ↓reduceIte]
        refine ⟨?_, fun _ => ⟨?_, wireValue_denote_of_simplify hci'.2.2 a⟩⟩
        · simpa [a', b, Polynomial.denote_subst] using hci'.1.denote a
        · simpa [a', b, Polynomial.denote_subst] using hci'.2.1.denote a
      · have hci' : m.CompactedSlotCheck ctx g left right idx (3 + memObj.value.words.length) := by
          simpa only [idx, s, slot, memObj, hle, ↓reduceIte] using hci
        simp only [hle, ↓reduceIte]
        have hidx : idx < m.numLookups := by simp [idx, Member.numLookups, hi]
        have hnotSend : ¬ idx < m.origin.sends.length := by simp [idx]
        have hsub : idx - m.origin.sends.length = i := Nat.add_sub_cancel_left _ _
        have hraw : m.rawPayloadAt idx =
            (memObj.enable, [.const 0, .const 0, memObj.address] ++ memObj.value.words) := by
          unfold Member.rawPayloadAt
          rw [dif_neg hnotSend, dif_pos (by omega)]
          simp [hsub, memObj]
        obtain ⟨henEq, hwordsEq⟩ := compactedSlot_eval hctx hidx hci' origCons
        rw [hraw] at henEq hwordsEq
        dsimp only at henEq hwordsEq
        refine ⟨henEq, fun hen1 => ?_⟩
        rw [henEq] at hen1
        have hminLen : 3 + memObj.value.words.length ≤ slot.args.length := hci'.2.2.2.1
        constructor
        · have h2 : (word slot.args 2).denote a' =
              (word ([.const (0 : F), .const 0, memObj.address] ++ memObj.value.words) 2).denote b :=
            hwordsEq hen1 2 (le_refl 2) (by omega)
          simpa [word] using h2
        · cases hval : memObj.value with
          | mk vty vwords =>
              rw [hval] at hminLen hwordsEq
              dsimp only at hminLen hwordsEq
              simp only [WireValue.map, WireValue.mk.injEq, true_and]
              apply List.ext_getElem
              · simp only [List.length_map, List.length_take, List.length_drop]
                omega
              · intro j hj1 hj2
                have hjlt : j < vwords.length := by simpa using hj2
                have hw : (word slot.args (3 + j)).denote a' =
                    (word ([.const (0 : F), .const 0, memObj.address] ++ vwords) (3 + j)).denote b :=
                  hwordsEq hen1 (3 + j) (by omega) (by omega)
                have hslotLt : 3 + j < slot.args.length := by omega
                have hrawLt : 3 + j < ([.const (0 : F), .const 0, memObj.address] ++ vwords).length := by
                  simp; omega
                simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                simp only [word, List.getElem?_eq_getElem hslotLt, List.getElem?_eq_getElem hrawLt,
                  Option.getD_some] at hw
                have hget : ([.const (0 : F), .const 0, memObj.address] ++ vwords)[3 + j]'hrawLt =
                    vwords[j]'hjlt := by
                  rw [List.getElem_append_right (by simp)]
                  simp
                rw [hget] at hw
                exact hw
  · exact Payload.ActiveEquiv.of_eq (by simpa only [Payload.denote_subst] using h.denote a)

/-- Finite checks over actual output expressions and actual constraints.
All conditions are decidable polynomial/structural comparisons. -/
structure Certificate (sources : List (Chip F)) (g : Layout F) : Prop where
  sources_eq : g.members.map Member.origin = sources
  shapes : ∀ m ∈ g.members, m.Shape
  names : ∀ m ∈ g.members, m.name = m.origin.name
  formed : ∀ m ∈ g.members, m.origin.wellFormed = true
  unique : ∀ m ∈ g.members, ∀ n ∈ g.members, m.selector = n.selector → m = n
  project_payload : ∀ m ∈ g.members,
    m.PayloadCheck g (g.back (some m.selector)) m.project
  extend_payload : ∀ m ∈ g.members,
    m.PayloadCheck g m.embedding (fun v => .var v)
  extend_constraints : ∀ m ∈ g.members, ∀ p ∈ g.constraints,
    Implied m.origin.constraints (p.subst m.embedding)
  extend_selectors : ∀ m ∈ g.members, ∀ n ∈ g.members,
    (m.embedding n.selector).Identical (.const (selected (some m.selector) n))
  extend_activation : ∀ m ∈ g.members,
    (g.activation.subst m.embedding).Identical (.const 1)
  zero_constraints : Satisfies g.constraints (fun _ => 0)

instance (sources : List (Chip F)) (g : Layout F) : Decidable (Certificate sources g) := by
  letI (m : Member F) : Decidable (∀ p ∈ g.constraints,
      Implied m.origin.constraints (p.subst m.embedding)) :=
    allImpliedDecidable m.origin.constraints g.constraints m.embedding
  letI : Decidable (Satisfies g.constraints (fun _ => (0 : F))) := by
    unfold Satisfies Scalar.Circuit.Satisfies
    infer_instance
  apply decidable_of_iff ((g.members.map Member.origin = sources) ∧
    (∀ m ∈ g.members, m.Shape) ∧
    (∀ m ∈ g.members, m.name = m.origin.name) ∧
    (∀ m ∈ g.members, m.origin.wellFormed = true) ∧
    (∀ m ∈ g.members, ∀ n ∈ g.members, m.selector = n.selector → m = n) ∧
    (∀ m ∈ g.members, m.PayloadCheck g (g.back (some m.selector)) m.project) ∧
    (∀ m ∈ g.members, m.PayloadCheck g m.embedding (fun v => .var v)) ∧
    (∀ m ∈ g.members, ∀ p ∈ g.constraints,
    Implied m.origin.constraints (p.subst m.embedding)) ∧
    (∀ m ∈ g.members, ∀ n ∈ g.members,
    (m.embedding n.selector).Identical (.const (selected (some m.selector) n))) ∧
    (∀ m ∈ g.members,
    (g.activation.subst m.embedding).Identical (.const 1)) ∧
    (Satisfies g.constraints (fun _ => 0)))
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · intro h
    exact ⟨h.sources_eq, h.shapes, h.names, h.formed, h.unique, h.project_payload, h.extend_payload, h.extend_constraints, h.extend_selectors, h.extend_activation, h.zero_constraints⟩

namespace Certificate
variable {sources : List (Chip F)} {g : Layout F}

theorem payload_project (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a)
    (selectors : ∀ n ∈ g.members, a n.selector = selected (some m.selector) n)
    (origCons : Satisfies m.origin.constraints (fun v => a (m.columns[v]?.getD 0))) :
    ((g.view m).denote a).ActiveEquiv ((ofChip m.origin).denote (fun v => a (m.columns[v]?.getD 0))) := by
  have back := g.back_sound checked.shapes a valid (some m.selector) selectors
  have same := (checked.project_payload m hm).sound a (by simpa [Member.project, Scalar.Circuit.ArithExpr.denote] using origCons)
  simpa only [back, Member.project, Scalar.Circuit.ArithExpr.denote] using same

theorem payload_extend (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (origCons : Satisfies m.origin.constraints a) :
    ((g.view m).denote (fun v => (m.embedding v).denote a)).ActiveEquiv ((ofChip m.origin).denote a) := by
  simpa only [Scalar.Circuit.ArithExpr.denote] using
    (checked.extend_payload m hm).sound a (by simpa [Scalar.Circuit.ArithExpr.denote] using origCons)

theorem project_valid (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : g.ValidRow rom a) (active : a m.selector = 1) :
    m.origin.ValidAssignment rom (fun v => a (m.columns[v]?.getD 0)) ∧
      ((g.view m).denote a).ActiveEquiv ((ofChip m.origin).denote (fun v => a (m.columns[v]?.getD 0))) := by
  obtain ⟨n, hn, _, selectors⟩ := g.select checked.shapes a valid.1 valid.2.1
  have sameSelector : n.selector = m.selector := by
    have h := selectors m hm
    by_contra hne
    simp [selected, hne, active] at h
  have same := checked.unique n hn m hm sameSelector
  subst n
  let b := fun v : Nat => a (m.columns[v]?.getD 0)
  have on : b m.sourceSelector = 1 := by simpa [b, ← (checked.shapes m hm).1] using active
  have origCons : Satisfies m.origin.constraints b :=
    g.selected_origin_constraints m hm a valid.1 on
  have payload := checked.payload_project m hm a valid.1 selectors origCons
  have memory := valid.2.2 m hm active
  rw [payload.memoryValid_iff rom, ofChip_memory] at memory
  exact ⟨⟨origCons, memory⟩, payload⟩

theorem extend_valid (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : m.origin.ValidAssignment rom a) :
    g.ValidRow rom (fun v => (m.embedding v).denote a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h := (checked.extend_constraints m hm p hp).sound a valid.1
    simpa only [Polynomial.denote_subst] using h
  · simpa only [Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote] using
      (checked.extend_activation m hm).denote a
  · intro n hn on
    have sel := (checked.extend_selectors m hm n hn).denote a
    have sameSelector : m.selector = n.selector := by
      by_contra different
      simp [selected, different, Scalar.Circuit.ArithExpr.denote, on] at sel
    have same := checked.unique m hm n hn sameSelector
    subst n
    rw [(checked.payload_extend m hm a valid.1).memoryValid_iff rom, ofChip_memory]
    exact valid.2

/-- The complete emitted row rule is equivalent to the disjunction of the
original source row rules. Selection and source-memory validity are derived,
not premises supplied to this theorem. -/
theorem localRule_iff (checked : Certificate sources g) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    g.LocalRule rom root premises ↔ ∃ c ∈ sources, c.LocalRule rom root premises := by
  constructor
  · rintro ⟨a, m, hm, valid, active, rootEq, callsEq⟩
    have h := checked.project_valid m hm a valid active
    have finite := m.origin.finiteAssignment (checked.formed m hm)
      (fun v => a (m.columns[v]?.getD 0)) rom
    refine ⟨m.origin, ?_, Row.ofAssignment m.origin.name m.origin.numVars
      (fun v => a (m.columns[v]?.getD 0)), rfl,
      ⟨checked.formed m hm, Row.ofAssignment_length _ _ _, finite.1.mp h.1⟩, ?_, ?_⟩
    · rw [← checked.sources_eq]
      exact List.mem_map.mpr ⟨m, hm, rfl⟩
    · rw [h.2.root_eq, ofChip_root] at rootEq
      exact finite.2.1.symm.trans rootEq
    · rw [h.2.requirements_eq, ofChip_requirements] at callsEq
      exact finite.2.2.symm.trans callsEq
  · rintro ⟨c, hc, row, _, valid, rootEq, callsEq⟩
    rw [← checked.sources_eq] at hc
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc
    have ext := checked.payload_extend m hm row.assignment valid.2.2.1
    refine ⟨fun v => (m.embedding v).denote row.assignment, m, hm,
      checked.extend_valid m hm row.assignment valid.2.2, ?_, ?_, ?_⟩
    · simpa [selected, Scalar.Circuit.ArithExpr.denote] using
        (checked.extend_selectors m hm m hm).denote row.assignment
    · rw [ext.root_eq, ofChip_root]
      exact rootEq
    · rw [ext.requirements_eq, ofChip_requirements]
      exact callsEq

end Certificate
end Aiur.Optimized.Grouping
