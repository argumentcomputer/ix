import IxCC.Xv.Validate.Check
import IxCC.Xv.Validate.Proof.RowSim
import IxCC.Xv.Validate.Proof.State

/-!
# What the operand checks establish

`operandCode c ps row = none` (the validator's per-instruction checks,
05 §5) decoded into propositions (`OperandFacts`), and, for a row whose
operands are paired with their locations, the facts the row simulation
needs (`rowFacts_of_checks`): every operand's location is usable and meets
its constraint, a tie's definition shares its use's location (`tie_loc`),
definitions are distinct, early definitions avoid the uses, and the row's
stack cells fit the scratch registers it does not name.
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Operand Kind Pos Con)
open IxCC.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable WriteOk)
open IxCC.Xv

/-! ## Boolean checks -/

theorem nodup_iff : ∀ {xs : List VReg}, nodup xs = true ↔ xs.Nodup
  | [] => by simp [nodup]
  | x :: xs => by
      rw [List.nodup_cons, ← nodup_iff]
      simp [nodup]

theorem allDistinct_iff : ∀ {ls : List Loc}, allDistinct ls = true ↔ ls.Nodup
  | [] => by simp [allDistinct]
  | l :: ls => by
      rw [List.nodup_cons, ← allDistinct_iff]
      simp [allDistinct]

theorem firstCode_none : ∀ {cs : List (Option Code)}, firstCode cs = none → ∀ c ∈ cs, c = none
  | [], _, _, h => by simp at h
  | none :: cs, h, c, hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · rfl
      · exact firstCode_none (by simpa [firstCode] using h) c hc
  | some _ :: _, h, _, _ => by simp [firstCode] at h

/-- The checks of `operandCode`, as propositions. -/
structure OperandFacts (c : Ctx) (ps : Pairs) (row : Bool) : Prop where
  loc : ∀ p ∈ ps, locCode c p.2 = none
  con : ∀ p ∈ ps, conOk p.1.con p.2 = true
  tie : ∀ p ∈ ps, tieOk ps p = true
  defLocs : ((defsOf ps).map (·.2)).Nodup
  defRegs : ((defsOf ps).map (·.1.v)).Nodup
  early : ∀ p ∈ defsOf ps, p.1.pos = .early → ∀ u ∈ usesOf ps, u.2 ≠ p.2
  cells : row = true → ((dedup (ps.map (·.2))).filter Loc.isCell).length +
    ((dedup (ps.map (·.2))).filter (!·.isCell)).length ≤ scratch.length

theorem operandCode_none {c : Ctx} {ps : Pairs} {row : Bool} (h : operandCode c ps row = none) :
    OperandFacts c ps row := by
  unfold operandCode at h
  split at h
  · simp at h
  rename_i hfirst
  have hloc : ∀ p ∈ ps, locCode c p.2 = none := fun p hp =>
    firstCode_none hfirst _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  split at h
  · simp at h
  rename_i hcon
  split at h
  · simp at h
  rename_i htie
  dsimp only at h
  split at h
  · simp at h
  rename_i hdist
  split at h
  · simp at h
  rename_i hearly
  split at h
  · simp at h
  rename_i hlate
  have hcon' : ps.all (fun p => conOk p.1.con p.2) = true := by
    cases e : ps.all (fun p => conOk p.1.con p.2) <;> simp_all
  have htie' : ps.all (tieOk ps) = true := by
    cases e : ps.all (tieOk ps) <;> simp_all
  have hd₁ : allDistinct ((defsOf ps).map (·.2)) = true := by
    cases e : allDistinct ((defsOf ps).map (·.2)) <;> simp_all
  have hd₂ : nodup ((defsOf ps).map (·.1.v)) = true := by
    cases e : nodup ((defsOf ps).map (·.1.v)) <;> simp_all
  refine ⟨hloc, ?_, ?_, allDistinct_iff.1 hd₁, nodup_iff.1 hd₂, ?_, ?_⟩
  · intro p hp; exact List.all_eq_true.1 hcon' p hp
  · intro p hp; exact List.all_eq_true.1 htie' p hp
  · intro p hp he u hu e
    apply hearly
    rw [List.any_eq_true]
    refine ⟨p, hp, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨he, List.contains_iff_mem.2 (List.mem_map.2 ⟨u, hu, e⟩)⟩
  · intro hr
    split at h
    · simp at h
    · rename_i hc
      simp only [hr, Bool.true_and, gt_iff_lt, decide_eq_true_eq, Nat.not_lt] at hc
      exact hc

/-! ## Constraints -/

theorem conOk_readCon {s : X86.Slot} {l : Loc} (h : conOk (readCon s) l = true) :
    (!l.isCell || s.kinds.contains .mem) = true := by
  unfold readCon at h
  split at h
  · rename_i hm; simp [List.contains_iff_mem.1 hm]
  · cases l <;> simp_all [conOk, Loc.isCell]

theorem conOk_writeCon {s : X86.Slot} {l : Loc} (h : conOk (writeCon s) l = true) :
    (!l.isCell || (s.kinds.contains .mem && s.width == .w64)) = true := by
  unfold writeCon at h
  split at h
  · rename_i hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    simp [List.contains_iff_mem.1 hm.1, hm.2]
  · cases l <;> simp_all [conOk, Loc.isCell]

theorem conOk_reg {l : Loc} (h : conOk .reg l = true) : l.isCell = false := by
  cases l <;> simp_all [conOk, Loc.isCell]

theorem conOk_fixed {r : X86.GPR} {l : Loc} (h : conOk (.fixed r) l = true) : l = .reg r := by
  simpa [conOk] using h

/-! ## Operands paired with locations -/

/-- Operands over `VReg × Loc` as the validator's pairs. -/
def pairsOf (ops : List (Operand (VReg × Loc))) : Pairs := ops.map fun o => (opMap Prod.fst o, o.v.2)

theorem mem_pairsOf {ops : List (Operand (VReg × Loc))} {o : Operand (VReg × Loc)} (h : o ∈ ops) :
    (opMap Prod.fst o, o.v.2) ∈ pairsOf ops :=
  List.mem_map.2 ⟨o, h, rfl⟩

theorem boundUses_kind {α : Type} : ∀ {bs : List (Bound α)}, ∀ o ∈ boundUses bs, o.kind = .use ∧ o.pos = .early
  | [], o, h => by simp [boundUses] at h
  | b :: bs, o, h => by
      simp only [boundUses, List.mem_append] at h
      rcases h with h | h
      · cases b with
        | input s a =>
          cases a with
          | m m =>
            simp only [List.mem_map] at h
            obtain ⟨_, _, rfl⟩ := h
            simp [useAt]
          | _ => simp_all [useAt]
        | memory s m =>
          simp only [List.mem_map] at h
          obtain ⟨_, _, rfl⟩ := h
          simp [useAt]
        | _ => simp_all [useAt]
      · exact boundUses_kind o h

theorem boundDefs_kind {α : Type} (z : Bool) : ∀ (i : Nat) {bs : List (Bound α)}, ∀ o ∈ boundDefs z i bs,
    o.kind = .define
  | _, [], o, h => by simp [boundDefs] at h
  | i, b :: bs, o, h => by
      simp only [boundDefs, List.mem_append] at h
      rcases h with h | h
      · cases b with
        | output s x =>
          simp only at h
          split at h <;> simp_all [defAt, earlyDefAt]
        | _ => simp_all [defAt]
      · exact boundDefs_kind z _ o h

theorem usesOf_pairs {bs : List (Bound (VReg × Loc))} {z : Bool} :
    usesOf (pairsOf (boundOperands bs z)) = pairsOf (boundUses bs) := by
  unfold usesOf pairsOf boundOperands
  rw [List.map_append, List.filter_append]
  have h1 : (List.map (fun o => (opMap Prod.fst o, o.v.2)) (boundUses bs)).filter
      (fun p => p.1.kind == .use) = (boundUses bs).map (fun o => (opMap Prod.fst o, o.v.2)) := by
    apply List.filter_eq_self.2
    intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    simp [(boundUses_kind o ho).1]
  have h2 : (List.map (fun o => (opMap Prod.fst o, o.v.2)) (boundDefs z 0 bs)).filter
      (fun p => p.1.kind == .use) = [] := by
    apply List.filter_eq_nil_iff.2
    intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    simp [boundDefs_kind z 0 o ho]
  rw [h1, h2, List.append_nil]

theorem defsOf_pairs {bs : List (Bound (VReg × Loc))} {z : Bool} :
    defsOf (pairsOf (boundOperands bs z)) = pairsOf (boundDefs z 0 bs) := by
  unfold defsOf pairsOf boundOperands
  rw [List.map_append, List.filter_append]
  have h1 : (List.map (fun o => (opMap Prod.fst o, o.v.2)) (boundUses bs)).filter
      (fun p => p.1.kind == .define) = [] := by
    apply List.filter_eq_nil_iff.2
    intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    simp [(boundUses_kind o ho).1]
  have h2 : (List.map (fun o => (opMap Prod.fst o, o.v.2)) (boundDefs z 0 bs)).filter
      (fun p => p.1.kind == .define) = (boundDefs z 0 bs).map (fun o => (opMap Prod.fst o, o.v.2)) := by
    apply List.filter_eq_self.2
    intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    simp [boundDefs_kind z 0 o ho]
  rw [h1, h2, List.nil_append]

/-! ## Operands of a bound -/

theorem boundUses_flat {α : Type} : ∀ (bs : List (Bound α)), boundUses bs = bs.flatMap fun b => boundUses [b]
  | [] => rfl
  | b :: bs => by
      simp only [boundUses, List.flatMap_cons, List.append_nil]
      rw [boundUses_flat bs]
      simp [boundUses]

theorem mem_boundUses {α : Type} {bs : List (Bound α)} {b : Bound α} (hb : b ∈ bs)
    {o : Operand α} (ho : o ∈ boundUses [b]) : o ∈ boundUses bs := by
  rw [boundUses_flat]; exact List.mem_flatMap.2 ⟨b, hb, ho⟩

/-- Definitions of bounds other than ties do not depend on the use index. -/
theorem mem_boundDefs {α : Type} (z : Bool) {b : Bound α} (hb : ∀ i j, boundDefs z i [b] = boundDefs z j [b])
    {o : Operand α} (ho : o ∈ boundDefs z 0 [b]) : ∀ {bs : List (Bound α)} (i : Nat), b ∈ bs →
      o ∈ boundDefs z i bs
  | [], _, h => by simp at h
  | b' :: bs, i, h => by
      simp only [boundDefs, List.mem_append]
      rcases List.mem_cons.1 h with rfl | h
      · left
        have := hb 0 i
        simp only [boundDefs, List.append_nil] at this
        rw [← this]
        simpa [boundDefs] using ho
      · right; exact mem_boundDefs z hb ho _ h

/-- A tie's definition reuses its own use. -/
theorem tied_reuse {α : Type} (z : Bool) {s : X86.Slot} {a x : α} :
    ∀ {bs : List (Bound α)} (i : Nat), Bound.tied s a x ∈ bs →
      ∃ j, defAt (.reuse (i + j)) x ∈ boundDefs z i bs ∧ (boundUses bs)[j]? = some (useAt (writeCon s) a)
  | [], _, h => by simp at h
  | b :: bs, i, h => by
      rcases List.mem_cons.1 h with rfl | h
      · refine ⟨0, ?_, ?_⟩
        · simp [boundDefs]
        · simp [boundUses]
      · obtain ⟨j, hj, hu⟩ := tied_reuse z (i + (boundUses [b]).length) h
        refine ⟨(boundUses [b]).length + j, ?_, ?_⟩
        · simp only [boundDefs, List.mem_append]
          right
          rw [← Nat.add_assoc]
          exact hj
        · have e : boundUses (b :: bs) = boundUses [b] ++ boundUses bs := by
            simp [boundUses]
          rw [e, List.getElem?_append_right (by omega)]
          simpa using hu

theorem tie_loc {c : Ctx} {bs : List (Bound (VReg × Loc))} {z : Bool}
    (hf : OperandFacts c (pairsOf (boundOperands bs z)) row) {s : X86.Slot} {a x : VReg × Loc}
    (hb : Bound.tied s a x ∈ bs) : a.2 = x.2 := by
  obtain ⟨j, hj, hu⟩ := tied_reuse z 0 hb
  simp only [Nat.zero_add] at hj
  have hp : (opMap Prod.fst (defAt (.reuse j) x), x.2) ∈ pairsOf (boundOperands bs z) :=
    mem_pairsOf (by unfold boundOperands; exact List.mem_append_right _ hj)
  have ht := hf.tie _ hp
  simp only [tieOk, opMap_con, defAt] at ht
  have hjlt : j < (boundUses bs).length := by
    rcases h : (boundUses bs)[j]? with _ | _
    · rw [h] at hu; cases hu
    · exact (List.getElem?_eq_some_iff.1 h).1
  have hget : (pairsOf (boundOperands bs z))[j]? = some (opMap Prod.fst (useAt (writeCon s) a), a.2) := by
    unfold pairsOf boundOperands
    rw [List.getElem?_map, List.getElem?_append_left hjlt, hu]
    rfl
  rw [hget] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  exact ht.2

end IxCC.Xv.Validate
