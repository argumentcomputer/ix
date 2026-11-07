import IxCC.Xv.Validate.Proof.Checks

/-!
# From the operand checks to the row facts

`rowFacts_of_checks`: the validator's operand checks of an instruction's
rows, with its row-shape check, give the facts `execBound_sim` needs. The
one counting argument is the cell pressure check: the validator bounds the
distinct stack cells plus the distinct registers by the thirteen scratch
registers, which is exactly Xl's condition that the cells fit the scratch
registers the row does not name (`cells_fit`).
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Operand Kind Pos Con)
open IxCC.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable WriteOk)
open IxCC.Xv

/-! ## Counting -/

theorem length_filter_add {β : Type} (p : β → Bool) :
    ∀ (l : List β), (l.filter p).length + (l.filter fun x => !p x).length = l.length
  | [] => rfl
  | x :: l => by
      have := length_filter_add p l
      cases h : p x <;> simp [h] <;> omega

theorem mem_scratch_iff (r : X86.GPR) : r ∈ scratch ↔ Xl.reserved r = false := by
  cases r <;> decide

theorem perm_length {β : Type} {l₁ l₂ : List β} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.length = l₂.length :=
  ((List.perm_ext_iff_of_nodup h₁ h₂).2 h).length_eq

theorem nodup_filterMap_reg {l : List Loc} (h : l.Nodup) : (l.filterMap Xl.Loc.reg?).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at h
    cases x with
    | reg r =>
      simp only [List.filterMap_cons, Xl.Loc.reg?, List.nodup_cons]
      refine ⟨fun hm => ?_, ih h.2⟩
      rw [List.mem_filterMap] at hm
      obtain ⟨y, hy, e⟩ := hm
      cases y <;> simp [Xl.Loc.reg?] at e
      subst e
      exact h.1 hy
    | _ => simpa [List.filterMap_cons, Xl.Loc.reg?] using ih h.2

theorem length_filterMap_reg {l : List Loc} (h : ∀ x ∈ l, x.isCell = false) :
    (l.filterMap Xl.Loc.reg?).length = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    cases x <;> simp [Loc.isCell] at hx
    simp [Xl.Loc.reg?, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The validator's cell-pressure check gives Xl's. -/
theorem cells_fit {L : List Loc} {LB : List (Bound Loc)}
    (hmem : ∀ l, l ∈ L ↔ l ∈ xlLocs LB)
    (hres : ∀ r, Loc.reg r ∈ L → Xl.reserved r = false)
    (hc : ((dedup L).filter Loc.isCell).length + ((dedup L).filter (!·.isCell)).length ≤ scratch.length) :
    (xlCells LB).length ≤ (xlFree LB).length := by
  have e₁ : (xlCells LB).length = ((dedup L).filter Loc.isCell).length := by
    apply perm_length (Xl.nodup_dedup) (Xl.nodup_dedup.filter _)
    intro x
    simp only [Xl.mem_dedup, List.mem_filter]
    rw [hmem]
  have e₂ : (scratch.filter fun r => (xlNamed LB).contains r).length =
      ((dedup L).filter (!·.isCell)).length := by
    rw [← length_filterMap_reg (l := (dedup L).filter (!·.isCell)) (fun x hx => by
      simpa using (List.mem_filter.1 hx).2)]
    apply perm_length (Xl.scratch_nodup.filter _) (nodup_filterMap_reg (Xl.nodup_dedup.filter _))
    intro r
    simp only [List.mem_filter, List.mem_filterMap, Xl.mem_dedup, Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · rintro ⟨hs, hn⟩
      have hn' := Xl.mem_xlNamed.1 (List.contains_iff_mem.1 hn)
      exact ⟨.reg r, ⟨(hmem _).2 hn', rfl⟩, rfl⟩
    · rintro ⟨l, ⟨hl, hc⟩, e⟩
      cases l <;> simp [Xl.Loc.reg?] at e
      subst e
      exact ⟨(mem_scratch_iff _).2 (hres _ hl), List.contains_iff_mem.2 (Xl.mem_xlNamed.2 ((hmem _).1 hl))⟩
  have e₃ := length_filter_add (fun r => (xlNamed LB).contains r) scratch
  unfold xlFree
  omega

/-! ## The row facts -/

@[simp] theorem useAt_v {α : Type} (c : Con) (x : α) : (useAt c x).v = x := rfl
@[simp] theorem useAt_con {α : Type} (c : Con) (x : α) : (useAt c x).con = c := rfl
@[simp] theorem defAt_v {α : Type} (c : Con) (x : α) : (defAt c x).v = x := rfl
@[simp] theorem defAt_con {α : Type} (c : Con) (x : α) : (defAt c x).con = c := rfl
@[simp] theorem earlyDefAt_v {α : Type} (c : Con) (x : α) : (earlyDefAt c x).v = x := rfl
@[simp] theorem earlyDefAt_con {α : Type} (c : Con) (x : α) : (earlyDefAt c x).con = c := rfl

theorem pairs_snd {bs : List (Bound (VReg × Loc))} {z : Bool} :
    (pairsOf (boundOperands bs z)).map (·.2) =
      ((bs.flatMap Bound.uses).map (·.2)) ++ ((bs.flatMap Bound.defs).map (·.2)) := by
  unfold pairsOf boundOperands
  rw [List.map_map, List.map_append]
  have h1 := boundUses_v bs
  have h2 := boundDefs_v z 0 bs
  rw [← h1, ← h2, List.map_map, List.map_map]
  rfl

theorem use_pair {bs : List (Bound (VReg × Loc))} {z : Bool} {u : VReg × Loc}
    (hu : u ∈ bs.flatMap Bound.uses) : ∃ o ∈ boundUses bs, o.v = u ∧
      (opMap Prod.fst o, u.2) ∈ usesOf (pairsOf (boundOperands bs z)) := by
  rw [← boundUses_v] at hu
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
  exact ⟨o, ho, rfl, by rw [usesOf_pairs]; exact mem_pairsOf ho⟩

theorem def_pair {bs : List (Bound (VReg × Loc))} {z : Bool} {d : VReg × Loc}
    (hd : d ∈ bs.flatMap Bound.defs) : ∃ o ∈ boundDefs z 0 bs, o.v = d ∧
      (opMap Prod.fst o, d.2) ∈ defsOf (pairsOf (boundOperands bs z)) := by
  rw [← boundDefs_v z 0] at hd
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hd
  exact ⟨o, ho, rfl, by rw [defsOf_pairs]; exact mem_pairsOf ho⟩

theorem usesOf_mem {ps : Pairs} {p : Operand VReg × Loc} (h : p ∈ usesOf ps) : p ∈ ps :=
  (List.mem_filter.1 h).1

theorem defsOf_mem {ps : Pairs} {p : Operand VReg × Loc} (h : p ∈ defsOf ps) : p ∈ ps :=
  (List.mem_filter.1 h).1

/-- The constraint of an operand of bound `b` in the paired operand list. -/
theorem con_of_use {c : Ctx} {bs : List (Bound (VReg × Loc))} {z : Bool} {row : Bool}
    (hf : OperandFacts c (pairsOf (boundOperands bs z)) row) {b : Bound (VReg × Loc)} (hb : b ∈ bs)
    {o : Operand (VReg × Loc)} (ho : o ∈ boundUses [b]) : conOk o.con o.v.2 = true := by
  have := hf.con _ (mem_pairsOf (ops := boundOperands bs z)
    (by unfold boundOperands; exact List.mem_append_left _ (mem_boundUses hb ho)))
  simpa using this

theorem con_of_def {c : Ctx} {bs : List (Bound (VReg × Loc))} {z : Bool} {row : Bool}
    (hf : OperandFacts c (pairsOf (boundOperands bs z)) row) {o : Operand (VReg × Loc)}
    (ho : o ∈ boundDefs z 0 bs) : conOk o.con o.v.2 = true := by
  have := hf.con _ (mem_pairsOf (ops := boundOperands bs z)
    (by unfold boundOperands; exact List.mem_append_right _ ho))
  simpa using this

theorem rowFacts_of_checks {c : Ctx} {fr : Xl.Frame} (hin : fr.inArgs.size = c.stackParams)
    {parts : List (X86.Op × List (Bound (VReg × Loc)))} {z : Bool}
    (hshape : ∀ q ∈ parts, ∃ defs args, bindRow q.1 defs args = some q.2)
    (hstack : ∀ q ∈ parts, (X86.desc q.1).stack = .none)
    (hwide : ∀ q ∈ parts, ∀ i ∈ (X86.desc q.1).implicit, i.role.reads = true ∨ Wide i.width)
    (hnarrow : ∀ q ∈ parts, ∀ b ∈ q.2, b.narrowOutput = true → z = true ∧ parts.getLast? = some q)
    (honly : ∀ q ∈ parts.dropLast, q.2.flatMap Bound.defs = [])
    (hops : OperandFacts c (pairsOf (boundOperands (parts.flatMap Prod.snd) z)) true) :
    RowFacts parts z fr := by
  have locOf : ∀ p ∈ pairsOf (boundOperands (parts.flatMap Prod.snd) z), locCode c p.2 = none :=
    hops.loc
  have useLoc : ∀ u ∈ (parts.flatMap Prod.snd).flatMap Bound.uses, locCode c u.2 = none := by
    intro u hu
    obtain ⟨o, -, rfl, hp⟩ := use_pair (z := z) hu
    exact locOf _ (usesOf_mem hp)
  have defLoc : ∀ d ∈ (parts.flatMap Prod.snd).flatMap Bound.defs, locCode c d.2 = none := by
    intro d hd
    obtain ⟨o, -, rfl, hp⟩ := def_pair (z := z) hd
    exact locOf _ (defsOf_mem hp)
  have regOk : ∀ l, locCode c l = none → ∀ r, l = .reg r → Xl.reserved r = false := by
    intro l hl r e
    subst e
    simp only [locCode, allocatable] at hl
    cases h : Xl.reserved r <;> simp_all
  refine ⟨hshape, hstack, hwide, hnarrow, honly, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- placeable
    intro b hb
    cases b with
    | input s a =>
      cases a with
      | r q =>
        have := con_of_use hops hb (o := useAt (readCon s) q) (by simp [boundUses])
        simp only [useAt_con, useAt_v] at this
        simpa [Bound.map, XArg.map, Xl.Bound.placeable] using conOk_readCon this
      | _ => rfl
    | output s x =>
      by_cases hn : z = true ∧ (Bound.output s x).narrowOutput = true
      · obtain ⟨j, hj⟩ : ∃ j, earlyDefAt .reg x ∈ boundDefs z j [Bound.output s x] := ⟨0, by
          simp [boundDefs, hn.1, hn.2]⟩
        have hm := mem_boundDefs z (b := Bound.output s x) (fun i j => rfl)
          (by simpa [boundDefs] using hj) 0 hb
        have := con_of_def hops hm
        simp only [earlyDefAt_con, earlyDefAt_v] at this
        simp [Bound.map, Xl.Bound.placeable, conOk_reg this]
      · have hm := mem_boundDefs z (b := Bound.output s x) (o := defAt (writeCon s) x) (fun i j => rfl)
          (by simp [boundDefs, hn]) 0 hb
        have := con_of_def hops hm
        simp only [defAt_con, defAt_v] at this
        simpa [Bound.map, Xl.Bound.placeable] using conOk_writeCon this
    | tied s a x =>
      have hu := con_of_use hops hb (o := useAt (writeCon s) a) (by simp [boundUses])
      simp only [useAt_con, useAt_v] at hu
      have ht := tie_loc hops hb
      simp only [Bound.map, Xl.Bound.placeable, ht, beq_self_eq_true, Bool.true_and]
      have := conOk_writeCon hu
      rw [ht] at this
      exact this
    | memory s m => rfl
    | fixedUse i a =>
      have := con_of_use hops hb (o := useAt (.fixed i.reg) a) (by simp [boundUses])
      simp only [useAt_con, useAt_v] at this
      simp [Bound.map, Xl.Bound.placeable, conOk_fixed this]
    | fixedDef i x =>
      have hm := mem_boundDefs z (b := Bound.fixedDef i x) (o := defAt (.fixed i.reg) x) (fun i j => rfl)
        (by simp [boundDefs]) 0 hb
      have := con_of_def hops hm
      simp only [defAt_con, defAt_v] at this
      simp [Bound.map, Xl.Bound.placeable, conOk_fixed this]
    | fixedTied i a x =>
      have hu := con_of_use hops hb (o := useAt (.fixed i.reg) a) (by simp [boundUses])
      simp only [useAt_con, useAt_v] at hu
      have hm := mem_boundDefs z (b := Bound.fixedTied i a x) (o := defAt (.fixed i.reg) x) (fun i j => rfl)
        (by simp [boundDefs]) 0 hb
      have := con_of_def hops hm
      simp only [defAt_con, defAt_v] at this
      simp [Bound.map, Xl.Bound.placeable, conOk_fixed hu, conOk_fixed this]
  · -- address registers
    intro b hb u hu
    have hreg : ∀ (m : Amode (VReg × Loc)), u ∈ m.regs → (∀ q ∈ m.regs, useAt .reg q ∈ boundUses [b]) →
        u.2.isCell = false := fun m hm hall => by
      have := con_of_use hops hb (hall u hm)
      simp only [useAt_con, useAt_v] at this
      exact conOk_reg this
    cases b with
    | input s a =>
      cases a with
      | m m => exact hreg m hu fun q hq => by simp [boundUses]; exact ⟨q.1, q.2, hq, rfl⟩
      | _ => simp [Bound.addrRegs] at hu
    | memory s m => exact hreg m hu fun q hq => by simp [boundUses]; exact ⟨q.1, q.2, hq, rfl⟩
    | _ => simp [Bound.addrRegs] at hu
  · intro u hu r e
    exact regOk _ (useLoc u hu) r e
  · intro d hd
    have hl := defLoc d hd
    cases h : d.2 with
    | reg r => simp only [WriteOk]; exact regOk _ hl r h
    | slot i => trivial
    | inArg i =>
      rw [h] at hl
      simp only [locCode] at hl
      simp only [WriteOk, hin]
      split at hl <;> simp_all
    | outArg i => rw [h] at hl; simp [locCode] at hl
  · -- distinct definition locations
    have := hops.defLocs
    rw [defsOf_pairs] at this
    unfold pairsOf at this
    rw [List.map_map, ← boundDefs_v z 0, List.map_map] at *
    exact this
  · have := hops.defRegs
    rw [defsOf_pairs] at this
    unfold pairsOf at this
    rw [List.map_map, ← boundDefs_v z 0, List.map_map] at *
    exact this
  · -- early definitions avoid the uses
    intro b hb hn d hd u hu e
    obtain ⟨hz, -⟩ : z = true ∧ True := by
      obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.1 hb
      exact ⟨(hnarrow q hq b hbq hn).1, trivial⟩
    cases b with
    | output s x =>
      simp only [Bound.defs, List.mem_singleton] at hd
      subst hd
      have hm := mem_boundDefs z (b := Bound.output s d) (o := earlyDefAt .reg d) (fun i j => rfl)
        (by simp [boundDefs, hz, hn]) 0 hb
      have hp : (opMap Prod.fst (earlyDefAt .reg d), d.2) ∈ defsOf (pairsOf (boundOperands
          (parts.flatMap Prod.snd) z)) := by
        rw [defsOf_pairs]; exact mem_pairsOf hm
      obtain ⟨o, -, rfl, hup⟩ := use_pair (z := z) hu
      exact hops.early _ hp rfl _ hup e
    | _ => simp [Bound.narrowOutput] at hn
  · -- cells
    refine cells_fit (L := (pairsOf (boundOperands (parts.flatMap Prod.snd) z)).map (·.2)) ?_ ?_
      (hops.cells rfl)
    · intro l
      rw [pairs_snd, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
          exact use_mem_xlLocs hu
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
          exact def_mem_xlLocs hd
      · intro h
        rcases mem_xlLocs h with ⟨u, hu, rfl⟩ | ⟨d, hd, rfl⟩
        · exact .inl (List.mem_map_of_mem hu)
        · exact .inr (List.mem_map_of_mem hd)
    · intro r hr
      obtain ⟨p, hp, e⟩ := List.mem_map.1 hr
      exact regOk _ (locOf p hp) r e

end IxCC.Xv.Validate
