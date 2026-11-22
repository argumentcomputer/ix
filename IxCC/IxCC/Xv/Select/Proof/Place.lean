import IxCC.Xv.Validate.Proof.XvRow
import IxCC.Xv.Validate.Proof.Assign

/-!
# An Xv row runs: placement always succeeds

`Validate.Proof.XvRow.execBound_spec` describes a *successful* Xv row run as
a register assignment. Selection's proof needs the converse: an Xv row runs
whenever its operands are defined, the scratch registers suffice and its
fixed uses name distinct registers, and its outcome is then the rows'
outcome on the assignment's core (`execBound_run`). Each use's register
holds its value there, each write-only output's register is zero, the
context register holds the context, and the definitions are read back from
their registers afterwards.
-/

namespace IxCC.Xv

open IxCC.Lir (VReg Word Env)
open X86 (GPR)

/-! ## How many registers a placement takes -/

/-- The scratch registers the placer hands out for a bound operand. -/
def Bound.need : Bound VReg → Nat
  | .input _ a => a.regs.length
  | .output .. | .tied .. => 1
  | .memory _ m => m.regs.length
  | .fixedUse .. | .fixedDef .. | .fixedTied .. => 0

/-- The fixed register a bound operand reads, if any. -/
def Bound.fixedUse? : Bound VReg → Option GPR
  | .fixedUse i _ | .fixedTied i _ _ => some i.reg
  | _ => none

theorem Amode.map_id' (a : Amode VReg) : a.map id = a := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;> rfl

theorem Bound.map_id' (b : Bound VReg) : b.map id = b := by
  cases b with
  | input s a => cases a <;> simp [Bound.map, XArg.map, Amode.map_id']
  | memory s m => simp [Bound.map, Amode.map_id']
  | _ => rfl

/-! ## The placer succeeds -/

theorem Placer.take_some {p : Placer} (h : p.free ≠ []) : ∃ r p', p.take = some (r, p') := by
  unfold Placer.take
  cases hf : p.free with
  | nil => exact absurd hf h
  | cons r rs => exact ⟨r, _, rfl⟩

theorem Placer.use_some {p : Placer} (h : p.free ≠ []) (x : VReg) : ∃ r p', p.use x = some (r, p') := by
  obtain ⟨r, p', ht⟩ := take_some h
  simp [Placer.use, ht, pure]

theorem Placer.amode_some {p : Placer} {am : Amode VReg} (hlen : am.regs.length ≤ p.free.length)
    (hrsp : GPR.rsp ∉ p.free) : ∃ m p', p.amode am = some (m, p') := by
  rcases am with ⟨base, index, disp⟩
  have hidx : ∀ r ∈ p.free, ∃ i, indexReg r = some i := by
    intro r hr
    cases r <;> simp [indexReg]
    exact hrsp hr
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨x, s⟩
  · simp [Placer.amode, pure]
  · have hne : p.free ≠ [] := by intro h; simp [h, Amode.regs] at hlen
    obtain ⟨r, p₁, hu⟩ := use_some hne x
    obtain ⟨hf, -, -⟩ := use_spec hu
    obtain ⟨i, hi⟩ := hidx r (by rw [hf]; simp)
    simp [Placer.amode, hu, hi, pure]
  · have hne : p.free ≠ [] := by intro h; simp [h, Amode.regs] at hlen
    obtain ⟨r, p₁, hu⟩ := use_some hne b
    simp [Placer.amode, hu, pure]
  · have hne : p.free ≠ [] := by intro h; simp [h, Amode.regs] at hlen
    obtain ⟨r, p₁, hu⟩ := use_some hne b
    obtain ⟨hf, -, -⟩ := use_spec hu
    have hne' : p₁.free ≠ [] := by
      intro h
      rw [hf, h] at hlen
      simp [Amode.regs] at hlen
    obtain ⟨r', p₂, hu'⟩ := use_some hne' x
    obtain ⟨hf', -, -⟩ := use_spec hu'
    obtain ⟨i, hi⟩ := hidx r' (by rw [hf, hf']; simp)
    simp [Placer.amode, hu, hu', hi, pure]
  · simp [Placer.amode, pure]
  · have hne : p.free ≠ [] := by intro h; simp [h, Amode.regs] at hlen
    obtain ⟨r, p₁, hu⟩ := use_some hne x
    obtain ⟨hf, -, -⟩ := use_spec hu
    obtain ⟨i, hi⟩ := hidx r (by rw [hf]; simp)
    simp [Placer.amode, hu, hi, pure]

/-- Placing a bound operand takes `need` free registers. -/
theorem Placer.bound_free {p p' : Placer} {b : Bound VReg} {arg : Option X86.Arg}
    (h : p.bound b = some (arg, p')) : p.free = p.free.take b.need ++ p'.free ∧ p'.free = p.free.drop b.need := by
  have h' : p.bound (b.map id) = some (arg, p') := by rw [Bound.map_id']; exact h
  obtain ⟨bR, hmap, -, -, -, hf, -, -⟩ := bound_spec h'
  have hlen : (bR.taken).length = b.need := by
    rw [← hmap]
    cases bR with
    | input s a => cases a <;> simp [Bound.taken, Bound.need, Bound.map, XArg.map, XArg.regs]
    | memory s m => simp [Bound.taken, Bound.need, Bound.map]
    | _ => simp [Bound.taken, Bound.need, Bound.map]
  rw [hf, ← hlen]
  simp

theorem Placer.bound_some {p : Placer} {b : Bound VReg} (hlen : b.need ≤ p.free.length)
    (hrsp : GPR.rsp ∉ p.free) : ∃ arg p', p.bound b = some (arg, p') := by
  cases b with
  | input s a =>
    cases a with
    | r a =>
      have hne : p.free ≠ [] := by intro h; simp [h, Bound.need, XArg.regs] at hlen
      obtain ⟨r, p', hu⟩ := use_some hne a
      simp [Placer.bound, hu, pure]
    | m am =>
      obtain ⟨m, p', ha⟩ := amode_some (am := am) (by simpa [Bound.need, XArg.regs] using hlen) hrsp
      simp [Placer.bound, ha, pure]
    | i w => simp [Placer.bound, pure]
  | output s x =>
    have hne : p.free ≠ [] := by intro h; simp [h, Bound.need] at hlen
    obtain ⟨r, p', ht⟩ := take_some hne
    simp [Placer.bound, ht, pure]
  | tied s a x =>
    have hne : p.free ≠ [] := by intro h; simp [h, Bound.need] at hlen
    obtain ⟨r, p', hu⟩ := use_some hne a
    simp [Placer.bound, hu, pure]
  | memory s am =>
    obtain ⟨m, p', ha⟩ := amode_some (am := am) (by simpa [Bound.need] using hlen) hrsp
    simp [Placer.bound, ha, pure]
  | fixedUse i a => simp [Placer.bound, pure]
  | fixedDef i x => simp [Placer.bound, pure]
  | fixedTied i a x => simp [Placer.bound, pure]

theorem Placer.bounds_some : ∀ {bs : List (Bound VReg)} {p : Placer},
    (bs.map Bound.need).sum ≤ p.free.length → GPR.rsp ∉ p.free →
      ∃ margs p', p.bounds bs = some (margs, p') ∧ p'.free = p.free.drop (bs.map Bound.need).sum
  | [], p, _, _ => ⟨[], p, rfl, by simp⟩
  | b :: bs, p, hlen, hrsp => by
      simp only [List.map_cons, List.sum_cons] at hlen
      obtain ⟨arg, p₁, hb⟩ := bound_some (p := p) (b := b) (by omega) hrsp
      obtain ⟨-, hf₁⟩ := bound_free hb
      have hrsp₁ : GPR.rsp ∉ p₁.free := fun h => hrsp (by rw [hf₁] at h; exact List.mem_of_mem_drop h)
      obtain ⟨margs, p₂, hbs, hf₂⟩ := bounds_some (bs := bs) (p := p₁) (by rw [hf₁]; simp; omega) hrsp₁
      refine ⟨arg.toList ++ margs, p₂, ?_, ?_⟩
      · simp [Placer.bounds, hb, hbs, pure]
      · rw [hf₂, hf₁, List.drop_drop]
        simp [List.map_cons, List.sum_cons, Nat.add_comm]

theorem placeParts_some : ∀ {parts : List (X86.Op × List (Bound VReg))} {acc : List (X86.Op × List X86.Arg)}
    {p : Placer},
    ((parts.flatMap (·.2)).map Bound.need).sum ≤ p.free.length → GPR.rsp ∉ p.free →
      ∃ acc' p', parts.foldlM placePart (acc, p) = some (acc', p')
  | [], acc, p, _, _ => ⟨acc, p, rfl⟩
  | (o, bs) :: parts, acc, p, hlen, hrsp => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append] at hlen
      obtain ⟨margs, p₁, hbs, hf₁⟩ := Placer.bounds_some (bs := bs) (p := p) (by omega) hrsp
      have hrsp₁ : GPR.rsp ∉ p₁.free := fun h => hrsp (by rw [hf₁] at h; exact List.mem_of_mem_drop h)
      obtain ⟨acc', p', hrest⟩ := placeParts_some (parts := parts) (acc := acc ++ [(o, margs)]) (p := p₁)
        (by rw [hf₁]; simp; omega) hrsp₁
      refine ⟨acc', p', ?_⟩
      simp only [List.foldlM_cons, placePart, hbs, Option.bind_eq_bind, Option.bind_some, pure]
      exact hrest

/-! ## Loading the uses -/

theorem loadValues_some {ρ : Env} :
    ∀ {loads : List (GPR × VReg)}, (∀ l ∈ loads, ∃ w, ρ[l.2]? = some w) →
      ∃ vals, loads.mapM (loadValue ρ) = some vals
  | [], _ => ⟨[], rfl⟩
  | l :: loads, h => by
      obtain ⟨w, hw⟩ := h l (by simp)
      obtain ⟨vals, hvals⟩ := loadValues_some (loads := loads) fun l' hl' => h l' (by simp [hl'])
      exact ⟨(l.1, w) :: vals, by simp [List.mapM_cons, loadValue, hw, hvals, pure]⟩

theorem loadValues_map {ρ : Env} :
    ∀ {loads : List (GPR × VReg)} {vals : List (GPR × Word)}, loads.mapM (loadValue ρ) = some vals →
      vals.map (·.1) = loads.map (·.1)
  | [], vals, h => by simp at h; subst h; rfl
  | l :: loads, vals, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨v, hv, vs, hvs, rfl⟩ := h
      simp only [loadValue, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hv
      obtain ⟨w, -, rfl⟩ := hv
      simp [loadValues_map hvs]

/-- The guard passes when the loaded registers are distinct. -/
theorem mem_eq_of_nodup_fst {β : Type} :
    ∀ {l : List (GPR × β)}, (l.map (·.1)).Nodup → ∀ {a b : GPR × β}, a ∈ l → b ∈ l → a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: xs, hn, a, b, ha, hb, h => by
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.1 ha with rfl | ha₁ <;> rcases List.mem_cons.1 hb with rfl | hb₁
      · rfl
      · exact absurd (by rw [h]; exact List.mem_map_of_mem (f := (·.1)) hb₁) hn.1
      · exact absurd (by rw [← h]; exact List.mem_map_of_mem (f := (·.1)) ha₁) hn.1
      · exact mem_eq_of_nodup_fst hn.2 ha₁ hb₁ h

/-- The guard passes when the loaded registers are distinct. -/
theorem guard_vals {vals : List (GPR × Word)} (hn : (vals.map (·.1)).Nodup) :
    (vals.all fun v => vals.all fun v' => v.1 != v'.1 || v.2 == v'.2) = true := by
  rw [List.all_eq_true]
  intro v hv
  rw [List.all_eq_true]
  intro v' hv'
  by_cases he : v.1 = v'.1
  · rw [mem_eq_of_nodup_fst hn hv hv' he]; simp
  · simp [he]

/-! ## The registers of the uses are distinct -/

theorem Bound.uses_regs_mem {b : Bound (VReg × GPR)} (ha : b.Assigned) {r : GPR}
    (h : r ∈ b.uses.map (·.2)) : r ∈ b.taken ∨ (b.map Prod.fst).fixedUse? = some r := by
  cases b with
  | input s a => cases a <;> simp_all [Bound.uses, Bound.taken, XArg.regs]
  | memory s m => simp_all [Bound.uses, Bound.taken]
  | tied s a x => simp_all [Bound.uses, Bound.taken]
  | output s x => simp [Bound.uses] at h
  | fixedDef i x => simp [Bound.uses] at h
  | fixedUse i a =>
      simp only [Bound.uses, List.map_cons, List.map_nil, List.mem_singleton] at h
      simp [Bound.map, Bound.fixedUse?, h, ha.symm]
  | fixedTied i a x =>
      simp only [Bound.uses, List.map_cons, List.map_nil, List.mem_singleton] at h
      simp [Bound.map, Bound.fixedUse?, h]
      exact .inr ha.1.symm

theorem Bound.fixedUse?_fixed {b : Bound VReg} {r : GPR} (h : b.fixedUse? = some r) : b.fixed? = some r := by
  cases b <;> simp_all [Bound.fixedUse?, Bound.fixed?]

theorem Bound.uses_regs_nodup {b : Bound (VReg × GPR)} (ht : b.taken.Nodup) : (b.uses.map (·.2)).Nodup := by
  cases b with
  | input s a => cases a <;> simp_all [Bound.uses, Bound.taken, XArg.regs]
  | memory s m => simp_all [Bound.uses, Bound.taken]
  | _ => simp [Bound.uses]

theorem uses_regs_nodup : ∀ {bs : List (Bound (VReg × GPR))}, (∀ b ∈ bs, b.Assigned) →
    (bs.flatMap Bound.taken).Nodup → ((bs.map (Bound.map Prod.fst)).filterMap Bound.fixedUse?).Nodup →
    (∀ r ∈ bs.flatMap Bound.taken, r ∉ (bs.map (Bound.map Prod.fst)).filterMap Bound.fixedUse?) →
    ((bs.flatMap Bound.uses).map (·.2)).Nodup
  | [], _, _, _, _ => by simp
  | b :: bs, ha, ht, hf, hd => by
      simp only [List.flatMap_cons, List.nodup_append] at ht
      simp only [List.map_cons, List.filterMap_cons] at hf
      have hfb : ∀ r, (b.map Prod.fst).fixedUse? = some r →
          r ∉ (bs.map (Bound.map Prod.fst)).filterMap Bound.fixedUse? := by
        intro r hr hm
        rw [hr] at hf
        simp only [List.nodup_cons] at hf
        exact hf.1 hm
      have hfs : ((bs.map (Bound.map Prod.fst)).filterMap Bound.fixedUse?).Nodup := by
        cases h : (b.map Prod.fst).fixedUse? <;> rw [h] at hf <;> simp_all
      have hds : ∀ r ∈ bs.flatMap Bound.taken, r ∉ (bs.map (Bound.map Prod.fst)).filterMap Bound.fixedUse? := by
        intro r hr hm
        refine hd r (by simp only [List.flatMap_cons, List.mem_append]; exact .inr hr) ?_
        obtain ⟨a, ha', hfa⟩ := List.mem_filterMap.1 hm
        exact List.mem_filterMap.2 ⟨a, by simp only [List.map_cons]; exact List.mem_cons_of_mem _ ha', hfa⟩
      have ih := uses_regs_nodup (fun b' hb' => ha b' (by simp [hb'])) ht.2.1 hfs hds
      simp only [List.flatMap_cons, List.map_append, List.nodup_append]
      refine ⟨Bound.uses_regs_nodup ht.1, ih, ?_⟩
      intro r hr r' hr' e
      subst e
      have hb := Bound.uses_regs_mem (ha b (by simp)) hr
      have hmem : ∀ {r : GPR}, r ∈ (bs.flatMap Bound.uses).map (·.2) →
          r ∈ bs.flatMap Bound.taken ∨ r ∈ (bs.map (Bound.map Prod.fst)).filterMap Bound.fixedUse? := by
        intro r h
        simp only [List.mem_map, List.mem_flatMap] at h
        obtain ⟨q, ⟨b', hb', hq⟩, rfl⟩ := h
        rcases Bound.uses_regs_mem (ha b' (by simp [hb'])) (List.mem_map_of_mem hq) with h | h
        · exact .inl (List.mem_flatMap.2 ⟨b', hb', h⟩)
        · exact .inr (List.mem_filterMap.2 ⟨b'.map Prod.fst, List.mem_map_of_mem hb', h⟩)
      rcases hb with hb | hb <;> rcases hmem hr' with hs | hs
      · exact ht.2.2 _ hb _ hs rfl
      · refine hd r (by simp [hb]) ?_
        obtain ⟨a, ha', hfa⟩ := List.mem_filterMap.1 hs
        exact List.mem_filterMap.2 ⟨a, by simp only [List.map_cons]; exact List.mem_cons_of_mem _ ha', hfa⟩
      · refine hd r (List.mem_flatMap.2 (by obtain ⟨b', hb', h⟩ := List.mem_flatMap.1 hs; exact ⟨b', List.mem_cons_of_mem _ hb', h⟩)) ?_
        exact List.mem_filterMap.2 ⟨b.map Prod.fst, by simp, hb⟩
      · exact hfb _ hb hs

/-! ## A row runs -/

/-- The fixed registers of rows' bound operands (uses and definitions),
which the placer keeps out of its free list. -/
def fixedRegs (parts : List (X86.Op × List (Bound VReg))) : List GPR :=
  parts.flatMap fun part => part.2.filterMap Bound.fixed?

theorem scratch_no_rsp : GPR.rsp ∉ scratch := by decide

theorem parts_map_id (parts : List (X86.Op × List (Bound VReg))) :
    (parts.map fun q => (q.1, q.2.map (Bound.map id))) = parts := by
  induction parts with
  | nil => rfl
  | cons q parts ih =>
      simp only [List.map_cons, ih]
      congr
      rw [show (Bound.map id : Bound VReg → Bound VReg) = id from funext Bound.map_id', List.map_id]

/-- An Xv row runs whenever its operands are defined, the scratch registers
suffice and its fixed uses name distinct registers: its outcome is the
rows' outcome on an assignment's core, which holds each use's value in its
register, zero in each write-only output's, and the context in `r15`. -/
theorem execBound_run {parts : List (X86.Op × List (Bound VReg))} {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (hneed : ((parts.flatMap (·.2)).map Bound.need).sum ≤
      (scratch.filter (!(fixedRegs parts).contains ·)).length)
    (hdef : ∀ x ∈ (parts.flatMap (·.2)).flatMap Bound.uses, ∃ w, ρ[x]? = some w)
    (hfix : ((parts.flatMap (·.2)).filterMap Bound.fixedUse?).Nodup) :
    ∃ (aps : List (APart VReg)) (margs : List (X86.Op × List X86.Arg)) (core : X86.Core),
      aps.map (fun q => (q.1, q.2.map (Bound.map Prod.fst))) = parts ∧
      (∀ q ∈ aps, ∀ b ∈ q.2, b.Assigned) ∧
      aps.mapM APart.args = some margs ∧
      core.memory = mem ∧ core.readReg .r15 = ctx ∧
      ((aps.flatMap (·.2)).flatMap Bound.taken).Nodup ∧
      (∀ b ∈ aps.flatMap (·.2), ∀ r ∈ b.taken, r ∈ scratch ∧ r ∉ fixedRegs parts) ∧
      (∀ q ∈ (aps.flatMap (·.2)).flatMap Bound.uses, q.2 ≠ .r15 → ρ[q.1]? = some (core.readReg q.2)) ∧
      (∀ b ∈ aps.flatMap (·.2), ∀ q ∈ b.outputs, core.readReg q.2 = 0) ∧
      execBound parts ρ mem ctx = (execRows margs core).map fun r =>
        (readBack r.1 ρ (((aps.flatMap (·.2)).flatMap Bound.defs).map fun q => (q.1, q.2)), r.1.memory, r.2) := by
  obtain ⟨fixed, hfixed⟩ : ∃ fixed, fixed = fixedRegs parts := ⟨_, rfl⟩
  let p₀ : Placer := { free := scratch.filter (!fixed.contains ·) }
  have hrsp : GPR.rsp ∉ p₀.free := fun h => scratch_no_rsp (List.mem_filter.1 h).1
  obtain ⟨acc', p', hfold⟩ := placeParts_some (parts := parts) (acc := []) (p := p₀)
    (by simp only [p₀]; rw [hfixed]; exact hneed) hrsp
  have hfold' := hfold
  rw [← parts_map_id parts] at hfold'
  obtain ⟨aps, hmap, hass, hargs, hfree, hloads, hreads⟩ := placeParts_spec (f := id) hfold'
  simp only [List.nil_append, id] at hargs hloads hreads
  rw [show p₀.loads = [] from rfl, List.append_nil] at hloads
  rw [show p₀.reads = [] from rfl, List.append_nil] at hreads
  have hargs' : aps.mapM APart.args = some acc' := by
    revert hargs; cases aps.mapM APart.args <;> simp
  -- The bound operands, as assigned.
  have hbs : parts.flatMap (·.2) = (aps.flatMap (·.2)).map (Bound.map Prod.fst) := by
    rw [← hmap]
    simp [List.flatMap_map, List.map_flatMap]
  have hflat : (aps.flatMap fun q => q.2.flatMap Bound.taken) = (aps.flatMap (·.2)).flatMap Bound.taken :=
    List.flatMap_assoc.symm
  have hp₀nd : p₀.free.Nodup := by simp only [p₀]; exact scratch_nodup.filter _
  rw [hfree] at hp₀nd
  have htk : ((aps.flatMap (·.2)).flatMap Bound.taken).Nodup := by
    rw [← hflat]; exact (List.nodup_append.1 hp₀nd).1
  have htk_mem : ∀ r ∈ (aps.flatMap (·.2)).flatMap Bound.taken, r ∈ scratch ∧ r ∉ fixed := by
    intro r hr
    have : r ∈ p₀.free := by rw [hfree, hflat]; exact List.mem_append_left _ hr
    obtain ⟨h₁, h₂⟩ := List.mem_filter.1 this
    refine ⟨h₁, fun hm => ?_⟩
    rw [List.contains_iff_mem.2 hm] at h₂
    cases h₂
  -- Uses are defined; load them.
  have hdef' : ∀ l ∈ p'.loads, ∃ w, ρ[l.2]? = some w := by
    intro l hl
    rw [hloads] at hl
    simp only [List.mem_reverse, List.mem_map] at hl
    obtain ⟨q, hq, rfl⟩ := hl
    apply hdef
    rw [hbs]
    simp only [List.mem_flatMap, List.mem_map] at hq ⊢
    obtain ⟨b, hb, hq⟩ := hq
    exact ⟨b.map Prod.fst, ⟨b, hb, rfl⟩, by rw [Bound.uses_map]; exact List.mem_map_of_mem hq⟩
  obtain ⟨vals, hvals⟩ := loadValues_some hdef'
  -- The loaded registers are distinct.
  have hnd : ((aps.flatMap (·.2)).flatMap Bound.uses |>.map (·.2)).Nodup := by
    refine uses_regs_nodup (fun b hb => ?_) htk ?_ ?_
    · obtain ⟨q, hq, hb⟩ := List.mem_flatMap.1 hb
      exact hass q hq b hb
    · rw [← hbs]; exact hfix
    · intro r hr hm
      apply (htk_mem r hr).2
      rw [hfixed]
      rw [← hbs] at hm
      obtain ⟨b, hb, hbr⟩ := List.mem_filterMap.1 hm
      have hi := Bound.fixedUse?_fixed hbr
      simp only [fixedRegs, List.mem_flatMap, List.mem_filterMap]
      obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.1 hb
      exact ⟨q, hq, b, hbq, hi⟩
  have hvnd : (vals.map (·.1)).Nodup := by
    rw [loadValues_map hvals, hloads]
    simp only [List.map_reverse, List.map_map]
    rw [List.nodup_iff_pairwise_ne, List.pairwise_reverse]
    exact List.Pairwise.imp (fun h e => h e.symm) hnd
  have hg := guard_vals hvnd
  obtain ⟨hv₁, hv₂⟩ := loadValues_spec hvals
  refine ⟨aps, acc', { registers := loadRegisters ctx vals, memory := mem }, hmap, hass, hargs', rfl,
    loadRegisters_r15 ctx vals, htk, ?_, ?_, ?_, ?_⟩
  · intro b hb r hr
    have := htk_mem r (List.mem_flatMap.2 ⟨b, hb, hr⟩)
    rw [hfixed] at this
    exact this
  · intro q hq hr
    have hl : (q.2, q.1) ∈ p'.loads := by
      rw [hloads]; simp only [List.mem_reverse, List.mem_map]; exact ⟨q, hq, rfl⟩
    obtain ⟨w, hw, hm⟩ := hv₁ _ hl
    rw [hw]
    show some w = some (loadRegisters ctx vals q.2)
    rw [loadRegisters_mem hg hr hm]
  · intro b hb q hq
    have hqt : q.2 ∈ b.taken := by
      rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_right _ hq)
    have hmem := htk_mem q.2 (List.mem_flatMap.2 ⟨b, hb, hqt⟩)
    have hr : q.2 ≠ .r15 := fun e => r15_not_mem_scratch (e ▸ hmem.1)
    refine loadRegisters_none hr fun w hw => ?_
    obtain ⟨x, hx⟩ := hv₂ _ hw
    rw [hloads] at hx
    simp only [List.mem_reverse, List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨q', hq', hr', -⟩ := hx
    obtain ⟨b', hb', hq'⟩ := List.mem_flatMap.1 hq'
    by_cases hfu : q' ∈ b'.freeUses
    · exact outputs_not_freeUses htk q (List.mem_flatMap.2 ⟨b, hb, hq⟩) q'
        (List.mem_flatMap.2 ⟨b', hb', hfu⟩) hr'.symm
    · obtain ⟨ap, hap, hb''⟩ := List.mem_flatMap.1 hb'
      obtain ⟨i, hi, hqi⟩ := Bound.uses_fixed (hass ap hap b' hb'') hq' hfu
      apply hmem.2
      rw [hfixed, ← hr', hqi]
      simp only [fixedRegs, List.mem_flatMap, List.mem_filterMap]
      rw [← hmap]
      exact ⟨(ap.1, ap.2.map (Bound.map Prod.fst)), List.mem_map_of_mem hap, b'.map Prod.fst,
        List.mem_map_of_mem hb'', by rw [Bound.fixed?_map, hi]⟩
  · subst hfixed
    simp only [p₀, fixedRegs] at hfold
    simp only [execBound, hfold, Option.bind_eq_bind, Option.bind_some, hvals, hg, guard, ite_true]
    rw [hreads]
    cases execRows acc' { registers := loadRegisters ctx vals, memory := mem } <;> simp [pure]

end IxCC.Xv
