import Compilatrix.Xv.Validate.Proof.Assign

/-!
# An Xv row as a register assignment

`Xv.execBound` places the operands of all its parts with one placer, loads
the uses, runs the rows and reads the definitions back. `execBound_spec`
restates a successful run over operands with any payload (the validator
proof uses `VReg × Loc`) as a register assignment of those operands: each
use's register holds its register's value, each write-only output's
register starts at zero, the scratch registers handed out are distinct and
avoid the fixed ones, and the environment afterwards is the old one with
each definition read back from its register.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word Env)
open X86 (GPR)

variable {α : Type}

/-- The write-only output positions of a bound. -/
def Bound.outputs : Bound α → List α
  | .output _ x => [x]
  | _ => []

/-- The fixed register of a bound, if any, for assignments. -/
theorem Bound.fixed?_map {β : Type} (f : α → β) (b : Bound α) : (b.map f).fixed? = b.fixed? := by
  cases b <;> rfl

/-- One part, assigned. -/
abbrev APart (α : Type) := X86.Op × List (Bound (α × GPR))

/-- The machine arguments of assigned parts. -/
def APart.args (ap : APart α) : Option (X86.Op × List X86.Arg) :=
  (ap.1, ·) <$> slotArgs some some (ap.2.map (Bound.map Prod.snd))

theorem placeParts_spec {f : α → VReg} :
    ∀ {parts : List (X86.Op × List (Bound α))} {acc acc' : List (X86.Op × List X86.Arg)} {p p' : Placer},
      (parts.map fun q => (q.1, q.2.map (Bound.map f))).foldlM placePart (acc, p) = some (acc', p') →
      ∃ aps : List (APart α), aps.map (fun q => (q.1, q.2.map (Bound.map Prod.fst))) = parts ∧
        (∀ q ∈ aps, ∀ b ∈ q.2, b.Assigned) ∧
        (aps.mapM APart.args).map (acc ++ ·) = some acc' ∧
        p.free = (aps.flatMap fun q => q.2.flatMap Bound.taken) ++ p'.free ∧
        p'.loads = (((aps.flatMap (·.2)).flatMap Bound.uses).map fun q => (q.2, f q.1)).reverse ++ p.loads ∧
        p'.reads = (((aps.flatMap (·.2)).flatMap Bound.defs).map fun q => (f q.1, q.2)).reverse ++ p.reads
  | [], acc, acc', p, p', h => by
      simp only [List.map_nil, List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, by simp, by simp, by simp, by simp, by simp⟩
  | (o, bs) :: parts, acc, acc', p, p', h => by
      simp only [List.map_cons, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨acc₁, p₁⟩, h₁, h⟩ := h
      simp only [placePart, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h₁
      obtain ⟨⟨args, p₂⟩, hb, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨bR, hmap, hass, hargs, hf, hl, hr⟩ := Placer.bounds_spec hb
      obtain ⟨aps, hmaps, hasss, hargss, hfs, hls, hrs⟩ := placeParts_spec h
      refine ⟨(o, bR) :: aps, by simp [hmap, hmaps], ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hass
        · exact hasss q hq
      · simp only [List.mapM_cons, APart.args, hargs, Option.map_eq_map, Option.map_some,
          Option.bind_eq_bind, Option.bind_some]
        revert hargss
        cases List.mapM APart.args aps <;> simp
      · rw [hf, hfs]; simp
      · rw [hls, hl]; simp
      · rw [hrs, hr]; simp

/-! ## Loaded values -/

theorem loadValues_spec {ρ : Env} :
    ∀ {loads : List (GPR × VReg)} {vals : List (GPR × Word)}, loads.mapM (loadValue ρ) = some vals →
      (∀ l ∈ loads, ∃ w, ρ[l.2]? = some w ∧ (l.1, w) ∈ vals) ∧ (∀ v ∈ vals, ∃ x, (v.1, x) ∈ loads)
  | [], vals, h => by simp at h; subst h; simp
  | l :: loads, vals, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h
      obtain ⟨v, hv, vs, hvs, rfl⟩ := h
      simp only [loadValue, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      obtain ⟨ih₁, ih₂⟩ := loadValues_spec hvs
      refine ⟨?_, ?_⟩
      · intro l' hl'
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact ⟨w, hw, List.mem_cons_self⟩
        · obtain ⟨w', hw', hm⟩ := ih₁ l' hl'
          exact ⟨w', hw', List.mem_cons_of_mem _ hm⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨l.2, List.mem_cons_self⟩
        · obtain ⟨x, hx⟩ := ih₂ v hv
          exact ⟨x, List.mem_cons_of_mem _ hx⟩

theorem loadRegisters_mem {ctx : Word} {vals : List (GPR × Word)}
    (hg : (vals.all fun v => vals.all fun v' => v.1 != v'.1 || v.2 == v'.2) = true)
    {r : GPR} {w : Word} (hr : r ≠ .r15) (hm : (r, w) ∈ vals) : loadRegisters ctx vals r = w := by
  unfold loadRegisters
  have hne : (r == .r15) = false := by simpa using hr
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  cases hf : vals.find? (·.1 == r) with
  | none =>
    have := List.find?_eq_none.1 hf (r, w) hm
    simp at this
  | some v =>
    have hv := List.mem_of_find?_eq_some hf
    have hvr : v.1 = r := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.getD_some]
    rw [List.all_eq_true] at hg
    have := hg v hv
    rw [List.all_eq_true] at this
    have := this (r, w) hm
    simp [hvr] at this
    exact this

theorem loadRegisters_none {ctx : Word} {vals : List (GPR × Word)} {r : GPR} (hr : r ≠ .r15)
    (hm : ∀ w, (r, w) ∉ vals) : loadRegisters ctx vals r = 0 := by
  unfold loadRegisters
  have hne : (r == .r15) = false := by simpa using hr
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  cases hf : vals.find? (·.1 == r) with
  | none => rfl
  | some v =>
    have hv := List.mem_of_find?_eq_some hf
    have hvr : v.1 = r := by simpa using List.find?_some hf
    have : (v.1, v.2) ∈ vals := hv
    rw [hvr] at this
    exact absurd this (hm v.2)

theorem loadRegisters_r15 (ctx : Word) (vals : List (GPR × Word)) : loadRegisters ctx vals .r15 = ctx := by
  simp [loadRegisters]

/-! ## Reading back -/

theorem readBack_other {core : X86.Core} {x : VReg} :
    ∀ {ρ : Env} {reads : List (VReg × GPR)}, x ∉ reads.map (·.1) → (readBack core ρ reads)[x]? = ρ[x]?
  | _, [], _ => rfl
  | ρ, d :: reads, hx => by
      simp only [List.map_cons, List.mem_cons, not_or] at hx
      have e : readBack core ρ (d :: reads) = readBack core (ρ.insert d.1 (core.readReg d.2)) reads := rfl
      rw [e, readBack_other hx.2, Std.HashMap.getElem?_insert]
      have : (d.1 == x) = false := by simpa [beq_iff_eq] using fun e => hx.1 e.symm
      simp [this]

theorem readBack_mem {core : X86.Core} :
    ∀ {ρ : Env} {reads : List (VReg × GPR)}, (reads.map (·.1)).Nodup →
      ∀ d ∈ reads, (readBack core ρ reads)[d.1]? = some (core.readReg d.2)
  | _, [], _, d, hd => by simp at hd
  | ρ, d' :: reads, hn, d, hd => by
      simp only [List.map_cons, List.nodup_cons] at hn
      have e : readBack core ρ (d' :: reads) =
          readBack core (ρ.insert d'.1 (core.readReg d'.2)) reads := rfl
      rw [e]
      rcases List.mem_cons.1 hd with rfl | hd
      · rw [readBack_other hn.1, Std.HashMap.getElem?_insert_self]
      · exact readBack_mem hn.2 d hd

/-! ## Outputs start at zero -/

/-- The use positions of a bound that are not fixed. -/
def Bound.freeUses : Bound (α × GPR) → List (α × GPR)
  | .fixedUse .. | .fixedDef .. | .fixedTied .. => []
  | b => b.uses

theorem Bound.taken_eq (b : Bound (α × GPR)) :
    b.taken = (b.freeUses ++ b.outputs).map (·.2) := by
  cases b with
  | input s a => cases a <;> simp [Bound.taken, Bound.freeUses, Bound.outputs, Bound.uses, XArg.regs]
  | _ => simp [Bound.taken, Bound.freeUses, Bound.outputs, Bound.uses]

theorem outputs_not_freeUses :
    ∀ {bs : List (Bound (α × GPR))}, (bs.flatMap Bound.taken).Nodup →
      ∀ q ∈ bs.flatMap Bound.outputs, ∀ q' ∈ bs.flatMap Bound.freeUses, q.2 ≠ q'.2
  | [], _, q, hq, _, _ => by simp at hq
  | b :: bs, hn, q, hq, q', hq' => by
      simp only [List.flatMap_cons, List.nodup_append] at hn
      obtain ⟨hnb, hns, hdis⟩ := hn
      simp only [List.flatMap_cons, List.mem_append] at hq hq'
      have tk : ∀ q ∈ b.outputs, q.2 ∈ b.taken := fun q hq => by
        rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_right _ hq)
      have tu : ∀ q ∈ b.freeUses, q.2 ∈ b.taken := fun q hq => by
        rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_left _ hq)
      have tks : ∀ q ∈ bs.flatMap Bound.outputs, q.2 ∈ bs.flatMap Bound.taken := fun q hq => by
        simp only [List.mem_flatMap] at hq ⊢
        obtain ⟨b', hb', hq⟩ := hq
        exact ⟨b', hb', by rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_right _ hq)⟩
      have tus : ∀ q ∈ bs.flatMap Bound.freeUses, q.2 ∈ bs.flatMap Bound.taken := fun q hq => by
        simp only [List.mem_flatMap] at hq ⊢
        obtain ⟨b', hb', hq⟩ := hq
        exact ⟨b', hb', by rw [Bound.taken_eq]; exact List.mem_map_of_mem (List.mem_append_left _ hq)⟩
      rcases hq with hq | hq <;> rcases hq' with hq' | hq'
      · cases b <;> simp [Bound.outputs, Bound.freeUses, Bound.uses] at hq hq'
      · exact fun e => hdis _ (tk q hq) _ (e ▸ tus q' hq') rfl
      · exact fun e => hdis _ (tu q' hq') _ (e ▸ tks q hq) (e ▸ rfl) |>.elim
      · exact outputs_not_freeUses hns q hq q' hq'

theorem Bound.uses_fixed {b : Bound (α × GPR)} (ha : b.Assigned) {q : α × GPR} (hq : q ∈ b.uses)
    (hf : q ∉ b.freeUses) : ∃ i, b.fixed? = some i ∧ q.2 = i := by
  cases b <;> simp_all [Bound.uses, Bound.freeUses, Bound.fixed?, Bound.Assigned]

theorem Bound.taken_not_fixed {b : Bound (α × GPR)} {r : GPR} (hr : r ∈ b.taken) : b.fixed? = none := by
  cases b <;> simp_all [Bound.taken, Bound.fixed?]

/-! ## A row -/

theorem scratch_nodup : scratch.Nodup := by decide

theorem r15_not_mem_scratch : GPR.r15 ∉ scratch := by decide

/-- A successful Xv row run over operands with payload `α`, as a register
assignment. -/
theorem execBound_spec {parts : List (X86.Op × List (Bound α))} {f : α → VReg} {ρ ρ' : Env}
    {mem mem' : X86.Memory} {ctx : Word} {flags : X86.ByteEval.Flags}
    (h : execBound (parts.map fun q => (q.1, q.2.map (Bound.map f))) ρ mem ctx = some (ρ', mem', flags)) :
    ∃ (aps : List (APart α)) (margs : List (X86.Op × List X86.Arg)) (core core' : X86.Core),
      aps.map (fun q => (q.1, q.2.map (Bound.map Prod.fst))) = parts ∧
      (∀ q ∈ aps, ∀ b ∈ q.2, b.Assigned) ∧
      aps.mapM APart.args = some margs ∧
      execRows margs core = some (core', flags) ∧ core.memory = mem ∧ mem' = core'.memory ∧
      core.readReg .r15 = ctx ∧
      ((aps.flatMap (·.2)).flatMap Bound.taken).Nodup ∧
      (∀ b ∈ aps.flatMap (·.2), ∀ r ∈ b.taken, r ∈ scratch ∧
        ∀ b' ∈ aps.flatMap (·.2), ∀ i, b'.fixed? = some i → r ≠ i) ∧
      (∀ q ∈ (aps.flatMap (·.2)).flatMap Bound.uses, q.2 ≠ .r15 →
        ∃ w, ρ[f q.1]? = some w ∧ core.readReg q.2 = w) ∧
      (∀ b ∈ aps.flatMap (·.2), ∀ q ∈ b.outputs, core.readReg q.2 = 0) ∧
      ρ' = readBack core' ρ (((aps.flatMap (·.2)).flatMap Bound.defs).map fun q => (f q.1, q.2)) := by
  simp only [execBound, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨margs, p⟩, hfold, vals, hvals, ⟨⟩, hg, ⟨core', flags'⟩, hrun, he⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hgv : (vals.all fun v => vals.all fun v' => v.fst != v'.fst || v.snd == v'.snd) = true := by
    cases hc : (vals.all fun v => vals.all fun v' => v.fst != v'.fst || v.snd == v'.snd)
    · simp [guard, hc, failure] at hg
    · rfl
  simp only at hvals hrun
  obtain ⟨aps, hmap, hass, hargs, hfree, hloads, hreads⟩ := placeParts_spec hfold
  simp only [List.nil_append] at hargs
  have hargs' : aps.mapM APart.args = some margs := by
    revert hargs; cases aps.mapM APart.args <;> simp
  simp only [List.append_nil] at hfree hloads hreads
  obtain ⟨fixed, hfixed⟩ : ∃ fixed, fixed = (parts.map fun q => (q.1, q.2.map (Bound.map f))).flatMap
      fun part => part.2.filterMap Bound.fixed? := ⟨_, rfl⟩
  rw [← hfixed] at hfree
  have hfn : (scratch.filter (!fixed.contains ·)).Nodup := scratch_nodup.filter _
  rw [hfree] at hfn
  have htk_nodup := (List.nodup_append.1 hfn).1
  have hflat : (aps.flatMap fun q => q.2.flatMap Bound.taken) =
      (aps.flatMap (·.2)).flatMap Bound.taken := List.flatMap_assoc.symm
  have htk_mem : ∀ r ∈ (aps.flatMap (·.2)).flatMap Bound.taken, r ∈ scratch ∧ r ∉ fixed := by
    intro r hr
    have : r ∈ scratch.filter (!fixed.contains ·) := by
      rw [hfree]; apply List.mem_append_left
      rw [hflat]; exact hr
    simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    refine ⟨this.1, fun hm => ?_⟩
    have h2 := this.2
    rw [List.contains_iff_mem.2 hm] at h2
    cases h2
  obtain ⟨hv₁, hv₂⟩ := loadValues_spec hvals
  refine ⟨aps, margs, { registers := loadRegisters ctx vals, memory := mem }, core', hmap, hass, hargs',
    hrun, rfl, rfl, loadRegisters_r15 ctx vals, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hflat]; exact htk_nodup
  · intro b hb r hr
    have hm := htk_mem r (List.mem_flatMap.2 ⟨b, hb, hr⟩)
    refine ⟨hm.1, fun b' hb' i hi e => hm.2 ?_⟩
    subst e
    rw [hfixed, List.mem_flatMap]
    obtain ⟨ap, hap, hb''⟩ := List.mem_flatMap.1 hb'
    refine ⟨(ap.1, (ap.2.map (Bound.map Prod.fst)).map (Bound.map f)), ?_, ?_⟩
    · rw [← hmap, List.map_map]; exact List.mem_map.2 ⟨ap, hap, rfl⟩
    · rw [List.mem_filterMap]
      exact ⟨(b'.map Prod.fst).map f,
        List.mem_map.2 ⟨b'.map Prod.fst, List.mem_map.2 ⟨b', hb'', rfl⟩, rfl⟩,
        by rw [Bound.fixed?_map, Bound.fixed?_map, hi]⟩
  · intro q hq hr
    have hl : (q.2, f q.1) ∈ p.loads := by
      rw [hloads]; simp only [List.mem_reverse, List.mem_map]; exact ⟨q, hq, rfl⟩
    obtain ⟨w, hw, hm⟩ := hv₁ _ hl
    exact ⟨w, hw, loadRegisters_mem hgv hr hm⟩
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
    · exact outputs_not_freeUses (by rw [← hflat]; exact htk_nodup) q
        (List.mem_flatMap.2 ⟨b, hb, hq⟩) q' (List.mem_flatMap.2 ⟨b', hb', hfu⟩) hr'.symm
    · obtain ⟨ap, hap, hb''⟩ := List.mem_flatMap.1 hb'
      obtain ⟨i, hi, hqi⟩ := Bound.uses_fixed (hass ap hap b' hb'') hq' hfu
      apply hmem.2
      rw [hfixed, List.mem_flatMap]
      refine ⟨(ap.1, (ap.2.map (Bound.map Prod.fst)).map (Bound.map f)), ?_, ?_⟩
      · rw [← hmap, List.map_map]; exact List.mem_map.2 ⟨ap, hap, rfl⟩
      · rw [List.mem_filterMap]
        refine ⟨(b'.map Prod.fst).map f, ?_, ?_⟩
        · exact List.mem_map.2 ⟨b'.map Prod.fst, List.mem_map.2 ⟨b', hb'', rfl⟩, rfl⟩
        · rw [Bound.fixed?_map, Bound.fixed?_map, hi, ← hr', hqi]
  · rw [hreads]; simp

end Compilatrix.Xv
