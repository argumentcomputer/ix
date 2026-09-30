import Compilatrix.Xv.Validate.Proof.XlPlace

/-!
# Rows in sequence, and writing back

The pieces `Proof.Row` assembles: a fused pair's rows run one after the
other (`rows_corr`, where every row but the last defines nothing, so the
registers the next row reads are unchanged), Xv's definition registers are
distinct (`defRegs_nodup`), and Xl writes each definition back to its
location (`writeBacks_spec`).
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word)
open X86 (GPR)
open Compilatrix.Xv.Validate (Wide)

variable {α : Type}

/-! ## Rows in sequence -/

/-- One step of `execRows`. -/
def rowStep (s : X86.Core × X86.ByteEval.Flags) (p : X86.Op × List X86.Arg) :
    Option (X86.Core × X86.ByteEval.Flags) :=
  execRow p.1 p.2 s.1 s.2

theorem execRows_eq (parts : List (X86.Op × List X86.Arg)) (core : X86.Core) :
    execRows parts core = parts.foldlM rowStep (core, {}) := rfl

theorem APart.reassign_args (g : α → GPR) (ap : APart α) :
    (ap.reassign g).args = (ap.1, ·) <$> slotArgs some some (ap.2.map (Bound.map fun q => g q.1)) := by
  simp [APart.args, APart.reassign, List.map_map, Function.comp_def, Bound.reassign_snd]

theorem rows_corr {val : α → Word} {g : α → GPR} :
    ∀ {aps : List (APart α)} {margs₁ margs₂ : List (X86.Op × List X86.Arg)} {c₁ c₂ c₁' : X86.Core}
      {fl fl' : X86.ByteEval.Flags},
      aps.mapM APart.args = some margs₁ → (aps.map (APart.reassign g)).mapM APart.args = some margs₂ →
      (∀ ap ∈ aps, PartShape ap ∧ (X86.desc ap.1).stack = .none ∧
        ∀ i ∈ (X86.desc ap.1).implicit, i.role.reads = true ∨ Wide i.width) →
      (∀ ap ∈ aps, ∀ b ∈ ap.2, b.Assigned ∧ (b.reassign g).Assigned) →
      (∀ ap ∈ aps.dropLast, ap.2.flatMap Bound.defs = []) →
      c₁.memory = c₂.memory → c₁.readReg .r15 = c₂.readReg .r15 →
      (∀ q ∈ (aps.flatMap (·.2)).flatMap Bound.uses, c₁.readReg q.2 = val q.1) →
      (∀ q ∈ (aps.flatMap (·.2)).flatMap Bound.uses, c₂.readReg (g q.1) = val q.1) →
      (∀ b ∈ aps.flatMap (·.2), b.narrowOutput = true → ∀ q ∈ b.defs, c₁.readReg q.2 = 0) →
      (∀ b ∈ aps.flatMap (·.2), b.narrowOutput = true → ∀ q ∈ b.defs, c₂.readReg (g q.1) = 0) →
      (((aps.flatMap (·.2)).flatMap Bound.defs).map (·.2)).Nodup →
      (((aps.flatMap (·.2)).flatMap Bound.defs).map fun q => g q.1).Nodup →
      margs₁.foldlM rowStep (c₁, fl) = some (c₁', fl') →
      ∃ c₂', margs₂.foldlM rowStep (c₂, fl) = some (c₂', fl') ∧ c₁'.memory = c₂'.memory ∧
        ∀ q ∈ (aps.flatMap (·.2)).flatMap Bound.defs, c₁'.readReg q.2 = c₂'.readReg (g q.1)
  | [], margs₁, margs₂, c₁, c₂, c₁', fl, fl', h₁, h₂, _, _, _, hmem, _, _, _, _, _, _, _, hrun => by
      simp only [List.mapM_nil, pure, Option.some.injEq, List.map_nil] at h₁ h₂
      subst h₁ h₂
      simp only [List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨c₂, rfl, hmem, by simp⟩
  | ap :: rest, margs₁, margs₂, c₁, c₂, c₁', fl, fl', h₁, h₂, hsh, hass, hlast, hmem, hctx, hv₁, hv₂,
      hz₁, hz₂, hn₁, hn₂, hrun => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h₁
      obtain ⟨a₁, ha₁, ms₁, hms₁, rfl⟩ := h₁
      simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h₂
      obtain ⟨a₂, ha₂, ms₂, hms₂, rfl⟩ := h₂
      simp only [APart.args, Option.map_eq_map, Option.map_eq_some_iff] at ha₁
      obtain ⟨args₁, hargs₁, rfl⟩ := ha₁
      rw [APart.reassign_args, Option.map_eq_map, Option.map_eq_some_iff] at ha₂
      obtain ⟨args₂, hargs₂, rfl⟩ := ha₂
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
      obtain ⟨⟨d₁, fl₁⟩, hstep, hrest⟩ := hrun
      obtain ⟨hshape, hstack, hwide⟩ := hsh ap List.mem_cons_self
      have hmemb : ∀ b ∈ ap.2, b ∈ (ap :: rest).flatMap (·.2) := fun b hb =>
        List.mem_flatMap.2 ⟨ap, List.mem_cons_self, hb⟩
      have hmemr : ∀ b ∈ rest.flatMap (·.2), b ∈ (ap :: rest).flatMap (·.2) := fun b hb => by
        simp only [List.flatMap_cons]; exact List.mem_append_right _ hb
      have hfl : ((ap :: rest).flatMap (·.2)).flatMap Bound.defs =
          ap.2.flatMap Bound.defs ++ (rest.flatMap (·.2)).flatMap Bound.defs := by
        simp [List.flatMap_append]
      have hfu : ((ap :: rest).flatMap (·.2)).flatMap Bound.uses =
          ap.2.flatMap Bound.uses ++ (rest.flatMap (·.2)).flatMap Bound.uses := by
        simp [List.flatMap_append]
      rw [hfl] at hn₁ hn₂
      rw [hfu] at hv₁ hv₂
      simp only [List.map_append] at hn₁ hn₂
      obtain ⟨d₂, hstep₂, hmem', hdefs, hfr₁, hfr₂⟩ := part_corr (val := val) hshape hstack hwide
        (fun b hb => (hass ap List.mem_cons_self b hb).1) (fun b hb => (hass ap List.mem_cons_self b hb).2)
        hargs₁ hargs₂ hmem hctx (fun q hq => hv₁ q (List.mem_append_left _ hq))
        (fun q hq => hv₂ q (List.mem_append_left _ hq)) (fun b hb => hz₁ b (hmemb b hb))
        (fun b hb => hz₂ b (hmemb b hb)) (List.nodup_append.1 hn₁).1 (List.nodup_append.1 hn₂).1
        (by simpa [rowStep] using hstep)
      cases rest with
      | nil =>
        simp only [List.map_nil, List.mapM_nil, pure, Option.some.injEq] at hms₁ hms₂
        subst hms₁ hms₂
        simp only [List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        refine ⟨d₂, by simp [rowStep, hstep₂], hmem', ?_⟩
        intro q hq
        exact hdefs q (by simpa using hq)
      | cons ap' rest' =>
        have hnodef : ap.2.flatMap Bound.defs = [] := hlast ap (by simp)
        have hr₁ : ∀ r, d₁.readReg r = c₁.readReg r := fun r => hfr₁ r (by simp [hnodef])
        have hr₂ : ∀ r, d₂.readReg r = c₂.readReg r := fun r => hfr₂ r (by simp [hnodef])
        obtain ⟨c₂', hrun₂, hmem'', hdefs'⟩ := rows_corr (val := val) (g := g) hms₁ hms₂
          (fun a ha => hsh a (List.mem_cons_of_mem _ ha))
          (fun a ha => hass a (List.mem_cons_of_mem _ ha))
          (fun a ha => hlast a (by
            simp only [List.dropLast_cons₂] at ha ⊢
            exact List.mem_cons_of_mem _ ha))
          hmem' (by rw [hr₁, hr₂, hctx])
          (fun q hq => by rw [hr₁]; exact hv₁ q (List.mem_append_right _ hq))
          (fun q hq => by rw [hr₂]; exact hv₂ q (List.mem_append_right _ hq))
          (fun b hb hn q hq => by rw [hr₁]; exact hz₁ b (hmemr b hb) hn q hq)
          (fun b hb hn q hq => by rw [hr₂]; exact hz₂ b (hmemr b hb) hn q hq)
          (List.nodup_append.1 hn₁).2.1 (List.nodup_append.1 hn₂).2.1 hrest
        refine ⟨c₂', ?_, hmem'', ?_⟩
        · simp only [List.foldlM_cons, Option.bind_eq_bind]
          rw [show rowStep (c₂, fl) (ap.1, args₂) = some (d₂, fl₁) from hstep₂]
          exact hrun₂
        · intro q hq
          rw [hfl, hnodef, List.nil_append] at hq
          exact hdefs' q hq

/-! ## Xv's definition registers are distinct -/

/-- The definition registers of a slot bound. -/
def Bound.slotDefRegs : Bound (α × GPR) → List GPR
  | .output _ x => [x.2]
  | .tied _ _ x => [x.2]
  | _ => []

/-- The definition registers of an implicit bound. -/
def Bound.fixedDefRegs : Bound (α × GPR) → List GPR
  | .fixedDef _ x => [x.2]
  | .fixedTied _ _ x => [x.2]
  | _ => []

theorem Bound.defs_regs (b : Bound (α × GPR)) : b.defs.map (·.2) = b.slotDefRegs ++ b.fixedDefRegs := by
  cases b <;> rfl

theorem Bound.slotDefRegs_sublist {b : Bound (α × GPR)} (ha : b.Assigned) : b.slotDefRegs.Sublist b.taken := by
  cases b with
  | tied s a x => simp only [Bound.Assigned] at ha; simp [Bound.slotDefRegs, Bound.taken, ha]
  | output s x => simp [Bound.slotDefRegs, Bound.taken]
  | _ => simp [Bound.slotDefRegs]

theorem Bound.fixedDefRegs_fixed {b : Bound (α × GPR)} (ha : b.Assigned) {r : GPR}
    (hr : r ∈ b.fixedDefRegs) : ∃ i, b.fixed? = some i ∧ r = i := by
  cases b <;> simp_all [Bound.fixedDefRegs, Bound.Assigned, Bound.fixed?]

theorem Bound.fixedDefRegs_eq {g : α → GPR} {b : Bound (α × GPR)} (ha : b.Assigned)
    (ha' : (b.reassign g).Assigned) : b.fixedDefRegs = (b.reassign g).fixedDefRegs := by
  cases b <;> simp_all [Bound.fixedDefRegs, Bound.Assigned, Bound.reassign, Bound.map]

theorem nodup_flatMap_split {β : Type} {P S F : β → List GPR} (hP : ∀ b, P b = S b ++ F b) :
    ∀ {bs : List β}, (bs.flatMap S).Nodup → (bs.flatMap F).Nodup →
      (∀ b ∈ bs, ∀ r ∈ S b, ∀ b' ∈ bs, ∀ r' ∈ F b', r ≠ r') → (bs.flatMap P).Nodup
  | [], _, _, _ => by simp
  | b :: bs, hs, hf, hd => by
      simp only [List.flatMap_cons, List.nodup_append] at hs hf ⊢
      rw [hP b]
      refine ⟨?_, nodup_flatMap_split hP hs.2.1 hf.2.1 (fun b₁ h₁ r h b₂ h₂ r' h' =>
        hd b₁ (List.mem_cons_of_mem _ h₁) r h b₂ (List.mem_cons_of_mem _ h₂) r' h'), ?_⟩
      · rw [List.nodup_append]
        exact ⟨hs.1, hf.1, fun r h r' h' => hd b List.mem_cons_self r h b List.mem_cons_self r' h'⟩
      · intro r hr r' hr'
        obtain ⟨b', hb', hr'⟩ := List.mem_flatMap.1 hr'
        rw [hP b'] at hr'
        rcases List.mem_append.1 hr with hr | hr <;> rcases List.mem_append.1 hr' with hr' | hr'
        · exact hs.2.2 r hr r' (List.mem_flatMap.2 ⟨b', hb', hr'⟩)
        · exact hd b List.mem_cons_self r hr b' (List.mem_cons_of_mem _ hb') r' hr'
        · exact fun e => hd b' (List.mem_cons_of_mem _ hb') r' hr' b List.mem_cons_self r hr e.symm
        · exact hf.2.2 r hr r' (List.mem_flatMap.2 ⟨b', hb', hr'⟩)

theorem flatMap_congr' {β γ : Type} {f g : β → List γ} :
    ∀ {l : List β}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
      simp only [List.flatMap_cons]
      rw [h x List.mem_cons_self, flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem flatMap_sublist_flatMap {β γ : Type} {f g : β → List γ} :
    ∀ {l : List β}, (∀ x ∈ l, (f x).Sublist (g x)) → (l.flatMap f).Sublist (l.flatMap g)
  | [], _ => by simp
  | x :: l, h => by
      simp only [List.flatMap_cons]
      exact (h x List.mem_cons_self).append (flatMap_sublist_flatMap fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Xv's definition registers are distinct: slot definitions sit in distinct
scratch registers, implicit ones in their fixed registers, which are the
Xl definitions' there and distinct from every scratch register. -/
theorem defRegs_nodup {g : α → GPR} {bs : List (Bound (α × GPR))}
    (ha : ∀ b ∈ bs, b.Assigned) (ha' : ∀ b ∈ bs, (b.reassign g).Assigned)
    (htk : (bs.flatMap Bound.taken).Nodup)
    (hfix : ∀ b ∈ bs, ∀ r ∈ b.taken, ∀ b' ∈ bs, ∀ i, b'.fixed? = some i → r ≠ i)
    (hn₂ : ((bs.flatMap Bound.defs).map fun q => g q.1).Nodup) :
    ((bs.flatMap Bound.defs).map (·.2)).Nodup := by
  rw [List.map_flatMap]
  refine nodup_flatMap_split Bound.defs_regs ?_ ?_ ?_
  · exact (flatMap_sublist_flatMap fun b hb => Bound.slotDefRegs_sublist (ha b hb)).nodup htk
  · rw [flatMap_congr' fun b hb => Bound.fixedDefRegs_eq (ha b hb) (ha' b hb)]
    have hs : (bs.flatMap fun b => (b.reassign g).fixedDefRegs).Sublist
        ((bs.flatMap Bound.defs).map fun q => g q.1) := by
      rw [List.map_flatMap]
      refine flatMap_sublist_flatMap fun b _ => ?_
      have : (b.reassign g).defs.map (·.2) = b.defs.map fun q => g q.1 := by
        simp [Function.comp_def]
      rw [← this, Bound.defs_regs]
      exact List.sublist_append_right _ _
    exact hs.nodup hn₂
  · intro b hb r hr b' hb' r' hr'
    obtain ⟨i, hi, hri⟩ := Bound.fixedDefRegs_fixed (ha b' hb') hr'
    exact fun e => hfix b hb r ((Bound.slotDefRegs_sublist (ha b hb)).subset hr) b' hb' i hi (e.trans hri)

end Compilatrix.Xv
