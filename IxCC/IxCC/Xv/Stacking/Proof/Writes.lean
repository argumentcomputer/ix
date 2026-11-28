import IxCC.Xv.Stacking.Proof.Chain

/-!
# What a function may change

Every register an instruction or terminator of a function defines is among
the function's written registers (`Func.facts`), so it is saved or among
what the function may change (`mayChange`), which `run` checked against
what its callers allow (`allowedChanges`): `def_allowed`.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

theorem foldl_keeps {α β : Type} (P : α → Prop) (g : α → β → α) (hmono : ∀ a y, P a → P (g a y)) :
    ∀ (xs : List β) (a : α), P a → P (xs.foldl g a)
  | [], _, h => h
  | x :: xs, a, h => foldl_keeps P g hmono xs (g a x) (hmono a x h)

theorem foldl_gets {α β : Type} (P : α → Prop) (g : α → β → α) (hmono : ∀ a y, P a → P (g a y)) {x : β}
    (hx : ∀ a, P (g a x)) : ∀ (xs : List β) (a : α), x ∈ xs → P (xs.foldl g a)
  | [], _, h => by simp at h
  | y :: xs, a, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact foldl_keeps P g hmono xs _ (hx a)
      · exact foldl_gets P g hmono hx xs (g a y) h

section
variable {r : X86.GPR}

theorem noteLoc_writes (a : Facts) (l : Loc) : (a.noteLoc l).writes = a.writes := by
  cases l <;> rfl

theorem noteDef_mono (a : Facts) (l : Loc) (h : r ∈ a.writes) : r ∈ (a.noteDef l).writes := by
  cases l with
  | reg q =>
    simp only [Facts.noteDef]
    split
    · exact h
    · exact List.mem_append_left _ h
  | _ => simpa [Facts.noteDef, noteLoc_writes] using h

theorem noteDef_reg (a : Facts) : r ∈ (a.noteDef (.reg r)).writes := by
  simp only [Facts.noteDef]
  split
  · rename_i hc; exact List.contains_iff_mem.1 hc
  · simp

theorem foldl_noteLoc_writes : ∀ (ls : List Loc) (a : Facts), (ls.foldl Facts.noteLoc a).writes = a.writes
  | [], _ => rfl
  | l :: ls, a => by rw [List.foldl_cons, foldl_noteLoc_writes ls, noteLoc_writes]

theorem inst_mono (a : Facts) (i : Inst Loc) (h : r ∈ a.writes) : r ∈ (a.inst i).writes := by
  have h₁ : r ∈ (i.uses.foldl Facts.noteLoc a).writes := by rw [foldl_noteLoc_writes]; exact h
  have h₂ := foldl_keeps (fun a : Facts => r ∈ a.writes) Facts.noteDef (fun a l h => noteDef_mono a l h) i.defs _ h₁
  unfold Facts.inst
  cases i <;> exact h₂

theorem inst_def (a : Facts) {i : Inst Loc} (hr : Loc.reg r ∈ i.defs) : r ∈ (a.inst i).writes := by
  have h₂ := foldl_gets (fun a : Facts => r ∈ a.writes) Facts.noteDef (fun a l h => noteDef_mono a l h)
    (fun a => noteDef_reg a) i.defs (i.uses.foldl Facts.noteLoc a) hr
  unfold Facts.inst
  cases i <;> exact h₂

theorem term_mono (a : Facts) (t : Term Loc) (h : r ∈ a.writes) : r ∈ (a.term t).writes := by
  unfold Facts.term
  refine foldl_keeps (fun a : Facts => r ∈ a.writes) Facts.noteDef (fun a l h => noteDef_mono a l h) _ _ ?_
  rw [foldl_noteLoc_writes]; exact h

theorem term_def (a : Facts) {t : Term Loc} (hr : Loc.reg r ∈ t.defs) : r ∈ (a.term t).writes := by
  unfold Facts.term
  exact foldl_gets (fun a : Facts => r ∈ a.writes) Facts.noteDef (fun a l h => noteDef_mono a l h)
    (fun a => noteDef_reg a) _ _ hr

theorem block_mono (a : Facts) (b : Block Loc) (h : r ∈ a.writes) : r ∈ (a.block b).writes := by
  unfold Facts.block
  refine term_mono _ _ (foldl_keeps (fun a : Facts => r ∈ a.writes) Facts.inst (fun a i h => inst_mono a i h) _ _ ?_)
  exact foldl_keeps (fun a : Facts => r ∈ a.writes) Facts.noteDef (fun a l h => noteDef_mono a l h) _ _ h

/-- A register an instruction defines is among its function's writes. -/
theorem facts_inst {f : Func Loc} {b : Block Loc} (hb : b ∈ f.blocks.toList) {i : Inst Loc}
    (hi : i ∈ b.body.toList) (hr : Loc.reg r ∈ i.defs) : r ∈ f.facts.writes := by
  unfold Func.facts
  refine foldl_gets (fun a : Facts => r ∈ a.writes) Facts.block (fun a b h => block_mono a b h) (fun a => ?_) _ _ hb
  unfold Facts.block
  refine term_mono _ _ (foldl_gets (fun a : Facts => r ∈ a.writes) Facts.inst (fun a i h => inst_mono a i h)
    (fun a => inst_def a hr) _ _ hi)

/-- A register a terminator defines is among its function's writes. -/
theorem facts_term {f : Func Loc} {b : Block Loc} (hb : b ∈ f.blocks.toList) (hr : Loc.reg r ∈ b.term.defs) :
    r ∈ f.facts.writes := by
  unfold Func.facts
  refine foldl_gets (fun a : Facts => r ∈ a.writes) Facts.block (fun a b h => block_mono a b h) (fun a => ?_) _ _ hb
  unfold Facts.block
  exact term_def _ hr

end

/-- A register a function writes is saved, or its callers allow it. -/
theorem write_allowed {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) {r : X86.GPR} (hw : r ∈ f.facts.writes) :
    r ∈ l.saved ∨ r ∈ allowedChanges S.env k f := by
  by_cases hs : r ∈ l.saved
  · exact .inl hs
  · right
    have hx := hf.checks.2.1
    have hm : r ∈ mayChange S.env f f.facts l := by
      simp only [mayChange, List.mem_append, List.mem_filter]
      left; left
      exact ⟨hw, by simpa using hs⟩
    simp only [extraChanges, List.append_eq_nil_iff, List.filter_eq_nil_iff] at hx
    have := hx.1 r (List.mem_append_left _ hm)
    simpa using this

end IxCC.Xv.Stacking.Proof
