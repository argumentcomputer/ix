import IxCC.Lir.Proof.Run
import IxCC.X86.StreamMemory

/-!
# Lir runs keep memory permissions

A Lir step changes memory only by a store (`Memory.write?`), which writes
bytes and keeps which bytes are readable and writable. So a run's final
memory has its initial memory's permissions (`eval_perms`): the region a
program may read and write is fixed by its caller.
-/

namespace IxCC.Lir

/-- Two memories with the same permissions. -/
def SamePerms (m m' : X86.Memory) : Prop := m'.readable = m.readable ∧ m'.writable = m.writable

theorem SamePerms.refl (m : X86.Memory) : SamePerms m m := ⟨rfl, rfl⟩

theorem SamePerms.trans {a b c : X86.Memory} (h₁ : SamePerms a b) (h₂ : SamePerms b c) : SamePerms a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem write?_perms {m m' : X86.Memory} {w : X86.Width} {a v : Word} (h : m.write? w a v = .ok m') :
    SamePerms m m' := by
  unfold X86.Memory.write? at h
  split at h
  · cases h
    exact ⟨X86.Stream.writeLittle_readable _ _ _ _, X86.Stream.writeLittle_writable _ _ _ _⟩
  · cases h

theorem Stmt.exec_perms {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word} {st : Stmt}
    (h : st.exec ρ mem ctx = some (ρ', mem')) : SamePerms mem mem' := by
  cases st with
  | assign x r =>
    simp only [Stmt.exec, bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    exact .refl _
  | store w m a =>
    simp only [Stmt.exec, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    split at h
    · rename_i hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact write?_perms hw
    · cases h
  | call => simp [Stmt.exec] at h

theorem takeEdge_perms {f : Func} {s s' : State} {fr : Frame} {rest : List Frame} {ρ : Env}
    {e : Edge} {c : Bool} (h : takeEdge f s fr rest ρ e = .next s' c) : s'.mem = s.mem := by
  obtain ⟨-, -, -, rfl, -⟩ := takeEdge_next h
  rfl

theorem takeEdge_not_done {f : Func} {s : State} {fr : Frame} {rest : List Frame} {ρ : Env}
    {e : Edge} {vals : List Word} {mem : X86.Memory} : takeEdge f s fr rest ρ e ≠ .done vals mem := by
  unfold takeEdge
  split
  · split <;> simp
  · simp

/-- A step keeps the permissions: to the next state, or to a returned
memory. -/
theorem step_perms {p : Program} {s : State} :
    (∀ {s' c}, step p s = .next s' c → SamePerms s.mem s'.mem) ∧
      (∀ {vals mem}, step p s = .done vals mem → SamePerms s.mem mem) := by
  unfold step
  cases hst : s.stack with
  | nil => simp
  | cons fr rest =>
  simp only
  cases hf : p.funcs[fr.fn]? with
  | none => simp
  | some f =>
  simp only
  cases hb : f.blocks[fr.label]? with
  | none => simp
  | some blk =>
  simp only
  by_cases hpos : fr.pos < blk.body.size
  · simp only [hpos, ↓reduceDIte]
    split
    · split
      · refine ⟨fun h => ?_, fun h => by simp at h⟩
        simp only [Step.next.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact .refl _
      · simp
    · split
      · rename_i ρ mem' hex
        refine ⟨fun h => ?_, fun h => by simp at h⟩
        simp only [Step.next.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Stmt.exec_perms hex
      · simp
  · simp only [hpos, ↓reduceDIte]
    cases hT : blk.term with
    | jump e =>
      exact ⟨fun h => by rw [takeEdge_perms h]; exact .refl _, fun h => absurd h takeEdge_not_done⟩
    | br c' w a b' t e =>
      simp only
      split
      · exact ⟨fun h => by rw [takeEdge_perms h]; exact .refl _, fun h => absurd h takeEdge_not_done⟩
      · simp
    | brOvf o x a b' ok ovf =>
      simp only
      split
      · exact ⟨fun h => by rw [takeEdge_perms h]; exact .refl _, fun h => absurd h takeEdge_not_done⟩
      · simp
    | ret as =>
      simp only
      split
      · simp
      · split
        · refine ⟨fun h => by simp at h, fun h => ?_⟩
          simp only [Step.done.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact .refl _
        · split
          · refine ⟨fun h => ?_, fun h => by simp at h⟩
            simp only [Step.next.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact .refl _
          · simp
    | tail g as =>
      simp only
      split
      · refine ⟨fun h => ?_, fun h => by simp at h⟩
        simp only [Step.next.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact .refl _
      · simp
    | fail r => simp
    | trap => simp

theorem run_perms (p : Program) :
    ∀ (fuel k : Nat) (s : State) {vals : List Word} {mem : X86.Memory},
      run p fuel k s = .ok (vals, mem) → SamePerms s.mem mem
  | 0, _, _, _, _, h => by simp [run] at h
  | fuel + 1, k, s, vals, mem, h => by
    unfold run at h
    cases hs : step p s with
    | next s' c =>
      rw [hs] at h
      have h₁ := step_perms.1 hs
      cases c with
      | false => exact h₁.trans (run_perms p fuel k s' h)
      | true =>
        cases k with
        | zero => simp at h
        | succ k => exact h₁.trans (run_perms p fuel k s' h)
    | done vals' mem' =>
      rw [hs] at h
      simp only [Sem.Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact step_perms.2 hs
    | fail r => rw [hs] at h; cases h
    | trap => rw [hs] at h; cases h
    | stuck => rw [hs] at h; cases h

/-- **A Lir run keeps the permissions of its memory.** -/
theorem eval_perms {p : Program} {k : Nat} {args : List Word} {mem mem' : X86.Memory} {ctx : Word}
    {vals : List Word} (h : eval p k args mem ctx = .ok (vals, mem')) : SamePerms mem mem' := by
  unfold eval at h
  split at h
  · rename_i s hs
    have := run_perms p _ k s h
    simp only [State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
    obtain ⟨_, -, rfl⟩ := hs
    exact this
  · cases h

end IxCC.Lir
