import IxCC.Backend.Proof.Xl

/-!
# Selection and allocation for any entry function

The Lir, Xv and Xl programs name the function their runs start at (`main`);
selection (`Select.select`), the allocation check (`Validate.program`) and
its application (`Alloc.applyProgram`) work function by function and copy
`main`. So the programs that start at another function `g`,
`{ p with main := g }`, are selected and allocated to the same programs
started at `g`:

- `select_withMain`, `validate_withMain`: the passes commute with the
  choice of entry function;
- `xl_sim_select`: Lir to Xl for the recheck path's selection
  (`Select.select`, which `Select.correct` is stated of) and the validated
  allocation, with the identity clock map and equal values.
-/

namespace IxCC.Backend

open IxCC.Xv
open IxCC.Lir (Word)

/-- Selection does not read the entry function. -/
theorem select_withMain {p : Lir.Program} {q : VProgram} (h : Select.select p = .ok q) (g : Lir.FunId) :
    Select.select { p with main := g } = .ok { q with main := g } := by
  unfold Select.select at h ⊢
  cases hr : (Select.selectFuncs false p.funcs.toList.zipIdx).run ∅ with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨fs, fired⟩ := r
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl

/-- The allocation's application does not read the entry function. -/
theorem applyProgram_withMain {q : VProgram} {outs : List Alloc.Output} {l : LProgram}
    (h : Alloc.applyProgram q outs = .ok l) (g : Lir.FunId) :
    Alloc.applyProgram { q with main := g } outs = .ok { l with main := g } := by
  unfold Alloc.applyProgram at h ⊢
  cases hr : Alloc.applyProgram.go q.funcs.toList outs 0 with
  | error e => simp [hr, bind, Except.bind] at h
  | ok fs =>
    simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl

/-- The validated allocation does not read the entry function. -/
theorem validate_withMain {env : Xl.Env} {q : VProgram} {outs : List Alloc.Output} {l : LProgram}
    (h : Validate.run env q outs = .ok l) (g : Lir.FunId) :
    Validate.run env { q with main := g } outs = .ok { l with main := g } := by
  unfold Validate.run at h ⊢
  have hp : Validate.program env { q with main := g } outs = Validate.program env q outs := rfl
  rw [hp]
  split at h
  · cases h
  · exact applyProgram_withMain h g

variable {p : Lir.Program} {q : VProgram} {env : Xl.Env} {outs : List Alloc.Output} {l : LProgram}

/-- Lir to Xl on the recheck path: `Select.select`, then the validated
allocation, in lock step with the identity clock map and equal values. -/
theorem xl_sim_select (hs : Select.select p = .ok q) (hv : Validate.run env q outs = .ok l)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id (fun k => Lir.eval p k args mem ctx) (fun k => Xl.eval l env k args mem ctx) :=
  ((Select.sim hs args mem ctx).comp (Xl.eval_mono l env args mem ctx)
    (Validate.program_sim hv args mem ctx)).mono fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂

end IxCC.Backend
