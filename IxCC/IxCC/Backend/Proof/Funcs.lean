import IxCC.Backend.Proof.Retarget

/-!
# Selection and allocation keep each function's interface

Selection (`Select.select`) and the validated allocation (`Validate.run`)
keep every function's calling convention and parameter count, so a SysV
export of Lir is one of Xl, of the same symbol and arity: what stacking
emits a wrapper for (`select_func`, `validate_func`, `xl_func`).
-/

namespace IxCC.Backend

open IxCC.Xv
open IxCC.Xv.Select.Proof (tbind_ok)

theorem selectFunc_conv {stats : Bool} {fn : Lir.FunId} {f : Lir.Func}
    {fired fired' : Std.TreeMap String Nat compare} {xf : Func Lir.VReg}
    (h : Select.selectFunc stats fn f fired = .ok (xf, fired')) : xf.conv = f.conv := by
  unfold Select.selectFunc at h
  rw [tbind_ok] at h
  obtain ⟨d, s₁, h₀, h⟩ := h
  simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h₀
  obtain ⟨rfl, rfl⟩ := h₀
  rw [tbind_ok] at h
  obtain ⟨⟨sel, st⟩, s₂, h₁, h⟩ := h
  cases hr : (Select.selectBlocks fn (Select.useCounts f) f.blocks.toList.zipIdx).run
      { next := Select.maxVReg f + 1, fired := fired, stats := stats } with
  | error e =>
    rw [hr] at h₁
    cases h₁
  | ok p =>
    rw [hr] at h₁
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simp only at h
    cases hf : List.find? (fun x => match x with | (b, _) => !Block.avoids (List.flatMap (fun x => x.snd) sel) b)
        (List.map (fun x => x.fst) sel).zipIdx with
    | some p =>
      obtain ⟨b, l⟩ := p
      rw [hf] at h
      simp only [throw, throwThe, MonadExceptOf.throw, bind, StateT.bind, Except.bind] at h
      cases h
    | none =>
      rw [hf] at h
      simp only [set, MonadStateOf.set, StateT.set, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl

theorem selectFuncs_conv {stats : Bool} :
    ∀ {L : List (Lir.Func × Lir.FunId)} {fired fired' : Std.TreeMap String Nat compare} {fs : List (Func Lir.VReg)},
      Select.selectFuncs stats L fired = .ok (fs, fired') →
      ∀ (k : Nat) f fn, L[k]? = some (f, fn) → ∃ xf, fs[k]? = some xf ∧ xf.conv = f.conv
  | [], fired, fired', fs, h => by
      simp only [Select.selectFuncs, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun k f fn h => by simp at h
  | (f, fn) :: rest, fired, fired', fs, h => by
      simp only [Select.selectFuncs] at h
      rw [tbind_ok] at h
      obtain ⟨xf, s₁, h₁, h⟩ := h
      rw [tbind_ok] at h
      obtain ⟨fs', s₂, h₂, h⟩ := h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro k f' fn' hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨xf, rfl, selectFunc_conv h₁⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨xf', hs, hc⟩ := selectFuncs_conv h₂ k f' fn' hk
        exact ⟨xf', by simpa using hs, hc⟩

/-- Selection keeps each function's convention and parameters. -/
theorem select_func {p : Lir.Program} {q : VProgram} (h : Select.select p = .ok q) {g : Lir.FunId} {f : Lir.Func}
    (hf : p.funcs[g]? = some f) : ∃ vf, q.funcs[g]? = some vf ∧ vf.conv = f.conv ∧ vf.params = f.params := by
  obtain ⟨vf, D, hvf, hsel⟩ := (Select.Proof.select_spec h).func g f hf
  refine ⟨vf, hvf, ?_, hsel.params⟩
  unfold Select.select at h
  cases hr : (Select.selectFuncs false p.funcs.toList.zipIdx).run ∅ with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨fs, fired⟩ := r
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hk : p.funcs.toList.zipIdx[g]? = some (f, g) := by
      rw [List.getElem?_zipIdx, Array.getElem?_toList, hf]; simp
    obtain ⟨xf, hxf, hc⟩ := selectFuncs_conv hr g f g hk
    have : xf = vf := by
      simp only [List.getElem?_toArray] at hvf
      rw [hxf] at hvf
      exact Option.some.inj hvf
    rw [← this]
    exact hc

/-- An allocation applied keeps the convention and the parameter count. -/
theorem apply_func {f : Func Lir.VReg} {o : Alloc.Output} {g : Func Loc} (h : Alloc.apply f o = .ok g) :
    g.conv = f.conv ∧ g.params.length = f.params.length := by
  unfold Alloc.apply at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp

/-- The validated allocation keeps each function's convention and parameter
count. -/
theorem validate_func {env : Xl.Env} {q : VProgram} {outs : List Alloc.Output} {l : LProgram}
    (h : Validate.run env q outs = .ok l) {g : Lir.FunId} {vf : Func Lir.VReg} (hf : q.funcs[g]? = some vf) :
    ∃ xf, l.funcs[g]? = some xf ∧ xf.conv = vf.conv ∧ xf.params.length = vf.params.length := by
  obtain ⟨o, xf, -, hxf, -, happ⟩ := (Validate.accepted_of_run h).funcs g vf hf
  exact ⟨xf, hxf, apply_func happ⟩

/-- **Lir's functions reach Xl with their interface.** -/
theorem xl_func {p : Lir.Program} {q : VProgram} {env : Xl.Env} {outs : List Alloc.Output} {l : LProgram}
    (hs : Select.select p = .ok q) (hv : Validate.run env q outs = .ok l) {g : Lir.FunId} {f : Lir.Func}
    (hf : p.funcs[g]? = some f) : ∃ xf, l.funcs[g]? = some xf ∧ xf.conv = f.conv ∧ xf.params.length = f.params.length := by
  obtain ⟨vf, hvf, hc, hp⟩ := select_func hs hf
  obtain ⟨xf, hxf, hc', hp'⟩ := validate_func hv hvf
  exact ⟨xf, hxf, hc'.trans hc, hp'.trans (by rw [hp])⟩

end IxCC.Backend
