import IxCC.Xv.Stacking.Proof.WrapperEntry
import IxCC.Xv.Validate.Proof.Fuel

/-!
# Stacking is correct

`stacked_ends`: under the entry invariant, the stacked program's checked
run from its first instruction (`main`'s export wrapper) ends as `main`'s
clocked Xl run does (`Outcome`, the shape of `ObjectEval.Ends` with
`ReadableData` at every exit's stack pointer): a failed stack check exits
with status 2 at any clock; otherwise a result exits with status 0 and
`Final`, a timeout at clock `k` is a running machine after at least `k`
checked steps, and a resource failure or a trap exits with its status. -/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- **Stacking and the wrapper simulate Xl** (the backend's conclusion at the
stacked level). -/
theorem stacked_ends (S : Stk) {core₀ : Core} {retAddr ctx : Word} {args : List Word} {mem : Memory}
    (inv : EntryInv S.p S.reps core₀ retAddr args mem ctx) (k : Nat)
    (hk : Xl.eval S.p S.env k args mem ctx ≠ .stuck) :
    ∃ n holes after, SafeSteps Runtime.rejecting S.cs n (fun _ => False) (Machine.initial S.cs core₀) holes after ∧
      Outcome core₀ retAddr k n holes after (Xl.eval S.p S.env k args mem ctx) := by
  cases hs : Xl.State.initial S.p args mem ctx with
  | none => exact absurd (by simp [Xl.eval, hs]) hk
  | some s₀ =>
    have hrun := Xl.runs_eval (env := S.env) hs k
    rcases wrapper_entry inv hs with ⟨n, holes, after, hst, hexit, hdata⟩ |
        ⟨W, n, holes, m, fr, a, ret, hW₀, hWr, hwc, hst, hm⟩
    · exact ⟨n, holes, after, hst, .inl ⟨0, hexit, hdata⟩⟩
    · obtain ⟨n', holes', after, hst', hout⟩ := sim hwc hrun hm
      rw [hW₀, hWr] at hout
      exact ⟨n + n', holes', after, hst.append hst', hout.mono (by omega)⟩

/-- The same, for a program `run` stacked. -/
theorem run_ends {p : LProgram} {layouts : List FrameLayout} {reps : Lir.FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) (valid : st.program.wellFormed = true)
    {core₀ : Core} {retAddr ctx : Word} {args : List Word} {mem : Memory}
    (inv : EntryInv p reps core₀ retAddr args mem ctx) (k : Nat) (hk : Xl.eval p env k args mem ctx ≠ .stuck) :
    ∃ n holes after, SafeSteps Runtime.rejecting ⟨st.program, valid⟩ n (fun _ => False)
        (Machine.initial ⟨st.program, valid⟩ core₀) holes after ∧
      Outcome core₀ retAddr k n holes after (Xl.eval p env k args mem ctx) :=
  stacked_ends ⟨p, layouts, reps, env, st, h⟩ inv k hk

end IxCC.Xv.Stacking.Proof
