import IxCC.X86.Exe.Machine.Proof.Start

/-!
# The shell theorem (X0-P)

`shell_sound`: for a machine executable `Machine.writeChecked` made, whose
object's first root is the step (two parameters, a `Nat` result), run from the
loader's post-state (`Process.Loaded`) with arguments `args` under the
platform's system calls (`Process.Syscall`) and processor (`Process.Step`),
every finite trace of the process is one `Process.Shows` allows for the
object's calls: a prefix of the system calls of a trace the session model
performs over the object's calls (`cx_init` and the step, each from its own
call site, each keeping the driver contract), preceded by the confinement; or
past the system calls of a trace reaching a call the model shows stuck; or the
confinement's refusal.

It is `start` followed by `from_loop`. Safety only: nothing here says that a
trace goes on.

`shell_unspecified` is a corollary of the statement: where `Process.Step`
promises nothing (`Unspecified`: bytes the decoder does not decode that are
not a `syscall`, `rip` outside the file, or a condition on an undefined flag),
the process may go on with any system call, and `Shows` allows a system call
the shell never makes only past a call the model shows stuck. So the process
reaches such a state, if at all, only after such a call.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Exe.Machine (Config Reaches objCallAtOf)

/-- **The shell realises the session model** (see the module note). -/
theorem shell_sound {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)
    {roots : List Linked.Root} {sig : Rt.Sig}
    (hroot : roots[0]? = some { symbol := step, params := 2, ty := some (sig, .nat) })
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State}
    (hload : Loaded ce.checked args s₀) {σ : List Sys} (hσ : Trace ce.checked.bytes s₀ σ) :
    Shows (objCallAtOf (linkedOf object roots)
        ce.checked.plan.placement.textSize)
      (fileBase + ce.checked.plan.placement.dataOffset) args σ := by
  rcases start ce hargs hload hσ with h | h | ⟨s, σ', hat, ht, rfl⟩
  · exact .inr (.inr h)
  · exact .inl ⟨[], [], .inl ⟨_, .refl _⟩, .nil, by rw [List.append_nil]; exact h⟩
  · rcases from_loop ce hroot hat ht with ⟨t, ρ, hp, hd, hpre⟩ | ⟨t₀, c', ρ₀, hr, hs, hd, hpre⟩
    · exact .inl ⟨t, ρ, hp, hd, (List.prefix_append_right_inj _).mpr hpre⟩
    · exact .inr (.inl ⟨t₀, c', ρ₀, hr, hs, hd, (List.prefix_append_right_inj _).mpr hpre⟩)

/-- **The process reaches a state where `Process.Step` promises nothing only
past a call the model shows stuck**: if the process runs from the loader's
post-state, making the system calls `σ`, to a state `Unspecified` covers, then
`σ` has passed the system calls of a trace reaching a call the session model
shows stuck. A corollary of `shell_sound` (see the module note). -/
theorem shell_unspecified {L : Machine.Layout} {step : String} {object : ByteArray}
    (ce : Machine.Certified L step object) {roots : List Linked.Root} {sig : Rt.Sig}
    (hroot : roots[0]? = some { symbol := step, params := 2, ty := some (sig, .nat) })
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State}
    (hload : Loaded ce.checked args s₀) {σ : List Sys} {s : ByteEval.State}
    (hr : Run ce.checked.bytes s₀ σ s) (hu : Unspecified ce.checked.bytes s) :
    ∃ t₀ c' ρ₀, Reaches (objCallAtOf (linkedOf object roots) ce.checked.plan.placement.textSize)
        (Config.initial args) t₀ c' ∧
      objCallAtOf (linkedOf object roots) ce.checked.plan.placement.textSize c'.state c'.event .stuck ∧
      DenotesAll t₀ ρ₀ ∧ started (fileBase + ce.checked.plan.placement.dataOffset) ++ ρ₀ <+: σ :=
  Shows.stuck_of_other (shell_sound ce hroot hargs hload (Run.other_of_unspecified hr hu 0))

end IxCC.X86.Exe.Process
