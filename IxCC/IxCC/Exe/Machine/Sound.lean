import IxCC.Exe
import IxCC.Exe.Machine
import IxCC.Recheck.Proof.Soundness
import IxCC.Recheck.Rc.Proof.ObjectSound

/-!
# The session theorem of numeric state machines

Over the linked-object model, by induction over the session
(`Performs.refines`, `IxCC/Exe/Machine.lean`) from the per-call theorems:
`Recheck.sound` for immortal and zero-RC objects, `RcReplay.sound` for plain RC.

**The calls.** The object's (`objCallOf`): the linked object run on its first
root and `[s, e]` under *any* driver that keeps the contract (`Driver.Ok`; so
whatever the bytes the call starts from, which is how each call of a session
sees the memory the previous one left) and at any clock. The source's
(`srcCallOf`): SrcEval of the step on `[s, e]` at some clock, viewed at the
root's readback type.

**The theorem** (`session_sound`, `Rc.session_sound`): for a machine root
whose declared parameter count is two (`MachineRoot`; it makes every call one
the per-call theorems cover), every finite trace the object's session
performs from any configuration is one the source step's iteration performs
on the same answers; or it is such a prefix followed by a resource failure;
or the source step goes wrong at a call its own session reaches.
`machine_session_sound` is the same for every artifact `Exe.machine` accepts.

What it does not say: that a session which the source carries on is carried on
by the object (the progress direction); and that the executable's shell
realises this model (the ledger's `x86-linux-machine-shell`).
-/

set_option autoImplicit false

namespace IxCC.Exe.Machine

open IxCC.Sem (Result Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- The source's calls: SrcEval of root 0 on `[s, e]` at some clock, viewed
at the root's readback type. -/
def srcCallOf (src : Src.Program) (checked : Src.Relevance.Checked)
    (view : Nat → Option Obs → Option (Option Obs)) : Call := fun s e r =>
  ∃ k v o, Lang.run (⟨src, checked⟩ : CheckedProgram) (0, [s, e]) k = .ok v ∧
    view 0 (Lang.obs v) = some o ∧ r = .ok o

/-- The object's calls: the linked object run on root 0 and `[s, e]` under any
driver that keeps the contract, whatever its initial bytes, at any clock. -/
def objCallOf (linked : X86.Driver → X86.Linked) (textSize : Nat) : Call := fun s e r =>
  ∃ (D : X86.Driver) (k : Nat), D.Ok textSize ∧ Lang.run (linked D) (0, [s, e]) k = r

/-- A machine root: the first root's declared type has two parameters. -/
def MachineRoot (src : Src.Program) : Prop :=
  ∀ addr c, src.roots[0]? = some (addr, c) → Recheck.declaredParams src c = some 2

theorem MachineRoot.exact {src : Src.Program} (h : MachineRoot src) (s e : Nat) :
    Recheck.ExactDeclared src (0, [s, e]) := by
  intro addr c hr n hn
  rw [h addr c hr] at hn
  cases hn
  rfl

/-- The source's session is deterministic: one outcome per call. -/
theorem srcCallOf_functional {f : Recheck.Front} {s e : Nat} {r r' : Result (Option Obs)}
    (h : srcCallOf f.src f.checked f.view s e r) (h' : srcCallOf f.src f.checked f.view s e r') :
    r = r' := by
  obtain ⟨k, v, o, hv, ho, rfl⟩ := h
  obtain ⟨k', v', o', hv', ho', rfl⟩ := h'
  have := Recheck.Front.eval_unique (f := f) hv hv'
  subst this
  rw [ho] at ho'
  cases ho'
  rfl

section Immortal
variable {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {a : Recheck.Artifact}

/-- The calls of an immortal or zero-RC object. -/
def objCall (a : Recheck.Artifact) : Call := objCallOf a.linked a.backend.encoded.text.size
/-- The calls of its source. -/
def srcCall (a : Recheck.Artifact) : Call := srcCallOf a.src a.checked a.front.view

/-- `Recheck.sound`, per call of a machine root. -/
theorem callRefines (h : Recheck.run cfg P c = .ok a) (hroot : MachineRoot a.front.src) :
    CallRefines (objCall a) (srcCall a) (fun s e => a.front.GoesWrong (0, [s, e])) where
  ok := by
    intro s e o ho
    obtain ⟨D, k, hD, hr⟩ := ho
    have hcov : a.front.Covered c (0, [s, e]) := .inl (hroot.exact s e)
    rcases (Recheck.sound h D hD (0, [s, e]) hcov).1 k o hr with ⟨k', v, hv, hview⟩ | hb
    · exact .inl ⟨k', v, o, hv, hview, rfl⟩
    · exact .inr hb
  wrong := by
    intro s e r ho hw
    obtain ⟨D, k, hD, hr⟩ := ho
    have hcov : a.front.Covered c (0, [s, e]) := .inl (hroot.exact s e)
    refine Classical.byContradiction fun hs => ?_
    exact (Recheck.sound h D hD (0, [s, e]) hcov).2.1 hs k (hr ▸ hw)

/-- **The session theorem** (immortal and zero-RC objects): every finite trace
a machine's session performs over the linked object, with the environment's
answers, is one the source step's iteration performs on those answers; or it
is such a prefix followed by a resource failure; or the source step goes
wrong at a call the source's session reaches. -/
theorem session_sound (h : Recheck.run cfg P c = .ok a) (hroot : MachineRoot a.front.src)
    {c₀ : Config} {t : List Event} (ho : Performs (objCall a) c₀ t) :
    Performs (srcCall a) c₀ t ∨
    (∃ t₀ c' f b, t = t₀ ++ [.fail (statusOf f) b] ∧ Reaches (srcCall a) c₀ t₀ c') ∨
    ∃ t₀ c', Reaches (srcCall a) c₀ t₀ c' ∧ a.front.GoesWrong (0, [c'.state, c'.event]) :=
  Performs.refines (callRefines h hroot) ho

/-- What `Exe.machine` accepts is a machine root. -/
theorem machine_root {r : Recheck.Root} (hm : Exe.machine a = .ok r) : MachineRoot a.front.src := by
  have hd : Exe.declaredTwo a.src = true := by
    unfold Exe.machine at hm
    cases hr : a.roots.head? with
    | none => simp [hr] at hm <;> cases hm
    | some root =>
      simp only [hr] at hm
      by_cases hc : (root.params == 2 && CompileClaim.rootParamsAllNat a.src root && Exe.declaredTwo a.src) = true
      · simp only [Bool.and_eq_true] at hc
        exact hc.2
      · simp [hc] at hm <;> cases hm
  intro addr c' hr
  show Recheck.declaredParams a.src c' = some 2
  unfold Exe.declaredTwo at hd
  have hr' : a.src.roots[0]? = some (addr, c') := hr
  rw [hr'] at hd
  simpa using hd

/-- **The session theorem for a machine executable**: for every object
`Recheck.run` makes whose first root `Exe.machine` accepts (what `ixcc compile
--exe --machine` runs), from the process's first configuration on any
arguments. -/
theorem machine_session_sound (h : Recheck.run cfg P c = .ok a) {r : Recheck.Root}
    (hm : Exe.machine a = .ok r) (args : List (List Nat)) {t : List Event}
    (ho : Performs (objCall a) (Config.initial args) t) :
    Performs (srcCall a) (Config.initial args) t ∨
    (∃ t₀ c' f b, t = t₀ ++ [.fail (statusOf f) b] ∧ Reaches (srcCall a) (Config.initial args) t₀ c') ∨
    ∃ t₀ c', Reaches (srcCall a) (Config.initial args) t₀ c' ∧ a.front.GoesWrong (0, [c'.state, c'.event]) :=
  session_sound h (machine_root hm) ho

end Immortal

namespace Rc
variable {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
  {a : Recheck.RcReplay.Artifact}

/-- The calls of a plain-RC object. -/
def objCall (a : Recheck.RcReplay.Artifact) : Call := objCallOf a.linked a.backend.encoded.text.size
/-- The calls of its source. -/
def srcCall (a : Recheck.RcReplay.Artifact) : Call := srcCallOf a.front.src a.front.checked a.front.view

/-- `RcReplay.sound`, per call of a machine root. -/
theorem callRefines (h : Recheck.RcReplay.run cfg P c = .ok a) (hroot : MachineRoot a.front.src) :
    CallRefines (objCall a) (srcCall a) (fun s e => a.front.GoesWrong (0, [s, e])) where
  ok := by
    intro s e o ho
    obtain ⟨D, k, hD, hr⟩ := ho
    have hcov : a.front.Covered c (0, [s, e]) := .inl (hroot.exact s e)
    rcases (Recheck.RcReplay.sound h D hD (0, [s, e]) hcov).1 k o hr with ⟨k', v, hv, hview⟩ | hb
    · exact .inl ⟨k', v, o, hv, hview, rfl⟩
    · exact .inr hb
  wrong := by
    intro s e r ho hw
    obtain ⟨D, k, hD, hr⟩ := ho
    have hcov : a.front.Covered c (0, [s, e]) := .inl (hroot.exact s e)
    refine Classical.byContradiction fun hs => ?_
    exact (Recheck.RcReplay.sound h D hD (0, [s, e]) hcov).2.1 hs k (hr ▸ hw)

/-- **The session theorem** (plain-RC objects). -/
theorem session_sound (h : Recheck.RcReplay.run cfg P c = .ok a) (hroot : MachineRoot a.front.src)
    {c₀ : Config} {t : List Event} (ho : Performs (objCall a) c₀ t) :
    Performs (srcCall a) c₀ t ∨
    (∃ t₀ c' f b, t = t₀ ++ [.fail (statusOf f) b] ∧ Reaches (srcCall a) c₀ t₀ c') ∨
    ∃ t₀ c', Reaches (srcCall a) c₀ t₀ c' ∧ a.front.GoesWrong (0, [c'.state, c'.event]) :=
  Performs.refines (callRefines h hroot) ho

end Rc

end IxCC.Exe.Machine
