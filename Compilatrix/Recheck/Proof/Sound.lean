import Compilatrix.Recheck.Proof.Front

/-!
# `compile_sound` and `compile_safe` from the backend half (M2.7)

Roadmap §1.1 at stage S, for the recheck path's front half (`runLir`), with
the backend half as a hypothesis. **What the backend half (M2.7b) must
provide** is a refinement of the loaded Lir program by the object's
execution:

```lean
hback : Sem.Refines (f.loaded M) obj
```

for a model region `M` that `cx_init` accepts (`RegionOk M.ctx M.size`,
`Region M.mem M.ctx M.size`) and the object's execution `obj` in any
`Sem.Lang (Nat × List Nat) O`: on input `(r, ns)` it runs the object's
entry wrapper for root `r` (the symbol `Rt.lower` gave `f.lowered.roots[r]`)
on the arguments under the driver's contract, and observes its result by
the driver's readback at the root's type. `f.loaded M` fixes what that must
refine (`Rt.Loaded`): `cx_init` on `[M.size, M.budget]` over `M.mem` with
context `M.ctx`, then the root's Lir function on the tagged words of the
arguments (`natOverflow`, the wrapper's status 3, for an argument at or
above `2^63`), the result word read back by `Rt.readback` at the root's type
(`f.tys r`) with fuel `M.size / 8`; a root applied to fewer arguments than
it takes gives a value with no observation, to more is stuck
(`Sem.entryRun`). Refinement allows the object extra resource failures
(`heap`, `stack`, `natOverflow`) and asks nothing where the loaded program
is stuck.

From it, for every input:

* `compile_sound`: a value the object returns is the view of a value
  SrcEval returns (relabelled by tag at the root's type), or the source goes
  wrong;
* `compile_safe`: if the source does not go wrong, the object goes wrong
  at no clock (it returns, is still running, or fails for a resource);
* `compile_diverges`: a diverging source has an object that times out at
  every clock or fails for a resource.

`Front.GoesWrong` is stage S's disjunct: SrcEval stuck or trapping, or
returning a value its root's readback type does not read back.
-/

set_option autoImplicit false

namespace Compilatrix.Recheck

open Compilatrix.Sem (Obs Lang)
open Compilatrix.Lam.Erase.Proof (CheckedProgram)

/-- **The source goes wrong** on an input (roadmap §1.1 at stage S):
SrcEval is stuck or traps at some clock, or returns a value its root's
readback type does not read back (the view rejects it; Lean's typing
excludes it, stage S does not check it). -/
def Front.GoesWrong (f : Front) (i : Nat × List Nat) : Prop :=
  ∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).GoesWrong ∨
    ∃ v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v ∧ f.view i.1 (Lang.obs v) = none

/-- The viewed source goes wrong only where the source does. -/
theorem source_goesWrong {f : Front} {i : Nat × List Nat} {k : Nat}
    (h : (Lang.run f.source i k).GoesWrong) : f.GoesWrong i := by
  rcases Sem.Viewed.run_goesWrong.1 h with h' | h'
  · exact ⟨k, .inl h'⟩
  · exact ⟨k, .inr h'⟩

/-- **`compile_sound`, from the backend half** (roadmap §1.1 at stage S):
if the object's execution refines the loaded Lir program (`hback`, what
M2.7b proves), a value it returns is the view of a value SrcEval returns, or
the source goes wrong. -/
theorem compile_sound {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} {k : Nat} {w : Lang.Val O} (hw : Lang.run obj i k = .ok w) :
    (∃ k' v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k' = .ok v ∧
      f.view i.1 (Lang.obs v) = some (Lang.obs w)) ∨ f.GoesWrong i := by
  rcases ((front_refines h hok hreg).trans hback).backward hw with ⟨k', o, ho, hobs⟩ | ⟨k', hst⟩
  · obtain ⟨v, hv, hview⟩ := Sem.Viewed.run_ok ho
    exact .inl ⟨k', v, hv, hview.trans (congrArg some hobs)⟩
  · exact .inr (source_goesWrong (k := k') (by rw [hst]; trivial))

/-- **`compile_safe`, from the backend half**: if the source does not go
wrong, the object's execution goes wrong at no clock: it returns, is still
running or fails for a resource. -/
theorem compile_safe {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} (hs : ¬ f.GoesWrong i) (k : Nat) : ¬ (Lang.run obj i k).GoesWrong :=
  ((front_refines h hok hreg).trans hback).safe (fun _ hk' => hs (source_goesWrong hk')) k

/-- **Divergence, from the backend half**: a source that times out at every
clock has an object execution that times out at every clock or fails for a
resource. -/
theorem compile_diverges {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} (hs : ∀ k, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .timeout) :
    (∀ k, Lang.run obj i k = .timeout) ∨ ∃ k failure, Lang.run obj i k = .resource failure :=
  ((front_refines h hok hreg).trans hback).diverges fun k => by
    show (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).bind _ = _
    rw [hs k]
    rfl

/-- **The front half composes with any backend refinement** (the traced
shape, D-1): the object refines the viewed source. -/
theorem compose_traced {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj) :
    Sem.TRefines f.source obj :=
  Sem.Refines.ofPure ((front_refines h hok hreg).trans hback)

end Compilatrix.Recheck
