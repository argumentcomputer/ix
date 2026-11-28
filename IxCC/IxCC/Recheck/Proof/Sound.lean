import IxCC.Recheck.Proof.Front

/-!
# `compile_sound` and `compile_safe` from the backend half

The correctness statement at stage S, for the recheck path's front half (`runLir`), with
the backend half as a hypothesis. **What the backend half must
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

From it, for every input it covers (`Front.Covered`: of exactly its root's
declared count, or any input when the closures step left the certificate's
program unchanged):

* `compile_sound`: a value the object returns is the view of a value
  SrcEval returns (relabelled by tag at the root's type), or the source goes
  wrong;
* `compile_safe`: if the source does not go wrong, the object goes wrong
  at no clock (it returns, is still running, or fails for a resource);
* `compile_diverges`: a diverging source has an object that times out at
  every clock or fails for a resource.

`Front.GoesWrong` is stage S's disjunct: SrcEval stuck or trapping, or
returning a value its root's readback type does not read back. -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- **The source goes wrong** on an input (the correctness statement at stage S):
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

/-- **`compile_sound`, from the backend half** (the correctness statement at stage S):
if the object's execution refines the loaded Lir program (`hback`, what
`Recheck.back_refines` proves), a value it returns is the view of a value SrcEval returns, or
the source goes wrong. -/
theorem compile_sound {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} (hi : f.Covered c i) {k : Nat} {w : Lang.Val O} (hw : Lang.run obj i k = .ok w) :
    (∃ k' v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k' = .ok v ∧
      f.view i.1 (Lang.obs v) = some (Lang.obs w)) ∨ f.GoesWrong i := by
  rcases ((front_refines h hok hreg).trans_refines hback).backward hi hw with ⟨k', o, ho, hobs⟩ | ⟨k', hst⟩
  · obtain ⟨v, hv, hview⟩ := Sem.Viewed.run_ok ho
    exact .inl ⟨k', v, hv, hview.trans (congrArg some hobs)⟩
  · exact .inr (source_goesWrong (k := k') (by rw [hst]; trivial))

/-- **`compile_safe`, from the backend half**: if the source does not go
wrong, the object's execution goes wrong at no clock: it returns, is still
running or fails for a resource. -/
theorem compile_safe {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} (hi : f.Covered c i) (hs : ¬ f.GoesWrong i) (k : Nat) :
    ¬ (Lang.run obj i k).GoesWrong :=
  ((front_refines h hok hreg).trans_refines hback).safe hi (fun _ hk' => hs (source_goesWrong hk')) k

/-- **Divergence, from the backend half**: a source that times out at every
clock has an object execution that times out at every clock or fails for a
resource. -/
theorem compile_diverges {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} (hi : f.Covered c i)
    (hs : ∀ k, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .timeout) :
    (∀ k, Lang.run obj i k = .timeout) ∨ ∃ k failure, Lang.run obj i k = .resource failure :=
  ((front_refines h hok hreg).trans_refines hback).diverges hi fun k => by
    show (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).bind _ = _
    rw [hs k]
    rfl

/-- **The front half composes with any backend refinement** (the traced
shape, D-1): the object refines the viewed source. -/
theorem compose_traced {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj) :
    Sem.TRefinesOn (f.Covered c) f.source obj :=
  Sem.RefinesOn.ofPure ((front_refines h hok hreg).trans_refines hback)

/-! ## Non-vacuity of `Front.GoesWrong` and `compile_sound` -/

/-- By clock monotonicity of `CheckedProgram`, two successful evaluations on
the same input at any clocks return the same value. -/
theorem Front.eval_unique {f : Front} {i : Nat × List Nat} {k₁ k₂ : Nat}
    {v₁ v₂ : Lang.Val CheckedProgram}
    (h₁ : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k₁ = .ok v₁)
    (h₂ : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k₂ = .ok v₂) :
    v₁ = v₂ := by
  have heq := (Lang.mono (⟨f.src, f.checked⟩ : CheckedProgram) i).eq_of_ne_timeout
    (by rw [h₁]; simp) (by rw [h₂]; simp)
  rw [h₁, h₂] at heq
  exact Sem.Result.ok.inj heq

/-- **Non-vacuity of `Front.GoesWrong`**: whenever `CheckedProgram`
evaluates to `.ok v` on input `i` and `f.view i.1 (Lang.obs v) = some o`,
the source does not go wrong (`¬ f.GoesWrong i`). -/
theorem Front.not_goesWrong_of_eval {f : Front} {i : Nat × List Nat} {k : Nat}
    {v : Lang.Val CheckedProgram} {o : Option Obs}
    (heval : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v)
    (hview : f.view i.1 (Lang.obs v) = some o) :
    ¬ f.GoesWrong i := by
  rintro ⟨k', hgw | ⟨v', heval', hnone⟩⟩
  · have hne : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k' ≠ .timeout := by
      intro ht; rw [ht] at hgw; exact hgw
    have heq := (Lang.mono (⟨f.src, f.checked⟩ : CheckedProgram) i).eq_of_ne_timeout
      hne (by rw [heval]; simp)
    rw [heval] at heq
    rw [heq] at hgw
    exact hgw
  · have hv := Front.eval_unique heval heval'
    subst hv
    rw [hview] at hnone
    cases hnone

/-- **Non-vacuity at a `Nat` root**: whenever `CheckedProgram` evaluates to
`.ok v` with `Lang.obs v = some (.nat n)` at a root with readback type
`Nat`, `f.view` reports `some (some (.nat n))` and `¬ f.GoesWrong i`. -/
theorem Front.not_goesWrong_of_nat {f : Front} {i : Nat × List Nat} {k : Nat}
    {v : Lang.Val CheckedProgram} {n : Nat}
    (hty : f.tys i.1 = some ({}, .nat))
    (heval : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v)
    (hobs : Lang.obs v = some (.nat n)) :
    f.view i.1 (Lang.obs v) = some (some (.nat n)) ∧ ¬ f.GoesWrong i := by
  have hview : f.view i.1 (Lang.obs v) = some (some (.nat n)) := by
    rw [hobs]
    exact view_nat hty n
  exact ⟨hview, Front.not_goesWrong_of_eval heval hview⟩

/-- **Non-vacuity at a field-less constructor**: whenever `CheckedProgram`
evaluates to `.ok v` with `Lang.obs v = some (.ctor cid [])` matching the
root's inductive signature, `f.view` reports `some (some (.ctor c.tag []))`
and `¬ f.GoesWrong i`. -/
theorem Front.not_goesWrong_of_ctor0 {f : Front} {i : Nat × List Nat} {k : Nat}
    {v : Lang.Val CheckedProgram} {sig : Rt.Sig} {idx : Nat} {cid : Src.CId} {c : Fir.CtorInfo}
    (hty : f.tys i.1 = some (sig, .ind idx))
    (hc : Fir.CtorInfo.ofKey f.cfg.ctors (.src cid) = some c)
    (hsig : sig.ctor? idx c.tag = some [])
    (heval : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v)
    (hobs : Lang.obs v = some (.ctor cid [])) :
    f.view i.1 (Lang.obs v) = some (some (.ctor c.tag [])) ∧ ¬ f.GoesWrong i := by
  have hview : f.view i.1 (Lang.obs v) = some (some (.ctor c.tag [])) := by
    rw [hobs]
    exact view_ctor0 hty hc hsig
  exact ⟨hview, Front.not_goesWrong_of_eval heval hview⟩

/-- **Non-vacuous `compile_sound`**: when `CheckedProgram` evaluates to
`.ok v` with `f.view i.1 (Lang.obs v) = some o`, the `f.GoesWrong i`
disjunct of `compile_sound` is discharged, the object never goes wrong, and
every value `w` the object returns has `Lang.obs w = o`. -/
theorem compile_sound_of_eval {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (h : runLir cfg P c = .ok f) {M : Rt.Model}
    (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size)
    {O : Type} [Lang (Nat × List Nat) O] {obj : O} (hback : Sem.Refines (f.loaded M) obj)
    {i : Nat × List Nat} (hi : f.Covered c i) {k_src : Nat} {v : Lang.Val CheckedProgram} {o : Option Obs}
    (heval : Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k_src = .ok v)
    (hview : f.view i.1 (Lang.obs v) = some o) :
    ¬ f.GoesWrong i ∧
    (∀ k, ¬ (Lang.run obj i k).GoesWrong) ∧
    (∀ k w, Lang.run obj i k = .ok w → Lang.obs w = o) := by
  have hngw := Front.not_goesWrong_of_eval heval hview
  refine ⟨hngw, compile_safe h hok hreg hback hi hngw, fun k w hw => ?_⟩
  rcases compile_sound h hok hreg hback hi hw with ⟨k', v', heval', hview'⟩ | hgw
  · have hv := Front.eval_unique heval heval'
    subst hv
    rw [hview] at hview'
    exact (Option.some.inj hview').symm
  · exact absurd hgw hngw

end IxCC.Recheck
