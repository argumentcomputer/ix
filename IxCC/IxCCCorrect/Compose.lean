import IxCC.Exe.Plain.Exe
import IxCCCorrect.GroundCheck
import IxCCCorrect.Progress

/-!
# The compiled object computes the kernel meaning (`IxCCCorrect.Compose`)

The compiler's chain ends in "a value the object returns is the view of a value SrcEval returns"
(`Recheck.sound`, `RcReplay.sound`); the grounding library's ends in "a value SrcEval returns
denotes what the root applied to its arguments denotes". This module joins them, for a program the
certificate checker accepted and `groundCheck` accepted:

```lean
recheck_agrees : Recheck.run cfg P c = .ok a →
  GroundOk acc a.src (Input.ofProgram a.src a.checked) (a.front.view 0) claim.target claim.abi →
  ns.length = claim.abi.arity → NeverWrong a.front.source (0, ns) → ReturnsCanon a.src ns →
  D.Ok … → a.front.Covered c (0, ns) → Lang.run (a.linked D) (0, ns) k = .ok (some o) →
  ∃ answer, o = abiObs claim.abi answer ∧ Agrees claim acc ns answer
```

and `rc_agrees` on the plain-RC path. Both go through one statement about the source,
`agrees_of_srcPlainEval`, which the executable theorems reuse (`IxCCCorrect.ComposeExe`).

## The links of the inventory (design note, 9.3)

| Link | Here |
| --- | --- |
| G, the checks on the checker's data | `groundCheck_sound` (`IxCCCorrect.GroundCheck`): `GroundOk` is about `a.src`, the kernel's `acc.env`, and a key map the check ties to the reader's |
| G1, the observation bridge | `obsOf_lit`, `obsOf_con`, `viewNat_viewOf`, `viewNat_treeViewOf`; **under `ReturnsCanon`, not under `NeverWrong` alone** (below) |
| G2, G3, the target's key is root 0's | decided by `groundCheck` (`GroundOk`'s second and third conjuncts) |
| G4, the application denotes | `Grounded.app_denotes` (`IxCCCorrect.GroundRoot`) |
| G5, enumeration answers by address | decided by `groundCheck` (`ResultOk`) |
| G6, `Admits` | `admits_of_ingress` |

## G1 is false under `NeverWrong` alone

`NeverWrong` says the root's view rejects no value SrcEval returns. The view is lossy in three
ways, so "the view accepts it" does not make a value a canonical form of the root's type:

* erasure unboxes a one-constructor inductive with one kept field (`Lam.Erase.Input.unbox?`), so
  `OfNat.mk 5`-like values and the word towers observe as the number `5`;
* erasure retags `Decidable.isFalse`/`isTrue` as `Bool.false`/`true` (`Input.alias`);
* the view relabels a constructor by its table tag at the root's signature, which does not say
  which family the constructor belongs to (`Rt.tagify`).

Lean's typing excludes all three at a root of type `Nat` or of an enumeration, but neither SrcEval
nor `NeverWrong` carries typing, and no law of `Ix.Kernel.Model` separates a structure's value from
a numeral. So the bridge needs the canonical form as a fact about SrcEval: `ReturnsCanon`. The
shape discipline proves it on the way to `NeverWrong` and then drops it (`Shape1.run_ok` concludes
`ValOk`, `neverWrong_of_shape` keeps only the view's acceptance); `returnsCanon_of_shape1` below
recovers it for milestone M1. **`FunctionalProgress` as defined delivers `NeverWrong` only: for
tier 1 it has to deliver `ReturnsCanon` as well.**
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Obs Lang Result)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Grounding

universe u

/-! ## G6: `Admits`, from ingress -/

/-- **`Admits` from ingress at the claim's limits**: ingress decodes the bytes and runs the
kernel's tiered entry over the whole environment (`Recheck.ingress_parts`); the root and the role
table are compared by the checker. -/
theorem admits_of_ingress {claim : Claim} {envBytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {inp : Recheck.Input}
    (h : Recheck.ingress envBytes equations roots claim.kernelLimits = .ok inp)
    (henv : inp.env.root = claim.env)
    (hrole : inp.env.bindingAddress = some claim.roleTable) :
    Admits claim envBytes inp.kernel.acc := by
  obtain ⟨hdec, hacc, -⟩ := Recheck.ingress_parts h
  unfold Admits
  exact ⟨inp.env, hdec, henv, hrole, hacc⟩

/-! ## G1: the observation bridge, at canonical forms -/

/-- The compiler observes a literal as its number. -/
theorem obsOf_lit (I : Lam.Erase.Input) (n : Nat) : obsOf I (Value.lit n) = some (.nat n) := by
  show (IxCC.Lam.Erase.eraseVal I (Value.lit n)).bind IxCC.Lam.Erase.Proof.obsV = some (.nat n)
  simp [IxCC.Lam.Erase.eraseVal, IxCC.Lam.Erase.Proof.obsV]

/-- The compiler's observation of a field-less value of a level-monomorphic constructor depends
neither on the levels nor on the parameters the value carries. -/
theorem obsOf_con {I : Lam.Erase.Input} {c : CId} (h : I.lvls c = 0) (ls : Levels)
    (ps : List Slot) : obsOf I (Value.con c ls ps []) = obsOf I (Value.con c [] [] []) := by
  show (IxCC.Lam.Erase.eraseVal I (Value.con c ls ps [])).bind IxCC.Lam.Erase.Proof.obsV =
    (IxCC.Lam.Erase.eraseVal I (Value.con c [] [] [])).bind IxCC.Lam.Erase.Proof.obsV
  have hq : ∀ prof : IxCC.Src.Profile, IxCC.Src.Profile.normalize prof 0 = [] := fun _ => rfl
  simp only [IxCC.Lam.Erase.eraseVal, h, hq]

/-- **A view reports a number only as itself.** -/
def ViewNat (view : View) : Prop :=
  ∀ (n : Nat) (o : Obs), view (some (.nat n)) = some (some o) → o = .nat n

/-- The immortal and zero-RC paths' view (`Rt.viewOf`). -/
theorem viewNat_viewOf (T : List Lam.CtorInfo) (tys : Nat → Option (Rt.Sig × Rt.FoTy)) (r : Nat) :
    ViewNat (Rt.viewOf T tys r) := by
  intro n o h
  unfold Rt.viewOf at h
  cases hty : tys r with
  | none => rw [hty] at h; cases h
  | some st =>
    obtain ⟨sig, ty⟩ := st
    rw [hty] at h
    cases ty with
    | nat =>
      simp only [Option.bind_some, Rt.tagify, Option.map_some, Option.some.injEq] at h
      exact h.symm
    | ind i => simp [Rt.tagify] at h

/-- The plain-RC path's view (`RcReplay.treeViewOf`). -/
theorem viewNat_treeViewOf (T : List Lam.CtorInfo) (tys : Nat → Option (Rt.Sig × Rt.FoTy))
    (r : Nat) : ViewNat (Recheck.RcReplay.treeViewOf T tys r) := by
  intro n o h
  unfold Recheck.RcReplay.treeViewOf at h
  cases hty : tys r with
  | none => rw [hty] at h; cases h
  | some st =>
    obtain ⟨sig, ty⟩ := st
    rw [hty] at h
    cases ty with
    | nat =>
      simp only [Option.bind_some, IxCC.Rt.Rc.Procs.Readback.treeView, Option.map_some,
        Option.some.injEq] at h
      exact h.symm
    | ind i => simp [IxCC.Rt.Rc.Procs.Readback.treeView] at h

/-! ## The source run, read off the checked program -/

/-- A run of the checked source at root 0 is a run of SrcEval at the first root's constant, on
the literals, paired with the erasure input. -/
theorem srcRun_ok {src : Program} {checked : Src.Relevance.Checked} {ns : List Nat} {k : Nat}
    {val : Lang.Val CheckedProgram} {addr : Ixon.Address} {root : CId}
    (hroot : src.roots.head? = some (addr, root))
    (h : Lang.run (⟨src, checked⟩ : CheckedProgram) (0, ns) k = .ok val) :
    ∃ v, IxCC.Src.run src k root (ns.map Value.lit) = .ok v ∧
      val = (Lam.Erase.Input.ofProgram src checked, v) := by
  have e : Lang.run (⟨src, checked⟩ : CheckedProgram) (0, ns) k =
      IxCC.Lam.Erase.Proof.srcRun ⟨src, checked⟩ (0, ns) k := rfl
  rw [e] at h
  unfold IxCC.Lam.Erase.Proof.srcRun at h
  rw [List.head?_eq_getElem?] at hroot
  simp only [hroot] at h
  obtain ⟨v, hv, hval⟩ := Result.bind_eq_ok_iff.mp h
  cases hval
  exact ⟨v, hv, rfl⟩

/-! ## The composed statement, at the source -/

/-- The observation an answer is returned as: its number at a `Nat` result, the constructor at
its index at an enumeration. -/
def abiObs (abi : Abi) (answer : Nat) : Obs :=
  match abi.result with
  | .nat => .nat answer
  | .enum _ => .ctor answer []

/-- **Where the checked source evaluates to an observation, that observation is an answer that
agrees with the kernel meaning of the target.** `GroundOk` is what `groundCheck` established;
`ReturnsCanon` is the canonical-form fact about SrcEval (see the module note). No model is assumed:
`Agrees` quantifies over them. -/
theorem agrees_of_srcPlainEval {claim : Claim} {acc : Src.KernelFront.Accepted} {src : Program}
    {checked : Src.Relevance.Checked} {view : Nat → Option Obs → Option (Option Obs)}
    (hok : GroundOk acc src (Lam.Erase.Input.ofProgram src checked) (view 0) claim.target
      claim.abi)
    (hnat : ViewNat (view 0)) {ns : List Nat} (hlen : ns.length = claim.abi.arity)
    (hcanon : ReturnsCanon src ns) {o : Obs}
    (h : IxCC.Exe.Plain.srcPlainEval src checked view ns (some o)) :
    ∃ answer, o = abiObs claim.abi answer ∧ Agrees.{u} claim acc ns answer := by
  obtain ⟨κ, lpsOf, ann, Sl, Inst, root, res, hroot, hres, hkey, hparams, hG, hRes⟩ := hok
  obtain ⟨k, val, hrun, hview⟩ := h
  obtain ⟨v, hsrc, rfl⟩ := srcRun_ok hroot hrun
  have hview' : view 0 (obsOf (Lam.Erase.Input.ofProgram src checked) v) = some (some o) := hview
  obtain ⟨res', hres', hcan⟩ := hcanon _ root k v hroot hsrc
  rw [hres] at hres'
  cases hres'
  have harity : arityOf src root = ns.length := by
    rw [hlen]
    simp [Abi.arity, hparams]
  rw [harity] at hG
  have hcan0 := hcan
  cases res with
  | nat =>
    obtain ⟨n, rfl⟩ := hcan
    have ho : o = .nat n := hnat n o (by rw [obsOf_lit] at hview'; exact hview')
    have hr : claim.abi.result = ResTy.nat := hRes
    refine ⟨n, by rw [ho]; simp only [abiObs, hr], ?_⟩
    unfold Agrees
    refine ⟨κ root, litE n, hkey, by simp only [answerTerm, hr], ?_⟩
    unfold SameDenotation
    intro V _ M φ ρ
    exact hG.same M hsrc hcan0 φ ρ
  | enum D =>
    obtain ⟨c, ls, ps, s, lv, i, ty, rfl, hdc⟩ := hcan
    obtain ⟨addrs, hr, -, hall⟩ := hRes
    obtain ⟨hl, t, hvt, haddr, hk⟩ := hall c s lv i ty hdc
    have ho : o = .ctor t [] := by
      rw [obsOf_con hl, hvt] at hview'
      cases hview'
      rfl
    refine ⟨t, by rw [ho]; simp only [abiObs, hr], ?_⟩
    unfold Agrees
    refine ⟨κ root, .const (κ c) [], hkey,
      by simp only [answerTerm, hr, haddr, Option.bind_some, hk, Option.map_some], ?_⟩
    unfold SameDenotation
    intro V _ M φ ρ
    exact hG.same M hsrc hcan0 φ ρ

/-! ## The composed theorem, at the evaluator -/

/-- **The compiled object computes the kernel meaning** (immortal and zero-RC objects). For a
program the certificate checker accepted (`Recheck.run`) on which `groundCheck` accepted the claim's
target and calling convention (`GroundOk`), on an input of the claim's arity on which the viewed
source is never wrong and SrcEval returns canonical forms: an observation the linked object
returns for root 0 is an answer that agrees with the kernel meaning of the claimed address. -/
theorem recheck_agrees {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a) {claim : Claim}
    {acc : Src.KernelFront.Accepted}
    (hok : GroundOk acc a.src (Lam.Erase.Input.ofProgram a.src a.checked) (a.front.view 0)
      claim.target claim.abi)
    {ns : List Nat} (hlen : ns.length = claim.abi.arity)
    (hp : NeverWrong a.front.source (0, ns)) (hcanon : ReturnsCanon a.src ns)
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) (hi : a.front.Covered c (0, ns))
    {k : Nat} {o : Obs} (hw : Lang.run (a.linked D) (0, ns) k = .ok (some o)) :
    ∃ answer, o = abiObs claim.abi answer ∧ Agrees.{u} claim acc ns answer := by
  obtain ⟨k', v, hv, hview⟩ := (recheck_sound_of_neverWrong h D hD (0, ns) hi hp).1 k _ hw
  exact agrees_of_srcPlainEval (view := a.front.view) hok (viewNat_viewOf _ _ 0) hlen hcanon
    (Exists.intro k' ⟨v, hv, hview⟩)

/-- **The compiled object computes the kernel meaning** (plain-RC objects). -/
theorem rc_agrees {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a) {claim : Claim}
    {acc : Src.KernelFront.Accepted}
    (hok : GroundOk acc a.front.src (Lam.Erase.Input.ofProgram a.front.src a.front.checked)
      (a.front.view 0) claim.target claim.abi)
    {ns : List Nat} (hlen : ns.length = claim.abi.arity)
    (hp : NeverWrong a.front.source (0, ns)) (hcanon : ReturnsCanon a.front.src ns)
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) (hi : a.front.Covered c (0, ns))
    {k : Nat} {o : Obs} (hw : Lang.run (a.linked D) (0, ns) k = .ok (some o)) :
    ∃ answer, o = abiObs claim.abi answer ∧ Agrees.{u} claim acc ns answer := by
  obtain ⟨k', v, hv, hview⟩ := (rc_sound_of_neverWrong h D hD (0, ns) hi hp).1 k _ hw
  exact agrees_of_srcPlainEval (view := a.front.view) hok (viewNat_treeViewOf _ _ 0) hlen hcanon
    (Exists.intro k' ⟨v, hv, hview⟩)

/-! ## The check on the checker's artifacts -/

/-- **`groundCheck` on what `Recheck.run` checked**: the kernel's acceptance and reading from
ingress, the checked source and its annotation from the artifact and the certificate, the view of
root 0. This is the call a `compile` makes after the certificate checker accepts. -/
def groundCheckRecheck (inp : Recheck.Input) (c : Recheck.Cert) (a : Recheck.Artifact)
    (target : Ixon.Address) : Except String Abi :=
  groundCheck inp.kernel a.src a.checked c.relevance (a.front.view 0) target

/-- The same on the plain-RC path. -/
def groundCheckRc (inp : Recheck.Input) (c : Recheck.RcReplay.Cert) (a : Recheck.RcReplay.Artifact)
    (target : Ixon.Address) : Except String Abi :=
  groundCheck inp.kernel a.front.src a.front.checked c.base.relevance (a.front.view 0) target

/-- **The pipeline check gives the composed theorem's hypothesis** (immortal and zero-RC). -/
theorem groundCheckRecheck_sound {inp : Recheck.Input} {c : Recheck.Cert} {a : Recheck.Artifact}
    {target : Ixon.Address} {abi : Abi} (h : groundCheckRecheck inp c a target = .ok abi) :
    GroundOk inp.kernel.acc a.src (Lam.Erase.Input.ofProgram a.src a.checked) (a.front.view 0)
      target abi :=
  groundCheck_sound h

/-- **The pipeline check gives the composed theorem's hypothesis** (plain RC). -/
theorem groundCheckRc_sound {inp : Recheck.Input} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} {target : Ixon.Address} {abi : Abi}
    (h : groundCheckRc inp c a target = .ok abi) :
    GroundOk inp.kernel.acc a.front.src
      (Lam.Erase.Input.ofProgram a.front.src a.front.checked) (a.front.view 0) target abi :=
  groundCheck_sound h

end IxCC.Correct
