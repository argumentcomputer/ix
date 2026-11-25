import IxCCCorrect.Shape2Check

/-!
# The shape check on the recheck path (`IxCCCorrect.ShapeHook`)

`Recheck.sound` leaves one escape: "or the source goes wrong". `IxCCCorrect.Shape2Check`
removes it for a root whose shape certificate checks, from three hypotheses beyond the
artifact: `certOk` is true, the root's instance is in the certificate, and the root's
readback type is `Nat`. This module turns the three into **what a checker computes**, so
that "the checker accepted" is the only hypothesis left:

* `tys_nat_of_resultTy`: the readback type of a root (`Front.tys`, by `Recheck.rootTy`)
  is `Nat` when the root's declared result type is the pinned `Nat`
  (`Recheck.resultTy`), a test on the checked source alone.
* `natRootOk src sc r n`: root `r` has the instance `Nat → … → Nat → Nat` (`n`
  parameters) in the certificate `sc`, and its declared result type is `Nat`.
* `runShaped cfg P c sc arities`: **the recheck path with the shape check**:
  `Recheck.run`, then `certOk` on the checked source the run made, then `natRootOk` for
  each root at its stated parameter count. It only *checks* `sc`; the producer of `sc`
  (`IxCCCorrect.Shape2Produce`, unproved) is not on this path.
* `runShaped_sound`: `Recheck.sound` with no "source goes wrong" case, for every covered
  input of a stated root, from `runShaped … = .ok a` alone.
* `neverStuck_checked`: the unviewed statement, for any result shape: the checked
  source (not the source viewed at readback types) is stuck or trapping at no clock.
  This is the proposition `Compose.NeverStuck` of the circuit back end, with never-trap
  added.

The interface another lane needs is two functions and one theorem: `certOk` (or
`runShaped`), `natRootOk`, and `runShaped_sound`. Nothing in `IxCC/Recheck` changes: the
shape certificate travels beside `Recheck.Cert`, not inside it.
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape2

open IxCC.Src
open IxCC.X86
open IxCC.Sem (Lang Obs Result)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- A root's readback type is `Nat` when its declared result type is the pinned `Nat`. -/
theorem tys_nat_of_resultTy {f : Recheck.Front} {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : f.src.roots[r]? = some (addr, c)) (h : Recheck.resultTy f.src c = some .nat) :
    f.tys r = some ({}, .nat) := by
  simp [Recheck.Front.tys, hroot, Recheck.rootTy, h]

/-- **A `Nat` root of the certificate**: root `r` has the instance of `n` `Nat`
parameters and a `Nat` result, and its declared result type is `Nat`. -/
def natRootOk (src : Src.Program) (sc : Cert) (r n : Nat) : Bool :=
  match src.roots[r]? with
  | some (_, c) =>
    decide ((c, ([] : Levels), arrows (List.replicate n .nat) .nat) ∈ sc.insts) &&
      decide (Recheck.resultTy src c = some .nat)
  | none => false

/-- Each root from `r` on is a `Nat` root at its stated parameter count. -/
def rootsOk (src : Src.Program) (sc : Cert) : Nat → List Nat → Bool
  | _, [] => true
  | r, n :: rest => natRootOk src sc r n && rootsOk src sc (r + 1) rest

theorem rootsOk_get {src : Src.Program} {sc : Cert} : ∀ (arities : List Nat) (r0 : Nat),
    rootsOk src sc r0 arities = true → ∀ (i n : Nat), arities[i]? = some n →
    natRootOk src sc (r0 + i) n = true
  | [], _, _, i, n, hi => by simp at hi
  | m :: rest, r0, h, i, n, hi => by
    simp only [rootsOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := rootsOk_get rest (r0 + 1) h.2 i n hi
      have e : r0 + (i + 1) = r0 + 1 + i := by omega
      rw [e]
      exact this

/-- **Functional progress from the two checks**: no clock at which the viewed source is
stuck, traps, or returns a value its root's view rejects. -/
theorem neverWrong_of_check {f : Recheck.Front} {sc : Cert} (h : certOk f.src sc = true)
    {r : Nat} (ns : List Nat) (hn : natRootOk f.src sc r ns.length = true) :
    NeverWrong f.source (r, ns) := by
  unfold natRootOk at hn
  cases hroot : f.src.roots[r]? with
  | none => simp [hroot] at hn
  | some e =>
    obtain ⟨addr, c⟩ := e
    simp only [hroot, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact neverWrong_of_cert_nat h hroot ns hn.1 (.inr (tys_nat_of_resultTy hroot hn.2))

/-- **Never stuck and never a trap, unviewed.** The checked source itself (no root
view), at a root of any result shape the certificate gives it. -/
theorem neverStuck_checked {src : Src.Program} {ch : Src.Relevance.Checked} {sc : Cert}
    (h : certOk src sc = true) {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : src.roots[r]? = some (addr, c)) (ns : List Nat) {ρ : Shape}
    (hc : (c, ([] : Levels), arrows (List.replicate ns.length .nat) ρ) ∈ sc.insts) (k : Nat) :
    Lang.run (⟨src, ch⟩ : CheckedProgram) (r, ns) k ≠ .stuck ∧
      Lang.run (⟨src, ch⟩ : CheckedProgram) (r, ns) k ≠ .trap := by
  have e : Lang.run (⟨src, ch⟩ : CheckedProgram) (r, ns) k =
      IxCC.Lam.Erase.Proof.srcRun ⟨src, ch⟩ (r, ns) k := rfl
  unfold IxCC.Lam.Erase.Proof.srcRun at e
  simp only [hroot] at e
  rcases run_ok (sig := sc.sig) (sigOk_of_cert h) ns hc k with hr | ⟨v, hr, _⟩
  · rw [hr] at e
    have e' : Lang.run (⟨src, ch⟩ : CheckedProgram) (r, ns) k = .timeout := e
    rw [e']
    exact ⟨fun hw => (by cases hw), fun hw => (by cases hw)⟩
  · rw [hr] at e
    have e' : Lang.run (⟨src, ch⟩ : CheckedProgram) (r, ns) k =
        .ok (IxCC.Lam.Erase.Input.ofProgram src ch, v) := e
    rw [e']
    exact ⟨fun hw => (by cases hw), fun hw => (by cases hw)⟩

/-- What the shaped recheck path refuses with. -/
inductive Refusal where
  /-- the recheck path declined or rejected the program -/
  | recheck (e : Recheck.Err)
  /-- the shape certificate does not check, or a root is not a `Nat` root of its stated
  parameter count -/
  | shape

/-- **The recheck path with the shape check.** `arities` states, root by root from root
0, how many `Nat` parameters the root takes. The shape certificate `sc` is only
checked. -/
def runShaped (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.Cert) (sc : Cert)
    (arities : List Nat) : Except Refusal Recheck.Artifact :=
  match Recheck.run cfg P c with
  | .error e => .error (.recheck e)
  | .ok a => if certOk a.src sc && rootsOk a.src sc 0 arities then .ok a else .error .shape

/-- What `runShaped` accepted, `Recheck.run` made, and the two checks hold of it. -/
theorem runShaped_ok {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {sc : Cert}
    {arities : List Nat} {a : Recheck.Artifact} (h : runShaped cfg P c sc arities = .ok a) :
    Recheck.run cfg P c = .ok a ∧ certOk a.src sc = true ∧ rootsOk a.src sc 0 arities = true := by
  unfold runShaped at h
  cases hrun : Recheck.run cfg P c with
  | error e => simp [hrun] at h
  | ok a' =>
    simp only [hrun] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨rfl, hc.1, hc.2⟩
    · cases h

/-- **`Recheck.sound` with no escape, from the checker's acceptance alone.** If the
shaped recheck path accepts, then for every covered input of a root at its stated
parameter count: a value the object returns is the view of a value SrcEval returns, and
the object goes wrong at no clock. There is no "or the source goes wrong". -/
theorem runShaped_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {sc : Cert}
    {arities : List Nat} {a : Recheck.Artifact} (h : runShaped cfg P c sc arities = .ok a)
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) (r : Nat) (ns : List Nat)
    (hr : arities[r]? = some ns.length) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) := by
  obtain ⟨hrun, hcert, hroots⟩ := runShaped_ok h
  have hn := rootsOk_get arities 0 hroots r ns.length hr
  rw [Nat.zero_add] at hn
  exact recheck_sound_of_neverWrong hrun D hD (r, ns) hi
    (neverWrong_of_check (f := a.front) hcert ns hn)

/-! ## Any view, and the reference-counted path -/

/-- **Functional progress of a viewed checked source from a shape signature, whatever
the view** (`neverWrong_of_shape` without a front): a shaped root on `Nat` arguments is
never stuck and never traps, and its result is accepted by any view that accepts every
value of the result shape. -/
theorem neverWrong_of_shape_view {src : Src.Program} {ch : Src.Relevance.Checked} {sig : Sig}
    {view : Nat → Option Obs → Option (Option Obs)} (hsig : SigOk src sig) {r : Nat}
    {addr : Ixon.Address} {c : CId} (hroot : src.roots[r]? = some (addr, c)) (ns : List Nat)
    {ρ : Shape} (hc : sig.inst c [] (arrows (List.replicate ns.length .nat) ρ))
    (hview : ∀ v, ValOk src sig v ρ → view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram src ch, v) : Lang.Val CheckedProgram)) ≠ none) :
    NeverWrong (⟨⟨src, ch⟩, view⟩ : Source) (r, ns) := by
  rw [neverWrong_iff]
  intro k
  have e : Lang.run (⟨⟨src, ch⟩, view⟩ : Source).prog (r, ns) k =
      IxCC.Lam.Erase.Proof.srcRun ⟨src, ch⟩ (r, ns) k := rfl
  unfold IxCC.Lam.Erase.Proof.srcRun at e
  simp only [hroot] at e
  rcases run_ok hsig ns hc k with hr | ⟨v, hr, hv⟩
  · rw [hr] at e
    constructor
    · rw [e]
      intro hw
      exact hw
    · intro v hv
      rw [e] at hv
      cases hv
  · rw [hr] at e
    constructor
    · rw [e]
      intro hw
      exact hw
    · intro v' hv'
      rw [e] at hv'
      cases hv'
      exact hview v hv

/-- On the reference-counted path too, a root's readback type is `Nat` when its
declared result type is. -/
theorem rc_tys_nat_of_resultTy {f : Recheck.RcReplay.Front} {r : Nat} {addr : Ixon.Address}
    {c : CId} (hroot : f.src.roots[r]? = some (addr, c))
    (h : Recheck.resultTy f.src c = some .nat) : f.tys r = some ({}, .nat) := by
  simp [Recheck.RcReplay.Front.tys, hroot, Recheck.rootTy, h]

/-- The tree view at a root read back as `Nat` accepts every value of shape `nat`. -/
theorem rc_view_nat_ok {f : Recheck.RcReplay.Front} {sig : Sig} {r : Nat}
    (hty : f.tys r = some ({}, .nat)) (v : Value) (hv : ValOk f.src sig v .nat) :
    f.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, v) : Lang.Val CheckedProgram)) ≠ none := by
  obtain ⟨n, rfl⟩ := hv.nat_inv
  have ho : Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.lit n) : Lang.Val CheckedProgram) =
      some (.nat n) := by
    show (IxCC.Lam.Erase.eraseVal _ (Value.lit n)).bind IxCC.Lam.Erase.Proof.obsV = some (.nat n)
    simp [IxCC.Lam.Erase.eraseVal, IxCC.Lam.Erase.Proof.obsV]
  rw [ho]
  simp [Recheck.RcReplay.Front.view, Recheck.RcReplay.treeViewOf, hty,
    IxCC.Rt.Rc.Procs.Readback.treeView]

/-- **Functional progress on the reference-counted path from the two checks.** -/
theorem rc_neverWrong_of_check {f : Recheck.RcReplay.Front} {sc : Cert}
    (h : certOk f.src sc = true) {r : Nat} (ns : List Nat)
    (hn : natRootOk f.src sc r ns.length = true) : NeverWrong f.source (r, ns) := by
  unfold natRootOk at hn
  cases hroot : f.src.roots[r]? with
  | none => simp [hroot] at hn
  | some e =>
    obtain ⟨addr, c⟩ := e
    simp only [hroot, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact neverWrong_of_shape_view (sig := sc.sig) (view := f.view) (sigOk_of_cert h) hroot ns
      hn.1 (rc_view_nat_ok (rc_tys_nat_of_resultTy hroot hn.2))

/-- **The reference-counted recheck path with the shape check.** As `runShaped`. -/
def rcRunShaped (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.RcReplay.Cert) (sc : Cert)
    (arities : List Nat) : Except Refusal Recheck.RcReplay.Artifact :=
  match Recheck.RcReplay.run cfg P c with
  | .error e => .error (.recheck e)
  | .ok a =>
    if certOk a.front.src sc && rootsOk a.front.src sc 0 arities then .ok a else .error .shape

/-- **`RcReplay.sound` with no escape, from the checker's acceptance alone**, for the
roots with a `Nat` result. -/
theorem rcRunShaped_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {sc : Cert} {arities : List Nat} {a : Recheck.RcReplay.Artifact}
    (h : rcRunShaped cfg P c sc arities = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (r : Nat) (ns : List Nat)
    (hr : arities[r]? = some ns.length) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) := by
  unfold rcRunShaped at h
  cases hrun : Recheck.RcReplay.run cfg P c with
  | error e => simp [hrun] at h
  | ok a' =>
    simp only [hrun] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      have hn := rootsOk_get arities 0 hc.2 r ns.length hr
      rw [Nat.zero_add] at hn
      exact rc_sound_of_neverWrong hrun D hD (r, ns) hi (rc_neverWrong_of_check hc.1 ns hn)
    · cases h

/-- **`RcReplay.sound` for a shaped root of any result shape, given that the tree view
reads the shape.** The reference-counted path reads first-order constructor trees
back, so a root may return a list or a tree. What is left as a hypothesis is `hview`:
the root's view accepts every value of the result shape. For `nat` it is
`rc_view_nat_ok`; for a data entry it is a statement about erasure (unboxing, kept
fields, constructor tags) at that entry, not proved here. -/
theorem rc_sound_of_shape {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a) {sig : Sig}
    (hsig : SigOk a.front.src sig) {r : Nat} {addr : Ixon.Address} {root : CId}
    (hroot : a.front.src.roots[r]? = some (addr, root)) (ns : List Nat) {ρ : Shape}
    (hc : sig.inst root [] (arrows (List.replicate ns.length .nat) ρ))
    (hview : ∀ v, ValOk a.front.src sig v ρ → a.front.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram a.front.src a.front.checked, v) :
        Lang.Val CheckedProgram)) ≠ none)
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) :=
  rc_sound_of_neverWrong h D hD (r, ns) hi
    (neverWrong_of_shape_view (view := a.front.view) hsig hroot ns hc hview)

end IxCC.Correct.Shape2
