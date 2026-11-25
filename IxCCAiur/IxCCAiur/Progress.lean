import IxCCAiur.Claim
import IxCCCorrect.Shape2Produce

/-! # Source progress from the shape check, and accepted claims without the escape

`Compose` and `Claim` end with "the source evaluator returns that value, **or
is stuck on that input**", and remove the second disjunct under
`Compose.NeverStuck`. This file supplies `NeverStuck` from the source-progress
lane's shape check (`IxCCCorrect.Shape2`, `Shape2Check`):

* `neverStuck_of_sigOk`: `Shape2.run_ok` (a shaped root on `Nat` arguments
  times out or returns a value of its result shape) read at the language's
  `run`. No view and no readback type enter: the claim's result is read by
  `Claim.result_nat`, not by the native roots' view.
* `checkShape src cert r n`: the lane's decision `Shape2.certOk` on a shape
  certificate, and the certificate lists an instance of root `r`'s constant
  at no levels that takes `n` `Nat` arguments. `neverStuck_of_checkShape` is
  its soundness. The certificate is untrusted (`Shape2.Produce.produce`
  proposes one).
* `accepted_nat`, `accepted_enum`: an accepted claim, read at the source,
  **with no disjunct**: SrcEval returns that value.

`checkShape` is a Boolean on the checked source, like `World.checkWorld` on
the prepared Aiur source. Where the kernel evaluates it (`IxCCAiur.Fib`) it is
a theorem; otherwise it is a fact the driver computes natively. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Progress

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim
open IxCC.Correct.Shape2 (Shape arrows SigOk)

/-! ## The bridge -/

/-- **A shaped root is stuck at no clock on `Nat` arguments.** The
source-progress lane's `Shape2.run_ok`, read at the checked source's `run`
(`Lam.Erase.Proof.srcRun`): the unviewed, per-input statement the circuit
route needs. -/
theorem neverStuck_of_sigOk {src : Src.Program} {ch : Src.Relevance.Checked}
    {sig : Correct.Shape2.Sig} (hsig : SigOk src sig)
    {r : Nat} {addr : Ixon.Address} {c : Src.CId} (hroot : src.roots[r]? = some (addr, c))
    (ns : List Nat) {ρ : Shape}
    (hc : sig.inst c [] (arrows (List.replicate ns.length .nat) ρ)) :
    NeverStuck ⟨src, ch⟩ (r, ns) := by
  intro k
  have e : Sem.Lang.run (⟨src, ch⟩ : CheckedProgram) (r, ns) k =
      IxCC.Lam.Erase.Proof.srcRun ⟨src, ch⟩ (r, ns) k := rfl
  unfold IxCC.Lam.Erase.Proof.srcRun at e
  simp only [hroot] at e
  rcases Correct.Shape2.run_ok hsig ns hc k with hr | ⟨v, hr, _⟩
  · rw [hr] at e
    rw [e]
    simp [Sem.Result.map, Sem.Result.bind]
  · rw [hr] at e
    rw [e]
    simp [Sem.Result.map, Sem.Result.bind]

/-! ## The decision -/

/-- The result shape of `σ` after `n` `Nat` arguments, if `σ` takes them. -/
def resultAfter : Nat → Shape → Option Shape
  | 0, σ => some σ
  | n + 1, .fn .nat τ => resultAfter n τ
  | _ + 1, _ => none

theorem resultAfter_sound : ∀ (n : Nat) (σ ρ : Shape), resultAfter n σ = some ρ →
    σ = arrows (List.replicate n .nat) ρ
  | 0, σ, ρ, h => by
    simp only [resultAfter, Option.some.injEq] at h
    subst h
    rfl
  | n + 1, .fn .nat τ, ρ, h => by
    simp only [resultAfter] at h
    have hτ := resultAfter_sound n τ ρ h
    subst hτ
    rfl
  | _ + 1, .fn (.enum _) _, _, h => by simp [resultAfter] at h
  | _ + 1, .fn (.data _) _, _, h => by simp [resultAfter] at h
  | _ + 1, .fn .irr _, _, h => by simp [resultAfter] at h
  | _ + 1, .fn (.fn _ _) _, _, h => by simp [resultAfter] at h
  | _ + 1, .nat, _, h => by simp [resultAfter] at h
  | _ + 1, .enum _, _, h => by simp [resultAfter] at h
  | _ + 1, .data _, _, h => by simp [resultAfter] at h
  | _ + 1, .irr, _, h => by simp [resultAfter] at h

/-- **The shape decision for root `r` on `n` `Nat` arguments**: the
certificate passes the source-progress lane's check on the program
(`Shape2.certOk`), and it lists an instance of the root's constant at no
levels whose shape takes `n` `Nat` arguments. -/
def checkShape (src : Src.Program) (cert : Correct.Shape2.Cert) (r n : Nat) : Bool :=
  Correct.Shape2.certOk src cert &&
    match src.roots[r]? with
    | some (_, c) => cert.insts.any fun e =>
        decide (e.1 = c) && decide (e.2.1 = ([] : Src.Levels)) && (resultAfter n e.2.2).isSome
    | none => false

/-- **The shape decision is sound for progress**: a root that passes it is
stuck at no clock on any `n` `Nat` arguments. -/
theorem neverStuck_of_checkShape {src : Src.Program} {ch : Src.Relevance.Checked}
    {cert : Correct.Shape2.Cert} {r : Nat} {ns : List Nat}
    (h : checkShape src cert r ns.length = true) : NeverStuck ⟨src, ch⟩ (r, ns) := by
  unfold checkShape at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hcert, hroot⟩ := h
  cases hr : src.roots[r]? with
  | none => rw [hr] at hroot; simp at hroot
  | some ac =>
    obtain ⟨addr, c⟩ := ac
    rw [hr] at hroot
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Option.isSome_iff_exists] at hroot
    obtain ⟨e, hmem, ⟨hc, hls⟩, ρ, hρ⟩ := hroot
    obtain ⟨c', ls, σ⟩ := e
    have hc : c' = c := hc
    have hls : ls = [] := hls
    have hσ : σ = arrows (List.replicate ns.length .nat) ρ := resultAfter_sound _ _ _ hρ
    subst hc hls hσ
    exact neverStuck_of_sigOk (sig := cert.sig) (Correct.Shape2.sigOk_of_cert hcert) hr ns hmem

/-! ## Accepted claims without the escape -/

/-- **An accepted `Nat` claim, read at the source.** If the checker accepts
the claim that `Prog::main<i>` on the field arguments `as` returns
`Prog::Obj::N(y)`, and root `i` passes the shape decision at that many
arguments, then on the `Nat` arguments `as.map ZMod.val` SrcEval returns, at
some clock, a value whose observation is the `Nat` `y.val`. -/
theorem accepted_nat {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : Correct.Shape2.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  accepted_nat_sound hf hlow prepared hw hexp acc hcov
    (neverStuck_of_checkShape (ns := as.map ZMod.val) (by rw [List.length_map]; exact hshape))

/-- **An accepted enumeration claim, read at the source**, with no disjunct. -/
theorem accepted_enum {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct objQName (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : Correct.Shape2.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid []) :=
  accepted_enum_sound hf hlow prepared hw hexp hget hkey acc hcov
    (neverStuck_of_checkShape (ns := as.map ZMod.val) (by rw [List.length_map]; exact hshape))

end IxCC.AiurBackend.Progress
