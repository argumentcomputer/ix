import IxCCAiur.Progress

/-! # One decision per closure

What the escape-free statement for a concrete closure needs of the compiler's
front half, as one Boolean on `Recheck.runFir`'s result (`decision`), so that
an instance is one kernel evaluation (`IxCCAiur.Fib`, `IxCCAiur.Gcd`):

* the front half accepts, and the Fir program has an export 0;
* root 0 declares exactly `n` parameters (so every `n`-argument input is
  covered, `Recheck.ExactDeclared`);
* root 0 passes the shape decision at `n` `Nat` arguments
  (`Progress.checkShape`) on the certificate the source-progress lane's
  untrusted producer proposes (`SrcShape.Produce.produce`).

`accepted_nat` is `Progress.accepted_nat` with those facts read off the
decision: for a closure whose decision holds, an accepted `Nat` claim of the
lowered entry is the value SrcEval returns. What remains hypotheses there is
on the Aiur side only (`lowerProgram`'s result, a prepared program that passes
the world check, the accepted claim). -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Instance

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim

/-- **The decision for root 0 at `n` `Nat` arguments**, on the front half's
result. -/
def decision (n : Nat) : Except Recheck.Err Recheck.FrontFir → Bool
  | .ok f =>
    (f.fir.exports[0]?).isSome &&
      match f.src.roots[0]? with
      | some (_, c) =>
        decide (Recheck.declaredParams f.src c = some n) &&
          Progress.checkShape f.src (SrcShape.Produce.produce f.src c) 0 n
      | none => false
  | .error _ => false

/-- **What the decision gives**: an export 0, and for every input of `n`
`Nat`s, that it is covered and that SrcEval is stuck on it at no clock. -/
theorem facts {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {n : Nat}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    (hd : decision n (Recheck.runFir cfg P c) = true) :
    (∃ g, f.fir.exports[0]? = some g) ∧
      ∀ ns : List Nat, ns.length = n →
        f.Covered c (0, ns) ∧ NeverStuck ⟨f.src, f.checked⟩ (0, ns) := by
  rw [hf] at hd
  simp only [decision, Bool.and_eq_true] at hd
  obtain ⟨hexp, hroot⟩ := hd
  cases hr : f.src.roots[0]? with
  | none => rw [hr] at hroot; simp at hroot
  | some ac =>
    obtain ⟨addr, c0⟩ := ac
    rw [hr] at hroot
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hroot
    obtain ⟨hdecl, hshape⟩ := hroot
    refine ⟨Option.isSome_iff_exists.mp hexp, fun ns hlen => ⟨Or.inl ?_, ?_⟩⟩
    · intro addr' c' hroot' m hm
      have hroot'' : f.src.roots[0]? = some (addr', c') := hroot'
      rw [hr] at hroot''
      cases hroot''
      rw [hdecl] at hm
      cases hm
      exact hlen
    · exact Progress.neverStuck_of_checkShape
        (cert := SrcShape.Produce.produce f.src c0) (by rw [hlen]; exact hshape)

/-- **An accepted `Nat` claim of a decided closure, read at the source.** If
the decision holds for the closure at `n` arguments and the checker accepts
the claim that `Prog::main0` on `n` field arguments `as` returns
`Prog::Obj::N(y)`, then SrcEval on root 0 and the `Nat` arguments
`as.map ZMod.val` returns, at some clock, a value whose observation is the
`Nat` `y.val`. No disjunct, no progress hypothesis, no coverage hypothesis. -/
theorem accepted_nat {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {n : Nat}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    (hd : decision n (Recheck.runFir cfg P c) = true)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {as : List G} (hlen : as.length = n) {y : G}
    (acc : Accepted prepared 0 (as.map Value.field) (.construct objQName "N" [.field y])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  obtain ⟨⟨g, hexp⟩, hall⟩ := facts hf hd
  obtain ⟨hcov, hns⟩ := hall (as.map ZMod.val) (by rw [List.length_map]; exact hlen)
  exact accepted_nat_sound hf hlow prepared hw hexp acc hcov hns

end IxCC.AiurBackend.Instance
