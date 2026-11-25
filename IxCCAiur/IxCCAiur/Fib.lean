import IxCCAiur.Instance
import IxCCTests.Recheck.Artifacts.Fib

/-! # The `fib` closure: an accepted claim, read at the source

The instance of `Claim.accepted_nat_backward` for the K1 benchmark closure
`fixtures/ixon-v4/bench-k1/fib.ixe` (root `entry : Nat → Nat`, `K1.fib`).

The source program, the configuration and the producer's certificate are the
Lean terms `IxCCTests.Recheck.Artifacts.Fib.{program, cfg, cert}`
(`lake exe gen-recheck-artifacts` writes them from the committed closure and
checks them against it). On them the kernel evaluates the front half
(`Recheck.runFir`): it accepts, root 0 declares one parameter, and there is
one export (`summary_fib`). So nothing about the compiler's front half is a
hypothesis below, and every one-argument input is covered.

What the theorems still take as hypotheses is on the Aiur side, and is what
the driver computes natively when it writes a package (`IxCCAiur.Driver`):
that the lowering accepts the Fir program (`hlow`), a prepared Aiur program
(`prepared`) that passes the world check (`hw`), and the accepted claim
(`Claim.Accepted`). `accepted_sound` takes source progress on the input
(`Compose.NeverStuck`) as a hypothesis; `accepted` does not: the kernel also
evaluates the source-progress lane's shape decision on the checked source
(`decision_fib`), which gives it (`Progress.neverStuck_of_checkShape`). -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Fib

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim
open IxCCTests.Recheck.Artifacts.Fib (program cfg cert)

/-- What the instance needs of the front half's result: the declared
parameter count of root 0 and the number of exports. -/
def summary : Except Recheck.Err Recheck.FrontFir → Option (Option Nat × Nat)
  | .ok f =>
    some ((f.src.roots[0]?).bind (fun r => Recheck.declaredParams f.src r.2),
      f.fir.exports.length)
  | .error _ => none

set_option maxRecDepth 1000000 in
/-- **The kernel's evaluation of the front half on the `fib` closure**: it
accepts, root 0 declares one parameter, and the Fir program has one export. -/
theorem summary_fib : summary (Recheck.runFir cfg program cert) = some (some 1, 1) := by
  decide +kernel

/-- The front half accepts the `fib` closure. -/
theorem runFir_ok : ∃ f, Recheck.runFir cfg program cert = .ok f := by
  cases h : Recheck.runFir cfg program cert with
  | ok f => exact ⟨f, rfl⟩
  | error e =>
    have hs := summary_fib
    rw [h] at hs
    simp [summary] at hs

/-- What the front half made of `fib` has an export 0, and every
one-argument input of root 0 is covered. -/
theorem front {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f) :
    (∃ g, f.fir.exports[0]? = some g) ∧ ∀ x : Nat, f.Covered cert (0, [x]) := by
  have h := summary_fib
  rw [hf] at h
  simp only [summary, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hdecl, hlen⟩ := h
  refine ⟨?_, fun x => Or.inl ?_⟩
  · cases hex : f.fir.exports with
    | nil => rw [hex] at hlen; simp at hlen
    | cons g gs => exact ⟨g, rfl⟩
  · intro addr c hroot n hn
    have hroot' : f.src.roots[0]? = some (addr, c) := hroot
    rw [hroot'] at hdecl
    have h1 : Recheck.declaredParams f.src c = some 1 := hdecl
    have hn1 : n = 1 := Option.some.inj (hn.symm.trans h1)
    subst hn1
    rfl

/-- **`fib`: an accepted claim, read at the source (with the stuck-source
disjunct).** Let `f` be what the front half makes of the `fib` closure, `prog`
its lowering, and `prepared` a prepared Aiur program that passes the world
check for `prog`. If the checker accepts the claim that `Prog::main0` on the
field element `x` returns `Prog::Obj::N(y)`, then SrcEval on root 0 (`entry`)
and the `Nat` argument `x.val` returns, at some clock, a value whose
observation is the `Nat` `y.val`, **or SrcEval is stuck on that input**. -/
theorem accepted_backward {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {x y : G}
    (acc : Accepted prepared 0 [.field x] (.construct objQName "N" [.field y])) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [x.val]) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val)) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [x.val]) k = .stuck := by
  obtain ⟨⟨g, hexp⟩, hcov⟩ := front hf
  exact accepted_nat_backward hf hlow prepared hw hexp (as := [x]) acc (hcov x.val)

/-- **`fib`: an accepted claim, read at the source, under source progress on
the input.** As `accepted_backward`, where SrcEval is stuck at no clock on
`x.val` (`Compose.NeverStuck`, a hypothesis): SrcEval returns a value whose
observation is `y.val`. -/
theorem accepted_sound {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {x y : G}
    (acc : Accepted prepared 0 [.field x] (.construct objQName "N" [.field y]))
    (hp : NeverStuck ⟨f.src, f.checked⟩ (0, [x.val])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [x.val]) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  rcases accepted_backward hf hlow prepared hw acc with h | ⟨k, hk⟩
  · exact h
  · exact absurd hk (hp k)

/-! ## Without the escape -/

set_option maxRecDepth 1000000 in
/-- **The kernel's evaluation of the decision on the `fib` closure**
(`Instance.decision`): the front half accepts, root 0 declares one parameter,
and its checked source passes the shape decision on the certificate the
untrusted producer proposes. -/
theorem decision_fib : Instance.decision 1 (Recheck.runFir cfg program cert) = true := by
  decide +kernel

/-- **SrcEval is stuck at no clock on `fib`'s root**, on any `Nat` argument. -/
theorem neverStuck {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    (x : Nat) : NeverStuck ⟨f.src, f.checked⟩ (0, [x]) :=
  ((Instance.facts hf decision_fib).2 [x] rfl).2

/-- **`fib`: an accepted claim, read at the source.** Let `f` be what the front
half makes of the `fib` closure, `prog` its lowering, and `prepared` a prepared
Aiur program that passes the world check for `prog`. If the checker accepts
the claim that `Prog::main0` on the field element `x` returns
`Prog::Obj::N(y)`, then SrcEval on root 0 (`entry`) and the `Nat` argument
`x.val` returns, at some clock, a value whose observation is the `Nat`
`y.val`. No disjunct and no progress hypothesis (`decision_fib`). -/
theorem accepted {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {x y : G}
    (acc : Accepted prepared 0 [.field x] (.construct objQName "N" [.field y])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [x.val]) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  Instance.accepted_nat hf decision_fib hlow prepared hw (as := [x]) rfl acc

end IxCC.AiurBackend.Fib
