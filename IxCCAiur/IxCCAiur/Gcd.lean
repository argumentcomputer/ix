import IxCCAiur.Instance
import IxCCTests.Recheck.Artifacts.Gcd

/-! # The `gcd` closure: an accepted claim, read at the source

The instance of `Instance.accepted_nat` for the K1 benchmark closure
`fixtures/ixon-v4/bench-k1/gcd.ixe` (root `entry : Nat → Nat → Nat`,
`K1.gcd`), on the Lean terms `IxCCTests.Recheck.Artifacts.Gcd.{program, cfg,
cert}`. As for `fib` (`IxCCAiur.Fib`), the kernel evaluates the front half and
the shape decision (`decision_gcd`), so the statement has no disjunct and no
hypothesis about the compiler's front half or about source progress. The
lowered `gcd` divides, so an accepted claim of it has gone through the
division helper and its advice (`Gadgets.divmod_sound`). -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Gcd

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim
open IxCCTests.Recheck.Artifacts.Gcd (program cfg cert)

set_option maxRecDepth 1000000 in
/-- **The kernel's evaluation of the decision on the `gcd` closure**
(`Instance.decision`): the front half accepts, root 0 declares two parameters,
and its checked source passes the shape decision on the certificate the
untrusted producer proposes. -/
theorem decision_gcd : Instance.decision 2 (Recheck.runFir cfg program cert) = true := by
  decide +kernel

/-- **SrcEval is stuck at no clock on `gcd`'s root**, on any two `Nat`
arguments. -/
theorem neverStuck {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    (a b : Nat) : NeverStuck ⟨f.src, f.checked⟩ (0, [a, b]) :=
  ((Instance.facts hf decision_gcd).2 [a, b] rfl).2

/-- **`gcd`: an accepted claim, read at the source.** If the checker accepts
the claim that `Prog::main0` on the field elements `a`, `b` returns
`Prog::Obj::N(y)`, then SrcEval on root 0 (`entry`) and the `Nat` arguments
`a.val`, `b.val` returns, at some clock, a value whose observation is the
`Nat` `y.val`. -/
theorem accepted {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {a b y : G}
    (acc : Accepted prepared 0 [.field a, .field b] (.construct objQName "N" [.field y])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [a.val, b.val]) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  Instance.accepted_nat hf decision_gcd hlow prepared hw (as := [a, b]) rfl acc

end IxCC.AiurBackend.Gcd
