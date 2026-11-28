import IxCCAiur.Instance
import IxCCTests.Recheck.Artifacts.EvenOdd
import IxCCTests.Recheck.Artifacts.Sfib
import IxCCTests.Recheck.Artifacts.Tak

/-! # Three more K1 closures: accepted claims, read at the source

The instances of `Instance.accepted_nat` for the K1 benchmark closures
`even-odd` (`Nat → Nat`), `sfib` (`Nat → Nat`) and `tak`
(`Nat → Nat → Nat → Nat → Nat`), on the Lean terms
`IxCCTests.Recheck.Artifacts.{EvenOdd, Sfib, Tak}`, as `IxCCAiur.Fib` and
`IxCCAiur.Gcd`: for each, the kernel evaluates the front half and the shape
decision, and the statement has no disjunct and no progress hypothesis.

These are the K1 roots that have both a generated artifact and a shape
certificate the source-progress lane's decision accepts. `ackermann` passes
the decision but has no artifact module; `collatz`, `prime-count` and
`sum-loop` lower and run, and the decision refuses them (they keep the
disjunct, `Claim.accepted_nat_backward`). -/

set_option autoImplicit false

namespace IxCC.AiurBackend.EvenOdd

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim
open IxCCTests.Recheck.Artifacts.EvenOdd (program cfg cert)

set_option maxRecDepth 1000000 in
/-- **The kernel's evaluation of the decision on the `even-odd` closure**
(`Instance.decision` at one argument). -/
theorem decision : Instance.decision 1 (Recheck.runFir cfg program cert) = true := by
  decide +kernel

/-- **`even-odd`: an accepted claim, read at the source**, with no disjunct. -/
theorem accepted {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {x y : G}
    (acc : Accepted prepared 0 [.field x] (.construct objQName "N" [.field y])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [x.val]) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  Instance.accepted_nat hf decision hlow prepared hw (as := [x]) rfl acc

end IxCC.AiurBackend.EvenOdd

namespace IxCC.AiurBackend.Sfib

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim
open IxCCTests.Recheck.Artifacts.Sfib (program cfg cert)

set_option maxRecDepth 1000000 in
/-- **The kernel's evaluation of the decision on the `sfib` closure**
(`Instance.decision` at one argument). -/
theorem decision : Instance.decision 1 (Recheck.runFir cfg program cert) = true := by
  decide +kernel

/-- **`sfib`: an accepted claim, read at the source**, with no disjunct. -/
theorem accepted {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {x y : G}
    (acc : Accepted prepared 0 [.field x] (.construct objQName "N" [.field y])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [x.val]) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  Instance.accepted_nat hf decision hlow prepared hw (as := [x]) rfl acc

end IxCC.AiurBackend.Sfib

namespace IxCC.AiurBackend.Tak

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Compose IxCC.AiurBackend.Claim
open IxCCTests.Recheck.Artifacts.Tak (program cfg cert)

set_option maxRecDepth 1000000 in
/-- **The kernel's evaluation of the decision on the `tak` closure**
(`Instance.decision` at four arguments). -/
theorem decision : Instance.decision 4 (Recheck.runFir cfg program cert) = true := by
  decide +kernel

/-- **`tak`: an accepted claim, read at the source**, with no disjunct. -/
theorem accepted {f : Recheck.FrontFir} (hf : Recheck.runFir cfg program cert = .ok f)
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram f.fir = .ok prog)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : World.checkWorld prepared.environment.source prog = true)
    {a b c d y : G}
    (acc : Accepted prepared 0 [.field a, .field b, .field c, .field d] (.construct objQName "N" [.field y])) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (0, [a.val, b.val, c.val, d.val]) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  Instance.accepted_nat hf decision hlow prepared hw (as := [a, b, c, d]) rfl acc

end IxCC.AiurBackend.Tak

