import IxCCTests.Recheck.RootShape
import IxCC.CompileClaim
import IxCCTests.Support.Envelope

/-! Role-bound closures through the byte-level verifiers.

For two committed closures (every committed closure is role-bound, as
`ix compile` writes it) and the unbound envelope of the same records (the
closure without its binding, `Support.Envelope.unboundTwin`):
`CompileClaim.makeClaim` claims the root; `verifyBytes` and `checkClaim`
accept the claim on the role-bound bytes; the claims name the closures' root
(the same `H`, which covers the records only) and the role-bound claim its role
table, the unbound one none; the object, its hash, the target, the policy and
the arity are the same, byte for byte; and the role-bound bytes refuse a claim
naming no role table, the unbound bytes one naming the role table
(`IxCC/docs/byte-contract.md`). -/

namespace IxCCTests.Recheck.Bound

open IxCC
open IxCCTests.Src (Assert expect)

/-- Each role-bound closure and the root it compiles. -/
def closures : List (String × String × String) :=
  [("tuple", "fixtures/corpus/phase1-scalar/tuple", "entry"),
   ("fib", "fixtures/ixon-v4/bench-k1/fib", "entry")]

def run (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for (label, stem, root) in closures do
    let cfg : Recheck.Config := { names := [root] }
    let bb ← IO.FS.readBinFile s!"{stem}.ixe"
    let bj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
    let ub ← IxCCTests.Support.Envelope.unboundTwin s!"{stem}.ixe"
    let benv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bb)
    let uenv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv ub)
    let (bc, bcert, bobj) ← IO.ofExcept (CompileClaim.makeClaim cfg bb bj)
    let (uc, _, uobj) ← IO.ofExcept (CompileClaim.makeClaim cfg ub bj)
    expect a (benv.isBound && !uenv.isBound && bc.env == benv.root && uc.env == uenv.root &&
        bc.env == uc.env && bc.roleTable == benv.bindingAddress && bc.roleTable.isSome &&
        uc.roleTable.isNone)
      s!"{label}: the claims name the closures' root and the role-bound one its role table"
    expect a (CompileClaim.verifyBytes cfg bb bj bc bcert)
      s!"{label}: verifyBytes refused the role-bound claim"
    expect a ((CompileClaim.checkClaim cfg bb bj bc bcert).toOption.isSome)
      s!"{label}: checkClaim refused the role-bound claim"
    expect a (bobj == uobj && bc.elfHash == uc.elfHash && bc.target == uc.target &&
      bc.policy == uc.policy && bc.abiArity == uc.abiArity)
      s!"{label}: the role-bound closure compiled to another object than its unbound envelope"
    expect a (!CompileClaim.verifyBytes cfg bb bj { bc with roleTable := none } bcert &&
      !CompileClaim.verifyBytes cfg ub bj bc bcert)
      s!"{label}: a claim naming the other envelope's role table was accepted"
    lines := lines.push s!"{label}: root {benv.root}, role table {(bc.roleTable.map toString).getD "-"}, \
      object {bobj.size} bytes, the same unbound"
  return lines

end IxCCTests.Recheck.Bound
