import IxCCTests.Recheck.RootShape
import IxCC.CompileClaim

/-! Role-bound closures through the byte-level verifiers.

For each committed role-bound closure (`fixtures/ixon-v4/bound`, written by
`ix compile` with its role binding) and its unbound twin, the committed
fixture of the same source: `CompileClaim.makeClaim` claims the root;
`verifyBytes` and `checkClaim` accept the claim on the role-bound bytes; the
claim names the role-bound root; the object, its hash, the target, the policy
and the arity are the unbound twin's, byte for byte; the role-bound bytes
refuse a claim naming the unbound twin's root, and the unbound bytes one naming
the role-bound root (`IxCC/docs/byte-contract.md`). -/

namespace IxCCTests.Recheck.Bound

open IxCC
open IxCCTests.Src (Assert expect)

/-- Each role-bound closure, its unbound twin and the root they compile. -/
def pairs : List (String × String × String × String) :=
  [("tuple", "fixtures/ixon-v4/bound/tuple", "fixtures/corpus/phase1-scalar/tuple", "entry"),
   ("fib", "fixtures/ixon-v4/bound/fib", "fixtures/ixon-v4/bench-k1/fib", "entry")]

private def read (stem : String) : IO (ByteArray × Lean.Json) := do
  let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  return (bytes, json)

def run (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for (label, bound, unbound, root) in pairs do
    let cfg : Recheck.Config := { names := [root] }
    let (bb, bj) ← read bound
    let (ub, uj) ← read unbound
    let benv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bb)
    let uenv ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv ub)
    let (bc, bcert, bobj) ← IO.ofExcept (CompileClaim.makeClaim cfg bb bj)
    let (uc, _, uobj) ← IO.ofExcept (CompileClaim.makeClaim cfg ub uj)
    expect a (benv.isBound && !uenv.isBound && bc.env == benv.root && uc.env == uenv.root)
      s!"{label}: the claims name the closures' roots"
    expect a (CompileClaim.verifyBytes cfg bb bj bc bcert)
      s!"{label}: verifyBytes refused the role-bound claim"
    expect a ((CompileClaim.checkClaim cfg bb bj bc bcert).toOption.isSome)
      s!"{label}: checkClaim refused the role-bound claim"
    expect a (bobj == uobj && bc.elfHash == uc.elfHash && bc.target == uc.target &&
      bc.policy == uc.policy && bc.abiArity == uc.abiArity)
      s!"{label}: the role-bound closure compiled to another object than its unbound twin"
    expect a (benv.root != uenv.root &&
      !CompileClaim.verifyBytes cfg bb bj { bc with env := uenv.root } bcert &&
      !CompileClaim.verifyBytes cfg ub uj { bc with env := benv.root } bcert)
      s!"{label}: a claim naming the other envelope's root was accepted"
    lines := lines.push s!"{label}: role-bound root {benv.root}, unbound root {uenv.root}, \
      object {bobj.size} bytes, the same"
  return lines

end IxCCTests.Recheck.Bound
