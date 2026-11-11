import IxCCTests.Recheck.RootShape
import IxCC.CompileClaim
import IxCCTests.Support.Envelope

/-! Role-bound closures through the byte-level verifiers.

For two committed closures (every committed closure is role-bound, as
`ix compile` writes it) and the unbound envelope of the same records (the
closure without its binding, `Support.Envelope.unboundTwin`):
`CompileClaim.makeClaim` claims the root of the role-bound bytes;
`verifyBytes` and `checkClaim` accept the claim; the claim names the closure's
root and its role table; and a claim naming no role table is refused. The
unbound envelope is refused at ingress, by the certified kernel, which admits
only role-bound environments (`ingress: kernel`, stage `envelope`): `makeClaim`
refuses it, and `verifyBytes` refuses the role-bound claim, and the claim
naming no role table, on it (`IxCC/docs/byte-contract.md`). -/

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
    expect a (benv.isBound && !uenv.isBound && bc.env == benv.root && uenv.root == benv.root &&
        bc.roleTable == benv.bindingAddress && bc.roleTable.isSome)
      s!"{label}: the claim names the closure's root and its role table"
    expect a (CompileClaim.verifyBytes cfg bb bj bc bcert)
      s!"{label}: verifyBytes refused the role-bound claim"
    expect a ((CompileClaim.checkClaim cfg bb bj bc bcert).toOption.isSome)
      s!"{label}: checkClaim refused the role-bound claim"
    -- the unbound envelope: refused at ingress by the kernel, as unbound
    let r := Recheck.ingress ub bj [root]
    expect a (match r with
      | .error e => e.stage == .ingress && e.code == "kernel" &&
          (e.message.splitOn "envelope").length > 1 && (e.message.splitOn "unbound").length > 1
      | .ok _ => false)
      s!"{label}: ingress did not refuse the unbound envelope as unbound: \
        {match r with | .error e => e.render | .ok _ => "accepted"}"
    expect a (CompileClaim.makeClaim cfg ub bj matches .error _)
      s!"{label}: makeClaim accepted the unbound envelope"
    let unboundClaim := { bc with roleTable := none }
    expect a (!CompileClaim.verifyBytes cfg bb bj unboundClaim bcert &&
      !CompileClaim.verifyBytes cfg ub bj bc bcert &&
      !CompileClaim.verifyBytes cfg ub bj unboundClaim bcert)
      s!"{label}: a claim naming no role table, or the unbound envelope, was accepted"
    lines := lines.push s!"{label}: root {benv.root}, role table {(bc.roleTable.map toString).getD "-"}, \
      object {bobj.size} bytes; the unbound envelope refused at ingress"
  return lines

end IxCCTests.Recheck.Bound
