import LSpec
import Ix.Meta
import Ix.LeanIngress
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.SourceIngressStep

/-! # Source evidence from the committed bundle (`kernel-bundle-evidence`)

Source mode's evidence for the well-founded `Nat` operations is the
certificate theorems of `IxC/Kernel/PinGen/Certs.lean`, closed. An input that
does not carry that module (the compiler's: Init, Std, Mathlib) takes them
from the committed bundle (`Ix.RoleEvidence.bundleEvidence`:
`RoleData.sourceEvidence`, theorem records whose references are names).

The bundle reads with no reason (`bundleEvidenceReport`), every well-founded
operation gets its certificate theorems in order under their names, and the
structural ones their `defeq` entries. Then the eight operations and what
they reach in `Init`, with no certificate theorem, are checked in Source mode
group by group: at the input's own evidence `Nat.div`, `Nat.mod` and
`Nat.shiftLeft` decline (no proof evidence; the control), at the bundle's
every operation is accepted; and all at once (`checkSourceWith`) at the
bundle's evidence. -/

namespace Tests.Ix.Kernel.BundleEvidence

open LSpec
open Tests.Ix.Kernel.SourceIngressStep (condense run)

/-- The operations whose specification takes evidence. -/
def operations : Array Lean.Name :=
  #[`Nat.div, `Nat.mod, `Nat.gcd, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight]

/-- The bundle's evidence: no reason, the structural operations' entries, and
each well-founded operation's theorems, in order, under their names. -/
def shape : TestSeq :=
  let (ev, why) := Ix.RoleEvidence.bundleEvidenceReport ()
  let structural := Ix.RoleEvidence.defeqRoles.all fun r =>
    ev.any fun (r', es) => r' == r && es.length == (Ix.RoleEvidence.defeqEvidence (K := Unit) r).length &&
      es.all (· == .defeq)
  let proved := Ix.RoleEvidence.certTheorems.all fun (r, thms) =>
    ev.any fun (r', es) => r' == r && es.length == thms.length &&
      (es.zip thms).all fun (e, t) => match e with
        | .proof (k, _) => k == Ix.RoleEvidence.ofLeanName t
        | .defeq => false
  test s!"the committed bundle reads ({why})" why.isEmpty $
  test "the structural operations: their defeq entries" structural $
  test "the well-founded operations: their certificate theorems, in order, by name" proved

/-- The operations' closure in `Init` (no certificate theorem), checked group
by group at the input's own evidence and at the bundle's, and all at once at
the bundle's. -/
def evaluate : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[`Init]
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv operations
  let blocks := condense env
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let own ← run pre env blocks
  let bundled ← run pre env blocks (evidence := some (Ix.RoleEvidence.bundleEvidence ()))
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  for n in operations do
    let k := Ix.Kernel.Key.ofName (Ix.Kernel.Name.ofLeanName n)
    let o := (own.rowOf k).map (·.outcome)
    let b := (bundled.rowOf k).map (·.outcome)
    lines := lines.push s!"{n}: input's evidence {o}, bundle's {b}"
    unless b == some "accept" do errors := errors.push s!"{n}: {b} at the bundle's evidence"
    let declinesWithout := n == `Nat.div || n == `Nat.mod || n == `Nat.shiftLeft
    if declinesWithout && o == some "accept" then
      errors := errors.push s!"{n}: accepted without evidence (the control)"
  lines := lines.push s!"closure: {env.consts.size} constants; input's evidence \
    {own.counts.constants.toList}, bundle's {bundled.counts.constants.toList}"
  match Ix.LeanIngress.checkSourceWith pre (Ix.RoleEvidence.bundleEvidence ()) env blocks with
  | .ok kenv => lines := lines.push s!"checkSourceWith at the bundle's evidence: accepted, \
      {kenv.consts.length} kernel constants"
  | .error e => errors := errors.push s!"checkSourceWith at the bundle's evidence: {e}"
  return (errors, lines)

def closureCheck : TestSeq :=
  .individualIO "the operations' Init closure, without certificates, at the bundle's evidence" none (do
    let (errors, lines) ← evaluate
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, operations.size, 0, msg)) .done

def suite : List TestSeq := [shape, closureCheck]

end Tests.Ix.Kernel.BundleEvidence
