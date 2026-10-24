import LSpec
import Ix.Meta
import Ix.LeanIngress
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.SourceIngressStep
import Tests.Ix.AuxGen.FlatBlockSource

/-! # Source evidence from the committed bundle (`kernel-bundle-evidence`, `bundle-evidence-initstd`)

Source mode's evidence for the well-founded `Nat` operations is the
certificate theorems of `IxC/Kernel/PinGen/Certs.lean`, closed. An input that
does not carry that module (the compiler's: Init, Std, Mathlib, and so
AuxGen's Source service) takes them from the committed bundle
(`Ix.RoleEvidence.bundleEvidence`: `RoleData.sourceEvidence`, theorem records
whose references are names).

* `kernel-bundle-evidence` (primary): the bundle reads with no reason
  (`bundleEvidenceReport`), every well-founded operation gets its certificate
  theorems in order under their names, and the structural ones their `defeq`
  entries. Then the eight operations and what they reach in `Init`, with no
  certificate theorem, are checked in Source mode group by group: at the
  input's own evidence `Nat.div`, `Nat.mod` and `Nat.shiftLeft` decline (no
  proof evidence; the control), at the bundle's every operation is
  accepted; and all at once (`checkSourceWith`) at the bundle's evidence.
* `bundle-evidence-initstd` (manual, about 1 min): AuxGen's Source service
  (`Ix.AuxGen.Source.Service`) over Init+Std without the certificate module,
  created at the input's own evidence and at the bundle's. For each
  inductive block, in dependency order, the service folds the block's groups
  and what they depend on (`ensureNames`), as AuxGen M1's projection
  (`auxgen-flat-initstd`) does: printed, the blocks whose own groups are
  accepted and the groups refused or blocked; asserted, every block's groups
  accepted at the bundle's evidence and no group refused. -/

namespace Tests.Ix.Kernel.BundleEvidence

open LSpec
open Tests.Ix.Kernel.SourceIngressStep (canon condense run)

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

/-! ## AuxGen's Source service on Init+Std -/

def workers : Nat := 32

/-- The service at evidence `ev` (the input's own when `none`): per inductive
block, its groups folded; the blocks whose own groups are accepted, the
group counts, and the reasons. -/
def measure (pre : Ix.Kernel.Reader.Prelude .source) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) (ev : Option (Ix.Kernel.Evidences .source)) :
    IO (Nat × Nat × (Nat × Nat × Nat × Nat) × Array String) := do
  let mut svc ← IO.lazyPure fun _ =>
    Ix.AuxGen.Source.Service.create pre env blocks (workers := workers) (evidence := ev)
  let mut n := 0
  let mut own := 0
  let mut why : Std.HashMap String Nat := {}
  for (_, members) in Tests.Ix.AuxGen.FlatBlockSource.inductiveBlocks env blocks do
    n := n + 1
    svc ← IO.lazyPure fun _ => svc.ensureNames members
    if members.all fun m => (svc.statusOf? m).any (·.isAccepted) then own := own + 1
    else
      let w := (members.findSome? fun m => match svc.statusOf? m with
        | some (.refused r) => some (r.take 90).toString
        | some (.blocked _) => some "blocked"
        | _ => none).getD "?"
      why := why.insert w (why.getD w 0 + 1)
  let mut lines : Array String := #[]
  for (w, k) in (why.toArray.qsort fun a b => a.2 > b.2).extract 0 8 do
    lines := lines.push s!"  block not accepted ({k}): {w}"
  for (st, i) in svc.status.zipIdx do
    if let .refused w := st then
      lines := lines.push s!"  group refused: {svc.graph.groups[i]!.name}: {(w.take 120).toString}"
  return (n, own, svc.counts, lines)

def runInitStd : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let leanEnv ← getCompileEnv #[`Init, `Std]
  let env ← IO.lazyPure fun _ => canon leanEnv.constants.toList.toArray workers
  let blocks ← IO.lazyPure fun _ => condense env (parallel := true)
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let t1 ← IO.monoMsNow
  IO.println s!"[bundle-evidence-initstd] Init+Std, no certificate module: {env.consts.size} \
    constants; load, canon and condense {t1 - t0} ms"
  let mut ok := true
  let settings : List (String × Option (Ix.Kernel.Evidences .source)) :=
    [("the input's evidence", none), ("the bundle's evidence", some (Ix.RoleEvidence.bundleEvidence ()))]
  for (label, ev) in settings do
    let s ← IO.monoMsNow
    let (n, own, (pending, acc, ref, blk), lines) ← measure pre env blocks ev
    IO.println s!"[bundle-evidence-initstd] {label}: inductive blocks {n}, own groups accepted \
      {own}; groups folded {acc} accepted, {ref} refused, {blk} blocked, {pending} never asked \
      for; {(← IO.monoMsNow) - s} ms"
    for l in lines do IO.println s!"[bundle-evidence-initstd] {l}"
    if ev.isSome && (own != n || ref != 0 || blk != 0) then ok := false
  IO.println s!"[bundle-evidence-initstd] {if ok then "PASS" else "FAIL"}"
  return if ok then 0 else 1

end Tests.Ix.Kernel.BundleEvidence
