import Tests.Ix.IxonV4
import Tests.Ix.ResourceAddressed
import Tests.Ix.IxVM.TagN

/-!
# The IxVM program's Ixon codec and claim boundary

The VM half of `ixon-v4-tests`, which the legacy suite ran through test-only
codec entry points: the program reads expressions and constants as the host
does, and refuses the claim bytes the host refuses.

Expressions are read as a constant's type (`TagN.rewrite .type`) and constants
whole, through the differential of `Tests.Ix.IxVM.TagN`: when the host reads
the constant, a `Reveal` of every field it read must be accepted (so the
program re-encodes each expression to the host's bytes); when the host refuses
it, the program must too. The vectors are `ixon-v4-tests`': the golden
expressions with a trailing byte and every truncation, the rejected
expressions, counted lists cut short, and hand-written declarations of every
kind.

The claim boundary: a check, check-env, reveal and contains claim, each
accepted as built and as rewritten unchanged, and refused with a trailing byte,
truncated, under another object format or validator, and (the typing claims)
with the retired validator, another specification or further axioms; a
catalog claim has no arm; and the retired resource claim is refused. The fixture's hand-built
records get their binder-data sections first, as the compiler writes them
(`withRecordSections`), so a claim is decided by its bytes, not by a missing
section.
-/

namespace Tests.Ix.IxVM.Codec

open Tests.Ix.IxVM TagN

/-- An expression's case: its bytes as a constant's type. -/
def expression (label : String) (bytes : ByteArray) : Builder :=
  differential label (rewrite .type bytes)

/-- A golden expression, with a trailing byte and every truncation. -/
def encodingCases (name : String) (bytes : ByteArray) (embed : String → ByteArray → Builder) :
    Array Builder :=
  #[embed s!"codec {name}" bytes, embed s!"codec {name} with a trailing byte" (bytes.push 0)] ++
    (List.range bytes.size).toArray.map fun n =>
      embed s!"codec {name} cut to {n} bytes" (bytes.extract 0 n)

/-- Counted lists cut short: each list holds one complete element, then the
stream ends, under a count of 1 (accepted), 2, 128 (a two-byte count) and the
largest `UInt64`. -/
def countCases : Array Builder := Id.run do
  let mut out := #[]
  for count in [1, 2, 128, (2 ^ 64 - 1 : Nat)] do
    let accept := count == 1
    let tag0 : ByteArray := Ixon.runPut (Ixon.putTagN 0 0 count.toUInt64)
    let tag4 (flag : UInt8) : ByteArray := Ixon.runPut (Ixon.putTagN 4 flag count.toUInt64)
    let finish (bytes tail : ByteArray) := if accept then bytes ++ tail else bytes
    let countLabel := if count == 2 ^ 64 - 1 then "max-u64" else toString count
    for (label, bytes) in [
        ("ref-universes", tag4 2 ++ .mk #[0, 0]),
        ("rec-universes", tag4 3 ++ .mk #[0, 0]),
        ("app-arguments", tag4 7 ++ .mk #[0x10, 0x10]),
        ("lambda-binders", finish (tag4 8 ++ .mk #[0x00]) (.mk #[0x10])),
        ("forall-binders", finish (tag4 9 ++ .mk #[0x00]) (.mk #[0x10]))] do
      out := out.push (expression s!"codec count {label}-{countLabel}" bytes)
    let axiomPrefix : ByteArray := .mk #[0xd2, 0, 0, 0]
    for (label, bytes) in [
        ("sharing", finish (axiomPrefix ++ tag0 ++ .mk #[0x10]) (.mk #[0, 0])),
        ("references", finish (axiomPrefix ++ .mk #[0] ++ tag0 ++
          .mk (Array.replicate 32 0)) (.mk #[0])),
        ("universes", axiomPrefix ++ .mk #[0, 0] ++ tag0 ++ .mk #[0]),
        ("recursor-rules", finish (.mk #[0xd1, 0, 0, 0, 0, 0, 0, 0] ++
          tag0 ++ .mk #[0, 0x10]) (.mk #[0, 0, 0])),
        ("constructors", finish (.mk #[0xc1, 1, 0, 0, 0, 0, 0] ++
          tag0 ++ .mk #[0, 0, 0, 0, 0, 0]) (.mk #[0, 0, 0])),
        ("mutual-members", finish (tag4 12 ++ .mk #[0, 0x06, 0x05, 0x00, 0x10])
          (.mk #[0, 0, 0]))] do
      out := out.push (differential s!"codec count {label}-{countLabel}" bytes)
  return out

/-- Independently authored declaration bytes for the six headers. -/
def declarations : List (String × String) := [
  ("definition", "d006050010000000"),
  ("recursor", "d101050102030400010310000000"),
  ("axiom", "d2010500000000"),
  ("quotient", "d3020500000000"),
  ("mutual", "c101000502030001010501020300000000")]

/-- `witness` with its claim replaced by `bytes`. -/
def replaceClaimBytes (witness : IxVM.ClaimHarness.ClaimWitness) (bytes : ByteArray) :
    IxVM.ClaimHarness.ClaimWitness :=
  let key := IxVM.ClaimHarness.packedDigestKey (Address.blake3 bytes)
  { witness with
    input := key
    inputIOBuffer := witness.inputIOBuffer.extend 0 key (bytes.data.map .ofUInt8) }

/-- The claim-boundary cases. -/
def claimCases (r : Runner) : IO Unit := do
  let (base, unit) := Tests.ResourceAddressed.unitEnv
  let constant := Tests.ResourceAddressed.identity unit
  let (env, validTarget) := Tests.ResourceAddressed.store base constant
  let env := { env with anonHints := env.anonHints.insert validTarget .opaque }
  let some tree := IxVM.ClaimHarness.envCanonicalTree env
    | throw <| IO.userError "the claim fixture has no tree"
  let trees := ({} : Std.HashMap Address Ix.AssumptionTree).insert tree.root tree
  let ctx ← IO.ofExcept Ix.ClaimContext.ofDefaultTable
  let revealedType := Address.blake3 (Ixon.runPut (Ixon.putExpr (.all (.ref 0 #[]) (.ref 0 #[]))))
  let add (label : String) (witness : IxVM.ClaimHarness.ClaimWitness) (accept : Bool)
      (rejectsWith : Option String := none) : IO Unit :=
    r.add { label := s!"claim boundary {label}", accept, rejectsWith, witness }
  for (name, original) in [
      ("check", Ix.Claim.check ctx validTarget none),
      ("check-env", .checkEnv ctx tree.root none),
      ("reveal", .reveal validTarget (.defn none none none (some revealedType) none)),
      ("contains", .contains tree.root validTarget)] do
    let (cenv, claim, ctrees) ← IO.ofExcept (withRecordSections env original trees)
    let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness cenv claim ctrees)
    add name witness true
    let bytes := Ix.Claim.ser claim
    -- Positive control: the unchanged bytes, through the same replacement as
    -- the mutations, are accepted, so a broken replacement cannot make every
    -- mutation pass vacuously.
    add s!"{name}-identity" (replaceClaimBytes witness bytes) true
    -- Byte 1 is the object format: exactly `Ixon.Env.OBJECT_FORMAT` (4).
    for (mutation, bad, reason) in [
        ("trailing", bytes.push 0, "let pattern mismatch"),
        ("legacy-version", bytes.set! 1 (Ixon.Env.OBJECT_FORMAT - 1), "unsupported object format"),
        ("future-version", bytes.set! 1 (Ixon.Env.OBJECT_FORMAT + 1), "unsupported object format"),
        ("wrong-validator", bytes.set! 2 255, "wrong validator identity"),
        ("truncated", bytes.extract 0 (bytes.size - 1), "let pattern mismatch")] do
      add s!"{name}-{mutation}" (replaceClaimBytes witness bad) false reason
    -- A typing claim's context: the retired validator, another specification
    -- digest, and an axiom set beyond the standard three are each refused.
    if name == "check" || name == "check-env" then
      for (mutation, bad, reason) in [
          ("retired-validator", bytes.set! 2 1, "wrong validator identity"),
          ("other-specification", bytes.set! 3 (bytes[3]! ^^^ 1),
            "specification digest is not this circuit's")] do
        add s!"{name}-{mutation}" (replaceClaimBytes witness bad) false reason
      -- The axiom set (the target, which is no axiom) is seeded with the claim,
      -- so the refusal is the axiom policy's rather than a missing tree.
      let some axioms := Ix.AssumptionTree.canonical #[validTarget]
        | throw <| IO.userError "the axiom fixture has no tree"
      let further := match original with
        | .check c t a => .check { c with axioms := some axioms.root } t a
        | .checkEnv c root a => .checkEnv { c with axioms := some axioms.root } root a
        | other => other
      let (fenv, further, ftrees) ← IO.ofExcept
        (withRecordSections env further (trees.insert axioms.root axioms))
      add s!"{name}-further-axioms" (← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness fenv
        further ftrees)) false "axioms tree entry is not an axiom"
    -- A catalog claim has no circuit arm: catalogs are verified by host or
    -- aggregate composition, never by `run_claim`.
    if name == "check" then
      add "catalog-no-arm" (replaceClaimBytes witness (Ix.Claim.ser (.catalog tree.root))) false
        "no matching arm"
      -- The retired resource claim's tag and scope (`E8 01`, validator 2) are refused.
      add "resource-retired" (replaceClaimBytes witness
        (ByteArray.mk #[0xE8, 0x01, Ixon.Env.OBJECT_FORMAT, 2] ++ tree.root.hash ++ tree.root.hash)) false

def run : IO UInt32 := do
  let golden ← Tests.IxonV4.readExprCases
  withRunner "ixvm-codec" fun r => do
    for c in golden do
      for build in encodingCases c.name c.bytes expression do r.build (build ())
    for (name, bytes) in Tests.IxonV4.rejectedExprCases do
      r.build (expression s!"codec rejects {name}" bytes ())
    for build in countCases do r.build (build ())
    for (name, hex) in declarations do
      let some bytes := bytesOfHex hex
        | throw <| IO.userError s!"invalid declaration fixture hex: {name}"
      for build in encodingCases s!"declaration {name}" bytes differential do r.build (build ())
    claimCases r

end Tests.Ix.IxVM.Codec
