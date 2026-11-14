import Ix.Commit
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
      ("reveal", .reveal validTarget (.defn none none none (some revealedType) none none) none),
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

/-- Reveal mode-commitment cases: definition `asserts`, constructor
`fieldModes` (both all-inherited `#[]` and listed), `binders` section address
(`none` and `some`), and malformed wire bytes. -/
def revealModeCases (r : Runner) : IO Unit := do
  let add (label : String) (witness : IxVM.ClaimHarness.ClaimWitness) (accept : Bool)
      (rejectsWith : Option String := none) : IO Unit :=
    r.add { label := s!"reveal mode {label}", accept, rejectsWith, witness }

  -- 1. Standalone definition with non-default `asserts` and moded `binders`.
  let defBinders : Array Ixon.BinderBlock := #[
    ⟨false, 0, 0, #[.zero ⟨.unique, .unique⟩]⟩,
    ⟨false, 1, 0, #[.zero ⟨.once, .shared⟩]⟩]
  let defConst : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, ⟨.noAlloc, true⟩, 0, .all (.sort 0) (.var 0), .lam (.sort 0) (.var 0)⟩,
     #[], #[], #[.zero], defBinders⟩
  let (envDef, defAddr) := Exploits.storeAt {} defConst
  let envDef ← IO.ofExcept (bare envDef)
  let defSecAddr := Ix.Commit.sectionAddr defBinders
  let wrongAddr := Address.blake3 "wrong-section".toUTF8

  for (label, claim, accept, reason) in [
      ("defn-asserts-binders-none",
       Ix.Claim.reveal defAddr (.defn none none none none none (some ⟨.noAlloc, true⟩)) none,
       true, none),
      ("defn-asserts-binders-some",
       .reveal defAddr (.defn none none none none none (some ⟨.noAlloc, true⟩)) (some defSecAddr),
       true, none),
      ("defn-wrong-alloc",
       .reveal defAddr (.defn none none none none none (some ⟨.noRc, true⟩)) none,
       false, some "claimed definition asserts != real"),
      ("defn-wrong-bounded-stack",
       .reveal defAddr (.defn none none none none none (some ⟨.noAlloc, false⟩)) none,
       false, some "claimed definition asserts != real"),
      ("defn-wrong-binders-addr",
       .reveal defAddr (.defn none none none none none none) (some wrongAddr),
       false, some "claimed binder section hash != hash of the real section")] do
    let w ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness envDef claim)
    add label w accept reason

  -- 2. Empty binder-data section (`#[]`) committed via `sectionAddr #[]`.
  let axConst : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero], #[]⟩
  let (envAx, axAddr) := Exploits.storeAt {} axConst
  let envAx ← IO.ofExcept (bare envAx)
  let emptySecAddr := Ix.Commit.sectionAddr #[]
  add "empty-binders-some"
    (← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness envAx
      (.reveal axAddr (.axio none none none) (some emptySecAddr)))) true
  add "empty-binders-mismatch"
    (← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness envAx
      (.reveal axAddr (.axio none none none) (some defSecAddr)))) false
    (some "claimed binder section hash != hash of the real section")

  -- 3. Mutual block with inductive constructors (ctor 0 inherited `#[]`,
  --    ctor 1 listed `#[.inherited, .shared]`) and a mutual definition with `asserts`.
  let ctor0 : Ixon.Constructor :=
    { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 2
      fieldModes := .inherited, typ := .sort 0 }
  let ctor1 : Ixon.Constructor :=
    { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 2
      fieldModes := Ixon.FieldModes.ofArray #[.inherited, .shared], typ := .sort 0 }
  let indInfo : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0
      typ := .sort 0, ctors := #[ctor0, ctor1] }
  let mutDef : Ixon.Definition := ⟨.defn, .safe, ⟨.noRc, true⟩, 0, .sort 0, .sort 0⟩
  let mutConst : Ixon.Constant :=
    ⟨.muts #[.indc indInfo, .defn mutDef], #[], #[], #[.zero], #[]⟩
  let (envMut, mutAddr) := Exploits.storeAt {} mutConst
  let envMut ← IO.ofExcept (bare envMut)
  let ctorReveal (cidx : UInt64) (modes : Array Ixon.FieldMode) : Ix.RevealConstantInfo :=
    .muts #[(0, .indc none none none none none (some #[(cidx, { fieldModes := some modes })]))]

  for (label, info, accept, reason) in [
      ("ctor-inherited-empty", ctorReveal 0 #[], true, none),
      ("ctor-inherited-rejects-explicit-inherited", ctorReveal 0 #[.inherited, .inherited],
       false, some "KernelClaim::check_field_modes"),
      ("ctor-inherited-rejects-shared", ctorReveal 0 #[.inherited, .shared],
       false, some "KernelClaim::check_field_modes"),
      ("ctor-listed-exact", ctorReveal 1 #[.inherited, .shared], true, none),
      ("ctor-listed-rejects-empty", ctorReveal 1 #[],
       false, some "KernelClaim::check_field_modes"),
      ("ctor-listed-rejects-swapped", ctorReveal 1 #[.shared, .inherited],
       false, some "claimed constructor field mode != real"),
      ("ctor-listed-rejects-short", ctorReveal 1 #[.inherited],
       false, some "KernelClaim::check_field_modes"),
      ("ctor-listed-rejects-long", ctorReveal 1 #[.inherited, .shared, .inherited],
       false, some "KernelClaim::check_field_modes"),
      ("mut-defn-asserts-exact",
       .muts #[(1, .defn none none none none none (some ⟨.noRc, true⟩))], true, none),
      ("mut-defn-asserts-wrong",
       .muts #[(1, .defn none none none none none (some ⟨.unrestricted, true⟩))],
       false, some "claimed definition asserts != real")] do
    let w ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness envMut (.reveal mutAddr info none))
    add label w accept reason

  -- 4. Raw malformed reveal claim wire bytes must be rejected by the circuit.
  let baseDefWitness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness envDef
    (.reveal defAddr (.defn none none none none none none) none))
  let baseMutWitness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness envMut
    (.reveal mutAddr (.muts #[]) none))
  let defHeader : ByteArray := ByteArray.mk #[0xE6, Ixon.Env.OBJECT_FORMAT, 0x00] ++ defAddr.hash
  let mutHeader : ByteArray := ByteArray.mk #[0xE6, Ixon.Env.OBJECT_FORMAT, 0x00] ++ mutAddr.hash
  for (label, baseW, rawBytes, reason) in [
      ("wire-defn-mask-64", baseDefWitness,
       defHeader ++ ByteArray.mk #[0x00, 0x40, 0x00],
       "claim: reveal defn mask out of range"),
      ("wire-defn-asserts-3", baseDefWitness,
       defHeader ++ ByteArray.mk #[0x00, 0x20, 0x03, 0x00],
       "KernelClaim::get_opt_def_asserts_masked"),
      ("wire-defn-asserts-7", baseDefWitness,
       defHeader ++ ByteArray.mk #[0x00, 0x20, 0x07, 0x00],
       "KernelClaim::get_opt_def_asserts_masked"),
      ("wire-defn-asserts-8", baseDefWitness,
       defHeader ++ ByteArray.mk #[0x00, 0x20, 0x08, 0x00],
       "KernelClaim::get_opt_def_asserts_masked"),
      ("wire-binders-opt-tag-2", baseDefWitness,
       defHeader ++ ByteArray.mk #[0x00, 0x00, 0x02],
       "KernelClaim::get_opt_addr"),
      ("wire-mut-defn-mask-64", baseMutWitness,
       mutHeader ++ ByteArray.mk #[0x08, 0x01, 0x01, 0x01, 0x00, 0x40, 0x00],
       "claim: reveal mut defn mask out of range"),
      ("wire-ctor-mask-128", baseMutWitness,
       mutHeader ++ ByteArray.mk #[0x08, 0x01, 0x01, 0x00, 0x01, 0x20, 0x01, 0x00, 0x80, 0x00, 0x00],
       "claim: reveal constructor mask out of range"),
      ("wire-ctor-field-mode-2", baseMutWitness,
       mutHeader ++ ByteArray.mk #[0x08, 0x01, 0x01, 0x00, 0x01, 0x20, 0x01, 0x01, 0x40, 0x02, 0x00, 0x02, 0x00],
       "IxonDeserialize::get_field_mode_list")] do
    add label (replaceClaimBytes baseW rawBytes) false (some reason)

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
    revealModeCases r

end Tests.Ix.IxVM.Codec
