module

public import Ix.HostAdmission
public import Tests.Ix.RoleGeneration

namespace Tests.Ix.HostAdmission

open _root_.Ix.HostAdmission

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def zero : Address := ⟨ByteArray.mk (Array.replicate 32 0)⟩
private def one : Address := ⟨ByteArray.mk (Array.replicate 32 1)⟩
private def other : Address := Address.admissionHash "different identity".toUTF8

private def samples : Array (String × Statement) := #[
  ("logical", { kind := .logical, hostSpecDigest := zero, bindingHash := one, contentRoot := zero, main := none }),
  ("logical_main", { kind := .logical, hostSpecDigest := one, bindingHash := zero, contentRoot := one, main := some zero }),
  ("tier_empty_logical", { kind := .tiered none (some zero), hostSpecDigest := zero, bindingHash := zero, contentRoot := zero, main := none }),
  ("tier_both", { kind := .tiered (some zero) (some one), hostSpecDigest := one, bindingHash := zero, contentRoot := zero, main := some one })]

private def codecChecks : Except String Unit := do
  let logical : Statement :=
    { kind := .logical, hostSpecDigest := zero, bindingHash := one, contentRoot := zero, main := none }
  for (_, sample) in samples do
    let bytes ← sample.bytes
    unless (← Statement.decode bytes) == sample do throw "host codec roundtrip differs"
    if (Statement.decode (bytes.push 0)).isOk then throw "host codec accepted trailing data"
    for n in [:bytes.size] do
      if (Statement.decode (bytes.extract 0 n)).isOk then throw "host codec accepted truncation"
    for (index, value) in #[(0, (0xE5 : UInt8)), (4, 2), (5, 3), (6, 2), (7, 1), (104, 2)] do
      if (Statement.decode (bytes.set! index value)).isOk then
        throw "host codec accepted wrong domain/version/object/kind/policy"
  if (({ logical with main := some ⟨ByteArray.empty⟩ } : Statement).bytes).isOk then
    throw "host codec accepted a short address"
  let left ← ({ logical with kind := .tiered none (some zero) } : Statement).bytes
  let right ← ({ logical with kind := .tiered (some zero) (some zero) } : Statement).bytes
  unless left != right do throw "host codec equated an absent and zero root"
  for addresses in #[#[], #[zero], #[zero, one], #[one, zero, other], #[zero, one, other, zero],
      #[other, one, zero, one, other]] do
    unless (← Merkle.root addresses) == _root_.Ix.Merkle.merkleRootCanonical addresses do
      throw "total host root differs from the existing canonical root"
  unless (← Merkle.root #[]) == none do throw "empty root was replaced by a zero hash"
  unless (← Merkle.root #[zero]).isSome do throw "zero leaf was mistaken for empty input"
  unless (← Merkle.root #[zero, one, other]) == (← Merkle.root #[other, one, zero, one]) do
    throw "host root depends on duplicate/permuted leaves"

private def vectors : IO Unit := do
  let text ← IO.FS.readFile "Tests/Fixtures/host-admission-v1/vectors.tsv"
  let mut counts := (0, 0)
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | ["statement", name, hash, hex] =>
      let some (_, expected) := samples.find? (·.1 == name) | throw (IO.userError s!"unknown vector {name}")
      let some raw := bytesOfHex hex | throw (IO.userError "bad vector bytes")
      ensure ((← IO.ofExcept expected.bytes) == raw && (← IO.ofExcept (Statement.decode raw)) == expected)
        "host codec differs from independently assembled bytes"
      ensure (toString (Address.admissionHash raw) == hash) "host address differs from pure reference BLAKE3"
      counts := (counts.1 + 1, counts.2)
    | ["merkle", ids, hash] =>
      let mut addresses := #[]
      if ids != "-" then
        for id in ids.splitOn "," do
          let some n := id.toNat? | throw (IO.userError "bad reference leaf")
          ensure (n < 256) "bad reference leaf width"
          addresses := addresses.push (⟨ByteArray.mk (Array.replicate 32 n.toUInt8)⟩ : Address)
      let root ← IO.ofExcept (Merkle.root addresses)
      ensure ((root.map toString).getD "none" == hash && root == _root_.Ix.Merkle.merkleRootCanonical addresses)
        "total host/legacy Merkle root differs from independent reference vector"
      counts := (counts.1, counts.2 + 1)
    | _ => throw (IO.userError "invalid host fixture row")
  ensure (counts == (4, 8)) "host vector coverage changed"

private def checks : IO Nat := do
  IO.ofExcept codecChecks
  vectors
  let limits := _root_.Ix.Resource.typingLimits
  let (source, generated) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let some main := generated.table.addressOf? .natDiv | throw (IO.userError "fixture has no main")
  let artifact := { source with main := some main }
  let ⟨statement, checked⟩ ← IO.ofExcept ((certify artifact limits).mapError toString)
  ensure (statement.kind == .logical && statement.main == some main) "wrong actual logical statement"
  ensure (statement.bindingHash == checked.run.prepared.binding.address &&
    statement.hostSpecDigest == (← IO.ofExcept _root_.Ix.SpecDigest.specDigest)) "statement did not use actual identities"
  let raw ← IO.ofExcept statement.bytes
  let address ← IO.ofExcept statement.address
  ensure (verifyAddressed address raw artifact limits).isOk "addressed verified statement failed"
  ensure (!(verifyAddressed other raw artifact limits).isOk) "addressed read trusted its key without hashing"
  for changed in #[{ statement with hostSpecDigest := other }, { statement with bindingHash := other },
      { statement with contentRoot := other }, { statement with main := none },
      { statement with kind := .tiered (some statement.contentRoot) none }] do
    ensure (match verify changed artifact limits with | .error (.identity _) => true | _ => false)
      "changed expected statement escaped comparison against the same accepted artifact"
  ensure (verify statement { artifact with named := {}, names := {}, addrToName := {} } limits).isOk
    "display metadata changed the host semantic identity"
  ensure (!(certify { artifact with main := some other } limits).isOk) "absent main received a statement"
  ensure (!(certify { artifact with main := some ⟨ByteArray.empty⟩ } limits).isOk) "malformed main was not refused"
  ensure (!(certify { artifact with roleBinding := none } limits).isOk) "unbound input received a host statement"
  ensure (!(certify { artifact with assumptions := ({} : Std.HashSet Address).insert main } limits).isOk)
    "external artifact assumptions received a closed statement"

  -- Unsafe False is permitted only as an opaque tier axiom. It must never
  -- enter the logical environment or acquire a logical-only statement.
  let some falseAddress := generated.table.addressOf? .false | throw (IO.userError "fixture has no False")
  let unsafeAxiom : Ixon.Constant := {
    info := .axio ⟨true, 0, .ref 0 #[]⟩, sharing := #[], refs := #[falseAddress], univs := #[] }
  let unsafeAddress := Address.admissionHash (Ixon.serConstant unsafeAxiom)
  let tierArtifact := { artifact with consts := artifact.consts.insert unsafeAddress (Ixon.LazyConstant.ofConstant unsafeAxiom) }
  let ⟨tierStatement, tierChecked⟩ ← IO.ofExcept ((certify tierArtifact limits).mapError toString)
  ensure (match tierStatement.kind with | .tiered (some _) (some _) => true | _ => false)
    "actual nonempty tier partition was not committed"
  ensure (tierChecked.run.typed.length == 1 &&
    (tierChecked.run.logicalEnv.find? (.id unsafeAddress)).isNone) "unsafe axiom escaped into the logical model"
  ensure (verify tierStatement tierArtifact limits).isOk "actual typed-tier statement did not verify"
  for changed in #[{ tierStatement with kind := .logical },
      { tierStatement with kind := .tiered none (some zero) }] do
    ensure (!(verify changed tierArtifact limits).isOk) "tier downgrade/partition tampering passed"
  return 2

public def units : LSpec.TestSeq :=
  .individualIO "host admission: actual receipts, canonical identities and replay/tamper controls" none (do
    let count ← checks
    return (true, count, 0, none)) .done

end Tests.Ix.HostAdmission
