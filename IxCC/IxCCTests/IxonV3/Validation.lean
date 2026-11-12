import IxCCTests.IxonV3.Builder

/-! The resource-validation API (`V3.validate`: resource admission and the
literal pins, no typing), the primitive table's parity with
`fixtures/ixon-v4/primitives.tsv`, and the `Nat` literal bytes. These were the
parts of the erased checker's suite that are not typing; the typing cases went
with the checker (the certified kernel decides them at ingress, and
`tests-kernel-front` tests its refusals). -/

namespace IxCCTests.IxonV3.Validation

open IxCC.Ixon IxCC.Ixon.V3 Builder

private def require (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError s!"v3 validation: {label}")

private def expect (label : String) (result : Except String α) (accepted : Bool) : IO Unit :=
  unless result.toOption.isSome == accepted do
    let detail := match result with | .ok _ => "accepted" | .error e => e
    throw (IO.userError s!"v3 validation {label}: expected {accepted}, got {detail}")

def run (root : System.FilePath) : IO Nat := do
  let raw ← IO.FS.readBinFile (root / "handoff/accepted.ixe")
  let profileRaw ← IO.FS.readBinFile (root / "handoff/profile.bin")
  let claim ← IO.FS.readBinFile (root / "handoff/accepted.claim")
  let input ← IO.ofExcept (validate raw profileRaw)
  expect "producer claim" (input.checkClaim claim) true
  let rejected ← IO.FS.readBinFile (root / "handoff/rejected-local-escape.ixe")
  let rejectedEnv ← IO.ofExcept (decodeAnonymousEnv rejected)
  expect "resource admission rejects local escape" (validate rejected profileRaw) false
  let wrongSubject : ResourceClaim := ⟨rejectedEnv.root, input.resource.resolved.profileAddress⟩
  expect "validated claim cannot change subject" (input.checkClaim wrongSubject.bytes) false
  let unit := input.resource.resolved.addresses[0]!
  expect "Nat profile cannot redirect" (checkLiteralProfile { natType := some unit }) false
  expect "String profile cannot redirect" (checkLiteralProfile { stringType := some unit }) false
  expect "canonical literal profile" (checkLiteralProfile {
    natType := some V3.PrimAddrs.canonical.nat, stringType := some V3.PrimAddrs.canonical.string }) true
  -- An ill-typed component the resource analysis does not look at: the
  -- validation API, which types nothing, passes it (the kernel refuses it at
  -- ingress on every compile path).
  let malformed : C := ⟨.defn ⟨.defn, .safe, 0, .sort 0, .var 0⟩, #[], #[], #[.zero]⟩
  let badEnv := (store input.resource.env malformed).1
  expect "ordinary ill-typed component passes resources"
    (Resource.Addressed.checkResources badEnv input.resource.profile) true
  expect "the validation API types nothing: the same raw bytes pass it"
    (validate (bytes badEnv) profileRaw) true
  let mut assertions := 8
  let table := V3.PrimAddrs.leanParityTable
  let lines := (← IO.FS.readFile (root / "primitives.tsv")).splitOn "\n" |>.filter
    (fun line => !line.isEmpty && !line.startsWith "#")
  require (lines.length == table.size) "primitive inventory size differs"
  assertions := assertions + 1
  for line in lines do
    let [name, address] := line.splitOn "\t" | throw (IO.userError "invalid primitive fixture")
    if name == "eagerReduce" then
      -- The actual declaration aliases id. Only the synthetic, reserved
      -- marker may trigger eager reduction (the producer makes this exception).
      require (address == "173299c76efa82e689210a09e49ad09c14ee1108f2da8d355ef9333b1583a1d5" &&
        V3.PrimAddrs.canonical.eagerReduce.toHex ==
          "ff00000000000000000000000000000000000000000000000000000000000003")
        "synthetic eager-reduction marker"
    else
      require (table.any fun (n, a) => n == name && a.toHex == address) s!"primitive differs: {name}"
    assertions := assertions + 1
  let (env, a) := base
  expect "full byte admission with explicit assumption"
    (validate (bytes (store env (identity a)).1) ({ assumptions := #[a] } : Resource.Profile).bytes) true
  assertions := assertions + 1
  -- A safe theorem's proof (erased computation) has no usage, ownership or
  -- locality obligations: resource admission only types it against its
  -- statement with contracts (`checkTheorem`). `∀ (P : sort) (p : linear P),
  -- P`, proved by `(fun q r => q) p p`.
  let linear : BinderContract := ⟨.linear, .shared⟩
  let theoremOf (kind : DefKind) (sort : E) : Environment := (store {}
    ⟨.defn ⟨kind, .safe, 0, arrow sort (.all linear .shared (.var 0) (.var 1)),
      lambda sort (.lam linear (.var 0)
        (.app (.app (lambda (.var 1) (lambda (.var 2) (.var 1))) (.var 0)) (.var 0)))⟩,
      #[], #[], #[.zero, .succ .zero]⟩).1
  let profile : Resource.Profile := {}
  let propTheorem := theoremOf .thm (.sort 0)
  expect "theorem proof has no usage obligations" (admitResources (bytes propTheorem) profile.bytes) true
  expect "theorem over a proposition passes the validation API"
    (validate (bytes propTheorem) profile.bytes) true
  expect "the same proof as a definition is resource-checked"
    (admitResources (bytes (theoremOf .defn (.sort 0))) profile.bytes) false
  expect "non-proposition theorem passes the resource half"
    (admitResources (bytes (theoremOf .thm (.sort 1))) profile.bytes) true
  assertions := assertions + 4
  for n in #[0, 1, 255, 256, 65535, 18446744073709551615, 2^130 + 513] do
    require (V3.natFromBytesLE (V3.natBytesLE n) == n) s!"natural bytes {n}"
    assertions := assertions + 1
  require ((V3.natBytesLE 256) == #[0, 1]) "natural byte order"
  require ((V3.natBytesLE 0) == #[0]) "zero literal bytes"
  assertions := assertions + 2
  IO.println s!"v3 validation: {assertions} assertions passed"
  return assertions

end IxCCTests.IxonV3.Validation
