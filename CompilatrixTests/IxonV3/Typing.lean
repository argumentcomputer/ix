import CompilatrixTests.IxonV3.TypingFixtures

namespace CompilatrixTests.IxonV3.Typing

open Compilatrix.Ixon Compilatrix.Ixon.V3 TypingFixtures

private def require (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError s!"v3 typing: {label}")

private def expect (label : String) (result : Except String α) (accepted : Bool) : IO Unit :=
  unless result.toOption.isSome == accepted do
    let detail := match result with | .ok _ => "accepted" | .error e => e
    throw (IO.userError s!"v3 typing {label}: expected {accepted}, got {detail}")

def run (root : System.FilePath) : IO Nat := do
  let raw ← IO.FS.readBinFile (root / "handoff/accepted.ixe")
  let profileRaw ← IO.FS.readBinFile (root / "handoff/profile.bin")
  let claim ← IO.FS.readBinFile (root / "handoff/accepted.claim")
  let input ← IO.ofExcept (validate raw profileRaw)
  expect "producer claim" (input.checkClaim claim) true
  let rejected ← IO.FS.readBinFile (root / "handoff/rejected-local-escape.ixe")
  let rejectedEnv ← IO.ofExcept (decodeAnonymousEnv rejected)
  expect "erased typing permits local escape" (Tc.checkEnv rejectedEnv) true
  expect "combined admission rejects local escape" (validate rejected profileRaw) false
  let wrongSubject : ResourceClaim := ⟨rejectedEnv.root, input.resource.resolved.profileAddress⟩
  expect "validated claim cannot change subject" (input.checkClaim wrongSubject.bytes) false
  let unit := input.resource.resolved.addresses[0]!
  expect "Nat profile cannot redirect" (checkLiteralProfile { natType := some unit }) false
  expect "String profile cannot redirect" (checkLiteralProfile { stringType := some unit }) false
  expect "canonical literal profile" (checkLiteralProfile {
    natType := some Tc.PrimAddrs.canonical.nat, stringType := some Tc.PrimAddrs.canonical.string }) true
  let malformed : C := ⟨.defn ⟨.defn, .safe, 0, .sort 0, .var 0⟩, #[], #[], #[.zero]⟩
  let badEnv := (store input.resource.env malformed).1
  expect "ordinary ill-typed component passes resources"
    (Resource.Addressed.checkResources badEnv input.resource.profile) true
  expect "ordinary ill-typed component fails typing" (Tc.checkEnv badEnv) false
  expect "same raw bytes fail combined admission" (validate (bytes badEnv) profileRaw) false
  let mut assertions := 10
  let table := Tc.PrimAddrs.leanParityTable
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
        Tc.PrimAddrs.canonical.eagerReduce.toHex ==
          "ff00000000000000000000000000000000000000000000000000000000000003" &&
        !Tc.primAddrSet.contains (Tc.PrimAddrs.h address)) "synthetic eager-reduction marker"
    else
      require (table.any fun (n, a) => n == name && a.toHex == address) s!"primitive differs: {name}"
    assertions := assertions + 1
  let (env, a) := base
  expect "axiom type" (Tc.checkEnv env) true
  expect "ordinary identity" (Tc.checkEnv (store env (identity a)).1) true
  expect "full byte admission with explicit assumption"
    (validate (bytes (store env (identity a)).1) ({ assumptions := #[a] } : Resource.Profile).bytes) true
  assertions := assertions + 3
  for bits in [:16] do
    let contract := (BinderContract.ofBits? bits.toUInt8).get!
    let c : C := ⟨.defn ⟨.defn, .safe, 0,
      .all contract .localShared (.ref 0 #[]) (.ref 0 #[]),
      .lam contract (.ref 0 #[]) (.var 0)⟩, #[], #[a], #[]⟩
    expect s!"erased binder contract {bits}" (Tc.checkEnv (store env c).1) true
    assertions := assertions + 1
  let badCases : Array (String × C) := #[
    ("value type mismatch", ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 0⟩, #[], #[a], #[.zero]⟩),
    ("loose variable", malformed),
    ("universe parameter", ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.var 0]⟩),
    ("universe table index", ⟨.axio ⟨false, 0, .sort 1⟩, #[], #[], #[.zero]⟩),
    ("reference universe arity", ⟨.axio ⟨false, 0, .ref 0 #[0]⟩, #[], #[a], #[.zero]⟩),
    ("missing reference", ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[Address.replicate 7], #[]⟩),
    ("invalid reference index", ⟨.axio ⟨false, 0, .ref 1 #[]⟩, #[], #[a], #[]⟩),
    ("invalid recursive index", ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 1 #[]⟩, #[], #[a], #[]⟩),
    ("sharing cycle", ⟨.axio ⟨false, 0, .share 0⟩, #[.share 0], #[], #[]⟩),
    ("indirect sharing cycle", ⟨.axio ⟨false, 0, .share 0⟩, #[.share 1, .share 0], #[], #[]⟩),
    ("sharing bounds", ⟨.axio ⟨false, 0, .share 9⟩, #[.sort 0], #[], #[.zero]⟩),
    ("binder count budget", ⟨.axio ⟨false, 4097, .sort 0⟩, #[], #[], #[.zero]⟩),
    ("variable arithmetic overflow", ⟨.axio ⟨false, 0, .var 18446744073709551615⟩, #[], #[], #[]⟩),
    ("empty block", ⟨.muts #[], #[], #[], #[]⟩),
    ("orphan projection", ⟨.iPrj ⟨0, a⟩, #[], #[], #[]⟩),
    ("forged quotient", ⟨.quot ⟨.type, 0, .sort 0⟩, #[], #[], #[.zero]⟩)]
  for (label, c) in badCases do
    expect label (Tc.checkEnv (store env c).1) false
    assertions := assertions + 1
  let typeOne : C := ⟨.defn ⟨.defn, .safe, 0, .sort 1, .sort 0⟩,
    #[], #[], #[.zero, .succ .zero]⟩
  expect "sort typing" (Tc.checkEnv (store {} typeOne).1) true
  let shared : C := ⟨.defn ⟨.defn, .safe, 0, arrow (.ref 0 #[]) (.ref 0 #[]), .share 0⟩,
    #[.share 1, lambda (.ref 0 #[]) (.var 0)], #[a], #[]⟩
  expect "acyclic forward sharing" (Tc.checkEnv (store env shared).1) true
  let uUnsafe : C := ⟨.axio ⟨true, 0, .ref 0 #[]⟩, #[], #[a], #[]⟩
  let (unsafeEnv, u) := store env uUnsafe
  let safeUse : C := ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[a, u], #[]⟩
  expect "safe definition cannot use unsafe axiom" (Tc.checkEnv (store unsafeEnv safeUse).1) false
  let notProp : C := ⟨.defn ⟨.thm, .safe, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
    lambda (.ref 0 #[]) (.var 0)⟩, #[], #[a], #[]⟩
  expect "theorem must inhabit Prop" (Tc.checkEnv (store env notProp).1) false
  let (propEnv, prop) := store {} ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let validTheorem : C := ⟨.defn ⟨.thm, .safe, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
    lambda (.ref 0 #[]) (.var 0)⟩, #[], #[prop], #[]⟩
  expect "valid theorem" (Tc.checkEnv (store propEnv validTheorem).1) true
  assertions := assertions + 5
  expect "recursive inductive" (Tc.checkEnv (indEnv natLike)) true
  let negative : V3.Inductive := ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 1, arrow (arrow (.recur 0 #[]) (.recur 0 #[])) (.recur 0 #[])⟩]⟩
  expect "strict positivity" (Tc.checkEnv (indEnv negative)) false
  let highField : V3.Inductive := ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 1, arrow (.sort 0) (.recur 0 #[])⟩]⟩
  expect "constructor field universe" (Tc.checkEnv (indEnv highField)) false
  let parameterized : V3.Inductive := ⟨false, 0, 1, 0, arrow (.sort 0) (.sort 0),
    #[⟨false, 0, 0, 1, 1, arrow (.sort 0) (arrow (.var 0) (.app (.recur 0 #[]) (.var 1)))⟩]⟩
  expect "parameterized inductive" (Tc.checkEnv (indEnv parameterized)) true
  let badCtor := { natLike with ctors := #[{ natLike.ctors[0]! with cidx := 1 }] }
  expect "constructor index" (Tc.checkEnv (indEnv badCtor)) false
  let badFields := { natLike with ctors := #[{ natLike.ctors[0]! with fields := 1 }] }
  expect "constructor field count" (Tc.checkEnv (indEnv badFields)) false
  let (nEnv, nBlock) := block {} ⟨.muts #[.indc natLike], #[], #[], #[.succ .zero]⟩
  expect "missing constructor wrapper" (Tc.checkEnv
    { nEnv with consts := nEnv.consts.erase (Tc.ctorProjAddr nBlock 0 1) }) false
  let orphan := (store nEnv ⟨.iPrj ⟨99, nBlock⟩, #[], #[], #[]⟩).1
  expect "out of range wrapper" (Tc.checkEnv orphan) false
  assertions := assertions + 8
  expect "canonical generated recursor" (Tc.checkEnv (recursorEnv false false)) true
  expect "recursor K flag mismatch" (Tc.checkEnv (recursorEnv true false)) false
  expect "recursor rule mismatch" (Tc.checkEnv (recursorEnv false true)) false
  expect "recursor universe arity mismatch" (Tc.checkEnv (recursorEnv false false 2)) false
  assertions := assertions + 4
  let mismatch := { env with consts := env.consts.insert Tc.PrimAddrs.canonical.nat (constantBytes axiomType) }
  expect "primitive content cannot be forged" (Tc.checkEnv mismatch) false
  expect "verification cannot be disabled" (Tc.getConstVerified mismatch Tc.PrimAddrs.canonical.nat false) false
  let blob : ByteArray := ⟨#[42]⟩
  let blobAddr := Address.blake3 blob
  let literal : C := ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .nat 1⟩, #[], #[a, blobAddr], #[]⟩
  expect "Nat literal cannot have arbitrary type" (Tc.checkEnv
    (store { env with blobs := ({} : Std.HashMap Address ByteArray).insert blobAddr blob } literal).1) false
  let wrongBlob := { env with blobs := ({} : Std.HashMap Address ByteArray).insert blobAddr ⟨#[43]⟩ }
  expect "literal bytes are checked" (Tc.checkEnv (store wrongBlob literal).1) false
  assertions := assertions + 4
  for n in #[0, 1, 255, 256, 65535, 18446744073709551615, 2^130 + 513] do
    require (Tc.natFromBytesLE (Tc.tcNatBytesLE n) == n) s!"natural bytes {n}"
    assertions := assertions + 1
  require (Tc.tcUInt64BytesLE 0x0807060504030201 == ⟨#[1,2,3,4,5,6,7,8]⟩)
    "fixed integer byte order"
  require ((Tc.tcNatBytesLE 256) == #[0, 1]) "natural byte order"
  require ((Tc.tcNatBytesLE 0) == #[0]) "zero literal bytes"
  assertions := assertions + 3
  let ku : Tc.KUniv .anon := .mkParam 0 ()
  let kv : Tc.KUniv .anon := .mkParam 1 ()
  let one : Tc.KUniv .anon := .mkSucc .mkZero
  let levels : Array (String × Tc.KUniv .anon × Tc.KUniv .anon × Bool) := #[
    ("max commutes", .mkMax ku kv, .mkMax kv ku, true),
    ("imax zero", .mkIMax ku .mkZero, .mkZero, true),
    ("max duplicate", .mkMax ku ku, ku, true),
    ("different parameters", ku, kv, false),
    ("successor", .mkSucc ku, ku, false),
    ("imax differs from max", .mkIMax one kv, .mkMax one kv, false),
    ("conditioned subsumption", .mkMax (.mkSucc ku) (.mkIMax (.mkSucc ku) kv),
      .mkMax (.mkSucc ku) kv, true)]
  for (label, left, right, expected) in levels do
    require (Tc.univEq left right == expected) s!"universe normalization: {label}"
    assertions := assertions + 1
  IO.println s!"v3 erased typing: {assertions} assertions passed"
  return assertions

end CompilatrixTests.IxonV3.Typing
