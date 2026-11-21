module
public import Lean.Data.Json
public import Ix.Ixon
public import Ix.Claim
public import Ix.AssumptionTree
public import Ix.DynamicLink.Codec
public import LSpec

/-! # Rust ↔ Lean Ixon v4/v5, Claim, Proof, AssumptionTree, Comm & BLAKE3 Parity

Consumes the Rust-generated fixture `Tests/Fixtures/IxonParity/vectors.json`
(produced by `crates/ixon/tests/parity_vectors.rs`) and verifies byte-for-byte
serialization, deserialization, round-trip, and BLAKE3 digest agreement across:
- 20 `Ix.Claim` vectors (all variants, validators `0`/`3`/`4`/`5`, optional axioms/assumptions)
- 7 `Ix.Proof` vectors
- 5 `Ix.AssumptionTree` vectors (wire bytes + Merkle root hash)
- 2 `Ixon.Comm` vectors (untagged, tagged, and commitment BLAKE3 digest)
- 7 `Ixon.Univ` vectors
- 22 `Ixon.Expr` vectors (every constructor + telescopes + non-dep/borrow `let`)
- 11 `Ixon.Constant` vectors (every variant)
- 6 `BLAKE3` vectors (`0`, `3`, `64`, `65`, `1024`, `1025` bytes — both FFI `blake3` and pure `blake3Pure`)
- 17 negative `Ix.Claim` controls (retired/reserved tags & validators, plus
  DynamicLink `0xE8 0x0D` / `0xE8 0x0E` and validators `10`/`11` which MUST be
  rejected by `Ix.Claim.de` while round-tripping under `Ix.DynamicLink.Codec`).
-/

open LSpec Lean

public section

namespace Tests.Ix.IxonRustParity

def fixturePath : System.FilePath := "Tests/Fixtures/IxonParity/vectors.json"

private def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

private def parseHex (s : String) : Except String ByteArray := do
  let cs := s.toList
  unless cs.length % 2 == 0 do throw s!"odd hex length: {s.length}"
  let mut out := ByteArray.emptyWithCapacity (cs.length / 2)
  for i in [0:cs.length / 2] do
    match hexDigit cs[2 * i]!, hexDigit cs[2 * i + 1]! with
    | some hi, some lo => out := out.push (hi * 16 + lo)
    | _, _ => throw s!"invalid hex digit in {s}"
  return out

private def toHex (bs : ByteArray) : String := Id.run do
  let digits := #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let mut s := ""
  for i in [0:bs.size] do
    let b := bs[i]!
    s := s.push digits[(b.toNat >>> 4) &&& 0xF]!
    s := s.push digits[b.toNat &&& 0xF]!
  return s

private def addrHex (a : Address) : String := toHex a.hash

private def reqStr (j : Json) (k : String) : Except String String :=
  j.getObjValAs? String k

private def reqNat (j : Json) (k : String) : Except String Nat :=
  j.getObjValAs? Nat k

private def reqArr (j : Json) (k : String) : Except String (Array Json) := do
  (← j.getObjVal? k).getArr?

def suite : IO (List TestSeq) := do
  let raw ← IO.FS.readFile fixturePath
  let root ← IO.ofExcept (Json.parse raw)
  let mut tests : TestSeq := .done

  -- 1. Claims (20 positive vectors)
  let claims ← IO.ofExcept (reqArr root "claims")
  tests := tests ++ test "claims count ≥ 15" (claims.size ≥ 15)
  for c in claims do
    let name ← IO.ofExcept (reqStr c "name")
    let hex ← IO.ofExcept (reqStr c "hex")
    let blake ← IO.ofExcept (reqStr c "blake3")
    let byteLen ← IO.ofExcept (reqNat c "byte_len")
    let bytes ← IO.ofExcept (parseHex hex)
    let lenOk := bytes.size == byteLen
    let hashOk := addrHex (Address.blake3 bytes) == blake && addrHex (Address.blake3Pure bytes) == blake
    let rtOk := match Ix.Claim.de bytes with
      | .ok val => Ix.Claim.ser val == bytes
      | .error _ => false
    tests := tests ++ test s!"claim/{name}: len+blake3+roundtrip" (lenOk && hashOk && rtOk)

  -- 2. Proofs (7 positive vectors)
  let proofs ← IO.ofExcept (reqArr root "proofs")
  tests := tests ++ test "proofs count ≥ 7" (proofs.size ≥ 7)
  for p in proofs do
    let name ← IO.ofExcept (reqStr p "name")
    let hex ← IO.ofExcept (reqStr p "hex")
    let blake ← IO.ofExcept (reqStr p "blake3")
    let bytes ← IO.ofExcept (parseHex hex)
    let hashOk := addrHex (Address.blake3 bytes) == blake && addrHex (Address.blake3Pure bytes) == blake
    let rtOk := match Ixon.Proof.de bytes with
      | .ok val => Ixon.Proof.ser val == bytes
      | .error _ => false
    tests := tests ++ test s!"proof/{name}: blake3+roundtrip" (hashOk && rtOk)

  -- 3. AssumptionTrees (5 vectors + root hash)
  let trees ← IO.ofExcept (reqArr root "assumption_trees")
  tests := tests ++ test "assumption_trees count ≥ 5" (trees.size ≥ 5)
  for t in trees do
    let name ← IO.ofExcept (reqStr t "name")
    let hex ← IO.ofExcept (reqStr t "hex")
    let blake ← IO.ofExcept (reqStr t "blake3")
    let rootBlake ← IO.ofExcept (reqStr t "root_blake3")
    let bytes ← IO.ofExcept (parseHex hex)
    let hashOk := addrHex (Address.blake3 bytes) == blake
    let rtOk := match Ix.AssumptionTree.de bytes with
      | .ok val => Ix.AssumptionTree.ser val == bytes && addrHex val.root == rootBlake
      | .error _ => false
    tests := tests ++ test s!"tree/{name}: blake3+roundtrip+root" (hashOk && rtOk)

  -- 4. Comms (2 vectors: untagged, tagged, commitment digest)
  let comms ← IO.ofExcept (reqArr root "comms")
  tests := tests ++ test "comms count ≥ 2" (comms.size ≥ 2)
  for cm in comms do
    let name ← IO.ofExcept (reqStr cm "name")
    let untaggedHex ← IO.ofExcept (reqStr cm "untagged_hex")
    let taggedHex ← IO.ofExcept (reqStr cm "tagged_hex")
    let commitBlake ← IO.ofExcept (reqStr cm "commit_blake3")
    let untagged ← IO.ofExcept (parseHex untaggedHex)
    let tagged ← IO.ofExcept (parseHex taggedHex)
    let rtOk := match Ixon.deComm untagged with
      | .ok val =>
        Ixon.serComm val == untagged &&
        Ixon.serCommTagged val == tagged &&
        addrHex val.commit == commitBlake
      | .error _ => false
    tests := tests ++ test s!"comm/{name}: untagged+tagged+commit" (rtOk == true)

  -- 5. Univs (7 vectors)
  let univs ← IO.ofExcept (reqArr root "univs")
  tests := tests ++ test "univs count ≥ 7" (univs.size ≥ 7)
  for u in univs do
    let name ← IO.ofExcept (reqStr u "name")
    let hex ← IO.ofExcept (reqStr u "hex")
    let blake ← IO.ofExcept (reqStr u "blake3")
    let bytes ← IO.ofExcept (parseHex hex)
    let hashOk := addrHex (Address.blake3 bytes) == blake
    let rtOk := match Ixon.deUniv bytes with
      | .ok val => Ixon.serUniv val == bytes
      | .error _ => false
    tests := tests ++ test s!"univ/{name}: blake3+roundtrip" (hashOk && rtOk)

  -- 6. Exprs (22 vectors)
  let exprs ← IO.ofExcept (reqArr root "exprs")
  tests := tests ++ test "exprs count ≥ 20" (exprs.size ≥ 20)
  for e in exprs do
    let name ← IO.ofExcept (reqStr e "name")
    let hex ← IO.ofExcept (reqStr e "hex")
    let blake ← IO.ofExcept (reqStr e "blake3")
    let bytes ← IO.ofExcept (parseHex hex)
    let hashOk := addrHex (Address.blake3 bytes) == blake
    let rtOk := match Ixon.deExpr bytes with
      | .ok val => Ixon.serExpr val == bytes
      | .error _ => false
    tests := tests ++ test s!"expr/{name}: blake3+roundtrip" (hashOk && rtOk)

  -- 7. Constants (11 vectors)
  let consts ← IO.ofExcept (reqArr root "constants")
  tests := tests ++ test "constants count ≥ 11" (consts.size ≥ 11)
  for k in consts do
    let name ← IO.ofExcept (reqStr k "name")
    let hex ← IO.ofExcept (reqStr k "hex")
    let blake ← IO.ofExcept (reqStr k "blake3")
    let bytes ← IO.ofExcept (parseHex hex)
    let hashOk := addrHex (Address.blake3 bytes) == blake
    let rtOk := match Ixon.deConstant bytes with
      | .ok val => Ixon.serConstant val == bytes
      | .error _ => false
    tests := tests ++ test s!"constant/{name}: blake3+roundtrip" (hashOk && rtOk)

  -- 8. BLAKE3 (6 vectors across block & chunk boundaries)
  let b3s ← IO.ofExcept (reqArr root "blake3")
  tests := tests ++ test "blake3 count ≥ 6" (b3s.size ≥ 6)
  for b in b3s do
    let name ← IO.ofExcept (reqStr b "name")
    let inputHex ← IO.ofExcept (reqStr b "input_hex")
    let blake ← IO.ofExcept (reqStr b "blake3")
    let bytes ← IO.ofExcept (parseHex inputHex)
    let ok := addrHex (Address.blake3 bytes) == blake && addrHex (Address.blake3Pure bytes) == blake
    tests := tests ++ test s!"blake3/{name}: ffi+pure match Rust" ok

  -- 9. Negative Claim Controls (17 vectors: ALL rejected by Claim.de, DynamicLink cases round-trip in Codec)
  let negs ← IO.ofExcept (reqArr root "negative_claims")
  tests := tests ++ test "negative_claims count ≥ 17" (negs.size ≥ 17)
  for n in negs do
    let name ← IO.ofExcept (reqStr n "name")
    let hex ← IO.ofExcept (reqStr n "hex")
    let dlKind ← IO.ofExcept (reqStr n "dynamic_link_kind")
    let bytes ← IO.ofExcept (parseHex hex)
    let rejectedByClaim := !(Ix.Claim.de bytes).isOk
    tests := tests ++ test s!"neg/{name}: Claim.de rejects" rejectedByClaim
    -- For the canonical DynamicLink wire vectors (non-scope-prefix probes), verify Lean Codec round-trip
    if dlKind == "dynamic_link" && !name.endsWith "_scope_prefix_0403" then
      let dlOk := match Ix.DynamicLink.deDynamicLink bytes with
        | .ok s => Ix.DynamicLink.serDynamicLink s == bytes
        | .error _ => false
      tests := tests ++ test s!"neg/{name}: DynamicLink.deDynamicLink roundtrips" (dlOk == true)
    else if dlKind == "eval_assumption" && !name.endsWith "_scope_prefix_0403" then
      let eaOk := match Ix.DynamicLink.deEvalAssumption bytes with
        | .ok e => Ix.DynamicLink.serEvalAssumption e == bytes
        | .error _ => false
      tests := tests ++ test s!"neg/{name}: DynamicLink.deEvalAssumption roundtrips" (eaOk == true)
    else if dlKind == "eval_assumed_claim" then
      let eacOk := match Ix.DynamicLink.deEvalAssumedClaim bytes with
        | .ok c => Ix.DynamicLink.serEvalAssumedClaim c == bytes
        | .error _ => false
      tests := tests ++ test s!"neg/{name}: DynamicLink.deEvalAssumedClaim roundtrips" (eacOk == true)

  return [tests]

end Tests.Ix.IxonRustParity

end
