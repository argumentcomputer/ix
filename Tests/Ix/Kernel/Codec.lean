/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify
import Ix.Ixon.Canonical
import Tests.Ix.Kernel.IxonFixtures

/-! The production Ixon codec: exact round trips, the bounded and canonical
decoders' refusals and budgets, checked at elaboration. -/

open Tests.Ix.Kernel.IxonFixtures

namespace Tests.Ix.Kernel.Codec

def exactConstant (value : Ixon.Constant) : Bool :=
  match Ixon.deConstantExact (Ixon.serConstant value) with
  | .ok decoded => decoded == value
  | .error _ => false

def exactExpr (value : Ixon.Expr) : Bool :=
  match Ixon.deExpr (Ixon.serExpr value) with
  | .ok decoded => decoded == value
  | .error _ => false

def exactUniv (value : Ixon.Univ) : Bool :=
  match Ixon.deUniv (Ixon.serUniv value) with
  | .ok decoded => decoded == value
  | .error _ => false

def exactBoundedConstant (value : Ixon.Constant) : Bool :=
  let bytes := Ixon.serConstant value
  let nodes := Ixon.Bounded.univNodes value.univs
  match Ixon.Bounded.deConstant bytes.size nodes bytes with
  | .ok decoded => decoded == value
  | .error _ => false

def exactCanonicalConstant (value : Ixon.Constant) : Bool :=
  let bytes := Ixon.serConstant value
  match Ixon.Canonical.deConstant bytes.size (Ixon.Bounded.univNodes value.univs) bytes with
  | .ok decoded => decoded == value
  | .error _ => false

#guard variants.all fun (_, value) => exactConstant value
#guard falseStore.all fun (_, value) => exactConstant value
#guard separatedFalse.all fun (_, value) => exactConstant value
#guard exactConstant sharedIdentity
#guard exactConstant ⟨.muts #[], #[], #[], #[]⟩
#guard variants.all fun (_, value) => exactBoundedConstant value
#guard falseStore.all fun (_, value) => exactBoundedConstant value
#guard separatedFalse.all fun (_, value) => exactBoundedConstant value
#guard exactBoundedConstant sharedIdentity
#guard exactBoundedConstant ⟨.muts #[], #[], #[], #[]⟩
#guard exactBoundedConstant ⟨.muts #[], #[], #[], Array.replicate 4096 .zero⟩
#guard variants.all fun (_, value) => exactCanonicalConstant value
#guard falseStore.all fun (_, value) => exactCanonicalConstant value
#guard separatedFalse.all fun (_, value) => exactCanonicalConstant value
#guard exactCanonicalConstant sharedIdentity
#guard exactCanonicalConstant ⟨.muts #[], #[], #[], #[]⟩

-- Malformed address widths are outside the wire domain regardless of typing.
#guard !Ixon.WireCheck.validConstant ⟨.muts #[], #[], #[⟨⟨#[0]⟩⟩], #[]⟩
#guard !Ixon.WireCheck.validConstant ⟨.iPrj ⟨0, ⟨⟨#[0]⟩⟩⟩, #[], #[], #[]⟩
#guard Ixon.WireCheck.validExpr
  ((List.range 4096).foldl (fun e i => .app e (.var i.toUInt64)) (.var 0))

def sharedUniverseBudget : Ixon.Constant :=
  ⟨.muts #[], #[], #[], #[.addSucc 15 .zero, .addSucc 15 .zero]⟩

#guard exactBoundedConstant sharedUniverseBudget
-- Each entry fits 16 nodes, but the table requires 32. Resetting the budget
-- at each entry would incorrectly accept either of these insufficient limits.
#guard [16, 31].all fun budget =>
  !(Ixon.Bounded.deConstant 256 budget (Ixon.serConstant sharedUniverseBudget)).isOk
#guard match Ixon.Bounded.deConstant 256 32 (Ixon.serConstant sharedUniverseBudget) with
  | .ok value => value == sharedUniverseBudget
  | .error _ => false

def recordUnivsPayload (count : UInt64) (payload : ByteArray) : ByteArray :=
  Ixon.runPut do
    Ixon.putConstantInfo (.muts #[])
    Ixon.putTag0 ⟨0⟩
    Ixon.putTag0 ⟨0⟩
    Ixon.putTag0 ⟨count⟩
    Ixon.putBytes payload

def nonminimalSharingCount : ByteArray := Ixon.runPut do
  Ixon.putConstantInfo (.muts #[])
  Ixon.putBytes ⟨#[0x80, 0]⟩
  Ixon.putTag0 ⟨0⟩
  Ixon.putTag0 ⟨0⟩

def nonBooleanAxiom : ByteArray := Ixon.runPut do
  Ixon.putTag4 ⟨Ixon.Constant.FLAG, Ixon.ConstantInfo.CONST_AXIO⟩
  Ixon.putU8 2
  Ixon.putTag0 ⟨0⟩
  Ixon.putExpr (.sort 0)
  Ixon.putTag0 ⟨0⟩
  Ixon.putTag0 ⟨0⟩
  Ixon.putTag0 ⟨0⟩

-- Production decoding accepts these alternate universe spellings. Canonical
-- decoding rejects nonmaximal successor chains and ignored universe tag sizes
-- rather than normalizing their bytes.
def alternateSpellings : List ByteArray := [
  recordUnivsPayload 1 ⟨#[1, 1, 0]⟩,
  recordUnivsPayload 1 ⟨#[0x41, 0, 0]⟩]

-- Ixon v3's production decoder itself rejects nonminimal integer tags and
-- non-Boolean flags; the bounded and canonical decoders report its reason.
def decoderRejectedSpellings : List (ByteArray × String) := [
  (nonminimalSharingCount, "noncanonical Tag0 integer"),
  (recordUnivsPayload 1 ⟨#[0xE0, 0]⟩, "noncanonical Tag2 integer"),
  (nonBooleanAxiom, "expected Bool (0 or 1), got 2")]

#guard decoderRejectedSpellings.all fun (bytes, reason) =>
  (match Ixon.deConstantExact bytes with | .error e => e == reason | .ok _ => false) &&
  (match Ixon.Bounded.deConstant 256 64 bytes with | .error e => e == reason | .ok _ => false) &&
  (match Ixon.Canonical.deConstant 256 64 bytes with | .error e => e == reason | .ok _ => false)

#guard alternateSpellings.all fun bytes =>
  (Ixon.Bounded.deConstant 256 64 bytes).isOk &&
    match Ixon.Canonical.deConstant 256 64 bytes with
    | .ok _ => false
    | .error reason => reason == "getConstantCanonical: noncanonical wire encoding"

-- Claimed lengths are consumed as streaming loops, not preallocations.
#guard !(Ixon.Bounded.deConstant 256 64
  (recordUnivsPayload 18446744073709551615 ⟨#[]⟩)).isOk
#guard !(Ixon.Bounded.deConstant 256 64 (Ixon.runPut do
  Ixon.putConstantInfo (.muts #[])
  Ixon.putTag0 ⟨18446744073709551615⟩)).isOk
#guard !(Ixon.Bounded.deConstant 256 64 (Ixon.runPut do
  Ixon.putConstantInfo (.muts #[])
  Ixon.putTag0 ⟨0⟩
  Ixon.putTag0 ⟨18446744073709551615⟩)).isOk

def wordBoundaries : List UInt64 :=
  [0, 1, 7, 8, 31, 32, 127, 128, 255, 256, 65535, 65536, 18446744073709551615]

#guard wordBoundaries.all fun n =>
  [Ixon.Expr.var n, .sort n, .str n, .nat n, .share n,
    .ref n #[n], .recur n #[n], .prj n n (.var 0)].all exactExpr
#guard wordBoundaries.all fun n => exactUniv (.var n)
#guard [0, 1, 31, 32, 255, 256].all fun n =>
  exactUniv (.addSucc n (.max (.var 18446744073709551615) (.imax .zero (.var 1))))

def boundedUniverses : List Ixon.Univ :=
  [.zero, .var 18446744073709551615, .max .zero (.var 0),
    .imax (.succ .zero) (.max (.var 1) (.succ (.var 2))),
    .max (.addSucc 31 .zero) (.addSucc 31 .zero)] ++
    [0, 1, 31, 32, 255, 256].map fun n =>
      .addSucc n (.max (.var 18446744073709551615) (.imax .zero (.var 1)))

-- Both exact and surplus budgets preserve valid inputs. Each limit is
-- independently enforced, including a budget shared by binary children.
#guard boundedUniverses.all fun value =>
  let bytes := Ixon.serUniv value
  [0, 1, 16].all (fun surplus =>
    match Ixon.Bounded.deUniv (bytes.size + surplus) (value.nodeCount + surplus) bytes with
    | .ok decoded => decoded == value
    | .error _ => false) &&
  !(Ixon.Bounded.deUniv (bytes.size - 1) value.nodeCount bytes).isOk &&
  !(Ixon.Bounded.deUniv bytes.size (value.nodeCount - 1) bytes).isOk

-- Ten bytes can request UInt64.max successor nodes. Rejection must happen
-- before successor construction, even when the encoded base is present.
def successorBomb : ByteArray := ⟨#[0x27, 255, 255, 255, 255, 255, 255, 255, 255, 0]⟩

#guard match Ixon.Bounded.deConstant 256 64 (recordUnivsPayload 1 successorBomb) with
  | .error reason => reason == "getUnivBounded: expanded-node budget exhausted"
  | .ok _ => false
#guard match Ixon.Bounded.deConstant 256 64
    (recordUnivsPayload 2 (Ixon.serUniv .zero ++ successorBomb)) with
  | .error reason => reason == "getUnivBounded: expanded-node budget exhausted"
  | .ok _ => false
#guard !(Ixon.Canonical.deConstant 256 64 (recordUnivsPayload 1 successorBomb)).isOk

#guard match Ixon.Bounded.deUniv successorBomb.size 64 successorBomb with
  | .error reason => reason == "getUnivBounded: expanded-node budget exhausted"
  | .ok _ => false

-- Cursor evidence distinguishes preallocation rejection from a decoder
-- that reads or expands the base before checking the claimed chain size.
#guard match Ixon.Bounded.getUniv 64 { bytes := successorBomb } with
  | .error reason state =>
    reason == "getUnivBounded: expanded-node budget exhausted" && state.idx == 9
  | .ok _ _ => false

#guard !(Ixon.runGet (Ixon.Bounded.getUnivFuel 1 64) (Ixon.serUniv (.succ .zero))).isOk
#guard boundedUniverses.all fun value =>
  let bytes := Ixon.serUniv value
  !(Ixon.Bounded.deUniv (bytes.size + 1) value.nodeCount (bytes ++ ⟨#[0]⟩)).isOk &&
    (List.range bytes.size).all (fun n =>
      !(Ixon.Bounded.deUniv bytes.size value.nodeCount (bytes.extract 0 n)).isOk)

/-- All sixteen v3 binder contracts, four value contracts, and the four let
flag spellings over a binder. -/
def binderContracts : List Ixon.BinderContract :=
  (List.range 16).filterMap fun bits => Ixon.BinderContract.ofBits? bits.toUInt8
def valueContracts : List Ixon.ValueContract :=
  (List.range 4).filterMap fun bits => Ixon.ValueContract.ofBits? bits.toUInt8
def letContracts (binder : Ixon.BinderContract) : List Ixon.LetContract :=
  (List.range 4).filterMap fun flags => Ixon.LetContract.ofFlags? flags.toUInt64 binder
#guard binderContracts.length == 16 && valueContracts.length == 4 &&
  (letContracts .many).length == 4

-- Every v3 binder contract, forall result contract, and let flag spelling.
#guard binderContracts.all fun binder =>
  valueContracts.all fun result =>
    letContracts binder |>.all fun letContract =>
      exactExpr (.all binder result (.sort 0)
        (.lam binder (.var 0) (.letE letContract (.var 1) (.var 0) (.var 0))))
#guard exactExpr (.letE (.lean false) (.sort 0) (.app (.var 0) (.var 1)) (.var 2))
#guard [1, 7, 8, 31, 32, 128].all fun n =>
  exactExpr ((List.range n).foldl (fun e i => .app e (.var i.toUInt64)) (.ref 0 #[]))

-- Exact framing rejects suffixes even though the legacy prefix API succeeds.
#guard match Ixon.deConstant (Ixon.serConstant identity ++ ⟨#[255]⟩) with
  | .ok value => value == identity
  | _ => false
#guard !(Ixon.deConstantExact (Ixon.serConstant identity ++ ⟨#[255]⟩)).isOk
#guard !(Ixon.deConstantExact (Ixon.serConstant identity ++ Ixon.serConstant identity)).isOk
#guard !(Ixon.deExpr (Ixon.serExpr (.var 0) ++ ⟨#[0]⟩)).isOk
#guard !(Ixon.deUniv (Ixon.serUniv .zero ++ ⟨#[0]⟩)).isOk
#guard !(Ixon.deConstantExact ⟨#[]⟩).isOk
#guard !(Ixon.deConstantExact ⟨#[255]⟩).isOk
#guard !(Ixon.deExpr ⟨#[0x80, 0xff]⟩).isOk
#guard !(Ixon.runGet Ixon.getTag0 ⟨#[0x88, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩).isOk

-- Every proper prefix of a valid record is incomplete.
#guard (List.range (Ixon.serConstant variedBlock).size).all fun n =>
  !(Ixon.deConstantExact ((Ixon.serConstant variedBlock).extract 0 n)).isOk

#guard variants.all fun (_, value) =>
  let bytes := Ixon.serConstant value
  let nodes := Ixon.Bounded.univNodes value.univs
  !(Ixon.Bounded.deConstant (bytes.size - 1) nodes bytes).isOk &&
    !(Ixon.Bounded.deConstant (bytes.size + 1) nodes (bytes ++ ⟨#[0]⟩)).isOk &&
    (List.range bytes.size).all (fun n =>
      !(Ixon.Bounded.deConstant bytes.size nodes (bytes.extract 0 n)).isOk)

#guard variants.all fun (_, value) =>
  let bytes := Ixon.serConstant value
  let nodes := Ixon.Bounded.univNodes value.univs
  !(Ixon.Canonical.deConstant (bytes.size - 1) nodes bytes).isOk &&
    !(Ixon.Canonical.deConstant (bytes.size + 1) nodes (bytes ++ ⟨#[0]⟩)).isOk &&
    (List.range bytes.size).all (fun n =>
      !(Ixon.Canonical.deConstant bytes.size nodes (bytes.extract 0 n)).isOk)

-- Resource bounds apply to the bytes actually consumed, excluding an
-- untouched prefix and suffix. Every fixture must successfully read its
-- expected value; an error cannot vacuously satisfy these controls.
def resourceRead [BEq α] (reader : Ixon.GetM α) (units : α → Nat)
    (payload : ByteArray) (expected : α) : Bool :=
  let bytes := (⟨#[0xff, 0xee]⟩ : ByteArray) ++ payload ++ ⟨#[0xdd]⟩
  match reader { bytes, idx := 2 } with
  | .error _ _ => false
  | .ok value finish =>
    value == expected && finish.bytes == bytes && finish.idx == 2 + payload.size &&
      units value ≤ 2 * (finish.idx - 2)

def resourceExpr (value : Ixon.Expr) : Bool :=
  resourceRead Ixon.getExpr (fun expr => expr.resourceSize + 1) (Ixon.serExpr value) value

def resourceConstant (value : Ixon.Constant) : Bool :=
  let bytes := Ixon.serConstant value
  let nodes := Ixon.Bounded.univNodes value.univs
  resourceRead Ixon.getConstant Ixon.Constant.resourceSize bytes value &&
    match Ixon.Bounded.deConstant bytes.size nodes bytes with
    | .error _ => false
    | .ok decoded => decoded.resourceSize + Ixon.Bounded.univNodes decoded.univs ≤ 2 * bytes.size + nodes

#guard (variants ++ falseStore ++ separatedFalse).all fun (_, value) => resourceConstant value
#guard resourceConstant sharedIdentity
#guard resourceConstant sharedUniverseBudget
#guard resourceConstant ⟨.muts #[], #[], #[], #[]⟩
#guard resourceConstant ⟨.muts #[], Array.replicate 128 (.var 0),
  Array.replicate 128 (address 0), Array.replicate 128 .zero⟩
#guard alternateSpellings.all fun bytes =>
  match Ixon.deConstantExact bytes with
  | .error _ => false
  | .ok value => resourceRead Ixon.getConstant Ixon.Constant.resourceSize bytes value

#guard wordBoundaries.all fun n =>
  [Ixon.Expr.var n, .sort n, .str n, .nat n, .share n,
    .ref n #[n], .recur n #[n], .prj n n (.var 0)].all resourceExpr
-- Every v3 binder contract, forall result contract, and let flag spelling.
#guard binderContracts.all fun binder =>
  valueContracts.all fun result =>
    letContracts binder |>.all fun letContract =>
      resourceExpr (.all binder result (.sort 0)
        (.lam binder (.var 0) (.letE letContract (.var 1) (.var 0) (.var 0))))
#guard resourceExpr (.letE (.lean false) (.sort 0) (.app (.var 0) (.var 1)) (.var 2))
#guard [0, 1, 7, 8, 31, 32, 128, 1024].all fun n =>
  let levels := Array.replicate n 0
  (Ixon.Expr.ref 0 levels).resourceSize == n + 1 &&
    resourceExpr (.ref 0 levels) && resourceExpr (.recur 0 levels)
#guard [1, 7, 8, 31, 32, 128].all fun n =>
  resourceExpr ((List.range n).foldl (fun e _ => .app e (.var 0)) (.var 0)) &&
    resourceExpr ((List.range n).foldl (fun e _ => .lam .many (.sort 0) e) (.var 0)) &&
    resourceExpr ((List.range n).foldl (fun e _ => .all .many .shared (.sort 0) e) (.var 0))

-- Compressed application spines can contain more constructors than bytes;
-- a one-unit-per-byte claim would be false even on canonical input.
def compressedApp : Ixon.Expr :=
  (List.range 128).foldl (fun e _ => .app e (.var 0)) (.var 0)

#guard compressedApp.resourceSize > (Ixon.serExpr compressedApp).size
#guard resourceExpr compressedApp
-- Ixon v3's production reader rejects nonminimal tag spellings.
#guard match Ixon.deExpr ⟨#[0x18, 0]⟩ with
  | .error e => e == "noncanonical Tag4 integer"
  | .ok _ => false

def failsAt (reader : Ixon.GetM α) (bytes : ByteArray) (start finish : Nat) : Bool :=
  match reader { bytes, idx := start } with
  | .error _ state => state.bytes == bytes && state.idx == finish
  | .ok _ _ => false

-- UInt64.max counts stop at the first failed element. A malformed element
-- with a valid element after it checks short-circuiting independently of EOF.
#guard failsAt (Ixon.getArray Ixon.getU8 18446744073709551615) ⟨#[9, 8, 7, 6, 5]⟩ 2 5
#guard failsAt (Ixon.getArray Ixon.getExpr 18446744073709551615) ⟨#[9, 8, 0x10, 0xc0, 0x10]⟩ 2 4
#guard failsAt (Ixon.getArray Ixon.getTag0 18446744073709551615) ⟨#[9, 8, 0, 0x88, 0]⟩ 2 4
#guard failsAt (Ixon.getArray (Ixon.Serialize.get : Ixon.GetM Address) 18446744073709551615)
  ⟨Array.replicate 65 0⟩ 2 34
#guard failsAt (Ixon.getArray Ixon.getExpr 18446744073709551615) ⟨#[0x10, 0x10]⟩ 0 2

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.deConstantExact (Ixon.serConstant value) = .ok value :=
  Ix.Ixon.Verify.deConstantExact_serConstant value h

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.Bounded.deConstant (Ixon.serConstant value).size
      (Ixon.Bounded.univNodes value.univs) (Ixon.serConstant value) = .ok value :=
  Ix.Ixon.Verify.BoundedConstant.deConstant_serConstant value h _ _ (by omega) (by omega)

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.Canonical.deConstant (Ixon.serConstant value).size
      (Ixon.Bounded.univNodes value.univs) (Ixon.serConstant value) = .ok value :=
  Ix.Ixon.Verify.Canonical.deConstant_serConstant value h _ _ (by omega) (by omega)

example (start finish : Ixon.GetState) (value : Ixon.Expr)
    (valid : start.idx ≤ start.bytes.size) (read : Ixon.getExpr start = .ok value finish) :
    value.resourceSize + 1 ≤ 2 * (finish.idx - start.idx) :=
  (Ix.Ixon.Verify.ReaderBounds.getExpr_bound _ _ _ valid read).units_le

example (bytes : ByteArray) (value : Ixon.Constant)
    (read : Ixon.deConstantExact bytes = .ok value) : value.resourceSize ≤ 2 * bytes.size :=
  Ix.Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes value read

end Tests.Ix.Kernel.Codec

/-- Independently specified Ixon v3 expression bytes from upstream
`Tests/Fixtures/ixon-v3/expressions.txt` (the binder, result, and let contract
cases), checked for the codec's exact round trip. -/
def upstreamV3Expressions : List (String × List UInt8) := [
  ("app", [0x73, 0x13, 0x12, 0x11, 0x10]),
  ("lam", [0x83, 0x07, 0x00, 0x07, 0x00, 0x07, 0x00, 0x10]),
  ("lam_local_unique", [0x81, 0x09, 0x00, 0x10]),
  ("lam_affine_local", [0x81, 0x0e, 0x00, 0x10]),
  ("all", [0x92, 0x29, 0x00, 0x17, 0x00, 0x10]),
  ("ordinary_let", [0xa1, 0x00, 0x00, 0x61, 0x10]),
  ("local_unique_let", [0xa0, 0x0a, 0x00, 0x11, 0x10]),
  ("borrow", [0xa2, 0x0e, 0x00, 0x41, 0x02, 0x11, 0x10]),
  ("borrow_nondep", [0xa3, 0x0f, 0x00, 0x11, 0x10])]

#guard upstreamV3Expressions.all fun (_, bytes) =>
  match Ixon.deExpr ⟨bytes.toArray⟩ with
  | .ok source => Ixon.serExpr source == ⟨bytes.toArray⟩
  | .error _ => false

-- Ixon v3 admits single-use sharing entries: canonical decoding accepts a
-- table slot referenced exactly once (the certified entry's verdict is in
-- `Tests.Ix.Kernel.ByteAdmission`).
def singleUseSharing : Ixon.Constant :=
  { identity with
    sharing := #[.var 0]
    info := .defn ⟨.defn, .safe, 1, idType, .leanLam (.sort 0) (.leanLam (.var 0) (.share 0))⟩ }

#guard match Ixon.Canonical.deConstant 256 64 (Ixon.serConstant singleUseSharing) with
  | .ok value => value == singleUseSharing
  | .error _ => false
