import IxC.Ixon.Verify
import IxC.Ixon.Canonical
import IxC.Fixtures.IxonFixtures

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
    Ixon.putTagN 0 0 0
    Ixon.putTagN 0 0 0
    Ixon.putTagN 0 0 count
    Ixon.putBytes payload

/-- An empty block whose sharing count is the raw bytes `count`, followed by
empty reference and universe tables. -/
def recordSharingCount (count : List UInt8) : ByteArray := Ixon.runPut do
  Ixon.putConstantInfo (.muts #[])
  Ixon.putBytes ⟨count.toArray⟩
  Ixon.putTagN 0 0 0
  Ixon.putTagN 0 0 0

/-- The sharing count is `0xC4`: code 4 of an `f = 0` TagN header, which no
rung uses. -/
def invalidSharingCount : ByteArray := recordSharingCount [0xC4]

def nonBooleanAxiom : ByteArray := Ixon.runPut do
  Ixon.putTagN 4 Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_AXIO
  Ixon.putU8 2
  Ixon.putTagN 0 0 0
  Ixon.putExpr (.sort 0)
  Ixon.putTagN 0 0 0
  Ixon.putTagN 0 0 0
  Ixon.putTagN 0 0 0

-- Production decoding accepts these alternate universe spellings. Canonical
-- decoding rejects nonmaximal successor chains and ignored universe tag sizes
-- rather than normalizing their bytes.
def alternateSpellings : List ByteArray := [
  recordUnivsPayload 1 ⟨#[1, 1, 0]⟩,
  recordUnivsPayload 1 ⟨#[0x41, 0, 0]⟩]

/-! ### TagN integers

Ixon v4 writes every integer as TagN (`Ixon.putTagN f flag value`, `f ∈ {0,
2, 4}`): six rungs of 1, 2, 3, 4, 5 and 9 bytes, each starting where the
previous one ends, so every value has exactly one encoding and there is no
nonminimal spelling to reject. The reader rejects exactly an invalid code
(`f = 0, 2`), a 9-byte value reaching `2^64`, and truncation. The vectors are
sharing's `Tests.Ixon.tagNUnits` (`Tests/Ix/Ixon.lean`) and the rejection
vectors of `Tests/Ix/IxVM/TagN.lean`. -/

/-- `(f, flag, value, bytes)`: the encodings of `Tests.Ixon.tagNUnits`, the
first and last value of every rung, and `2^64 - 1` for each `f`. -/
def tagNVectors : List (Nat × UInt8 × UInt64 × List UInt8) := [
  (4, 0xA, 7, [0xA7]),
  (4, 0xA, 8, [0xA8, 0x00]),
  (4, 0x1, 1031, [0x1B, 0xFF]),
  (4, 0, 1032, [0x0C, 0x00, 0x00]),
  (4, 0, 66567, [0x0C, 0xFF, 0xFF]),
  (4, 0, 66568, [0x0D, 0, 0, 0]),
  (4, 0, 16843783, [0x0D, 0xFF, 0xFF, 0xFF]),
  (4, 0, 16843784, [0x0E, 0, 0, 0, 0]),
  (4, 0, 4311811079, [0x0E, 0xFF, 0xFF, 0xFF, 0xFF]),
  (4, 0, 4311811080, [0x0F, 0, 0, 0, 0, 0, 0, 0, 0]),
  (4, 0, 18446744073709551615, [0x0F, 0xF7, 0xFB, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]),
  (0, 0, 127, [0x7F]),
  (0, 0, 128, [0x80, 0x00]),
  (0, 0, 16512, [0xC0, 0x00, 0x00]),
  (0, 0, 82047, [0xC0, 0xFF, 0xFF]),
  (0, 0, 82048, [0xC1, 0, 0, 0]),
  (0, 0, 16859263, [0xC1, 0xFF, 0xFF, 0xFF]),
  (0, 0, 16859264, [0xC2, 0, 0, 0, 0]),
  (0, 0, 4311826560, [0xC3, 0, 0, 0, 0, 0, 0, 0, 0]),
  (0, 0, 18446744073709551615, [0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]),
  (2, 3, 32, [0xE0, 0x00]),
  (2, 3, 4128, [0xF0, 0x00, 0x00]),
  (2, 3, 69663, [0xF0, 0xFF, 0xFF]),
  (2, 3, 69664, [0xF1, 0, 0, 0]),
  (2, 3, 16846879, [0xF1, 0xFF, 0xFF, 0xFF]),
  (2, 3, 16846880, [0xF2, 0, 0, 0, 0]),
  (2, 3, 4311814176, [0xF3, 0, 0, 0, 0, 0, 0, 0, 0]),
  (2, 0, 18446744073709551615, [0x33, 0xDF, 0xEF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF])]

-- Each vector is written exactly and read back exactly.
#guard tagNVectors.all fun (f, flag, value, bytes) =>
  Ixon.runPut (Ixon.putTagN f flag value) == ⟨bytes.toArray⟩ &&
    match Ixon.runGetExact (Ixon.getTagN f) ⟨bytes.toArray⟩ with
    | .ok tag => tag == ⟨flag, value⟩
    | .error _ => false

/-- `(f, bytes, reason, stop)`: every rejection vector of `tagNUnits`, with the
reader's reason and the cursor it stops at. Invalid codes stop right after
the header byte, overflow after the 8-byte payload, truncation at the end of
the input. -/
def tagNRejected : List (Nat × List UInt8 × String × Nat) := [
  (2, [0x34], "invalid TagN code 4", 1),
  (2, [0x3F], "invalid TagN code 15", 1),
  (0, [0xC4], "invalid TagN code 4", 1),
  (0, [0xFF], "invalid TagN code 63", 1),
  (0, [0xC4, 0x00, 0x00], "invalid TagN code 4", 1),
  (2, [0x34, 0x00, 0x00], "invalid TagN code 4", 1),
  (0, [0xC4, 0, 0, 0, 0, 0, 0, 0, 0], "invalid TagN code 4", 1),
  (4, [0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF], "TagN value exceeds UInt64", 9),
  (0, [0xC3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF], "TagN value exceeds UInt64", 9),
  -- The smallest overflowing 9-byte payloads, one past `2^64 - 1` above.
  (0, [0xC3, 0x80, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF], "TagN value exceeds UInt64", 9),
  (2, [0x33, 0xE0, 0xEF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF], "TagN value exceeds UInt64", 9),
  (4, [0x0F, 0xF8, 0xFB, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF], "TagN value exceeds UInt64", 9),
  (4, [0x08], "EOF", 1),
  (4, [0x0D, 0x00, 0x00], "EOF", 3),
  (4, [0x0E, 0x00, 0x00, 0x00], "EOF", 4),
  (4, [0x0F, 0x00, 0x00, 0x00], "EOF", 4)]

#guard tagNRejected.all fun (f, bytes, reason, stop) =>
  match Ixon.getTagN f { bytes := ⟨bytes.toArray⟩ } with
  | .error e state => e == reason && state.idx == stop
  | .ok _ _ => false
-- A complete encoding followed by a byte is not an exact read.
#guard match Ixon.runGetExact (Ixon.getTagN 4) ⟨#[0x07, 0x00]⟩ with
  | .error e => e == "trailing bytes: consumed 1 of 2"
  | .ok _ => false

-- Ixon v4's production decoder rejects an invalid TagN code, a TagN value
-- reaching 2^64, truncation and non-Boolean flags; the bounded and canonical
-- decoders report its reason. The integers are a record's sharing count
-- (`f = 0`) and a universe term (`f = 2`).
def decoderRejectedSpellings : List (ByteArray × String) := [
  (invalidSharingCount, "invalid TagN code 4"),
  (recordSharingCount [0xC4, 0x00, 0x00], "invalid TagN code 4"),
  (recordUnivsPayload 1 ⟨#[0x34]⟩, "invalid TagN code 4"),
  (recordUnivsPayload 1 ⟨#[0x3F]⟩, "invalid TagN code 15"),
  (recordSharingCount [0xC3, 0x80, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF], "TagN value exceeds UInt64"),
  (recordUnivsPayload 1 ⟨#[0x33, 0xE0, 0xEF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]⟩,
    "TagN value exceeds UInt64"),
  (recordSharingCount [0xC3, 0x00, 0x00, 0x00], "EOF"),
  (nonBooleanAxiom, "expected Bool (0 or 1), got 2")]

#guard decoderRejectedSpellings.all fun (bytes, reason) =>
  (match Ixon.deConstantExact bytes with | .error e => e == reason | .ok _ => false) &&
  (match Ixon.Bounded.deConstant 256 64 bytes with | .error e => e == reason | .ok _ => false) &&
  (match Ixon.Canonical.deConstant 256 64 bytes with | .error e => e == reason | .ok _ => false)

-- The integer spellings Ixon v3 rejected as nonminimal are the unique v4
-- encodings of other values: Tag0 `80 00` is TagN 128 (rung 2 of `f = 0`),
-- and Tag2 `E0 00` is the universe variable 32 (rung 2 of `f = 2`, flag 3),
-- which every decoder, the canonical one included, accepts.
#guard match Ixon.runGetExact (Ixon.getTagN 0) ⟨#[0x80, 0x00]⟩ with
  | .ok tag => tag == ⟨0, 128⟩
  | .error _ => false
#guard [Ixon.deConstantExact, Ixon.Bounded.deConstant 256 64, Ixon.Canonical.deConstant 256 64].all
  fun decode => match decode (recordUnivsPayload 1 ⟨#[0xE0, 0x00]⟩) with
    | .ok value => value == ⟨.muts #[], #[], #[], #[.var 32]⟩
    | .error _ => false

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
  Ixon.putTagN 0 0 18446744073709551615)).isOk
#guard !(Ixon.Bounded.deConstant 256 64 (Ixon.runPut do
  Ixon.putConstantInfo (.muts #[])
  Ixon.putTagN 0 0 0
  Ixon.putTagN 0 0 18446744073709551615)).isOk

/-- Byte and word boundaries, and every TagN rung boundary (the last value of
a rung, the first of the next, and one past it) for `f = 0, 2, 4`. -/
def wordBoundaries : List UInt64 :=
  [0, 1, 7, 8, 31, 32, 127, 128, 255, 256, 65535, 65536, 18446744073709551615] ++
    [0, 2, 4].flatMap fun f =>
      [Ixon.tagNEnd1 f, Ixon.tagNEnd2 f, Ixon.tagNEnd3 f, Ixon.tagNEnd4 f, Ixon.tagNEnd5 f].flatMap
        fun e => [(e - 1).toUInt64, e.toUInt64, (e + 1).toUInt64]

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

-- Ten bytes can request UInt64.max successor nodes (`addSucc` with count
-- `2^64 - 1`: the 9-byte TagN of `f = 2`, flag 0, then the base `zero`).
-- Rejection must happen before successor construction, even when the encoded
-- base is present.
def successorBomb : ByteArray :=
  ⟨#[0x33, 0xDF, 0xEF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF, 0]⟩

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

/-- All sixteen Ixon binder contracts, four value contracts, and the four let
flag spellings over a binder. -/
def binderContracts : List Ixon.BinderContract :=
  (List.range 16).filterMap fun bits => Ixon.BinderContract.ofBits? bits.toUInt8
def valueContracts : List Ixon.ValueContract :=
  (List.range 4).filterMap fun bits => Ixon.ValueContract.ofBits? bits.toUInt8
def letContracts (binder : Ixon.BinderContract) : List Ixon.LetContract :=
  (List.range 4).filterMap fun flags => Ixon.LetContract.ofFlags? flags.toUInt64 binder
#guard binderContracts.length == 16 && valueContracts.length == 4 &&
  (letContracts .many).length == 4

-- Every Ixon binder contract, forall result contract, and let flag spelling.
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
-- Even the prefix API rejects an invalid TagN code followed by as many bytes
-- as the 9-byte rung reads, and a 9-byte value reaching 2^64.
#guard !(Ixon.runGet (Ixon.getTagN 0) ⟨#[0xC4, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩).isOk
#guard !(Ixon.runGet (Ixon.getTagN 0) ⟨#[0xC3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0]⟩).isOk

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
-- Every Ixon binder contract, forall result contract, and let flag spelling.
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
-- `18 00`, which Ixon v3 rejected as a nonminimal Tag4 spelling of `var 0`,
-- is in v4 the unique encoding of `var 8` (the first value of rung 2 of
-- `f = 4`; `tagn4_rung2_first` in `Tests/Fixtures/ixon-v4/expressions.txt`).
#guard match Ixon.deExpr ⟨#[0x18, 0]⟩ with
  | .ok value => value == .var 8 && Ixon.serExpr value == ⟨#[0x18, 0]⟩
  | .error _ => false

def failsAt (reader : Ixon.GetM α) (bytes : ByteArray) (start finish : Nat) : Bool :=
  match reader { bytes, idx := start } with
  | .error _ state => state.bytes == bytes && state.idx == finish
  | .ok _ _ => false

-- UInt64.max counts stop at the first failed element. A malformed element
-- with a valid element after it checks short-circuiting independently of EOF.
#guard failsAt (Ixon.getArray Ixon.getU8 18446744073709551615) ⟨#[9, 8, 7, 6, 5]⟩ 2 5
#guard failsAt (Ixon.getArray Ixon.getExpr 18446744073709551615) ⟨#[9, 8, 0x10, 0xc0, 0x10]⟩ 2 4
#guard failsAt (Ixon.getArray (Ixon.getTagN 0) 18446744073709551615) ⟨#[9, 8, 0, 0xC4, 0]⟩ 2 4
#guard failsAt (Ixon.getArray (Ixon.Serialize.get : Ixon.GetM Address) 18446744073709551615)
  ⟨Array.replicate 65 0⟩ 2 34
#guard failsAt (Ixon.getArray Ixon.getExpr 18446744073709551615) ⟨#[0x10, 0x10]⟩ 0 2

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.deConstantExact (Ixon.serConstant value) = .ok value :=
  Ixon.Verify.deConstantExact_serConstant value h

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.Bounded.deConstant (Ixon.serConstant value).size
      (Ixon.Bounded.univNodes value.univs) (Ixon.serConstant value) = .ok value :=
  Ixon.Verify.BoundedConstant.deConstant_serConstant value h _ _ (by omega) (by omega)

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.Canonical.deConstant (Ixon.serConstant value).size
      (Ixon.Bounded.univNodes value.univs) (Ixon.serConstant value) = .ok value :=
  Ixon.Verify.Canonical.deConstant_serConstant value h _ _ (by omega) (by omega)

example (start finish : Ixon.GetState) (value : Ixon.Expr)
    (valid : start.idx ≤ start.bytes.size) (read : Ixon.getExpr start = .ok value finish) :
    value.resourceSize + 1 ≤ 2 * (finish.idx - start.idx) :=
  (Ixon.Verify.ReaderBounds.getExpr_bound _ _ _ valid read).units_le

example (bytes : ByteArray) (value : Ixon.Constant)
    (read : Ixon.deConstantExact bytes = .ok value) : value.resourceSize ≤ 2 * bytes.size :=
  Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes value read

end Tests.Ix.Kernel.Codec

/-- Independently specified Ixon v4 expression bytes, every vector of
`Tests/Fixtures/ixon-v4/expressions.txt`: the binder, result and let contract
cases (all integers in rung 1, so byte-identical to Ixon v3), and the
multi-byte TagN cases (the first and last value of every rung of `f = 4` and
`f = 0`, a count of 8 and a rung-3 `Share`), checked for the codec's exact
round trip. -/
def upstreamV4Expressions : List (String × List UInt8) := [
  ("app", [0x73, 0x13, 0x12, 0x11, 0x10]),
  ("lam", [0x83, 0x07, 0x00, 0x07, 0x00, 0x07, 0x00, 0x10]),
  ("lam_local_unique", [0x81, 0x09, 0x00, 0x10]),
  ("lam_affine_local", [0x81, 0x0e, 0x00, 0x10]),
  ("all", [0x92, 0x29, 0x00, 0x17, 0x00, 0x10]),
  ("ordinary_let", [0xa1, 0x00, 0x00, 0x61, 0x10]),
  ("local_unique_let", [0xa0, 0x0a, 0x00, 0x11, 0x10]),
  ("borrow", [0xa2, 0x0e, 0x00, 0x41, 0x02, 0x11, 0x10]),
  ("borrow_nondep", [0xa3, 0x0f, 0x00, 0x11, 0x10]),
  ("reference", [0x20, 0x00]),
  ("recursion", [0x32, 0x02, 0x00, 0x01]),
  ("tagn4_rung1_last", [0x17]),
  ("tagn4_rung2_first", [0x18, 0x00]),
  ("tagn4_rung2_last", [0x1b, 0xff]),
  ("tagn4_rung3_first", [0x1c, 0x00, 0x00]),
  ("tagn4_rung3_last", [0x1c, 0xff, 0xff]),
  ("tagn4_rung4_first", [0x1d, 0x00, 0x00, 0x00]),
  ("tagn4_rung4_last", [0x1d, 0xff, 0xff, 0xff]),
  ("tagn4_rung5_first", [0x1e, 0x00, 0x00, 0x00, 0x00]),
  ("tagn4_rung5_last", [0x1e, 0xff, 0xff, 0xff, 0xff]),
  ("tagn4_rung6_first", [0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
  ("tagn4_rung6_last", [0x1f, 0xf7, 0xfb, 0xfe, 0xfe, 0xfe, 0xff, 0xff, 0xff]),
  ("tagn0_rung1_last", [0x20, 0x7f]),
  ("tagn0_rung2_first", [0x20, 0x80, 0x00]),
  ("tagn0_rung2_last", [0x20, 0xbf, 0xff]),
  ("tagn0_rung3_first", [0x20, 0xc0, 0x00, 0x00]),
  ("tagn0_rung3_last", [0x20, 0xc0, 0xff, 0xff]),
  ("tagn0_rung4_first", [0x20, 0xc1, 0x00, 0x00, 0x00]),
  ("tagn0_rung4_last", [0x20, 0xc1, 0xff, 0xff, 0xff]),
  ("tagn0_rung5_first", [0x20, 0xc2, 0x00, 0x00, 0x00, 0x00]),
  ("tagn0_rung5_last", [0x20, 0xc2, 0xff, 0xff, 0xff, 0xff]),
  ("tagn0_rung6_first", [0x20, 0xc3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
  ("tagn0_rung6_last", [0x20, 0xc3, 0x7f, 0xbf, 0xfe, 0xfe, 0xfe, 0xff, 0xff, 0xff]),
  ("app_telescope_8", [0x78, 0x00, 0x18, 0x00, 0x17, 0x16, 0x15, 0x14, 0x13, 0x12, 0x11, 0x10]),
  ("ref_univs_8", [0x28, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]),
  ("share_rung3", [0xbc, 0x00, 0x00])]

#guard upstreamV4Expressions.length == 36
#guard upstreamV4Expressions.all fun (_, bytes) =>
  match Ixon.deExpr ⟨bytes.toArray⟩ with
  | .ok source => Ixon.serExpr source == ⟨bytes.toArray⟩
  | .error _ => false

/-- The values the fixture's rung vectors encode, from its rung table:
`tagn4_rungK_{first,last}` is `var` of the first and last value of rung `K`
of `f = 4`, `tagn0_rungK_{first,last}` a `ref` whose index is that value for
`f = 0`; and its last three vectors. -/
def rungValue (f : Nat) (first : Bool) (rung : Nat) : UInt64 :=
  let ends := [0, Ixon.tagNEnd1 f, Ixon.tagNEnd2 f, Ixon.tagNEnd3 f, Ixon.tagNEnd4 f,
    Ixon.tagNEnd5 f, 2 ^ 64]
  (if first then ends[rung - 1]! else ends[rung]! - 1).toUInt64

def upstreamV4Values : List (String × Ixon.Expr) :=
  ("tagn4_rung1_last", .var (rungValue 4 false 1)) ::
  ("tagn0_rung1_last", .ref (rungValue 0 false 1) #[]) ::
  ([2, 3, 4, 5, 6].flatMap fun rung =>
    [(s!"tagn4_rung{rung}_first", .var (rungValue 4 true rung)),
     (s!"tagn4_rung{rung}_last", .var (rungValue 4 false rung)),
     (s!"tagn0_rung{rung}_first", .ref (rungValue 0 true rung) #[]),
     (s!"tagn0_rung{rung}_last", .ref (rungValue 0 false rung) #[])]) ++
  [("app_telescope_8", (List.range 8).foldl (fun e i => .app e (.var (7 - i).toUInt64)) (.var 8)),
   ("ref_univs_8", .ref 0 #[0, 1, 2, 3, 4, 5, 6, 7]),
   ("share_rung3", .share 1032)]

#guard upstreamV4Values.length == 25
#guard upstreamV4Values.all fun (name, value) =>
  match upstreamV4Expressions.lookup name with
  | some bytes => match Ixon.deExpr ⟨bytes.toArray⟩ with
    | .ok decoded => decoded == value
    | .error _ => false
  | none => false

-- Ixon v4 does not check on read that a record's sharing table is the
-- canonical one (`canonicalSharingTiered` of its roots): canonical decoding
-- accepts any backward table, here a slot referenced exactly once (the
-- certified entry's verdict is in `Tests.Ix.Kernel.ByteAdmission`).
def singleUseSharing : Ixon.Constant :=
  { identity with
    sharing := #[.var 0]
    info := .defn ⟨.defn, .safe, 1, idType, .leanLam (.sort 0) (.leanLam (.var 0) (.share 0))⟩ }

#guard match Ixon.Canonical.deConstant 256 64 (Ixon.serConstant singleUseSharing) with
  | .ok value => value == singleUseSharing
  | .error _ => false
