module

public import LSpec
public import Ix.Aiur
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.U64.Goldilocks
public import Ix.IxVM.U64.Small

/-!
The U64 boundary interface (`flatten_u64` / `idx_to_u64`, see
`Ix/IxVM/U64/`) under both implementations, executed by the bytecode
interpreter: the Goldilocks form packs 7 bytes, the small-field form 3 and
rejects anything wider — a checked embedding, never a wrap.
-/

public section

open LSpec Aiur

namespace AiurTests.U64

/-- Entrypoints exercising the boundary. Each returns `1` on success; a
failing `assert_eq!` aborts execution, which is the negative signal. -/
def boundaryTests : Source.Toplevel := ⟦
  -- 3 bytes: representable under both forms.
  pub fn u64_roundtrip_narrow() -> G {
    let x = flatten_u64([1u8, 2u8, 3u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    assert_eq!(x, 197121, "narrow pack");
    let [b0, b1, b2, b3, b4, b5, b6, b7] = idx_to_u64(197121);
    assert_eq!(to_field(b0) + 1000 * to_field(b1) + 1000000 * to_field(b2), 3002001, "narrow unpack");
    assert_eq!(to_field(b3) + to_field(b4) + to_field(b5) + to_field(b6) + to_field(b7), 0, "narrow high bytes");
    1
  }

  -- 7 bytes: representable under Goldilocks only.
  pub fn u64_roundtrip_wide() -> G {
    let x = flatten_u64([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8]);
    assert_eq!(x, 281474976710657, "wide pack");
    let [b0, b1, b2, b3, b4, b5, b6, b7] = idx_to_u64(281474976710657);
    assert_eq!(to_field(b0) + 2 * to_field(b6), 3, "wide unpack");
    assert_eq!(to_field(b1) + to_field(b2) + to_field(b3) + to_field(b4) + to_field(b5) + to_field(b7), 0, "wide zero bytes");
    1
  }

  -- 2^24: the first value the small form must refuse.
  pub fn u64_pack_2_24() -> G {
    let x = flatten_u64([0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8]);
    assert_eq!(x, 16777216, "2^24 pack");
    1
  }
⟧

def toplevelOver (u64 : Source.Toplevel) : Except Global Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  let t ← t.merge u64
  t.merge boundaryTests

/-- Runs `name` in the toplevel over `u64`; `some true` when it returns `1`,
`some false` when execution fails (a failed assert), `none` on a setup
problem. -/
def run (u64 : Source.Toplevel) (name : Lean.Name) : Option Bool := do
  let top ← (toplevelOver u64).toOption
  let compiled ← top.compile.toOption
  let idx ← compiled.getFuncIdx name
  match compiled.bytecode.execute idx #[] default with
  | .error _ => some false
  | .ok (output, _, _) => some (output == #[Aiur.G.ofNat 1])

def tests : TestSeq :=
  test "goldilocks: narrow roundtrip" (run IxVM.u64Goldilocks `u64_roundtrip_narrow == some true) ++
  test "goldilocks: wide (7-byte) roundtrip" (run IxVM.u64Goldilocks `u64_roundtrip_wide == some true) ++
  test "goldilocks: packs 2^24" (run IxVM.u64Goldilocks `u64_pack_2_24 == some true) ++
  test "small: narrow roundtrip" (run IxVM.u64Small `u64_roundtrip_narrow == some true) ++
  test "small: wide (7-byte) value is rejected" (run IxVM.u64Small `u64_roundtrip_wide == some false) ++
  test "small: 2^24 is rejected (checked embedding)" (run IxVM.u64Small `u64_pack_2_24 == some false)

end AiurTests.U64
