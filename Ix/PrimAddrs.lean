module

public import Ix.Address
public import Std.Data.HashSet

/-!
# The canonical primitive addresses (Address-only)

Mirror: crates/common/src/prim_addrs.rs (`PrimAddrs::new()`).

The primitive and reserved-marker content addresses, the Lean parity table,
and their membership set are shared by the resource validator and IxVM claim
harness. They require only the address representation, independently of the
kernel typechecker.
The addresses are hardcoded BLAKE3 hashes matching `PrimAddrs::new()` in
`ix-common`; regenerate them as `docs/kernel.md` describes (`lake exe
ixon-v4-primitives`; `lake test -- --ignored rust-kernel-build-primitives`
prints the table in `PrimAddrs::new` form) and update both tables. The ordered
live comparison is
`Tests.Ix.Kernel.PrimitiveTable` in the `prim-addrs` entry.

`Lean.reduceBool` and `Lean.reduceNat` dispatch by their real content
addresses. `eagerReduce` is a synthetic kernel-only marker: Lean's real
`eagerReduce` compiles to the same canonical content address as `id`, so
address-only dispatch on that real constant would be unsound. The
`pprod`/`pprodMk` addresses support nested-inductive recursor generation.
-/

public section
@[expose] section

namespace Ix

/-- Hardcoded canonical primitive addresses (for lookup in the env). -/
structure PrimAddrs where
  nat : Address
  natZero : Address
  natSucc : Address
  natAdd : Address
  natPred : Address
  natSub : Address
  natMul : Address
  natPow : Address
  natGcd : Address
  natMod : Address
  natDiv : Address
  natBitwise : Address
  natBeq : Address
  natBle : Address
  natLand : Address
  natLor : Address
  natXor : Address
  natShiftLeft : Address
  natShiftRight : Address
  boolType : Address
  boolTrue : Address
  boolFalse : Address
  string : Address
  stringMk : Address
  charType : Address
  charMk : Address
  charOfNat : Address
  stringOfList : Address
  stringToByteArray : Address
  byteArrayEmpty : Address
  list : Address
  listNil : Address
  listCons : Address
  eq : Address
  eqRefl : Address
  quotType : Address
  quotCtor : Address
  quotLift : Address
  quotInd : Address
  reduceBool : Address
  reduceNat : Address
  eagerReduce : Address
  systemPlatformNumBits : Address
  systemPlatformGetNumBits : Address
  subtypeVal : Address
  natDecLe : Address
  natDecEq : Address
  natDecLt : Address
  decidableRec : Address
  decidableIsTrue : Address
  decidableIsFalse : Address
  natLeOfBleEqTrue : Address
  natNotLeOfNotBleEqTrue : Address
  natEqOfBeqEqTrue : Address
  natNeOfBeqEqFalse : Address
  fin : Address
  boolNoConfusion : Address
  int : Address
  intOfNat : Address
  intNegSucc : Address
  intAdd : Address
  intSub : Address
  intMul : Address
  intNeg : Address
  intEmod : Address
  intEdiv : Address
  intBmod : Address
  intBdiv : Address
  intNatAbs : Address
  intPow : Address
  intDecEq : Address
  intDecLe : Address
  intDecLt : Address
  punit : Address
  pprod : Address
  pprodMk : Address
  natRec : Address
  natCasesOn : Address
  bitVec : Address
  bitVecToNat : Address
  bitVecOfNat : Address
  bitVecUlt : Address
  decidableDecide : Address
  ltLt : Address
  ofNatOfNat : Address
  unit : Address
  punitSizeOf1 : Address
  sizeOfSizeOf : Address
  stringBack : Address
  stringUtf8ByteSize : Address
  stringAppend : Address
  stringDecEq : Address

namespace PrimAddrs

def h (hex : String) : Address :=
  (Address.fromString hex).getD default

/-- Canonical content-hash addresses, hardcoded from the Ixon-compiled form
    of each primitive (byte-for-byte from Rust `PrimAddrs::new()`).

    `eagerReduce` is intentionally not a compiled Lean content hash — see the
    module doc. -/
def canonical : PrimAddrs where
  nat := h "4eff35f9c8a98dc247d142cc249f4b3985df15f343536919e12edfa72bc4dd93"
  natZero := h "c71205099a2902497f2150ab8e4cde07de6f7bacd9c92483bce4de96f137b14b"
  natSucc := h "8b1290e5bef5ec6fe00b659cd3488cf300b8393ec2dcccb7bc54c106213d9b21"
  natAdd := h "dddceb4ce8f1c5e7a7a0a208d3a15e70b50c149577431658f50c39ddeb1ff2a0"
  natPred := h "542e0c31f900818c9340ab6c892884e7cb986f6bf0dcc026971c1f69a3051465"
  natSub := h "fef3e836e9df48c4df01657d7affa51fc45a8cef0ca88c2a4f573f467041a895"
  natMul := h "ed09022d61ed8a1dbf0a8984ddc6b8f64c53c07aa1faf2a439644fc56f72c92d"
  natPow := h "9f5172c1cb62afa53e3a1006990f49494bd2ccf15a6935780b8e2db36b9121e0"
  natGcd := h "fe8e2ec10f267f0993337ec3ecc95b83dbc813c0d772cecf0ec314e1be91c406"
  natMod := h "9ecd2580ba1e3f1167cd101da660a8a275ca4ababc5852953dcfc91110970121"
  natDiv := h "3b449ee19fedf5943e918bdb4b1d434aa9e62cc0c8ab478eb10ddd2df43bfcf7"
  natBitwise := h "7d0cc9e9aba5f2621021c034702b0c5751718e402b69c178972da23da3937d3d"
  natBeq := h "60715a1e76d31403a223485f28c74c4270b2bca66c437e9e11d1a5aff17ec861"
  natBle := h "7ca154b768ee1421e4c68b931d29911325e342d821a53888e4647b706cab4caa"
  natLand := h "96e8408ccea0c808203eae83c07af598c7e6c7be42a41162cc25e89fad7a648e"
  natLor := h "924195bf8769c1f82b1e9643f51896ace6f4474b9bccd451a6243287cf38039e"
  natXor := h "2a854ccfd0f62a8a699e38607c0350853e324d790c40a4f27f1d684dca85bfcd"
  natShiftLeft := h "6c5331afbd9de5eaeaeff6647398ebac0d71f6728946915b9e7df752cc5f25b1"
  natShiftRight := h "830fc024c194ad2ffa0f093ac8df77af05f32c9f06723f5effa9d369bd2f019b"
  boolType := h "77db82d7052a606eaaf324893161d6989049ef4e0f393e2fe9edaf52f4225ed8"
  boolTrue := h "ef156463a527bfd236472e606b2ccddf73f4585195e365e0430ee3c20921d8cc"
  boolFalse := h "a5fc856de635cfc40ab703eea51cb704dce6985fd7de921f94b8d635e9d3667f"
  string := h "9453b6b0aeb66e0cd6e36b01b51e3bde67b15b837096ea96ba32b4e41db2dafc"
  stringMk := h "05769905206b8a2cd9d9f82f2bb47084f6a97016efaef14cc6b3d7a14480e4a7"
  charType := h "72552513510812c5f5e12676d5a18e7c59d04aca7781fb9ad29b9f8549c2f79c"
  charMk := h "d54ba5429435d1a5fa6818757b40f6324b82241c5057abb640f8f777c5003e2d"
  charOfNat := h "c3aaf394d4d2d7a358423decfed631ec962bddda4467526d762767202113ecaf"
  stringOfList := h "05769905206b8a2cd9d9f82f2bb47084f6a97016efaef14cc6b3d7a14480e4a7"
  stringToByteArray := h "8327ea2328818c14a44230ed31802012360bc0d10d80407c7b1f0802fa264ec3"
  byteArrayEmpty := h "a2e6f9002d9c85a5b15ba4b84081c4d79d4953a4477f7eeef11c5347eb807391"
  list := h "e4c9a8e4fb921be9d9b7ad0cdaaa4195ac2d0942141f2bfbea47e804f97591ff"
  listNil := h "892f3d35a4788c60b18e722f14215603a59fad868b0b8bdad68954fc312fabfb"
  listCons := h "80c5ba913d234543c9dec70cf3f39c348b1785b976684c35bae33ac9b96234c2"
  eq := h "8283e2ba6471c8318a8637d7346b54fef85c5e7eae35df4b2d482915e02c415d"
  eqRefl := h "9733a9248863e7ca2290dd97bc544c5e6bf8d54b29c8cf955c1db7d3dce99716"
  quotType := h "30cb0558b0b4e65d26189bcd146b044f2d8078e5e8a1328728212ceb70c2b37f"
  quotCtor := h "6c5f020fa71c2dc8661042152a8387bd9b451e44e7dfd22e2184e60d008ac98b"
  quotLift := h "0b3e6c618c4b071e66e8fcacb8f79e8ac973fc7269337fe534cd97a222e564d6"
  quotInd := h "9bbd6787a148a17068d2aac13e43addeee405f0015a8e164e146a6b86168c891"
  reduceBool := h "5de91d01cb0cc7e1ef182265342bbd734b17b6c6db05078cf5cd2b8940713148"
  reduceNat := h "1e17ba5f7d9b02f6b4ff567a892bd6f4674ee0ad779ddf50faec64b2c49e80fd"
  eagerReduce := h "ff00000000000000000000000000000000000000000000000000000000000003"
  systemPlatformNumBits := h "cad987902ae218507d32365ed1d50def0532787957e8967d24c47f088504f96f"
  systemPlatformGetNumBits := h "64091b011bbf318f26bb2c84650cd9b66bdf6f03d1f7da95830e1b04eb2405c3"
  subtypeVal := h "d3e5cecbbfae503cf2be2a01b7763f0f51aa89f358be156ba0805e3cc287f81b"
  natDecLe := h "19a2fa64b6ec0fb9833405709daf397763fcd301e97126d6b94db6cc4b74486d"
  natDecEq := h "a1e1eb8c3f2d9911152170b4350acd7578fd350eba365019ba447743370c83f7"
  natDecLt := h "ca989f4ca063b20c3d7e906b1548f1113ec37639ed2af0242add396470b75bb6"
  decidableRec := h "e7012fff108d4f267d5262b8d3337a4eceee661a612c21136ba968f34a8ca8e0"
  decidableIsTrue := h "48f3948c2ff1756d8fd1dcbbfe389b4043b0ca1142810d086ba76810073e422b"
  decidableIsFalse := h "ef055b6807256b5ca9e0289aa48c37696bcb2c19e7526a7920d3d9fe4387bd62"
  natLeOfBleEqTrue := h "95c70bd18c88a4b68216db65cc9f06a5f82db8c450eed60989475e81f2537ac4"
  natNotLeOfNotBleEqTrue := h "3f1316e9d97f8e860d7c0571fa0cf9ed9cacf09f6877901c6d372a5dd5ddb5ff"
  natEqOfBeqEqTrue := h "a5db2676b189496e2576d25050e131e7d9228ba6559a14ebf8647da9c6171fa7"
  natNeOfBeqEqFalse := h "a36ca0338f1c021c54d1202b45e74d925d2bba61702bf506a89ad18554cf4fb4"
  fin := h "ba0845fbe202248f55cd6dd065a8cf619d86d5f981cbe5b805a2cc1e034f9b72"
  boolNoConfusion := h "2cf6bb040826ec937ca30af21a2fe0a00a753e6aaa3d19748150c5e093daecbb"
  int := h "600b310f606d3280d81592d87b9e1e3dbf65bb0588ab9c768ae93e42a0f1bc2b"
  intOfNat := h "02d9c1c33edb983f1762845fc835178fb0987428f103b7a661d921ca1ac83903"
  intNegSucc := h "ea5998100b288b15e8c2b86352d17a9543356bcfd01beeed067bca9ba4e421be"
  intAdd := h "2955ec5e18cf9e3b5d33a9b7b5c77fea2d1386255e29db3259b70dd915357743"
  intSub := h "2bf464cbedae2766db8b1abd8f506f9026867470bee5eb205b3d288f208a267f"
  intMul := h "d8fd892631ba66726eb869c6c209cfa2cce79bbdc90cd2cb787a23106f71c7d2"
  intNeg := h "dff2ef576cadddcbabaf9901afaec633a8d9339adbfb995dc83649261100de31"
  intEmod := h "409dec138fe3909a91bbc6ddead1acce7fb1456d68218bec16d4b45b1baaec8a"
  intEdiv := h "c5e6f3e89b81ad150dd38ee8d2b9dbdeb71b97dba147cdd73e512a127d56fc4d"
  intBmod := h "abc16a0d33db31ef490e4e6375c60a86f70bae454cd2f3357138e735aa79741b"
  intBdiv := h "b99e130816aa7474c6606434d7893a0adb6529a68c0926e8ef9d8b68a5f7e11d"
  intNatAbs := h "61ca2ac86bf2ba5265c5ce0332157fb12259d2e8fb1c449e56c98dc77534ce1b"
  intPow := h "f84c33759cab12aa5502c141a700fc2345aae38ca8ee3bdbf5d45ddf9b6a1863"
  intDecEq := h "b3f26f97f5a8bf58b0b872bb86dca4366ee843c7c5e66e9246d546aa68978884"
  intDecLe := h "9d5081f5cd648e4011f5432b4731ca908aeee30f631833230fccf53ae8ee004a"
  intDecLt := h "a65d4c6d2901d6882ec994381e4d9bae23ebf44e439a3e0d8bf4a9f195ebcf9f"
  punit := h "1f24b345045e83033dc57342cdd3bd2842d1c3a2c04b193c409873becb75b414"
  pprod := h "0d2ce4c74d60afaff1374a1815386d85c5f2c8fffc022d68647321cc022483ca"
  pprodMk := h "5aa42169584200055600bde3b8299edba45a17a1659f371f7cbb53f1c6392598"
  natRec := h "3dc32a7921881e8d7e882cc407c88a29ab9eb6886d4c8d06737f5fa5eb364d9d"
  natCasesOn := h "05bbf91cc5f5857dcf31889f1757af2f38d9aa19a400bcc1ce063703d06f44ca"
  bitVec := h "4035f2f9376c166678e218090d8ad310c831956e2dd1509a7721c0c8b9485087"
  bitVecToNat := h "09681380c93b474123dfe8a344481297dff500d266a28b0d3e456f8170cd3de6"
  bitVecOfNat := h "f1cdd30b88094caf70371245abf5ff3f1acf5fded196f4155fa536e126a7df6d"
  bitVecUlt := h "43bee1d933c3e28ee41e17cccbf567e989ea45d835c7631be05a46ea8189494e"
  decidableDecide := h "d1a0f891ac4b85cdff478113bbd5ca0029d9f121cb4e0c3bc26d1a2a494cf68b"
  ltLt := h "34ee35af6409123b16f55c67cd65d4f48f525a3139545d04b61d8b2fd7941550"
  ofNatOfNat := h "72c6287074ab54b933bebf28c45f50f4b3f411a8fc9be1cf989f7a85565def09"
  unit := h "585e362473d1a5811630ce9ce11b21868b6053a1419e7e3e637d8fb8fb0f9fce"
  punitSizeOf1 := h "6a8b99388c4191b1652053eee475777a791655d0f42df5ff8c09f02062f2f56f"
  sizeOfSizeOf := h "0e87647301ea0cb27db9f3218c25a713fa713dcf71b42478a9bd7430d303ae3b"
  stringBack := h "1ae98f7e1d03a491f11bbe3b963af97245afa08ff818a26c9cd6f8cc342187e7"
  stringUtf8ByteSize := h "88091d363f2573e373d9a0bb0583eee794a444bf5349a0822945523477065104"
  stringAppend := h "e79d3e9179930b799fdc73995ebb4d3cb54121eedc904366bdcf500e261d77e2"
  stringDecEq := h "0803fbe1abc2e1d180631c22ad7e29a832d2b871584b53ccd98a6092e4b2b4e0"

/-- Addresses reserved for kernel-only reduction markers. These are not Lean
    constants and must never be accepted as user environment entries. -/
def reservedMarkerAddrs : Array (String × Address) :=
  #[("eager_reduce", canonical.eagerReduce)]

/-- `(lean_name, canonical_address_hex)` pairs in the same order as Rust's
    `PrimAddrs::lean_parity_table()` / the `kernelPrimitives` list. Used by
    the parity test against `rs_prim_addrs_canonical`. -/
def leanParityTable : Array (String × Address) :=
  let p := canonical
  #[
    ("Nat", p.nat),
    ("Nat.zero", p.natZero),
    ("Nat.succ", p.natSucc),
    ("Nat.add", p.natAdd),
    ("Nat.pred", p.natPred),
    ("Nat.sub", p.natSub),
    ("Nat.mul", p.natMul),
    ("Nat.pow", p.natPow),
    ("Nat.gcd", p.natGcd),
    ("Nat.mod", p.natMod),
    ("Nat.div", p.natDiv),
    ("Nat.bitwise", p.natBitwise),
    ("Nat.beq", p.natBeq),
    ("Nat.ble", p.natBle),
    ("Nat.land", p.natLand),
    ("Nat.lor", p.natLor),
    ("Nat.xor", p.natXor),
    ("Nat.shiftLeft", p.natShiftLeft),
    ("Nat.shiftRight", p.natShiftRight),
    ("Bool", p.boolType),
    ("Bool.true", p.boolTrue),
    ("Bool.false", p.boolFalse),
    ("String", p.string),
    ("String.mk", p.stringMk),
    ("Char", p.charType),
    ("Char.mk", p.charMk),
    ("Char.ofNat", p.charOfNat),
    ("String.ofList", p.stringOfList),
    ("List", p.list),
    ("List.nil", p.listNil),
    ("List.cons", p.listCons),
    ("Eq", p.eq),
    ("Eq.refl", p.eqRefl),
    ("Quot", p.quotType),
    ("Quot.mk", p.quotCtor),
    ("Quot.lift", p.quotLift),
    ("Quot.ind", p.quotInd),
    ("Lean.reduceBool", p.reduceBool),
    ("Lean.reduceNat", p.reduceNat),
    ("eagerReduce", p.eagerReduce),
    ("System.Platform.numBits", p.systemPlatformNumBits),
    ("System.Platform.getNumBits", p.systemPlatformGetNumBits),
    ("Subtype.val", p.subtypeVal),
    ("String.toByteArray", p.stringToByteArray),
    ("ByteArray.empty", p.byteArrayEmpty),
    ("Nat.decLe", p.natDecLe),
    ("Nat.decEq", p.natDecEq),
    ("Nat.decLt", p.natDecLt),
    ("Decidable.rec", p.decidableRec),
    ("Decidable.isTrue", p.decidableIsTrue),
    ("Decidable.isFalse", p.decidableIsFalse),
    ("Nat.le_of_ble_eq_true", p.natLeOfBleEqTrue),
    ("Nat.not_le_of_not_ble_eq_true", p.natNotLeOfNotBleEqTrue),
    ("Nat.eq_of_beq_eq_true", p.natEqOfBeqEqTrue),
    ("Nat.ne_of_beq_eq_false", p.natNeOfBeqEqFalse),
    ("Fin", p.fin),
    ("Bool.noConfusion", p.boolNoConfusion),
    ("Int", p.int),
    ("Int.ofNat", p.intOfNat),
    ("Int.negSucc", p.intNegSucc),
    ("Int.add", p.intAdd),
    ("Int.sub", p.intSub),
    ("Int.mul", p.intMul),
    ("Int.neg", p.intNeg),
    ("Int.emod", p.intEmod),
    ("Int.ediv", p.intEdiv),
    ("Int.bmod", p.intBmod),
    ("Int.bdiv", p.intBdiv),
    ("Int.natAbs", p.intNatAbs),
    ("Int.pow", p.intPow),
    ("Int.decEq", p.intDecEq),
    ("Int.decLe", p.intDecLe),
    ("Int.decLt", p.intDecLt),
    ("PUnit", p.punit),
    ("PProd", p.pprod),
    ("PProd.mk", p.pprodMk),
    ("Nat.rec", p.natRec),
    ("Nat.casesOn", p.natCasesOn),
    ("BitVec", p.bitVec),
    ("BitVec.toNat", p.bitVecToNat),
    ("BitVec.ofNat", p.bitVecOfNat),
    ("BitVec.ult", p.bitVecUlt),
    ("Decidable.decide", p.decidableDecide),
    ("LT.lt", p.ltLt),
    ("OfNat.ofNat", p.ofNatOfNat),
    ("Unit", p.unit),
    ("PUnit._sizeOf_1", p.punitSizeOf1),
    ("SizeOf.sizeOf", p.sizeOfSizeOf),
    ("String.back", p.stringBack),
    ("String.utf8ByteSize", p.stringUtf8ByteSize),
    ("String.append", p.stringAppend),
    ("String.decEq", p.stringDecEq)
  ]

end PrimAddrs

/-- If `addr` is a reserved kernel marker, its diagnostic name. -/
def reservedMarkerName (addr : Address) : Option String :=
  PrimAddrs.reservedMarkerAddrs.findSome? fun (name, marker) =>
    if marker == addr then some name else none

/-- Membership set over every hardcoded primitive and reserved-marker
    address (built once at module init from `leanParityTable` +
    `reservedMarkerAddrs`).

    The IxVM claim harness (`IxVM.ClaimHarness.closureFrom` and its
    siblings) seeds a claim's byte scope with the members an environment
    carries: the kernel can reference them without any `Constant.refs`
    naming them. Membership grants no semantics: every constant a native
    rule recognizes or builds is a role, read through the claim's role
    binding and validated against its specification. -/
def primAddrSet : Std.HashSet Address := Id.run do
  let mut s : Std.HashSet Address :=
    Std.HashSet.emptyWithCapacity (PrimAddrs.leanParityTable.size + 4)
  for (_, a) in PrimAddrs.leanParityTable do
    s := s.insert a
  for (_, a) in PrimAddrs.reservedMarkerAddrs do
    s := s.insert a
  return s

end Ix

end
end
