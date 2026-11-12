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
  nat := h "ee5d424f6fbb5410ce82a4657c586ed8dc57eb2588947578636676e42ed0072b"
  natZero := h "09851a0422a18822447d9785123b46be1d53f1a2d0137992fe16ae693cb3f07d"
  natSucc := h "757ca9ddbbfdfcb939a42c164c435dede6d6d234279f89e1d13668f3ef4d891d"
  natAdd := h "a04e7e6b19f5e48dbb0b53dae24db5dcc1b1a98c8e97551db8fb4b5f4a14caa8"
  natPred := h "b8d8ab1875dbb7fdb150a34988c32d7006204b9506a0ba148f453e5c555bf218"
  natSub := h "f8410bb7b91afaa0cb6f9162faeee2a682e98cde21acf19712380f4e9dbcbf00"
  natMul := h "7e736639472dcc920bdc54d8ff0255a4c03b3c05375eacf08814e341deebd331"
  natPow := h "473d7239744c820ddb45b6ce56d0506734ba90e5699e985444fd7a6647e9b0a0"
  natGcd := h "f1286e3ceac7bf4afa1c95a2f70c69ffc0667295035661b9be57ed6f0b08babb"
  natMod := h "fdc3d6f24a0d4968b0e2bd5502a95a54506566a6d6f8bf5673b95b5278da8cdd"
  natDiv := h "2f22b34c61096990d6ce6b2485b31ed9696feaae6902855de6116b6a58e90331"
  natBitwise := h "f67972af52c7a4fce7de2595075e6b6d0ca7d7f67e01e1a1383c6a270aa613cd"
  natBeq := h "dd0668fbe8c2b2a2260e95da62a2bea5df42c670a3e95ccffea03c3a7ffdc1c2"
  natBle := h "a939cc7925834d04a7ced860c5c44484231c9f5c44728d83d55f19c08037f3b4"
  natLand := h "a4f25748d7376a55ce31462ae4ad90ac33181a6000b9908f398cc850ad865f67"
  natLor := h "0330cfdb86165b40463f2931bf794d375aa7acecd21feaabe1319e03fd80a5d9"
  natXor := h "7c79bfc28b46cca9137779a26b8da0b4aedc718eaf554f76e6e38650074327d6"
  natShiftLeft := h "c2a2258d56e14ebdb8c9986365cf0c0f6dfe4128a8faf847dd5e50b4ae7bb310"
  natShiftRight := h "74a4836a0eddfd07e45e5da0929df974e0caef28fd26001f7de1712d5beddd4e"
  boolType := h "77db82d7052a606eaaf324893161d6989049ef4e0f393e2fe9edaf52f4225ed8"
  boolTrue := h "ef156463a527bfd236472e606b2ccddf73f4585195e365e0430ee3c20921d8cc"
  boolFalse := h "a5fc856de635cfc40ab703eea51cb704dce6985fd7de921f94b8d635e9d3667f"
  string := h "9964f625c7e537f667af5c445f1c1cd4ea18d6094dd7b7083c49f59613566306"
  stringMk := h "37f3bf73d4ef5dfa4705a3125b788141b980a48e7303e1f23e2465acca2e19d6"
  charType := h "f730fc437187a5bf297d6f68f125ab93a4f15da80eecf8379cef2a5ce3e9b015"
  charMk := h "85f033fda46ae0e305e02bcc83c9f76b04bffb005536a5bc7a15107d57a9c4b6"
  charOfNat := h "6b8d46124c1396c972f51482fe4f6afcf76bf50da76c9772be03a19ebf3564ac"
  stringOfList := h "37f3bf73d4ef5dfa4705a3125b788141b980a48e7303e1f23e2465acca2e19d6"
  stringToByteArray := h "6fabcaf163e83cf02d51624cade44120c65b6e5dc439578fe68eb1972870d1dc"
  byteArrayEmpty := h "e2872f038c01610a4f78126ca7abe6573a57f717edf7b990ce01e3d32f60b991"
  list := h "487a90b33c7dcd5f3434aa04338e1a5b290552cbe922eeb59b025b1dcdbf5de0"
  listNil := h "acc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a9711786818fa"
  listCons := h "63cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bfca4fd0073e01ab"
  eq := h "9d3c7bcfcc8f1f1661bce87d371a5da0d5188c1bc05def21d4aa176138c91b10"
  eqRefl := h "54b03dedcfd0b6910e04eb06e402ee285adacfcf388b2cf924abe3b208e07b48"
  quotType := h "c87b29931ce4e002425f8566d1cbf012cb95383f7e7cc3533f5763d63b3f2060"
  quotCtor := h "b38e6ec63d3ac6caa456af698ffaf866e192bd3e84d8092a8415b793a7abb598"
  quotLift := h "abbb9c07b2c466ed630087842844ea0464b95ca0218b2a1ee67907542d443084"
  quotInd := h "2c05f283a450a057bb67a0b44225f478c2d00fbbfd9728b4f8cef6c0f3553cfd"
  reduceBool := h "6f934549cecd15776349147cb2d7b2161caae5ea2af0e5f773bf6e96a34501dd"
  reduceNat := h "9ff7e16f724d7aee1243b6b670cd19c13e153d7a7472789a9b5a6d68224963ab"
  eagerReduce := h "ff00000000000000000000000000000000000000000000000000000000000003"
  systemPlatformNumBits := h "7984aff2c623559abf205435ff3a193e4e8a1339c4d2db4f7fc4301840f121b4"
  systemPlatformGetNumBits := h "e8b0ce9336fdebfe436dc9ef0bf8141a137dce0533ef15d544295567fcae2054"
  subtypeVal := h "8289d019f214f560cfe57247da921a2cdfab41172cf3b56376c3a06e5edff08d"
  natDecLe := h "50f5ae564c67023119e61cd8a1510970065582bdfedc7770bf88cc2f047ef079"
  natDecEq := h "cff050af9ca1951b0c4c4dd7280da5837e5390bcd6249f8e45c6b997fb63be34"
  natDecLt := h "dd7ee8e548a8aa482caf21c99c2f5c10254700d2ad3784530e740dd9f61a8cd3"
  decidableRec := h "6be931292c410641a78101e973c604b94da29b6ee09ea00a557968fb2efe252e"
  decidableIsTrue := h "23e3b904854e2f117770ac908a90ef0bdd50bf2ed11a6274b8c233db4cdb866f"
  decidableIsFalse := h "f1fe3bef188e3a340b3ba29ae5ecdd265c970439e3993b5b3fb3bf8d85342663"
  natLeOfBleEqTrue := h "9648c8fade1402c8b4e05e7280d56ffdb6485a5b12c053eb409ddb2abe64d49e"
  natNotLeOfNotBleEqTrue := h "47be72026cd031236a38d19bf7891e17e6b72b57347221a9f31d2500374bb1ce"
  natEqOfBeqEqTrue := h "d464a3b9c60c79f1c15c42ba3ecd64f2aa9db4dc466dbeff9c2f7f8c6fe2f809"
  natNeOfBeqEqFalse := h "680e71feb2d9ffab6d006358e66264c3898792eac445696061cdcd78e8e65c1e"
  fin := h "638ff947a118e46c15195a4c6fb4dbe00f69beddefe9ba80e64fc31fe7de140f"
  boolNoConfusion := h "1173d7b6f2bd5f453467d131f67d29e1f1f5a43a61262e1e8036bdb9e1ab640d"
  int := h "35597c7bd15920710c3e00596c6e31ee24a496beb5f61efaeb356dd9e4b2d9f4"
  intOfNat := h "7f2fc3d5811ae7540af7cd6943abed4e822e4939f8d73bc4cda4985ba2653503"
  intNegSucc := h "1c49eff96dc8bbc4d9d0f3faa21b3d90a67fe7ba5e0d6d5abcdef0013a683825"
  intAdd := h "514e4a1d06a0a11bc0de8e7723e56cf92402ea91914970c71666a2723d0a8948"
  intSub := h "5c0921619ad0e89e59589e4ee62da332382217da03df9978d81dc713724edc02"
  intMul := h "88f54e211e3d65e4e64ba847a24db743109268f1459724b3d50b8dbacfa2ac4d"
  intNeg := h "93670808b6171d82d973d9e607cb056474a384ce0d3c10b87f3925d05436629f"
  intEmod := h "5234a2d2ce00bf4e1df19ad5ffe55daac0424c7c74e5d1a2b740efd43d612b8e"
  intEdiv := h "de44c29f84913a451ef5a3526db1000cbc87c8ed4d4417f646e0d841c59306b3"
  intBmod := h "26a7af17d6b4bd04d7d0a6280ed682982ac5e12d75280c83c9ebdb4f7cff64c9"
  intBdiv := h "953f3109bcbf54692990572bce05ff9f2ffb03438882b9d47fa01d914a3db52c"
  intNatAbs := h "9dff1da5f30f3cca942bbfce551d8e0a4d1f13d946ea1ef44c478ea3257551c1"
  intPow := h "1cddad5e261c1786036f900b15ce94de7cdec55dc741062e0de8b2192613bc04"
  intDecEq := h "ad376bc32d8789ae58304b84cde55511f1b7cdca85cba9d593b87031d651fb5a"
  intDecLe := h "4da67faa95070121d3310db52aeadfffddbf4ce2dd8902398603e536d16c8d14"
  intDecLt := h "976882e78acc2475953e59c23415750f1ec40f13d8a5dfc453385dfc18346ff1"
  punit := h "1f24b345045e83033dc57342cdd3bd2842d1c3a2c04b193c409873becb75b414"
  pprod := h "02944ab961161c59fe9f4bf62fd114344a79229f604aeb649440c53a9cfc3de9"
  pprodMk := h "0980754525afb7a32e274bef06865a7b03bab07b8343ca334e16ab8049baa6ff"
  natRec := h "a37d28a22a02cd33b3c87380f45c8990c95cce53f154ad332a9cb5f9b1638753"
  natCasesOn := h "4c2eb46bd344dd88dd451538be890ecc4734373b8aeaf13b671c970570949109"
  bitVec := h "805395dc5aee5c43d794dc1fdf6015886d19c78d4ecc57c51685456c1685cce6"
  bitVecToNat := h "2e42823b21abae43f4c0624983662038e4ef9c01e8eeb6d39ec5253b24b2b8db"
  bitVecOfNat := h "0d0e2c6e31c12bcba061871f4eeef439d95aa536771931e7fdbf6036d0c88f7a"
  bitVecUlt := h "c5bd60dbef7e03d7afcb4ea1436b3f7b283262e2e025449ad8b0d5828b47dfba"
  decidableDecide := h "702607152432fb22bd2a59d80423b9f7a369a55acc6a4c16d3654523a5788d16"
  ltLt := h "0eeab75a4c4d71e2f7f745ab54fd64a9ce45e9f506ef09f3312711c4619fd178"
  ofNatOfNat := h "8c074cca466bf7a3a5ec2b1f0c11886da5d003837d3b29ca4973b89ab01e0382"
  unit := h "585e362473d1a5811630ce9ce11b21868b6053a1419e7e3e637d8fb8fb0f9fce"
  punitSizeOf1 := h "2f546e3974f2ab35d4cb8e2a452b0c7fc24f6e515cec781744ee78d52fd0fdf0"
  sizeOfSizeOf := h "7c51fbcfd57ae985f7f6845874da7c171aa7edceef4daee875eb53899d4685cd"
  stringBack := h "1d9ed0da7f32dd9e16399c57b5cf7f3120928f127803e45835f1d58c6fc3e3b2"
  stringUtf8ByteSize := h "e47a3627ce6d979fee7b68a3aa86abf2b2b67b8eb24d4d984f10e284c2384d7a"
  stringAppend := h "606e3f9fd1b1cb9484145af8ee112dcf66fa3203f1ff11322ebd1f4f63403a3e"
  stringDecEq := h "f799ab07a9dc29e3c2d7492e21262e4f38752fd6b00c6813fb14039748e6185e"

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
