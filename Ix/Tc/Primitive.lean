module

public import Ix.Tc.Env

/-!
Mirror: crates/kernel/src/primitive.rs

Well-known primitive constant KIds. Content addresses are hardcoded Blake3
hashes matching `PrimAddrs::new()` in Rust (regenerate with
`lake test -- --ignored rust-kernel-build-primitives` and paste into both).

`Primitives m` stores `KId m` values resolved from the environment by address
so meta-mode names match; in anon mode resolution is trivial (names are
`Unit`). `Lean.reduceBool`/`Lean.reduceNat` are real constants dispatched by
content address. `eagerReduce` is a synthetic kernel-only marker: Lean's
`eagerReduce` compiles to the same canonical content address as `id`, so
address-only dispatch on the real constant would be unsound.

The `pprod`/`pprodMk` addresses exist only on `PrimAddrs` (used directly by
nested-inductive recursor generation), mirroring Rust.
-/

public section
@[expose] section

namespace Ix.Tc

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
  stringLegacyBack : Address
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
  nat := h "398a7706cf13f223992d173dce07946857240f49afcc743723e839f8f3f2b631"
  natZero := h "d397370157fb9ae2c6e1eda79feb10bf497401741aba788fab726cfa4c467db6"
  natSucc := h "def52d1dad5f10cf9893c945e169718d62b15e2dd2c9066e597b9d4570ba056e"
  natAdd := h "e1ee4c78a3906464fa8c17ec2ed0c0bf66db3b412d9b1c5f31fba7bb974a93e5"
  natPred := h "914f9c01884853652e9224dc511f867d5408517f3beb3192fc4477e0e9594c88"
  natSub := h "bf058ee446527af6ec749223752d07e6d7c2df8dc0a0778d934f885ae8267d57"
  natMul := h "c2fe5eda1e559236bfc2a7a47db0ca6cf782f7b69bdd963237d0889fbf9a4b07"
  natPow := h "0aec92313e598d5fcb5dcf0b80399c69ebf6a43b9ee97a3e561436b9f2b95480"
  natGcd := h "59e47d71d73c544ee1a4edf07e9ffff542cb757e739651a9cd453af03d3dce42"
  natMod := h "2c9d2d3e7e974b43ca3d212f32707187382125b1272758f69c4b47e96d9aabcf"
  natDiv := h "2f12f32294b7d1168ada1809c9b8b2563824e9c2879bf8d3bb9b5c03d7ab7131"
  natBitwise := h "e2a8fae8bf498a31582ac0f816e7902ad7c484ab5cfee0db53776bd24ffc994e"
  natBeq := h "ca3022a3c8359b0c435eb4bb8e8eac0aa085d1da10f259287025229861112070"
  natBle := h "ca4b398b2080beccccf3a3121e848bd1977847668c18a6447b0edc5f561b1cbc"
  natLand := h "833c5b2e3c077eb6b3c0e4d848cf5408240c7d3cff8c40635c6e3bf946630e34"
  natLor := h "7232095aea9a5f79cc0f2b0ad848dbf1904a630f1ef86f244f8a42b847afab9a"
  natXor := h "c3b00b514b9f26dc1edf10c7d6f69f455ef8ed0c51b0a666e3427fb44d3a04f0"
  natShiftLeft := h "6e70cd9d1708b8f00be460655ca47a419dc601f9c0558e7ac212b80ee6ff0978"
  natShiftRight := h "d8ddec67d32eeb1f2b0d540372ed745220fdb1e4e2b2f54badde60b66734f9f3"
  boolType := h "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4"
  boolTrue := h "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762"
  boolFalse := h "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e"
  string := h "fd53e8dce82d568b56e9b16c390b5693c137b4e54d12ac09aa559863954b6587"
  stringMk := h "0f0250d7713704439073babd511b77a9eeeae5adbd50ff574d801ffb558128d9"
  charType := h "203b76c5b4f5ca061563314057a943bc4380885e73d0efaf14644598c2fa6eee"
  charMk := h "ef840f0ed608f9fb81cfe0c67bb5a09334a8e77cc087288062e13595a6f65883"
  charOfNat := h "09eeb416c84076666457417f4b7ce3d1bf34977d3f56dd2562c0014a51cb8d34"
  stringOfList := h "0f0250d7713704439073babd511b77a9eeeae5adbd50ff574d801ffb558128d9"
  stringToByteArray := h "8709f570a8193252182a9ecd713f890e75d3bfb5a27f5b9181ccabe0654a0c29"
  byteArrayEmpty := h "0d2363d6035cc7c0331fff5ca1de7b4091251b504d44eeb2850993bd0ddde222"
  list := h "144e207a88d1dfbde22a1b40689033b3a65a652c8f7500b9be3cb7f66366e0fe"
  listNil := h "258a7364b87c99fe9f83e05e0d05c935609a0dc5df8d77939130efe5e0efca3e"
  listCons := h "77d519259ec9fa489dbe0e3dc0b9352aef349ccdaa73ea58b08bb0bc683502a0"
  eq := h "036b63d5cc0961e920dee50e7364ec0dd3f9c38a9cace40e513b3835dec8e0c9"
  eqRefl := h "6c9bd60e1eae938e5626ca237dbca7fd950f2e99e234a99c23cfdc294ca7adce"
  quotType := h "ab682c1778a17bbeae4032974df36447ce8bfcab6764a36d378566e3ad63cab8"
  quotCtor := h "88266677fee774d109867e4b2240281aa2ee12d97920c1171cf5c1f6c87decf6"
  quotLift := h "8dc4a97527812f8b7817b77cd079ace61450aa0185ac5885661ec2acba8b7bd0"
  quotInd := h "124984bcb95208a0f30bb69d6736d3d59404e115e2202043fda3d34e01b0ad16"
  reduceBool := h "1c170098e23143fd8fd6172cefd2ecee305072d2991113cfc4d52840a5a9fa78"
  reduceNat := h "16853076b0d96d356d85485c56f3398014b6a0f2ee72ab16284a381d9c28e560"
  eagerReduce := h "ff00000000000000000000000000000000000000000000000000000000000003"
  systemPlatformNumBits := h "a91624445393a674fa0f9e9f9a52f41b93b10487018046cbc1265a2455bcfaec"
  systemPlatformGetNumBits := h "66f29be6e00ac835638a2814988f9cf16547bebb0763527c119bca51d7b0bdd5"
  subtypeVal := h "0c7072a927b1c46efc9498e749b8320b74d8994ec280601628bfaee1ade36c71"
  natDecLe := h "4560c5f121a542f2c233626f4ef6fdd8f36ebe97c948adeaee283d9ed4572fdb"
  natDecEq := h "a3f5a80d1a8cc990639d06be98bcc2b240f793a4adba9b002712b804a6fe3376"
  natDecLt := h "2ea36539ac1a8e0022a90d8b70ddb6f4db46b0ce19efe4e1c44792feed9d7e8f"
  decidableRec := h "ab3776985743af13a9cb1a7d2f8496997892e17983d14be5270a716570b35719"
  decidableIsTrue := h "0f9ee8d9033d8f7b852f5b7152fd124f7d411930c992e0f457f8104b60a98381"
  decidableIsFalse := h "0471e47158b2ae18d3c08dd5c77aae23e62d7bbc1e61116bc2813b1306bc5795"
  natLeOfBleEqTrue := h "042a9ad1489e769fd295d58cb64a7405e86f7881b5e7c22d77df486915d58eb3"
  natNotLeOfNotBleEqTrue := h "7dafaa151ed90b0ab27f0279b9383ab8abe8602c6635ca191f28cbb7aba6afdd"
  natEqOfBeqEqTrue := h "f8313971bba5ee8c814554b0c0447a10c129b41945ac5fb817c3fc7b98b23a10"
  natNeOfBeqEqFalse := h "7aecc206714d64b5177acb753a285e670a918a1ac9fe8f57460f776f17b7adc2"
  fin := h "745936fcb9d86c4457f0fd1e537e67077f46f7841108419dac7984008b565b97"
  boolNoConfusion := h "cd983a826c1e20c4570afca244916c79e20e816f618ffdda38be8a79079274ce"
  int := h "a5ca2e1d5ceb8d43367bc34d69a50c1650a25dc10780aa0c378cdfa931ff0424"
  intOfNat := h "09bc253147c36ce22c8e0ccd43c79b2cdae2206e0ddd168fca3609b2a584d3dc"
  intNegSucc := h "267c0a9c92e75638fc73ed52a9f9c81647eeeceeff2144c1f97e65e2aff149f1"
  intAdd := h "b6bbac00c8e46f8b8640298f4c9ac894cbcd0101035edd543f7c434e2c9fe926"
  intSub := h "bcb09ba43f8bdae65c56a47ff77b50b42ede120fbcdba8469e799a21f12fd389"
  intMul := h "74ed1fb9a9bf99d0b02dbefe042464cd715301859a70337a99344be762dcbe10"
  intNeg := h "f61c7d3fce595430f86f0cd52da5bcb00bf910edd85e14dc0402130fcce34ebd"
  intEmod := h "ac9c72319551f5637f7c51c70be6da8fd66a81837c9eb50c3fd50ecf8cbbc070"
  intEdiv := h "9f2ca4e3de3a794f67db64849dd577c066e56142206fa6bc724e4b8db6f20f5b"
  intBmod := h "197d3c7e9ce0949c52ef98f50b58ddb942db6d367640d6fb6f49ab91f82f4271"
  intBdiv := h "0713405a689d2155a84123a0f6395c31c6fa55c1ad905fc55663acf7d7577f57"
  intNatAbs := h "83e3ce8a747520cc248a0dacf9bd1369467e4907e8aaaa433e1b438e1cad7ca4"
  intPow := h "875be8d8ae5f332003ec2bade698bb0aa5f2f46e71218da9cdd9d09506e84c10"
  intDecEq := h "0f53bc5768fd32aa6801dc8762934b69049db3e7e57412c6904dd1a8b9cff4f8"
  intDecLe := h "0e5f70efda0598182819a10a238796462debc05f40888117d1196992b9423fae"
  intDecLt := h "ce137cce4c1a49323a788f1677a9d6a1d4a936111588083589baab2bac01108c"
  punit := h "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b"
  pprod := h "c1c9c9a4f2b52a87f6be51476de8fe93d3ed8e7fd5652d5a11617e3255190da5"
  pprodMk := h "59f659338954244d5574ab1a951c11d7e3a6efe2964a466d460450809732dfb2"
  natRec := h "b975152f3f0cd9039433c68f5a5e5455f5cb5d917078baed0118b59067a74ea7"
  natCasesOn := h "1917841d2085796dd7ba346de93a579571b5641c33fc400408ec55b5778a9a51"
  bitVec := h "67f474b8c3302b04417f721ff3e88ce6f16a7dfcb3bae99368085d1c5e872ba4"
  bitVecToNat := h "e32ab4e7720d3442a266b37c97a27218e68239318311f8e4b046a6bdde520374"
  bitVecOfNat := h "3b334c94dd56d80beb4eff5d825f67f6f1ac4e140403699e3daff52a00bdbf6e"
  bitVecUlt := h "4f9d4e0c70e16c78e0eda38e2d6d94ccd12598755e0e7200a9239da92b9057cc"
  decidableDecide := h "c5f7b19663e4499e70e1b2645162c5be15fa860f4f8157e331ae546c6f733723"
  ltLt := h "cacaea97f4cdba0a4a0af71005d0517d1818ab2623bd2ea7fa8c637a0e3d3312"
  ofNatOfNat := h "5a7292ad756ee1f2df4b92f18a27574a47cbbcf7094f98ab2865f92eb22342d7"
  unit := h "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb"
  punitSizeOf1 := h "7bd8e19f47f6eae620a5c39f243ce415dd6a77f09590f4c227cef363007f4012"
  sizeOfSizeOf := h "a343a651bff408c3a29ff27b2b62e34b54b2ab381cf6f3ad87c540c977dc3c4a"
  stringBack := h "548bbf22ba305f8e363edf9907d0c2c454add416ddbf25b38c76d0063ad21d65"
  stringLegacyBack := h "ef4e74e44e3bb9fa5e5488a46c5b4d61fbfd701e3679c5bfb4154c8747cefdc9"
  stringUtf8ByteSize := h "5186d91ef8892e48eb02918b0926e9767c6d4b9b0814064a449a5afe8a9e5a6e"
  stringAppend := h "ff459554dfdc34d159027038174571b770464d52834c1dbc6436467fa81d039e"
  stringDecEq := h "14cf519b05c30384fd4cb2e271b0896fe23e74c995010d42eb1ffce14927e56b"

/-- The synthetic kernel-only marker address used by the *original*
    (LEON-addressed) environment's `PrimAddrs::new_orig()`. Only the marker is
    ported — the full orig table belongs to the Lean→kernel ingress half,
    which is out of scope. -/
def origEagerReduce : Address :=
  h "ff00000000000000000000000000000000000000000000000000000000000013"

/-- Addresses reserved for kernel-only reduction markers. These are not Lean
    constants and must never be accepted as user environment entries. -/
def reservedMarkerAddrs : Array (String × Address) :=
  #[("eager_reduce", canonical.eagerReduce),
    ("orig.eager_reduce", origEagerReduce)]

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
    ("String.Legacy.back", p.stringLegacyBack),
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

    Soundness note: the kernel substitutes native/GMP semantics for the
    declarations at these addresses (`tryReduceNat*`/`tryReduceDecidable`/
    …), so its verdicts are sound only if address = content holds exactly
    here — which the blake3 integrity check at materialization
    establishes. Ingress therefore verifies prim-addressed constants
    UNCONDITIONALLY, even under `--no-verify` (`getConstVerified`): for
    every other constant, skipping verification merely risks checking a
    mislabeled-but-still-checked declaration; a mislabeled primitive
    would be silently trusted with the wrong semantics. The Rust mirror
    has no analogous hole — its integrity check is unconditional at
    deserialize (`crates/ixon/src/serialize.rs` `Env::get`/`get_anon`,
    plus the anon merkle-root check). -/
def primAddrSet : Std.HashSet Address := Id.run do
  let mut s : Std.HashSet Address :=
    Std.HashSet.emptyWithCapacity (PrimAddrs.leanParityTable.size + 4)
  for (_, a) in PrimAddrs.leanParityTable do
    s := s.insert a
  for (_, a) in PrimAddrs.reservedMarkerAddrs do
    s := s.insert a
  return s

/-- Well-known primitive KIds (mode-resolved). -/
structure Primitives (m : Mode) where
  nat : KId m
  natZero : KId m
  natSucc : KId m
  natAdd : KId m
  natPred : KId m
  natSub : KId m
  natMul : KId m
  natPow : KId m
  natGcd : KId m
  natMod : KId m
  natDiv : KId m
  natBitwise : KId m
  natBeq : KId m
  natBle : KId m
  natLand : KId m
  natLor : KId m
  natXor : KId m
  natShiftLeft : KId m
  natShiftRight : KId m
  boolType : KId m
  boolTrue : KId m
  boolFalse : KId m
  string : KId m
  stringMk : KId m
  charType : KId m
  charMk : KId m
  charOfNat : KId m
  stringOfList : KId m
  stringToByteArray : KId m
  byteArrayEmpty : KId m
  list : KId m
  listNil : KId m
  listCons : KId m
  eq : KId m
  eqRefl : KId m
  quotType : KId m
  quotCtor : KId m
  quotLift : KId m
  quotInd : KId m
  reduceBool : KId m
  reduceNat : KId m
  eagerReduce : KId m
  systemPlatformNumBits : KId m
  systemPlatformGetNumBits : KId m
  subtypeVal : KId m
  natDecLe : KId m
  natDecEq : KId m
  natDecLt : KId m
  decidableRec : KId m
  decidableIsTrue : KId m
  decidableIsFalse : KId m
  natLeOfBleEqTrue : KId m
  natNotLeOfNotBleEqTrue : KId m
  natEqOfBeqEqTrue : KId m
  natNeOfBeqEqFalse : KId m
  fin : KId m
  boolNoConfusion : KId m
  int : KId m
  intOfNat : KId m
  intNegSucc : KId m
  intAdd : KId m
  intSub : KId m
  intMul : KId m
  intNeg : KId m
  intEmod : KId m
  intEdiv : KId m
  intBmod : KId m
  intBdiv : KId m
  intNatAbs : KId m
  intPow : KId m
  intDecEq : KId m
  intDecLe : KId m
  intDecLt : KId m
  punit : KId m
  natRec : KId m
  natCasesOn : KId m
  bitVec : KId m
  bitVecToNat : KId m
  bitVecOfNat : KId m
  bitVecUlt : KId m
  decidableDecide : KId m
  ltLt : KId m
  ofNatOfNat : KId m
  unit : KId m
  punitSizeOf1 : KId m
  sizeOfSizeOf : KId m
  stringBack : KId m
  stringLegacyBack : KId m
  stringUtf8ByteSize : KId m
  stringAppend : KId m
  stringDecEq : KId m

namespace Primitives

/-- Core resolution parameterized on the address table and a resolver.
    Unresolved addresses fall back to a synthetic `@<hex8>` display name
    (expected for the `eagerReduce` marker; hash drift otherwise). -/
def ofResolve (a : PrimAddrs) (resolve : Address → Option (KId m)) :
    Primitives m :=
  let r (addr : Address) : KId m :=
    match resolve addr with
    | some id => id
    | none =>
      let name := Mode.fieldWith (m := m) fun _ =>
        Ix.Name.mkStr .mkAnon s!"@{(toString addr).take 8 |>.toString}"
      ⟨addr, name⟩
  let marker (addr : Address) (markerName : String) : KId m :=
    ⟨addr, Mode.fieldWith fun _ => Ix.Name.mkStr .mkAnon s!"@{markerName}"⟩
  {
    nat := r a.nat,
    natZero := r a.natZero,
    natSucc := r a.natSucc,
    natAdd := r a.natAdd,
    natPred := r a.natPred,
    natSub := r a.natSub,
    natMul := r a.natMul,
    natPow := r a.natPow,
    natGcd := r a.natGcd,
    natMod := r a.natMod,
    natDiv := r a.natDiv,
    natBitwise := r a.natBitwise,
    natBeq := r a.natBeq,
    natBle := r a.natBle,
    natLand := r a.natLand,
    natLor := r a.natLor,
    natXor := r a.natXor,
    natShiftLeft := r a.natShiftLeft,
    natShiftRight := r a.natShiftRight,
    boolType := r a.boolType,
    boolTrue := r a.boolTrue,
    boolFalse := r a.boolFalse,
    string := r a.string,
    stringMk := r a.stringMk,
    charType := r a.charType,
    charMk := r a.charMk,
    charOfNat := r a.charOfNat,
    stringOfList := r a.stringOfList,
    stringToByteArray := r a.stringToByteArray,
    byteArrayEmpty := r a.byteArrayEmpty,
    list := r a.list,
    listNil := r a.listNil,
    listCons := r a.listCons,
    eq := r a.eq,
    eqRefl := r a.eqRefl,
    quotType := r a.quotType,
    quotCtor := r a.quotCtor,
    quotLift := r a.quotLift,
    quotInd := r a.quotInd,
    reduceBool := r a.reduceBool,
    reduceNat := r a.reduceNat,
    eagerReduce := marker a.eagerReduce "eager_reduce",
    systemPlatformNumBits := r a.systemPlatformNumBits,
    systemPlatformGetNumBits := r a.systemPlatformGetNumBits,
    subtypeVal := r a.subtypeVal,
    natDecLe := r a.natDecLe,
    natDecEq := r a.natDecEq,
    natDecLt := r a.natDecLt,
    decidableRec := r a.decidableRec,
    decidableIsTrue := r a.decidableIsTrue,
    decidableIsFalse := r a.decidableIsFalse,
    natLeOfBleEqTrue := r a.natLeOfBleEqTrue,
    natNotLeOfNotBleEqTrue := r a.natNotLeOfNotBleEqTrue,
    natEqOfBeqEqTrue := r a.natEqOfBeqEqTrue,
    natNeOfBeqEqFalse := r a.natNeOfBeqEqFalse,
    fin := r a.fin,
    boolNoConfusion := r a.boolNoConfusion,
    int := r a.int,
    intOfNat := r a.intOfNat,
    intNegSucc := r a.intNegSucc,
    intAdd := r a.intAdd,
    intSub := r a.intSub,
    intMul := r a.intMul,
    intNeg := r a.intNeg,
    intEmod := r a.intEmod,
    intEdiv := r a.intEdiv,
    intBmod := r a.intBmod,
    intBdiv := r a.intBdiv,
    intNatAbs := r a.intNatAbs,
    intPow := r a.intPow,
    intDecEq := r a.intDecEq,
    intDecLe := r a.intDecLe,
    intDecLt := r a.intDecLt,
    punit := r a.punit,
    natRec := r a.natRec,
    natCasesOn := r a.natCasesOn,
    bitVec := r a.bitVec,
    bitVecToNat := r a.bitVecToNat,
    bitVecOfNat := r a.bitVecOfNat,
    bitVecUlt := r a.bitVecUlt,
    decidableDecide := r a.decidableDecide,
    ltLt := r a.ltLt,
    ofNatOfNat := r a.ofNatOfNat,
    unit := r a.unit,
    punitSizeOf1 := r a.punitSizeOf1,
    sizeOfSizeOf := r a.sizeOfSizeOf,
    stringBack := r a.stringBack,
    stringLegacyBack := r a.stringLegacyBack,
    stringUtf8ByteSize := r a.stringUtf8ByteSize,
    stringAppend := r a.stringAppend,
    stringDecEq := r a.stringDecEq
  }

/-- Resolve primitives from the environment using the canonical address
    table. Builds an addr → KId index from `env.consts` (mirrors
    `Primitives::from_env`). -/
def fromEnv (env : KEnv m) : Primitives m :=
  let byAddr : Std.HashMap Address (KId m) :=
    env.consts.fold (init := {}) fun acc id _ =>
      if acc.contains id.addr then acc else acc.insert id.addr id
  ofResolve .canonical (byAddr[·]?)

/-- Anon-mode resolution needs no environment: every `KId .anon` is just the
    address (mirrors `Primitives::from_addr_names` with a `None` resolver —
    the name slot is `Unit`). -/
def ofAnonAddrs : Primitives .anon :=
  ofResolve .canonical fun _ => none

end Primitives

end Ix.Tc

end
end
