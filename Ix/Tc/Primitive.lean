module

public import Ix.Tc.Env

/-!
Mirror: crates/kernel/src/primitive.rs

Well-known primitive constant KIds. Content addresses are hardcoded Blake3
hashes matching `PrimAddrs::new()` in Rust (regenerate with
`lake test -- rust-kernel-build-primitives --ignored` and paste into both).

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
  natAdd := h "d6f62a9779108f9fb6b66b31cc94c3d84ca72d8bea185e13137c50c7ef84c969"
  natPred := h "914f9c01884853652e9224dc511f867d5408517f3beb3192fc4477e0e9594c88"
  natSub := h "fdbd5fef40149c85333c6f3ccebb4be741270d2066336cb2eef87623744b72b0"
  natMul := h "6649665607b0750c2ca73f45de600f21cb670398504865bb97972438014f96d9"
  natPow := h "33c604451d01cb19a433668246b98f6e874bd630b78a791d7a373a979849a1cf"
  natGcd := h "3be48357ae17f74d4df27d697aed3f47c1307941f41affcf74da5f66d511a797"
  natMod := h "5179638b82cc8337914a7bcaad858c85888844e9a292430cac51e5eadc41a1af"
  natDiv := h "89deca86dd8f0066a5064fdb19a2c6897a3a9867caadc04f778d5c5cd0225362"
  natBitwise := h "d2075e323bed82f23eaf75ebc0fae4ceb80794240c046b90c51a94d07f5e885f"
  natBeq := h "a34ab2daba34839e851fa3675124566f9f4dcde597349ecd54ae32f8424e44b8"
  natBle := h "de0befa84faa22d1394379a0ba67296e116660f781b4eb639dbbaba200ef2bf8"
  natLand := h "818abb331150400d10b34fae4dfb9426741c4607baeed8d96271ba1659058ef8"
  natLor := h "9b76f32bbb1dbdf4ff68e0221225015df0ca2d2a6023c1a81306d4020d4ef397"
  natXor := h "97e325a96a6a1827194eeb7d2aa0d91921073aef9c2d333c24613e9ac956ed29"
  natShiftLeft := h "dc81e41cad1190377dbe604bfc3afe658a413b9a2dcfbcab79fad7b7a5cdd954"
  natShiftRight := h "6db49304bf0f5acbfd1d9d9a0c1b7ae20ef99d0737887056129f5b5cb5a9ba8a"
  boolType := h "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4"
  boolTrue := h "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762"
  boolFalse := h "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e"
  string := h "7ab2d52ac52fd1f51809b718e53cd058ac4b50d65150e78ae619139ccf13c8fd"
  stringMk := h "9671fd4fcfbc061c93c2824864cf03124ffee7cc22308de12a7c826473e49906"
  charType := h "29dd2d1986a525bdde49b4ad2defc349cec71d0484cd13f2da92f1fce89a4c79"
  charMk := h "97afa5ad3d86895e6d155019b66c256cd1aa862b4e3c89d8c6580b61939ee541"
  charOfNat := h "1a4c66f76760f5ef386de089682a55b752131e14a08557c4465ed17fe0c4dc86"
  stringOfList := h "9671fd4fcfbc061c93c2824864cf03124ffee7cc22308de12a7c826473e49906"
  stringToByteArray := h "ed43c77e555593b6cd0d4bfbc4273ba122e1c0cdf1090571612a952f941eadb1"
  byteArrayEmpty := h "7cfba8fa95847c213aa4066110ba01a97fb597daf29f5c07f72366072f250744"
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
  systemPlatformNumBits := h "cf86263521d345c39076473ecdb9f6fd411b5b503bce83e2318ba3fb6f2376d8"
  systemPlatformGetNumBits := h "f5d256c1dd794d02cfdf1762c9e41b13abe5bddde12d929d02ada37e4f40e85f"
  subtypeVal := h "0b5958a3c822c99e8643a27f0b928dfb82c45447bee0353c200ad1b7d0e46092"
  natDecLe := h "ec1f60c1a28d48bc98fe3ef72d255132735a503cc36e3ff0f22e3d486e266ebe"
  natDecEq := h "b4b26c2e29931c06e885914613faff5856138e5cb09620ddb6921a342ded8957"
  natDecLt := h "c013c153ebf02028aed264333c1e4c85017d0b87025d7596a96971bb2b67921d"
  decidableRec := h "ab3776985743af13a9cb1a7d2f8496997892e17983d14be5270a716570b35719"
  decidableIsTrue := h "0f9ee8d9033d8f7b852f5b7152fd124f7d411930c992e0f457f8104b60a98381"
  decidableIsFalse := h "0471e47158b2ae18d3c08dd5c77aae23e62d7bbc1e61116bc2813b1306bc5795"
  natLeOfBleEqTrue := h "21e0e0783b7617b0cc4eff4d1fab7cffefe01cd43da77e2f98d15094a0d8f086"
  natNotLeOfNotBleEqTrue := h "0183595b837b9b84da5f004b8ac4a4bbd3bc0628b99c8d550eb351f74ce16d48"
  natEqOfBeqEqTrue := h "9ce6e322f19481f21cf4c48f88789876b69b8a9b1520439c101d983f96ea60b7"
  natNeOfBeqEqFalse := h "3cf54d333821dd37683a0bf38739e687610a1991759220b77edec338ba3cfbc8"
  fin := h "745936fcb9d86c4457f0fd1e537e67077f46f7841108419dac7984008b565b97"
  boolNoConfusion := h "cd983a826c1e20c4570afca244916c79e20e816f618ffdda38be8a79079274ce"
  int := h "a5ca2e1d5ceb8d43367bc34d69a50c1650a25dc10780aa0c378cdfa931ff0424"
  intOfNat := h "09bc253147c36ce22c8e0ccd43c79b2cdae2206e0ddd168fca3609b2a584d3dc"
  intNegSucc := h "267c0a9c92e75638fc73ed52a9f9c81647eeeceeff2144c1f97e65e2aff149f1"
  intAdd := h "ca99084c9d2fcb4c5dd139aecaf159ebd04992d76230cb930f41b86074684817"
  intSub := h "d3141231800e012e8db7c240f794e4929bfd156b3845e22f1cf31d3fe39aecd9"
  intMul := h "482064e35634a95c0f252de73d687c24764ea4fa7dfd14cf7af8aa7531f17a5c"
  intNeg := h "f61c7d3fce595430f86f0cd52da5bcb00bf910edd85e14dc0402130fcce34ebd"
  intEmod := h "25c267ef44f15007f2d2e0819be6fb64902c33a7d27a6f2c9d61263898953804"
  intEdiv := h "49b34dcbff1e60532825ff5af477eb5de9810ee38e0f7a32014d54c8c1a3a3c5"
  intBmod := h "6a6adf0e95b3a4ce18330ee22105712e9a640ee4311b5dd1022a8e0a30cba0af"
  intBdiv := h "a4f1d7a3fe5b6b2ef9522fa537f1e622fbb8176f9fb3358c56cebe1a379b6184"
  intNatAbs := h "83e3ce8a747520cc248a0dacf9bd1369467e4907e8aaaa433e1b438e1cad7ca4"
  intPow := h "73ecccfeab8a63a3a0faf8d71dc77995bda83418b13cd399b1fa571b50b4575e"
  intDecEq := h "83fde38faa1164648e4227975abf2e8c260d7d4ef1c92676214ffe5826c2075d"
  intDecLe := h "38d60ffa07b50678d0c3bf0c06f86cd7967b35e87ab071bc55899fcbaed4744f"
  intDecLt := h "5568e799198dad9fab0e784b7a4c58112bfc2688aecebe3c2c6563304210f956"
  punit := h "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b"
  pprod := h "81a422a42b2cb656b9a47e61a4422f89cdb0a0c166035d47bf5e2c2af02175fa"
  pprodMk := h "c9c584da782cdc453306be9a643244fa0bcbfc3b5dbcbafe3f6b9d65df031fed"
  natRec := h "b975152f3f0cd9039433c68f5a5e5455f5cb5d917078baed0118b59067a74ea7"
  natCasesOn := h "1917841d2085796dd7ba346de93a579571b5641c33fc400408ec55b5778a9a51"
  bitVec := h "698dd593abfb63db362aaef57e70a793044fb657257291ee2c3e997caa423eae"
  bitVecToNat := h "77a025c19f8be131fb9d5b0bec494817a26538b9a550abbbcec8099fae9de4e4"
  bitVecOfNat := h "90ca8130735c8d9a34005a8943b59fe1df182e08a9f2bfc7dc8323229659a574"
  bitVecUlt := h "9fd8e7459a1d2deef00a4992a50419bac66c03082b58ade07422896f13033d74"
  decidableDecide := h "c5f7b19663e4499e70e1b2645162c5be15fa860f4f8157e331ae546c6f733723"
  ltLt := h "cacaea97f4cdba0a4a0af71005d0517d1818ab2623bd2ea7fa8c637a0e3d3312"
  ofNatOfNat := h "5a7292ad756ee1f2df4b92f18a27574a47cbbcf7094f98ab2865f92eb22342d7"
  unit := h "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb"
  punitSizeOf1 := h "7bd8e19f47f6eae620a5c39f243ce415dd6a77f09590f4c227cef363007f4012"
  sizeOfSizeOf := h "389715f91e66683dc7108ccd853efce92949512fa659ad3c1902e754692919cd"
  stringBack := h "e95c8d876e7ccf780418615e33b747a245d94facd7567fecbe7ae73a5ac09206"
  stringLegacyBack := h "6bb6162aac7d6a01b6ec05580664e8a7f0d4b0ec1fc5afaae66018e9a1936dac"
  stringUtf8ByteSize := h "def4433d9547b53175e24a3ac182c88b072af0d4ad33fd04ec4cf2ba3d95ea93"

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
    ("String.utf8ByteSize", p.stringUtf8ByteSize)
  ]

end PrimAddrs

/-- If `addr` is a reserved kernel marker, its diagnostic name. -/
def reservedMarkerName (addr : Address) : Option String :=
  PrimAddrs.reservedMarkerAddrs.findSome? fun (name, marker) =>
    if marker == addr then some name else none

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
    stringUtf8ByteSize := r a.stringUtf8ByteSize
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
