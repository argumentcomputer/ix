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
  natAdd := h "5ed78ee081e10bc0999a372a5e54acd3373d85d41e9be3fa75fdde32db2d6501"
  natPred := h "914f9c01884853652e9224dc511f867d5408517f3beb3192fc4477e0e9594c88"
  natSub := h "610fe5a4f5a03f64f60ef5a069f1640758e000a1b4d57fd594866e9f6b3381ed"
  natMul := h "da6fb725803db79f318e8aef5b19e1d4c2d1a7c41831df48787e8a319b8c48d3"
  natPow := h "ab6f3f1cad636ceeb67df749cd7cc634a2d68aeb54255e085ca7ef692b395e63"
  natGcd := h "8cd419904449a4d91beab84dc26b48b216dafe1636d71f48dcc0d20c9fed10eb"
  natMod := h "4fc91588d0b04ee9eb2201c80b72b39defa1edf45c82e5eae34e1f71858d76b6"
  natDiv := h "83c270388e404a2dcc9924f2482782d9debf7166f3d2e0763a7828172b8c131e"
  natBitwise := h "c60b9a8fdc174dbe1647a1f0d3cef13c5df73871d9eabd002c7a76f36e654800"
  natBeq := h "fd8625d516605103bf8e019a5d86d47d34dd47c1ef649e3dec0fa697bbfd9e41"
  natBle := h "da3f95087782f40743168bd9176ddcde64bf5a4d503463c3d5eef4ca2efaed23"
  natLand := h "64e182cef33cb717b788404d31bad2103d1afb76db5447ba3432d83f72cb9bf4"
  natLor := h "d75de12a584bd5febaf89a7728dc6270ed38ae1797ff5a44683b8df159509994"
  natXor := h "0c6788b58d9568cc118a9b0a861e872732dbb8453647ea9d6013515244e60e38"
  natShiftLeft := h "424c36ee14362ae7342d1527d251d4378afd2a45a3b5097d2d2ae0321d5f9fff"
  natShiftRight := h "aa9b61bedc9ee6a9908d5f0e98955f18330f38587df710fdebe415cec7da29ed"
  boolType := h "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4"
  boolTrue := h "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762"
  boolFalse := h "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e"
  string := h "4ac09ed8ff61e44f1159bc6fb00fd7e72c15deefea569d755d8b1d05f5d191f7"
  stringMk := h "8e9e6af2d65a17094a87500f84f7b26d82edcad0dd6999794a8b46ecb554242d"
  charType := h "98c98c0f996f21f6e2b61f1efcae99baa98be26a7ff82515684a826954b35e29"
  charMk := h "8ef984f787bf09688fd6ef734f7032b3f43c0e667159d2eaf2b030326271d2cc"
  charOfNat := h "604b23cd0facf5b3e56def57da91b2688ffca7c5435bb5dc2cb11a68a3318609"
  stringOfList := h "8e9e6af2d65a17094a87500f84f7b26d82edcad0dd6999794a8b46ecb554242d"
  stringToByteArray := h "35d4f382e24e009cc0e9457955d3ef1e6f79fae9d8d31cfd2e153fa03b054a6a"
  byteArrayEmpty := h "e21c24b42f049239c7f73392fedc911f574c798386cbe3e3e2a2888e2df3aef0"
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
  natDecLe := h "08faad5e92316e17e5f80804982c6f853e32bc43f4dc410619ec13df152377e3"
  natDecEq := h "676e87dde5cf30c001690bbbe7ab74fca92b0aa612ed9ef3caf89f1d9e6a2401"
  natDecLt := h "cce125650b775d1910efea919f5cf272f7d9e7b11d62343d6d0a589cdfaeff21"
  decidableRec := h "ab3776985743af13a9cb1a7d2f8496997892e17983d14be5270a716570b35719"
  decidableIsTrue := h "0f9ee8d9033d8f7b852f5b7152fd124f7d411930c992e0f457f8104b60a98381"
  decidableIsFalse := h "0471e47158b2ae18d3c08dd5c77aae23e62d7bbc1e61116bc2813b1306bc5795"
  natLeOfBleEqTrue := h "cb1fa5ad3e632c07b48828af604f73c70a820b1de4a13babf31f2b7896f7f9ba"
  natNotLeOfNotBleEqTrue := h "ea7561db25aa24ce481ce3e9ee8d704d483dd9056757da7eda24b5111be59bc2"
  natEqOfBeqEqTrue := h "cb0ff07d3f7226a898769da8caac9ac1b49226d6ae43b2affc849a97f9d3e5c7"
  natNeOfBeqEqFalse := h "79a57e7f8d1030fb95ff4f19ea212c9ae011638ff7349c4a692ddf5e8e071ad4"
  fin := h "745936fcb9d86c4457f0fd1e537e67077f46f7841108419dac7984008b565b97"
  boolNoConfusion := h "cd983a826c1e20c4570afca244916c79e20e816f618ffdda38be8a79079274ce"
  int := h "a5ca2e1d5ceb8d43367bc34d69a50c1650a25dc10780aa0c378cdfa931ff0424"
  intOfNat := h "09bc253147c36ce22c8e0ccd43c79b2cdae2206e0ddd168fca3609b2a584d3dc"
  intNegSucc := h "267c0a9c92e75638fc73ed52a9f9c81647eeeceeff2144c1f97e65e2aff149f1"
  intAdd := h "2389b32aaff43e1cda02299613f3b1d1308e448cac31678f1f358819f84fec31"
  intSub := h "dc3f17411b643dcf55164c6eceb086daf2c788c0becec06c7808714a909979db"
  intMul := h "d5b342455210f488f1d6805e7a0bc06aa686ca45d32e05abc407815a600c07bd"
  intNeg := h "f61c7d3fce595430f86f0cd52da5bcb00bf910edd85e14dc0402130fcce34ebd"
  intEmod := h "3b5f63733cd0fbdff551b0a006ba88a6f9638db75ee6385576a2c1ad1c93b500"
  intEdiv := h "d6d38dfff92a41edd96fb8b935d1725e62202fa7af7c8503e1aa5b6a49ebf172"
  intBmod := h "34dbb235a97b1719b2be6d8c7242d58cd3be2d3cfef59d4276eb7d0d6e2dac80"
  intBdiv := h "a4b5c5e3a05be0e12faf9412376ff23aa975f8e56669255d5868ddb1c7ad4a90"
  intNatAbs := h "83e3ce8a747520cc248a0dacf9bd1369467e4907e8aaaa433e1b438e1cad7ca4"
  intPow := h "836aeaf2e8c4b240d2e8243f4a9a25679937f2581408e7b3853407bbd18e45fc"
  intDecEq := h "402cb01bfa52fe93aef3d96e7d28ee03e0e1f76f3c879654f5e719a72015237f"
  intDecLe := h "bffed7cd4968b8fc251ed24a9c253da00215902354c2944f59e81538dc1ae2c7"
  intDecLt := h "09b5fb2f2d8451689f842711744a27bfe55c6fd5010fd24a90845393c707e0a4"
  punit := h "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b"
  pprod := h "c1c9c9a4f2b52a87f6be51476de8fe93d3ed8e7fd5652d5a11617e3255190da5"
  pprodMk := h "59f659338954244d5574ab1a951c11d7e3a6efe2964a466d460450809732dfb2"
  natRec := h "b975152f3f0cd9039433c68f5a5e5455f5cb5d917078baed0118b59067a74ea7"
  natCasesOn := h "1917841d2085796dd7ba346de93a579571b5641c33fc400408ec55b5778a9a51"
  bitVec := h "eafd1b2f6b571abf76ae96eaf9c4852aa4520d06df534291590a71a21e6f0b5a"
  bitVecToNat := h "986b9c736cb930c81cae697ec496804b6e4415a178e4f0022fb058f5034ab7bf"
  bitVecOfNat := h "da082f157d2a7b86eb226b1881bfacd0d9dd1be17a27e13fa300c015c4ffbf85"
  bitVecUlt := h "b668db7d12cabb4d7fe2e1af25984baa28bb2852a982da8d54942bb344726ccf"
  decidableDecide := h "c5f7b19663e4499e70e1b2645162c5be15fa860f4f8157e331ae546c6f733723"
  ltLt := h "cacaea97f4cdba0a4a0af71005d0517d1818ab2623bd2ea7fa8c637a0e3d3312"
  ofNatOfNat := h "5a7292ad756ee1f2df4b92f18a27574a47cbbcf7094f98ab2865f92eb22342d7"
  unit := h "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb"
  punitSizeOf1 := h "7bd8e19f47f6eae620a5c39f243ce415dd6a77f09590f4c227cef363007f4012"
  sizeOfSizeOf := h "a343a651bff408c3a29ff27b2b62e34b54b2ab381cf6f3ad87c540c977dc3c4a"
  stringBack := h "d07f8105c544227a13ec90befae2005e9c6f64493f8c7ff669ba743e1547c935"
  stringLegacyBack := h "fc49357a5bc6525839a7bc11b9df207852a6e9c6afa3ec62bac3c542ac89e0e0"
  stringUtf8ByteSize := h "6a142d91e877959e1419c345808a79a3e95818577afda68d287f4f881521dde9"
  stringAppend := h "3803adc21d899693a1491db054104b20bd40fc0ca1f6b4374b7b158b4252b38b"
  stringDecEq := h "ba51b5d8a3b14201d22402cda8e731e49fdf78f08b72643c1b08e250436aaff1"

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
