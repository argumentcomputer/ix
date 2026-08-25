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
  nat := h "1dfffde48c4ef6653b95ecc5474dee8b99461008d26d80ca384f1e59e927714d"
  natZero := h "50e5d69d806bc1c616cace4230c982a0ee5b350b3efe3b1a15801df77fc00c8c"
  natSucc := h "8c09ca644b10decad158d37006e81cdc1b84761312260546449aa02e343b2b0c"
  natAdd := h "f9ac92a11388a7cdca229a8024208554feb32d6c0a3af74a7bc12c28b949543c"
  natPred := h "fce916cf3c6dd01ad8c6d38641bca7b3eeac5bc93b3529ad7812768b3407d64e"
  natSub := h "df38352ffa1d6e292349259f33eb678024bb646b358638a02da1995ed4abeb09"
  natMul := h "f38d4f7baaa021e3b555312145d9ffd3ddc5eacb7bfd5b86a7b0eafdfcf416aa"
  natPow := h "68f61ef55b63cd23ad8ed185b7eec3dc754e61cc58056087a97e819d0e95e6fd"
  natGcd := h "ad47f2bbe891b825c48a278f9a0d72997b78baac79891ca6651988b7c9b47f03"
  natMod := h "f6eb742996c60f1068c2d437afdd8b3609040d64eec5e15f07a11dc11d070d7b"
  natDiv := h "23173649a58ea5095d1c51a21c7ad2cf8e8dccef342698e07e241668ff7ad3e7"
  natBitwise := h "85a6fefff63e96a963ef8406d394ab39992323a0ff4530e134a94d46e3a7ba4d"
  natBeq := h "72c6d4a3b653798850a9ed57018b87ceee0e34195c0902858fd41f6f0e9962ae"
  natBle := h "c37f2e811f44d59c07094947146ffcbd3aec5ec7002ac3c48ebdebcd83d4688e"
  natLand := h "8f475cc72da2ac6ce2a9282b6b5df4ccf7bc3cee0649d22766bebd32d1806f3b"
  natLor := h "8f3c1c432c598e4240d36f8945942174675c5c91e03f6b8ab018e8b052622c63"
  natXor := h "800a8a2d6f91bd1a91d313d1e19ef69f37dedd07f7de4f929780be855a03fd1f"
  natShiftLeft := h "5473592e707943ec072a2ee53c433da2c77aa45ed634da54b24374d19eb90cd2"
  natShiftRight := h "1b591149158d896937eebfd53232b5ae8a4bcdb25a6811c96bd94114a9f8bed5"
  boolType := h "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4"
  boolTrue := h "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762"
  boolFalse := h "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e"
  string := h "4288f92ed1d51f4935e5d2775f33ec585d6fe5ec63dadf0ea698554478fd9fad"
  stringMk := h "d54db71fee55311aafeead74768e6e952262c29abd24b9319fa6859481dd44b8"
  charType := h "d55429725a19c1837b34624fb35784b91bc8b0e2d79f98b3c296317fb6c5c789"
  charMk := h "7b443f2f10fd4b2fb88b59e90f1a04b46552f73ea2e8f26d77290b7ae63dd531"
  charOfNat := h "29563da271c23f66b27d05f924fb0612272dcfba6b1083b348733e00f9b36b2a"
  stringOfList := h "d54db71fee55311aafeead74768e6e952262c29abd24b9319fa6859481dd44b8"
  stringToByteArray := h "ad700c0806e673e74adcafc28ca659d30a616633a4a36420324fc29eae69eb9c"
  byteArrayEmpty := h "d838bb6bb651533081ac2495a25d690c54f8e345fff41efbd5585eb468705308"
  list := h "ae8d736dd3fcc89dc3f9d66aa54bed4ad8607fb9d4843f4c8736591dd0c9e000"
  listNil := h "3c0149c3432969ee5d9354c8d2d89ceec4a79711f8dec8710879a12a12b72c42"
  listCons := h "d1e0802c38bcda14061e2012f12e73c2a24a671137984f8ef76744ea04d188c4"
  eq := h "b20ea17ba3d9723f0bd06457d9cf48ce26ca36619b946980627de923873e9595"
  eqRefl := h "e308035bdf280c927556824d6a9f9236a1487651f0059a7df3bda85b331f67e6"
  quotType := h "e775aa31759a9d4acdbc2b8519ff73f57552bb0cba4daf1659bba00f6a931b4b"
  quotCtor := h "0a4cc7c930dd6726bbd7f1bc3fea685df5f666549d651d3e766fe5746ec459a4"
  quotLift := h "560276f95e0d93e27b8c05097995bf82876332c2e7e31033e0a194819e4e8d30"
  quotInd := h "02f358808fd4328d74850582d3608d2d31e49519b4c6c66b3605fbe6f42d3c5d"
  reduceBool := h "d4d775ceff37ab7a402416118f1d2ce5b9e7f2143d0c3dc8fe5431571df3260c"
  reduceNat := h "2075bda5457b299b27246770c8416273686bbf627aa6a01ac413a27e583eb95d"
  eagerReduce := h "ff00000000000000000000000000000000000000000000000000000000000003"
  systemPlatformNumBits := h "5060a22df86307dd8bbe656e13868f3a1618e7a0d880b8cbb00759cffd31800d"
  systemPlatformGetNumBits := h "80f975ded9d6ab7095e9db2ed1cfa6f5c35eafe5c56990e2c1321b02c5664e6c"
  subtypeVal := h "7e4e9b33b696a7d3fce1745dfb5fbeeb938fc8882a82bee15723e0d253e59158"
  natDecLe := h "2999801598c1da48f562d4836064f635c045d0521452b5e74a12bf99d2e316ec"
  natDecEq := h "1bac041756ed22d73bbcac849a94f246ee2696999faf351940468d962970ca2a"
  natDecLt := h "12f386f486913b11b5473cb2538330d51f25aeec7f2d7d6b96904329c78b6967"
  decidableRec := h "6af73809a6128adcb9c5d7e73a30c28d489dba4d905717055ac2edd755ffa713"
  decidableIsTrue := h "7b3f6a6eebf32a9d5a54305e693dce60511afeb1fa11bc8844a5c21bbfd3214c"
  decidableIsFalse := h "ab1470196419f71d06feed9ccb8c1d03674528ec03012b095badc169d48d03d0"
  natLeOfBleEqTrue := h "23bea3bbf3a8d0a8d0033cf7e56af0c4aee01582d5a758c0df5615929ca6204d"
  natNotLeOfNotBleEqTrue := h "be50b6053df0b07438a4ac2eefd70a11708b0cbb0fc90564bafee6e165615de8"
  natEqOfBeqEqTrue := h "c489329197b59a040d1e5e4d5de6a770478d1ea4f9750176026dd2bf8593bf22"
  natNeOfBeqEqFalse := h "0eb5b987f12124be0575a477cc0a535516a24b0ae5ceddbee2d472765aed299c"
  fin := h "a7e9a8b84a2fe96cc204acc93d7ed1366d9d0574aaf0f09633d2b09a94c9e860"
  boolNoConfusion := h "99e7eaac2b27ffae4adc4902f8965520ee696c662438f10169cf36c8ad4cc4e5"
  int := h "fb2bd9d8fb7c3cc603bc021dcdbc5c6aa3ae80688b7d2e85ab18fa336ccc04ba"
  intOfNat := h "48786b7f7adc632ae35059f3fd181df32d9e5cc7360c4fd02c3e8b1181a1539b"
  intNegSucc := h "cfc934fd6d53a5b23b6a3b30d02165fdaa574e3b5eb13926bb166e6486fc0e50"
  intAdd := h "1e60bd377a746cb7bd7ae541d7dfb237097d883d28ec7aadd732c0674e0db964"
  intSub := h "0d74ba85f9749a0c25aa6a2b70348e57e709831fb7cc05229fecd7d66adf184d"
  intMul := h "c5bef6be6c3fdc520454c11e9950eb2f1a6c92f41a646b5ca168ff198f13c55a"
  intNeg := h "bc61c10fcca6415223ed97bcae21cb99d4836d077b0786a2fc5c5905f8b04ba2"
  intEmod := h "d435a15e6f222f786b6130fa764c7fbe98746f798e97a627a6237a17e74f7227"
  intEdiv := h "3e13fc1a077eb692af40acbed4a6adae255c0cbbba9a3c1f0de29573b197cb0e"
  intBmod := h "9970f402c870e8a3146fbf4b76f949aa64b206de9b0157b469fde357b715f19c"
  intBdiv := h "867f8e9dfb752265ba4742368b6afa546ae4e240fc5ac69b4a4e86d85a6e46f6"
  intNatAbs := h "21d4dacc0f406b31e044fbf4d8987a332dd8b4244f7d9e62b086501474825544"
  intPow := h "878599e9f5bbccb942232ff93b62c63db4ebdf62b9f9237900a37049f422ad86"
  intDecEq := h "7a06496d07b59710348a5f657851a4eea1f59492a5b7de3f51abbc84f9bc1d17"
  intDecLe := h "14eccee1deba05e9443bd169d00ed634170e3246b37921199edbbad3f67db5b4"
  intDecLt := h "ad32c05d7e3c5ddf4e4c85cf8f60d83e0fba55e2676bf8a1e608db54b167c9fa"
  punit := h "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b"
  pprod := h "7eac420873e8f1ea8fe66831a6c6f69d88693bed6aeb30bfba82069af60ebea8"
  pprodMk := h "f3993d287c47b81c9e0902aa91d227650f6f4e55b3a1c63a87f283b4ed9e418e"
  natRec := h "89d6690b0808b1da49e015a4f21df3fc3f00fb96ac502f5f097ce452e573704c"
  natCasesOn := h "b2f8855b5e76a480493cd6cc922977e60723b4bec665dd7e9b73ca2b215df576"
  bitVec := h "c7192ac507d67c3c3e1eb90633858ae7b7cbc80e3988312618c7ec09b483b04a"
  bitVecToNat := h "acd9f0a3f7e8c53a46b91759358366fa028240b0b6cc09205dde34a33544678d"
  bitVecOfNat := h "5721ca2acf2c6994771509332fb185f783f442aefce417d2863e2d148edcdb8a"
  bitVecUlt := h "8d57c7c6aee1ba510d3208ddc4b08a83b44319f6af8ee09b3940d0ddedce1eb6"
  decidableDecide := h "d1107c99ad9ebcb5028d9aea0da521ed5c12e71ea2ecdeaf637bb4a14d4a7e44"
  ltLt := h "c69df4833ecdce76bdb0d23159e1fac652d88919768c312c6611dc060da16f04"
  ofNatOfNat := h "c68bfa47519ff72b1d053b86e6e3b7356286eb2252616cc5b2acbed59ef1f5f0"
  unit := h "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb"
  punitSizeOf1 := h "84fe3d0f08f0651a6f0936a9a0f18e4f0dace169ac4233bf1adad05d6e078a25"
  sizeOfSizeOf := h "78f38887f6bbe54339ecec6b3c5f66856de7baa530378d2d9065bfe2daf4b801"
  stringBack := h "3f92a46a1451fd66215aae9cf789ce38a2c73fdd55909d454f61259634d90b6b"
  stringLegacyBack := h "a2a310133d17371af67cd91d279aaf735fa8cb810c39aaa824a443c652e3df66"
  stringUtf8ByteSize := h "b1f6f04bde3d81f9102ea6b7d2c9f4236d72b17e01125523c5d5e261afc71105"
  stringAppend := h "b6ec2d443f3ee61de45ad859b8cc41a896d8fba49bc29883fc34c427dbdf71f8"
  stringDecEq := h "d616327d4fc219bd7114bad46cd0866befe2551518b5bf2e10b5cac93381fb77"

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
