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
  nat := h "35e1cc809f6f076521a43f85068d5592220407c0532b6a08952f40d8523d04bc"
  natZero := h "eeb2e6268ff6d0e6b2e9764d9940b81bb64b9f8f4b1358d294ff9817e6941a46"
  natSucc := h "42d6ed31536f0958176f1dc973383808ac8583223746ebca78dbe389b65321a6"
  natAdd := h "724db797e1817545a08371432fd1fa6428a37dcf9c1671df7e464849db0a81ac"
  natPred := h "76afa254a8bbf2ac4327d7b94be0c63bd708836b5f7384ce990388adb0a1d3cf"
  natSub := h "9de2d2c60e7d421a2fdfb8706e91e0e6d8576c3bd46ec00405c65875cb9b5a26"
  natMul := h "566a3c2249bc2076543d9bc561a841f6fd35ffb5bdbbc5c991a9c64feccbd5d4"
  natPow := h "5ba43ac3e5d29fe5ce81f18a18178a2705c37ee674b9b6ee50e9466a86593b15"
  natGcd := h "76007dcf8b285cdbd6f779012290fe2e6afd221ce8821082a7e2ef81e8d815cf"
  natMod := h "e6ffe78713d4b974a82d0187538f1a0cf5c4b260f0fd99264fab263b1af847f9"
  natDiv := h "c075ed976f1702f364fb0bb34aa8bbc166adace573f2ce914b43dc4f4aab6219"
  natBitwise := h "aaf7df6a1f024f580fde236cba16235f071d1b796cc279faf43178d22b5ae36d"
  natBeq := h "ffd3f02a19fda649aa5608ed818db382e160231b76d5b09176d7dd1a8d5b1ec5"
  natBle := h "68a3643ec69816aec107302ddbfa054cebcd3ec173cd5f7e6d883638631afe65"
  natLand := h "c61fad46a102dbff5922312d4fbe6e704ec3c62c6c6f64b3d481b78c77cf315d"
  natLor := h "cb7dccc020a530fed7c622b100ee52c1078b5018159ba4682f817e3776789ee8"
  natXor := h "d8a6b05a1a4e5cadc69c53792e8e130314745e76e32bb30a9ce0272fa079e8a6"
  natShiftLeft := h "5c15f98e2bd9c257bcdfac62b0043a2e3e2bbdff8b210f104b5c3739e862ac0c"
  natShiftRight := h "3f92725324b09fa75c6fcd16da863671428ff33b7db667eb760e1cd503a2bcad"
  boolType := h "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4"
  boolTrue := h "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762"
  boolFalse := h "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e"
  string := h "9d6ae43429ec02a9338bbcd0db0ac193d75ebd46f884bfcbd2c42bf7faea150d"
  stringMk := h "272ea5ce6bab8958165c7f56d71ffe2a5b175ed58110126dfa96e1f8a0c99ad2"
  charType := h "4c59bc4eac82d31ebed59bb206909dbded65b92fd56de2518fcdadb0a42c11a0"
  charMk := h "82e09601422cae23b0b6df9922abb9f0b014e20047a00a7ab96871dd7da3e5ac"
  charOfNat := h "caf51b039d71cfce7063e106064f9435f5337bbc42567c8c78b5f66c7f087920"
  stringOfList := h "272ea5ce6bab8958165c7f56d71ffe2a5b175ed58110126dfa96e1f8a0c99ad2"
  stringToByteArray := h "79862acfbc2e37b7b6122143f0a6a51114c34fa483ff14146483de18835d4209"
  byteArrayEmpty := h "bf58e6cb3aa0f746850629041635cd30c0ad66262b6617660f2290241f08b08b"
  list := h "4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01"
  listNil := h "3994bc51e3686f30a1d483d69d0a835a7b484d892393c084f87a5849de54f302"
  listCons := h "b3a7d80249fd823100ee03626232d1412a0e8335275d5df53b92943887b650f7"
  eq := h "c37d6290e00fb865fb5db7bce18fd69e6d1674ad573724b85466ea9f7578a207"
  eqRefl := h "d494dc601386ba8e8f0b711fe62a2d60ab60c6488c8cf6ce97796ebc3ad5fefb"
  quotType := h "45040b3126855169dad919a970a9c72cee5875658aedb3bd1f89fcdf8c88edfa"
  quotCtor := h "811600dfa59f3612cb03c0f0475af152399defff9226c6e19fd648041a6899a9"
  quotLift := h "86b365e75bb4230f04c6e4f3a7ca6988adf574616d79a3d7477ad65cac102110"
  quotInd := h "1745491c0d651de0bea589d5fffbc9bc4d7fbe897c1d805b1f7f59ca9696a6ef"
  reduceBool := h "bacc4c814a4572ddfd969a1857adfe18239eb6bd8b1627ee79744a6a9b23b030"
  reduceNat := h "b6327d9a1bbb461a447f0c971e622dd9a35132bd7de75bf69e20794d7a0e8595"
  eagerReduce := h "ff00000000000000000000000000000000000000000000000000000000000003"
  systemPlatformNumBits := h "6f620654d341990a301387b80ef75b1e0b6130ddf19164025b6dc37bf3c3dc18"
  systemPlatformGetNumBits := h "00c266834f9039931b4be2fac5584cd176a0ae7ee4cb4064ddb5e04dd12b6cbb"
  subtypeVal := h "ea65f517457fae9b705299da08b0d3c8cf9a476f16470cca5cae5ea7bd238230"
  natDecLe := h "f0f15ed079822f06e82e36664bf61e797e5b1e7b0b4155152762c513274bfee1"
  natDecEq := h "8a5d5eee414a2fa5956b74e8323a20508d774ed1b5603f55e774ad896bd3e6e7"
  natDecLt := h "7c4977196e95be2a759fc9c6d1533db8da49592f06419b155d888333c8dd8931"
  decidableRec := h "16cfddda9c274660f391b10eefe066275afffae1ccd49c6daf43afb8a80aea85"
  decidableIsTrue := h "363d071182be414e1a58599b83f5e19f9b873723054f4287ba69705aafef27da"
  decidableIsFalse := h "8cc0e1360c1b29108dab3d6172e7fce8a9aa9640daa4bbe99ba1305d9623624b"
  natLeOfBleEqTrue := h "ad25bfd207bae832c73d5ce614bead22ef9862e110f8d17a5064ffb7603eee3d"
  natNotLeOfNotBleEqTrue := h "e3658f50dc5123efff213588dee3d4c6063f5edb18950850ac0490c937819009"
  natEqOfBeqEqTrue := h "9c91e79de732226ba2e73cbdd330851baec40668eb40c6f32aa2f8dac5a04b51"
  natNeOfBeqEqFalse := h "a07db532747e65ee77a7ba015069bdbaf1f709ce0d60b83c94f40d0e5e57595a"
  fin := h "3d79797bc572d8f33eb7cff5aa13f8dc73bcf21026bf05d03888c9aa0369dcef"
  boolNoConfusion := h "de7b523cc4470e15328a01d935988861dadf9bd012240400464dea8c79a9dfe2"
  int := h "c60c95e3cdbf4ed010d999b3277f4e1fd3695e8c30260876102905d7b36241a2"
  intOfNat := h "0a99f49cc73ab9f42783092e7120613225670bab89b9d63533d1adefc876182f"
  intNegSucc := h "f7130d5864e1ba77b0f6a7338f92159c35bd5147e0febcf1ebed456e513538cc"
  intAdd := h "9db0177e4e8b6a0e7323069509c2457de9598a7e38e72ffe19ad34617256e10d"
  intSub := h "85621387ef3027028d835287f3cc1461ef041def1fd91e28e87f669cc04a5eea"
  intMul := h "b05459623d23299d3a849eb7fb75badbc1547a1cd9ee560c15067fbd985c6cea"
  intNeg := h "6701d765ff10bfa3a6c347df15194e0db862ee25b54f25a59f7cf21951a3997e"
  intEmod := h "e29cfa7921bb57f4782b021c977596a4fae04e94f7b07955fe2814fc48de90e7"
  intEdiv := h "9c952d45a3bd43161529fcfb5e276beab0cf4fd64a01ba9bc2c7cda376cb8f54"
  intBmod := h "0b1564dea6ffcd204ebcd1aa69d29ee6f3acccd87bd146ff674556ac9cc8ccb3"
  intBdiv := h "6d35dc43660f6c509a13f2824c027ed99ab070a08f058ff0a5f46a759250797d"
  intNatAbs := h "261ae54edb66e900784a64350bc01e8b3fe1332a47caeab58e0361dffc7ea008"
  intPow := h "87266415982bbdec50c61dec5b73cc0ccd5c997445997a9724a1cc5c2e39d3a4"
  intDecEq := h "fc8c44cc970cfc183ccd10a2d1cdeb2c849307760e91f5cd29a2b02f706d83da"
  intDecLe := h "fcdf1860ad4cd672239392e60e7b49e024af0475739c3a40195a914eaec42c04"
  intDecLt := h "1d54806ab1ebc791e1db96e88d0407cef3523927d60ba669689b92a8eeb36445"
  punit := h "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b"
  pprod := h "90ca5bcf995d68d7dfcb3c7cfe466986dc4beaa402b262ca395b3e53c36f6cad"
  pprodMk := h "ce30fc0f4135e679cf3b16d0d667bd9df4e7a69dbb8177a29e5c75b48c4cec10"
  natRec := h "d1053449c217e5cc6fc29b2cb59cfd5ead385d392d00ada2221d4000dda7def3"
  natCasesOn := h "c575abb02efd158091356aa793c809c0570f8a24a8a777f206a95b9ce0b88855"
  bitVec := h "7f0f5feda1828072123f242a46a40549e85934f7395e4f93f65dda4e4809f325"
  bitVecToNat := h "c110d614b441c6cca69ecd7c1c2c76f3bc21fd40c4001e6a1a7d1cf481e23cdd"
  bitVecOfNat := h "29b9f24086b1b1f88211358866139fdb7dcdfc97b5f6c77fc495bf8c77639982"
  bitVecUlt := h "9301d850bde246940b7b3e81e786f7f12bae8e5cea6b3f4040060b3a7f59557c"
  decidableDecide := h "20e8906280b4dcd74a7a78e06d580e6f00eebba9fc40789262e95cacb6f0d699"
  ltLt := h "4802b183f4d6dcccacba57721824a7bb67daeb2725da17239271c135952caa61"
  ofNatOfNat := h "a99dedbb1676866aed829c3d4bba86a37e98ec62a35834389c32937e4e2b1a4a"
  unit := h "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb"
  punitSizeOf1 := h "e85bf516c76cadd8ce1fdab3cc94ed685e47be3c7a8b52f53fe2b3502e6f70c7"
  sizeOfSizeOf := h "402b71bcccf0be0315f1bda6bdbb20e559e31704617d3eaccb05d5c5fe03b53d"
  stringBack := h "32104b03348d11acb2437fda24966dc58cc8c8bcca96582614e644d319a42c62"
  stringLegacyBack := h "37ef5fee765dc2e5c7425c180cd42007db7d29ae0d5c091789f462f2805b0e09"
  stringUtf8ByteSize := h "52b0226ea14c94b1f9334c9957f5589399a86bcdae111f2847c9b0c2fb0a2261"
  stringAppend := h "132f1175cc3cac5a3e3d74e8797f9ba67f2e467b8004a3f28bb5dfd16a3647b1"
  stringDecEq := h "19134fdc188e8377d0173857e15d3b5065ed76da981397107e5c404db3f3b718"

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

