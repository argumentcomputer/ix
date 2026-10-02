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
  natAdd := h "3e8aadcc611c4d8677cadf00c78506561d33738ee3d571f7a4196e260580c9b8"
  natPred := h "3244687301d779ec757274761d903def3eb3135177327b709bcbd854ef496f79"
  natSub := h "03b3a041285b0fe202d90b227d405c4cec252df18ba7616acd6dae2792e672bb"
  natMul := h "373b7d74f6b40da11b7ed79603a45ec7011a8831b720b57d2efe92e82a3d57f0"
  natPow := h "5baaf05c969d2cf377312111be51bb64c600c13fa164ee722e92243b0f771bab"
  natGcd := h "aba94bfb41351d4db36172c379a512f04219ef21dc5454d71590967d4e8f913f"
  natMod := h "11abbf986481c53a21c8cb21ee2581ae6238aedbec15f972959d086bef1a1985"
  natDiv := h "824d1c53d8c1c3cf0a27f24639ec2be1ecc13d4a01c993171595edccf6949737"
  natBitwise := h "6eff55f72c856bd08aa02896fb78d93c28e11aae2be05c318b9d1f9fab8d7a53"
  natBeq := h "d3d8ff924af9dc4b5cd869760615b3e7ee80916bb617259d45890c69f4128337"
  natBle := h "9e445b9d5f8252772347872e909b5db4e7eca7086cedf4fec6de840f6b7b5f92"
  natLand := h "d98bed1e14cda0eea470a5a49ff7926c80eb4bc7bfbdd0c3e14d4baa5c2dd0d7"
  natLor := h "88ff34dd42e57766beefc229d8b62dabba9cef6aadcc85c88ad67323d02bbf21"
  natXor := h "1b0acdd4080abe5bc4acb5f06527cb62ad92792eb429c2b3bcb6f471d7945085"
  natShiftLeft := h "05bb657e8b9d5dc224e7ef3d53e54153ce3ac26da8d1f1b1d61069a3726566cd"
  natShiftRight := h "25019ff485fcf5709597cd1e07fcc3ce796776ef3f715a6d187eb5831c63b4be"
  boolType := h "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4"
  boolTrue := h "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762"
  boolFalse := h "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e"
  string := h "221625a00ee2d6b96297e34d7e05bf7e4fd38d8d99d3e1d64a7cd2e06ca0752d"
  stringMk := h "45dcb3c5e5ada3bc0ca52d62a66f7f9dda3507df71061a5c200adea0cf241014"
  charType := h "065fc8b41393f525c1e541b9d4bc97c20c13bf23a7209a2093b6f4527330114a"
  charMk := h "60cc6cfe4577b99a30113d09e9921f2253fac15fe3d5ad976b9dc3626edc6822"
  charOfNat := h "cff875914f3f8b4f0014d1eaa223c6b9da7201239bc5976e140b69d99cd1f357"
  stringOfList := h "45dcb3c5e5ada3bc0ca52d62a66f7f9dda3507df71061a5c200adea0cf241014"
  stringToByteArray := h "de013024c598e5f0c3dcd067f506e1d2e32749573522acb539b61400627cf897"
  byteArrayEmpty := h "4da661917a58152f5ca974d2256d98efa9d722c4f16382e9cdf016df4c574368"
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
  systemPlatformNumBits := h "57a31c1e34cf3993b20939dd29ba27263f24fbbeede2f6a6d089b8051fe32c3c"
  systemPlatformGetNumBits := h "236e46bde1f59309c2cc685a7379bc5294a9817e597915ddcc4b3d933284cd70"
  subtypeVal := h "d1bfec8df908c887e4f489adc2eec77a53e8ff28b5bd9a4c21a56da6381eed8f"
  natDecLe := h "7bb659876671e03d0731c456e894ce9e6f7de8250ab4ae70113dc08e24532127"
  natDecEq := h "f1de7103802ebc5309041bdaadea4a65652d54af37e66aaaf41787b1d8919557"
  natDecLt := h "af586b07546e1fca9ab0780d1c236af8d360c4c6bb32bb0cd03ec9ca63d3da96"
  decidableRec := h "3ea7e18fcbb7c498b2a45237bda659c0edc97b3d54a4ad0d11bc2ebec80cfa17"
  decidableIsTrue := h "363d071182be414e1a58599b83f5e19f9b873723054f4287ba69705aafef27da"
  decidableIsFalse := h "8cc0e1360c1b29108dab3d6172e7fce8a9aa9640daa4bbe99ba1305d9623624b"
  natLeOfBleEqTrue := h "5c99dc61889e4a1e06ff6f24d184dc6553028cc62b89fa61bc23115b6a762068"
  natNotLeOfNotBleEqTrue := h "93c0ea70c5c33f7bcecd405dfdee5c5471f74aee61f8bb610b2552d7ffe28183"
  natEqOfBeqEqTrue := h "c44c528578dab3903088d064cc9b679d2c0eb3fe73da3c1ce1cc9d1b8f2cadd3"
  natNeOfBeqEqFalse := h "6a7739ca74fd0033ddcb1c4d98cde41920f173d3b8a6fade75a49b7496ec8cad"
  fin := h "1e1a2bbb1920ed4a1281a3deca646ad313ca9c7bf7eabdc3655987797ccc0c55"
  boolNoConfusion := h "55b3bf142fb5a8078ad3b7515f90ab239c32ae0443dfe383b67dae6f4ba17fc5"
  int := h "c60c95e3cdbf4ed010d999b3277f4e1fd3695e8c30260876102905d7b36241a2"
  intOfNat := h "0a99f49cc73ab9f42783092e7120613225670bab89b9d63533d1adefc876182f"
  intNegSucc := h "f7130d5864e1ba77b0f6a7338f92159c35bd5147e0febcf1ebed456e513538cc"
  intAdd := h "b666925b10473fbe1a7630ec496fe07d799c5248667db1e2302fca5fe4c50cb6"
  intSub := h "7c60043d6016e2f0ef5d764e1ab7923968d43d5c388186ddf6c83c28f024017a"
  intMul := h "9dff949e4d0282393213042a36a69af4b71a58709096eaa3de5130bae0af84f3"
  intNeg := h "19c87649f9a17809f248beff7bc37f569f548e24a98d8a7cddd5b82eb808e5a6"
  intEmod := h "13c97e84fb8ac3ee8120e923d61fca6f7e6bb9241ec3aa5d359ba5dce542aa11"
  intEdiv := h "53e404f5dd3c53693bc3b5bfae582b0496ec3c05af0cee0a46c38ab662c57fdf"
  intBmod := h "d0380dc9b63afeeb3235a77adeb355a8b52b0730971595093741ec2c6d57cd49"
  intBdiv := h "209aca62cc1f9dd2c0a928cd84d72bb41570aa97c1fd833e5fffc567c1c6401f"
  intNatAbs := h "01e7c724508897e01e5d0b8f72e2cfa2607cea5ff0d352d008d0e7512aab2f46"
  intPow := h "a28958d747e87b5a60e4fa07ef7ed8d949f69adcbc44afe2958482d3ee9b3365"
  intDecEq := h "35a9ed7202e3c43857cdc4063eac123fe7b77f0631154ac540dba2c997bdf224"
  intDecLe := h "1710034a517f249f5c8265e8e2783be60619f0c8e85f4eab625e85983abd722e"
  intDecLt := h "5318877ae61e1da37980d80c11e3e47a36d850c3e43e99716122f1e6eff01e9f"
  punit := h "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b"
  pprod := h "90ca5bcf995d68d7dfcb3c7cfe466986dc4beaa402b262ca395b3e53c36f6cad"
  pprodMk := h "ce30fc0f4135e679cf3b16d0d667bd9df4e7a69dbb8177a29e5c75b48c4cec10"
  natRec := h "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992"
  natCasesOn := h "937374ed09b8b62f36ef75f06f1ee46dd487c7a9f3e74db919bde48bb76b2cc6"
  bitVec := h "90022ae4c5d52ad28acd80051dd41f27f51c9c4afbab1bb391773c19ef0dc1e9"
  bitVecToNat := h "fade2dbfb1d7f77c30c247d52df128bf516eedce01f817d363ce88da13cfac2b"
  bitVecOfNat := h "67160b97679306d2820445383a6d740e6fe9839c2545ea48680ff2a77b0be986"
  bitVecUlt := h "2f9c9c369045036d9a35ff7b38285dca3b976426c81a8f366fce1161b090d60d"
  decidableDecide := h "11157bc3898f06e3e6f2ca83411efd0d43b8846b57d2f6088e18f3447ddc3b28"
  ltLt := h "061c2658c76a68d90978859824993bbbe15dbf9b9968619325420e7c839b05c7"
  ofNatOfNat := h "cb84bffa6d7092a309630214af29d9ec4e35cd5e0003eb9cdf75ee484e24925b"
  unit := h "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb"
  punitSizeOf1 := h "523699b6e827b74a950d4718bdf5b13c193e3c7c371aaad4d635667be74b05fa"
  sizeOfSizeOf := h "ea81aee4a7d154faa8211a2594406dfdc7442020c0f29d2d0f79b4e62314da51"
  stringBack := h "b052e814120ea6299aecf4e9bb2b656d67c1f9537e8f0e9f16479c98a04fde93"
  stringLegacyBack := h "10af1decd5d2cd085adff8ae7fb44cfc5d22a89bbc40b81b809d3d556fda3e8f"
  stringUtf8ByteSize := h "4c086826cc679df3b6aa57a29f3d093a8a92d0de4edecef46a908d8398733dc0"
  stringAppend := h "0eae69f3f8b198d1ffac67b9e88d39526b1b039ff519cd87eec106f63974860c"
  stringDecEq := h "da7bb331e098f9bf5cdabcb9609a7e953dffc609ad9d90871a14c016c52a3011"

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

