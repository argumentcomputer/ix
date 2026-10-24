module

public import Ix.Tc.Env
public import Ix.PrimAddrs

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

