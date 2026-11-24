import IxCC.BigNat.Entry
import IxCC.BigNat.Proof.Entry
import IxCC.Src.Load
import IxCC.Src.Table.Word
import IxCC.Lam.Syntax
import IxCC.Lir.Syntax
import IxCC.Rt.Layout
import Lean.Data.Json
import Std.Data.HashMap

/-! # Pure-Lean `BigNat` Closure Freezer & Bootstrap Checker (`IxCC.BigNat.Bootstrap`)

Provides the Wave 3b bootstrap bridge for compiling `IxCC.BigNat.Entry` into the
linked Phase 4 slow-path runtime library:

1. **Five syntactic `LimbOps` word equation theorems** (`clz64_eqn`, `mulWide64_eqn`,
   `divWide64_eqn`, `addCarry64_eqn`, `subBorrow64_eqn`) matching `IxCC.Src.Table.limbEqnType`
   term-for-term (`Nat.add`, `Nat.mod`, raw `nat_lit` sizes, no notation), proved
   strictly under `[propext, Quot.sound]`.
2. **Slow-path runtime library interface** (`SlowPathOp`, `FrozenLibrary`, JSON codec)
   mapping all 19 arbitrary-precision `Nat` operations to their `IxCC.BigNat.Entry`
   roots, LIR symbol names, and content addresses.
3. **Zero-`natOverflow` bootstrap checkers:**
   * `checkSrcNoBigNatLit` — statically verifies that no runtime definition outside
     the 5 hardware-pinned `LimbOps` contains any `Nat` literal `≥ 2^63`;
   * `validateLimbEquations` — runs `Src.Table.checkLimb` across all 5 `LimbOps`;
   * `checkLirHasNoNatOverflow` — checks a compiled `Lir.Program` for `.fail .natOverflow`;
   * `verifyInternalIndices` — pure-Lean boundary/multi-limb checker confirming all
     internal `Nat` indices, limb counts, and `log2` outputs stay strictly `< 2^63`.
4. **Pure-Lean closure freezer** (`FreezeConfig`, `freezeClosure`) invoking
   `ix compile --consts ... --equations` (including all 5 `LimbOps` word equations),
   resolving all addresses into `Src.Pinned.LimbPins` and `FrozenLibrary`, and
   running full ingress + `checkLimb` + zero-`natOverflow` validation.

## References

* `IxCC/docs/bignum-design.md` (§Bootstrapping, §Linking, §Proof obligation).
* `IxCC/IxCC/Src/Table/Word.lean` (`limbEqnType`, `checkLimb`).
-/

set_option autoImplicit false

namespace IxCC.BigNat.Bootstrap

open Lean System
open IxCC.BigNat
open IxCC.BigNat.Entry
open IxCC.Ixon
open IxCC.Src

/-! ## Five Exact `LimbOps` Word Equation Theorems (`Src.Table.limbEqnType`)

Each statement matches `IxCC.Src.Table.limbEqnType` syntactically (applied `Nat.*`
constants, raw `nat_lit 18446744073709551616`, explicit `@Prod.mk` and `@cond`),
so `Src.Table.checkLimb` accepts them directly in any frozen `BigNat` closure. -/

/-- Exact syntactic word equation for `IxCC.BigNat.clz64` (`Src.Table.limbEqnType .clz64`). -/
theorem clz64_eqn (x : Nat) :
    IxCC.BigNat.clz64 (UInt64.ofNat x) =
      UInt64.ofNat
        (@cond Nat
          (Nat.beq (Nat.mod x (nat_lit 18446744073709551616)) (nat_lit 0))
          (nat_lit 64)
          (Nat.sub (nat_lit 63) (Nat.log2 (Nat.mod x (nat_lit 18446744073709551616))))) := by
  unfold IxCC.BigNat.clz64
  have hmod : (UInt64.ofNat x).toNat = x % 18446744073709551616 := UInt64.toNat_ofNat'
  by_cases hz : x % 18446744073709551616 = 0
  · have hu : UInt64.ofNat x = 0 := UInt64.toNat_inj.mp (by rw [hmod, hz]; rfl)
    have hbeq : Nat.beq (Nat.mod x (nat_lit 18446744073709551616)) (nat_lit 0) = true :=
      Nat.beq_eq.mpr hz
    simp only [hu, beq_self_eq_true, ↓reduceIte, hbeq, Bool.cond_true]
    rfl
  · have hu : UInt64.ofNat x ≠ 0 := by
      intro h0
      have := congrArg UInt64.toNat h0
      rw [hmod] at this
      exact hz this
    have hub : (UInt64.ofNat x == 0) = false := beq_false_of_ne hu
    have hbeq : Nat.beq (Nat.mod x (nat_lit 18446744073709551616)) (nat_lit 0) = false := by
      cases hc : Nat.beq (Nat.mod x (nat_lit 18446744073709551616)) (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc) hz
    simp only [hub, Bool.false_eq_true, ↓reduceIte, hbeq, Bool.cond_false, hmod]
    rfl

/-- Exact syntactic word equation for `IxCC.BigNat.mulWide64` (`Src.Table.limbEqnType .mulWide64`). -/
theorem mulWide64_eqn (x y : Nat) :
    IxCC.BigNat.mulWide64 (UInt64.ofNat x) (UInt64.ofNat y) =
      @Prod.mk UInt64 UInt64
        (UInt64.ofNat (Nat.mod (Nat.mul (Nat.mod x (nat_lit 18446744073709551616))
          (Nat.mod y (nat_lit 18446744073709551616))) (nat_lit 18446744073709551616)))
        (UInt64.ofNat (Nat.div (Nat.mul (Nat.mod x (nat_lit 18446744073709551616))
          (Nat.mod y (nat_lit 18446744073709551616))) (nat_lit 18446744073709551616))) := by
  unfold IxCC.BigNat.mulWide64
  simp only [UInt64.toNat_ofNat']
  rfl

/-- Exact syntactic word equation for `IxCC.BigNat.divWide64` (`Src.Table.limbEqnType .divWide64`). -/
theorem divWide64_eqn (hi lo d : Nat)
    (h : Nat.le (Nat.succ (Nat.mod hi (nat_lit 18446744073709551616)))
      (Nat.mod d (nat_lit 18446744073709551616))) :
    IxCC.BigNat.divWide64 (UInt64.ofNat hi) (UInt64.ofNat lo) (UInt64.ofNat d) h =
      @Prod.mk UInt64 UInt64
        (UInt64.ofNat (Nat.div (Nat.add (Nat.mul (Nat.mod hi (nat_lit 18446744073709551616))
          (nat_lit 18446744073709551616)) (Nat.mod lo (nat_lit 18446744073709551616)))
          (Nat.mod d (nat_lit 18446744073709551616))))
        (UInt64.ofNat (Nat.mod (Nat.add (Nat.mul (Nat.mod hi (nat_lit 18446744073709551616))
          (nat_lit 18446744073709551616)) (Nat.mod lo (nat_lit 18446744073709551616)))
          (Nat.mod d (nat_lit 18446744073709551616)))) := by
  unfold IxCC.BigNat.divWide64
  simp only [UInt64.toNat_ofNat']
  rfl

/-- Exact syntactic word equation for `IxCC.BigNat.addCarry64` (`Src.Table.limbEqnType .addCarry64`). -/
theorem addCarry64_eqn (x y : Nat) (c : Bool) :
    IxCC.BigNat.addCarry64 (UInt64.ofNat x) (UInt64.ofNat y) c =
      @Prod.mk UInt64 Bool
        (UInt64.ofNat (Nat.add (Nat.add (Nat.mod x (nat_lit 18446744073709551616))
          (Nat.mod y (nat_lit 18446744073709551616))) (Bool.toNat c)))
        (Nat.ble (nat_lit 18446744073709551616)
          (Nat.add (Nat.add (Nat.mod x (nat_lit 18446744073709551616))
            (Nat.mod y (nat_lit 18446744073709551616))) (Bool.toNat c))) := by
  unfold IxCC.BigNat.addCarry64
  simp only [UInt64.toNat_ofNat']
  congr 1
  by_cases h : (2 ^ 64 : Nat) ≤ x % 18446744073709551616 + y % 18446744073709551616 + c.toNat
  · have hble : Nat.ble (nat_lit 18446744073709551616)
        (Nat.add (Nat.add (Nat.mod x (nat_lit 18446744073709551616))
          (Nat.mod y (nat_lit 18446744073709551616))) (Bool.toNat c)) = true :=
      Nat.ble_eq.mpr h
    rw [hble]
    exact decide_eq_true h
  · have hble : Nat.ble (nat_lit 18446744073709551616)
        (Nat.add (Nat.add (Nat.mod x (nat_lit 18446744073709551616))
          (Nat.mod y (nat_lit 18446744073709551616))) (Bool.toNat c)) = false := by
      cases hb : Nat.ble (nat_lit 18446744073709551616)
          (Nat.add (Nat.add (Nat.mod x (nat_lit 18446744073709551616))
            (Nat.mod y (nat_lit 18446744073709551616))) (Bool.toNat c))
      · rfl
      · exact absurd (Nat.ble_eq.mp hb) h
    rw [hble]
    exact decide_eq_false h

/-- Exact syntactic word equation for `IxCC.BigNat.subBorrow64` (`Src.Table.limbEqnType .subBorrow64`). -/
theorem subBorrow64_eqn (x y : Nat) (c : Bool) :
    IxCC.BigNat.subBorrow64 (UInt64.ofNat x) (UInt64.ofNat y) c =
      @Prod.mk UInt64 Bool
        (UInt64.ofNat
          (@cond Nat
            (Nat.ble (Nat.succ (Nat.mod x (nat_lit 18446744073709551616)))
              (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c)))
            (Nat.sub (Nat.add (nat_lit 18446744073709551616) (Nat.mod x (nat_lit 18446744073709551616)))
              (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c)))
            (Nat.sub (Nat.mod x (nat_lit 18446744073709551616))
              (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c)))))
        (Nat.ble (Nat.succ (Nat.mod x (nat_lit 18446744073709551616)))
          (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c))) := by
  unfold IxCC.BigNat.subBorrow64
  simp only [UInt64.toNat_ofNat']
  by_cases h : x % 18446744073709551616 < y % 18446744073709551616 + c.toNat
  · have hble : Nat.ble (Nat.succ (Nat.mod x (nat_lit 18446744073709551616)))
        (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c)) = true :=
      Nat.ble_eq.mpr h
    simp only [h, ↓reduceIte, decide_true, hble, Bool.cond_true]
    rfl
  · have hble : Nat.ble (Nat.succ (Nat.mod x (nat_lit 18446744073709551616)))
        (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c)) = false := by
      cases hb : Nat.ble (Nat.succ (Nat.mod x (nat_lit 18446744073709551616)))
          (Nat.add (Nat.mod y (nat_lit 18446744073709551616)) (Bool.toNat c))
      · rfl
      · exact absurd (Nat.ble_eq.mp hb) h
    simp only [h, ↓reduceIte, decide_false, hble, Bool.cond_false]
    rfl

/-! ## Slow-Path Runtime Library Interface -/

/-- Every arbitrary-precision `Nat` slow-path operation exported by the frozen
`IxCC.BigNat.Entry` runtime library. -/
inductive SlowPathOp where
  | add | sub | pred | mul | div | mod | pow | gcd
  | beq | ble | blt
  | land | lor | xor
  | shiftLeft | shiftRight
  | log2 | toDecimal | ofDecimal
  deriving DecidableEq, BEq, Repr, Inhabited

namespace SlowPathOp

def all : List SlowPathOp :=
  [ .add, .sub, .pred, .mul, .div, .mod, .pow, .gcd
  , .beq, .ble, .blt
  , .land, .lor, .xor
  , .shiftLeft, .shiftRight
  , .log2, .toDecimal, .ofDecimal ]

/-- The 17 pure-`Array UInt64` numeric slow-path operations (the 16 `Lam.Prim` `Nat`
ops plus `log2`, requiring zero `String` / `Char` runtime dependencies). -/
def numericOps : List SlowPathOp :=
  [ .add, .sub, .pred, .mul, .div, .mod, .pow, .gcd
  , .beq, .ble, .blt
  , .land, .lor, .xor
  , .shiftLeft, .shiftRight
  , .log2 ]

/-- Short canonical key name (used in manifests and diagnostics). -/
def key : SlowPathOp → String
  | .add => "add" | .sub => "sub" | .pred => "pred" | .mul => "mul"
  | .div => "div" | .mod => "mod" | .pow => "pow" | .gcd => "gcd"
  | .beq => "beq" | .ble => "ble" | .blt => "blt"
  | .land => "land" | .lor => "lor" | .xor => "xor"
  | .shiftLeft => "shiftLeft" | .shiftRight => "shiftRight"
  | .log2 => "log2" | .toDecimal => "toDecimal" | .ofDecimal => "ofDecimal"

def ofKey? (s : String) : Option SlowPathOp :=
  all.find? (·.key == s)

/-- Exact Lean constant name in `IxCC.BigNat.Entry`. -/
def leanName : SlowPathOp → String
  | .add => "IxCC.BigNat.Entry.add"
  | .sub => "IxCC.BigNat.Entry.sub"
  | .pred => "IxCC.BigNat.Entry.pred"
  | .mul => "IxCC.BigNat.Entry.mul"
  | .div => "IxCC.BigNat.Entry.div"
  | .mod => "IxCC.BigNat.Entry.mod"
  | .pow => "IxCC.BigNat.Entry.pow?"
  | .gcd => "IxCC.BigNat.Entry.gcd"
  | .beq => "IxCC.BigNat.Entry.beq"
  | .ble => "IxCC.BigNat.Entry.ble"
  | .blt => "IxCC.BigNat.Entry.blt"
  | .land => "IxCC.BigNat.Entry.land"
  | .lor => "IxCC.BigNat.Entry.lor"
  | .xor => "IxCC.BigNat.Entry.xor"
  | .shiftLeft => "IxCC.BigNat.Entry.shiftLeft?"
  | .shiftRight => "IxCC.BigNat.Entry.shiftRightSlow"
  | .log2 => "IxCC.BigNat.Entry.log2Slow"
  | .toDecimal => "IxCC.BigNat.Entry.toDecimal"
  | .ofDecimal => "IxCC.BigNat.Entry.ofDecimal"

/-- Canonical LIR runtime symbol name linked by Wave 3b lowering. -/
def lirSymbol : SlowPathOp → String
  | .add => "rt_bignat_add"
  | .sub => "rt_bignat_sub"
  | .pred => "rt_bignat_pred"
  | .mul => "rt_bignat_mul"
  | .div => "rt_bignat_div"
  | .mod => "rt_bignat_mod"
  | .pow => "rt_bignat_pow"
  | .gcd => "rt_bignat_gcd"
  | .beq => "rt_bignat_beq"
  | .ble => "rt_bignat_ble"
  | .blt => "rt_bignat_blt"
  | .land => "rt_bignat_land"
  | .lor => "rt_bignat_lor"
  | .xor => "rt_bignat_xor"
  | .shiftLeft => "rt_bignat_shl"
  | .shiftRight => "rt_bignat_shr"
  | .log2 => "rt_bignat_log2"
  | .toDecimal => "rt_bignat_toDecimal"
  | .ofDecimal => "rt_bignat_ofDecimal"

def arity : SlowPathOp → Nat
  | .pred | .log2 | .toDecimal | .ofDecimal => 1
  | _ => 2

/-- Corresponding `Lam.Prim`, for the 16 `Nat` primitives lowered by `Rt.BigNat.Dispatch`. -/
def lamPrim? : SlowPathOp → Option Lam.Prim
  | .add => some .natAdd
  | .sub => some .natSub
  | .pred => some .natPred
  | .mul => some .natMul
  | .div => some .natDiv
  | .mod => some .natMod
  | .pow => some .natPow
  | .gcd => some .natGcd
  | .beq => some .natBeq
  | .ble => some .natBle
  | .blt => some .natBlt
  | .land => some .natLand
  | .lor => some .natLor
  | .xor => some .natXor
  | .shiftLeft => some .natShl
  | .shiftRight => some .natShr
  | .log2 | .toDecimal | .ofDecimal => none

end SlowPathOp

/-- Mapping of each of the 5 `LimbOps` to its Lean constant name and its exact
`Src.Table.limbEqnType` theorem name in `IxCC.BigNat.Bootstrap`. -/
def limbEquationSpecs : List (Src.LimbOp × String × String) :=
  [ (.clz64,       "IxCC.BigNat.clz64",       "IxCC.BigNat.Bootstrap.clz64_eqn")
  , (.mulWide64,   "IxCC.BigNat.mulWide64",   "IxCC.BigNat.Bootstrap.mulWide64_eqn")
  , (.divWide64,   "IxCC.BigNat.divWide64",   "IxCC.BigNat.Bootstrap.divWide64_eqn")
  , (.addCarry64,  "IxCC.BigNat.addCarry64",  "IxCC.BigNat.Bootstrap.addCarry64_eqn")
  , (.subBorrow64, "IxCC.BigNat.subBorrow64", "IxCC.BigNat.Bootstrap.subBorrow64_eqn")
  ]

/-- Auxiliary `Init` constants whose addresses populate `Src.Pinned.LimbPins`. -/
def auxPinNames : List String :=
  ["Prod", "Prod.mk", "Nat.log2", "Bool.toNat", "cond"]

/-- Complete `--consts` root list frozen by `ix compile --consts ... --equations`:
all `IxCC.BigNat.Entry` entrypoints plus all 5 `LimbOps` and their 5 equation theorems. -/
def allFreezeConsts (includeLimbEqns : Bool := true) : List String :=
  let entries := SlowPathOp.all.map SlowPathOp.leanName
  let limbDefs := limbEquationSpecs.map (·.2.1)
  let limbThms := if includeLimbEqns then limbEquationSpecs.map (·.2.2) else []
  (entries ++ limbDefs ++ limbThms).eraseDups

/-! ## Frozen Slow-Path Runtime Library Artifact -/

/-- Hex encoding of raw bytes (lowercase). -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def bytesToHex (bs : ByteArray) : String := Id.run do
  let mut cs : Array Char := Array.mkEmpty (2 * bs.size)
  for i in [:bs.size] do
    let b := bs[i]!.toNat
    cs := cs.push (hexDigit (b / 16))
    cs := cs.push (hexDigit (b % 16))
  return String.ofList cs.toList

private def fromHexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexToBytes? (s : String) : Option ByteArray :=
  go s.toList ByteArray.empty
where
  go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | h :: l :: rest, acc => do
      let hi ← fromHexDigit h
      let lo ← fromHexDigit l
      go rest (acc.push (UInt8.ofNat (16 * hi + lo)))
    | [_], _ => none

def hexToAddr? (s : String) : Option Ixon.Address := do
  let bs ← hexToBytes? s
  if h : bs.size = 32 then some ⟨bs, h⟩ else none

/-- Frozen `IxCC.BigNat.Entry` runtime closure ready for Wave 3b compilation and linking. -/
structure FrozenLibrary where
  /-- Anonymous Ixon v4 closure bytes of `IxCC.BigNat.Entry` + all 5 `LimbOps` equations. -/
  closureBytes : ByteArray
  /-- Address-resolved `ixcc/k1-equations/1` sidecar JSON. -/
  equationsJson : Json
  /-- Resolved 256-bit addresses of the 5 hardware `LimbOps` + `Prod`/`Nat.log2`/`Bool.toNat`/`cond`. -/
  limbPins : Pinned.LimbPins
  /-- Content addresses of all slow-path entrypoints in `closureBytes`. -/
  entryAddrs : List (SlowPathOp × Ixon.Address)
  /-- Content addresses of the 5 `LimbOps` word equation theorems in `closureBytes`. -/
  limbEqnAddrs : List (Src.LimbOp × Ixon.Address)
  /-- Version string of the `ix` producer used to freeze this closure. -/
  ixVersion : String := ""
  deriving Inhabited

namespace FrozenLibrary

def entryAddr? (lib : FrozenLibrary) (op : SlowPathOp) : Option Ixon.Address :=
  (lib.entryAddrs.find? (·.1 == op)).map (·.2)

def hasAllEntries (lib : FrozenLibrary) : Bool :=
  SlowPathOp.all.all fun op => (lib.entryAddr? op).isSome

def hasAllLimbPins (lib : FrozenLibrary) : Bool :=
  Src.LimbOp.all.all (fun op => (lib.limbPins.op? op).isSome) &&
    lib.limbPins.prodType.isSome &&
    lib.limbPins.prodMk.isSome &&
    lib.limbPins.natLog2.isSome &&
    lib.limbPins.boolToNat.isSome &&
    lib.limbPins.cond.isSome &&
    Src.LimbOp.all.all (fun op => (lib.limbEqnAddrs.find? (·.1 == op)).isSome)

private def limbOpKey : Src.LimbOp → String
  | .clz64 => "clz64"
  | .mulWide64 => "mulWide64"
  | .divWide64 => "divWide64"
  | .addCarry64 => "addCarry64"
  | .subBorrow64 => "subBorrow64"

private def limbOpOfKey? : String → Option Src.LimbOp
  | "clz64" => some .clz64
  | "mulWide64" => some .mulWide64
  | "divWide64" => some .divWide64
  | "addCarry64" => some .addCarry64
  | "subBorrow64" => some .subBorrow64
  | _ => none

private def natAddrHex (n : Nat) : String := toString (Pinned.addrOfNat n)

private def optNatAddrJson : Option Nat → Json
  | some n => Json.str (natAddrHex n)
  | none => Json.null

private def parseOptNatAddr (j : Json) : Except String (Option Nat) :=
  match j with
  | .null => pure none
  | .str s =>
    match hexToAddr? s with
    | some a => pure (some (Pinned.addrNat a))
    | none => throw s!"bootstrap: invalid 32-byte hex address: {s}"
  | _ => throw "bootstrap: expected hex string or null for pinned address"

/-- Serialize `FrozenLibrary` metadata + embedded closure to JSON (`ixcc/bignat-bootstrap/1`). -/
def toJson (lib : FrozenLibrary) : Json :=
  let entriesJ := Json.mkObj (lib.entryAddrs.map fun (op, a) => (op.key, Json.str (toString a)))
  let limbOpsJ := Json.mkObj (lib.limbPins.ops.map fun (op, n) => (limbOpKey op, Json.str (natAddrHex n)))
  let limbEqnsJ := Json.mkObj (lib.limbEqnAddrs.map fun (op, a) => (limbOpKey op, Json.str (toString a)))
  let pinsJ := Json.mkObj
    [ ("ops", limbOpsJ)
    , ("prodType", optNatAddrJson lib.limbPins.prodType)
    , ("prodMk", optNatAddrJson lib.limbPins.prodMk)
    , ("natLog2", optNatAddrJson lib.limbPins.natLog2)
    , ("boolToNat", optNatAddrJson lib.limbPins.boolToNat)
    , ("cond", optNatAddrJson lib.limbPins.cond)
    ]
  Json.mkObj
    [ ("format", Json.str "ixcc/bignat-bootstrap/1")
    , ("ixVersion", Json.str lib.ixVersion)
    , ("closureHex", Json.str (bytesToHex lib.closureBytes))
    , ("equations", lib.equationsJson)
    , ("limbPins", pinsJ)
    , ("entries", entriesJ)
    , ("limbEquations", limbEqnsJ)
    ]

/-- Deserialize `FrozenLibrary` from `ixcc/bignat-bootstrap/1` JSON. -/
def ofJson (j : Json) : Except String FrozenLibrary := do
  let fmt ← (← j.getObjVal? "format").getStr?
  unless fmt == "ixcc/bignat-bootstrap/1" do
    throw s!"bootstrap: unexpected format '{fmt}'"
  let ixVersion ← (← j.getObjVal? "ixVersion").getStr?
  let closureHex ← (← j.getObjVal? "closureHex").getStr?
  let some closureBytes := hexToBytes? closureHex
    | throw "bootstrap: invalid hex in closureHex"
  let equationsJson ← j.getObjVal? "equations"
  let pinsJ ← j.getObjVal? "limbPins"
  let opsJ ← pinsJ.getObjVal? "ops"
  let opsMap ← opsJ.getObj?
  let mut ops : List (Src.LimbOp × Nat) := []
  for (k, v) in opsMap.toList do
    let some lop := limbOpOfKey? k | throw s!"bootstrap: unknown limb op '{k}'"
    let s ← v.getStr?
    let some a := hexToAddr? s | throw s!"bootstrap: invalid address for limb op '{k}'"
    ops := ops ++ [(lop, Pinned.addrNat a)]
  let prodType ← parseOptNatAddr (← pinsJ.getObjVal? "prodType")
  let prodMk ← parseOptNatAddr (← pinsJ.getObjVal? "prodMk")
  let natLog2 ← parseOptNatAddr (← pinsJ.getObjVal? "natLog2")
  let boolToNat ← parseOptNatAddr (← pinsJ.getObjVal? "boolToNat")
  let cond ← parseOptNatAddr (← pinsJ.getObjVal? "cond")
  let entriesMap ← (← j.getObjVal? "entries").getObj?
  let mut entryAddrs : List (SlowPathOp × Ixon.Address) := []
  for (k, v) in entriesMap.toList do
    let some sop := SlowPathOp.ofKey? k | throw s!"bootstrap: unknown entry op '{k}'"
    let s ← v.getStr?
    let some a := hexToAddr? s | throw s!"bootstrap: invalid address for entry '{k}'"
    entryAddrs := entryAddrs ++ [(sop, a)]
  let eqnsMap ← (← j.getObjVal? "limbEquations").getObj?
  let mut limbEqnAddrs : List (Src.LimbOp × Ixon.Address) := []
  for (k, v) in eqnsMap.toList do
    let some lop := limbOpOfKey? k | throw s!"bootstrap: unknown limb equation '{k}'"
    let s ← v.getStr?
    let some a := hexToAddr? s | throw s!"bootstrap: invalid address for limb equation '{k}'"
    limbEqnAddrs := limbEqnAddrs ++ [(lop, a)]
  pure
    { closureBytes
    , equationsJson
    , limbPins := { ops, prodType, prodMk, natLog2, boolToNat, cond }
    , entryAddrs
    , limbEqnAddrs
    , ixVersion }

end FrozenLibrary

/-! ## Zero-`natOverflow` Static & Dynamic Bootstrap Verification -/

/-- Collect every runtime-relevant `Nat` literal `≥ 2^63` (`Rt.natLimit`) in a `Src.Term`.
Skips irrelevant (`type`/`proof .always`) arguments, binder domains, and `let` types. -/
def termBigNatLits : Src.Term → List Nat
  | .natLit n => if n ≥ Rt.natLimit then [n] else []
  | .app f a _ r => termBigNatLits f ++ if r.alwaysIrr then [] else termBigNatLits a
  | .lam _ _ body => termBigNatLits body
  | .letE _ _ r _ val body => (if r.alwaysIrr then [] else termBigNatLits val) ++ termBigNatLits body
  | .proj _ _ e => termBigNatLits e
  | .var _ | .sort _ | .const _ _ | .pi _ _ _ | .strLit _ => []

/-- Static bootstrap check: verify that no non-theorem runtime definition in `p`
outside the 5 hardware-pinned `LimbOps` and table-resolved word/prim/csimp operations
contains any `Nat` literal `≥ 2^63`. -/
def checkSrcNoBigNatLit (p : Src.Program) (pins : Pinned.LimbPins)
    (nameOf : Ixon.Address → Option String := fun _ => none) : Except String Unit := do
  let mut bad : List (CId × String × List Nat) := []
  for c in List.range p.size do
    if (Pinned.limbAt? pins (p.addr c)).isSome then
      continue
    if (p.table.resolveOf c).isSome then
      continue
    match p.decl? c with
    | some (.defn .defn _ _ _ val) =>
      let nm := (nameOf (p.addr c)).getD (p.short c)
      -- `UInt64.size` / `USize.size` are purely type-level `Fin` moduli erased by `Lam.erase`
      if nm == "UInt64.size" || nm == "USize.size" then
        continue
      let bigs := termBigNatLits val
      if !bigs.isEmpty then
        bad := bad ++ [(c, nm, bigs)]
    | _ => pure ()
  if !bad.isEmpty then
    let desc := ", ".intercalate (bad.map fun (c, nm, ns) => s!"cid {c} ({nm}): {ns}")
    throw s!"bootstrap: runtime definition(s) contain Nat literals ≥ 2^63: {desc}"

/-- Validate all 5 `LimbOps` word equations in `p` via `Src.Table.checkLimb`. -/
def validateLimbEquations (cfg : Table.Config) (p : Src.Program) (pins : Pinned.LimbPins)
    (eqns : List (Src.LimbOp × Ixon.Address)) : Except String Unit := do
  for op in Src.LimbOp.all do
    let some opAddr := pins.op? op
      | throw s!"bootstrap: missing LimbPin for {op.leanName}"
    let some fId := p.lookup (Pinned.addrOfNat opAddr)
      | throw s!"bootstrap: {op.leanName} absent from frozen closure"
    let some thmAddr := (eqns.find? (·.1 == op)).map (·.2)
      | throw s!"bootstrap: missing equation theorem address for {op.leanName}"
    let some thmId := p.lookup thmAddr
      | throw s!"bootstrap: equation theorem for {op.leanName} absent from frozen closure"
    Table.checkLimb cfg p pins fId op thmId

/-- Scan a compiled `Lir.Program` and report any `(funId, blockLabel)` whose terminator
is `.fail .natOverflow`. An empty list proves syntactic absence of `natOverflow` exits. -/
def checkLirHasNoNatOverflow (lp : Lir.Program) : List (Lir.FunId × Lir.Label) :=
  lp.funcs.toList.zipIdx.flatMap fun (f, fi) =>
    f.blocks.toList.zipIdx.filterMap fun (b, bi) =>
      if b.term == .fail .natOverflow then some (fi, bi) else none

/-- Pure-Lean executable bootstrap index verifier: exercises every `IxCC.BigNat.Entry`
operation across boundary and multi-limb values (`0`, `1`, `2^63 - 1`, `2^63`, `2^64 - 1`,
`2^64`, `10^19`, `2^128`, `2^256`) and verifies:
1. exact mathematical agreement with `Nat`,
2. canonical normal form (`isCanonical`), and
3. every internal `Nat` index, limb count, and `log2` value stays strictly `< 2^63`
   (zero `natOverflow`). -/
def verifyInternalIndices : Except String Nat := do
  let samples : List Nat :=
    [ 0, 1, 2, 3, 7, 63, 64
    , 2 ^ 63 - 2, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1
    , 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1
    , 10 ^ 19
    , 2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1
    , 2 ^ 256 - 1, 2 ^ 256 ]
  let checkLimb := fun (label : String) (s : SlowNat) (expected : Nat) => do
    unless isCanonical s do
      throw s!"bootstrap verify ({label}): non-canonical result for {expected}"
    unless s.val == expected do
      throw s!"bootstrap verify ({label}): got {s.val}, expected {expected}"
    unless s.limbCount < Rt.natLimit do
      throw s!"bootstrap verify ({label}): limbCount {s.limbCount} ≥ 2^63"
  let mut checks : Nat := 0
  for a in samples do
    let sa := SlowNat.ofNat a
    checkLimb s!"pred {a}" (Entry.pred sa) (a - 1)
    let lg := Entry.log2 sa
    unless lg == Nat.log2 a && lg < Rt.natLimit do
      throw s!"bootstrap verify (log2 {a}): got {lg}, expected {Nat.log2 a}"
    checkLimb s!"log2Slow {a}" (Entry.log2Slow sa) (Nat.log2 a)
    let dec := Entry.toDecimal sa
    match Entry.ofDecimal dec with
    | some parsed => checkLimb s!"decimal {a}" parsed a
    | none => throw s!"bootstrap verify (ofDecimal {dec}): failed"
    checks := checks + 4
    for b in samples do
      let sb := SlowNat.ofNat b
      checkLimb s!"add {a} {b}" (Entry.add sa sb) (a + b)
      checkLimb s!"sub {a} {b}" (Entry.sub sa sb) (a - b)
      checkLimb s!"mul {a} {b}" (Entry.mul sa sb) (a * b)
      checkLimb s!"div {a} {b}" (Entry.div sa sb) (a / b)
      checkLimb s!"mod {a} {b}" (Entry.mod sa sb) (a % b)
      checkLimb s!"gcd {a} {b}" (Entry.gcd sa sb) (Nat.gcd a b)
      checkLimb s!"land {a} {b}" (Entry.land sa sb) (a &&& b)
      checkLimb s!"lor {a} {b}" (Entry.lor sa sb) (a ||| b)
      checkLimb s!"xor {a} {b}" (Entry.xor sa sb) (a ^^^ b)
      checkLimb s!"shr {a} {b}" (Entry.shiftRightSlow sa sb) (if b ≥ 512 then 0 else a / 2 ^ b)
      unless Entry.beq sa sb == (a == b) do
        throw s!"bootstrap verify (beq {a} {b}): mismatch"
      unless Entry.ble sa sb == decide (a ≤ b) do
        throw s!"bootstrap verify (ble {a} {b}): mismatch"
      unless Entry.blt sa sb == decide (a < b) do
        throw s!"bootstrap verify (blt {a} {b}): mismatch"
      checks := checks + 13
    for s in [0, 1, 7, 63, 64, 65, 128] do
      checkLimb s!"shl {a} {s}" (Entry.shiftLeft sa s) (a * 2 ^ s)
      match Entry.shiftLeft? sa (SlowNat.ofNat s) with
      | some r => checkLimb s!"shl? {a} {s}" r (a * 2 ^ s)
      | none => throw s!"bootstrap verify (shl? {a} {s}): unexpected none"
      checks := checks + 2
    for e in [0, 1, 2, 3, 5] do
      checkLimb s!"pow {a} {e}" (Entry.pow sa e) (a ^ e)
      match Entry.pow? sa (SlowNat.ofNat e) with
      | some r => checkLimb s!"pow? {a} {e}" r (a ^ e)
      | none => throw s!"bootstrap verify (pow? {a} {e}): unexpected none"
      checks := checks + 2
  pure checks

/-! ## Pure-Lean Closure Freezer (`ix compile --consts ... --equations`) -/

/-- Configuration for freezing `IxCC.BigNat.Entry` + all 5 `LimbOps` word equations
via `ix compile --no-build --consts ... --equations --equations-out ... --word-equations`. -/
structure FreezeConfig where
  /-- Path to the pinned `ix` binary. -/
  ix : FilePath
  /-- Path to the Lean module root (`IxCC/BigNat/Bootstrap.lean` or `IxCC/BigNat/Entry.lean`). -/
  sourceFile : FilePath := "IxCC/BigNat/Bootstrap.lean"
  /-- Output directory for frozen `.ixe`, `.equations.json`, and `bignat-bootstrap.json`. -/
  outDir : FilePath
  /-- Optional directories prepended to `PATH` when invoking `ix`. -/
  ixPath : List String := []
  /-- Optional directories prepended to `LEAN_PATH` when invoking `ix`. -/
  leanPath : List String := []
  /-- Working directory for `ix` (typically the `IxCC` package root). -/
  cwd : Option FilePath := none
  /-- Include all 5 `LimbOps` equation theorems in `--consts`. -/
  includeLimbEqns : Bool := true
  /-- Subset of slow-path operations to freeze (defaults to all 19). -/
  ops : List SlowPathOp := SlowPathOp.all
  deriving Inhabited

/-- Seed `--consts` list for a given `FreezeConfig`. -/
def freezeConstsOf (cfg : FreezeConfig) : List String :=
  let entries := cfg.ops.map SlowPathOp.leanName
  let limbDefs := limbEquationSpecs.map (·.2.1)
  let limbThms := if cfg.includeLimbEqns then limbEquationSpecs.map (·.2.2) else []
  (entries ++ limbDefs ++ limbThms).eraseDups

/-- Exact `ix compile` arguments for the anonymous frozen closure + equations sidecar. -/
def compileAnonArgs (cfg : FreezeConfig) (anonIxe anonEqs : FilePath) : Array String :=
  #[ "compile"
   , "--no-build"
   , "--anon"
   , "--consts", ",".intercalate (freezeConstsOf cfg)
   , "--equations"
   , "--equations-out", anonEqs.toString
   , "--word-equations"
   , "--out", anonIxe.toString
   , cfg.sourceFile.toString ]

/-- Exact `ix compile` arguments for the named twin closure used for in-memory §4/§5 resolution. -/
def compileNamedArgs (cfg : FreezeConfig) (namedIxe namedEqs : FilePath) : Array String :=
  #[ "compile"
   , "--no-build"
   , "--consts", ",".intercalate (freezeConstsOf cfg)
   , "--equations"
   , "--equations-out", namedEqs.toString
   , "--word-equations"
   , "--out", namedIxe.toString
   , cfg.sourceFile.toString ]

/-- Exact `ix addr-of` arguments resolving a Lean constant name against the named twin. -/
def addrOfArgs (namedIxe : FilePath) (constName : String) : Array String :=
  #["addr-of", namedIxe.toString, constName]

private def addrBytesLt (a b : Ixon.Address) : Bool := Id.run do
  let n := min a.hash.size b.hash.size
  for i in [:n] do
    let x := a.hash.get! i
    let y := b.hash.get! i
    if x != y then return x < y
  return a.hash.size < b.hash.size

private def natFromBytesLE (bs : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut shift : Nat := 0
  for i in [:bs.size] do
    acc := acc ||| ((bs.get! i).toNat <<< shift)
    shift := shift + 8
  return acc

/-- Decode Section 4 (names) and Section 5 (named → §2 constant rank) directly from a named
`.ixe` envelope in memory (< 5ms, zero `ix addr-of` subprocess spawns). -/
def extractNamedMap (bytes : ByteArray) : Except String (Std.HashMap String String) := do
  let env ← Ixon.V3.decodeAnonymousEnv bytes
  let constOrder : Array Ixon.Address :=
    (env.consts.toArray.map (·.1)).qsort addrBytesLt
  let parseMeta : _root_.Ixon.GetM (Std.HashMap String String) := do
    let numNames := (← _root_.Ixon.getTagN 0).value.toNat
    let mut namesLookup : Std.HashMap ByteArray String := {}
    let mut nameRev : Array String := Array.mkEmpty numNames
    for _ in [:numNames] do
      let addrBytes ← _root_.Ixon.getBytes 32
      let tag ← _root_.Ixon.getU8
      let nm ← match tag with
        | 0 => pure ""
        | 1 =>
          let pBytes ← _root_.Ixon.getBytes 32
          let len := (← _root_.Ixon.getTagN 0).value.toNat
          let sBytes ← _root_.Ixon.getBytes len
          let some s := String.fromUTF8? sBytes | throw "§4 invalid UTF-8 name"
          let parent := namesLookup.getD pBytes ""
          pure (if parent.isEmpty then s else s!"{parent}.{s}")
        | 2 =>
          let pBytes ← _root_.Ixon.getBytes 32
          let len := (← _root_.Ixon.getTagN 0).value.toNat
          let nBytes ← _root_.Ixon.getBytes len
          let n := natFromBytesLE nBytes
          let parent := namesLookup.getD pBytes ""
          pure (if parent.isEmpty then toString n else s!"{parent}.{n}")
        | t => throw s!"§4 invalid name component tag {t}"
      nameRev := nameRev.push nm
      namesLookup := namesLookup.insert addrBytes nm
    let numNamed := (← _root_.Ixon.getTagN 0).value.toNat
    let mut out : Std.HashMap String String := Std.HashMap.emptyWithCapacity numNamed
    for _ in [:numNamed] do
      let nameIdx := (← _root_.Ixon.getTagN 0).value.toNat
      let constRank := (← _root_.Ixon.getTagN 0).value.toNat
      let _hint ← _root_.Ixon.getTagN 0
      let metaLen := (← _root_.Ixon.getTagN 0).value.toNat
      let _skip ← _root_.Ixon.getBytes metaLen
      if let (some nm, some addr) := (nameRev[nameIdx]?, constOrder[constRank]?) then
        out := out.insert nm (bytesToHex addr.hash)
    return out
  match parseMeta.run { bytes := env.metadata, idx := 0 } with
  | .ok m _ => .ok m
  | .error e _ => .error s!"extractNamedMap: {e}"

/-- Convert an `ix/compile-equations/2` JSON sidecar into an address-resolved
`ixcc/k1-equations/1` JSON sidecar using `namedMap` from `extractNamedMap`. -/
def convertIxEquations (sourceName : String) (rootNames : List String)
    (namedMap : Std.HashMap String String) (rawJson : Json) : Except String Json := do
  let fmt ← (rawJson.getObjValAs? String "format").mapError fun e =>
    s!"bootstrap: equations json missing format: {e}"
  unless fmt == "ix/compile-equations/2" do
    throw s!"bootstrap: unexpected ix equations format '{fmt}'"
  let eqArr ← (rawJson.getObjValAs? (Array Json) "equations").mapError fun e =>
    s!"bootstrap: equations json missing equations: {e}"
  let thmArr := match rawJson.getObjValAs? (Array Json) "theorems" with
    | .ok arr => arr
    | .error _ => #[]
  let resolve (nm : String) : Except String String :=
    match namedMap[nm]? with
    | some a => .ok a
    | none => .error s!"bootstrap: name '{nm}' absent from .ixe §5 table"
  let mut rootRows : Array Json := #[]
  for r in rootNames do
    let ra ← resolve r
    rootRows := rootRows.push (Json.mkObj [("name", .str r), ("address", .str ra)])
  let mut eqRows : Array Json := #[]
  for p in eqArr do
    let d ← (p.getObjValAs? String "definition").mapError (s!"bootstrap: eq missing definition: {·}")
    let e ← (p.getObjValAs? String "equation").mapError (s!"bootstrap: eq missing equation: {·}")
    let da ← resolve d
    let ea ← resolve e
    eqRows := eqRows.push (Json.mkObj [
      ("definition", .str d), ("definition_address", .str da),
      ("equation", .str e), ("equation_address", .str ea)
    ])
  let mut thmRows : Array Json := #[]
  for t in thmArr do
    let k ← (t.getObjValAs? String "kind").mapError (s!"bootstrap: thm missing kind: {·}")
    let s ← (t.getObjValAs? String "subject").mapError (s!"bootstrap: thm missing subject: {·}")
    let n ← (t.getObjValAs? String "theorem").mapError (s!"bootstrap: thm missing theorem: {·}")
    let sa ← resolve s
    let na ← resolve n
    thmRows := thmRows.push (Json.mkObj [
      ("kind", .str k), ("subject", .str s), ("subject_address", .str sa),
      ("theorem", .str n), ("theorem_address", .str na)
    ])
  let fields : List (String × Json) :=
    [ ("format", .str "ixcc/k1-equations/1")
    , ("source", .str sourceName)
    , ("roots", .arr rootRows)
    , ("equations", .arr eqRows) ] ++
    (if thmRows.isEmpty then [] else [("theorems", .arr thmRows)]) ++
    [ ("failures", .arr #[]) ]
  pure (Json.mkObj fields)

private def runCmd (cmd : String) (args : Array String) (cwd : Option FilePath)
    (extraPath extraLeanPath : List String) : IO String := do
  let mut env : Array (String × Option String) := #[]
  if !extraPath.isEmpty then
    let old := (← IO.getEnv "PATH").getD ""
    env := env.push ("PATH", some (":".intercalate (extraPath ++ [old])))
  if !extraLeanPath.isEmpty then
    let old := (← IO.getEnv "LEAN_PATH").getD ""
    let val := if old.isEmpty then ":".intercalate extraLeanPath
               else ":".intercalate (extraLeanPath ++ [old])
    env := env.push ("LEAN_PATH", some val)
  let out ← IO.Process.output { cmd, args, cwd, env }
  unless out.exitCode == 0 do
    throw (IO.userError s!"bootstrap: `{cmd} {" ".intercalate args.toList}` exited {out.exitCode}\n{out.stdout}\n{out.stderr}")
  return out.stdout

private def resolveFromMap (namedMap : Std.HashMap String String) (name : String) :
    Except String Ixon.Address := do
  let some hex := namedMap[name]?
    | throw s!"bootstrap: '{name}' absent from .ixe §5 name table"
  let some a := hexToAddr? hex
    | throw s!"bootstrap: invalid hex address for '{name}': {hex}"
  pure a

/-- Freeze `IxCC.BigNat.Entry` + all 5 `LimbOps` word equations with `ix compile`,
resolve all entrypoint and `LimbPins` addresses in memory from the `.ixe` §4/§5 tables,
convert `ix/compile-equations/2` to `ixcc/k1-equations/1`, validate ingress +
`Src.Table.checkLimb` + `checkSrcNoBigNatLit`, write the frozen library JSON, and return
`FrozenLibrary`. -/
def freezeClosure (cfg : FreezeConfig) : IO FrozenLibrary := do
  IO.FS.createDirAll cfg.outDir
  let namedIxe := cfg.outDir / "bignat-entry.named.ixe"
  let namedEqs := cfg.outDir / "bignat-entry.named.equations.json"
  let ixVersion := (← runCmd cfg.ix.toString #["--version"] cfg.cwd cfg.ixPath cfg.leanPath).trimAscii.toString
  let _ ← runCmd cfg.ix.toString (compileNamedArgs cfg namedIxe namedEqs) cfg.cwd cfg.ixPath cfg.leanPath
  let closureBytes ← IO.FS.readBinFile namedIxe
  let rawEqJson ← IO.ofExcept (Json.parse (← IO.FS.readFile namedEqs))
  let namedMap ← IO.ofExcept (extractNamedMap closureBytes)
  let rootNames := cfg.ops.map SlowPathOp.leanName
  let equationsJson ← IO.ofExcept (convertIxEquations cfg.sourceFile.toString rootNames namedMap rawEqJson)
  let mut entryAddrs : List (SlowPathOp × Ixon.Address) := []
  for op in cfg.ops do
    let a ← IO.ofExcept (resolveFromMap namedMap op.leanName)
    entryAddrs := entryAddrs ++ [(op, a)]
  let mut limbOps : List (Src.LimbOp × Nat) := []
  let mut limbEqnAddrs : List (Src.LimbOp × Ixon.Address) := []
  for (op, defName, thmName) in limbEquationSpecs do
    let defAddr ← IO.ofExcept (resolveFromMap namedMap defName)
    limbOps := limbOps ++ [(op, Pinned.addrNat defAddr)]
    if cfg.includeLimbEqns then
      let thmAddr ← IO.ofExcept (resolveFromMap namedMap thmName)
      limbEqnAddrs := limbEqnAddrs ++ [(op, thmAddr)]
  let prodType? := (resolveFromMap namedMap "Prod").toOption.map Pinned.addrNat
  let prodMk? := (resolveFromMap namedMap "Prod.mk").toOption.map Pinned.addrNat
  let natLog2? := (resolveFromMap namedMap "Nat.log2").toOption.map Pinned.addrNat
  let boolToNat? := (resolveFromMap namedMap "Bool.toNat").toOption.map Pinned.addrNat
  let cond? := (resolveFromMap namedMap "cond").toOption.map Pinned.addrNat
  let limbPins : Pinned.LimbPins :=
    { ops := limbOps
    , prodType := prodType?
    , prodMk := prodMk?
    , natLog2 := natLog2?
    , boolToNat := boolToNat?
    , cond := cond? }
  -- Validate the frozen closure through IxCC's own Src loader, checkLimb, and zero-natOverflow checker
  match Src.load closureBytes equationsJson with
  | .error diag => throw (IO.userError s!"bootstrap: Src.load failed: {diag}")
  | .ok loaded =>
    if cfg.includeLimbEqns then
      IO.ofExcept (validateLimbEquations { words := true } loaded.program limbPins limbEqnAddrs)
    let revMap : Std.HashMap String String :=
      namedMap.fold (init := {}) fun m nm hex => m.insert hex nm
    IO.ofExcept (checkSrcNoBigNatLit loaded.program limbPins fun a => revMap[bytesToHex a.hash]?)
    let _ ← IO.ofExcept verifyInternalIndices
    let lib : FrozenLibrary :=
      { closureBytes, equationsJson, limbPins, entryAddrs, limbEqnAddrs, ixVersion }
    IO.FS.writeFile (cfg.outDir / "bignat-bootstrap.json") (lib.toJson.pretty ++ "\n")
    pure lib

end IxCC.BigNat.Bootstrap
