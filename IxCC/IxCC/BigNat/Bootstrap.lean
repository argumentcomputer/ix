import IxCC.BigNat.Entry
import IxCC.BigNat.Proof.Entry
import IxCC.Src.Load
import IxCC.Src.Table.Word
import IxCC.Lam.Syntax
import IxCC.Lir.Syntax
import IxCC.Rt.Layout
import Lean.Data.Json

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
outside the 5 hardware-pinned `LimbOps` (whose bodies are replaced by hardware word
equations) contains any `Nat` literal `≥ 2^63`. -/
def checkSrcNoBigNatLit (p : Src.Program) (pins : Pinned.LimbPins) : Except String Unit := do
  let mut bad : List (CId × List Nat) := []
  for c in List.range p.size do
    if (Pinned.limbAt? pins (p.addr c)).isSome then
      continue
    match p.decl? c with
    | some (.defn .defn _ _ _ val) =>
      let bigs := termBigNatLits val
      if !bigs.isEmpty then
        bad := bad ++ [(c, bigs)]
    | _ => pure ()
  if !bad.isEmpty then
    let desc := ", ".intercalate (bad.map fun (c, ns) => s!"cid {c} ({p.short c}): {ns}")
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
def checkLirHasNoNatOverflow (lp : Lir.Program) : List (Lir.FunId × Lir.Label) := Id.run do
  let mut hits : List (Lir.FunId × Lir.Label) := []
  for fi in [:lp.funcs.size] do
    let f := lp.funcs[fi]!
    for bi in [:f.blocks.size] do
      let b := f.blocks[bi]!
      if b.term == .fail .natOverflow then
        hits := hits ++ [(fi, bi)]
  return hits

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
via `ix compile --consts ... --equations`. -/
structure FreezeConfig where
  /-- Path to the pinned `ix` binary. -/
  ix : FilePath
  /-- Path to the Lean module root (`IxCC/IxCC/BigNat/Bootstrap.lean`, which imports `Entry`). -/
  sourceFile : FilePath := "IxCC/BigNat/Bootstrap.lean"
  /-- Output directory for frozen `.ixe`, `.equations.json`, and `bignat-bootstrap.json`. -/
  outDir : FilePath
  /-- Optional directories prepended to `PATH` when invoking `ix`. -/
  ixPath : List String := []
  /-- Working directory for `ix` (typically the `IxCC` package root). -/
  cwd : Option FilePath := none
  /-- Include all 5 `LimbOps` equation theorems in `--consts`. -/
  includeLimbEqns : Bool := true
  deriving Inhabited

/-- Exact `ix compile` arguments for the anonymous frozen closure + equations sidecar. -/
def compileAnonArgs (cfg : FreezeConfig) (anonIxe anonEqs : FilePath) : Array String :=
  #[ "compile"
   , "--anon"
   , "--consts", ",".intercalate (allFreezeConsts cfg.includeLimbEqns)
   , "--equations", anonEqs.toString
   , "-o", anonIxe.toString
   , cfg.sourceFile.toString ]

/-- Exact `ix compile` arguments for the named twin closure used by `ix addr-of`. -/
def compileNamedArgs (cfg : FreezeConfig) (namedIxe namedEqs : FilePath) : Array String :=
  #[ "compile"
   , "--consts", ",".intercalate (allFreezeConsts cfg.includeLimbEqns)
   , "--equations", namedEqs.toString
   , "-o", namedIxe.toString
   , cfg.sourceFile.toString ]

/-- Exact `ix addr-of` arguments resolving a Lean constant name against the named twin. -/
def addrOfArgs (namedIxe : FilePath) (constName : String) : Array String :=
  #["addr-of", namedIxe.toString, constName]

private def runCmd (cmd : String) (args : Array String) (cwd : Option FilePath)
    (extraPath : List String) : IO String := do
  let env ← if extraPath.isEmpty then pure #[] else do
    let old := (← IO.getEnv "PATH").getD ""
    pure #[("PATH", some (":".intercalate (extraPath ++ [old])))]
  let out ← IO.Process.output { cmd, args, cwd, env }
  unless out.exitCode == 0 do
    throw (IO.userError s!"bootstrap: `{cmd} {" ".intercalate args.toList}` exited {out.exitCode}\n{out.stderr}")
  return out.stdout

private def resolveAddr (cfg : FreezeConfig) (namedIxe : FilePath) (name : String) :
    IO Ixon.Address := do
  let out ← runCmd cfg.ix.toString (addrOfArgs namedIxe name) cfg.cwd cfg.ixPath
  let line := ((out.splitOn "\n").filter (!·.trimAscii.isEmpty)).getLast?.getD "" |>.trimAscii.toString
  match hexToAddr? line with
  | some a => pure a
  | none => throw (IO.userError s!"bootstrap: `ix addr-of {name}` returned invalid address: {out}")

/-- Freeze `IxCC.BigNat.Entry` + all 5 `LimbOps` word equations with `ix compile`,
resolve all entrypoint and `LimbPins` addresses, validate ingress + `Src.Table.checkLimb` +
`checkSrcNoBigNatLit`, write the frozen library JSON, and return `FrozenLibrary`. -/
def freezeClosure (cfg : FreezeConfig) : IO FrozenLibrary := do
  IO.FS.createDirAll cfg.outDir
  let anonIxe := cfg.outDir / "bignat-entry.ixe"
  let anonEqs := cfg.outDir / "bignat-entry.anon.equations.json"
  let namedIxe := cfg.outDir / "bignat-entry.named.ixe"
  let namedEqs := cfg.outDir / "bignat-entry.named.equations.json"
  let ixVersion := (← runCmd cfg.ix.toString #["--version"] cfg.cwd cfg.ixPath).trimAscii.toString
  let _ ← runCmd cfg.ix.toString (compileAnonArgs cfg anonIxe anonEqs) cfg.cwd cfg.ixPath
  let _ ← runCmd cfg.ix.toString (compileNamedArgs cfg namedIxe namedEqs) cfg.cwd cfg.ixPath
  let closureBytes ← IO.FS.readBinFile anonIxe
  let anonJson ← IO.ofExcept (Json.parse (← IO.FS.readFile anonEqs))
  let namedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile namedEqs))
  unless anonJson == namedJson do
    throw (IO.userError "bootstrap: anonymous and named equation sidecars differ")
  let mut entryAddrs : List (SlowPathOp × Ixon.Address) := []
  for op in SlowPathOp.all do
    let a ← resolveAddr cfg namedIxe op.leanName
    entryAddrs := entryAddrs ++ [(op, a)]
  let mut limbOps : List (Src.LimbOp × Nat) := []
  let mut limbEqnAddrs : List (Src.LimbOp × Ixon.Address) := []
  for (op, defName, thmName) in limbEquationSpecs do
    let defAddr ← resolveAddr cfg namedIxe defName
    limbOps := limbOps ++ [(op, Pinned.addrNat defAddr)]
    if cfg.includeLimbEqns then
      let thmAddr ← resolveAddr cfg namedIxe thmName
      limbEqnAddrs := limbEqnAddrs ++ [(op, thmAddr)]
  let prodType ← resolveAddr cfg namedIxe "Prod"
  let prodMk ← resolveAddr cfg namedIxe "Prod.mk"
  let natLog2 ← resolveAddr cfg namedIxe "Nat.log2"
  let boolToNat ← resolveAddr cfg namedIxe "Bool.toNat"
  let cond ← resolveAddr cfg namedIxe "cond"
  let limbPins : Pinned.LimbPins :=
    { ops := limbOps
    , prodType := some (Pinned.addrNat prodType)
    , prodMk := some (Pinned.addrNat prodMk)
    , natLog2 := some (Pinned.addrNat natLog2)
    , boolToNat := some (Pinned.addrNat boolToNat)
    , cond := some (Pinned.addrNat cond) }
  -- Validate the frozen closure through IxCC's own Src loader, checkLimb, and zero-natOverflow checker
  match Src.load closureBytes anonJson with
  | .error diag => throw (IO.userError s!"bootstrap: Src.load failed: {diag}")
  | .ok loaded =>
    if cfg.includeLimbEqns then
      IO.ofExcept (validateLimbEquations { words := true } loaded.program limbPins limbEqnAddrs)
    IO.ofExcept (checkSrcNoBigNatLit loaded.program limbPins)
    let _ ← IO.ofExcept verifyInternalIndices
    let lib : FrozenLibrary :=
      { closureBytes, equationsJson := anonJson, limbPins, entryAddrs, limbEqnAddrs, ixVersion }
    IO.FS.writeFile (cfg.outDir / "bignat-bootstrap.json") (lib.toJson.pretty ++ "\n")
    pure lib

end IxCC.BigNat.Bootstrap
