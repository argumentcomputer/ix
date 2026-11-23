import IxCC.Lam.Erase
import IxCC.Lam.Erase.Limb
import IxCC.Src.Table.Array

/-! # DR3 Native Array, ByteArray & `Array UInt64` Erasure Wiring (`IxCC.Lam.Erase.Array`)

Coordinates `Src → Lam` erasure for programs using native contiguous arrays
(`Array α`, `ByteArray`, `Array UInt64`):

1. Suppresses single-field unboxing (`noUnbox`) for `Array` and `ByteArray`
   while preserving `String` unboxing to `ByteArray` (so UTF-8 `String` values
   and static `.rodata` string literals share the exact `ByteArray` cell layout).
2. Identifies all pinned `Array` / `ByteArray` primitive constants present in
   the `Src.Program` and records their `Key.GKey`s as non-inlinable for
   `Anf.Pipeline` so their O(n) `List` reference bodies are never inlined into
   callers before `Rt.lowerRep` lowers them to O(1) `Rt.Rc.Array.Procs`.
3. Detects `Array UInt64` (`ArrayRepKind.limbs`) usage from the pre-erasure
   `Src.Program` types/terms so unboxed `Array UInt64` programs (e.g.
   `IxCC.BigNat.{add, mul, divMod}`) route directly to `LimbArray` (`tag = 0x7F03`)
   with raw 64-bit `.word` limbs, while polymorphic/boxed arrays route to
   `BoxedArray` (`tag = 0x7F01`).
-/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Array

open IxCC.Src (CId ArrayOp ByteArrayOp ArrayRepKind)
open IxCC.Src.Table (ArrayPins)

/-- Resolve an optional 256-bit pin address in `p`. -/
def resolvePin (p : Src.Program) (pin : Option Nat) : Option CId :=
  pin.bind fun n => p.lookup (Src.Pinned.addrOfNat n)

/-- Inductives whose unboxing must be suppressed for DR3 native arrays:
`Array` and `ByteArray` (never `String`, which unboxes directly to `ByteArray`). -/
def noUnboxCIds (p : Src.Program) (pins : ArrayPins := .fixed) : List CId :=
  [resolvePin p pins.arrayType, resolvePin p pins.byteArrayType].filterMap id

/-- Classification of a pinned `Src.CId` as a native array or `ByteArray` primitive. -/
inductive PinnedOp where
  | arr (op : ArrayOp)
  | arrUget
  | arrUset
  | arrSetBang
  | arrSwapIfInBounds
  | ba (op : ByteArrayOp)
  | baEmpty
  | baUget
  | baUset
  | baGetBang
  | baSetBang
  deriving DecidableEq, Repr, Inhabited

/-- Resolve all pinned `Array` / `ByteArray` operation `CId`s present in `p`. -/
def resolveOps (p : Src.Program) (pins : ArrayPins := .fixed) : List (CId × PinnedOp) :=
  let arrOps := pins.arrayOps.filterMap fun (op, n) =>
    (p.lookup (Src.Pinned.addrOfNat n)).map (·, PinnedOp.arr op)
  let baOps := pins.byteArrayOps.filterMap fun (op, n) =>
    (p.lookup (Src.Pinned.addrOfNat n)).map (·, PinnedOp.ba op)
  let extras : List (Option CId × PinnedOp) :=
    [ (resolvePin p pins.arrayUget, .arrUget),
      (resolvePin p pins.arrayUset, .arrUset),
      (resolvePin p pins.arraySetBang, .arrSetBang),
      (resolvePin p pins.arraySwapIfInBounds, .arrSwapIfInBounds),
      (resolvePin p pins.byteArrayEmpty, .baEmpty),
      (resolvePin p pins.byteArrayUget, .baUget),
      (resolvePin p pins.byteArrayUset, .baUset),
      (resolvePin p pins.byteArrayGetBang, .baGetBang),
      (resolvePin p pins.byteArraySetBang, .baSetBang) ]
  let extraOps := extras.filterMap fun (oc, op) => oc.map (·, op)
  arrOps ++ baOps ++ extraOps

/-- Lookup a `CId`'s pinned array operation. -/
def pinnedOpOf (ops : List (CId × PinnedOp)) (c : CId) : Option PinnedOp :=
  ops.lookup c

/-- Scan a `Src.Term` to classify element type arguments passed to `Array` type
constructor or `Array.*` operations as `UInt64` (`limbs`) vs non-`UInt64` (`boxed`). -/
private def scanArrayElemTypes (arrC uint64C : CId) (arrOpIds : List CId) :
    Nat → Src.Term → Bool × Bool
  | 0, _ => (false, false)
  | fuel + 1, t =>
    match t with
    | .app .. =>
      let (head, args) := t.spineL
      let fromSelf :=
        match head with
        | .const c _ =>
          if c == arrC || arrOpIds.contains c then
            match args.head? with
            | some (tyArg, _, _) =>
              match tyArg with
              | .const u _ => if u == uint64C then (true, false) else (false, true)
              | .var _ => (false, false) -- polymorphic definition body, skip
              | _ => (false, true)
            | none => (false, false)
          else (false, false)
        | _ => (false, false)
      let fromHead := scanArrayElemTypes arrC uint64C arrOpIds fuel head
      args.foldl (init := (fromSelf.1 || fromHead.1, fromSelf.2 || fromHead.2)) fun acc (a, _, _) =>
        let r := scanArrayElemTypes arrC uint64C arrOpIds fuel a
        (acc.1 || r.1, acc.2 || r.2)
    | .lam _ d b =>
      let r1 := scanArrayElemTypes arrC uint64C arrOpIds fuel d
      let r2 := scanArrayElemTypes arrC uint64C arrOpIds fuel b
      (r1.1 || r2.1, r1.2 || r2.2)
    | .pi _ d b =>
      let r1 := scanArrayElemTypes arrC uint64C arrOpIds fuel d
      let r2 := scanArrayElemTypes arrC uint64C arrOpIds fuel b
      (r1.1 || r2.1, r1.2 || r2.2)
    | .letE _ _ _ ty v b =>
      let r1 := scanArrayElemTypes arrC uint64C arrOpIds fuel ty
      let r2 := scanArrayElemTypes arrC uint64C arrOpIds fuel v
      let r3 := scanArrayElemTypes arrC uint64C arrOpIds fuel b
      (r1.1 || r2.1 || r3.1, r1.2 || r2.2 || r3.2)
    | .proj _ _ e => scanArrayElemTypes arrC uint64C arrOpIds fuel e
    | _ => (false, false)

/-- Determine whether `p`'s roots operate exclusively on unboxed `Array UInt64`
(`ArrayRepKind.limbs`) vs boxed `Array α` (`ArrayRepKind.boxed`).
Checks all root declarations and non-prelude definitions (excluding `Array.*` itself). -/
def detectArrayKind (p : Src.Program) (pins : ArrayPins := .fixed) : ArrayRepKind :=
  match resolvePin p pins.arrayType, resolvePin p pins.uint64Type with
  | some arrC, some uint64C =>
    let ops := resolveOps p pins
    let arrMkC := resolvePin p pins.arrayMk
    let arrOpIds := ops.filterMap (fun (c, op) =>
      match op with
      | .arr _ | .arrUget | .arrUset | .arrSetBang | .arrSwapIfInBounds => some c
      | _ => none) ++ (arrMkC.toList)
    -- Check root types and root bodies directly (most reliable signal).
    let (hasU64, hasOther) := p.roots.foldl (init := (false, false)) fun acc (_, rc) =>
      match p.decl? rc with
      | some (.defn _ _ _ ty val) =>
        let r1 := scanArrayElemTypes arrC uint64C arrOpIds 256 ty
        let r2 := scanArrayElemTypes arrC uint64C arrOpIds 256 val
        (acc.1 || r1.1 || r2.1, acc.2 || r1.2 || r2.2)
      | _ => acc
    if hasU64 && !hasOther then .limbs else .boxed
  | _, _ => .boxed

/-- Metadata collected during DR3 array-aware erasure, passed to `Anf.Pipeline` and `Fir.Rep`. -/
structure ArrayEraseInfo where
  /-- `Key.GKey`s of pinned native array/bytearray globals withheld from inlining. -/
  noInline : List Key.GKey := []
  /-- Resolved `(CId, PinnedOp)` table in the source program. -/
  ops : List (CId × PinnedOp) := []
  /-- Detected representation kind for `Array` in this closure (`.boxed` or `.limbs`). -/
  arrayKind : ArrayRepKind := .boxed
  /-- Constructor key for `Array.mk` when present in the erased program. -/
  arrayMkKey : Option Key.CtorKey := none
  /-- Constructor key for `ByteArray.mk` when present in the erased program. -/
  byteArrayMkKey : Option Key.CtorKey := none
  /-- Constructor key for `List.nil` when present. -/
  listNilKey : Option Key.CtorKey := none
  /-- Constructor key for `List.cons` when present. -/
  listConsKey : Option Key.CtorKey := none
  deriving Inhabited

/-- Collect `ArrayEraseInfo` from a checked `Src.Program` and its erased `Lam.Program`. -/
def collectInfo (p : Src.Program) (L : Lam.Program) (pins : ArrayPins := .fixed)
    (kindOverride : Option ArrayRepKind := none) : ArrayEraseInfo :=
  let ops := resolveOps p pins
  let opCIds := ops.map (·.1)
  let noInline := L.globalList.filterMap fun (_, gl) =>
    match gl.key with
    | .const c _ => if opCIds.contains c then some gl.key else none
    | _ => none
  let arrayKind := kindOverride.getD (detectArrayKind p pins)
  { noInline
    ops
    arrayKind
    arrayMkKey := (resolvePin p pins.arrayMk).map .src
    byteArrayMkKey := (resolvePin p pins.byteArrayMk).map .src
    listNilKey := (resolvePin p pins.listNil).map .src
    listConsKey := (resolvePin p pins.listCons).map .src }

/-- DR3 array-aware erasure: suppresses `Array`/`ByteArray` unboxing (while keeping `String`
unboxed to `ByteArray`), optionally rewrites pinned `IxCC.BigNat.LimbOps` globals via
`Lam.Erase.Limb.rewriteProgram`, and returns `(Lam.Program, Erase.Stats, ArrayEraseInfo)`. -/
def eraseWithArrays (p : Src.Program) (ch : Src.Relevance.Checked)
    (pins : ArrayPins := .fixed) (limbPins : List (CId × Src.LimbOp) := [])
    (prodKey : Option Key.CtorKey := none) (kindOverride : Option ArrayRepKind := none) :
    Except EraseError (Lam.Program × Erase.Stats × ArrayEraseInfo) := do
  let noUnbox := noUnboxCIds p pins
  let (L0, stats) ← Lam.eraseWithNoUnbox noUnbox p ch
  let L := match prodKey with
    | some pk => if limbPins.isEmpty then L0 else Limb.rewriteProgram limbPins pk L0
    | none => L0
  let info := collectInfo p L pins kindOverride
  pure (L, stats, info)

end IxCC.Lam.Erase.Array
