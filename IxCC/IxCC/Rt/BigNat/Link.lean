import IxCC.BigNat.Bootstrap
import IxCC.Rt.BigNat.Dispatch
import IxCC.Rt.Procs.Entry
import IxCC.Rt.Procs.Nat
import IxCC.Rt.Rc.Array.Wire
import IxCC.Lam.Erase.Array
import IxCC.Anf.Pipeline
import IxCC.Fir.Lower
import IxCC.Fir.Rep
import IxCC.Own.Immortal
import IxCC.Cfg.Lower
import IxCC.Recheck.Produce
import IxCC.Lir.WellFormed

/-! # Bootstrap Compilation & Linking of the Pure-Lean `IxCC.BigNat` Runtime Library (`IxCC.Rt.BigNat.Link`)

Compiles all 19 `IxCC.BigNat.Entry` slow-path routines (or the 17 pure-`Array UInt64`
numeric entrypoints) through IxCC's own DR2+DR3 bootstrap pipeline
(`Src → Lam.Erase.Array (limbs + 5 LimbOps) → Anf → Fir → Fir.Rep → Own → Cfg → Rt.lowerRep`),
with **zero C and zero GMP**, and generates thin, zero-critical-edge, zero-`natOverflow`,
aliasing-safe LIR ABI wrappers bridging unified Phase 4 `NatVal` words
(odd immediate `2n + 1` for `< 2^63`, even `LimbArray*` pointer for `≥ 2^63`) ↔ `SlowNat`.

## Aliasing Safety Across the Immortal User ↔ Counted `BigNat` Boundary

User programs compiled in the immortal fragment do not emit RC increments when sharing
a `Nat` value across multiple uses (`let y := x + 1; let z := x + 2`). To prevent any
in-place mutation inside `BigNat` (`normalize`, `pred`, `padZeros`, `setLimb`) from
corrupting a user-held `LimbArray` cell:
1. `natValToSlowNat` saturatingly increments `[w + 4]` (`rc := rc + 1` when unsigned
   `rc < 0x40000000`, so static `.rodata` cells with `rc = 0x80000000` receive zero
   writes) before wrapping `w` into `SlowNat.big`.
2. `slowNatToNatVal` promotes `rc == 0 → 1` on any dynamic `LimbArray` cell exiting
   the slow-path library into user code (again leaving `.rodata` cells untouched).
Inside `BigNat` itself, all intermediate limb buffers stay unique (`rc == 0`) and
mutate in place at O(1) cost. -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC
open IxCC.BigNat.Bootstrap
open IxCC.Lir (VReg Word FunId)
open IxCC.Rt
open IxCC.Rt.Lower
open IxCC.Rt.Rc.Array (relocateFunc)

/-! ## Compiled `BigNat` Runtime Library Bundle -/

/-- Bootstrap-compiled `IxCC.BigNat.Entry` LIR library ready to relocate and link
into any Phase 4 arbitrary-precision `Nat` program. -/
structure CompiledBigNatLib where
  /-- Compiled LIR functions of `IxCC.BigNat.Entry` + its relocated array runtime (all `.internal`). -/
  funcs : List Lir.Func
  /-- Local 0-based `FunId` in `funcs` for each compiled `SlowPathOp` entrypoint. -/
  entries : List (SlowPathOp × FunId)
  /-- Constructor tag of `SlowNat.small`. -/
  smallTag : Nat := 0
  /-- Constructor tag of `SlowNat.big`. -/
  bigTag : Nat := 1
  /-- Field representation of `SlowNat.small` field 0 (`.word` or `.obj`). -/
  smallFieldRep : Fir.Rep := .obj
  /-- Constructor tag of `Option.none`. -/
  optNoneTag : Nat := 0
  /-- Constructor tag of `Option.some`. -/
  optSomeTag : Nat := 1
  /-- Constructor tag of `Bool.false` inside the compiled library. -/
  boolFalseTag : Nat := 0
  /-- Constructor tag of `Bool.true` inside the compiled library. -/
  boolTrueTag : Nat := 1
  /-- Diagnostic count of `.fail .natOverflow` blocks inside the raw bootstrap-compiled
  internal `BigNat` functions (internal index bounds, never reached at runtime). -/
  rawNatOverflowCount : Nat := 0
  deriving Inhabited

namespace CompiledBigNatLib

def entryId? (lib : CompiledBigNatLib) (op : SlowPathOp) : Option FunId :=
  (lib.entries.find? (·.1 == op)).map (·.2)

/-- Strip `.sysvExport` on all compiled internal functions and shift internal `FunId`s by `+ base`. -/
def relocate (lib : CompiledBigNatLib) (base : FunId) : List Lir.Func :=
  lib.funcs.map fun f => relocateFunc base { f with conv := .internal }

end CompiledBigNatLib

/-! ## Thin Zero-`natOverflow` `NatVal ↔ SlowNat` LIR ABI Wrappers -/

def bumpAllocCell (ptr : VReg) (nobj tag : Nat) (field : Lir.Arg) : M Unit := do
  assign ptr (.load .w64 .zero (ctxAt bumpOff))
  let e ← freshReg
  assign e (.addr (mem ptr (cellBytes 1)))
  let l ← temp (.load .w64 .zero (ctxAt limitOff))
  check .heap fun ok bad => .br .ugt (.v e) l bad ok
  emit (.store .w64 (ctxAt bumpOff) (.v e))
  emit (.store .w32 (mem ptr 0) (.imm (UInt64.ofNat (headerLow nobj 0 tag))))
  emit (.store .w32 (mem ptr 4) (.imm (UInt64.ofNat immortalRc)))
  emit (.store .w64 (mem ptr (fieldOffset 0)) field)

/-- Convert a Phase 4 `NatVal` word `w` into a `SlowNat` cell in `out`:
* odd immediate `2v + 1` → `SlowNat.small` cell (`w` directly if `.obj`, `w >>> 1` if `.word`);
* even `LimbArray*` pointer → saturating RC bump (`rc < 0x40000000`, zero writes to `.rodata`),
  then `SlowNat.big` cell wrapping `w`.
Zero critical edges, zero `.fail .natOverflow` (only `.fail .heap` on arena exhaustion). -/
def emitNatValToSlowNat (smallTag bigTag : Nat) (smallFieldRep : Fir.Rep)
    (out : VReg) (w : VReg) : M Unit := do
  let smallBlk ← newLabel
  let bigBlk ← newLabel
  let incRcBlk ← newLabel
  let noIncBlk ← newLabel
  let allocBigBlk ← newLabel
  let joinBlk ← newLabel
  close (.br .tz (.v w) (.imm 1) (loc bigBlk) (loc smallBlk))
  -- Small immediate branch: allocate `SlowNat.small`
  openAt smallBlk
  let pSmall ← freshReg
  if smallFieldRep == .word then
    let raw ← bin .shr (.v w) (.imm 1)
    bumpAllocCell pSmall 0 smallTag raw
  else
    bumpAllocCell pSmall 1 smallTag (.v w)
  close (.jump ⟨.loc joinBlk, [.v pSmall]⟩)
  -- Big LimbArray branch: saturating RC increment (skips static `.rodata` `rc = 0x80000000`)
  openAt bigBlk
  let rc ← temp (.load .w32 .zero (mem w 4))
  close (.br .ult rc (.imm 0x40000000) (loc incRcBlk) (loc noIncBlk))
  openAt incRcBlk
  let rc1 ← freshReg
  assign rc1 (.bin .add .w32 rc (.imm 1))
  emit (.store .w32 (mem w 4) (.v rc1))
  close (.jump (loc allocBigBlk))
  openAt noIncBlk
  close (.jump (loc allocBigBlk))
  openAt allocBigBlk
  let pBig ← freshReg
  bumpAllocCell pBig 1 bigTag (.v w)
  close (.jump ⟨.loc joinBlk, [.v pBig]⟩)
  openAt joinBlk [out]

/-- Convert a canonical `SlowNat` cell `sn` back into a Phase 4 `NatVal` word in `out`:
* `SlowNat.small`: extracts `v < 2^63` (handling both odd tagged `.obj` and 1-scalar-word boxed
  `.obj`, or raw `.word`) and returns odd tagged `2v + 1`;
* `SlowNat.big`: loads `limbsPtr`, sets `rc := 1` when `rc == 0` (leaving `.rodata` `rc = 0x80000000`
  untouched), and returns `limbsPtr`.
Zero critical edges, zero `.fail .natOverflow`. -/
def emitSlowNatToNatVal (smallTag : Nat) (smallFieldRep : Fir.Rep)
    (out : VReg) (sn : VReg) : M Unit := do
  let tag ← temp (.load .w16 .zero (mem sn tagOffset))
  let smallBlk ← newLabel
  let bigBlk ← newLabel
  let joinBlk ← newLabel
  close (.br .eq tag (.imm (UInt64.ofNat smallTag)) (loc smallBlk) (loc bigBlk))
  -- Small branch
  openAt smallBlk
  let f ← freshReg
  assign f (.load .w64 .zero (mem sn (fieldOffset 0)))
  if smallFieldRep == .word then
    let r ← temp (retag (.v f))
    close (.jump ⟨.loc joinBlk, [r]⟩)
  else
    let taggedBlk ← newLabel
    let boxedBlk ← newLabel
    close (.br .tz (.v f) (.imm 1) (loc boxedBlk) (loc taggedBlk))
    openAt taggedBlk
    close (.jump ⟨.loc joinBlk, [.v f]⟩)
    openAt boxedBlk
    let raw ← temp (.load .w64 .zero (mem f (fieldOffset 0)))
    let r ← temp (retag raw)
    close (.jump ⟨.loc joinBlk, [r]⟩)
  -- Big branch: promote unique `rc == 0` to `1` for immortal-user sharing safety
  openAt bigBlk
  let lp ← freshReg
  assign lp (.load .w64 .zero (mem sn (fieldOffset 0)))
  let rc ← temp (.load .w32 .zero (mem lp 4))
  let setRcBlk ← newLabel
  let keepRcBlk ← newLabel
  close (.br .eq rc (.imm 0) (loc setRcBlk) (loc keepRcBlk))
  openAt setRcBlk
  emit (.store .w32 (mem lp 4) (.imm 1))
  close (.jump ⟨.loc joinBlk, [.v lp]⟩)
  openAt keepRcBlk
  close (.jump ⟨.loc joinBlk, [.v lp]⟩)
  openAt joinBlk [out]

/-- Materialize a `Rt.Lower.M Unit` body into a critical-edge-free `Lir.Func`. -/
def buildWrapperFunc (name : String) (params : List VReg) (freshStart : VReg)
    (conv : Lir.Conv := .internal) (act : M Unit) : Except Error Lir.Func := do
  let ((), st) ← act.run { fresh := freshStart }
  let pblocks ← chunkBlocks 0 st
  let (starts, _) := chunkStarts 0 [pblocks]
  let raw ← resolveChunks 0 starts [(pblocks, 0)]
  let seen := reachable raw
  unless reachClosed raw seen do
    throw (.internal 0 s!"bignat wrapper '{name}' has unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name, params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

/-- Binary `NatVal → NatVal → NatVal` wrapper calling `SlowNat → SlowNat → SlowNat`. -/
def mkBinNatWrapper (lib : CompiledBigNatLib) (name : String) (callee : FunId)
    (conv : Lir.Conv := .internal) : Except Error Lir.Func :=
  buildWrapperFunc name [0, 1] 2 conv do
    let sa ← freshReg
    let sb ← freshReg
    let sn ← freshReg
    let res ← freshReg
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sa 0
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sb 1
    emit (.call [sn] callee [.v sa, .v sb])
    emitSlowNatToNatVal lib.smallTag lib.smallFieldRep res sn
    close (.ret (.v res))

/-- Unary `NatVal → NatVal` wrapper calling `SlowNat → SlowNat`. -/
def mkUnNatWrapper (lib : CompiledBigNatLib) (name : String) (callee : FunId)
    (conv : Lir.Conv := .internal) : Except Error Lir.Func :=
  buildWrapperFunc name [0] 1 conv do
    let sa ← freshReg
    let sn ← freshReg
    let res ← freshReg
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sa 0
    emit (.call [sn] callee [.v sa])
    emitSlowNatToNatVal lib.smallTag lib.smallFieldRep res sn
    close (.ret (.v res))

/-- Binary `NatVal → NatVal → NatVal` wrapper calling `SlowNat → SlowNat → Option SlowNat`
(`pow?`, `shiftLeft?`): returns `.fail .heap` on `Option.none` (ZERO `.fail .natOverflow`!). -/
def mkOptBinNatWrapper (lib : CompiledBigNatLib) (name : String) (callee : FunId)
    (conv : Lir.Conv := .internal) : Except Error Lir.Func :=
  buildWrapperFunc name [0, 1] 2 conv do
    let sa ← freshReg
    let sb ← freshReg
    let opt ← freshReg
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sa 0
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sb 1
    emit (.call [opt] callee [.v sa, .v sb])
    let noneBlk ← newLabel
    let someBlk ← newLabel
    close (.br .eq (.v opt) (.imm (ctor0Word lib.optNoneTag)) (loc noneBlk) (loc someBlk))
    put noneBlk { term := .fail .heap, cold := true }
    openAt someBlk
    let sn ← freshReg
    assign sn (.load .w64 .zero (mem opt (fieldOffset 0)))
    let res ← freshReg
    emitSlowNatToNatVal lib.smallTag lib.smallFieldRep res sn
    close (.ret (.v res))

/-- Binary `NatVal → NatVal → BoolVal tWord fWord` comparison wrapper (`beq`, `ble`, `blt`). -/
def mkCmpNatWrapper (lib : CompiledBigNatLib) (name : String) (callee : FunId)
    (tWord fWord : Word) (conv : Lir.Conv := .internal) : Except Error Lir.Func :=
  buildWrapperFunc name [0, 1] 2 conv do
    let sa ← freshReg
    let sb ← freshReg
    let b ← freshReg
    let res ← freshReg
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sa 0
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sb 1
    emit (.call [b] callee [.v sa, .v sb])
    assign res (.select .eq .w64 (.v b) (.imm (ctor0Word lib.boolTrueTag)) (.imm tWord) (.imm fWord))
    close (.ret (.v res))

/-- Unary `NatVal → String` (`ByteArray` cell) decimal formatting wrapper (`toDecimal`). -/
def mkToDecimalWrapper (lib : CompiledBigNatLib) (name : String) (callee : FunId)
    (conv : Lir.Conv := .internal) : Except Error Lir.Func :=
  buildWrapperFunc name [0] 1 conv do
    let sa ← freshReg
    let str ← freshReg
    emitNatValToSlowNat lib.smallTag lib.bigTag lib.smallFieldRep sa 0
    emit (.call [str] callee [.v sa])
    close (.ret (.v str))

/-- Unary `String` (`ByteArray` cell) → `NatVal` decimal parsing wrapper (`ofDecimal`;
returns tagged `0` on `Option.none`). -/
def mkOfDecimalWrapper (lib : CompiledBigNatLib) (name : String) (callee : FunId)
    (conv : Lir.Conv := .internal) : Except Error Lir.Func :=
  buildWrapperFunc name [0] 1 conv do
    let opt ← freshReg
    emit (.call [opt] callee [.v 0])
    let noneBlk ← newLabel
    let someBlk ← newLabel
    close (.br .eq (.v opt) (.imm (ctor0Word lib.optNoneTag)) (loc noneBlk) (loc someBlk))
    put noneBlk { term := .ret (.imm 1), cold := true }
    openAt someBlk
    let sn ← freshReg
    assign sn (.load .w64 .zero (mem opt (fieldOffset 0)))
    let res ← freshReg
    emitSlowNatToNatVal lib.smallTag lib.smallFieldRep res sn
    close (.ret (.v res))

/-! ## Linking the 16 Core `BigNatProcs` Wrappers into a Program -/

/-- Exact number of ABI wrapper procedures emitted for the 16 core `Nat` primitives
(`add, sub, pred, mul, div, mod, powSlow, gcdSlow, beq, ble, blt, land, lor, xor, shl, shr`). -/
def coreWrapperCount : Nat := 16

/-- Build the 16 ABI wrapper procedures at `wrapBase ..< wrapBase + 16`, targeting the
relocated `lib` starting at `libBase`, plus the populated `BigNatProcs` table pointing
`pow` to `natPowId` (`Rt.Procs.natPowBig (wrapBase + 6)`) and `gcd` to `natGcdId`
(`Rt.Procs.natGcdBig (wrapBase + 7)`). -/
def buildCoreWrappers (lib : CompiledBigNatLib) (libBase wrapBase natPowId natGcdId : FunId)
    (bools : Option (Word × Word)) : Except Error (List Lir.Func × BigNatProcs × FunId × FunId) := do
  let req (op : SlowPathOp) : Except Error FunId :=
    match lib.entryId? op with
    | some fid => pure (libBase + fid)
    | none => throw (.internal 0 s!"bignat link: missing compiled entry for '{op.key}'")
  let (tWord, fWord) := bools.getD (ctor0Word lib.boolTrueTag, ctor0Word lib.boolFalseTag)
  let fAdd ← mkBinNatWrapper lib "rt_bignat_add" (← req .add)
  let fSub ← mkBinNatWrapper lib "rt_bignat_sub" (← req .sub)
  let fPred ← mkUnNatWrapper lib "rt_bignat_pred" (← req .pred)
  let fMul ← mkBinNatWrapper lib "rt_bignat_mul" (← req .mul)
  let fDiv ← mkBinNatWrapper lib "rt_bignat_div" (← req .div)
  let fMod ← mkBinNatWrapper lib "rt_bignat_mod" (← req .mod)
  let fPowSlow ← mkOptBinNatWrapper lib "rt_bignat_pow_slow" (← req .pow)
  let fGcdSlow ← mkBinNatWrapper lib "rt_bignat_gcd_slow" (← req .gcd)
  let fBeq ← mkCmpNatWrapper lib "rt_bignat_beq" (← req .beq) tWord fWord
  let fBle ← mkCmpNatWrapper lib "rt_bignat_ble" (← req .ble) tWord fWord
  let fBlt ← mkCmpNatWrapper lib "rt_bignat_blt" (← req .blt) tWord fWord
  let fLand ← mkBinNatWrapper lib "rt_bignat_land" (← req .land)
  let fLor ← mkBinNatWrapper lib "rt_bignat_lor" (← req .lor)
  let fXor ← mkBinNatWrapper lib "rt_bignat_xor" (← req .xor)
  let fShl ← mkOptBinNatWrapper lib "rt_bignat_shl" (← req .shiftLeft)
  let fShr ← mkBinNatWrapper lib "rt_bignat_shr" (← req .shiftRight)
  let wrappers : List Lir.Func :=
    [ fAdd, fSub, fPred, fMul, fDiv, fMod, fPowSlow, fGcdSlow
    , fBeq, fBle, fBlt, fLand, fLor, fXor, fShl, fShr ]
  let slowPowId := wrapBase + 6
  let slowGcdId := wrapBase + 7
  let procs : BigNatProcs :=
    { add := wrapBase + 0
    , sub := wrapBase + 1
    , pred := wrapBase + 2
    , mul := wrapBase + 3
    , div := wrapBase + 4
    , mod := wrapBase + 5
    , pow := natPowId
    , gcd := natGcdId
    , beq := wrapBase + 8
    , ble := wrapBase + 9
    , blt := wrapBase + 10
    , land := wrapBase + 11
    , lor := wrapBase + 12
    , xor := wrapBase + 13
    , shl := wrapBase + 14
    , shr := wrapBase + 15 }
  pure (wrappers, procs, slowPowId, slowGcdId)

/-! ## Bootstrap Compilation (`FrozenLibrary → CompiledBigNatLib`) -/

private def lookupCtorTag (namedMap : Std.HashMap String String) (src : Src.Program)
    (ctors : List Lam.CtorInfo) (name : String) (defaultTag : Nat) : Nat :=
  match (namedMap[name]?.bind hexToAddr?).bind src.lookup with
  | some cid =>
    match Fir.CtorInfo.ofKey ctors (.src cid) with
    | some ci => ci.tag
    | none => defaultTag
  | none => defaultTag

private def lookupCtorFieldRep (namedMap : Std.HashMap String String) (src : Src.Program)
    (cert : Fir.Rep.Cert) (name : String) (fieldIdx : Nat) (defaultRep : Fir.Rep) : Fir.Rep :=
  match (namedMap[name]?.bind hexToAddr?).bind src.lookup with
  | some cid => cert.fieldRep (.src cid) fieldIdx
  | none => defaultRep

/-- Refine `.limbs` array primitive parameter representations in a `Fir.Rep.Cert` so
`Array.set` / `Array.push` take raw `.word` `UInt64` limb values (zero `box64`/`unbox64`
inside tight limb loops) and index parameters take `.tobj` whenever accepted by
`Fir.Rep.checkWithArrays`. -/
private def refineLimbsArrayCert (P : Fir.Program) (cert : Fir.Rep.Cert) : Fir.Rep.Cert :=
  let tryFun (c : Fir.Rep.Cert) (f : FunId) : Fir.Rep.Cert :=
    match P.fun? f, c.arrayPrims.get? f with
    | some fd, some spec =>
      if spec.kind != .limbs then c
      else
        let updateParam (fc0 : Fir.Rep.FunCert) (idx : Nat) (rep : Fir.Rep) : Fir.Rep.FunCert :=
          match fd.params[idx]? with
          | some (v, _) =>
            { fc0 with
              params := fc0.params.set idx rep
              vars := fc0.vars.insert v rep }
          | none => fc0
        let tryParam (c0 : Fir.Rep.Cert) (idx : Nat) (rep : Fir.Rep) : Fir.Rep.Cert :=
          let fc' := updateParam (c0.funCert f) idx rep
          let c' := { c0 with funs := c0.funs.insert f fc' }
          if Fir.Rep.checkWithArrays P c' then c' else c0
        match spec.op, spec.argIdx with
        | .set, [_, ii, vi] => tryParam (tryParam c vi .word) ii .tobj
        | .push, [_, vi] => tryParam c vi .word
        | .get, [_, ii] => tryParam c ii .tobj
        | .emptyCap, [ci] => tryParam c ci .tobj
        | _, _ => c
    | _, _ => c
  (List.range P.size).foldl tryFun cert

/-- Compile a frozen `IxCC.BigNat.Entry` closure (`FrozenLibrary`) through IxCC's own
DR2+DR3 bootstrap pipeline (`Src → Lam.Erase.Array (limbs + 5 LimbOps) → Anf → Fir →
Fir.Rep → Own → Cfg → Rt.lowerRep`) into a `CompiledBigNatLib` (zero C, zero GMP). -/
def compileLibrary (lib : FrozenLibrary) : Except String CompiledBigNatLib := do
  let rootNames := lib.entryAddrs.map (·.1.leanName)
  let inp ← (Recheck.ingress lib.closureBytes lib.equationsJson rootNames).mapError (·.render)
  let ps ← (Recheck.produceSource {} inp).mapError (·.render)
  -- Resolve the 5 hardware `LimbOps` pins + `Prod.mk` key in `ps.src`
  let limbPins : List (Src.CId × Src.LimbOp) :=
    lib.limbPins.ops.filterMap fun (op, addrNat) =>
      (ps.src.lookup (Src.Pinned.addrOfNat addrNat)).map (·, op)
  let prodKey : Option Key.CtorKey :=
    lib.limbPins.prodMk.bind fun addrNat =>
      (ps.src.lookup (Src.Pinned.addrOfNat addrNat)).map Key.CtorKey.src
  let (lam, _, info) ← (Lam.Erase.Array.eraseWithArrays ps.src ps.checked
      .fixed limbPins prodKey (kindOverride := some .limbs)).mapError toString
  let budgets : Anf.Pipeline.Budgets :=
    { inline := { noInline := info.noInline } }
  let trace ← Anf.Pipeline.produce budgets lam
  let (anf, _) ← (Recheck.produceClosures ps.src trace).mapError (·.render)
  let fir ← (Fir.lower anf).mapError (·.render)
  let cert := refineLimbsArrayCert fir (Fir.Rep.inferWithArrays fir info)
  unless Fir.Rep.checkWithArrays fir cert do
    throw "bignat link: Fir.Rep.checkWithArrays failed on compiled BigNat.Entry"
  let own := Own.immortal fir
  let cfg := Cfg.lower own
  let lowered ← (Rt.lowerRep { names := rootNames } cert cfg).mapError (·.render)
  lowered.program.check
  -- Resolve exact constructor tags & field reps from the compiled closure
  let namedMap := (extractNamedMap lib.closureBytes).toOption.getD {}
  let smallTag := lookupCtorTag namedMap ps.src fir.ctors "IxCC.BigNat.Entry.SlowNat.small" 0
  let bigTag := lookupCtorTag namedMap ps.src fir.ctors "IxCC.BigNat.Entry.SlowNat.big" 1
  let smallFieldRep := lookupCtorFieldRep namedMap ps.src cert "IxCC.BigNat.Entry.SlowNat.small" 0 .obj
  let optNoneTag := lookupCtorTag namedMap ps.src fir.ctors "Option.none" 0
  let optSomeTag := lookupCtorTag namedMap ps.src fir.ctors "Option.some" 1
  let boolFalseTag := (fir.known.boolFalse.bind (Fir.CtorInfo.ofKey fir.ctors)).map (·.tag) |>.getD 0
  let boolTrueTag := (fir.known.boolTrue.bind (Fir.CtorInfo.ofKey fir.ctors)).map (·.tag) |>.getD 1
  -- Pair each `SlowPathOp` with its compiled `Lir.FunId` (exports preserve `rootNames` order)
  unless lowered.roots.length == lib.entryAddrs.length do
    throw s!"bignat link: root count mismatch ({lowered.roots.length} vs {lib.entryAddrs.length})"
  let entries : List (SlowPathOp × FunId) :=
    (lib.entryAddrs.zip lowered.roots).map fun ((op, _), (fid, _)) => (op, fid)
  let funcs := lowered.program.funcs.toList.map fun f => { f with conv := .internal }
  let rawOvfs := (checkLirHasNoNatOverflow lowered.program).length
  pure
    { funcs
    , entries
    , smallTag
    , bigTag
    , smallFieldRep
    , optNoneTag
    , optSomeTag
    , boolFalseTag
    , boolTrueTag
    , rawNatOverflowCount := rawOvfs }

/-- Build a standalone LIR program exporting `cx_init` plus ALL compiled `BigNat` ABI
wrappers (`rt_bignat_add`, ..., `rt_bignat_shr`, plus `rt_bignat_log2`, `rt_bignat_toDecimal`,
`rt_bignat_ofDecimal` when present) for direct native Xeon testing and 100k+ differential
verification against Lean 4 GMP. -/
def standaloneLibraryProgram (lib : CompiledBigNatLib) :
    Except Error (Lir.Program × List String) := do
  -- Function 0: `cx_init`; 1..lib.funcs.length: relocated internal library; wrappers after
  let libBase : FunId := 1
  let wrapBase : FunId := libBase + lib.funcs.length
  let relocLib := lib.relocate libBase
  let tWord := ctor0Word lib.boolTrueTag
  let fWord := ctor0Word lib.boolFalseTag
  let mut wrappers : List Lir.Func := []
  let mut exports : List String := ["cx_init"]
  for (op, localId) in lib.entries do
    let callee := libBase + localId
    let sym := op.lirSymbol
    let fn ← match op with
      | .add | .sub | .mul | .div | .mod | .gcd | .land | .lor | .xor | .shiftRight =>
        mkBinNatWrapper lib sym callee (.sysvExport sym)
      | .pred | .log2 =>
        mkUnNatWrapper lib sym callee (.sysvExport sym)
      | .pow | .shiftLeft =>
        mkOptBinNatWrapper lib sym callee (.sysvExport sym)
      | .beq | .ble | .blt =>
        mkCmpNatWrapper lib sym callee tWord fWord (.sysvExport sym)
      | .toDecimal =>
        mkToDecimalWrapper lib sym callee (.sysvExport sym)
      | .ofDecimal =>
        mkOfDecimalWrapper lib sym callee (.sysvExport sym)
    wrappers := wrappers ++ [fn]
    exports := exports ++ [sym]
  let _ := wrapBase
  let allFuncs := [Procs.cxInit] ++ relocLib ++ wrappers
  pure ({ funcs := allFuncs.toArray, main := 0 }, exports)

end IxCC.Rt.BigNat
