import IxCC.Rt.Lower
import IxCC.Rt.BigNat.Cell
import IxCC.Rt.BigNat.Dispatch
import IxCC.Rt.BigNat.Link
import IxCC.Rt.Procs.Entry
import IxCC.Rt.Procs.Nat
import IxCC.Rt.Rc.Array.Wire

/-! # Phase 4 Arbitrary-Precision `Nat` Lowering (`IxCC.Rt.BigNat.LowerBig`)

Wires arbitrary-precision `Nat` end-to-end into IxCC's Cfg → Lir lowering without
modifying Phase 1's `Rt.lower` or `Rt.lowerRep`:

* **`lowerBig` / `lowerBigWith`**: lowers any `Cfg.Program` (immortal fragment +
  static strings + static `≥ 2^63` `Nat` literals) using `Rt.BigNat.Dispatch.primitiveBig`
  for all 16 `Nat` primitives, `Dispatch.natSuccPeelBig` for `Nat.succ` projection peel,
  exact `v == 1` `Nat` switches (`NatVal.eq_one_iff_zero`), immortal `.rodata` /
  position-independent `bigNatLitProc` cells for `≥ 2^63` `Nat` literals, `Rt.Procs.natPowBig`
  and `Rt.Procs.natGcdBig`, and the bootstrap-compiled `IxCC.BigNat.Entry` library (`Link.lean`).
* **`lowerRepBig`**: combines Phase 4 arbitrary-precision `Nat` with DR1 `.rodata`,
  DR2 raw 64-bit `UInt64` + fused `LimbOps`, DR3 native `Array`/`ByteArray`/`LimbArray`,
  and DR4 UTF-8 `String` literals (`Fir.Rep.Cert`).
* **Zero `.fail .natOverflow` by construction:** NO user function, runtime wrapper,
  `bigNatLitProc`, `strLitProc`, `natPowBig`, `natGcdBig`, or `cxInit` lowered by
  `lowerBig` / `lowerRepBig` EVER emits `.fail .natOverflow` (structurally proved in
  `IxCC.Rt.BigNat.LowerBigProof`). -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC
open IxCC.Fir (FunId)
open IxCC.Lir (VReg Label Word)
open IxCC.Rt
open IxCC.Rt.Lower
open IxCC.Rt.LowerRep
open IxCC.Rt.Rc.Array
open IxCC.X86.ELFRodata

/-! ## 1. Collecting `≥ 2^63` `Nat` Literals & Building `.rodata` / Materializer Procs -/

def addBigNat (acc : List Nat) (n : Nat) : List Nat :=
  if n < Rt.natLimit || acc.contains n then acc else acc ++ [n]

def collectArgBigNats (acc : List Nat) : Fir.Arg → List Nat
  | .lit (.nat n) => addBigNat acc n
  | _ => acc

def collectArgsBigNats (acc : List Nat) (as : List Fir.Arg) : List Nat :=
  as.foldl collectArgBigNats acc

def collectRhsBigNats (acc : List Nat) : Own.Rhs → List Nat
  | .fir (.arg a) => collectArgBigNats acc a
  | .fir (.ctor _ as) | .fir (.prim _ as) | .fir (.call _ as) => collectArgsBigNats acc as
  | .fir (.proj ..) => acc
  | .alloc _ as _ => collectArgsBigNats acc as
  | .proj .. => acc

def collectInstrBigNats (acc : List Nat) : Cfg.Instr → List Nat
  | .bind _ r => collectRhsBigNats acc r

def collectEdgeBigNats (acc : List Nat) (e : Cfg.Edge) : List Nat :=
  collectArgsBigNats acc e.args

def collectTermBigNats (acc : List Nat) : Cfg.Term → List Nat
  | .jump e => collectEdgeBigNats acc e
  | .switch _ alts d =>
    let a1 := alts.foldl (fun s (_, e) => collectEdgeBigNats s e) acc
    match d with
    | some e => collectEdgeBigNats a1 e
    | none => a1
  | .ret a => collectArgBigNats acc a
  | .tcall _ as => collectArgsBigNats acc as
  | .trap => acc

def collectBlockBigNats (acc : List Nat) (b : Cfg.Block) : List Nat :=
  collectTermBigNats (b.body.foldl collectInstrBigNats acc) b.term

def collectFunBigNats (acc : List Nat) (fd : Cfg.Fun) : List Nat :=
  fd.blocks.foldl collectBlockBigNats acc

/-- All distinct `Nat` literals `≥ 2^63` (`Rt.natLimit`) occurring in functions `0 ..< P.size`
of `P`, in deterministic order. -/
def collectBigNats (P : Cfg.Program) : List Nat :=
  (List.range P.size).foldl (init := []) fun acc f =>
    match P.fun? f with
    | some fd => collectFunBigNats acc fd
    | none => acc

/-- Build a `.rodata` section table and per-literal byte offsets for `≥ 2^63` `Nat` literals
(`cx_bignat_lit_0`, ...). -/
def buildBigNatRodata (nats : List Nat) : RodataTable × List (Nat × Nat) :=
  nats.zipIdx.foldl (init := (RodataTable.empty, [])) fun (tbl, offs) (n, i) =>
    let (tbl', off) := addBigNatLiteral tbl s!"cx_bignat_lit_{i}" n
    (tbl', offs ++ [(n, off)])

/-- Kernel-evaluable version of `buildBigNatRodata` (zero `ByteArray` copies). -/
def buildBigNatRodataK (nats : List Nat) : RodataTable × List (Nat × Nat) :=
  let (tbl, offs) :=
    nats.zipIdx.foldl (init := (RodataTableK.empty, [])) fun (tbl, offs) (n, i) =>
      let (tbl', off) := addBigNatLiteralK tbl s!"cx_bignat_lit_{i}" n
      (tbl', offs ++ [(n, off)])
  (tbl.toRodataTable, offs)

/-- Kernel-evaluable combined `.rodata` builder for both static UTF-8 strings (`cx_str_i`)
and static `≥ 2^63` `BigNat` literals (`cx_bignat_lit_i`) in one `.rodata` section. -/
def buildCombinedRodataK (strs : List String) (nats : List Nat) :
    RodataTable × List (String × Nat) × List (Nat × Nat) :=
  let (tbl1, strOffs) :=
    strs.zipIdx.foldl (init := (RodataTableK.empty, [])) fun (tbl, offs) (s, i) =>
      let (tbl', off) := tbl.addString s!"cx_str_{i}" s
      (tbl', offs ++ [(s, off)])
  let (tbl2, natOffs) :=
    nats.zipIdx.foldl (init := (tbl1, [])) fun (tbl, offs) (n, i) =>
      let (tbl', off) := addBigNatLiteralK tbl s!"cx_bignat_lit_{i}" n
      (tbl', offs ++ [(n, off)])
  (tbl2.toRodataTable, strOffs, natOffs)

/-- Position-independent LIR materializer for a `≥ 2^63` `Nat` literal `n`:
bump-allocates `24 + 8 * limbs.length` bytes and stores the exact 64-bit words of
`encodeStaticLimbArray (IxCC.BigNat.ofNat n).toList` (`staticHeader 0 tagLimbArray`,
`size`, `cap`, and every little-endian 64-bit limb).
Zero critical edges, zero `.fail .natOverflow` (fails `.heap` only). -/
def bigNatLitProc (idx : Nat) (n : Nat) : Lir.Func :=
  let limbs : List Word := (IxCC.BigNat.ofNat n).toList
  let words : List Word :=
    staticHeader 0 tagLimbArray :: UInt64.ofNat limbs.length :: UInt64.ofNat limbs.length :: limbs
  let nBytes := 8 * words.length
  if nBytes ≥ 2 ^ 31 then
    { name := s!"rt_bignat_lit_{idx}"
      params := []
      results := 1
      blocks := #[{ term := .fail .heap, cold := true }] }
  else
    let storeStmts : List Lir.Stmt :=
      words.zipIdx.flatMap fun (w, k) =>
        let reg := 3 + k
        [ .assign reg (.arg (.imm w))
        , .store .w64 { base := some (.v 0), disp := (8 * k : Int) } (.v reg) ]
    { name := s!"rt_bignat_lit_{idx}"
      params := []
      results := 1
      blocks := #[
        -- 0: bump = [ctx - 40], limit = [ctx - 32], next = bump + nBytes
        { body := #[
            .assign 0 (.load .w64 .zero (ctxAt bumpOff)),
            .assign 1 (.load .w64 .zero (ctxAt limitOff))]
          term := .brOvf .addC 2 (.v 0) (.imm (UInt64.ofNat nBytes)) ⟨1, []⟩ ⟨3, []⟩ },
        -- 1: check next <= limit
        { term := .br .ule .w64 (.v 2) (.v 1) ⟨2, []⟩ ⟨4, []⟩ },
        -- 2: commit bump, store exact static LimbArray words, return bump
        { body := (#[.store .w64 (ctxAt bumpOff) (.v 2)] ++ storeStmts.toArray)
          term := .ret [.v 0] },
        -- 3: heap exhausted (overflow)
        { term := .fail .heap, cold := true },
        -- 4: heap exhausted (limit)
        { term := .fail .heap, cold := true } ] }

/-- Context resolving `≥ 2^63` `Nat` literals to either direct `.rodata` addresses
(`Config.rodataBase = some base`) or position-independent `bigNatLitProc` `FunId`s. -/
structure BigNatLitCtx where
  rodataAddrs : List (Nat × Word) := []
  litFns : List (Nat × FunId) := []
  deriving Inhabited

/-! ## 2. Zero-`natOverflow` Word ↔ `NatVal` Coercions -/

/-- Promote a raw 64-bit unsigned word `r` (`[0, 2^64)`) to a canonical Phase 4 `NatVal` in `x`:
* `r < 2^63`: odd tagged immediate `(r <<< 1) ||| 1`;
* `r ≥ 2^63`: bump-allocates a 32-byte canonical 1-limb immortal `LimbArray` cell
  `[staticHeader 0 tagLimbArray, 1, 1, r]` (fails `.heap` only — ZERO `.fail .natOverflow`!). -/
def promoteRaw64ToNatVal (x : VReg) (r : Lir.Arg) : M Unit := do
  let smallBlk ← newLabel
  let bigBlk ← newLabel
  let joinBlk ← newLabel
  close (.br .ugt r (.imm 0x7fffffffffffffff) (loc bigBlk) (loc smallBlk))
  -- Small (< 2^63) fast path
  openAt smallBlk
  let rs ← temp (retag r)
  close (.jump ⟨.loc joinBlk, [rs]⟩)
  -- Big (>= 2^63) cold path: allocate 32-byte 1-limb static-header LimbArray
  openAt bigBlk
  let ptr ← freshReg
  assign ptr (.load .w64 .zero (ctxAt bumpOff))
  let e ← freshReg
  assign e (.addr (mem ptr 32))
  let lim ← temp (.load .w64 .zero (ctxAt limitOff))
  check .heap fun ok bad => .br .ugt (.v e) lim bad ok
  emit (.store .w64 (ctxAt bumpOff) (.v e))
  let hdr ← temp (.arg (.imm (staticHeader 0 tagLimbArray)))
  emit (.store .w64 (mem ptr 0) hdr)
  emit (.store .w64 (mem ptr 8) (.imm 1))
  emit (.store .w64 (mem ptr 16) (.imm 1))
  emit (.store .w64 (mem ptr 24) r)
  close (.jump ⟨.loc joinBlk, [.v ptr]⟩)
  openAt joinBlk [x]

/-- Extract the low 64 bits (`n mod 2^64`) of any Phase 4 `NatVal` word `a` into raw `.word` `x`:
odd immediate `2n + 1` → `w >>> 1`; even canonical `LimbArray*` → `load64 [w + 24]` (limb 0). -/
def natValLow64 (x : VReg) (a : Lir.Arg) : M Unit :=
  match a with
  | .imm w => assign x (.arg (.imm (w >>> 1)))
  | .v y => do
    let smallBlk ← newLabel
    let bigBlk ← newLabel
    let joinBlk ← newLabel
    close (.br .tz (.v y) (.imm 1) (loc bigBlk) (loc smallBlk))
    let rSmall ← freshReg
    put smallBlk {
      body := [.assign rSmall (.bin .shr .w64 (.v y) (.imm 1))]
      term := .jump ⟨.loc joinBlk, [.v rSmall]⟩
    }
    let rBig ← freshReg
    put bigBlk {
      body := [.assign rBig (.load .w64 .zero (mem y 24))]
      term := .jump ⟨.loc joinBlk, [.v rBig]⟩
      cold := true
    }
    openAt joinBlk [x]

/-- Uniformly unbox a `.obj` word that may hold an odd tagged immediate (`< 2^63`),
a 1-scalar-word boxed `UInt64` (`tag = 0`, payload at `+8`), OR a canonical `BigNat`
`LimbArray` (`tag = 0x7F03`, limb 0 at `+24`). -/
def unbox64OrBigNat (x : VReg) (a : Lir.Arg) : M Unit :=
  match a with
  | .imm w => assign x (.arg (.imm (w >>> 1)))
  | .v y => do
    let immBlk ← newLabel
    let ptrBlk ← newLabel
    let boxBlk ← newLabel
    let limbBlk ← newLabel
    let joinBlk ← newLabel
    close (.br .tz (.v y) (.imm 1) (loc ptrBlk) (loc immBlk))
    let rImm ← freshReg
    put immBlk {
      body := [.assign rImm (.bin .shr .w64 (.v y) (.imm 1))]
      term := .jump ⟨.loc joinBlk, [.v rImm]⟩
    }
    let tag ← freshReg
    put ptrBlk {
      body := [.assign tag (.load .w16 .zero (mem y tagOffset))]
      term := .br .eq (.v tag) (.imm (UInt64.ofNat tagLimbArray)) (loc limbBlk) (loc boxBlk)
    }
    let rBox ← freshReg
    put boxBlk {
      body := [.assign rBox (.load .w64 .zero (mem y (fieldOffset 0)))]
      term := .jump ⟨.loc joinBlk, [.v rBox]⟩
    }
    let rLimb ← freshReg
    put limbBlk {
      body := [.assign rLimb (.load .w64 .zero (mem y 24))]
      term := .jump ⟨.loc joinBlk, [.v rLimb]⟩
      cold := true
    }
    openAt joinBlk [x]

/-- Normalize a numeric `.obj` word (odd tagged immediate, `BigNat` `LimbArray` with
`tag = 0x7F03`, or 1-scalar-word `box64` `UInt64` cell) into a canonical Phase 4 `NatVal`.
Preserves all limbs of arbitrary-precision `BigNat` values; never fails `.natOverflow`. -/
def objToNatVal (x : VReg) (a : Lir.Arg) : M Unit :=
  match a with
  | .imm w => assign x (.arg (.imm w))
  | .v y => do
    let immBlk ← newLabel
    let ptrBlk ← newLabel
    let limbBlk ← newLabel
    let boxBlk ← newLabel
    let joinBlk ← newLabel
    close (.br .tz (.v y) (.imm 1) (loc ptrBlk) (loc immBlk))
    put immBlk { term := .jump ⟨.loc joinBlk, [.v y]⟩ }
    let tag ← freshReg
    put ptrBlk {
      body := [.assign tag (.load .w16 .zero (mem y tagOffset))]
      term := .br .eq (.v tag) (.imm (UInt64.ofNat tagLimbArray)) (loc limbBlk) (loc boxBlk)
    }
    put limbBlk { term := .jump ⟨.loc joinBlk, [.v y]⟩, cold := true }
    openAt boxBlk
    let raw ← freshReg
    assign raw (.load .w64 .zero (mem y (fieldOffset 0)))
    let nv ← freshReg
    promoteRaw64ToNatVal nv (.v raw)
    close (.jump ⟨.loc joinBlk, [.v nv]⟩)
    openAt joinBlk [x]

/-- Extract a 64-bit unsigned index/bound/capacity from a `.tobj` Phase 4 `NatVal`:
odd immediate `2n + 1` → `w >>> 1`; even `BigNat` (`n ≥ 2^63`) → saturates to
`0xFFFFFFFFFFFFFFFF` (`UINT64_MAX`) instead of silently truncating mod `2^64`. -/
def natValSaturate64 (x : VReg) (a : Lir.Arg) : M Unit :=
  match a with
  | .imm w => assign x (.arg (.imm (w >>> 1)))
  | .v y => do
    let smallBlk ← newLabel
    let bigBlk ← newLabel
    let joinBlk ← newLabel
    close (.br .tz (.v y) (.imm 1) (loc bigBlk) (loc smallBlk))
    let rSmall ← freshReg
    put smallBlk {
      body := [.assign rSmall (.bin .shr .w64 (.v y) (.imm 1))]
      term := .jump ⟨.loc joinBlk, [.v rSmall]⟩
    }
    put bigBlk {
      term := .jump ⟨.loc joinBlk, [.imm 0xFFFFFFFFFFFFFFFF]⟩
      cold := true
    }
    openAt joinBlk [x]

/-- Extract a 64-bit unsigned index/bound/capacity from a `.obj` word:
odd immediate `2n + 1` → `w >>> 1`; even `BigNat` `LimbArray` (`tag = 0x7F03`, `n ≥ 2^63`)
→ saturates to `0xFFFFFFFFFFFFFFFF` (`UINT64_MAX`); even 1-scalar-word `box64` cell
(`tag ≠ 0x7F03`, e.g. boxed `USize`/`UInt64`) → loads raw `[y + 8]`. -/
def unbox64OrSaturateBigNat (x : VReg) (a : Lir.Arg) : M Unit :=
  match a with
  | .imm w => assign x (.arg (.imm (w >>> 1)))
  | .v y => do
    let immBlk ← newLabel
    let ptrBlk ← newLabel
    let boxBlk ← newLabel
    let limbBlk ← newLabel
    let joinBlk ← newLabel
    close (.br .tz (.v y) (.imm 1) (loc ptrBlk) (loc immBlk))
    let rImm ← freshReg
    put immBlk {
      body := [.assign rImm (.bin .shr .w64 (.v y) (.imm 1))]
      term := .jump ⟨.loc joinBlk, [.v rImm]⟩
    }
    let tag ← freshReg
    put ptrBlk {
      body := [.assign tag (.load .w16 .zero (mem y tagOffset))]
      term := .br .eq (.v tag) (.imm (UInt64.ofNat tagLimbArray)) (loc limbBlk) (loc boxBlk)
    }
    let rBox ← freshReg
    put boxBlk {
      body := [.assign rBox (.load .w64 .zero (mem y (fieldOffset 0)))]
      term := .jump ⟨.loc joinBlk, [.v rBox]⟩
    }
    put limbBlk {
      term := .jump ⟨.loc joinBlk, [.imm 0xFFFFFFFFFFFFFFFF]⟩
      cold := true
    }
    openAt joinBlk [x]

/-- Zero-`natOverflow` width-64 word operation on `NatVal` operands (for non-Rep `lowerBig`):
extracts low 64 bits via `natValLow64`, computes raw 64-bit result via `wordRaw64`, and
promotes via `promoteRaw64ToNatVal`. -/
def word64Big (f : FunId) (x : VReg) (op : Src.WordOp) (as : List Lir.Arg) : M Unit := do
  let raws ← as.mapM fun a => do
    let t ← freshReg
    natValLow64 t a
    pure (.v t)
  let tmp ← freshReg
  wordRaw64 f tmp op raws
  promoteRaw64ToNatVal x (.v tmp)

/-- Zero-`natOverflow` fixed-width word operation on `NatVal` operands (non-Rep `lowerBig`). -/
def wordBig (f : FunId) (x : VReg) (w : Src.Width) (op : Src.WordOp) (as : List Lir.Arg) : M Unit :=
  if w == .w64 then
    match op, as with
    | .toNat, [a] => assign x (.arg a)
    | .convert .w64, [a] => assign x (.arg a)
    | .convert w', [a] => do
      let u ← freshReg
      natValLow64 u a
      let t ← temp (retag (.v u))
      assign x (.bin .and .w64 t (.imm (tagMask w')))
    | _, _ => word64Big f x op as
  else
    match op, as with
    | .ofNat, [a] => do
      let u ← freshReg
      natValLow64 u a
      let t ← temp (retag (.v u))
      assign x (.bin .and .w64 t (.imm (tagMask w)))
    | _, _ => Lower.word f x w op as

/-! ## 3. Non-Rep Phase 4 Arbitrary-Precision Lowering (`lowerBig`) -/

/-- Pure operand check (no materializer calls needed) for non-Rep `lowerBig`. -/
def pureOperandBig (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) :
    Fir.Arg → Except Error (Option Lir.Arg)
  | .var x => pure (some (.v x))
  | .lit (.nat n) =>
    if n < Rt.natLimit then pure (some (.imm (UInt64.ofNat (2 * n + 1))))
    else match bc.rodataAddrs.lookup n with
      | some addr => pure (some (.imm addr))
      | none =>
        if (bc.litFns.lookup n).isSome then pure none
        else throw (.internal f s!"bignat literal {n} missing from BigNatLitCtx")
  | .lit (.str s) =>
    match sc.rodataAddrs.lookup s with
    | some addr => pure (some (.imm addr))
    | none =>
      if (sc.strFns.lookup s).isSome then pure none
      else throw (.string f)
  | .erased => pure (some (.imm erasedWord))

def pureOperandsBig (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) :
    List Fir.Arg → Except Error (Option (List Lir.Arg))
  | [] => pure (some [])
  | a :: as => do
    match ← pureOperandBig f sc bc a with
    | none => pure none
    | some la =>
      match ← pureOperandsBig f sc bc as with
      | none => pure none
      | some las => pure (some (la :: las))

/-- Lower one `Fir.Arg` in `lowerBig`, emitting a zero-arg materializer call only for
position-independent `≥ 2^63` `Nat` or `String` literals. NEVER emits `.fail .natOverflow`. -/
def operandBig (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) : Fir.Arg → M Lir.Arg
  | .var x => pure (.v x)
  | .lit (.nat n) =>
    if n < Rt.natLimit then pure (.imm (UInt64.ofNat (2 * n + 1)))
    else match bc.rodataAddrs.lookup n with
      | some addr => pure (.imm addr)
      | none =>
        match bc.litFns.lookup n with
        | some fnId => do
          let t ← freshReg
          emit (.call [t] fnId [])
          pure (.v t)
        | none => throw (.internal f s!"bignat literal {n} missing from BigNatLitCtx")
  | .lit (.str s) =>
    match sc.rodataAddrs.lookup s with
    | some addr => pure (.imm addr)
    | none =>
      match sc.strFns.lookup s with
      | some fnId => do
        let t ← freshReg
        emit (.call [t] fnId [])
        pure (.v t)
      | none => throw (.string f)
  | .erased => pure (.imm erasedWord)

def operandsBig (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) : List Fir.Arg → M (List Lir.Arg)
  | [] => pure []
  | a :: as => do
    let la ← operandBig f sc bc a
    let las ← operandsBig f sc bc as
    pure (la :: las)

/-- Unified Phase 4 primitive dispatcher for `lowerBig` (all 16 `Nat` ops via
`Rt.BigNat.Dispatch.primitiveBig`, plus zero-`natOverflow` `wordBig`). -/
def primitiveBigAll (f : FunId) (T : Tables) (procs : BigNatProcs) (x : VReg)
    (op : Lam.Prim) (as : List Lir.Arg) : M Unit :=
  match op with
  | .word w wo => wordBig f x w wo as
  | _ => primitiveBig f { bools := T.bools, procs } x op as

/-- Projection lowering for `lowerBig`: `Nat.succ` peel uses `Dispatch.natSuccPeelBig`
(handling both odd immediates and `≥ 2^63` `LimbArray`s with canonical demotion at `2^63`). -/
def projBig (f : FunId) (T : Tables) (procs : BigNatProcs) (x y : VReg)
    (c : Key.CtorKey) (i : Nat) : M Unit := do
  if T.known.natSucc == some c then
    if i == 0 then natSuccPeelBig procs x y
    else throw (.form f "a projection past the Nat successor's field")
  else if T.known.natZero == some c then throw (.form f "a projection of Nat.zero")
  else
    match Fir.CtorInfo.ofKey T.ctors c with
    | some info =>
      if i < info.arity then assign x (.load .w64 .zero (mem y (fieldOffset i)))
      else throw (.form f s!"field {i} of a constructor with {info.arity}")
    | none => throw (.form f "a projection key outside the table")

/-- Single instruction lowering for `lowerBig` (ZERO `.fail .natOverflow`). -/
def instrBig (f : FunId) (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx) :
    Cfg.Instr → M Unit
  | .bind x (.fir (.arg a)) => do
    let la ← operandBig f sc bc a
    assign x (.arg la)
  | .bind x (.fir (.prim op as)) => do
    let las ← operandsBig f sc bc as
    primitiveBigAll f T procs x op las
  | .bind x (.fir (.call g as)) => do
    let las ← operandsBig f sc bc as
    emit (.call [x] g las)
  | .bind _ (.fir (.ctor ..)) => throw (.form f "a Fir constructor in Cfg")
  | .bind _ (.fir (.proj ..)) => throw (.form f "a Fir projection in Cfg")
  | .bind x (.alloc c as _) => do
    let las ← operandsBig f sc bc as
    Lower.alloc f T x c las
  | .bind x (.proj y c i) => projBig f T procs x y c i

def instrsBig (f : FunId) (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx) :
    List Cfg.Instr → M Unit
  | [] => pure ()
  | i :: is => do instrBig f T procs sc bc i; instrsBig f T procs sc bc is

/-- Edge lowering for `lowerBig`: emits a trampoline block only if an edge argument
requires a position-independent materializer call. NEVER emits `.fail .natOverflow`. -/
def edgeBig (f : FunId) (sc : StrCtx) (bc : BigNatLitCtx) (src : Nat) (e : Cfg.Edge) : M PEdge := do
  unless e.back == decide (e.target ≤ src) do throw (.edgeOrder f src)
  match ← pureOperandsBig f sc bc e.args with
  | some las => pure ⟨.blk e.target, las⟩
  | none =>
    let saved ← get
    let tramp ← newLabel
    modify fun st => { st with cur := tramp, params := [], acc := [] }
    let las ← operandsBig f sc bc e.args
    close (.jump ⟨.blk e.target, las⟩)
    modify fun st => { st with cur := saved.cur, params := saved.params, acc := saved.acc }
    pure (loc tramp)

def switchAltBig (f : FunId) (T : Tables) (sc : StrCtx) (bc : BigNatLitCtx) (src : Nat)
    (ke : Key.CtorKey × Cfg.Edge) : M (KeyKind × PEdge) := do
  let some kind := keyKind T ke.1 | throw (.switch f src "a key outside the constructor table")
  pure (kind, ← edgeBig f sc bc src ke.2)

/-- Switch lowering for `lowerBig`: `Nat` keys still use the exact 1-instruction `v == 1`
test (exact across ALL arbitrary-precision `Nat` values via `NatVal.eq_one_iff_zero`!). -/
def switchBig (f : FunId) (T : Tables) (sc : StrCtx) (bc : BigNatLitCtx) (src : Nat) (x : VReg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) : M Unit := do
  let es ← alts.mapM (switchAltBig f T sc bc src)
  let dd ← d.mapM (edgeBig f sc bc src)
  let nats := es.filter (·.1.isNat)
  if !nats.isEmpty then
    unless nats.length == es.length do throw (.switch f src "Nat keys mixed with other keys")
    natSwitch x es dd
  else tagSwitch x es dd

def termBig (f : FunId) (T : Tables) (sc : StrCtx) (bc : BigNatLitCtx) (src : Nat) :
    Cfg.Term → M Unit
  | .jump e => do close (.jump (← edgeBig f sc bc src e))
  | .switch x alts d => switchBig f T sc bc src x alts d
  | .ret a => do close (.ret (← operandBig f sc bc a))
  | .tcall g as => do close (.tail g (← operandsBig f sc bc as))
  | .trap => close .trap

def blockBig (f : FunId) (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx)
    (src : Nat) (entry : Bool) (b : Cfg.Block) : M Unit := do
  openAt 0 (if entry then [] else b.params.map (·.1))
  instrsBig f T procs sc bc b.body
  termBig f T sc bc src b.term

def chunksBig (f : FunId) (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx)
    (merged : Bool) : List (Cfg.Block × Nat) → VReg → Except Error (List (List PBlock) × VReg)
  | [], fresh => pure ([], fresh)
  | (b, i) :: bs, fresh => do
    let ((), st) ← (blockBig f T procs sc bc i (merged && i == 0) b).run { fresh }
    let blocks ← chunkBlocks f st
    let (rest, fresh) ← chunksBig f T procs sc bc merged bs st.fresh
    pure (blocks :: rest, fresh)

def functionRawBig (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx)
    (f : FunId) (fd : Cfg.Fun) : Except Error (List VReg × List Lir.Block) := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
  if let some b := misordered fd then throw (.edgeOrder f b)
  let merged := !(fd.blocks.any fun b => b.term.edges.any (·.target == 0))
  let supply := max fd.vars (maxVar fd + 1)
  let arity := b0.params.length
  let (params, supply) :=
    if merged then (b0.params.map (·.1), supply)
    else ((List.range arity).map (supply + ·), supply + arity)
  let (cs, _) ← chunksBig f T procs sc bc merged fd.blocks.zipIdx supply
  let (starts, _) := chunkStarts (if merged then 0 else 1) cs
  let body ← resolveChunks f starts cs.zipIdx
  let entry : List Lir.Block :=
    if merged then [] else [{ term := .jump { target := starts.getD 0 1, args := params.map .v } }]
  pure (params, entry ++ body)

def functionBig (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx)
    (f : FunId) (fd : Cfg.Fun) (conv : Lir.Conv) : Except Error Lir.Func := do
  let (params, raw) ← functionRawBig T procs sc bc f fd
  let seen := reachable raw
  unless reachClosed raw seen do throw (.internal f "a reached block has an unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

def functionsBig (T : Tables) (procs : BigNatProcs) (sc : StrCtx) (bc : BigNatLitCtx)
    (P : Cfg.Program) (roots : List (FunId × String)) :
    List Nat → Except Error (List Lir.Func)
  | [] => pure []
  | f :: fs => do
    let some fd := P.fun? f | throw (.missingFun f)
    let conv := match roots.lookup f with
      | some s => .sysvExport s
      | none => .internal
    pure ((← functionBig T procs sc bc f fd conv) :: (← functionsBig T procs sc bc P roots fs))

/-- Build `.rodata` + literal contexts (`StrCtx`, `BigNatLitCtx`, materializer procs) for `P`. -/
def buildLiteralContexts (cfg : Config) (strs : List String) (nats : List Nat) (litBase : FunId) :
    StrCtx × BigNatLitCtx × List Lir.Func × Option ByteArray × List X86.ELF.RodataSymbol :=
  if strs.isEmpty && nats.isEmpty then ({}, {}, [], none, [])
  else
    let (rtbl, strOffs, natOffs) := buildCombinedRodataK strs nats
    match cfg.rodataBase with
    | some base =>
      let sc : StrCtx := { rodataAddrs := strOffs.map fun (s, off) => (s, base + UInt64.ofNat off) }
      let bc : BigNatLitCtx := { rodataAddrs := natOffs.map fun (n, off) => (n, base + UInt64.ofNat off) }
      (sc, bc, [], some rtbl.bytes, rtbl.symbols)
    | none =>
      let strProcs := strOffs.zipIdx.map fun ((s, _), i) => Rt.Rc.Array.strLitProc i s
      let strFns := strOffs.zipIdx.map fun ((s, _), i) => (s, litBase + i)
      let natBase := litBase + strProcs.length
      let natProcs := natOffs.zipIdx.map fun ((n, _), i) => bigNatLitProc i n
      let natFns := natOffs.zipIdx.map fun ((n, _), i) => (n, natBase + i)
      ({ strFns }, { litFns := natFns }, strProcs ++ natProcs, some rtbl.bytes, rtbl.symbols)

/-- **Phase 4 Arbitrary-Precision `Nat` Lowering (`lowerBig`)**:
Lowers any `Cfg.Program` (immortal fragment + static strings + static `≥ 2^63` `Nat`
literals) to Lir with zero `.fail .natOverflow` in user code, linking the compiled
pure-Lean `IxCC.BigNat.Entry` runtime library `lib`. -/
def lowerBig (cfg : Config) (lib : CompiledBigNatLib) (P : Cfg.Program) :
    Except Error Lowered := do
  let some main := P.exports.head? | throw .noExports
  if let some (f, _) := P.funs.toList.find? (P.size ≤ ·.1) then throw (.funRange f)
  let named := P.exports.zipIdx.map fun (f, i) => (f, symbolOf ((cfg.names[i]?).getD s!"root{i}"))
  let roots := named.map fun (f, s) => (f, (named.lookup f).getD s)
  let T := tables P
  let initId := P.size
  let natPowId := P.size + 1
  let natGcdId := P.size + 2
  let litBase := P.size + 3
  let strs := LowerStr.collectStrings P
  let nats := collectBigNats P
  let (sc, bc, litProcs, rodata, rodataExports) := buildLiteralContexts cfg strs nats litBase
  let libBase := litBase + litProcs.length
  let relocLib := lib.relocate libBase
  let wrapBase := libBase + relocLib.length
  let (wrappers, procs, slowPowId, slowGcdId) ←
    buildCoreWrappers lib libBase wrapBase natPowId natGcdId T.bools
  let funcs ← functionsBig T procs sc bc P roots (List.range P.size)
  let allFuncs :=
    funcs ++ [Procs.cxInit, Procs.natPowBig slowPowId, Procs.natGcdBig slowGcdId] ++
    litProcs ++ relocLib ++ wrappers
  pure
    { program := { funcs := allFuncs.toArray, main }
    , init := initId
    , natPow := natPowId
    , natGcd := natGcdId
    , roots
    , rodata
    , rodataExports }

/-! ## 4. Rep-Aware Phase 4 Lowering (`lowerRepBig`: DR1 + DR2 + DR3 + DR4 + BigNat) -/

/-- Deliver a raw 64-bit word `r` to `x` at representation `rx`, promoting `≥ 2^63`
`.tobj` results to a canonical 1-limb `BigNat` instead of failing `.natOverflow`. -/
def finishRaw64Big (x : VReg) (rx : Fir.Rep) (r : Lir.Arg) : M Unit :=
  match rx with
  | .word => assign x (.arg r)
  | .obj => box64 x r
  | .tobj => promoteRaw64ToNatVal x r
  | .erased => assign x (.arg r)

/-- Evaluate operand `a` as a raw 64-bit word without ever failing `.natOverflow`. -/
def operandRaw64Big (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) : M Lir.Arg :=
  match a with
  | .var y =>
    match fc.varRep y with
    | .word => pure (.v y)
    | .tobj => do
      let r ← freshReg
      natValLow64 r (.v y)
      pure (.v r)
    | .obj => do
      let r ← freshReg
      unbox64OrBigNat r (.v y)
      pure (.v r)
    | .erased => pure (.v y)
  | .lit (.nat n) => pure (.imm (UInt64.ofNat (n % 2 ^ 64)))
  | .lit (.str _) => throw (.string f)
  | .erased => pure (.imm 0)

def operandsRaw64Big (f : FunId) (fc : Fir.Rep.FunCert) : List Fir.Arg → M (List Lir.Arg)
  | [] => pure []
  | a :: as => do
    let la ← operandRaw64Big f fc a
    let las ← operandsRaw64Big f fc as
    pure (la :: las)

/-- Evaluate operand `a` at target representation `expected`, using `.rodata` /
`bigNatLitProc` for `≥ 2^63` `Nat` literals (ZERO `.fail .natOverflow`!). -/
def operandAtRepBig (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) (expected : Fir.Rep)
    (sc : StrCtx) (bc : BigNatLitCtx) : M Lir.Arg :=
  match expected with
  | .word => operandRaw64Big f fc a
  | .tobj =>
    match a with
    | .var y =>
      if fc.varRep y == .word then do
        let r ← freshReg
        promoteRaw64ToNatVal r (.v y)
        pure (.v r)
      else pure (.v y)
    | _ => operandBig f sc bc a
  | .obj =>
    match a with
    | .var y =>
      if fc.varRep y == .word then do
        let b ← freshReg
        box64 b (.v y)
        pure (.v b)
      else pure (.v y)
    | .lit (.nat n) =>
      if n < Rt.natLimit then pure (.imm (UInt64.ofNat (2 * n + 1)))
      else operandBig f sc bc (.lit (.nat n))
    | _ => operandBig f sc bc a
  | .erased => pure (.imm erasedWord)

def operandsAtRepsBig (f : FunId) (fc : Fir.Rep.FunCert)
    (as : List Fir.Arg) (rs : List Fir.Rep) (sc : StrCtx) (bc : BigNatLitCtx) :
    M (List Lir.Arg) :=
  match as with
  | [] => pure []
  | a :: as => do
    let la ← operandAtRepBig f fc a (rs.headD .tobj) sc bc
    let las ← operandsAtRepsBig f fc as rs.tail sc bc
    pure (la :: las)

/-- Zero-alloc limb pair fusion for `lowerRepBig` (ZERO `.fail .natOverflow`). -/
def emitLimbPairBig (f : FunId) (fc : Fir.Rep.FunCert) (kind : LimbPairKind)
    (r1 r2 : VReg) (as : List Fir.Arg) : M Unit := do
  let las ← operandsRaw64Big f fc as
  let t1 ← freshReg
  let t2 ← freshReg
  match kind, las with
  | .mulWide, [a, b] =>
    emit (.limb t1 t2 (.mulWide64 a b))
    finishRaw64Big r1 (fc.varRep r1) (.v t1)
    finishRaw64Big r2 (fc.varRep r2) (.v t2)
  | .divWide, [hi, lo, d] =>
    emit (.limb t1 t2 (.divWide64 hi lo d))
    finishRaw64Big r1 (fc.varRep r1) (.v t1)
    finishRaw64Big r2 (fc.varRep r2) (.v t2)
  | .addCarry, [a, b, c] =>
    emit (.limb t1 t2 (.addCarry64 a b c))
    finishRaw64Big r1 (fc.varRep r1) (.v t1)
    finishRaw64Big r2 (fc.varRep r2) (.v t2)
  | .subBorrow, [a, b, c] =>
    emit (.limb t1 t2 (.subBorrow64 a b c))
    finishRaw64Big r1 (fc.varRep r1) (.v t1)
    finishRaw64Big r2 (fc.varRep r2) (.v t2)
  | _, _ => throw (.form f "limb pair arity mismatch")

/-- Strict raw 64-bit operand predicate for `lowerRepBig`: `true` ONLY when `a` is guaranteed
to be a raw 64-bit unsigned word `< 2^64` (NEVER a `.tobj` or `.obj` variable that could hold
an arbitrary-precision `BigNat ≥ 2^64`). -/
def isStrictWord64Arg (fc : Fir.Rep.FunCert) : Fir.Arg → Bool
  | .var y => fc.varRep y == .word
  | .lit (.nat n) => decide (n < 2 ^ 64)
  | _ => false

/-- Strict raw 64-bit comparison predicate for `lowerRepBig`: `true` ONLY when BOTH operands
are guaranteed `< 2^64` raw words/literals (never arbitrary-precision `Nat` values). -/
def cmpIsStrictWord64 (fc : Fir.Rep.FunCert) (a b : Fir.Arg) : Bool :=
  isStrictWord64Arg fc a && isStrictWord64Arg fc b

/-- Evaluate numeric operand `a` as a canonical Phase 4 `NatVal` (promoting `.word` via
`promoteRaw64ToNatVal` and normalizing `.obj` via `objToNatVal`). -/
def operandNatValBig (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) (a : Fir.Arg) : M Lir.Arg :=
  match a with
  | .var y =>
    match fc.varRep y with
    | .word => do
      let r ← freshReg
      promoteRaw64ToNatVal r (.v y)
      pure (.v r)
    | .obj => do
      let r ← freshReg
      objToNatVal r (.v y)
      pure (.v r)
    | .tobj | .erased => pure (.v y)
  | _ => operandBig f sc bc a

def operandsNatValBig (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) : List Fir.Arg → M (List Lir.Arg)
  | [] => pure []
  | a :: as => do
    let la ← operandNatValBig f fc sc bc a
    let las ← operandsNatValBig f fc sc bc as
    pure (la :: las)

/-- Convert operand `a` to the representation expected by narrow `wordBig` (`w ≠ .w64`),
respecting `fc.varRep y` (`.word` → `retag`, `.obj` → `unbox64OrBigNat` + `retag`,
`.tobj` → as-is). Never passes raw even `.word`s or 16-byte `box64` cells to `natValLow64`. -/
def operandNarrowRepBig (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) (a : Fir.Arg) : M Lir.Arg :=
  match a with
  | .var y =>
    match fc.varRep y with
    | .word => temp (retag (.v y))
    | .obj => do
      let u ← freshReg
      unbox64OrBigNat u (.v y)
      temp (retag (.v u))
    | .tobj | .erased => pure (.v y)
  | _ => operandBig f sc bc a

def operandsNarrowRepBig (f : FunId) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) : List Fir.Arg → M (List Lir.Arg)
  | [] => pure []
  | a :: as => do
    let la ← operandNarrowRepBig f fc sc bc a
    let las ← operandsNarrowRepBig f fc sc bc as
    pure (la :: las)

/-- Primitive lowering for `lowerRepBig` (ZERO `.fail .natOverflow`):
* `.word .w64 op` / widening `.convert .w64`: raw 64-bit ALU + `finishRaw64Big` (with narrowing
  `.convert w'` retagging into `.tobj`/`.obj`, NEVER `box64`!);
* narrow `.word w op`: `operandsNarrowRepBig` + `wordBig`;
* strict raw 64-bit `UInt64` comparisons (`cmpIsStrictWord64`): direct unsigned `select`;
* ALL 16 arbitrary-precision `Nat` primitives: `operandsNatValBig` + `Dispatch.primitiveBig`! -/
def primitiveRepBig (f : FunId) (T : Tables) (procs : BigNatProcs) (fc : Fir.Rep.FunCert)
    (sc : StrCtx) (bc : BigNatLitCtx) (x : VReg) (op : Lam.Prim) (as : List Fir.Arg) : M Unit :=
  let rx := fc.varRep x
  match op with
  | .word .w64 wo =>
    match wo with
    | .toNat =>
      match as with
      | [a] => do
        let la ← operandRaw64Big f fc a
        finishRaw64Big x rx la
      | _ => throw (.prim f (.word .w64 .toNat))
    | .convert w' =>
      if w' == .w64 then
        match as with
        | [a] => do
          let la ← operandRaw64Big f fc a
          finishRaw64Big x rx la
        | _ => throw (.prim f (.word .w64 (.convert .w64)))
      else
        match as with
        | [a] => do
          let la ← operandRaw64Big f fc a
          let m ← bin .and la (.imm (UInt64.ofNat (w'.size - 1)))
          match rx with
          | .word => assign x (.arg m)
          | .tobj | .obj => assign x (retag m)
          | .erased => assign x (.arg m)
        | _ => throw (.prim f (.word .w64 (.convert w')))
    | _ => do
      let las ← operandsRaw64Big f fc as
      if rx == .word then
        wordRaw64 f x wo las
      else
        let tmp ← freshReg
        wordRaw64 f tmp wo las
        finishRaw64Big x rx (.v tmp)
  | .word w (.convert .w64) => do
    match ← operandsRaw64Big f fc as with
    | [a] => finishRaw64Big x rx a
    | _ => throw (.prim f (.word w (.convert .w64)))
  | .word w wo => do
    let las ← operandsNarrowRepBig f fc sc bc as
    if rx == .word then
      let tmp ← freshReg
      wordBig f tmp w wo las
      natValLow64 x (.v tmp)
    else
      wordBig f x w wo las
  | op =>
    match compareOf op, as with
    | some cond, [a, b] =>
      if cmpIsStrictWord64 fc a b then do
        let [la, lb] ← operandsRaw64Big f fc [a, b] | throw (.prim f op)
        let some (t, e) := T.bools | throw (.noBool f)
        assign x (.select cond .w64 la lb (.imm t) (.imm e))
      else do
        let las ← operandsNatValBig f fc sc bc [a, b]
        primitiveBig f { bools := T.bools, procs } x op las
    | _, _ => do
      let las ← operandsNatValBig f fc sc bc as
      primitiveBig f { bools := T.bools, procs } x op las

/-- Allocation lowering for `lowerRepBig` (DR3 arrays + scalar tails + big `Nat` literals,
ZERO `.fail .natOverflow`). -/
def allocRepBig (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (x : VReg) (c : Fir.CtorInfo) (as : List Fir.Arg)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) (liveAfter : Src.NatSet) : M Unit := do
  if rc.enabled && cert.arrayMkKey == some c.key then
    match as with
    | [xs] =>
      let callee := rc.arrBase +
        if cert.arrayMkKind == .limbs then Rt.Rc.Array.fnArrOfListLimbs
        else Rt.Rc.Array.fnArrOfListBoxed
      let [lxs] ← operandsAtRepsBig f fc [xs] [.obj] sc bc | pure ()
      emit (.call [x] callee [lxs])
    | _ => throw (.form f s!"Array.mk expected 1 field, got {as.length}")
  else if rc.enabled && cert.byteArrayMkKey == some c.key then
    match as with
    | [arr] =>
      let [larr] ← operandsAtRepsBig f fc [arr] [.obj] sc bc | pure ()
      emit (.call [x] (rc.arrBase + Rt.Rc.Array.fnByteArrOfArr) [larr])
    | _ => throw (.form f s!"ByteArray.mk expected 1 field, got {as.length}")
  else
    if isNatKey T c.key then throw (.layout f "a Nat constructor cell (Nat values are literals)")
    let some baseInfo := Fir.CtorInfo.ofKey T.ctors c.key
      | throw (.form f "allocation key outside the table")
    let (nobj, nscalar, fieldReps) : Nat × Nat × List Fir.Rep := match cert.ctorRep? c.key with
      | some cr =>
        (cr.nobj, cr.nscalar, List.replicate cr.nobj cr.objRep ++ List.replicate cr.nscalar Fir.Rep.word)
      | none =>
        (c.nobj, c.nscalar, List.replicate c.nobj Fir.Rep.tobj ++ List.replicate c.nscalar Fir.Rep.word)
    let totalArity := nobj + nscalar
    if as.length != totalArity || totalArity != baseInfo.arity then
      throw (.form f s!"an allocation of {as.length} fields for {totalArity}")
    if baseInfo.tag > maxTag then throw (.layout f s!"constructor tag {baseInfo.tag} above {maxTag}")
    if totalArity == 0 then
      assign x (.arg (.imm (ctor0Word baseInfo.tag)))
    else
      if totalArity > maxFields then throw (.layout f s!"{totalArity} fields, above {maxFields}")
      emitIncCallArgs rc fc liveAfter as (List.replicate nobj true ++ List.replicate nscalar false)
      let las ← operandsAtRepsBig f fc as fieldReps sc bc
      if las.any (· == .v x) then throw (.form f "an allocation reads the variable it defines")
      assign x (.load .w64 .zero (ctxAt bumpOff))
      let e ← freshReg
      assign e (.addr (mem x (cellBytes totalArity)))
      let l ← temp (.load .w64 .zero (ctxAt limitOff))
      check .heap fun ok bad => .br .ugt (.v e) l bad ok
      emit (.store .w64 (ctxAt bumpOff) (.v e))
      emit (.store .w32 (mem x 0) (.imm (UInt64.ofNat (headerLow nobj 0 baseInfo.tag))))
      emit (.store .w32 (mem x 4) (.imm (UInt64.ofNat immortalRc)))
      las.zipIdx.forM fun (a, i) => emit (.store .w64 (mem x (fieldOffset i)) a)

/-- Projection lowering for `lowerRepBig`: `Nat.succ` peel uses `Dispatch.natSuccPeelBig`. -/
def projRepBig (f : FunId) (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (x y : VReg) (c : Key.CtorKey) (i : Nat)
    (rc : RcCtx) (liveAfter : Src.NatSet) (liveTerm : Src.NatSet)
    (rest : List Cfg.Instr) : M Unit := do
  if rc.enabled && cert.arrayMkKey == some c && i == 0 then
    let callee := rc.arrBase +
      if cert.arrayMkKind == .limbs then Rt.Rc.Array.fnArrToListLimbs
      else Rt.Rc.Array.fnArrToListBoxed
    emit (.call [x] callee [.v y])
  else if rc.enabled && cert.byteArrayMkKey == some c && i == 0 then
    emit (.call [x] (rc.arrBase + Rt.Rc.Array.fnByteArrToArr) [.v y])
  else if T.known.natSucc == some c then
    if i == 0 then natSuccPeelBig procs x y
    else throw (.form f "a projection past the Nat successor's field")
  else if T.known.natZero == some c then throw (.form f "a projection of Nat.zero")
  else
    match Fir.CtorInfo.ofKey T.ctors c with
    | some info =>
      if i < info.arity then
        let fr := cert.fieldRep c i
        let rx := fc.varRep x
        if fr == .word && rx == .obj then
          let tmp ← freshReg
          assign tmp (.load .w64 .zero (mem y (fieldOffset i)))
          box64 x (.v tmp)
        else if fr == .word && rx == .tobj then
          let tmp ← freshReg
          assign tmp (.load .w64 .zero (mem y (fieldOffset i)))
          promoteRaw64ToNatVal x (.v tmp)
        else if fr != .word && rx == .word then
          let tmp ← freshReg
          assign tmp (.load .w64 .zero (mem y (fieldOffset i)))
          unbox64OrBigNat x (.v tmp)
        else
          assign x (.load .w64 .zero (mem y (fieldOffset i)))
          if rc.enabled && rx != .word && (rc.tainted.contains x || rc.tainted.contains y) &&
              liveAfter.contains y &&
              (liveTerm.contains y || hasConflictProjUse y c i rest) then
            emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v x])
      else throw (.form f s!"field {i} of a constructor with {info.arity}")
    | none => throw (.form f "a projection key outside the table")

def instrRepBig (f : FunId) (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (ins : Cfg.Instr) (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx)
    (liveAfter : Src.NatSet) (liveTerm : Src.NatSet) (rest : List Cfg.Instr) : M Unit :=
  match ins with
  | .bind x (.fir (.arg a)) => do
    match a with
    | .var y =>
      if rc.enabled && fc.varRep y != .word && liveAfter.contains y &&
          (rc.tainted.contains x || rc.tainted.contains y) then
        emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])
    | _ => pure ()
    let la ← operandAtRepBig f fc a (fc.varRep x) sc bc
    assign x (.arg la)
  | .bind x (.fir (.prim op as)) => primitiveRepBig f T procs fc sc bc x op as
  | .bind x (.fir (.call g as)) => do
    let gc := cert.funCert g
    let mutFlags := rc.paramMut.getD g (List.replicate as.length true)
    emitIncCallArgs rc fc liveAfter as mutFlags
    let las ← operandsAtRepsBig f fc as gc.params sc bc
    let rx := fc.varRep x
    if gc.ret == .word && rx == .obj then
      let tmp ← freshReg
      emit (.call [tmp] g las)
      box64 x (.v tmp)
    else if gc.ret == .word && rx == .tobj then
      let tmp ← freshReg
      emit (.call [tmp] g las)
      promoteRaw64ToNatVal x (.v tmp)
    else
      emit (.call [x] g las)
  | .bind _ (.fir (.ctor ..)) => throw (.form f "a Fir constructor in Cfg")
  | .bind _ (.fir (.proj ..)) => throw (.form f "a Fir projection in Cfg")
  | .bind x (.alloc c as _) => allocRepBig f T cert fc x c as sc bc rc liveAfter
  | .bind x (.proj y c i) => projRepBig f T procs cert fc x y c i rc liveAfter liveTerm rest

def instrsRepBigAnn (f : FunId) (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx)
    (liveTerm : Src.NatSet) : List (Cfg.Instr × Src.NatSet) → M Unit
  | [] => pure ()
  | [(i, la)] => instrRepBig f T procs cert fc i sc bc rc la liveTerm []
  | (i1, la1) :: (i2, la2) :: rest =>
    match matchLimbPair i1 i2 with
    | some (kind, r1, r2, as) => do
      emitLimbPairBig f fc kind r1 r2 as
      instrsRepBigAnn f T procs cert fc sc bc rc liveTerm rest
    | none => do
      let restInstrs := i2 :: rest.map (·.1)
      instrRepBig f T procs cert fc i1 sc bc rc la1 liveTerm restInstrs
      instrsRepBigAnn f T procs cert fc sc bc rc liveTerm ((i2, la2) :: rest)

def pureOperandAtRepBig (f : FunId) (fc : Fir.Rep.FunCert) (a : Fir.Arg) (expected : Fir.Rep)
    (sc : StrCtx) (bc : BigNatLitCtx) : Except Error (Option Lir.Arg) :=
  match expected with
  | .word =>
    match a with
    | .var y => if fc.varRep y == .word then pure (some (.v y)) else pure none
    | .lit (.nat n) => pure (some (.imm (UInt64.ofNat (n % 2 ^ 64))))
    | .lit (.str _) => throw (.string f)
    | .erased => pure (some (.imm 0))
  | .tobj =>
    match a with
    | .var y => if fc.varRep y == .word then pure none else pure (some (.v y))
    | _ => pureOperandBig f sc bc a
  | .obj =>
    match a with
    | .var y => if fc.varRep y == .word then pure none else pure (some (.v y))
    | _ => pureOperandBig f sc bc a
  | .erased => pure (some (.imm erasedWord))

def pureOperandsAtRepsBig (f : FunId) (fc : Fir.Rep.FunCert)
    (as : List Fir.Arg) (rs : List Fir.Rep) (sc : StrCtx) (bc : BigNatLitCtx) :
    Except Error (Option (List Lir.Arg)) :=
  match as with
  | [] => pure (some [])
  | a :: as => do
    match ← pureOperandAtRepBig f fc a (rs.headD .tobj) sc bc with
    | none => pure none
    | some la =>
      match ← pureOperandsAtRepsBig f fc as rs.tail sc bc with
      | none => pure none
      | some las => pure (some (la :: las))

def edgeRepBig (f : FunId) (fc : Fir.Rep.FunCert) (blockReps : Src.NatMap (List Fir.Rep))
    (src : Nat) (e : Cfg.Edge) (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : M PEdge := do
  unless e.back == decide (e.target ≤ src) do throw (.edgeOrder f src)
  let targetReps := blockReps.getD e.target (List.replicate e.args.length .tobj)
  let incVars := edgeIncVars fc rc e
  let pureRes ← if incVars.isEmpty then pureOperandsAtRepsBig f fc e.args targetReps sc bc else pure none
  match pureRes with
  | some las => pure ⟨.blk e.target, las⟩
  | none =>
    let saved ← get
    let tramp ← newLabel
    modify fun st => { st with cur := tramp, params := [], acc := [] }
    incVars.forM fun y => emit (.call [] (rc.arrBase + Rt.Rc.Array.fnIncVal) [.v y])
    let las ← operandsAtRepsBig f fc e.args targetReps sc bc
    close (.jump ⟨.blk e.target, las⟩)
    modify fun st => { st with cur := saved.cur, params := saved.params, acc := saved.acc }
    pure (loc tramp)

def switchAltRepBig (f : FunId) (T : Tables) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (ke : Key.CtorKey × Cfg.Edge)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : M (KeyKind × PEdge) := do
  let some kind := keyKind T ke.1 | throw (.switch f src "a key outside the constructor table")
  pure (kind, ← edgeRepBig f fc blockReps src ke.2 sc bc rc)

def switchRepBig (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (x : VReg)
    (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : M Unit := do
  match alts, d with
  | [(k, e)], none =>
    if rc.enabled && (cert.arrayMkKey == some k || cert.byteArrayMkKey == some k) then
      close (.jump (← edgeRepBig f fc blockReps src e sc bc rc))
      return
  | _, _ => pure ()
  let es ← alts.mapM (switchAltRepBig f T fc blockReps src · sc bc rc)
  let dd ← d.mapM (edgeRepBig f fc blockReps src · sc bc rc)
  let nats := es.filter (·.1.isNat)
  if !nats.isEmpty then
    unless nats.length == es.length do throw (.switch f src "Nat keys mixed with other keys")
    natSwitch x es dd
  else tagSwitch x es dd

def termRepBig (f : FunId) (T : Tables) (cert : Fir.Rep.Cert) (fc : Fir.Rep.FunCert)
    (blockReps : Src.NatMap (List Fir.Rep)) (src : Nat) (t : Cfg.Term)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : M Unit :=
  match t with
  | .jump e => do close (.jump (← edgeRepBig f fc blockReps src e sc bc rc))
  | .switch x alts d => switchRepBig f T cert fc blockReps src x alts d sc bc rc
  | .ret a => do close (.ret (← operandAtRepBig f fc a fc.ret sc bc))
  | .tcall g as => do
    let gc := cert.funCert g
    let mutFlags := rc.paramMut.getD g (List.replicate as.length true)
    emitIncCallArgs rc fc .leaf as mutFlags
    let las ← operandsAtRepsBig f fc as gc.params sc bc
    close (.tail g las)
  | .trap => close .trap

private def liveAtTermBig (liveIn : Src.NatMap Src.NatSet) (b : Cfg.Block) : Src.NatSet :=
  let fromEdges : Src.NatSet := b.term.edges.foldl (init := .leaf) fun s e =>
    (liveIn.getD e.target .leaf).toList.foldl (fun acc (k, _) => acc.insert k) s
  (Cfg.Check.termVars b.term).foldl (fun s x => s.insert x) fromEdges

def blockCodeRepBig (f : FunId) (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (blockReps : Src.NatMap (List Fir.Rep)) (uses : Src.NatMap Nat)
    (src : Nat) (b : Cfg.Block) (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : M Unit :=
  let lt := if rc.enabled then liveAtTermBig rc.liveIn b else .leaf
  -- Only fuse strict raw 64-bit `.word` comparisons (NEVER arbitrary-precision `Nat` comparisons!)
  match fusable T uses b with
  | some (init, c, a, a') =>
    if cmpIsStrictWord64 fc a a' then do
      let lt' := (Cfg.Check.argVars [a, a']).foldl (fun s x => s.insert x) lt
      let ann := if rc.enabled then annotateBody lt' init else init.map (·, .leaf)
      instrsRepBigAnn f T procs cert fc sc bc rc lt ann
      let [la, la'] ← operandsRaw64Big f fc [a, a'] | throw (.internal f "raw cmp arity")
      match b.term with
      | .switch _ alts d =>
        let te ← (boolEdge alts d T.known.boolTrue).mapM (edgeRepBig f fc blockReps src · sc bc rc)
        let fe ← (boolEdge alts d T.known.boolFalse).mapM (edgeRepBig f fc blockReps src · sc bc rc)
        fusedClose c la la' te fe
      | t => termRepBig f T cert fc blockReps src t sc bc rc
    else do
      let ann := if rc.enabled then annotateBody lt b.body else b.body.map (·, .leaf)
      instrsRepBigAnn f T procs cert fc sc bc rc lt ann
      termRepBig f T cert fc blockReps src b.term sc bc rc
  | none => do
    let ann := if rc.enabled then annotateBody lt b.body else b.body.map (·, .leaf)
    instrsRepBigAnn f T procs cert fc sc bc rc lt ann
    termRepBig f T cert fc blockReps src b.term sc bc rc

def blockRepBig (f : FunId) (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (blockReps : Src.NatMap (List Fir.Rep)) (uses : Src.NatMap Nat)
    (src : Nat) (entry : Bool) (b : Cfg.Block)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : M Unit := do
  openAt 0 (if entry then [] else b.params.map (·.1))
  blockCodeRepBig f T procs cert fc blockReps uses src b sc bc rc

def chunksRepBig (f : FunId) (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (fc : Fir.Rep.FunCert) (blockReps : Src.NatMap (List Fir.Rep)) (uses : Src.NatMap Nat)
    (merged : Bool) (bs : List (Cfg.Block × Nat)) (fresh : VReg)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    Except Error (List (List PBlock) × VReg) :=
  match bs with
  | [] => pure ([], fresh)
  | (b, i) :: bs => do
    let ((), st) ← (blockRepBig f T procs cert fc blockReps uses i (merged && i == 0) b sc bc rc).run { fresh }
    let blocks ← chunkBlocks f st
    let (rest, fresh) ← chunksRepBig f T procs cert fc blockReps uses merged bs st.fresh sc bc rc
    pure (blocks :: rest, fresh)

def toRawWordParamBig (reg : VReg) (rep : Fir.Rep) : M Lir.Arg :=
  match rep with
  | .word => pure (.v reg)
  | .tobj => do
    let r ← freshReg
    natValLow64 r (.v reg)
    pure (.v r)
  | .obj => do
    let r ← freshReg
    unbox64OrBigNat r (.v reg)
    pure (.v r)
  | .erased => pure (.imm 0)

/-- Convert a `Nat` index/offset/length/capacity parameter to a raw 64-bit word,
saturating any `BigNat` cell (`≥ 2^63`, `tag = 0x7F03`) to `0xFFFFFFFFFFFFFFFF`
instead of truncating mod `2^64`. (Separate from `toRawWordParamBig`, used for
`UInt64`/`UInt8` payloads.) -/
def toRawIndexBig (reg : VReg) (rep : Fir.Rep) : M Lir.Arg :=
  match rep with
  | .word => pure (.v reg)
  | .tobj => do
    let r ← freshReg
    natValSaturate64 r (.v reg)
    pure (.v r)
  | .obj => do
    let r ← freshReg
    unbox64OrSaturateBigNat r (.v reg)
    pure (.v r)
  | .erased => pure (.imm 0)

def paramRegRepBig (f : FunId) (params : List VReg) (fc : Fir.Rep.FunCert) (idx : Nat) :
    M (VReg × Fir.Rep) := do
  let some reg := params[idx]? | throw (.form f s!"array prim param index {idx} out of range")
  pure (reg, fc.params.getD idx .tobj)

/-- Monadic body for `arrayPrimFuncBig` (ZERO `.fail .natOverflow`). -/
def arrayPrimBody (arrBase : FunId) (f : FunId) (params : List VReg) (fc : Fir.Rep.FunCert)
    (spec : Fir.Rep.ArrayPrimSpec) : M Unit := do
  openAt 0 []
  match spec.op, spec.argIdx with
  | .emptyCap, [] =>
    let callee := arrBase + match spec.kind with
      | .boxed => Rt.Rc.Array.fnEmptyCapBoxed
      | .limbs => Rt.Rc.Array.fnEmptyCapLimbs
      | .bytes => Rt.Rc.Array.fnByteEmptyCap
    let res ← freshReg
    emit (.call [res] callee [.imm 0])
    close (.ret (.v res))
  | .emptyCap, [ci] =>
    let (creg, crep) ← paramRegRepBig f params fc ci
    let cap ← toRawIndexBig creg crep
    let callee := arrBase + match spec.kind with
      | .boxed => Rt.Rc.Array.fnEmptyCapBoxed
      | .limbs => Rt.Rc.Array.fnEmptyCapLimbs
      | .bytes => Rt.Rc.Array.fnByteEmptyCap
    let res ← freshReg
    emit (.call [res] callee [cap])
    close (.ret (.v res))
  | .size, [ai] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let raw ← freshReg
    emit (.call [raw] (arrBase + Rt.Rc.Array.fnSize) [.v areg])
    if fc.ret == .word then
      close (.ret (.v raw))
    else
      let out ← freshReg
      promoteRaw64ToNatVal out (.v raw)
      close (.ret (.v out))
  | .get, [ai, ii] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let (ireg, irep) ← paramRegRepBig f params fc ii
    let idx ← toRawIndexBig ireg irep
    match spec.kind with
    | .bytes =>
      let raw ← freshReg
      emit (.call [raw] (arrBase + Rt.Rc.Array.fnByteGet) [.v areg, idx])
      if fc.ret == .word then close (.ret (.v raw))
      else
        let out ← temp (retag (.v raw))
        close (.ret out)
    | .limbs =>
      let raw ← freshReg
      emit (.call [raw] (arrBase + Rt.Rc.Array.fnGetWord) [.v areg, idx])
      let out ← freshReg
      finishRaw64Big out fc.ret (.v raw)
      close (.ret (.v out))
    | .boxed =>
      let res ← freshReg
      emit (.call [res] (arrBase + Rt.Rc.Array.fnGetWord) [.v areg, idx])
      emit (.call [] (arrBase + Rt.Rc.Array.fnIncVal) [.v res])
      if fc.ret == .word then
        let out ← freshReg
        unbox64OrBigNat out (.v res)
        close (.ret (.v out))
      else
        close (.ret (.v res))
  | .getBang, [ai, ii] =>
    unless spec.kind == .bytes do
      throw (.form f "array prim getBang is only supported for ByteArray (.bytes)")
    let (areg, _) ← paramRegRepBig f params fc ai
    let (ireg, irep) ← paramRegRepBig f params fc ii
    let idx ← toRawIndexBig ireg irep
    let sz ← freshReg
    emit (.call [sz] (arrBase + Rt.Rc.Array.fnSize) [.v areg])
    let inB ← newLabel
    let oobB ← newLabel
    close (.br .ult idx (.v sz) (loc inB) (loc oobB))
    openAt inB []
    let raw ← freshReg
    emit (.call [raw] (arrBase + Rt.Rc.Array.fnByteGet) [.v areg, idx])
    if fc.ret == .word then close (.ret (.v raw))
    else
      let out ← temp (retag (.v raw))
      close (.ret out)
    openAt oobB []
    if fc.ret == .word then close (.ret (.imm 0))
    else close (.ret (.imm (UInt64.ofNat 1)))
  | .set, [ai, ii, vi] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let (ireg, irep) ← paramRegRepBig f params fc ii
    let (vreg, vrep) ← paramRegRepBig f params fc vi
    let idx ← toRawIndexBig ireg irep
    let res ← freshReg
    match spec.kind with
    | .bytes =>
      let b ← toRawWordParamBig vreg vrep
      emit (.call [res] (arrBase + Rt.Rc.Array.fnByteSet) [.v areg, idx, b])
    | .limbs =>
      let w ← toRawWordParamBig vreg vrep
      emit (.call [res] (arrBase + Rt.Rc.Array.fnSetLimbs) [.v areg, idx, w])
    | .boxed =>
      let va ← if vrep == .word then do
          let b ← freshReg; box64 b (.v vreg); pure (.v b)
        else pure (.v vreg)
      emit (.call [res] (arrBase + Rt.Rc.Array.fnSetBoxed) [.v areg, idx, va])
    close (.ret (.v res))
  | .push, [ai, vi] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let (vreg, vrep) ← paramRegRepBig f params fc vi
    let res ← freshReg
    match spec.kind with
    | .bytes =>
      let b ← toRawWordParamBig vreg vrep
      emit (.call [res] (arrBase + Rt.Rc.Array.fnBytePush) [.v areg, b])
    | .limbs =>
      let w ← toRawWordParamBig vreg vrep
      emit (.call [res] (arrBase + Rt.Rc.Array.fnPushLimbs) [.v areg, w])
    | .boxed =>
      let va ← if vrep == .word then do
          let b ← freshReg; box64 b (.v vreg); pure (.v b)
        else pure (.v vreg)
      emit (.call [res] (arrBase + Rt.Rc.Array.fnPushBoxed) [.v areg, va])
    close (.ret (.v res))
  | .pop, [ai] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let callee := arrBase + match spec.kind with
      | .boxed => Rt.Rc.Array.fnPopBoxed
      | .limbs => Rt.Rc.Array.fnPopLimbs
      | .bytes => Rt.Rc.Array.fnBytePop
    let res ← freshReg
    emit (.call [res] callee [.v areg])
    close (.ret (.v res))
  | .extract, [ai, bi, ei] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let (breg, brep) ← paramRegRepBig f params fc bi
    let (ereg, erep) ← paramRegRepBig f params fc ei
    let bRaw ← toRawIndexBig breg brep
    let eRaw ← toRawIndexBig ereg erep
    let callee := arrBase + match spec.kind with
      | .boxed => Rt.Rc.Array.fnExtractBoxed
      | .limbs => Rt.Rc.Array.fnExtractLimbs
      | .bytes => Rt.Rc.Array.fnByteExtract
    let res ← freshReg
    emit (.call [res] callee [.v areg, bRaw, eRaw])
    close (.ret (.v res))
  | .copySlice, [si, soi, di, doi, li] =>
    let (sreg, _) ← paramRegRepBig f params fc si
    let (soreg, sorep) ← paramRegRepBig f params fc soi
    let (dreg, _) ← paramRegRepBig f params fc di
    let (doreg, dorep) ← paramRegRepBig f params fc doi
    let (lreg, lrep) ← paramRegRepBig f params fc li
    let soRaw ← toRawIndexBig soreg sorep
    let doRaw ← toRawIndexBig doreg dorep
    let lRaw ← toRawIndexBig lreg lrep
    let callee := arrBase + match spec.kind with
      | .boxed => Rt.Rc.Array.fnCopySliceBoxed
      | .limbs => Rt.Rc.Array.fnCopySliceLimbs
      | .bytes => Rt.Rc.Array.fnByteCopySlice
    let res ← freshReg
    emit (.call [res] callee [.v sreg, soRaw, .v dreg, doRaw, lRaw])
    close (.ret (.v res))
  | .swap, [ai, ii, ji] =>
    let (areg, _) ← paramRegRepBig f params fc ai
    let (ireg, irep) ← paramRegRepBig f params fc ii
    let (jreg, jrep) ← paramRegRepBig f params fc ji
    let iRaw ← toRawIndexBig ireg irep
    let jRaw ← toRawIndexBig jreg jrep
    let callee := arrBase + match spec.kind with
      | .limbs => Rt.Rc.Array.fnSwapLimbs
      | _ => Rt.Rc.Array.fnSwapBoxed
    let res ← freshReg
    emit (.call [res] callee [.v areg, iRaw, jRaw])
    close (.ret (.v res))
  | _, _ => throw (.form f "array prim spec arity mismatch")

/-- Zero-`natOverflow` DR3 native array primitive wrapper for `lowerRepBig` (uses
`promoteRaw64ToNatVal` / `finishRaw64Big` / `toRawWordParamBig`). -/
def arrayPrimFuncBig (arrBase : FunId) (f : FunId) (fd : Cfg.Fun) (fc : Fir.Rep.FunCert)
    (spec : Fir.Rep.ArrayPrimSpec) (conv : Lir.Conv) : Except Error Lir.Func := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
  let params := b0.params.map (·.1)
  let supply := max fd.vars (maxVar fd + 1)
  let ((), st) ← (arrayPrimBody arrBase f params fc spec).run { fresh := supply }
  let pblocks ← chunkBlocks f st
  let (starts, _) := chunkStarts 0 [pblocks]
  let raw ← resolveChunks f starts [(pblocks, 0)]
  let seen := reachable raw
  unless reachClosed raw seen do throw (.internal f "array prim wrapper has unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

def functionRawRepBig (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (f : FunId) (fd : Cfg.Fun) (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) :
    Except Error (List VReg × List Lir.Block) := do
  let some b0 := fd.blocks.head? | throw (.missingBlock f 0)
  if let some b := misordered fd then throw (.edgeOrder f b)
  let fc := cert.funCert f
  let blockReps : Src.NatMap (List Fir.Rep) :=
    Src.NatMap.ofDense (fd.blocks.map fun b => b.params.map fun (v, _) => fc.varRep v)
  let rcFun : RcCtx :=
    if !rc.enabled then rc
    else
      { rc with
        tainted := computeTainted fd rc.paramMut
        liveIn := computeLiveIn fd
        blockParams := Src.NatMap.ofDense (fd.blocks.map fun b => b.params.map (·.1)) }
  let merged := !(fd.blocks.any fun b => b.term.edges.any (·.target == 0))
  let supply := max fd.vars (maxVar fd + 1)
  let arity := b0.params.length
  let (params, supply) :=
    if merged then (b0.params.map (·.1), supply)
    else ((List.range arity).map (supply + ·), supply + arity)
  let uses := useCounts fd
  let (cs, _) ← chunksRepBig f T procs cert fc blockReps uses merged fd.blocks.zipIdx supply sc bc rcFun
  let (starts, _) := chunkStarts (if merged then 0 else 1) cs
  let body ← resolveChunks f starts cs.zipIdx
  let entry : List Lir.Block :=
    if merged then [] else [{ term := .jump { target := starts.getD 0 1, args := params.map .v } }]
  pure (params, entry ++ body)

def functionRepBig (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (f : FunId) (fd : Cfg.Fun) (conv : Lir.Conv)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : Except Error Lir.Func := do
  if rc.enabled then
    match cert.arrayPrims.get? f with
    | some spec => return ← arrayPrimFuncBig rc.arrBase f fd (cert.funCert f) spec conv
    | none => pure ()
  let (params, raw) ← functionRawRepBig T procs cert f fd sc bc rc
  let seen := reachable raw
  unless reachClosed raw seen do throw (.internal f "a reached block has an unreached successor")
  pure (Lir.Func.splitCriticalEdges
    { name := s!"f{f}", params, results := 1, blocks := (pruneWith seen raw).toArray, conv })

def functionsRepBig (T : Tables) (procs : BigNatProcs) (cert : Fir.Rep.Cert)
    (P : Cfg.Program) (roots : List (FunId × String)) (fs : List Nat)
    (sc : StrCtx) (bc : BigNatLitCtx) (rc : RcCtx) : Except Error (List Lir.Func) :=
  match fs with
  | [] => pure []
  | f :: fs => do
    let some fd := P.fun? f | throw (.missingFun f)
    let conv := match roots.lookup f with
      | some s => .sysvExport s
      | none => .internal
    pure ((← functionRepBig T procs cert f fd conv sc bc rc) ::
      (← functionsRepBig T procs cert P roots fs sc bc rc))

/-- **Phase 4 Arbitrary-Precision `Nat` + DR1/DR2/DR3/DR4 Lowering (`lowerRepBig`)**:
Full production lowering combining `Fir.Rep.Cert` (raw 64-bit `UInt64`, DR3 contiguous
arrays, DR4 UTF-8 strings) with arbitrary-precision `Nat` (`Dispatch.primitiveBig`,
`natSuccPeelBig`, `.rodata` / `bigNatLitProc` `≥ 2^63` literals, `Rt.Procs.natPowBig`,
`Rt.Procs.natGcdBig`, and the compiled pure-Lean `IxCC.BigNat.Entry` library `lib`). -/
def lowerRepBig (cfg : Config) (lib : CompiledBigNatLib) (cert : Fir.Rep.Cert)
    (P : Cfg.Program) : Except Error Lowered := do
  let some main := P.exports.head? | throw .noExports
  if let some (f, _) := P.funs.toList.find? (P.size ≤ ·.1) then throw (.funRange f)
  let named := P.exports.zipIdx.map fun (f, i) => (f, symbolOf ((cfg.names[i]?).getD s!"root{i}"))
  let roots := named.map fun (f, s) => (f, (named.lookup f).getD s)
  let T := tables P
  let initId := P.size
  let natPowId := P.size + 1
  let natGcdId := P.size + 2
  let hasArr := cert.hasArrays
  let arrBase := P.size + 3
  let arrProcs : List Lir.Func :=
    if hasArr then Rt.Rc.Array.extendedArrayRuntimeFuncs arrBase cert.listNilTag cert.listConsTag
    else []
  let rc : RcCtx :=
    if hasArr then { enabled := true, arrBase, paramMut := computeParamMutates P cert }
    else {}
  let litBase := arrBase + arrProcs.length
  let strs := LowerStr.collectStrings P
  let nats := collectBigNats P
  let (sc, bc, litProcs, rodata, rodataExports) := buildLiteralContexts cfg strs nats litBase
  let libBase := litBase + litProcs.length
  let relocLib := lib.relocate libBase
  let wrapBase := libBase + relocLib.length
  let (wrappers, procs, slowPowId, slowGcdId) ←
    buildCoreWrappers lib libBase wrapBase natPowId natGcdId T.bools
  let funcs ← functionsRepBig T procs cert P roots (List.range P.size) sc bc rc
  let allFuncs :=
    funcs ++ [Procs.cxInit, Procs.natPowBig slowPowId, Procs.natGcdBig slowGcdId] ++
    arrProcs ++ litProcs ++ relocLib ++ wrappers
  pure
    { program := { funcs := allFuncs.toArray, main }
    , init := initId
    , natPow := natPowId
    , natGcd := natGcdId
    , roots
    , rodata
    , rodataExports }

end IxCC.Rt.BigNat
