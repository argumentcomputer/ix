import IxCC.Lir.Opt.Sym
import IxCC.Lir.Graph
import IxCC.Src.NatMap

/-!
# Validated Lir SSA translation validator (`Lir.Opt.check`)

A small, linear-time, kernel-evaluable translation validator for `Lir`
optimizations, split cleanly into:

1. **Trusted validator** (`checkFuncWithPlan`, `checkProgramWithPlan`):
   given a `ProgPlan` (target block map + per-block relational invariants
   `BlockInv`), verifies every reachable block independently by:
   - Splitting block bodies at `.call` statements into local straight-line segments.
   - Symbolically executing each source segment and target segment against a
     shared `SnapTable`, checking every target operation's safety (defined
     operands, readable/writable addresses proven by source execution, nonzero
     divisors/`bsr64`) and final byte-level memory equivalence (`symMemEquiv`).
   - Verifying terminators (including constant/fact/interval branch folding,
     non-overflowing `brOvf` folding, and hoisted `.fail` guards) and edges
     (including preheader / hoisted-guard hops and clock preservation).
2. **Untrusted plan inference** (`inferFuncPlan`, `inferProgPlan`):
   reconstructs `ProgPlan` directly from `(p, q)` using a dominator-guided
   abstract fixpoint so `Lir.Opt.check : Program → Program → Bool` needs no
   external certificate!

Soundness (`IxCC.Lir.Proof.Opt.Sim`) proves `checkProgramWithPlan_sim` for
*any* plan accepted by the trusted validator, so `inferProgPlan` is completely
outside the TCB.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word)

/-! ## Block invariants and verification plans -/

/-- Relational invariant at a block entry (or immediately after a `.call`).
All expressions and facts are memory-free (`isMemFree = true`). -/
structure BlockInv where
  /-- Source registers guaranteed defined in `ρ₁`. -/
  srcDef : List VReg := []
  /-- Target register bindings `(y, e)`: `e` is total/mem-free and `ρ₂[y] = eval e ρ₁`. -/
  tgtOf : List (VReg × SymExpr) := []
  /-- Source register equalities `(x, e)`: `ρ₁[x] = eval e ρ₁`. -/
  srcEq : List (VReg × SymExpr) := []
  /-- Known dominating branch facts over `ρ₁`. -/
  facts : List PFact := []
  deriving DecidableEq, Repr, Inhabited

/-- Verification plan for one reachable block of `F`. -/
structure BlockPlan where
  target : Label
  entryInv : BlockInv
  afterCalls : List BlockInv := []
  deriving DecidableEq, Repr, Inhabited

/-- Verification plan for one function `F → G`. -/
structure FuncPlan where
  blocks : Array (Option BlockPlan)
  deriving DecidableEq, Repr, Inhabited

/-- Verification plan for a whole program `p → q`. -/
structure ProgPlan where
  funcs : Array FuncPlan
  deriving DecidableEq, Repr, Inhabited

/-! ## Splitting a block body into call-free segments -/

/-- A `.call` statement paired with the non-call segment immediately following it. -/
structure CallSplit where
  rs : List VReg
  fn : FunId
  args : List Arg
  after : List Stmt
  deriving DecidableEq, Repr, Inhabited

def splitByCallsAux (acc : List Stmt) : List Stmt → List Stmt × List CallSplit
  | [] => (acc.reverse, [])
  | .call rs f as :: rest =>
      let (seg1, more) := splitByCallsAux [] rest
      (acc.reverse, { rs, fn := f, args := as, after := seg1 } :: more)
  | s :: rest => splitByCallsAux (s :: acc) rest

/-- Split a block body into `(firstSeg, callSplits)`. Every statement in `firstSeg`
and in each `c.after` is a non-call local statement. -/
def splitByCalls (stmts : List Stmt) : List Stmt × List CallSplit :=
  splitByCallsAux [] stmts

/-! ## Segment symbolic state -/

/-- Symbolic state during verification of one straight-line segment. -/
structure SegState where
  /-- Source register expressions over segment-entry `ρ₁⁰` (missing key `x` means `.reg x`). -/
  srcEnv : Src.NatMap SymExpr := .leaf
  /-- Source registers known defined in current `ρ₁`. -/
  srcDef : Src.NatSet := .leaf
  /-- Target register expressions over segment-entry `ρ₁⁰`. -/
  tgtEnv : Src.NatMap SymExpr := .leaf
  /-- Dominating facts over segment-entry `ρ₁⁰` (all mem-free). -/
  facts : List PFact := []
  /-- Normalized write logs for source and target in this segment. -/
  smem1 : SymMem := []
  smem2 : SymMem := []
  /-- Shared append-only snapshot table for this segment. -/
  snaps : SnapTable := SnapTable.init
  /-- Memory accesses and partial ops proven safe by `F`'s execution of `seg₁`. -/
  safeReads : List (Width × SymExpr) := []
  safeWrites : List (Width × SymExpr) := []
  safeDivs : List (Width × SymExpr) := []
  safeBsrs : List SymExpr := []
  safeDivWides : List (SymExpr × SymExpr) := []

/-- Look up a source register in `m`, defaulting to `.reg x`. -/
def srcLookup (m : Src.NatMap SymExpr) (x : VReg) : SymExpr :=
  m.getD x (.reg x)

/-- Look up a target register in `m` (returns `none` if not guaranteed defined). -/
def tgtLookup (m : Src.NatMap SymExpr) (y : VReg) : Option SymExpr :=
  m.get? y

/-- Check if `inv` has only memory-free expressions and facts. -/
def BlockInv.isMemFree (inv : BlockInv) : Bool :=
  inv.tgtOf.all (fun (_, e) => e.isMemFree) &&
  inv.srcEq.all (fun (_, e) => e.isMemFree) &&
  inv.facts.all PFact.isMemFree

/-- Initialize segment symbolic state from a block-entry `BlockInv`.
Target register expressions and path facts are substituted through `srcEnv` (derived
from `inv.srcEq`) so source and target symbolic expressions share canonical names
(essential for loop-invariant block parameters and constant/copy-propagated entries). -/
def SegState.ofInv (inv : BlockInv) : SegState :=
  let srcEnv := Src.NatMap.ofList (inv.srcEq.map fun (x, e) => (x, e.norm))
  let sub := srcLookup srcEnv
  { srcEnv
    srcDef := Src.NatSet.ofList inv.srcDef
    tgtEnv := Src.NatMap.ofList (inv.tgtOf.map fun (y, e) => (y, (e.subst sub).norm))
    facts := inv.facts.map fun f =>
      { f with lhs := f.lhs.subst sub, rhs := f.rhs.subst sub } }

/-! ## Stepping source statements -/

def stepSrcRhs (st : SegState) : Rhs → SymExpr × SegState
  | .arg a => ((argToSym (srcLookup st.srcEnv) a).norm, st)
  | .bin o w a b =>
      let ea := (argToSym (srcLookup st.srcEnv) a).norm
      let eb := (argToSym (srcLookup st.srcEnv) b).norm
      let e := mkBin o w ea eb
      let safeDivs := if o == .udiv || o == .urem then (w, eb) :: st.safeDivs else st.safeDivs
      (e, { st with safeDivs })
  | .load w ext m =>
      let addr := (addrToSym (srcLookup st.srcEnv) m).norm
      let ca := toConstAddr (srcLookup st.srcEnv) m
      let (e, snaps') := SymMem.read st.smem1 st.snaps w ext addr ca
      (e.norm, { st with snaps := snaps', safeReads := (w, addr) :: st.safeReads })
  | .addr m => ((addrToSym (srcLookup st.srcEnv) m).norm, st)
  | .select c w a b t f =>
      let e := SymExpr.norm (.select c w
        (argToSym (srcLookup st.srcEnv) a) (argToSym (srcLookup st.srcEnv) b)
        (argToSym (srcLookup st.srcEnv) t) (argToSym (srcLookup st.srcEnv) f))
      (e, st)
  | .test c w a b =>
      let e := SymExpr.norm (.test c w
        (argToSym (srcLookup st.srcEnv) a) (argToSym (srcLookup st.srcEnv) b))
      (e, st)
  | .bsr64 a =>
      let ea := (argToSym (srcLookup st.srcEnv) a).norm
      ((SymExpr.bsr64 ea).norm, { st with safeBsrs := ea :: st.safeBsrs })

def stepSrcLimb (st : SegState) : LimbOp → SymExpr × SymExpr × SegState
  | .mulWide64 a b =>
      let ea := (argToSym (srcLookup st.srcEnv) a).norm
      let eb := (argToSym (srcLookup st.srcEnv) b).norm
      (mkBin .mul .w64 ea eb, (SymExpr.mulHi ea eb).norm, st)
  | .divWide64 hi lo d =>
      let ehi := (argToSym (srcLookup st.srcEnv) hi).norm
      let elo := (argToSym (srcLookup st.srcEnv) lo).norm
      let ed := (argToSym (srcLookup st.srcEnv) d).norm
      ((SymExpr.divQ ehi elo ed).norm, (SymExpr.divR ehi elo ed).norm,
       { st with safeDivWides := (ehi, ed) :: st.safeDivWides })
  | .addCarry64 a b c =>
      let ea := (argToSym (srcLookup st.srcEnv) a).norm
      let eb := (argToSym (srcLookup st.srcEnv) b).norm
      let ec := (argToSym (srcLookup st.srcEnv) c).norm
      ((SymExpr.addCLo ea eb ec).norm, (SymExpr.addCHi ea eb ec).norm, st)
  | .subBorrow64 a b c =>
      let ea := (argToSym (srcLookup st.srcEnv) a).norm
      let eb := (argToSym (srcLookup st.srcEnv) b).norm
      let ec := (argToSym (srcLookup st.srcEnv) c).norm
      ((SymExpr.subBLo ea eb ec).norm, (SymExpr.subBHi ea eb ec).norm, st)

/-- Symbolically step one non-call source statement. -/
def stepSrcStmt (st : SegState) : Stmt → SegState
  | .assign x r =>
      let (e, st') := stepSrcRhs st r
      { st' with srcEnv := st'.srcEnv.insert x e, srcDef := st'.srcDef.insert x }
  | .limb r1 r2 op =>
      let (e1, e2, st') := stepSrcLimb st op
      { st' with
        srcEnv := (st'.srcEnv.insert r1 e1).insert r2 e2
        srcDef := (st'.srcDef.insert r1).insert r2 }
  | .store w m a =>
      let addr := (addrToSym (srcLookup st.srcEnv) m).norm
      let ca := toConstAddr (srcLookup st.srcEnv) m
      let val := (argToSym (srcLookup st.srcEnv) a).norm
      { st with
        smem1 := SymMem.write st.smem1 w addr ca val
        safeWrites := (w, addr) :: st.safeWrites }
  | .call .. => st

def stepSrcList (st : SegState) : List Stmt → SegState
  | [] => st
  | s :: rest => stepSrcList (stepSrcStmt st s) rest

/-! ## Stepping target statements (with full safety checks) -/

def evalTgtArg (tgtEnv : Src.NatMap SymExpr) : Arg → Option SymExpr
  | .v y => tgtEnv.get? y
  | .imm w => some (.imm w)

def evalTgtArgs (tgtEnv : Src.NatMap SymExpr) : List Arg → Option (List SymExpr)
  | [] => some []
  | a :: rest => do
      let e ← evalTgtArg tgtEnv a
      let es ← evalTgtArgs tgtEnv rest
      some (e :: es)

def evalTgtAddr (tgtEnv : Src.NatMap SymExpr) (m : Addr) : Option (SymExpr × Option ConstAddr) := do
  let baseExpr ← match m.base with
    | none => some (.imm 0)
    | some .ctx => some .ctx
    | some (.v y) => tgtEnv.get? y
  let idxExpr ← match m.index with
    | none => some (.imm 0)
    | some (y, s) => do
        let ey ← tgtEnv.get? y
        some (mkBin .mul .w64 ey (.imm s.word))
  let sum1 := mkBin .add .w64 baseExpr idxExpr
  let addr := (mkBin .add .w64 sum1 (.imm (dispWord m.disp))).norm
  let ca : Option ConstAddr :=
    if m.index.isSome || !decide (-2147483648 ≤ m.disp ∧ m.disp < 2147483648) then none
    else
      let mb := match m.base with
        | none => MemBase.zero
        | some .ctx => MemBase.ctx
        | some (.v _) => MemBase.expr baseExpr.norm
      some ⟨mb, m.disp⟩
  some (addr, ca)

/-- Whether divisor `eb` at width `w` is guaranteed nonzero. -/
def isSafeDiv (st : SegState) (w : Width) (eb : SymExpr) : Bool :=
  (match eb with | .imm k => w.truncate k != 0 | _ => false) ||
  st.safeDivs.any (fun (w', d') => w' == w && exprEquiv d' eb) ||
  (w == .w64 && decide (0 < (rangeOf st.facts eb).lo))

/-- Whether `bsr64` operand `ea` is guaranteed nonzero. -/
def isSafeBsr (st : SegState) (ea : SymExpr) : Bool :=
  (match ea with | .imm k => k != 0 | _ => false) ||
  st.safeBsrs.any (fun a' => exprEquiv a' ea) ||
  decide (0 < (rangeOf st.facts ea).lo)

/-- Whether `divWide64 hi lo d` is guaranteed safe (`d ≠ 0 ∧ hi < d`). -/
def isSafeDivWide (st : SegState) (ehi ed : SymExpr) : Bool :=
  (match ehi, ed with
   | .imm hi, .imm d => d.toNat != 0 && decide (hi.toNat < d.toNat)
   | _, _ => false) ||
  st.safeDivWides.any (fun (hi', d') => exprEquiv hi' ehi && exprEquiv d' ed)

/-- Whether a target load at `(w, addr)` is guaranteed readable (executed by `F` in this segment). -/
def isSafeLoad (st : SegState) (w : Width) (addr : SymExpr) : Bool :=
  st.safeReads.any (fun (w', a') => w' == w && exprEquiv a' addr)

/-- Whether a target store at `(w, addr)` is guaranteed writable (executed by `F` in this segment). -/
def isSafeStore (st : SegState) (w : Width) (addr : SymExpr) : Bool :=
  st.safeWrites.any (fun (w', a') => w' == w && exprEquiv a' addr)

/-- Symbolically step one non-call target statement, checking full safety.
Returns `none` if any safety check fails. -/
def stepTgtStmt (st : SegState) : Stmt → Option SegState
  | .assign y r =>
      match r with
      | .arg a => do
          let ea ← evalTgtArg st.tgtEnv a
          some { st with tgtEnv := st.tgtEnv.insert y ea.norm }
      | .bin o w a b => do
          let ea ← evalTgtArg st.tgtEnv a
          let eb ← evalTgtArg st.tgtEnv b
          let ea' := ea.norm; let eb' := eb.norm
          if (o == .udiv || o == .urem) && !isSafeDiv st w eb' then none
          else some { st with tgtEnv := st.tgtEnv.insert y (mkBin o w ea' eb') }
      | .load w ext m => do
          let (addr, ca) ← evalTgtAddr st.tgtEnv m
          if !isSafeLoad st w addr then none
          else
            let (e, snaps') := SymMem.read st.smem2 st.snaps w ext addr ca
            some { st with tgtEnv := st.tgtEnv.insert y e.norm, snaps := snaps' }
      | .addr m => do
          let (addr, _) ← evalTgtAddr st.tgtEnv m
          some { st with tgtEnv := st.tgtEnv.insert y addr }
      | .select c w a b t f => do
          let ea ← evalTgtArg st.tgtEnv a
          let eb ← evalTgtArg st.tgtEnv b
          let et ← evalTgtArg st.tgtEnv t
          let ef ← evalTgtArg st.tgtEnv f
          some { st with tgtEnv := st.tgtEnv.insert y (SymExpr.norm (.select c w ea eb et ef)) }
      | .test c w a b => do
          let ea ← evalTgtArg st.tgtEnv a
          let eb ← evalTgtArg st.tgtEnv b
          some { st with tgtEnv := st.tgtEnv.insert y (SymExpr.norm (.test c w ea eb)) }
      | .bsr64 a => do
          let ea ← evalTgtArg st.tgtEnv a
          let ea' := ea.norm
          if !isSafeBsr st ea' then none
          else some { st with tgtEnv := st.tgtEnv.insert y (SymExpr.bsr64 ea').norm }
  | .limb r1 r2 op =>
      match op with
      | .mulWide64 a b => do
          let ea ← evalTgtArg st.tgtEnv a
          let eb ← evalTgtArg st.tgtEnv b
          let ea' := ea.norm; let eb' := eb.norm
          some { st with tgtEnv := (st.tgtEnv.insert r1 (mkBin .mul .w64 ea' eb')).insert r2 (SymExpr.mulHi ea' eb').norm }
      | .divWide64 hi lo d => do
          let ehi ← evalTgtArg st.tgtEnv hi
          let elo ← evalTgtArg st.tgtEnv lo
          let ed ← evalTgtArg st.tgtEnv d
          let ehi' := ehi.norm; let elo' := elo.norm; let ed' := ed.norm
          if !isSafeDivWide st ehi' ed' then none
          else some { st with
            tgtEnv := (st.tgtEnv.insert r1 (SymExpr.divQ ehi' elo' ed').norm).insert r2 (SymExpr.divR ehi' elo' ed').norm }
      | .addCarry64 a b c => do
          let ea ← evalTgtArg st.tgtEnv a
          let eb ← evalTgtArg st.tgtEnv b
          let ec ← evalTgtArg st.tgtEnv c
          let ea' := ea.norm; let eb' := eb.norm; let ec' := ec.norm
          some { st with
            tgtEnv := (st.tgtEnv.insert r1 (SymExpr.addCLo ea' eb' ec').norm).insert r2 (SymExpr.addCHi ea' eb' ec').norm }
      | .subBorrow64 a b c => do
          let ea ← evalTgtArg st.tgtEnv a
          let eb ← evalTgtArg st.tgtEnv b
          let ec ← evalTgtArg st.tgtEnv c
          let ea' := ea.norm; let eb' := eb.norm; let ec' := ec.norm
          some { st with
            tgtEnv := (st.tgtEnv.insert r1 (SymExpr.subBLo ea' eb' ec').norm).insert r2 (SymExpr.subBHi ea' eb' ec').norm }
  | .store w m a => do
      let (addr, ca) ← evalTgtAddr st.tgtEnv m
      let val ← evalTgtArg st.tgtEnv a
      if !isSafeStore st w addr then none
      else some { st with smem2 := SymMem.write st.smem2 w addr ca val.norm }
  | .call .. => none

def stepTgtList (st : SegState) : List Stmt → Option SegState
  | [] => some st
  | s :: rest => do
      let st' ← stepTgtStmt st s
      stepTgtList st' rest

/-- Symbolically step one pure total statement in a target preheader block (no calls,
no stores, no loads, no partial divisions/bsr). -/
def stepTotalTgtStmt (tgtEnv : Src.NatMap SymExpr) : Stmt → Option (Src.NatMap SymExpr)
  | .assign y r =>
      match r with
      | .arg a => do
          let ea ← evalTgtArg tgtEnv a
          some (tgtEnv.insert y ea.norm)
      | .bin o w a b => do
          let ea ← evalTgtArg tgtEnv a
          let eb ← evalTgtArg tgtEnv b
          let ea' := ea.norm; let eb' := eb.norm
          let ok := binOpIsTotal o || match eb' with | .imm k => w.truncate k != 0 | _ => false
          if !ok then none
          else some (tgtEnv.insert y (mkBin o w ea' eb'))
      | .addr m => do
          let (addr, _) ← evalTgtAddr tgtEnv m
          some (tgtEnv.insert y addr)
      | .select c w a b t f => do
          let ea ← evalTgtArg tgtEnv a
          let eb ← evalTgtArg tgtEnv b
          let et ← evalTgtArg tgtEnv t
          let ef ← evalTgtArg tgtEnv f
          some (tgtEnv.insert y (SymExpr.norm (.select c w ea eb et ef)))
      | .test c w a b => do
          let ea ← evalTgtArg tgtEnv a
          let eb ← evalTgtArg tgtEnv b
          some (tgtEnv.insert y (SymExpr.norm (.test c w ea eb)))
      | .bsr64 a => do
          let ea ← evalTgtArg tgtEnv a
          match ea.norm with
          | .imm k => if k != 0 then some (tgtEnv.insert y (.imm (UInt64.ofNat k.toNat.log2))) else none
          | _ => none
      | .load .. => none
  | .limb r1 r2 op =>
      match op with
      | .mulWide64 a b => do
          let ea ← evalTgtArg tgtEnv a
          let eb ← evalTgtArg tgtEnv b
          let ea' := ea.norm; let eb' := eb.norm
          some ((tgtEnv.insert r1 (mkBin .mul .w64 ea' eb')).insert r2 (SymExpr.mulHi ea' eb').norm)
      | .addCarry64 a b c => do
          let ea ← evalTgtArg tgtEnv a
          let eb ← evalTgtArg tgtEnv b
          let ec ← evalTgtArg tgtEnv c
          let ea' := ea.norm; let eb' := eb.norm; let ec' := ec.norm
          some ((tgtEnv.insert r1 (SymExpr.addCLo ea' eb' ec').norm).insert r2 (SymExpr.addCHi ea' eb' ec').norm)
      | .subBorrow64 a b c => do
          let ea ← evalTgtArg tgtEnv a
          let eb ← evalTgtArg tgtEnv b
          let ec ← evalTgtArg tgtEnv c
          let ea' := ea.norm; let eb' := eb.norm; let ec' := ec.norm
          some ((tgtEnv.insert r1 (SymExpr.subBLo ea' eb' ec').norm).insert r2 (SymExpr.subBHi ea' eb' ec').norm)
      | .divWide64 .. => none
  | .store .. | .call .. => none

def stepTotalTgtList (tgtEnv : Src.NatMap SymExpr) : List Stmt → Option (Src.NatMap SymExpr)
  | [] => some tgtEnv
  | s :: rest => do
      let tgtEnv' ← stepTotalTgtStmt tgtEnv s
      stepTotalTgtList tgtEnv' rest

/-- Verify one straight-line segment `(seg1, seg2)` starting from `inv`, checking safety
and exact final memory equivalence. Returns the post-segment `SegState` on success. -/
def checkSeg (inv : BlockInv) (seg1 seg2 : List Stmt) : Option SegState := do
  let st0 := SegState.ofInv inv
  let st1 := stepSrcList st0 seg1
  let st2 ← stepTgtList st1 seg2
  if symMemEquiv st2.smem1 st2.smem2 then some st2 else none

/-! ## Checking arguments, calls, entailment, edges, and terminators -/

/-- Check that source argument `a1` and target argument `a2` evaluate to the same word. -/
def checkArgEquiv (st : SegState) (a1 a2 : Arg) : Bool :=
  match evalTgtArg st.tgtEnv a2 with
  | none => false
  | some e2 => exprEquiv (argToSym (srcLookup st.srcEnv) a1) e2

/-- Check pairwise equivalence of argument lists. -/
def checkArgsEquiv (st : SegState) : List Arg → List Arg → Bool
  | [], [] => true
  | a1 :: r1, a2 :: r2 => checkArgEquiv st a1 a2 && checkArgsEquiv st r1 r2
  | _, _ => false

/-- Parallel binding of `params` to `vals` into a `NatMap`. -/
def bindNatMap (m : Src.NatMap SymExpr) : List VReg → List SymExpr → Src.NatMap SymExpr
  | [], _ => m
  | _, [] => m
  | x :: xs, e :: es => bindNatMap (m.insert x e) xs es

/-- Insert a list of registers into a `NatSet`. -/
def insertDefs (s : Src.NatSet) : List VReg → Src.NatSet
  | [] => s
  | x :: xs => insertDefs (s.insert x) xs

/-- Check that a post-edge state `(srcEnv1, srcDef1, tgtEnv1, allFacts)` entails `tgtInv`. -/
def checkEntails (srcEnv1 : Src.NatMap SymExpr) (srcDef1 : Src.NatSet)
    (tgtEnv1 : Src.NatMap SymExpr) (allFacts : List PFact) (tgtInv : BlockInv) : Bool :=
  tgtInv.isMemFree &&
  tgtInv.srcDef.all srcDef1.contains &&
  tgtInv.tgtOf.all (fun (y, expr) =>
    expr.isTotal &&
    expr.vars.all srcDef1.contains &&
    match tgtEnv1.get? y with
    | none => false
    | some ty => exprEquiv (expr.subst (srcLookup srcEnv1)) ty) &&
  tgtInv.srcEq.all (fun (x, expr) =>
    expr.isTotal &&
    srcDef1.contains x &&
    expr.vars.all srcDef1.contains &&
    exprEquiv (srcLookup srcEnv1 x) (expr.subst (srcLookup srcEnv1))) &&
  tgtInv.facts.all (fun f =>
    let lhs' := f.lhs.subst (srcLookup srcEnv1)
    let rhs' := f.rhs.subst (srcLookup srcEnv1)
    condFromFacts allFacts f.cond f.width lhs' rhs' == some f.result)

/-- Check that a post-call invariant `postInv` holds after `.call rs g as` returns any `vals`
of length `rs.length` into both `ρ₁` and `ρ₂`. -/
def checkAfterCall (st : SegState) (rs : List VReg) (postInv : BlockInv) : Bool :=
  postInv.isMemFree &&
  postInv.srcDef.all (fun x => rs.contains x || st.srcDef.contains x) &&
  postInv.tgtOf.all (fun (y, expr) =>
    if expr == .reg y && rs.contains y then true
    else
      !rs.contains y &&
      expr.isTotal &&
      expr.vars.all (fun v => !rs.contains v && st.srcDef.contains v) &&
      match st.tgtEnv.get? y with
      | none => false
      | some ty => exprEquiv (expr.subst (srcLookup st.srcEnv)) ty) &&
  postInv.srcEq.all (fun (x, expr) =>
    !rs.contains x &&
    expr.isTotal &&
    st.srcDef.contains x &&
    expr.vars.all (fun v => !rs.contains v && st.srcDef.contains v) &&
    exprEquiv (srcLookup st.srcEnv x) (expr.subst (srcLookup st.srcEnv))) &&
  postInv.facts.all (fun f =>
    f.vars.all (fun v => !rs.contains v) &&
    let lhs' := f.lhs.subst (srcLookup st.srcEnv)
    let rhs' := f.rhs.subst (srcLookup st.srcEnv)
    condFromFacts st.facts f.cond f.width lhs' rhs' == some f.result)

/-- Whether edge `e` jumps with no args to an immediate `.fail r` block (no params, empty body). -/
def isFailEdge (G : Func) (e : Edge) : Bool :=
  e.args.isEmpty &&
  match G.blocks[e.target]? with
  | some b =>
      b.params.isEmpty && b.body.isEmpty &&
      match b.term with | .fail _ => true | _ => false
  | none => false

/-- Check that source edge `e` (from `L`) is matched by target edge `e'` (from `curL'`),
possibly traversing pure total preheader blocks and/or hoisted `.fail` guards (up to `fuel` hops).
`needCharge` tracks whether a back-edge charge is still required along the target hop chain. -/
def checkEdge (F G : Func) (plan : FuncPlan) (srcEnv : Src.NatMap SymExpr) (srcDef : Src.NatSet)
    (tgtEnv : Src.NatMap SymExpr) (allFacts : List PFact)
    (curL' : Label) (needCharge : Bool) (e e' : Edge) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    match plan.blocks[e.target]?, F.blocks[e.target]? with
    | some (some bp), some fTgt =>
        let tgt' := bp.target
        let edgeCharged := decide (e'.target ≤ curL')
        if e'.target == tgt' then
          match G.blocks[tgt']?, evalTgtArgs tgtEnv e'.args with
          | some gTgt, some tArgs =>
              (!needCharge || edgeCharged) &&
              e.args.length == fTgt.params.length &&
              e'.args.length == gTgt.params.length &&
              let sArgs := e.args.map (fun a => (argToSym (srcLookup srcEnv) a).norm)
              let srcEnv1 := bindNatMap srcEnv fTgt.params sArgs
              let srcDef1 := insertDefs srcDef fTgt.params
              let tgtEnv1 := bindNatMap tgtEnv gTgt.params tArgs
              checkEntails srcEnv1 srcDef1 tgtEnv1 allFacts bp.entryInv
          | _, _ => false
        else
          -- Hop through a pure total preheader / hoisted-guard block `ph = e'.target`
          match G.blocks[e'.target]?, evalTgtArgs tgtEnv e'.args with
          | some phBlk, some tArgs =>
              if e'.args.length != phBlk.params.length then false
              else
                let tgtEnvPh0 := bindNatMap tgtEnv phBlk.params tArgs
                match stepTotalTgtList tgtEnvPh0 phBlk.body.toList with
                | none => false
                | some tgtEnvPh =>
                    let need' := needCharge && !edgeCharged
                    match phBlk.term with
                    | .jump e'' =>
                        checkEdge F G plan srcEnv srcDef tgtEnvPh allFacts e'.target need' e e'' fuel
                    | .br gc gw ga gb gt gf =>
                        match evalTgtArg tgtEnvPh ga, evalTgtArg tgtEnvPh gb with
                        | some ea, some eb =>
                            let ea' := ea.norm; let eb' := eb.norm
                            if isFailEdge G gf then
                              let extra := if ea'.isMemFree && eb'.isMemFree
                                then ({ cond := gc, width := gw, lhs := ea', rhs := eb', result := true } : PFact) :: allFacts
                                else allFacts
                              checkEdge F G plan srcEnv srcDef tgtEnvPh extra e'.target need' e gt fuel
                            else if isFailEdge G gt then
                              let extra := if ea'.isMemFree && eb'.isMemFree
                                then ({ cond := gc, width := gw, lhs := ea', rhs := eb', result := false } : PFact) :: allFacts
                                else allFacts
                              checkEdge F G plan srcEnv srcDef tgtEnvPh extra e'.target need' e gf fuel
                            else false
                        | _, _ => false
                    | _ => false
          | _, _ => false
    | _, _ => false

/-- Maximum preheader/guard hop depth allowed on an edge. -/
def maxEdgeHops : Nat := 8

/-- Check whether two branch conditions `(c1, w1, a1, b1)` and `(c2, w2, a2, b2)` are
equivalent (returning `some false` if identical, `some true` if negated). -/
def checkCondRelation (c1 : Cond) (w1 : Width) (a1 b1 : SymExpr)
    (c2 : Cond) (w2 : Width) (a2 b2 : SymExpr) : Option Bool :=
  if w1 != w2 then none
  else if exprEquiv a1 a2 && exprEquiv b1 b2 then
    if c1 == c2 then some false
    else if c1 == condNegate c2 then some true
    else none
  else if exprEquiv a1 b2 && exprEquiv b1 a2 then
    if c1 == condSwap c2 then some false
    else if c1 == condNegate (condSwap c2) then some true
    else none
  else none

/-- Helper: add a pure branch fact if both sides are memory-free. -/
def addFact (facts : List PFact) (c : Cond) (w : Width) (a b : SymExpr) (res : Bool) : List PFact :=
  let a' := a.norm; let b' := b.norm
  if a'.isMemFree && b'.isMemFree then
    { cond := c, width := w, lhs := a', rhs := b', result := res } :: facts
  else facts

/-- Verify terminator correspondence at the end of block `(L, L')`. -/
def checkTerm (F G : Func) (plan : FuncPlan) (L L' : Label) (st : SegState)
    (t1 t2 : Term) : Bool :=
  match t1, t2 with
  | .ret as1, .ret as2 => checkArgsEquiv st as1 as2
  | .tail g1 as1, .tail g2 as2 => g1 == g2 && checkArgsEquiv st as1 as2
  | .fail r1, .fail r2 => r1 == r2
  | .trap, .trap => true
  | .jump e1, .jump e2 =>
      checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv st.facts L' (decide (e1.target ≤ L)) e1 e2 maxEdgeHops
  | .jump e1, .br gc gw ga gb gt gf =>
      -- Hoisted invariant `.fail` guard inside an existing preheader block!
      match evalTgtArg st.tgtEnv ga, evalTgtArg st.tgtEnv gb with
      | some ea, some eb =>
          if isFailEdge G gf then
            let fs := addFact st.facts gc gw ea eb true
            checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv fs L' (decide (e1.target ≤ L)) e1 gt maxEdgeHops
          else if isFailEdge G gt then
            let fs := addFact st.facts gc gw ea eb false
            checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv fs L' (decide (e1.target ≤ L)) e1 gf maxEdgeHops
          else false
      | _, _ => false
  | .br c1 w1 a1 b1 t1 f1, .br c2 w2 a2 b2 t2 f2 =>
      match evalTgtArg st.tgtEnv a2, evalTgtArg st.tgtEnv b2 with
      | some ea2, some eb2 =>
          let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
          let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
          match checkCondRelation c1 w1 ea1 eb1 c2 w2 ea2 eb2 with
          | some false =>
              let fsT := addFact st.facts c1 w1 ea1 eb1 true
              let fsF := addFact st.facts c1 w1 ea1 eb1 false
              checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv fsT L' (decide (t1.target ≤ L)) t1 t2 maxEdgeHops &&
              checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv fsF L' (decide (f1.target ≤ L)) f1 f2 maxEdgeHops
          | some true =>
              let fsT := addFact st.facts c1 w1 ea1 eb1 true
              let fsF := addFact st.facts c1 w1 ea1 eb1 false
              checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv fsT L' (decide (t1.target ≤ L)) t1 f2 maxEdgeHops &&
              checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv fsF L' (decide (f1.target ≤ L)) f1 t2 maxEdgeHops
          | none => false
      | _, _ => false
  | .br c1 w1 a1 b1 t1 f1, .jump e2 =>
      let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
      let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
      match condFromFacts st.facts c1 w1 ea1 eb1 with
      | some true =>
          checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv st.facts L' (decide (t1.target ≤ L)) t1 e2 maxEdgeHops
      | some false =>
          checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv st.facts L' (decide (f1.target ≤ L)) f1 e2 maxEdgeHops
      | none =>
          if t1 == f1 then
            checkEdge F G plan st.srcEnv st.srcDef st.tgtEnv st.facts L' (decide (t1.target ≤ L)) t1 e2 maxEdgeHops
          else false
  | .brOvf o1 x1 a1 b1 ok1 ovf1, .brOvf o2 x2 a2 b2 ok2 ovf2 =>
      match evalTgtArg st.tgtEnv a2, evalTgtArg st.tgtEnv b2 with
      | some ea2, some eb2 =>
          let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
          let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
          o1 == o2 &&
          exprEquiv ea1 ea2 && exprEquiv eb1 eb2 &&
          let r1 := ovfToSym o1 ea1 eb1
          let r2 := ovfToSym o2 ea2.norm eb2.norm
          let srcEnv' := st.srcEnv.insert x1 r1
          let srcDef' := st.srcDef.insert x1
          let tgtEnv' := st.tgtEnv.insert x2 r2
          checkEdge F G plan srcEnv' srcDef' tgtEnv' st.facts L' (decide (ok1.target ≤ L)) ok1 ok2 maxEdgeHops &&
          checkEdge F G plan srcEnv' srcDef' tgtEnv' st.facts L' (decide (ovf1.target ≤ L)) ovf1 ovf2 maxEdgeHops
      | _, _ => false
  | .brOvf o1 x1 a1 b1 ok1 ovf1, .jump e2 =>
      let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
      let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
      let r1 := ovfToSym o1 ea1 eb1
      let srcEnv' := st.srcEnv.insert x1 r1
      let srcDef' := st.srcDef.insert x1
      match ovfFromFacts st.facts o1 ea1 eb1 with
      | some false =>
          checkEdge F G plan srcEnv' srcDef' st.tgtEnv st.facts L' (decide (ok1.target ≤ L)) ok1 e2 maxEdgeHops
      | some true =>
          checkEdge F G plan srcEnv' srcDef' st.tgtEnv st.facts L' (decide (ovf1.target ≤ L)) ovf1 e2 maxEdgeHops
      | none =>
          if ok1 == ovf1 then
            checkEdge F G plan srcEnv' srcDef' st.tgtEnv st.facts L' (decide (ok1.target ≤ L)) ok1 e2 maxEdgeHops
          else false
  | _, _ => false

/-- Verify a block's call chain and final terminator starting from segment 0's `st`. -/
def checkCallsAndTerm (F G : Func) (plan : FuncPlan) (L L' : Label) (t1 t2 : Term)
    (st : SegState) : List CallSplit → List CallSplit → List BlockInv → Bool
  | [], [], [] => checkTerm F G plan L L' st t1 t2
  | c1 :: rest1, c2 :: rest2, inv :: invs =>
      c1.fn == c2.fn &&
      c1.rs == c2.rs &&
      checkArgsEquiv st c1.args c2.args &&
      checkAfterCall st c1.rs inv &&
      match checkSeg inv c1.after c2.after with
      | none => false
      | some st' => checkCallsAndTerm F G plan L L' t1 t2 st' rest1 rest2 invs
  | _, _, _ => false

/-- Verify one planned block `L` of `F` against `bp.target` of `G`. -/
def checkBlock (F G : Func) (plan : FuncPlan) (L : Label) (bp : BlockPlan) : Bool :=
  match F.blocks[L]?, G.blocks[bp.target]? with
  | some b1, some b2 =>
      bp.entryInv.isMemFree &&
      let (seg1, calls1) := splitByCalls b1.body.toList
      let (seg2, calls2) := splitByCalls b2.body.toList
      match checkSeg bp.entryInv seg1 seg2 with
      | none => false
      | some st => checkCallsAndTerm F G plan L bp.target b1.term b2.term st calls1 calls2 bp.afterCalls
  | _, _ => false

/-- Check that `entryInv` is valid for any function entry state `bindParams {} F.params vals`. -/
def checkEntryInv (params : List VReg) (inv : BlockInv) : Bool :=
  inv.isMemFree &&
  inv.srcEq.isEmpty &&
  inv.facts.isEmpty &&
  inv.srcDef.all params.contains &&
  inv.tgtOf.all (fun (y, e) => e == .reg y && params.contains y)

/-- Trusted validator for a single function pair `(F, G)` given `plan`. -/
def checkFuncWithPlan (F G : Func) (plan : FuncPlan) : Bool :=
  G.params == F.params &&
  G.results == F.results &&
  G.conv == F.conv &&
  plan.blocks.size == F.blocks.size &&
  (match F.blocks[0]?, G.blocks[0]?, plan.blocks[0]? with
   | some fb0, some gb0, some (some bp0) =>
       fb0.params.isEmpty && gb0.params.isEmpty &&
       bp0.target == 0 && checkEntryInv F.params bp0.entryInv
   | _, _, _ => false) &&
  (List.range F.blocks.size).all fun L =>
    match plan.blocks[L]? with
    | some (some bp) => checkBlock F G plan L bp
    | some none => true
    | none => false

/-- Trusted validator for a whole program pair `(p, q)` given `plan`. -/
def checkProgramWithPlan (p q : Program) (plan : ProgPlan) : Bool :=
  q.main == p.main &&
  q.funcs.size == p.funcs.size &&
  plan.funcs.size == p.funcs.size &&
  (List.range p.funcs.size).all fun fi =>
    match p.funcs[fi]?, q.funcs[fi]?, plan.funcs[fi]? with
    | some F, some G, some fplan => checkFuncWithPlan F G fplan
    | _, _, _ => false

/-! ## Untrusted plan inference (outside the TCB) -/

/-- Whether block `L` of `F` has any back-edge predecessor (`p ≥ L` with `L ∈ succs p`). -/
private def hasBackPred (F : Func) (L : Label) : Bool :=
  (List.range F.blocks.size).any fun p =>
    decide (L ≤ p) && (match F.blocks[p]? with | some b => b.term.succs.contains L | none => false)

/-- Follow pure preheader / hoisted-guard blocks in `G` from `start` until reaching a block
with a back-edge predecessor (or stop if not a pure preheader). -/
private def skipPreheader (G : Func) (needBack : Bool) : Nat → Label → Label
  | 0, l => l
  | fuel + 1, l =>
      if !needBack || hasBackPred G l then l
      else match G.blocks[l]? with
      | some b =>
          if b.body.any (fun | .store .. | .call .. => true | _ => false) then l
          else match b.term with
          | .jump e => if e.target > l then skipPreheader G needBack fuel e.target else l
          | .br _ _ _ _ t f =>
              if isFailEdge G f && t.target > l then skipPreheader G needBack fuel t.target
              else if isFailEdge G t && f.target > l then skipPreheader G needBack fuel f.target
              else l
          | _ => l
      | none => l

/-- Intersect two `BlockInv`s conservatively at a control-flow merge point. -/
private def meetInv (a b : BlockInv) : BlockInv :=
  let bDef := Src.NatSet.ofList b.srcDef
  let srcDef := a.srcDef.filter bDef.contains
  let tgtOf := a.tgtOf.filter (fun p => b.tgtOf.contains p)
  let srcEq := a.srcEq.filter (fun p => b.srcEq.contains p)
  let facts := a.facts.filter (fun f => b.facts.contains f)
  { srcDef, tgtOf, srcEq, facts }

/-- Extract all registers defined in `F` strictly before or at each block (used as a
fast filter when building `BlockInv`s). -/
private def dedupList {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => if xs.contains x then dedupList xs else x :: dedupList xs

/-- Compute the set of source registers guaranteed defined on entry to each block `L`
(i.e. `F.params`, `F.blocks[L].params`, and all registers defined in strict dominators of `L`). -/
private def entryDomDefs (F : Func) : Array Src.NatSet :=
  let n := F.blocks.size
  let doms := F.dominators
  let blockDefs : Array (List VReg) := F.blocks.map fun blk =>
    let stmtDefs := blk.body.toList.flatMap (·.defs)
    let termDefs := match blk.term with | .brOvf _ x .. => [x] | _ => []
    blk.params ++ stmtDefs ++ termDefs
  (List.range n).toArray.map fun L =>
    let init := Src.NatSet.ofList (F.params ++ (F.blocks[L]?.map (·.params)).getD [])
    (List.range n).foldl (init := init) fun acc d =>
      if d != L && Lir.Func.dominates doms d L then
        (blockDefs[d]?.getD []).foldl (fun s x => Src.NatSet.insert s x) acc
      else acc

/-- Build a clean `BlockInv` from a post-edge symbolic state `(srcEnv, srcDef, tgtEnv, facts)`
for target block `L` (whose own `fTgt.params` were just bound), restricted to registers
dominating `L`'s entry (`domDef`) so loop-body temporaries do not pollute loop-header invariants. -/
private def buildEdgeInv (F : Func) (domDefs : Array Src.NatSet) (L : Label)
    (srcEnv : Src.NatMap SymExpr) (srcDef : Src.NatSet)
    (tgtEnv : Src.NatMap SymExpr) (facts : List PFact)
    (eArgsF : List Arg) (eArgsG : List Arg) (gParams : List VReg) : BlockInv :=
  let fParams := (F.blocks[L]?.map (·.params)).getD []
  let sArgs := eArgsF.map (fun a => (argToSym (srcLookup srcEnv) a).norm)
  let tArgs := eArgsG.filterMap (evalTgtArg tgtEnv)
  let srcEnv1 := bindNatMap srcEnv fParams sArgs
  let srcDefRaw := insertDefs srcDef fParams
  let domDef := domDefs[L]?.getD srcDefRaw
  let defListRaw : List VReg :=
    (srcDefRaw.toList.map Prod.fst).filter domDef.contains
  let fParamSet := Src.NatSet.ofList fParams
  -- Order non-params first (ascending) then params (ascending) so `findSrcReg` picks a
  -- canonical dominating register consistently across preheader and back-edges!
  let nonParams := (defListRaw.filter fun x => !fParamSet.contains x).mergeSort (· ≤ ·)
  let onlyParams := (defListRaw.filter fParamSet.contains).mergeSort (· ≤ ·)
  let defList : List VReg := nonParams ++ onlyParams
  let srcDef1 := Src.NatSet.ofList defList
  let tgtEnv1 := if tArgs.length == gParams.length then bindNatMap tgtEnv gParams tArgs else tgtEnv
  -- Map normalized symbolic expression (including loaded values!) back to a canonical source register `x ∈ srcDef1`
  let exprToSrc : List (SymExpr × VReg) :=
    defList.map fun x => ((srcLookup srcEnv1 x).norm, x)
  let findSrcReg (e : SymExpr) : Option VReg :=
    (exprToSrc.find? fun (se, _) => se == e).map (·.2)
  let isFixed (x : VReg) : Bool :=
    srcDef1.contains x && (srcLookup srcEnv1 x) == .reg x
  -- Helper: rewrite a symbolic expression (over old ρ₁⁰) into one over post-edge ρ₁
  let rec rewriteExpr : Nat → SymExpr → Option SymExpr
    | 0, _ => none
    | fuel + 1, e =>
        match e with
        | .imm w => some (.imm w)
        | .ctx => some .ctx
        | _ =>
          if e.isMemFree && e.vars.all isFixed then some e
          else match findSrcReg e with
          | some x => some (.reg x)
          | none =>
              match e with
              | .bin o w a b =>
                  if binOpIsTotal o || (match b with | .imm k => w.truncate k != 0 | _ => false) then do
                    let a' ← rewriteExpr fuel a
                    let b' ← rewriteExpr fuel b
                    some (mkBin o w a' b')
                  else none
              | .select c w a b t f => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                  let t' ← rewriteExpr fuel t; let f' ← rewriteExpr fuel f
                  some (SymExpr.norm (.select c w a' b' t' f'))
              | .test c w a b => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                  some (SymExpr.norm (.test c w a' b'))
              | .mulHi a b => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                  some (SymExpr.norm (.mulHi a' b'))
              | .addCLo a b c => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b; let c' ← rewriteExpr fuel c
                  some (SymExpr.norm (.addCLo a' b' c'))
              | .addCHi a b c => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b; let c' ← rewriteExpr fuel c
                  some (SymExpr.norm (.addCHi a' b' c'))
              | .subBLo a b c => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b; let c' ← rewriteExpr fuel c
                  some (SymExpr.norm (.subBLo a' b' c'))
              | .subBHi a b c => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b; let c' ← rewriteExpr fuel c
                  some (SymExpr.norm (.subBHi a' b' c'))
              | _ => none
  -- Build `tgtOf`: for every target register `(y, ty)` in `tgtEnv1`:
  -- 1. prefer `(y, .reg y)` if `y ∈ srcDef1` and `srcEnv1[y] == ty` (even for loaded/partial values!),
  -- 2. else if `ty` is total, memory-free, and refers only to fixed dominating registers, keep `ty`,
  -- 3. else rewrite `ty` into post-edge source registers (mapping loaded subexpressions via `exprToSrc`!).
  let tgtOf := tgtEnv1.toList.filterMap fun (y, ty) =>
    if srcDef1.contains y && exprEquiv (srcLookup srcEnv1 y) ty then
      some (y, SymExpr.reg y)
    else if ty.isTotal && ty.isMemFree && ty.vars.all isFixed then
      some (y, ty)
    else
      match rewriteExpr 6 ty with
      | some e => if e.isTotal && e.isMemFree && e.vars.all srcDef1.contains then some (y, e) else none
      | none => none
  -- Build `srcEq`: capture constants, copies, and invariant block params using a strict
  -- total order (`nonParams` ascending < `onlyParams` ascending) so `srcEq` is 1-step flat & acyclic!
  let ltOrder (a b : VReg) : Bool :=
    match fParamSet.contains a, fParamSet.contains b with
    | false, true => true
    | true, false => false
    | _, _ => a < b
  let srcEq := defList.filterMap fun x =>
    let sx := (srcLookup srcEnv1 x).norm
    match sx with
    | .imm k => some (x, SymExpr.imm k)
    | _ =>
        match defList.find? fun x0 => ltOrder x0 x && (srcLookup srcEnv1 x0).norm == sx with
        | some x0 => some (x, SymExpr.reg x0)
        | none => none
  -- Build `facts`: rewrite each fact into post-edge registers and keep only facts
  -- entailed by `condFromFacts facts` (avoiding impossible dead-branch contradictions).
  let newFacts := dedupList <| facts.filterMap fun f =>
    match rewriteExpr 4 f.lhs, rewriteExpr 4 f.rhs with
    | some l', some r' =>
        let ln := l'.norm; let rn := r'.norm
        if ln.isMemFree && rn.isMemFree && ln.vars.all srcDef1.contains && rn.vars.all srcDef1.contains &&
           condFromFacts facts f.cond f.width (ln.subst (srcLookup srcEnv1)) (rn.subst (srcLookup srcEnv1)) == some f.result then
          some { f with lhs := ln, rhs := rn }
        else none
    | _, _ => none
  { srcDef := defList, tgtOf, srcEq, facts := newFacts }

/-- Build a post-call `BlockInv` right after `.call rs g as` from `st`. -/
private def buildAfterCallInv (st : SegState) (rs : List VReg) : BlockInv :=
  let stDefList : List VReg := st.srcDef.toList.map Prod.fst
  let srcDef := dedupList (rs ++ stDefList)
  let retTgt := rs.map fun r => (r, SymExpr.reg r)
  let defList := (stDefList.filter fun x => !rs.contains x).mergeSort (· ≤ ·)
  let exprToSrc : List (SymExpr × VReg) :=
    defList.map fun x => ((srcLookup st.srcEnv x).norm, x)
  let findSrcReg (e : SymExpr) : Option VReg :=
    (exprToSrc.find? fun (se, _) => se == e).map (·.2)
  let rec rewriteExpr : Nat → SymExpr → Option SymExpr
    | 0, _ => none
    | fuel + 1, e =>
        match e with
        | .imm w => some (.imm w)
        | .ctx => some .ctx
        | _ =>
          match findSrcReg e with
          | some x => some (.reg x)
          | none =>
              match e with
              | .bin o w a b =>
                  if binOpIsTotal o || (match b with | .imm k => w.truncate k != 0 | _ => false) then do
                    let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                    some (mkBin o w a' b')
                  else none
              | .select c w a b t f => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                  let t' ← rewriteExpr fuel t; let f' ← rewriteExpr fuel f
                  some (SymExpr.norm (.select c w a' b' t' f'))
              | .test c w a b => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                  some (SymExpr.norm (.test c w a' b'))
              | .mulHi a b => do
                  let a' ← rewriteExpr fuel a; let b' ← rewriteExpr fuel b
                  some (SymExpr.norm (.mulHi a' b'))
              | _ => none
  let keptTgt := st.tgtEnv.toList.filterMap fun (y, ty) =>
    if rs.contains y then none
    else if st.srcDef.contains y && exprEquiv (srcLookup st.srcEnv y) ty then
      some (y, SymExpr.reg y)
    else
      match rewriteExpr 6 ty with
      | some e => if e.isTotal && e.isMemFree && e.vars.all (fun v => !rs.contains v && st.srcDef.contains v)
                  then some (y, e) else none
      | none => none
  let srcEq := defList.filterMap fun x =>
    let sx := (srcLookup st.srcEnv x).norm
    match sx with
    | .imm k => some (x, SymExpr.imm k)
    | _ =>
        match defList.find? fun x0 => x0 < x && (srcLookup st.srcEnv x0).norm == sx with
        | some x0 => some (x, SymExpr.reg x0)
        | none => none
  let facts := dedupList <| st.facts.filterMap fun f =>
    match rewriteExpr 4 f.lhs, rewriteExpr 4 f.rhs with
    | some l', some r' =>
        let ln := l'.norm; let rn := r'.norm
        if ln.isMemFree && rn.isMemFree &&
           ln.vars.all (fun v => !rs.contains v && st.srcDef.contains v) &&
           rn.vars.all (fun v => !rs.contains v && st.srcDef.contains v) &&
           condFromFacts st.facts f.cond f.width (ln.subst (srcLookup st.srcEnv)) (rn.subst (srcLookup st.srcEnv)) == some f.result then
          some { f with lhs := ln, rhs := rn }
        else none
    | _, _ => none
  { srcDef, tgtOf := retTgt ++ keptTgt, srcEq, facts }

/-- Advance along a single outgoing edge `(e1, e2)` during untrusted plan inference,
propagating `(targetLabel, edgeInv)` across any pure preheader / hoisted-guard hops. -/
private def inferEdgeTarget (F G : Func) (domDefs : Array Src.NatSet)
    (srcEnv : Src.NatMap SymExpr) (srcDef : Src.NatSet)
    (tgtEnv : Src.NatMap SymExpr) (facts : List PFact) (e1 e2 : Edge) :
    Nat → Option (Label × BlockInv)
  | 0 => none
  | fuel + 1 =>
      let needBack := hasBackPred F e1.target
      let dest := skipPreheader G needBack maxEdgeHops e2.target
      if e2.target == dest then
        match G.blocks[dest]? with
        | some gTgt =>
            some (dest, buildEdgeInv F domDefs e1.target srcEnv srcDef tgtEnv facts e1.args e2.args gTgt.params)
        | none => none
      else
        match G.blocks[e2.target]?, evalTgtArgs tgtEnv e2.args with
        | some phBlk, some tArgs =>
            if e2.args.length != phBlk.params.length then none
            else
              let tgtEnvPh0 := bindNatMap tgtEnv phBlk.params tArgs
              match stepTotalTgtList tgtEnvPh0 phBlk.body.toList with
              | none => none
              | some tgtEnvPh =>
                  match phBlk.term with
                  | .jump e'' => inferEdgeTarget F G domDefs srcEnv srcDef tgtEnvPh facts e1 e'' fuel
                  | .br gc gw ga gb gt gf =>
                      match evalTgtArg tgtEnvPh ga, evalTgtArg tgtEnvPh gb with
                      | some ea, some eb =>
                          if isFailEdge G gf then
                            let fs := addFact facts gc gw ea eb true
                            inferEdgeTarget F G domDefs srcEnv srcDef tgtEnvPh fs e1 gt fuel
                          else if isFailEdge G gt then
                            let fs := addFact facts gc gw ea eb false
                            inferEdgeTarget F G domDefs srcEnv srcDef tgtEnvPh fs e1 gf fuel
                          else none
                      | _, _ => none
                  | _ => none
        | _, _ => none

/-- Compute outgoing `(srcTarget, tgtTarget, edgeInv)` pairs for block `(L, L')` given
post-segment state `st`. -/
private def inferTermEdges (F G : Func) (domDefs : Array Src.NatSet) (st : SegState) (t1 t2 : Term) :
    List (Label × Label × BlockInv) :=
  let go (srcEnv : Src.NatMap SymExpr) (srcDef : Src.NatSet) (tgtEnv : Src.NatMap SymExpr)
      (facts : List PFact) (e1 e2 : Edge) : List (Label × Label × BlockInv) :=
    match inferEdgeTarget F G domDefs srcEnv srcDef tgtEnv facts e1 e2 maxEdgeHops with
    | some (tgt', inv) => [(e1.target, tgt', inv)]
    | none => []
  match t1, t2 with
  | .jump e1, .jump e2 => go st.srcEnv st.srcDef st.tgtEnv st.facts e1 e2
  | .jump e1, .br gc gw ga gb gt gf =>
      match evalTgtArg st.tgtEnv ga, evalTgtArg st.tgtEnv gb with
      | some ea, some eb =>
          if isFailEdge G gf then go st.srcEnv st.srcDef st.tgtEnv (addFact st.facts gc gw ea eb true) e1 gt
          else if isFailEdge G gt then go st.srcEnv st.srcDef st.tgtEnv (addFact st.facts gc gw ea eb false) e1 gf
          else []
      | _, _ => []
  | .br c1 w1 a1 b1 t1 f1, .br c2 w2 a2 b2 t2 f2 =>
      match evalTgtArg st.tgtEnv a2, evalTgtArg st.tgtEnv b2 with
      | some ea2, some eb2 =>
          let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
          let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
          let fsT := addFact st.facts c1 w1 ea1 eb1 true
          let fsF := addFact st.facts c1 w1 ea1 eb1 false
          match checkCondRelation c1 w1 ea1 eb1 c2 w2 ea2 eb2 with
          | some false =>
              go st.srcEnv st.srcDef st.tgtEnv fsT t1 t2 ++
              go st.srcEnv st.srcDef st.tgtEnv fsF f1 f2
          | some true =>
              go st.srcEnv st.srcDef st.tgtEnv fsT t1 f2 ++
              go st.srcEnv st.srcDef st.tgtEnv fsF f1 t2
          | none => []
      | _, _ => []
  | .br c1 w1 a1 b1 t1 f1, .jump e2 =>
      let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
      let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
      match condFromFacts st.facts c1 w1 ea1 eb1 with
      | some true => go st.srcEnv st.srcDef st.tgtEnv st.facts t1 e2
      | some false => go st.srcEnv st.srcDef st.tgtEnv st.facts f1 e2
      | none => if t1 == f1 then go st.srcEnv st.srcDef st.tgtEnv st.facts t1 e2 else []
  | .brOvf o1 x1 a1 b1 ok1 ovf1, .brOvf o2 x2 a2 b2 ok2 ovf2 =>
      match evalTgtArg st.tgtEnv a2, evalTgtArg st.tgtEnv b2 with
      | some ea2, some eb2 =>
          let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
          let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
          let srcEnv' := st.srcEnv.insert x1 (ovfToSym o1 ea1 eb1)
          let srcDef' := st.srcDef.insert x1
          let tgtEnv' := st.tgtEnv.insert x2 (ovfToSym o2 ea2.norm eb2.norm)
          go srcEnv' srcDef' tgtEnv' st.facts ok1 ok2 ++
          go srcEnv' srcDef' tgtEnv' st.facts ovf1 ovf2
      | _, _ => []
  | .brOvf o1 x1 a1 b1 ok1 ovf1, .jump e2 =>
      let ea1 := (argToSym (srcLookup st.srcEnv) a1).norm
      let eb1 := (argToSym (srcLookup st.srcEnv) b1).norm
      let srcEnv' := st.srcEnv.insert x1 (ovfToSym o1 ea1 eb1)
      let srcDef' := st.srcDef.insert x1
      match ovfFromFacts st.facts o1 ea1 eb1 with
      | some false => go srcEnv' srcDef' st.tgtEnv st.facts ok1 e2
      | some true => go srcEnv' srcDef' st.tgtEnv st.facts ovf1 e2
      | none => if ok1 == ovf1 then go srcEnv' srcDef' st.tgtEnv st.facts ok1 e2 else []
  | _, _ => []

/-- Run one block's segments and calls to infer `afterCalls` and the final `SegState`. -/
private def inferBlockCalls (inv : BlockInv) (seg1 seg2 : List Stmt)
    (calls1 calls2 : List CallSplit) : Option (List BlockInv × SegState) :=
  let rec go (st : SegState) (acc : List BlockInv) :
      List CallSplit → List CallSplit → Option (List BlockInv × SegState)
    | [], [] => some (acc.reverse, st)
    | c1 :: r1, c2 :: r2 =>
        let postInv := buildAfterCallInv st c1.rs
        let st1 := stepSrcList (SegState.ofInv postInv) c1.after
        match stepTgtList st1 c2.after with
        | some st2 => go st2 (postInv :: acc) r1 r2
        | none => none
    | _, _ => none
  let st1 := stepSrcList (SegState.ofInv inv) seg1
  match stepTgtList st1 seg2 with
  | some st2 => go st2 [] calls1 calls2
  | none => none

/-- Untrusted fixpoint inference of `FuncPlan` directly from `(F, G)`.
Starts from entry `(0, 0)` with `entryInv = F.params`, iterates over RPO blocks until
every block invariant reaches a fixpoint (bounded by fuel). -/
def inferFuncPlan (F G : Func) : FuncPlan :=
  let n := F.blocks.size
  if n == 0 || G.blocks.size == 0 then { blocks := Array.replicate n none }
  else
    let entryInv : BlockInv :=
      { srcDef := F.params
        tgtOf := F.params.map fun x => (x, .reg x)
        srcEq := []
        facts := [] }
    let initBlocks : Array (Option BlockPlan) :=
      (Array.replicate n none).set! 0 (some { target := 0, entryInv, afterCalls := [] })
    let domDefs := entryDomDefs F
    let order := F.rpo.toList
    let rec upsertEdge (xs : List ((Label × Nat) × BlockInv)) (k : Label × Nat) (v : BlockInv) :
        List ((Label × Nat) × BlockInv) :=
      match xs with
      | [] => [(k, v)]
      | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: upsertEdge rest k v
    let meetEdges : List ((Label × Nat) × BlockInv) → BlockInv
      | [] => { srcDef := [], tgtOf := [], srcEq := [], facts := [] }
      | (_, inv) :: rest => rest.foldl (fun acc (_, i) => meetInv acc i) inv
    let initInEdges : Array (List ((Label × Nat) × BlockInv)) := Array.replicate n []
    let pass (blocks : Array (Option BlockPlan)) (inEdges : Array (List ((Label × Nat) × BlockInv))) :
        Array (Option BlockPlan) × Array (List ((Label × Nat) × BlockInv)) × Bool :=
      order.foldl (init := (blocks, inEdges, false)) fun (cur, edges, changed) L =>
        match cur[L]?, F.blocks[L]? with
        | some (some bp), some b1 =>
            match G.blocks[bp.target]? with
            | none => (cur, edges, changed)
            | some b2 =>
                let (seg1, calls1) := splitByCalls b1.body.toList
                let (seg2, calls2) := splitByCalls b2.body.toList
                match inferBlockCalls bp.entryInv seg1 seg2 calls1 calls2 with
                | none => (cur, edges, changed)
                | some (afterCalls, stFinal) =>
                    let cur1 := if bp.afterCalls == afterCalls then cur
                      else cur.set! L (some { bp with afterCalls })
                    let ch1 := changed || (bp.afterCalls != afterCalls)
                    let outs := (inferTermEdges F G domDefs stFinal b1.term b2.term).zipIdx
                    outs.foldl (init := (cur1, edges, ch1)) fun (c, es, ch) ((tgt, tgt', edgeInv), eIdx) =>
                      if tgt < c.size then
                        let esTgt := upsertEdge es[tgt]! (L, eIdx) edgeInv
                        let es' := es.set! tgt esTgt
                        let merged := meetEdges esTgt
                        match c[tgt]! with
                        | none =>
                            (c.set! tgt (some { target := tgt', entryInv := merged, afterCalls := [] }), es', true)
                        | some old =>
                            if merged == old.entryInv then (c, es', ch)
                            else (c.set! tgt (some { old with entryInv := merged }), es', true)
                      else (c, es, ch)
        | _, _ => (cur, edges, changed)
    let rec fix : Nat → Array (Option BlockPlan) → Array (List ((Label × Nat) × BlockInv)) → Array (Option BlockPlan)
      | 0, bs, _ => bs
      | fuel + 1, bs, es =>
          let (bs', es', ch) := pass bs es
          if !ch then bs' else fix fuel bs' es'
    -- Bound iterations: each meet shrinks finite invariant sets; 8 * n + 8 is plenty and fast
    { blocks := fix (8 * n + 8) initBlocks initInEdges }

/-- Infer a `ProgPlan` for `(p, q)`. -/
def inferProgPlan (p q : Program) : ProgPlan :=
  { funcs := (List.range p.funcs.size).toArray.map fun fi =>
      match p.funcs[fi]?, q.funcs[fi]? with
      | some F, some G => inferFuncPlan F G
      | _, _ => { blocks := #[] } }

/-- **The formally validated Lir optimization checker.**
Accepts `(p, q)` only when the trusted validator `checkProgramWithPlan` accepts the
inferred relational proof plan. -/
def check (p q : Program) : Bool :=
  checkProgramWithPlan p q (inferProgPlan p q)

end IxCC.Lir.Opt
