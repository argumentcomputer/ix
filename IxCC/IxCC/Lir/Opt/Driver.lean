import IxCC.Lir.Opt.Check
import IxCC.Lir.Opt.Gvn
import IxCC.Lir.Opt.Licm
import IxCC.Lir.Opt.Inline
import IxCC.Lir.Opt.Unroll
import IxCC.Lir.Opt.IfConv
import IxCC.Lir.WellFormed

/-!
# Validated Lir SSA optimizer driver (`Lir.Opt.run` & `Lir.Opt.validateCert`)

Combines the validated intra-procedural optimizer (`runLocal`: `gvnFunc → licmFunc → gvnFunc`
gated by `Lir.Opt.check`) with the directly-proved structural passes:
- `inlineTailLoop`: bounded non-recursive `.tail` helper inlining (`Lir.Opt.Inline`)
- `inlineHelpersLoop`: bounded non-recursive helper inlining (`Lir.Opt.Inline`)
- `versionOddLoop`: odd-fixnum loop versioning for `--bignat` scalar loops (`Lir.Opt.Unroll`)
- `ifConvLoop`: branchless diamond if-conversion (`Lir.Opt.IfConv`)
- `inlineSelfLoop`: bounded recursive self-inlining/peeling (`Lir.Opt.Inline`)
- `unrollLoop`: bounded 2×–4× hot scalar loop unrolling (`Lir.Opt.Unroll`)

Every structural step is followed by `runLocal` to fold newly exposed constants,
branches, parity/overflow checks, and dead code, and every pass carries a complete
formal soundness proof (`run_wellFormed`, `run_sim`, `run_refines`).
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (FunId Label Func Program)

/-- Untrusted optimization pipeline on a single function:
1. GVN/CSE + algebraic simplification + div strength reduction + branch/brOvf fold +
   forwarding/load CSE + DSE + DCE + prune unreachable.
2. Natural-loop LICM + invariant block parameter substitution + invariant `.fail` guard hoisting.
3. Second GVN + DSE + DCE + prune pass to clean up hoisted code and newly folded checks. -/
def optimizeFunc (F : Func) : Func :=
  let F1 := gvnFunc F
  let F2 := licmFunc F1
  gvnFunc F2

/-- Untrusted optimization pipeline on a whole program. -/
def optimize (p : Program) : Program :=
  { p with funcs := p.funcs.map optimizeFunc }

/-- Validated per-function local optimization: optimizes each function independently,
keeping the optimized function only if it passes `checkFuncWithPlan` and well-formedness,
and gates the final program with `check p cand` (plus `cand.wellFormed` whenever `p` is
well-formed). -/
def runLocal (p : Program) : Program :=
  let candFuncs := (List.range p.funcs.size).toArray.map fun fi =>
    match p.funcs[fi]? with
    | none => default
    | some F =>
        let G := optimizeFunc F
        if checkFuncWithPlan F G (inferFuncPlan F G) &&
           (G.checkShape p fi).toBool && (G.checkSsa fi).toBool then G
        else F
  let cand : Program := { p with funcs := candFuncs }
  if check p cand && (!p.wellFormed || cand.wellFormed) then cand else p

/-- Validated single-function local optimization: optimizes only function `fi` and
validates it with a singleton `ProgPlan` (O(1) on all untouched functions, avoiding
O(N²) work across large `--bignat` programs). -/
def runLocalAt (p : Program) (fi : FunId) : Program :=
  match p.funcs[fi]? with
  | none => p
  | some F =>
      let G := optimizeFunc F
      if G == F then p
      else
        let cand : Program := { p with funcs := p.funcs.set! fi G }
        let plan : ProgPlan :=
          { funcs := (Array.replicate p.funcs.size none).set! fi (some (inferFuncPlan F G)) }
        if checkProgramWithPlan p cand plan && (!p.wellFormed || cand.wellFormed) then cand else p

/-! ## Bounded structural pass drivers -/

/-- Fuel bounds for structural optimization passes. -/
def tailInlineFuel : Nat := 4
def helperInlineFuel : Nat := 8
def versionOddFuel : Nat := 6
def ifConvFuel : Nat := 6
def selfInlineFuel : Nat := 6
def unrollFuel : Nat := 4
def selfInlineMaxBlocks : Nat := 96

private def findNextTailHelperSite (p : Program) : Option (FunId × Label) :=
  (List.range p.funcs.size).findSome? fun fi =>
    (findTailHelperSite p fi).map fun b => (fi, b)

private def findNextHelperSite (p : Program) : Option (FunId × Nat × Nat) :=
  (List.range p.funcs.size).findSome? fun fi =>
    (findHelperCallSite p fi).map fun (b, pos) => (fi, b, pos)

private def findNextSelfSite (p : Program) (pickLast : Bool := false) : Option (FunId × Nat × Nat) :=
  (List.range p.funcs.size).findSome? fun fi =>
    (findSelfCallSite p fi selfInlineMaxBlocks pickLast).map fun (b, pos) => (fi, b, pos)

private def findNextVersionOddSite (doneFns : Src.NatSet) (p : Program) :
    Option (FunId × Label × List Nat × List Lir.VReg) :=
  (List.range p.funcs.size).findSome? fun fi =>
    if doneFns.contains fi then none
    else match p.funcs[fi]? with
    | none => none
    | some F => (findVersionOddLoopSite F).map fun (h, idxs, outers) => (fi, h, idxs, outers)

private def findNextIfConvSite (p : Program) : Option (FunId × Label) :=
  (List.range p.funcs.size).findSome? fun fi =>
    match p.funcs[fi]? with
    | none => none
    | some F => (findIfConvDiamondSite F).map fun b => (fi, b)

private def findNextUnrollSite (doneFns : Src.NatSet) (p : Program) :
    Option (FunId × Label × Nat) :=
  (List.range p.funcs.size).findSome? fun fi =>
    if doneFns.contains fi then none
    else match p.funcs[fi]? with
    | none => none
    | some F => (findUnrollLoopSite F).map fun (h, U) => (fi, h, U)

/-- Iterated bounded tail-helper inlining (e.g. entry wrapper `f0(v0): tail f1(v0, 1, 1)`),
cleaning up the modified function with `runLocalAt` after each step. -/
def inlineTailLoop : Nat → Program → Program
  | 0, p => p
  | fuel + 1, p =>
      match findNextTailHelperSite p with
      | none => p
      | some (fi, blk) =>
          let (p1, ch) := inlineTailSiteChecked p fi blk
          if ch then inlineTailLoop fuel (runLocalAt p1 fi) else p

/-- Iterated bounded helper-call inlining, cleaning up with `runLocalAt` after each step. -/
def inlineHelpersLoop : Nat → Program → Program
  | 0, p => p
  | fuel + 1, p =>
      match findNextHelperSite p with
      | none => p
      | some (fi, blk, pos) =>
          let (p1, ch) := inlineCallSiteChecked p fi blk pos
          if ch then inlineHelpersLoop fuel (runLocalAt p1 fi) else p

/-- Iterated odd-fixnum loop versioning (at most one loop per function),
cleaning up with `runLocalAt` after each step. -/
def versionOddLoop : Nat → Src.NatSet → Program → Program
  | 0, _, p => p
  | fuel + 1, doneFns, p =>
      match findNextVersionOddSite doneFns p with
      | none => p
      | some (fi, h, idxs, outers) =>
          let (p1, ch) := versionOddLoopSiteChecked p fi h idxs outers
          if ch then versionOddLoop fuel (doneFns.insert fi) (runLocalAt p1 fi) else p

/-- Apply `ifConvDiamondSite` followed by `runLocalAt` (which prunes the newly unreachable
diamond arm blocks and validates the cleanup via `checkProgramWithPlan`), gating on `wellFormed`. -/
def ifConvDiamondStep (p : Program) (fi : FunId) (b : Label) : Program × Bool :=
  match ifConvDiamondSite p fi b with
  | none => (p, false)
  | some q0 =>
      let q1 := runLocalAt q0 fi
      if !p.wellFormed || q1.wellFormed then (q1, true) else (p, false)

/-- Iterated branchless diamond if-conversion, cleaning up with `runLocalAt` after each step. -/
def ifConvLoop : Nat → Program → Program
  | 0, p => p
  | fuel + 1, p =>
      match findNextIfConvSite p with
      | none => p
      | some (fi, b) =>
          let (p1, ch) := ifConvDiamondStep p fi b
          if ch then ifConvLoop fuel p1 else p

/-- Iterated bounded self-recursive inlining/peeling (alternating first/last call site for
balanced 2-call peeling on `fib`), cleaning up with `runLocalAt` after each step. -/
def inlineSelfLoop : Nat → Program → Program
  | 0, p => p
  | fuel + 1, p =>
      match findNextSelfSite p (fuel % 2 == 0) with
      | none => p
      | some (fi, blk, pos) =>
          let (p1, ch) := inlineCallSiteChecked p fi blk pos
          if ch then inlineSelfLoop fuel (runLocalAt p1 fi) else p

/-- Iterated bounded hot-loop unrolling (`1 ≤ U ≤ 4`, at most one loop per function),
cleaning up with `runLocalAt` after each step. -/
def unrollLoop : Nat → Src.NatSet → Program → Program
  | 0, _, p => p
  | fuel + 1, doneFns, p =>
      match findNextUnrollSite doneFns p with
      | none => p
      | some (fi, h, U) =>
          if 1 ≤ U && U ≤ 4 then
            let (p1, ch) := unrollLoopSiteChecked p fi h U
            if ch then unrollLoop fuel (doneFns.insert fi) (runLocalAt p1 fi) else p
          else p

/-- Clock scaling for `n` inlining steps (`k ↦ 2k + 1` iterated `n` times). -/
def inlineClock : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => 2 * inlineClock n k + 1

/-- Clock scaling for `n` unrolling steps (`k ↦ 4k + 3` iterated `n` times). -/
def unrollClock : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => 4 * unrollClock n k + 3

/-- Composed clock map for `Lir.Opt.run` (independent of input program `p`). -/
def runClock (k : Nat) : Nat :=
  inlineClock tailInlineFuel
    (inlineClock helperInlineFuel (inlineClock selfInlineFuel (unrollClock unrollFuel k)))

/-- Full verified Lir SSA + structural optimizer (`--opt`):
1. Local validated SSA opt (`runLocal`: GVN/CSE, algebraic/parity/rotate/LEA simp, LICM, DSE, DCE)
2. Entry/tail helper inlining (`inlineTailLoop`)
3. Non-recursive helper call inlining (`inlineHelpersLoop`)
4. Multi-operand odd-fixnum loop versioning (`versionOddLoop`)
5. Branchless diamond if-conversion (`ifConvLoop`)
6. Bounded self-recursive peeling (`inlineSelfLoop`)
7. Bounded 2×–4× hot scalar loop unrolling (`unrollLoop`) -/
def run (p : Program) : Program :=
  let p1 := runLocal p
  let p2 := inlineTailLoop tailInlineFuel p1
  let p3 := inlineHelpersLoop helperInlineFuel p2
  let p4 := versionOddLoop versionOddFuel .leaf p3
  let p5 := ifConvLoop ifConvFuel p4
  let p6 := inlineSelfLoop selfInlineFuel p5
  unrollLoop unrollFuel .leaf p6

/-- Validate an externally supplied optimized `Lir.Program` certificate `cert`
against source program `p`, requiring both semantic equivalence (`check p cert`)
and `cert.wellFormed`. -/
def validateCert (p cert : Program) : Except String Program :=
  if !check p cert then
    .error "lir.opt: translation validator rejected optimized program"
  else
    match cert.check with
    | .error msg => .error s!"lir.opt: optimized program not well-formed: {msg}"
    | .ok () => .ok cert

end IxCC.Lir.Opt
