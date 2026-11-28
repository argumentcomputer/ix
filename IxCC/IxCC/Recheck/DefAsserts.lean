import IxCC.Recheck.Run
import IxCC.Recheck.Rc.Replay
import IxCC.Src.KernelFront.Reading

/-! # `EM-0`: Certified enforcement of Ixon v5 `DefAsserts` in `Recheck`

Ixon v5 definitions carry three compiler-checked resource assertions
(`_root_.Ixon.DefAsserts`):

* **`@[no_rc]`** (`alloc = .noRc` or `.noAlloc`): no reference-counting
  operations (`inc`, `dec`, RC markers, or calls to RC runtime procedures)
  anywhere in the transitive call graph `Reach(f)`.
* **`@[no_alloc]`** (`alloc = .noAlloc`): implies `@[no_rc]`, plus no dynamic
  heap allocation (`Own.Rhs.alloc` with `arity > 0`, `Lir.Term.fail .heap`,
  bump-pointer stores to `ctx + Rt.bumpOff`, or calls to RC allocation
  procedures) anywhere in `Reach(f)`.
* **`@[bounded_stack]`** (`boundedStack = true`): a certified `StackWitness`
  (`B : Src.NatMap Nat`) over `Reach(f)` using the checked `FrameLayout` sizes
  such that for every `g ∈ Reach(f)`:
  - `l(g).size + 8 ≤ B(g)` (accounting for the 8-byte pushed return address),
  - for every non-tail call `g →_call h`, `l(g).size + 8 + B(h) ≤ B(g)`,
  - for every tail call `g →_tail h`, `B(h) ≤ B(g)`.

Because `l(g).size + 8 ≥ 8 > 0`, any valid `StackWitness` mathematically
precludes all non-tail call cycles (direct, mutual, or mixed tail/non-tail)
in `Reach(f)` (`stackWitness_no_nontail_cycle`) while accepting pure tail
recursion (such as `gcd` or mutual `even`/`odd`), and yields a formal upper
bound `B(f)` on total active frame bytes along every dynamic call stack
starting from `f` (`stackWitness_depth_bound`).

The checker is written in kernel-evaluable style (`D17`: structural recursion
on lists/fuel and `Src.NatMap`/`NatSet`) and exposes standalone entry points
for both `Recheck.Artifact` and `Recheck.RcReplay.Artifact` (taking decoded
`DefAsserts` either directly as a `Src.NatMap` or via `KernelFront.Reading`). -/

set_option autoImplicit false

namespace IxCC.Recheck.DefAsserts

open IxCC.Src (CId NatMap NatSet)

/-! ## Mapping compiled globals back to source constants -/

/-- The originating `Src.CId` of a compiled global key `Key.GKey`, if any.
Specialisations, workers, lifted lambdas, and root entries inherit the source
constant of their origin. -/
def gkeyOrigin? : Key.GKey → Option CId
  | .const c _ => some c
  | .byName c _ => some c
  | .recStar r _ => some r
  | .wrapper (.ctor c) _ | .wrapper (.quotMk c) _ | .wrapper (.quotLift c) _
  | .wrapper (.recr c) _ | .wrapper (.cases c) _ => some c
  | .wrapper _ _ => none
  | .spec g _ => gkeyOrigin? g
  | .worker g _ => gkeyOrigin? g
  | .lam g _ => gkeyOrigin? g
  | .dispatch _ => none
  | .entry g _ => gkeyOrigin? g

/-- Look up the Ixon v5 `DefAsserts` governing a compiled global key `k`. -/
def keyAsserts (asserts : NatMap _root_.Ixon.DefAsserts) (k : Key.GKey) :
    _root_.Ixon.DefAsserts :=
  match gkeyOrigin? k with
  | some c => (asserts.get? c).getD {}
  | none => {}

/-- Look up the Ixon v5 `DefAsserts` governing `Cfg.Fun` `fd`. -/
def funAsserts (asserts : NatMap _root_.Ixon.DefAsserts) (fd : Cfg.Fun) :
    _root_.Ixon.DefAsserts :=
  keyAsserts asserts fd.key

/-- Strength order on `AllocAssert`: `unrestricted ≤ noRc ≤ noAlloc`. -/
def allocRank : _root_.Ixon.AllocAssert → Nat
  | .unrestricted => 0
  | .noRc => 1
  | .noAlloc => 2

/-- Whether `caller`'s assertions are at least as strong as `callee`'s. -/
def assertsLe (callee caller : _root_.Ixon.DefAsserts) : Bool :=
  decide (allocRank callee.alloc ≤ allocRank caller.alloc) &&
  (!callee.boundedStack || caller.boundedStack)

/-! ## Pre-ANF reachability & inline-preservation checks (`H-7`) -/

mutual

/-- Direct global references in a pre-ANF `Lam.Term` (`D17` structural). -/
def lamTermRefs : Lam.Term → List Lam.GlobalId
  | .glob g => [g]
  | .lam _ _ b | .tick b | .proj _ _ b => lamTermRefs b
  | .app f a _ | .letE _ f a => lamTermRefs f ++ lamTermRefs a
  | .con _ fs | .prim _ fs => lamTermListRefs fs
  | .case s alts d => lamTermRefs s ++ lamAltRefs alts ++ lamOptRefs d
  | .var _ | .lit _ | .box | .trap => []
  termination_by structural t => t

def lamTermListRefs : List Lam.Term → List Lam.GlobalId
  | [] => []
  | t :: ts => lamTermRefs t ++ lamTermListRefs ts
  termination_by structural ts => ts

def lamAltRefs : List Lam.Alt → List Lam.GlobalId
  | [] => []
  | .mk _ _ b :: as => lamTermRefs b ++ lamAltRefs as
  termination_by structural as => as

def lamOptRefs : Option Lam.Term → List Lam.GlobalId
  | none => []
  | some t => lamTermRefs t
  termination_by structural o => o

end

/-- Enqueue each `GlobalId` in `gs` into `todo` at most once, tracking membership in `queued`. -/
def lamReachEnqueue :
    List Lam.GlobalId → NatSet → List Lam.GlobalId → NatSet × List Lam.GlobalId
  | [], queued, todo => (queued, todo)
  | h :: hs, queued, todo =>
    if queued.contains h then lamReachEnqueue hs queued todo
    else lamReachEnqueue hs (queued.insert h) (h :: todo)

/-- Worklist reachability from `L.roots` in pre-ANF `Lam.Program` (`D17` fuel-bounded).
Every `GlobalId` enters `queued` and `todo` at most once, so `L.size + 1` steps suffice. -/
def lamReachLoop (L : Lam.Program) :
    Nat → List Lam.GlobalId → NatSet → List Lam.GlobalId → Option (List Lam.GlobalId)
  | 0, _ :: _, _, _ => none
  | _, [], _, acc => some acc
  | fuel + 1, g :: todo, queued, acc =>
    match L.global? g with
    | none => none
    | some gd =>
      let (queued', todo') := lamReachEnqueue (lamTermRefs gd.body) queued todo
      lamReachLoop L fuel todo' queued' (g :: acc)

/-- Compute all globals reachable from `L.roots` in pre-ANF `Lam.Program`. -/
def lamReachable (L : Lam.Program) : Option (List Lam.GlobalId) :=
  let (queued0, todo0) := lamReachEnqueue L.roots .leaf []
  lamReachLoop L (L.size + L.globals.toList.length + 1) todo0 queued0 []

/-- Reject inlining any callee with non-default `DefAsserts` into a caller whose
`DefAsserts` do not subsume the callee's (`D17` structural). -/
def checkInlineRoundCallees (asserts : NatMap _root_.Ixon.DefAsserts) (P : Anf.Program)
    (callerId : Anf.GlobalId) (callerA : _root_.Ixon.DefAsserts) :
    List Anf.GlobalId → Except Err Unit
  | [] => pure ()
  | calleeId :: rest => do
    match P.global? calleeId with
    | some gd =>
      let calleeA := keyAsserts asserts gd.key
      if calleeA != ({} : _root_.Ixon.DefAsserts) && !assertsLe calleeA callerA then
        throw { stage := .rt, code := "assert.inline",
                message := s!"inline global {calleeId} into {callerId}: callee assertions are not subsumed by caller" }
    | none => pure ()
    checkInlineRoundCallees asserts P callerId callerA rest

def checkInlineRound (asserts : NatMap _root_.Ixon.DefAsserts) (P : Anf.Program) :
    Anf.Inline.Round → Except Err Unit
  | [] => pure ()
  | (callerId, callees) :: rest => do
    match P.global? callerId with
    | some gd => checkInlineRoundCallees asserts P callerId (keyAsserts asserts gd.key) callees
    | none => pure ()
    checkInlineRound asserts P rest

def checkMidSteps (asserts : NatMap _root_.Ixon.DefAsserts) (p : Anf.Shrink.Params) :
    List Anf.Pipeline.Step → Anf.Program → Except Err Anf.Program
  | [], P => pure P
  | s :: rest, P => do
    match s with
    | .inline r => checkInlineRound asserts P r
    | _ => pure ()
    let P' ← (s.run p P).mapError fun msg =>
      { stage := .anf, code := "anf.replay", message := msg }
    checkMidSteps asserts p rest P'

def checkPostSteps (asserts : NatMap _root_.Ixon.DefAsserts) (p : Anf.Shrink.Params) :
    List Anf.Pipeline.PostStep → Anf.Program → Except Err Unit
  | [], _ => pure ()
  | s :: rest, P => do
    match s with
    | .inline r => checkInlineRound asserts P r
    | _ => pure ()
    let P' ← (s.run p P).mapError fun msg =>
      { stage := .anf, code := "anf.replay", message := msg }
    checkPostSteps asserts p rest P'

/-- Trusted middle-end check: when `asserts` is non-empty, verify that no `Step.inline`
or `PostStep.inline` inlines a callee carrying `DefAsserts` into a caller whose `DefAsserts`
do not subsume the callee's. `O(1)` no-op when `asserts` is empty. -/
def checkMidNoUnsafeInline (asserts : NatMap _root_.Ixon.DefAsserts)
    (src : Src.Program) (lam : Lam.Program) (mid : Anf.Pipeline.Cert) : Except Err Unit := do
  if asserts.toList.isEmpty then
    return ()
  let P0 ← (Anf.Pipeline.checkLamNodes lam >>= Anf.convert >>= Anf.Pipeline.checkGlobalNodes).mapError
    fun msg => { stage := .anf, code := "anf.replay", message := msg }
  let P1 ← checkMidSteps asserts mid.shrink mid.steps P0
  match declaredCounts src with
  | none => throw { stage := .anf, code := "anf.entry", message := "a root has no declaration" }
  | some decl =>
    if Anf.Pipeline.plain decl P1 then
      pure ()
    else
      let E ← (Anf.Entry.run decl P1).mapError fun msg =>
        { stage := .anf, code := "anf.entry", message := msg }
      let Q8 ← (Anf.defun E).mapError Err.ofClosures
      let pc :=
        open IxCC.Anf.Pipeline (producePost) in
        match mid.post with
        | some c => if E.size == c.baseSize then c else producePost E.size Q8
        | none => producePost E.size Q8
      checkPostSteps asserts pc.shrink pc.steps Q8

/-! ## LIR call-graph extraction & transitive reachability -/

/-- Direct non-tail callees of a LIR block (`Lir.Stmt.call`). -/
def blockNonTailCallees (b : Lir.Block) : List Lir.FunId :=
  b.body.toList.filterMap fun
    | .call _ h _ => some h
    | _ => none

/-- Direct tail callee of a LIR block (`Lir.Term.tail`), if any. -/
def blockTailCallee (b : Lir.Block) : Option Lir.FunId :=
  match b.term with
  | .tail h _ => some h
  | _ => none

/-- All direct non-tail callees of LIR function `fn`. -/
def nonTailCallees (fn : Lir.Func) : List Lir.FunId :=
  fn.blocks.toList.flatMap blockNonTailCallees

/-- All direct tail callees of LIR function `fn`. -/
def tailCallees (fn : Lir.Func) : List Lir.FunId :=
  fn.blocks.toList.filterMap blockTailCallee

/-- All direct callees (non-tail and tail) of LIR function `fn`. -/
def callees (fn : Lir.Func) : List Lir.FunId :=
  nonTailCallees fn ++ tailCallees fn

/-- Non-tail call edge `g →_call h` in `P`. -/
def NonTailEdge (P : Lir.Program) (g h : Lir.FunId) : Prop :=
  ∃ fn, P.funcs[g]? = some fn ∧ h ∈ nonTailCallees fn

/-- Tail call edge `g →_tail h` in `P`. -/
def TailEdge (P : Lir.Program) (g h : Lir.FunId) : Prop :=
  ∃ fn, P.funcs[g]? = some fn ∧ h ∈ tailCallees fn

/-- Any call edge (non-tail or tail) in `P`. -/
def CallEdge (P : Lir.Program) (g h : Lir.FunId) : Prop :=
  NonTailEdge P g h ∨ TailEdge P g h

/-- Transitive call-graph reachability `Reach P f g` in LIR program `P`. -/
inductive Reach (P : Lir.Program) (f : Lir.FunId) : Lir.FunId → Prop where
  | refl : Reach P f f
  | step {g h : Lir.FunId} : Reach P f g → CallEdge P g h → Reach P f h

/-- Worklist computation of `Reach(f)` in `P` (structural on `fuel`).
Returns `none` if fuel runs out or an out-of-range callee is encountered. -/
def computeReachLoop (P : Lir.Program) :
    Nat → List Lir.FunId → NatSet → List Lir.FunId → Option (List Lir.FunId)
  | 0, _ :: _, _, _ => none
  | _, [], _, acc => some acc
  | fuel + 1, g :: todo, seen, acc =>
    if seen.contains g then
      computeReachLoop P fuel todo seen acc
    else
      match P.funcs[g]? with
      | none => none
      | some fn =>
        let cs := callees fn
        let next := cs.filter fun h => !seen.contains h && !todo.contains h
        computeReachLoop P fuel (next ++ todo) (seen.insert g) (g :: acc)

/-- Compute the list of functions reachable from `f` in `P`. -/
def computeReach (P : Lir.Program) (f : Lir.FunId) : Option (List Lir.FunId) :=
  computeReachLoop P (P.funcs.size * 2 + 16) [f] .leaf []

/-- Boolean check that `reach` contains `f`, lies within `P.funcs.size`, and is
closed under all direct callees in `P`. -/
def checkReachClosed (P : Lir.Program) (f : Lir.FunId) (reach : List Lir.FunId) : Bool :=
  reach.contains f &&
  reach.all fun g =>
    match P.funcs[g]? with
    | none => false
    | some fn => (callees fn).all fun h => reach.contains h

/-! ## Local RC and heap-allocation predicates -/

/-- Whether a Cfg function `fd` (with optional `Cfg.Rc.ActionTable`) contains
any RC operation (`Own.Plain.Action` entries or reserved RC markers). -/
def cfgHasRc (cfgSize : Nat) (fd : Cfg.Fun) (actions? : Option Cfg.Rc.ActionTable) : Bool :=
  let hasAction := match actions? with
    | some tbl => !tbl.toList.isEmpty
    | none => false
  let hasMarker := fd.blocks.any fun blk =>
    blk.body.any (Cfg.Rc.reserved cfgSize)
  hasAction || hasMarker

/-- Whether a LIR function `fn` invokes any RC runtime procedure (`incWrapper`,
`decWrapper`, `incProc`, `decProc`, `drop`). -/
def lirHasRcCall (rcProcs : List Lir.FunId) (fn : Lir.Func) : Bool :=
  (callees fn).any rcProcs.contains

/-- Whether a function `g` performs any RC operation (either in Cfg/RC or by
calling an RC runtime procedure in LIR). -/
def funcHasRc (cfg : Cfg.Program) (rcActions : Option (NatMap Cfg.Rc.ActionTable))
    (rcProcs : List Lir.FunId) (P : Lir.Program) (g : Lir.FunId) : Bool :=
  let inCfg := match cfg.fun? g with
    | some fd => cfgHasRc cfg.size fd (rcActions.bind (·.get? g))
    | none => false
  let inLir := match P.funcs[g]? with
    | some fn => rcProcs.contains g || lirHasRcCall rcProcs fn
    | none => true
  inCfg || inLir

/-- Whether a Cfg function `fd` performs any dynamic heap allocation
(`Own.Rhs.alloc` of a constructor with `arity > 0`). -/
def cfgHasAlloc (fd : Cfg.Fun) : Bool :=
  fd.blocks.any fun blk =>
    blk.body.any fun
      | .bind _ (.alloc c _ _) => c.arity > 0
      | _ => false

/-- Whether a LIR statement writes to the runtime bump pointer (`ctx + Rt.bumpOff`). -/
def stmtWritesBump : Lir.Stmt → Bool
  | .store _ { base := some .ctx, index := none, disp } _ => disp == Rt.bumpOff
  | _ => false

/-- Whether a LIR function `fn` has any heap allocation indicator:
* `.fail .heap` terminator,
* store to `ctx + Rt.bumpOff`, or
* call/tail-call to any allocation runtime procedure (`allocProc`/`allocWrapper`). -/
def lirHasAlloc (allocProcs : List Lir.FunId) (fn : Lir.Func) : Bool :=
  fn.blocks.any (fun blk =>
    (blk.term == .fail .heap) ||
    blk.body.toList.any stmtWritesBump) ||
  (callees fn).any allocProcs.contains

/-- Whether a function `g` performs any dynamic heap allocation (at Cfg or LIR). -/
def funcHasAlloc (cfg : Cfg.Program) (allocProcs : List Lir.FunId)
    (P : Lir.Program) (g : Lir.FunId) : Bool :=
  let inCfg := match cfg.fun? g with
    | some fd => cfgHasAlloc fd
    | none => false
  let inLir := match P.funcs[g]? with
    | some fn => allocProcs.contains g || lirHasAlloc allocProcs fn
    | none => true
  inCfg || inLir

/-- Certified check for `@[no_rc]` over a closed reachable set `reach` from `f`. -/
def checkNoRc (cfg : Cfg.Program) (rcActions : Option (NatMap Cfg.Rc.ActionTable))
    (rcProcs : List Lir.FunId) (P : Lir.Program) (f : Lir.FunId) (reach : List Lir.FunId) : Bool :=
  checkReachClosed P f reach &&
  reach.all fun g => !funcHasRc cfg rcActions rcProcs P g

/-- Certified check for `@[no_alloc]` over a closed reachable set `reach` from `f`.
Per Ixon v5 (`AllocAssert.noAlloc`), `@[no_alloc]` implies `@[no_rc]`. -/
def checkNoAlloc (cfg : Cfg.Program) (rcActions : Option (NatMap Cfg.Rc.ActionTable))
    (rcProcs allocProcs : List Lir.FunId) (P : Lir.Program) (f : Lir.FunId)
    (reach : List Lir.FunId) : Bool :=
  checkNoRc cfg rcActions rcProcs P f reach &&
  reach.all fun g => !funcHasAlloc cfg allocProcs P g

/-! ## Certified `@[bounded_stack]` witness checker and producer -/

/-- A stack-depth certificate mapping each reachable `Lir.FunId` `g` to an
upper bound `B(g)` (in bytes) on stack usage for any execution rooted at `g`. -/
abbrev StackWitness := NatMap Nat

/-- Check one function `g` against its `FrameLayout` and witness `B`:
* `fl.size + 8 ≤ B(g)` (own frame + 8-byte return address),
* for every non-tail callee `h`: `fl.size + 8 + B(h) ≤ B(g)`,
* for every tail callee `h`: `B(h) ≤ B(g)`. -/
def checkStackNode (P : Lir.Program) (frames : List Xv.Stacking.FrameLayout)
    (B : StackWitness) (g : Lir.FunId) : Bool :=
  match P.funcs[g]?, frames[g]?, B.get? g with
  | some fn, some fl, some bg =>
    let step := fl.size + 8
    decide (step ≤ bg) &&
    (nonTailCallees fn).all (fun h =>
      match B.get? h with
      | some bh => decide (step + bh ≤ bg)
      | none => false) &&
    (tailCallees fn).all (fun h =>
      match B.get? h with
      | some bh => decide (bh ≤ bg)
      | none => false)
  | _, _, _ => false

/-- Linear-time certified validator for `@[bounded_stack]` over `Reach(f)`
using checked `FrameLayout` sizes (`frames`). -/
def checkStackWitness (P : Lir.Program) (frames : List Xv.Stacking.FrameLayout)
    (f : Lir.FunId) (reach : List Lir.FunId) (B : StackWitness) : Bool :=
  checkReachClosed P f reach &&
  reach.all (checkStackNode P frames B)

/-- One Bellman-Ford relaxation pass over `reach`. -/
def relaxStackOnce (P : Lir.Program) (frames : List Xv.Stacking.FrameLayout)
    (reach : List Lir.FunId) (B : StackWitness) : StackWitness :=
  reach.foldl (fun acc g =>
    match P.funcs[g]?, frames[g]? with
    | some fn, some fl =>
      let step := fl.size + 8
      let cur := (acc.get? g).getD step
      let cur := Nat.max cur step
      let cur := (nonTailCallees fn).foldl (fun m h =>
        match acc.get? h with
        | some bh => Nat.max m (step + bh)
        | none => m) cur
      let cur := (tailCallees fn).foldl (fun m h =>
        match acc.get? h with
        | some bh => Nat.max m bh
        | none => m) cur
      acc.insert g cur
    | _, _ => acc) B

/-- Repeat Bellman-Ford relaxation `k` times (structural on `k`). -/
def relaxStackLoop (P : Lir.Program) (frames : List Xv.Stacking.FrameLayout)
    (reach : List Lir.FunId) : Nat → StackWitness → StackWitness
  | 0, B => B
  | k + 1, B => relaxStackLoop P frames reach k (relaxStackOnce P frames reach B)

/-- Untrusted producer for a `StackWitness` over `reach`: initializes every
`g ∈ reach` to `fl(g).size + 8`, runs `reach.length` relaxation rounds, and
returns `some B` iff `checkStackWitness` accepts `B` (returns `none` whenever
a non-tail call cycle exists in `Reach(f)`). -/
def produceStackWitness (P : Lir.Program) (frames : List Xv.Stacking.FrameLayout)
    (f : Lir.FunId) (reach : List Lir.FunId) : Option StackWitness :=
  let init : StackWitness := reach.foldl (fun acc g =>
    match frames[g]? with
    | some fl => acc.insert g (fl.size + 8)
    | none => acc) .leaf
  let B := relaxStackLoop P frames reach reach.length init
  if checkStackWitness P frames f reach B then some B else none

/-! ## Top-level `EM-0` checker for compiled artifacts -/

/-- Context bundled for checking all `DefAsserts` on a compiled program. -/
structure CheckCtx where
  cfg : Cfg.Program
  rcActions : Option (NatMap Cfg.Rc.ActionTable) := none
  rcProcs : List Lir.FunId := []
  allocProcs : List Lir.FunId := []
  lir : Lir.Program
  frames : List Xv.Stacking.FrameLayout
  /-- Optional pre-ANF `Lam.Program`, used to reject annotated definitions that
  were erased (inlined/pruned away) before `Cfg`. -/
  lam : Option Lam.Program := none

/-- Enforce a single function `f`'s decoded `DefAsserts` (`a`). -/
def checkFunAsserts (ctx : CheckCtx) (f : Lir.FunId) (a : _root_.Ixon.DefAsserts)
    (witness? : Option StackWitness := none) : Except Err Unit := do
  if a == ({} : _root_.Ixon.DefAsserts) then
    return ()
  let some reach := computeReach ctx.lir f
    | throw { stage := .rt, code := "assert.reach",
              message := s!"function {f}: call-graph reachability failed" }
  match a.alloc with
  | .unrestricted => pure ()
  | .noRc =>
    unless checkNoRc ctx.cfg ctx.rcActions ctx.rcProcs ctx.lir f reach do
      throw { stage := .rt, code := "assert.no_rc",
              message := s!"function {f}: @[no_rc] violated (RC operation reachable in call graph)" }
  | .noAlloc =>
    unless checkNoAlloc ctx.cfg ctx.rcActions ctx.rcProcs ctx.allocProcs ctx.lir f reach do
      throw { stage := .rt, code := "assert.no_alloc",
              message := s!"function {f}: @[no_alloc] violated (allocation or RC reachable in call graph)" }
  if a.boundedStack then
    match witness? with
    | some B =>
      unless checkStackWitness ctx.lir ctx.frames f reach B do
        throw { stage := .rt, code := "assert.bounded_stack",
                message := s!"function {f}: @[bounded_stack] witness rejected" }
    | none =>
      match produceStackWitness ctx.lir ctx.frames f reach with
      | some _ => pure ()
      | none =>
        throw { stage := .rt, code := "assert.bounded_stack",
                message := s!"function {f}: @[bounded_stack] violated (non-tail call cycle or missing frame layout)" }

/-- Enforce all `DefAsserts` across every function of `ctx.cfg` (structural on
the function list, `D17`). -/
def checkAllLoop (ctx : CheckCtx) (asserts : NatMap _root_.Ixon.DefAsserts)
    (witness? : Option StackWitness) : List (Lir.FunId × Cfg.Fun) → Except Err Unit
  | [] => pure ()
  | (f, fd) :: rest => do
    checkFunAsserts ctx f (funAsserts asserts fd) witness?
    checkAllLoop ctx asserts witness? rest

/-- Verify that every pre-ANF reachable `Lam.Global` carrying non-default `DefAsserts`
still has at least one surviving `Cfg.Fun` in `ctx.cfg.funList` with the same originating
`Src.CId`. Fails closed (`assert.erased`) if an annotated definition disappeared before `Cfg`. -/
def checkPreAnfLoop (L : Lam.Program) (asserts : NatMap _root_.Ixon.DefAsserts)
    (surviving : NatSet) : List Lam.GlobalId → Except Err Unit
  | [] => pure ()
  | g :: rest => do
    match L.global? g with
    | some gd =>
      match gkeyOrigin? gd.key with
      | some c =>
        let a := (asserts.get? c).getD {}
        if a != ({} : _root_.Ixon.DefAsserts) && !surviving.contains c then
          throw { stage := .rt, code := "assert.erased",
                  message := s!"constant {c}: definition carrying assertions was erased before Cfg" }
      | none => pure ()
    | none => pure ()
    checkPreAnfLoop L asserts surviving rest

def checkPreAnfAsserts (ctx : CheckCtx) (asserts : NatMap _root_.Ixon.DefAsserts) :
    Except Err Unit := do
  if asserts.toList.isEmpty then
    return ()
  match ctx.lam with
  | none => pure ()
  | some L =>
    let some reach := lamReachable L
      | throw { stage := .rt, code := "assert.reach",
                message := "pre-ANF call-graph reachability failed" }
    let surviving : NatSet := ctx.cfg.funList.foldl (fun s (_, fd) =>
      match gkeyOrigin? fd.key with
      | some c => s.insert c
      | none => s) .leaf
    checkPreAnfLoop L asserts surviving reach

/-- Enforce decoded Ixon v5 `DefAsserts` over a `CheckCtx` (both pre-ANF survival
of annotated constants and post-lowering RC/allocation/stack checks). -/
def check (ctx : CheckCtx) (asserts : NatMap _root_.Ixon.DefAsserts)
    (witness? : Option StackWitness := none) : Except Err Unit := do
  checkPreAnfAsserts ctx asserts
  checkAllLoop ctx asserts witness? ctx.cfg.funList

/-- Build a `CheckCtx` for a Phase 1 `Recheck.Artifact` and its frame layouts
(defaulting to `Xv.Stacking.produce art.xl` when `frames?` is `none`). -/
def ctxOfArtifact (art : Recheck.Artifact)
    (frames? : Option (List Xv.Stacking.FrameLayout) := none) : CheckCtx :=
  { cfg := art.cfg
    rcActions := none
    rcProcs := []
    allocProcs := []
    lir := art.lowered.program
    frames := frames?.getD (Xv.Stacking.produce art.xl)
    lam := some art.lam }

/-- Build a `CheckCtx` for a plain-RC `Recheck.RcReplay.Artifact` and its
frame layouts (identifying all RC, allocation, and Track A4 reset/reuse
runtime procedures from `art.front.layout` and `art.front.drop`). -/
def ctxOfRcArtifact (art : Recheck.RcReplay.Artifact)
    (frames : List Xv.Stacking.FrameLayout) : CheckCtx :=
  let layout := art.front.layout
  let ctorIdxs := List.range layout.ctors.length
  let rcProcs :=
    [layout.incWrapper, layout.decWrapper, layout.incProc, layout.decProc,
     art.front.drop, layout.isUniqueProc] ++
    ctorIdxs.flatMap fun i =>
      [layout.resetWrapper i, layout.resetUWrapper i,
       layout.reuseWrapper i, layout.reuseUWrapper i]
  let allocProcs :=
    ctorIdxs.flatMap fun i =>
      [layout.allocProc i, layout.allocWrapper i,
       layout.reuseWrapper i, layout.reuseUWrapper i]
  { cfg := art.front.cfg.base
    rcActions := some art.front.cfg.actions
    rcProcs
    allocProcs
    lir := art.front.lowered.program
    frames
    lam := some art.front.lam }

/-- Enforce `asserts` on a Phase 1 `Recheck.Artifact`. -/
def checkArtifact (asserts : NatMap _root_.Ixon.DefAsserts) (art : Recheck.Artifact)
    (frames? : Option (List Xv.Stacking.FrameLayout) := none)
    (witness? : Option StackWitness := none) : Except Err Unit :=
  check (ctxOfArtifact art frames?) asserts witness?

/-- Enforce `asserts` on a plain-RC `Recheck.RcReplay.Artifact`. -/
def checkRcArtifact (asserts : NatMap _root_.Ixon.DefAsserts)
    (art : Recheck.RcReplay.Artifact) (frames : List Xv.Stacking.FrameLayout)
    (witness? : Option StackWitness := none) : Except Err Unit :=
  check (ctxOfRcArtifact art frames) asserts witness?

/-- Enforce decoded Ixon v5 `Definition.asserts` from `KernelFront.Reading` on
a Phase 1 `Recheck.Artifact` and its `Recheck.Cert` (including middle-end
inline-preservation checks). -/
def checkWithReading (rd : Src.KernelFront.Reading) (art : Recheck.Artifact)
    (cert : Recheck.Cert) (witness? : Option StackWitness := none) : Except Err Unit := do
  let asserts := rd.assertsMap art.src
  checkMidNoUnsafeInline asserts art.src art.lam cert.mid
  checkArtifact asserts art (some cert.frames) witness?

/-- Enforce decoded Ixon v5 `Definition.asserts` from `KernelFront.Reading` on
a plain-RC `Recheck.RcReplay.Artifact` and its `Recheck.RcReplay.Cert` (including
middle-end inline-preservation checks). -/
def checkRcWithReading (rd : Src.KernelFront.Reading) (art : Recheck.RcReplay.Artifact)
    (cert : Recheck.RcReplay.Cert) (witness? : Option StackWitness := none) : Except Err Unit := do
  let asserts := rd.assertsMap art.front.src
  checkMidNoUnsafeInline asserts art.front.src art.front.lam cert.base.mid
  checkRcArtifact asserts art cert.base.frames witness?

/-- Run `Recheck.run` and enforce decoded Ixon v5 `Definition.asserts` from `rd`. -/
def runWithReading (cfg : Config) (P : Src.Program) (rd : Src.KernelFront.Reading)
    (c : Cert) (witness? : Option StackWitness := none) : Except Err Artifact := do
  let art ← Recheck.run cfg P c
  checkWithReading rd art c witness?
  pure art

/-- Run `RcReplay.run` and enforce decoded Ixon v5 `Definition.asserts` from `rd`. -/
def runRcWithReading (cfg : Config) (P : Src.Program) (rd : Src.KernelFront.Reading)
    (c : RcReplay.Cert) (witness? : Option StackWitness := none) : Except Err RcReplay.Artifact := do
  let art ← RcReplay.run cfg P c
  checkRcWithReading rd art c witness?
  pure art

theorem runWithReading_ok {cfg : Config} {P : Src.Program} {rd : Src.KernelFront.Reading}
    {c : Cert} {witness? : Option StackWitness} {art : Artifact}
    (h : runWithReading cfg P rd c witness? = .ok art) :
    Recheck.run cfg P c = .ok art ∧ checkWithReading rd art c witness? = .ok () := by
  unfold runWithReading at h
  simp only [bind, Except.bind] at h
  cases hr : Recheck.run cfg P c with
  | error e => simp [hr] at h
  | ok a =>
    simp only [hr] at h
    cases hc : checkWithReading rd a c witness? with
    | error e => simp [hc] at h
    | ok u =>
      cases u
      simp only [hc, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, hc⟩

theorem runRcWithReading_ok {cfg : Config} {P : Src.Program} {rd : Src.KernelFront.Reading}
    {c : RcReplay.Cert} {witness? : Option StackWitness} {art : RcReplay.Artifact}
    (h : runRcWithReading cfg P rd c witness? = .ok art) :
    RcReplay.run cfg P c = .ok art ∧ checkRcWithReading rd art c witness? = .ok () := by
  unfold runRcWithReading at h
  simp only [bind, Except.bind] at h
  cases hr : RcReplay.run cfg P c with
  | error e => simp [hr] at h
  | ok a =>
    simp only [hr] at h
    cases hc : checkRcWithReading rd a c witness? with
    | error e => simp [hc] at h
    | ok u =>
      cases u
      simp only [hc, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, hc⟩

/-! ## Soundness proofs -/

/-- If `checkReachClosed P f reach = true`, every `g` transitively reachable
from `f` (`Reach P f g`) lies in `reach`. -/
theorem reach_mem_of_closed {P : Lir.Program} {f : Lir.FunId} {reach : List Lir.FunId}
    (hcl : checkReachClosed P f reach = true) :
    ∀ {g : Lir.FunId}, Reach P f g → g ∈ reach := by
  unfold checkReachClosed at hcl
  rw [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at hcl
  obtain ⟨hf, hclosed⟩ := hcl
  intro g hr
  induction hr with
  | refl => exact hf
  | step _ hedge ih =>
    have hg := hclosed _ ih
    rcases hedge with ⟨fn, hfn, hmem⟩ | ⟨fn, hfn, hmem⟩
    · rw [hfn] at hg
      rw [List.all_eq_true] at hg
      exact List.contains_iff_mem.1 (hg _ (List.mem_append_left _ hmem))
    · rw [hfn] at hg
      rw [List.all_eq_true] at hg
      exact List.contains_iff_mem.1 (hg _ (List.mem_append_right _ hmem))

/-- **Soundness of `@[no_rc]`**: if `checkNoRc` accepts, NO function `g`
transitively reachable from `f` performs any RC operation (`funcHasRc = false`). -/
theorem checkNoRc_sound {cfg : Cfg.Program} {rcActions : Option (NatMap Cfg.Rc.ActionTable)}
    {rcProcs : List Lir.FunId} {P : Lir.Program} {f : Lir.FunId} {reach : List Lir.FunId}
    (h : checkNoRc cfg rcActions rcProcs P f reach = true) :
    ∀ g, Reach P f g → funcHasRc cfg rcActions rcProcs P g = false := by
  unfold checkNoRc at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro g hrg
  have hmem := reach_mem_of_closed h.1 hrg
  have hok := h.2 g hmem
  simpa using hok

/-- **Soundness of `@[no_alloc]`**: if `checkNoAlloc` accepts, every `g`
transitively reachable from `f` has BOTH `funcHasRc = false` (since `noAlloc`
implies `noRc`) AND `funcHasAlloc = false` (no Cfg dynamic `alloc`, no
`.fail .heap`, no `bumpOff` store, no allocation runtime calls). -/
theorem checkNoAlloc_sound {cfg : Cfg.Program} {rcActions : Option (NatMap Cfg.Rc.ActionTable)}
    {rcProcs allocProcs : List Lir.FunId} {P : Lir.Program} {f : Lir.FunId}
    {reach : List Lir.FunId}
    (h : checkNoAlloc cfg rcActions rcProcs allocProcs P f reach = true) :
    ∀ g, Reach P f g →
      funcHasRc cfg rcActions rcProcs P g = false ∧
      funcHasAlloc cfg allocProcs P g = false := by
  unfold checkNoAlloc at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hrc := checkNoRc_sound h.1
  unfold checkNoRc at h
  rw [Bool.and_eq_true] at h
  intro g hrg
  have hmem := reach_mem_of_closed h.1.1 hrg
  have halloc := h.2 g hmem
  exact ⟨hrc g hrg, by simpa using halloc⟩

/-- Properties extracted from `checkStackNode P frames B g = true`. -/
theorem checkStackNode_spec {P : Lir.Program} {frames : List Xv.Stacking.FrameLayout}
    {B : StackWitness} {g : Lir.FunId} (h : checkStackNode P frames B g = true) :
    ∃ fn fl bg,
      P.funcs[g]? = some fn ∧
      frames[g]? = some fl ∧
      B.get? g = some bg ∧
      fl.size + 8 ≤ bg ∧
      (∀ h ∈ nonTailCallees fn, ∃ bh, B.get? h = some bh ∧ fl.size + 8 + bh ≤ bg) ∧
      (∀ h ∈ tailCallees fn, ∃ bh, B.get? h = some bh ∧ bh ≤ bg) := by
  unfold checkStackNode at h
  cases hfn : P.funcs[g]? with
  | none => simp [hfn] at h
  | some fn =>
    cases hfl : frames[g]? with
    | none => simp [hfn, hfl] at h
    | some fl =>
      cases hbg : B.get? g with
      | none => simp [hfn, hfl, hbg] at h
      | some bg =>
        simp only [hfn, hfl, hbg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
        obtain ⟨⟨hself, hnt⟩, ht⟩ := h
        refine ⟨fn, fl, bg, rfl, rfl, rfl, hself, ?_, ?_⟩
        · intro c hc
          have h1 := hnt c hc
          cases hbh : B.get? c with
          | none => simp [hbh] at h1
          | some bh =>
            simp only [hbh, decide_eq_true_eq] at h1
            exact ⟨bh, rfl, h1⟩
        · intro c hc
          have h1 := ht c hc
          cases hbh : B.get? c with
          | none => simp [hbh] at h1
          | some bh =>
            simp only [hbh, decide_eq_true_eq] at h1
            exact ⟨bh, rfl, h1⟩

/-- **Soundness of `checkStackWitness`**: every `g` transitively reachable
from `f` carries a witness bound `B(g)` satisfying `fl(g).size + 8 ≤ B(g)`,
strict decrease `fl(g).size + 8 + B(h) ≤ B(g)` across every non-tail call, and
non-increase `B(h) ≤ B(g)` across every tail call. -/
theorem checkStackWitness_sound {P : Lir.Program} {frames : List Xv.Stacking.FrameLayout}
    {f : Lir.FunId} {reach : List Lir.FunId} {B : StackWitness}
    (h : checkStackWitness P frames f reach B = true) :
    ∀ g, Reach P f g →
      ∃ fn fl bg,
        P.funcs[g]? = some fn ∧
        frames[g]? = some fl ∧
        B.get? g = some bg ∧
        fl.size + 8 ≤ bg ∧
        (∀ h ∈ nonTailCallees fn, ∃ bh, B.get? h = some bh ∧ fl.size + 8 + bh ≤ bg) ∧
        (∀ h ∈ tailCallees fn, ∃ bh, B.get? h = some bh ∧ bh ≤ bg) := by
  unfold checkStackWitness at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro g hrg
  exact checkStackNode_spec (h.2 g (reach_mem_of_closed h.1 hrg))

/-- A finite call path from `g` to `h` in `P`, accumulating the total active
stack bytes pushed along non-tail edges (`bytes`). -/
inductive CallPath (P : Lir.Program) (frames : List Xv.Stacking.FrameLayout) :
    Lir.FunId → Lir.FunId → Nat → Prop where
  | nil (g : Lir.FunId) : CallPath P frames g g 0
  | nonTail {g m h n : Lir.FunId} {fl : Xv.Stacking.FrameLayout} :
      NonTailEdge P g m →
      frames[g]? = some fl →
      CallPath P frames m h n →
      CallPath P frames g h (fl.size + 8 + n)
  | tail {g m h n : Lir.FunId} :
      TailEdge P g m →
      CallPath P frames m h n →
      CallPath P frames g h n

/-- **Quantitative stack-depth bound**: along ANY dynamic call path from `g`
(reachable from `f`) to `h`, the accumulated frame bytes `bytes` plus `B(h)`
never exceed `B(g)`. In particular, total active stack bytes along any chain
from `f` are bounded by `B(f)`. -/
theorem stackWitness_depth_bound {P : Lir.Program} {frames : List Xv.Stacking.FrameLayout}
    {f : Lir.FunId} {reach : List Lir.FunId} {B : StackWitness}
    (hw : checkStackWitness P frames f reach B = true) :
    ∀ {g h bytes}, Reach P f g → CallPath P frames g h bytes →
      ∃ bg bh, B.get? g = some bg ∧ B.get? h = some bh ∧ bytes + bh ≤ bg := by
  intro g h bytes hrg hpath
  induction hpath with
  | nil g =>
    obtain ⟨_, _, bg, _, _, hbg, _, _, _⟩ := checkStackWitness_sound hw g hrg
    exact ⟨bg, bg, hbg, hbg, by omega⟩
  | @nonTail g m h n fl hedge hfl hrest ih =>
    obtain ⟨fn, fl', bg, hfn, hfl', hbg, _, hnt, _⟩ := checkStackWitness_sound hw g hrg
    obtain ⟨fn', hfn', hmem⟩ := hedge
    rw [hfn] at hfn'; cases hfn'
    rw [hfl] at hfl'; cases hfl'
    obtain ⟨bm, hbm, hle⟩ := hnt m hmem
    have hrm : Reach P f m := Reach.step hrg (Or.inl ⟨fn, hfn, hmem⟩)
    obtain ⟨bm', bh, hbm', hbh, hih⟩ := ih hrm
    rw [hbm] at hbm'; cases hbm'
    exact ⟨bg, bh, hbg, hbh, by omega⟩
  | @tail g m h n hedge hrest ih =>
    obtain ⟨fn, fl, bg, hfn, _, hbg, _, _, ht⟩ := checkStackWitness_sound hw g hrg
    obtain ⟨fn', hfn', hmem⟩ := hedge
    rw [hfn] at hfn'; cases hfn'
    obtain ⟨bm, hbm, hle⟩ := ht m hmem
    have hrm : Reach P f m := Reach.step hrg (Or.inr ⟨fn, hfn, hmem⟩)
    obtain ⟨bm', bh, hbm', hbh, hih⟩ := ih hrm
    rw [hbm] at hbm'; cases hbm'
    exact ⟨bg, bh, hbg, hbh, by omega⟩

/-- **Acyclicity of non-tail calls**: under a valid `StackWitness`, NO cycle
in `Reach(f)` can contain a non-tail call (ruling out direct non-tail
recursion, mutual non-tail recursion, and mixed tail/non-tail cycles). -/
theorem stackWitness_no_nontail_cycle {P : Lir.Program} {frames : List Xv.Stacking.FrameLayout}
    {f : Lir.FunId} {reach : List Lir.FunId} {B : StackWitness}
    (hw : checkStackWitness P frames f reach B = true)
    {g m bytes : Nat} (hrg : Reach P f g)
    (hedge : NonTailEdge P g m) (hback : CallPath P frames m g bytes) : False := by
  obtain ⟨_, fl, _, _, hfl, _, _, _, _⟩ := checkStackWitness_sound hw g hrg
  have hcyc : CallPath P frames g g (fl.size + 8 + bytes) :=
    CallPath.nonTail hedge hfl hback
  obtain ⟨bg, bg', hbg, hbg', hle⟩ := stackWitness_depth_bound hw hrg hcyc
  rw [hbg] at hbg'; cases hbg'
  omega

end IxCC.Recheck.DefAsserts
