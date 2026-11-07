import IxCC.Lir.Graph
import IxCCTests.Support.Rng
import IxCCTests.Lir.Region

/-!
# A seeded SSA program generator for Lir

After regalloc2's fuzzing generator (`ION.md` 1148–1176, `src/fuzzing/func.rs`),
but built so that programs also *run* to interesting outcomes:

- **Control flow** is grown from structured regions (sequences, diamonds,
  triangles, counted loops, overflow branches and early exits), so the
  dominator tree is known while the CFG is built and loops terminate. A
  random permutation of the non-entry labels then turns some forward edges
  into charged "backward" ones without changing the graph.
- **Values** are chosen from the registers in scope, which are exactly the
  definitions dominating the current point: function and block parameters,
  earlier statements of dominating blocks, and `brOvf` results. Joins and
  loop headers take block parameters, passed from each predecessor's scope.
- **Operations:** every `BinOp` at every width (variable shifts included),
  guarded `udiv`/`urem`, `select`, `test`, `brOvf addC/subB`, loads and
  stores in the heap and context blocks of `Region`, `addr`, calls along a
  call DAG plus fuel-bounded self-recursion, tail calls, `fail`, `trap`.
- **Critical edges** come from triangles, duplicate-target `brOvf`s and a
  shared overflow block. `Program.splitCriticalEdges` removes them, and the
  tests compare the two programs.
- A few "wild" programs may divide by zero or touch denied memory, so
  `stuck` is exercised too.

Each function receives a block budget; a program has 1 to `maxBlocks`
blocks before splitting. Everything is determined by the seed.
-/

namespace IxCCTests.Lir.Gen

open IxCC IxCC.Lir IxCCTests.Support

structure Config where
  /-- Largest block count per program (before splitting). -/
  maxBlocks : Nat := 200
  maxFuncs : Nat := 4
  /-- Emit critical edges (split before `WellFormed`). -/
  critical : Bool := true
  /-- Percent of functions whose non-entry labels are permuted. -/
  relabel : Nat := 25
  /-- Percent of programs that may divide by zero or access denied memory. -/
  wild : Nat := 3
  /-- Shift operators to draw. The defaults draw every form; `check-xv-select`
  narrows them to the forms the instruction table expresses, and the
  defaults keep the random stream (and so `check-lir`) unchanged. -/
  shiftOps : Array BinOp := #[.shl, .shr, .sar]
  /-- Draw register shift counts. -/
  varShifts : Bool := true
  /-- Draw guarded `udiv`/`urem` (and, in wild programs, unguarded ones). -/
  divs : Bool := true
  /-- Draw `select`. -/
  selects : Bool := true
  /-- Draw `test`. -/
  tests : Bool := true

structure Sig where
  params : Nat
  results : Nat
  /-- The first parameter is a recursion fuel, and the function may call
  itself with a smaller one. -/
  recursive : Bool
  deriving Inhabited, Repr

/-- What a register in scope may address: nothing, or the heap window
`[v + lo, v + hi)`. -/
structure Val where
  v : VReg
  window : Option (Int × Int) := none
  deriving Inhabited

structure Stats where
  programs : Nat := 0
  funcs : Nat := 0
  blocks : Nat := 0
  minBlocks : Nat := 1000000
  maxBlocks : Nat := 0
  /-- Programs with 1, 2–16, 17–64 and 65+ blocks. -/
  sizes : Array Nat := #[0, 0, 0, 0]
  stmts : Nat := 0
  calls : Nat := 0
  tails : Nat := 0
  loops : Nat := 0
  brOvfs : Nat := 0
  loads : Nat := 0
  stores : Nat := 0
  divs : Nat := 0
  shifts : Nat := 0
  params : Nat := 0
  exits : Nat := 0
  recursive : Nat := 0
  relabelled : Nat := 0
  wild : Nat := 0
  deriving Inhabited, Repr

structure St where
  rng : Rng
  cfg : Config
  sigs : Array Sig
  fi : FunId := 0
  blocks : Array Block := #[]
  next : VReg := 0
  budget : Nat := 0
  wild : Bool := false
  depth : Nat := 0
  selfFuel : Option VReg := none
  sharedFail : Option Label := none
  stats : Stats := {}

abbrev G := StateM St

def rand {α : Type} (m : RngM α) : G α :=
  modifyGet fun s => let (a, rng) := m.run s.rng; (a, { s with rng })

def chance (percent : Nat) : G Bool := rand (RngM.chance percent)
def range (lo hi : Nat) : G Nat := rand (RngM.range lo hi)
def weighted (ws : List Nat) : G Nat := rand (RngM.weighted ws)

def stat (f : Stats → Stats) : G Unit := modify fun s => { s with stats := f s.stats }

def fresh : G VReg := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def freshN (n : Nat) : G (List VReg) := (List.range n).mapM fun _ => fresh

/-- Reserve `n` blocks of the budget; false (and nothing reserved) if short. -/
def reserve (n : Nat) : G Bool := do
  let s ← get
  if s.budget < n then return false
  set { s with budget := s.budget - n }
  return true

/-- A block whose terminator is set later (`trap` until then). -/
def newBlock (params : List VReg := []) (cold := false) : G Label := do
  stat fun t => { t with params := t.params + params.length }
  modifyGet fun s => (s.blocks.size, { s with blocks := s.blocks.push { params, term := .trap, cold } })

def emit (b : Label) (stmt : Stmt) : G Unit := do
  stat fun t => { t with stmts := t.stmts + 1 }
  modify fun s => { s with blocks := s.blocks.modify b fun blk => { blk with body := blk.body.push stmt } }

def setTerm (b : Label) (t : Term) : G Unit :=
  modify fun s => { s with blocks := s.blocks.modify b fun blk => { blk with term := t } }

def assign (b : Label) (r : Rhs) : G VReg := do
  let x ← fresh
  emit b (.assign x r)
  return x

/-! ## Operands -/

def interesting : Array Word :=
  #[0, 1, 2, 3, 7, 31, 32, 63, 64, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff,
    0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff,
    0x8000000000000000, 0xffffffffffffffff, 0xfffffffffffffffe]

def immWord : G Word := do
  match ← weighted [5, 3, 2] with
  | 0 => rand (RngM.pick interesting)
  | 1 => return UInt64.ofNat (← range 0 99)
  | _ => rand RngM.word

def pickVal (env : Array Val) : G VReg := do
  return (← rand (RngM.pick env)).v

def pickArg (env : Array Val) : G Arg := do
  if !env.isEmpty && (← chance 75) then return .v (← pickVal env)
  return .imm (← immWord)

def argsFrom (env : Array Val) (n : Nat) : G (List Arg) := (List.range n).mapM fun _ => pickArg env

def width : G Width := do
  match ← weighted [1, 1, 2, 6] with
  | 0 => return .w8
  | 1 => return .w16
  | 2 => return .w32
  | _ => return .w64

def conds : Array Cond := #[.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge, .tz, .tnz]

def cond : G Cond := rand (RngM.pick conds)

def scale : G X86.Scale := rand (RngM.pick #[.one, .two, .four, .eight])

/-- A heap address `[p + i·s + d]` of `bytes` bytes inside some pointer's
window, emitting the index computation into `b`. -/
def heapAddr (b : Label) (env : Array Val) (bytes : Nat) : G (Option Addr) := do
  let ptrs := env.filter (·.window.isSome)
  if ptrs.isEmpty then return none
  let p ← rand (RngM.pick ptrs)
  let (lo, hi) := p.window.getD (0, 0)
  let indexed ← chance 60
  let s ← scale
  let span : Int := if indexed then 31 * (s.word.toNat : Int) else 0
  let room := hi - span - bytes - lo
  if room < 0 then return none
  let d := lo + ((← range 0 room.toNat) : Int)
  if indexed then
    let i ← assign b (.bin .and .w64 (← pickArg env) (.imm 31))
    return some { base := some (.v p.v), index := some (i, s), disp := d }
  return some { base := some (.v p.v), disp := d }

/-- A context-block address: a field below `ctx`, or a head above it. -/
def ctxAddr (b : Label) (env : Array Val) (write : Bool) : G Addr := do
  if !write && (← chance 30) then
    return { base := some .ctx, disp := -64 + 8 * ((← range 0 7) : Int) }
  if ← chance 50 then
    let i ← assign b (.bin .and .w64 (← pickArg env) (.imm 31))
    return { base := some .ctx, index := some (i, .eight), disp := 8 }
  return { base := some .ctx, disp := 8 * ((← range 1 32) : Int) }

/-! ## Statements -/

/-- A call along the DAG or, inside a recursive branch, to itself. -/
def genCall (b : Label) (env : Array Val) (tail : Bool) : G (Option (FunId × List Arg)) := do
  let s ← get
  let sig := s.sigs[s.fi]!
  let mut candidates := (List.range s.sigs.size).filter fun j =>
    j > s.fi && (!tail || s.sigs[j]!.results == sig.results)
  if sig.recursive && s.selfFuel.isSome then candidates := s.fi :: candidates
  if candidates.isEmpty then return none
  let j ← rand (RngM.pick candidates.toArray)
  let callee := s.sigs[j]!
  let mut args := []
  let mut rest := callee.params
  if callee.recursive then
    let fuel ← if j == s.fi then pure (Arg.v s.selfFuel.get!) else do
      let a ← pickArg env
      Arg.v <$> assign b (.bin .and .w64 a (.imm 3))
    args := [fuel]
    rest := rest - 1
  args := args ++ (← argsFrom env rest)
  return some (j, args)

def genStmt (b : Label) (env : Array Val) : G (Array Val) := do
  let s ← get
  let plain (x : VReg) : Array Val := env.push { v := x }
  let cfg := s.cfg
  match ← weighted [2, 1, 8, if cfg.shiftOps.isEmpty then 0 else 3, if cfg.divs then 2 else 0,
      if cfg.selects then 2 else 0, if cfg.tests then 2 else 0, 3, 2, 1, 1, 1, 1, 2, if s.wild then 2 else 0] with
  | 0 => return plain (← assign b (.arg (.imm (← immWord))))
  | 1 => return plain (← assign b (.arg (← pickArg env)))
  | 2 =>
      let o ← rand (RngM.pick #[BinOp.add, .sub, .and, .or, .xor, .mul])
      return plain (← assign b (.bin o (← width) (← pickArg env) (← pickArg env)))
  | 3 =>
      stat fun t => { t with shifts := t.shifts + 1 }
      let o ← rand (RngM.pick cfg.shiftOps)
      let amount ← if cfg.varShifts && (← chance 50) then Arg.v <$> pickVal env else Arg.imm <$> (UInt64.ofNat <$> range 0 70)
      return plain (← assign b (.bin o (← width) (← pickArg env) amount))
  | 4 =>
      stat fun t => { t with divs := t.divs + 1 }
      let o ← rand (RngM.pick #[BinOp.udiv, .urem])
      let w ← width
      let d ← assign b (.bin .or w (← pickArg env) (.imm 1))
      return plain (← assign b (.bin o w (← pickArg env) (.v d)))
  | 5 =>
      return plain (← assign b (.select (← cond) (← width) (← pickArg env) (← pickArg env)
        (← pickArg env) (← pickArg env)))
  | 6 => return plain (← assign b (.test (← cond) (← width) (← pickArg env) (← pickArg env)))
  | 7 =>
      let w ← width
      match ← heapAddr b env w.bytes with
      | some m =>
          stat fun t => { t with loads := t.loads + 1 }
          let e ← rand (RngM.pick #[Ext.zero, .sign])
          return plain (← assign b (.load w e m))
      | none => return env
  | 8 =>
      let w ← width
      match ← heapAddr b env w.bytes with
      | some m =>
          stat fun t => { t with stores := t.stores + 1 }
          emit b (.store w m (← pickArg env))
          return env
      | none => return env
  | 9 =>
      stat fun t => { t with loads := t.loads + 1 }
      return plain (← assign b (.load .w64 .zero (← ctxAddr b env false)))
  | 10 =>
      stat fun t => { t with stores := t.stores + 1 }
      emit b (.store .w64 (← ctxAddr b env true) (← pickArg env))
      return env
  | 11 =>
      -- A derived heap pointer `[root + i·8 + c]`, with its own window.
      match env.find? (·.window == some (0, (Region.heapSize : Int))) with
      | some root =>
          let c ← range 0 512
          let i ← assign b (.bin .and .w64 (← pickArg env) (.imm 31))
          let p ← assign b (.addr { base := some (.v root.v), index := some (i, .eight), disp := c })
          return env.push { v := p, window := some (-(c : Int), (Region.heapSize : Int) - c - 248) }
      | none => return env
  | 12 =>
      -- Address arithmetic on arbitrary values (`lea`), never dereferenced.
      let base ← if ← chance 80 then (some ∘ Base.v) <$> pickVal env else pure (some .ctx)
      let index ← if ← chance 50 then (fun x s => some (x, s)) <$> pickVal env <*> scale else pure none
      let disp : Int := (← range 0 200) - 100
      return plain (← assign b (.addr { base, index, disp }))
  | 13 =>
      match ← genCall b env false with
      | some (j, args) =>
          stat fun t => { t with calls := t.calls + 1 }
          let rs ← freshN (← get).sigs[j]!.results
          emit b (.call rs j args)
          return env ++ rs.toArray.map ({ v := · })
      | none => return env
  | _ =>
      -- Wild: possibly stuck.
      match ← weighted [if cfg.divs then 3 else 0, 1, 1] with
      | 0 =>
          stat fun t => { t with divs := t.divs + 1 }
          let o ← rand (RngM.pick #[BinOp.udiv, .urem])
          return plain (← assign b (.bin o (← width) (← pickArg env) (← pickArg env)))
      | 1 =>
          stat fun t => { t with stores := t.stores + 1 }
          emit b (.store .w64 { base := some .ctx, disp := 0x800 - 64 + 8 * ((← range 0 8) : Int) }
            (← pickArg env))
          return env
      | _ =>
          stat fun t => { t with loads := t.loads + 1 }
          return plain (← assign b (.load .w64 .zero { base := some .ctx, disp := 0x10000 }))

def genStmts (b : Label) (env : Array Val) : G (Array Val) := do
  let mut env := env
  for _ in [:← range 0 5] do
    env ← genStmt b env
  return env

/-! ## Control -/

def branchOperands (env : Array Val) : G (Cond × Width × Arg × Arg) := do
  return (← cond, ← width, ← pickArg env, ← pickArg env)

/-- The shared cold overflow block (a critical-edge source when shared). -/
def sharedFail : G (Option Label) := do
  if let some l := (← get).sharedFail then return some l
  unless ← reserve 1 do return none
  let l ← newBlock [] true
  setTerm l (.fail .natOverflow)
  modify fun s => { s with sharedFail := some l }
  return some l

/-- An exit terminator for block `x`: failure, trap, return or tail call. -/
def exitTerm (x : Label) (env : Array Val) : G Unit := do
  let s ← get
  let sig := s.sigs[s.fi]!
  match ← weighted [2, 1, 1, 4, 2, 1] with
  | 0 => setTerm x (.fail .heap)
  | 1 => setTerm x (.fail .natOverflow)
  | 2 => setTerm x .trap
  | 3 => setTerm x (.ret (← argsFrom env sig.results))
  | 5 => setTerm x (.fail .stack)
  | _ =>
      match ← genCall x env true with
      | some (j, args) =>
          stat fun t => { t with tails := t.tails + 1 }
          setTerm x (.tail j args)
      | none => setTerm x (.ret (← argsFrom env sig.results))

def genSeq : Nat → Label → Array Val → G (Label × Array Val)
  | 0, cur, env => return (cur, env)
  | fuel + 1, cur, env => do
    let env ← genStmts cur env
    if (← get).budget == 0 || (← chance 12) then return (cur, env)
    let critical := (← get).cfg.critical
    match ← weighted [4, if critical then 2 else 0, if (← get).depth < 3 then 3 else 0, 3, 2, 2] with
    | 0 =>
        -- Diamond.
        unless ← reserve 3 do return (cur, env)
        let (c, w, a, b) ← branchOperands env
        let t ← newBlock
        let f ← newBlock
        setTerm cur (.br c w a b ⟨t, []⟩ ⟨f, []⟩)
        let (tEnd, tEnv) ← genSeq fuel t env
        let (fEnd, fEnv) ← genSeq fuel f env
        let ps ← freshN (← range 0 3)
        let j ← newBlock ps
        setTerm tEnd (.jump ⟨j, ← argsFrom tEnv ps.length⟩)
        setTerm fEnd (.jump ⟨j, ← argsFrom fEnv ps.length⟩)
        genSeq fuel j (env ++ ps.toArray.map ({ v := · }))
    | 1 =>
        -- Triangle: the direct edge to the join is critical.
        unless ← reserve 2 do return (cur, env)
        let (c, w, a, b) ← branchOperands env
        let t ← newBlock
        let (tEnd, tEnv) ← genSeq fuel t env
        let ps ← freshN (← range 0 3)
        let j ← newBlock ps
        let direct : Edge := ⟨j, ← argsFrom env ps.length⟩
        setTerm cur (if ← chance 50 then .br c w a b ⟨t, []⟩ direct else .br c w a b direct ⟨t, []⟩)
        setTerm tEnd (.jump ⟨j, ← argsFrom tEnv ps.length⟩)
        genSeq fuel j (env ++ ps.toArray.map ({ v := · }))
    | 2 =>
        -- Counted loop: header `h(i, carried…)`, body, exit.
        unless ← reserve 3 do return (cur, env)
        stat fun t => { t with loops := t.loops + 1 }
        let bound ← if ← chance 40 then Arg.imm <$> (UInt64.ofNat <$> range 1 8) else do
          let a ← pickArg env
          Arg.v <$> assign cur (.bin .and .w64 a (.imm (← rand (RngM.pick #[3, 7]))))
        let i ← fresh
        let carried ← freshN (← range 0 2)
        let h ← newBlock (i :: carried)
        setTerm cur (.jump ⟨h, .imm 0 :: (← argsFrom env carried.length)⟩)
        let body ← newBlock
        let inner := env ++ (i :: carried).toArray.map ({ v := · })
        modify fun s => { s with depth := s.depth + 1 }
        let (bEnd, bEnv) ← genSeq fuel body inner
        modify fun s => { s with depth := s.depth - 1 }
        let i' ← assign bEnd (.bin .add .w64 (.v i) (.imm 1))
        setTerm bEnd (.jump ⟨h, .v i' :: (← argsFrom bEnv carried.length)⟩)
        let x ← newBlock
        setTerm h (.br .ult .w64 (.v i) bound ⟨body, []⟩ ⟨x, []⟩)
        genSeq fuel x inner
    | 3 =>
        -- Overflow branch.
        stat fun t => { t with brOvfs := t.brOvfs + 1 }
        let o ← rand (RngM.pick #[Ovf.addC, .subB])
        let a ← pickArg env
        let b ← pickArg env
        let x ← fresh
        match ← weighted [4, 2, if critical then 1 else 0] with
        | 0 =>
            -- Failure on overflow, possibly through the shared block.
            unless ← reserve 1 do return (cur, env)
            let shared ← if critical && (← chance 50) then sharedFail else pure none
            let fail ← match shared with
              | some l => pure (some l)
              | none =>
                  if ← reserve 1 then
                    let l ← newBlock [] true
                    setTerm l (.fail .natOverflow)
                    pure (some l)
                  else pure none
            let some fail := fail | return (cur, env)
            let ok ← newBlock
            setTerm cur (.brOvf o x a b ⟨ok, []⟩ ⟨fail, []⟩)
            genSeq fuel ok (env.push { v := x })
        | 1 =>
            -- Both edges join (truncated subtraction's shape).
            unless ← reserve 3 do return (cur, env)
            let ok ← newBlock
            let ovf ← newBlock
            let r ← fresh
            setTerm cur (.brOvf o x a b ⟨ok, []⟩ ⟨ovf, []⟩)
            let y ← assign ok (.bin .or .w64 (.v x) (.imm 1))
            let j ← newBlock [r]
            setTerm ok (.jump ⟨j, [.v y]⟩)
            setTerm ovf (.jump ⟨j, [.imm 1]⟩)
            genSeq fuel j ((env.push { v := x }).push { v := r })
        | _ =>
            -- Both edges straight to one join, passing `x`: two critical edges.
            unless ← reserve 1 do return (cur, env)
            let r ← fresh
            let j ← newBlock [r]
            setTerm cur (.brOvf o x a b ⟨j, [.v x]⟩ ⟨j, [← pickArg (env.push { v := x })]⟩)
            genSeq fuel j ((env.push { v := x }).push { v := r })
    | 4 =>
        -- Early exit on a (usually rare) condition.
        unless ← reserve 2 do return (cur, env)
        stat fun t => { t with exits := t.exits + 1 }
        let x ← newBlock
        let cont ← newBlock
        let (c, w, a, b) ← if ← chance 80 then do
            let a ← pickArg env
            let k ← immWord
            pure (Cond.eq, X86.Width.w64, a, Arg.imm k)
          else branchOperands env
        setTerm cur (if ← chance 50 then .br c w a b ⟨x, []⟩ ⟨cont, []⟩ else
          .br (match c with | .eq => .ne | c => c) w a b ⟨cont, []⟩ ⟨x, []⟩)
        exitTerm x env
        let term := (← get).blocks[x]!.term
        match term with
        | .fail _ | .trap => modify fun s => { s with blocks := s.blocks.modify x ({ · with cold := true }) }
        | _ => pure ()
        genSeq fuel cont env
    | _ =>
        -- Straight edge to a new block with parameters.
        unless ← reserve 1 do return (cur, env)
        let ps ← freshN (← range 0 2)
        let n ← newBlock ps
        setTerm cur (.jump ⟨n, ← argsFrom env ps.length⟩)
        genSeq fuel n (env ++ ps.toArray.map ({ v := · }))

/-- Permute the non-entry labels: `perm[old] = new`. -/
def relabel (f : Func) (perm : Array Nat) : Func :=
  let blocks := Id.run do
    let mut out := Array.replicate f.blocks.size default
    for h : b in [:f.blocks.size] do
      let blk := f.blocks[b]
      let edges := blk.term.edges.map fun e => { e with target := perm[e.target]! }
      out := out.set! perm[b]! { blk with term := blk.term.setEdges edges }
    return out
  { f with blocks }

def shuffle (n : Nat) : G (Array Nat) := do
  let mut perm := Array.range n
  for k in [:n] do
    let i := n - 1 - k
    if i ≥ 2 then
      let j := 1 + (← range 0 (i - 1))
      perm := perm.swapIfInBounds i j
  return perm

def genFunc (fi : FunId) (budget : Nat) : G Func := do
  modify fun s =>
    { s with fi := fi, blocks := #[], next := 0, budget := budget, depth := 0, selfFuel := none, sharedFail := none }
  let sig := (← get).sigs[fi]!
  let params ← freshN sig.params
  let entry ← newBlock
  let heap ← assign entry (.load .w64 .zero { base := some .ctx, disp := Region.regionBaseOff })
  let env : Array Val := params.toArray.map ({ v := · }) |>.push
    { v := heap, window := some (0, (Region.heapSize : Int)) }
  let fuel := 4 * budget + 8
  let recursive ← if sig.recursive then reserve 2 else pure false
  let (last, env) ← if recursive then do
      stat fun t => { t with recursive := t.recursive + 1 }
      let base ← newBlock
      let recur ← newBlock
      setTerm entry (.br .eq .w64 (.v params.head!) (.imm 0) ⟨base, []⟩ ⟨recur, []⟩)
      setTerm base (.ret (← argsFrom env sig.results))
      let f1 ← assign recur (.bin .sub .w64 (.v params.head!) (.imm 1))
      modify fun s => { s with selfFuel := some f1 }
      genSeq fuel recur (env.push { v := f1 })
    else genSeq fuel entry env
  match ← weighted [16, 2, 1] with
  | 0 => setTerm last (.ret (← argsFrom env sig.results))
  | 1 => exitTerm last env
  | _ => setTerm last (if ← chance 50 then .fail .heap else .trap)
  let s ← get
  let conv := if fi == 0 && (← chance 30) then Conv.sysvExport "lir_main" else .internal
  let f : Func := { name := s!"g{fi}", params, results := sig.results, blocks := s.blocks, conv }
  stat fun t => { t with funcs := t.funcs + 1 }
  if f.blocks.size > 2 && (← chance s.cfg.relabel) then
    stat fun t => { t with relabelled := t.relabelled + 1 }
    return relabel f (← shuffle f.blocks.size)
  return f

/-- The raw program drawn from `rng` (it may contain critical edges), with
the generator's counts and the final `Rng` (whose tape, when it has one,
holds the choices drawn: MT.5's shrinking replays them). -/
def programWith (cfg : Config) (rng : Rng) : (Program × Stats) × Rng := Id.run do
  let gen : G Program := do
    let target ← match ← weighted [5, 3, 2] with
      | 0 => range 1 16
      | 1 => range 17 64
      | _ => range 65 (max 65 cfg.maxBlocks)
    let target := min target cfg.maxBlocks
    let nf := min (← range 1 cfg.maxFuncs) target
    let mut sigs := #[]
    for i in [:nf] do
      let recursive := i > 0 && (← chance 30)
      let params := (if recursive then 1 else 0) + (← range 0 3)
      sigs := sigs.push { params, results := ← range 0 2, recursive }
    let wild ← chance cfg.wild
    modify fun s => { s with sigs, wild }
    if wild then stat fun t => { t with wild := t.wild + 1 }
    let share := target / nf
    let mut funcs := #[]
    for i in [:nf] do
      let budget := (if i == 0 then target - share * (nf - 1) else share) - 1
      funcs := funcs.push (← genFunc i budget)
    return { funcs, main := 0 }
  let (p, s) := gen.run { rng := rng, cfg, sigs := #[] }
  let blocks := p.funcs.foldl (fun n f => n + f.blocks.size) 0
  let bucket := if blocks ≤ 1 then 0 else if blocks ≤ 16 then 1 else if blocks ≤ 64 then 2 else 3
  let stats := { s.stats with
    programs := 1
    blocks := blocks
    minBlocks := blocks
    maxBlocks := blocks
    sizes := s.stats.sizes.modify bucket (· + 1) }
  return ((p, stats), s.rng)

/-- The raw program for `seed` (it may contain critical edges), with the
generator's counts. -/
def program (cfg : Config) (seed : UInt64) : Program × Stats :=
  (programWith cfg (Rng.ofSeed seed)).1

/-- Arguments for `main` drawn from `rng`, with the final `Rng`. -/
def mainArgsWith (p : Program) (rng : Rng) : List Word × Rng :=
  let count := (p.funcs[p.main]?.map (·.params.length)).getD 0
  let gen : G (List Word) := (List.range count).mapM fun _ => immWord
  let (args, s) := gen.run { rng, cfg := {}, sigs := #[] }
  (args, s.rng)

/-- Arguments for `main`, derived from the seed. -/
def mainArgs (p : Program) (seed : UInt64) : List Word :=
  (mainArgsWith p (Rng.ofSeed (Rng.derive seed 1))).1

def Stats.add (a b : Stats) : Stats :=
  { programs := a.programs + b.programs, funcs := a.funcs + b.funcs, blocks := a.blocks + b.blocks
    minBlocks := min a.minBlocks b.minBlocks, maxBlocks := max a.maxBlocks b.maxBlocks
    sizes := (a.sizes.zip b.sizes).map fun (x, y) => x + y
    stmts := a.stmts + b.stmts, calls := a.calls + b.calls, tails := a.tails + b.tails
    loops := a.loops + b.loops, brOvfs := a.brOvfs + b.brOvfs, loads := a.loads + b.loads
    stores := a.stores + b.stores, divs := a.divs + b.divs, shifts := a.shifts + b.shifts
    params := a.params + b.params, exits := a.exits + b.exits, recursive := a.recursive + b.recursive
    relabelled := a.relabelled + b.relabelled, wild := a.wild + b.wild }

end IxCCTests.Lir.Gen
