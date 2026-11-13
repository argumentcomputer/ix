import IxCC.Xv.Validate.Check
import IxCCTests.Xv.StackingLinear
import IxCCTests.Lir.Gen
import IxCCTests.Lir.Kernels

/-! # The validator's tracked walk against its first form

`Xv.Validate.checkBlock` walks a block on `Tracked` (the state with the registers it may hold and
the outgoing cells that may hold something), so a call or a definition does no pass over the whole
state; `Xv/Validate/Proof/Tracked.lean` proves it equal to `checkBlockList`, the definition before
2026-11-13. Tested before it was landed, and kept: on each allocation given, every block's
`checkBlock` and `checkBlockList`, and `Validate.program` against the whole check written out with
`checkBlockList` (`programList`), must give the same result, the same error included.
`tests-own-owned` passes every corpus root's allocations on both routes (the producer's), then the
same allocations with certificates edited to be wrong in each way the walk reads them (a fact
dropped, a fact claiming a register at a location that does not hold it, a fact claiming a register
the block defines later, an edit dropped or retargeted to an outgoing cell). It also counts the
walks whose `forget` found its register listed (the only case that still passes over the state):
none on the producer's allocations is expected (Xv is SSA, and a claim before a definition fails an
earlier block's edge check first, as Cfg numbers every forward edge upward). -/

set_option autoImplicit false

namespace IxCCTests.Xv.ValidateTracked

open IxCC IxCC.Xv IxCC.Xv.Validate
open IxCC.Lir (VReg)
open IxCC.Xv.Alloc (Edit Output BlockOut takeAt editsOrdered)

/-- `Validate.checkBlocks`, `func` and `program` with `checkBlockList`: the check before
2026-11-13, written out. -/
def checkBlocksList (c : Ctx) (fi : Nat) (info : BlockInfo) :
    List (Block VReg) → List BlockOut → Nat → Except Err Unit
  | [], [], _ => pure ()
  | b :: bs, o :: os, l => do
      match checkBlockList c info b o with
      | .error (pos, code) => throw { fn := fi, block := l, pos, code }
      | .ok () => checkBlocksList c fi info bs os (l + 1)
  | _, _, l => throw { fn := fi, block := l, code := .shape }

def funcList (env : Xl.Env) (fi : Nat) (f : Func VReg) (o : Output) : Except Err Unit := do
  unless sizeOk f o do throw { fn := fi, code := .shape }
  let blocks := f.blocks.toList
  unless blocks.length == o.blocks.length do throw { fn := fi, code := .shape }
  unless nodup f.params do throw { fn := fi, code := .params }
  let c : Ctx := { env, numSlots := o.numSlots, stackParams := f.params.length - Xl.nArgRegs }
  match o.blocks with
  | [] => throw { fn := fi, code := .shape }
  | o0 :: _ =>
      unless (AState.ofList o0.cert).le (entryState f.params) do throw { fn := fi, code := .entry }
  checkBlocksList c fi (blockInfo blocks o.blocks) blocks o.blocks 0

def programList (env : Xl.Env) (p : VProgram) (outs : List Output) : Except Err Unit :=
  go p.funcs.toList outs 0
where
  go : List (Func VReg) → List Output → Nat → Except Err Unit
    | [], [], _ => pure ()
    | f :: fs, o :: os, i => do funcList env i f o; go fs os (i + 1)
    | _, _, i => throw { fn := i, code := .shape }

structure Tally where
  programs : Nat := 0
  blocks : Nat := 0
  /-- block checks accepted and refused (by both) -/
  accepted : Nat := 0
  refused : Nat := 0
  edited : Nat := 0
  programsRefused : Nat := 0
  /-- walks in which a `forget` found its register listed -/
  scans : Nat := 0
  /-- the layout the scan needs, on the programs given (not the edits): blocks after the entry
  with no predecessor earlier in the order, and registers defined more than once -/
  laterPredOnly : Nat := 0
  redefined : Nat := 0
  programBlocks : Nat := 0
  failures : List String := []

def Tally.fail (t : Tally) (msg : String) : Tally := { t with failures := t.failures ++ [msg] }

/-! ## Counting the scans

A copy of the tracked walk's definitions that counts the `forget`s that find their register listed,
run beside the production walk (the count is not part of what is compared). -/

def forgetScans (s : Tracked) (defs : List (VReg × Loc)) : Nat × Tracked :=
  defs.foldl (fun (n, s) (v, _) => ((if (s.regs.find? v).isSome then n + 1 else n), s.forget v)) (0, s)

/-- Scans in one block's body: the tracked walk again, counting before each definition. -/
def bodyScans (c : Ctx) : Nat → Tracked → List (Inst VReg) → List (List Loc) → List (Nat × Edit) → Nat → Nat
  | n, a, inst :: insts, ls :: lss, es, i =>
    let (now, later) := takeAt i es
    match stepEditsT c a now with
    | .error _ => n
    | .ok a =>
      let defs : List (VReg × Loc) := match inst with
        | .call _ _ rets => rets.zip (resultLocs rets.length)
        | i => defsOfPairs (i.operands.zip ls)
      let a0 := match inst with | .call .. => a.clearOutArgs | _ => a
      let (k, _) := forgetScans a0 defs
      match stepInstT c a inst ls with
      | .error _ => n + k
      | .ok a' => bodyScans c (n + k) a' insts lss later (i + 1)
  | n, _, _, _, _, _ => n

/-- Two results agree: both accepted, or both refused with the same error. -/
def same {ε : Type} [DecidableEq ε] (r r' : Except ε Unit) : Bool :=
  match r, r' with
  | .ok (), .ok () => true
  | .error e, .error e' => decide (e = e')
  | _, _ => false

/-- Blocks after the entry none of whose predecessors comes earlier, and registers defined more
than once (function and block parameters, instruction definitions). -/
def layoutCounts (p : VProgram) : Nat × Nat × Nat := Id.run do
  let mut late := 0
  let mut redef := 0
  let mut blocks := 0
  for f in p.funcs.toList do
    let bs := f.blocks.toList
    blocks := blocks + bs.length
    let mut early : Validate.NatMap Unit := .leaf
    for (b, l) in bs.zipIdx do
      for e in b.term.edges do
        if l < e.target then early := early.insert e.target ()
    for l in (List.range bs.length).drop 1 do
      if (early.find? l).isNone then late := late + 1
    let mut seen : Validate.NatMap Unit := .leaf
    let defsOf (b : Block VReg) : List VReg :=
      b.params ++ (b.body.toList.flatMap fun i => (i.operands.filter (·.kind == .define)).map (·.v)) ++
        (b.term.operands.filter (·.kind == .define)).map (·.v)
    for v in f.params ++ bs.flatMap defsOf do
      if (seen.find? v).isSome then redef := redef + 1 else seen := seen.insert v ()
  return (late, redef, blocks)

/-- The checks `func` makes before it walks the blocks. -/
def preOk (f : Func VReg) (o : Output) : Bool :=
  sizeOk f o && f.blocks.toList.length == o.blocks.length && nodup f.params &&
    match o.blocks with
    | [] => false
    | o0 :: _ => (AState.ofList o0.cert).le (entryState f.params)

/-- Compare one program's allocation, block by block and as a whole. -/
def checkAlloc (t : Tally) (label : String) (env : Xl.Env) (p : VProgram) (outs : List Output) : Tally := Id.run do
  let mut t := { t with programs := t.programs + 1 }
  -- scans are counted only in the blocks `program` walks: in order, up to the first refusal
  let mut walking := true
  for ((f, o), fi) in (p.funcs.toList.zip outs).zipIdx do
    let blocks := f.blocks.toList
    let c : Ctx := { env, numSlots := o.numSlots, stackParams := f.params.length - Xl.nArgRegs }
    let info := blockInfo blocks o.blocks
    if walking && !preOk f o then walking := false
    for ((b, bo), l) in (blocks.zip o.blocks).zipIdx do
      t := { t with blocks := t.blocks + 1 }
      let r := checkBlock c info b bo
      unless same r (checkBlockList c info b bo) do t := t.fail s!"{label}: function {fi} block {l}: checkBlock"
      if walking && editsOrdered b.body.size bo.edits 0 then
        t := { t with scans := t.scans + bodyScans c 0 (Tracked.ofList bo.cert) b.body.toList bo.locs bo.edits 0 }
      match r with
      | .ok () => t := { t with accepted := t.accepted + 1 }
      | .error _ => t := { t with refused := t.refused + 1 }; walking := false
  let r := Validate.program env p outs
  unless same r (programList env p outs) do t := t.fail s!"{label}: program"
  if r.toBool == false then t := { t with programsRefused := t.programsRefused + 1 }
  return t

/-! ## Certificates made wrong -/

/-- A register the block's body defines, if any. -/
def laterDef (b : Block VReg) : Option VReg :=
  b.body.toList.findSome? fun i => (i.operands.find? (·.kind == .define)).map (·.v)

/-- Each way of making a block's certificate or edits wrong, for every block of every function
(one edit at a time): a fact dropped, a register added to a fact's location, a register the block
defines later claimed at a fresh slot, an edit dropped, an edit's destination made an outgoing
cell. -/
def edits (p : VProgram) (outs : List Output) : List (String × List Output) := Id.run do
  let mut r := []
  for ((f, o), fi) in (p.funcs.toList.zip outs).zipIdx do
    for (bo, l) in o.blocks.zipIdx do
      let b := (f.blocks[l]?).getD { term := .trap }
      let set (bo' : BlockOut) : List Output :=
        outs.modify fi fun o => { o with blocks := o.blocks.modify l fun _ => bo' }
      match bo.cert with
      | (loc, vs) :: rest =>
        r := r ++ [(s!"f{fi} b{l} fact dropped", set { bo with cert := rest })]
        let extra := (vs.foldl max 0) + 1
        r := r ++ [(s!"f{fi} b{l} register added", set { bo with cert := (loc, vs ++ [extra]) :: rest })]
      | [] => pure ()
      match laterDef b with
      | some v => r := r ++ [(s!"f{fi} b{l} later definition claimed",
          set { bo with cert := bo.cert ++ [(.slot 0, [v])] })]
      | none => pure ()
      match bo.edits with
      | (i, e) :: rest =>
        r := r ++ [(s!"f{fi} b{l} edit dropped", set { bo with edits := rest })]
        match e with
        | .move _ src => r := r ++ [(s!"f{fi} b{l} edit to an outgoing cell",
            set { bo with edits := (i, .move (.outArg 0) src) :: rest })]
      | [] => pure ()
  return r

def checkEdited (t : Tally) (label : String) (env : Xl.Env) (p : VProgram) (outs : List Output) (cap : Nat) : Tally :=
  (edits p outs).take cap |>.foldl (fun t (what, outs') =>
    let t := { t with edited := t.edited + 1 }
    checkAlloc t s!"{label} [{what}]" env p outs') t

/-- Both routes of one corpus root: the producer's allocations, then edited ones. -/
def checkRoot (t : Tally) (label : String) (names : List String) (env : Xl.Env) (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) (cap : Nat) : Tally :=
  match IxCCTests.Xv.StackingLinear.lirRoutes names env F bodies with
  | .error e => t.fail s!"{label}: lowering: {e}"
  | .ok rs => rs.foldl (fun t (route, lir, _, env) =>
      match Select.run lir with
      | .error _ => t.fail s!"{label} ({route}): select"
      | .ok (xv, _) =>
        match Alloc.runProducer env xv with
        | .error e => t.fail s!"{label} ({route}): alloc: {e}"
        | .ok a =>
          let (late, redef, nb) := layoutCounts xv
          let t := { t with laterPredOnly := t.laterPredOnly + late, redefined := t.redefined + redef,
                            programBlocks := t.programBlocks + nb }
          let t := checkAlloc t s!"{label} ({route})" env xv a.outs
          checkEdited t s!"{label} ({route})" env xv a.outs cap) t

/-- Generated Lir (`Lir.Gen`, a quarter of whose functions have their non-entry labels permuted, so
some blocks come before their predecessors) and the Lir kernels, selected and allocated, then their
allocations edited, `cap` edits each. -/
def synthetic (count cap : Nat) : Tally := Id.run do
  let kernels := [IxCCTests.Lir.Kernels.fib, IxCCTests.Lir.Kernels.sumLoop, IxCCTests.Lir.Kernels.gcd,
    IxCCTests.Lir.Kernels.natAdd, IxCCTests.Lir.Kernels.natMod].map IxCCTests.Lir.Kernels.program
  let gens := (List.range count).map fun seed =>
    (IxCCTests.Lir.Gen.program {} (UInt64.ofNat (seed * 7919 + 13))).1.splitCriticalEdges
  let mut t : Tally := {}
  for (p, i) in (kernels ++ gens).zipIdx do
    match Select.run p with
    | .error _ => continue
    | .ok (xv, _) =>
      match Alloc.runProducer {} xv with
      | .error _ => continue
      | .ok a =>
        let (late, redef, nb) := layoutCounts xv
        t := { t with laterPredOnly := t.laterPredOnly + late, redefined := t.redefined + redef,
                      programBlocks := t.programBlocks + nb }
        t := checkAlloc t s!"synthetic {i}" {} xv a.outs
        t := checkEdited t s!"synthetic {i}" {} xv a.outs cap
  return t

def report (label : String) (t : Tally) : List String × List String :=
  ([s!"validator walk ({label}): {t.programs} allocations ({t.edited} edited), {t.blocks} blocks (checkBlock accepted \
      {t.accepted}, refused {t.refused}), programs refused {t.programsRefused}; walks with a forget of a \
      listed register: {t.scans}; layout: of {t.programBlocks} blocks of the programs given, \
      {t.laterPredOnly} with no earlier predecessor, {t.redefined} registers defined twice; \
      {t.failures.length} failures"], t.failures)

end IxCCTests.Xv.ValidateTracked
