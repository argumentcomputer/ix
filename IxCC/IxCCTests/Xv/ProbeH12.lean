import IxCC.Recheck
import IxCC.Recheck.Rc.Replay

/-! # The back end's two superlinear terms (probe, H12; removed before a landing)

`back CLOSURE EQS ROOT CERT zero|plain REPS`: reads a saved certificate, runs the verifier to the
selected and allocated program, then times `Xv.Validate.program` (production; a count of the state
at each call and definition; a prototype that skips the whole-state passes when nothing needs
them) and `Backend.lay` split into the parts of `Stacking.run` and layout. -/

set_option autoImplicit false

namespace IxCCTests.Xv.ProbeH12

open IxCC IxCC.Xv IxCC.Xv.Validate IxCC.Xv.Stacking
open IxCC.Lir (VReg Operand)
open IxCC.Xv.Alloc (Edit Output BlockOut takeAt editsOrdered)

def timeMs {α : Type} (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0).toFloat / 1e6)

def fmt (x : Float) : String := toString (Float.round (x * 10) / 10)

def stage {α : Type} (label : String) (f : Unit → Except Recheck.Err α) : IO α := do
  let (r, t) ← timeMs f
  match r with
  | .ok a => IO.println s!"  {label}: {fmt t} ms"; return a
  | .error e =>
    IO.println s!"  {label}: REFUSED {fmt t} ms: {(e.render).take 300}"
    throw (IO.userError s!"{label} refused")

/-- Time `f` `n` times (at least once); print the best time and the first result's tag. -/
def best {α : Type} (label : String) (n : Nat) (tag : α → String) (f : Unit → α) : IO α := do
  let (r0, t0) ← timeMs f
  let mut tmin := t0
  let mut sink := (tag r0).length
  for _ in [1:n] do
    let (x, t) ← timeMs f
    sink := sink + (tag x).length
    if t < tmin then tmin := t
  IO.println s!"  {label}: {fmt tmin} ms (best of {max n 1}) {tag r0} [{sink}]"
  return r0

def exTag {ε β : Type} (r : Except ε β) : String := match r with | .ok _ => "ok" | .error _ => "error"

/-! ## The validator: counts -/

structure Cnt where
  calls : Nat := 0
  callSize : Nat := 0
  defs : Nat := 0
  defSize : Nat := 0
  maxSize : Nat := 0
  moves : Nat := 0
  outMoves : Nat := 0
  deriving Repr

def countInst (c : Cnt) (a : AState) (inst : Inst VReg) : Cnt :=
  let s := a.size
  match inst with
  | .call _ _ rets =>
    { c with calls := c.calls + 1, callSize := c.callSize + s, defs := c.defs + rets.length,
             defSize := c.defSize + rets.length * s, maxSize := max c.maxSize s }
  | i =>
    let d := (i.operands.filter (·.kind == .define)).length
    { c with defs := c.defs + d, defSize := c.defSize + d * s, maxSize := max c.maxSize s }

def countEdits (c : Cnt) (es : List Edit) : Cnt :=
  es.foldl (fun c e => match e with
    | .move dst _ => { c with moves := c.moves + 1, outMoves := c.outMoves + (if isOutArg dst then 1 else 0) }) c

def walkC (ctx : Ctx) : Cnt → AState → List (Inst VReg) → List (List Loc) → List (Nat × Edit) → Nat → Cnt
  | cnt, a, inst :: insts, ls :: lss, es, i =>
    let (now, later) := takeAt i es
    let cnt := countEdits cnt now
    match stepEdits ctx a now with
    | .error _ => cnt
    | .ok a => match stepInst ctx a inst ls with
      | .error _ => cnt
      | .ok a' => walkC ctx (countInst cnt a inst) a' insts lss later (i + 1)
  | cnt, _, _, _, _, _ => cnt

def countProgram (env : Xl.Env) (p : VProgram) (outs : List Output) : Cnt :=
  (p.funcs.toList.zip outs).foldl (fun cnt (f, o) =>
    let ctx : Ctx := { env, numSlots := o.numSlots, stackParams := f.params.length - Xl.nArgRegs }
    (f.blocks.toList.zip o.blocks).foldl (fun cnt (b, bo) =>
      walkC ctx cnt (AState.ofList bo.cert) b.body.toList bo.locs bo.edits 0) cnt) {}

/-! ## The validator: a prototype that skips the whole-state passes

The state carries the registers it may hold (`ment`) and the outgoing cells it may hold (`outs`):
`forget v` is the identity when `v` is not mentioned, and `clearOutArgs` erases the listed cells. -/

structure IS where
  a : AState
  ment : Validate.NatMap Unit
  outs : List Nat

def IS.ofList (facts : List (Loc × List VReg)) : IS :=
  { a := AState.ofList facts
    ment := facts.foldl (fun m (_, vs) => vs.foldl (fun m v => m.insert v ()) m) .leaf
    outs := facts.filterMap fun (l, _) => if isOutArgKey (locKey l) then some (locKey l) else none }

def IS.forget (s : IS) (v : VReg) : IS :=
  if (s.ment.find? v).isSome then { s with a := s.a.forget v, ment := s.ment.erase v } else s

def IS.clearOutArgs (s : IS) : IS := { s with a := s.outs.foldl (fun a k => a.erase k) s.a, outs := [] }

def IS.define (s : IS) (defs : List (VReg × Loc)) (clobbers : List Loc) : IS :=
  let s := defs.foldl (fun s (v, _) => s.forget v) s
  let s := { s with a := clobbers.foldl AState.clear s.a }
  defs.foldl (fun s (v, l) =>
    { a := s.a.set l [v], ment := s.ment.insert v (),
      outs := if isOutArgKey (locKey l) then locKey l :: s.outs else s.outs }) s

def IS.stepMove (s : IS) (dst src : Loc) : IS :=
  { s with a := s.a.stepMove dst src,
           outs := if isOutArgKey (locKey dst) then locKey dst :: s.outs else s.outs }

def stepOperandsI (c : Ctx) (a : IS) (ops : List (Operand VReg)) (ls : List Loc) (row : Bool) :
    Except Code IS := do
  unless ops.length == ls.length do throw .shape
  let ps := ops.zip ls
  if let some code := operandCode c ps row then throw code
  unless usesHold a.a ps do throw .useMissing
  pure (a.define (defsOfPairs ps) [])

def stepInstI (c : Ctx) (a : IS) (inst : Inst VReg) (ls : List Loc) : Except Code IS :=
  match inst with
  | .call g args rets => do
      let ops := inst.operands
      unless ops.length == ls.length do throw .shape
      let n := args.length
      unless rets.length ≤ Xl.nResultRegs do throw .convention
      unless nodup rets do throw .alias
      unless ls.take n == argLocs n && ls.drop n == resultLocs rets.length do throw .convention
      unless (args.zip (argLocs n)).all (fun (v, l) => a.a.holds l v) do throw .useMissing
      let clobbers := (c.env.clobbers g).map Loc.reg
      pure ((a.clearOutArgs).define (rets.zip (resultLocs rets.length)) clobbers)
  | .move .. => do
      match ls with
      | [src, dst] => if src.isCell && dst.isCell then throw .cellMove
      | _ => pure ()
      stepOperandsI c a inst.operands ls false
  | .zero _ => stepOperandsI c a inst.operands ls false
  | .op o defs args => do
      unless rowShapeOk o defs args false do throw .constraint
      stepOperandsI c a inst.operands ls true
  | .fused p pargs q defs qargs => do
      unless rowShapeOk p [] pargs false && rowShapeOk q defs qargs true do throw .constraint
      stepOperandsI c a inst.operands ls true

def stepTermI (c : Ctx) (a : IS) (t : Term VReg) (ls : List Loc) : Except Code IS :=
  match t with
  | .jcc p pargs defs .. => do
      unless rowShapeOk p defs pargs false do throw .constraint
      stepOperandsI c a t.operands ls true
  | .ret vs => do
      unless vs.length ≤ Xl.nResultRegs && ls == resultLocs vs.length do throw .convention
      unless (vs.zip ls).all (fun (v, l) => a.a.holds l v) do throw .useMissing
      pure a
  | .tail _ args => do
      unless args.length ≤ Xl.nArgRegs && ls == argLocs args.length do throw .convention
      unless (args.zip ls).all (fun (v, l) => a.a.holds l v) do throw .useMissing
      pure a
  | .jmp _ | .fail _ | .trap => do
      unless ls.isEmpty do throw .shape
      pure a

def stepEditI (c : Ctx) (a : IS) : Edit → Except Code IS
  | .move dst src => do
      if let some code := editLocCode c dst then throw code
      if let some code := editLocCode c src then throw code
      if dst.isCell && src.isCell then throw .cellMove
      if (a.a.get src).isEmpty then throw .unknownSource
      pure (a.stepMove dst src)

def stepEditsI (c : Ctx) : IS → List Edit → Except Code IS
  | a, [] => pure a
  | a, e :: es => do stepEditsI c (← stepEditI c a e) es

def walkBodyI (c : Ctx) : IS → List (Inst VReg) → List (List Loc) → List (Nat × Edit) → Nat →
    Except (Nat × Code) (IS × List (Nat × Edit))
  | a, [], [], es, _ => pure (a, es)
  | a, inst :: insts, ls :: lss, es, i => do
      let (now, later) := takeAt i es
      let a ← (stepEditsI c a now).mapError (i, ·)
      let a ← (stepInstI c a inst ls).mapError (i, ·)
      walkBodyI c a insts lss later (i + 1)
  | _, _, _, _, i => throw (i, .shape)

def checkBlockI (c : Ctx) (info : BlockInfo) (b : Block VReg) (o : BlockOut) : Except (Nat × Code) Unit := do
  let body := b.body.toList
  let n := body.length
  unless nodup b.params do throw (0, .params)
  unless editsOrdered n o.edits 0 do throw (0, .editOrder)
  let (a, left) ← walkBodyI c (IS.ofList o.cert) body o.locs o.edits 0
  let (now, rest) := takeAt n left
  unless rest.isEmpty do throw (n, .editOrder)
  let a ← (stepEditsI c a now).mapError (n, ·)
  let a ← (stepTermI c a b.term o.termLocs).mapError (n, ·)
  if let some code := checkEdges info a.a b.term.edges then throw (n + 1, code)

def checkBlocksI (c : Ctx) (fi : Nat) (info : BlockInfo) :
    List (Block VReg) → List BlockOut → Nat → Except Err Unit
  | [], [], _ => pure ()
  | b :: bs, o :: os, l => do
      match checkBlockI c info b o with
      | .error (pos, code) => throw { fn := fi, block := l, pos, code }
      | .ok () => checkBlocksI c fi info bs os (l + 1)
  | _, _, l => throw { fn := fi, block := l, code := .shape }

def funcI (env : Xl.Env) (fi : Nat) (f : Func VReg) (o : Output) : Except Err Unit := do
  unless sizeOk f o do throw { fn := fi, code := .shape }
  let blocks := f.blocks.toList
  unless blocks.length == o.blocks.length do throw { fn := fi, code := .shape }
  unless nodup f.params do throw { fn := fi, code := .params }
  let c : Ctx := { env, numSlots := o.numSlots, stackParams := f.params.length - Xl.nArgRegs }
  match o.blocks with
  | [] => throw { fn := fi, code := .shape }
  | o0 :: _ =>
      unless (AState.ofList o0.cert).le (entryState f.params) do throw { fn := fi, code := .entry }
  checkBlocksI c fi (blockInfo blocks o.blocks) blocks o.blocks 0

def programI (env : Xl.Env) (p : VProgram) (outs : List Output) : Except Err Unit :=
  go p.funcs.toList outs 0
where
  go : List (Func VReg) → List Output → Nat → Except Err Unit
    | [], [], _ => pure ()
    | f :: fs, o :: os, i => do funcI env i f o; go fs os (i + 1)
    | _, _, i => throw { fn := i, code := .shape }

def errTag (r : Except Err Unit) : String :=
  match r with
  | .ok () => "ok"
  | .error e => s!"error {e.text}"

/-! ## Stacking: the parts of `run` -/

def resultsOfA (p : LProgram) (g : Lir.FunId) : Option Nat := (p.funcs[g]?).map (·.results)

def aritiesOkA (p : LProgram) (f : Func Loc) : Bool :=
  f.blocks.toList.all fun b =>
    b.body.toList.all (fun | .call g _ rets => resultsOfA p g == some rets.length | _ => true) &&
      match b.term with
      | .ret vs => vs.length == f.results
      | .tail g _ => resultsOfA p g == some f.results
      | _ => true

def callSites (p : LProgram) : Nat × Nat :=
  p.funcs.toList.foldl (fun (c, t) f => f.blocks.toList.foldl (fun (c, t) b =>
    (c + (b.body.toList.filter fun | .call .. => true | _ => false).length,
     t + match b.term with | .tail .. => 1 | _ => 0)) (c, t)) (0, 0)

def placeListL {α β : Type} (mk : α → Nat → β) (sz : α → Nat) : List α → Nat → List β
  | [], _ => []
  | x :: xs, n => mk x n :: placeListL mk sz xs (n + sz x)

def back (clo eqs : System.FilePath) (root : String) (certPath : System.FilePath) (kind : String)
    (reps : Nat) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile clo
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let text ← IO.FS.readFile certPath
  IO.println s!"== {root} {kind} {certPath}"
  let inp ← stage "ingress" fun _ => Recheck.ingress bytes json [root]
  let cfg := Recheck.Config.forInput {} inp
  -- the selected and allocated program, and the backend configuration, as the verifier makes them
  let (env, xv, outs, bcfg) ← if kind == "zero" then do
      let c ← stage "Cert.ofText" fun _ => Recheck.Cert.ofText text
      let f ← stage "Recheck.runLir" fun _ => Recheck.runLir cfg inp.program c
      let r := (f.src.roots.head?.map (·.1)).getD default
      let xv ← stage "Xv.Select.select" fun _ => (Xv.Select.select f.lowered.program).mapError Recheck.Err.ofSelect
      pure (cfg.env, xv, c.alloc, Recheck.backendConfig cfg f.lowered r c)
    else do
      let rc ← stage "RcReplay.Cert.ofText" fun _ => (Recheck.RcReplay.Cert.ofText text).mapError
        fun m => { stage := .cert, code := "cert.parse", message := m }
      let f ← stage "RcReplay.runFront" fun _ => Recheck.RcReplay.runFront cfg inp.program rc
      let r := (f.src.roots.head?.map (·.1)).getD default
      let pcfg := { cfg with provenance := some (cfg.provenance.getD (.ixir1Policy r 3 1)) }
      let xv ← stage "Xv.Select.select" fun _ => (Xv.Select.select f.lowered.program).mapError Recheck.Err.ofSelect
      pure (f.env pcfg.env, xv, rc.base.alloc,
        { Recheck.backendConfig pcfg f.lowered r rc.base with reps := f.reps, env := f.env pcfg.env })
  IO.println s!"  (Xv: {xv.funcs.size} functions)"
  -- the validator
  IO.println "-- Xv.Validate"
  let _ ← best "Validate.program (production)" reps errTag fun _ => Validate.program env xv outs
  let _ ← best "prototype (mentioned registers, listed outgoing cells)" reps errTag fun _ => programI env xv outs
  let (cnt, tc) ← timeMs fun _ => countProgram env xv outs
  IO.println s!"  counts ({fmt tc} ms): {repr cnt}"
  -- stacking and layout
  let xl ← stage "Xv.Alloc.applyProgram" fun _ => (Xv.Alloc.applyProgram xv outs).mapError
    fun message => { stage := .alloc, code := "alloc.apply", message }
  let (cs, ts) := callSites xl
  IO.println s!"  (Xl: {xl.funcs.size} functions, {cs} call sites, {ts} tail calls)"
  IO.println "-- Backend.lay"
  let _ ← best "Backend.lay (production)" reps exTag fun _ => Backend.lay xl bcfg
  let layouts := bcfg.layouts.getD (Stacking.produce xl)
  let _ ← best "Stacking.run" reps exTag fun _ => Stacking.run xl layouts bcfg.reps bcfg.env
  let fns ← best "withLayouts" reps (fun l => s!"{l.length}") fun _ => withLayouts xl layouts
  let _ ← best "layout checks" reps (fun b => s!"{b}") fun _ => fns.all fun (_, _, l, a) => l.check a
  let _ ← best "extraChanges (with tailResults)" reps (fun b => s!"{b}") fun _ =>
    fns.all fun (f, fn, l, a) => (extraChanges xl bcfg.env f fn l a).isEmpty
  let _ ← best "tailResults alone" reps (fun n => s!"{n}") fun _ =>
    fns.foldl (fun n (f, _, _, _) => n + (tailResults xl f).length) 0
  let _ ← best "aritiesOk (production, list index)" reps (fun b => s!"{b}") fun _ => fns.all fun (f, _, _, _) => aritiesOk xl f
  let _ ← best "aritiesOk (array index)" reps (fun b => s!"{b}") fun _ => fns.all fun (f, _, _, _) => aritiesOkA xl f
  let exports ← best "exportsOf" reps (fun l => s!"{l.length}") fun _ => exportsOf bcfg.reps fns
  let (wrappers, next) ← best "placeExports (production)" reps (fun (l, n) => s!"{l.length} {n}") fun _ => placeExports exports
  let (placed, _) ← best "placeFuncs (production, acc ++ [x])" reps (fun (l, n) => s!"{l.length} {n}") fun _ => placeFuncs fns next
  let _ ← best "placeFuncs (placeList)" reps (fun l => s!"{l.length}") fun _ =>
    placeListL (fun (e : Func Loc × Lir.FunId × FrameLayout × Facts) n =>
      ({ func := e.1, fn := e.2.1, layout := e.2.2.1, facts := e.2.2.2, start := n } : Placed))
      (fun e => funcBlocks e.1 e.2.2.1 e.2.2.2) fns next
  let entries ← best "entriesOf" reps (fun _ => "") fun _ => entriesOf placed
  let _ ← best "wrapperCode" reps exTag fun _ => (wrappers.zip exports).mapM fun (w, (_, _, _, f)) => wrapperOf entries w f
  let funcCode ← best "funcCode (emitFunc)" reps exTag fun _ => placed.mapM fun pl =>
    (emitFunc entries 0 pl.func pl.layout pl.facts pl.start).mapError (Error.func pl.fn)
  match funcCode with
  | .error e => IO.println s!"  emit error {e}"
  | .ok code =>
    let prog ← best "program blocks" reps (fun (p : X86.Program) => s!"{p.blocks.size}") fun _ =>
      ({ blocks := (exitGroup 0 ++ code.flatten).toArray, entry := 0 } : X86.Program)
    let _ ← best "wellFormedK" reps (fun b => s!"{b}") fun _ => prog.wellFormedK
  match Stacking.run xl layouts bcfg.reps bcfg.env with
  | .error e => IO.println s!"  stacking error {e}"
  | .ok st =>
    let tun ← best "X86.Layout.tunnel" reps (fun (p : X86.Program) => s!"{p.blocks.size}") fun _ => X86.Layout.tunnel st.program
    let order := bcfg.order.getD (X86.Layout.Order.produce tun st.shape)
    let _ ← best "X86.Layout.run" reps exTag fun _ => X86.Layout.run tun st.shape order
  return 0

end IxCCTests.Xv.ProbeH12

def main (args : List String) : IO UInt32 :=
  match args with
  | ["back", clo, eqs, root, cert, kind, reps] =>
    IxCCTests.Xv.ProbeH12.back clo eqs root cert kind reps.toNat!
  | _ => do
    IO.eprintln "usage: probe-h12 back CLOSURE EQS ROOT CERT zero|plain REPS"
    return 2
