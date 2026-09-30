import CompilatrixTests.Pipeline.Support
import CompilatrixTests.Lam.Support
import CompilatrixTests.Support.Rng

/-! Certificate mutations (M1.I1): a wrong certificate is rejected, or it
makes code that still agrees on every tested input; it never makes wrong
code (design note 00, D17).

For each bench-k1 entry, the certificate `produce` made is corrupted by
random mutations in each class below and given to `Recheck.run`:

| Part | Classes |
| --- | --- |
| table | drop an entry, point an `eqn` at another theorem, change an entry's kind, add an entry, drop or add a recursor kind, change a `lazy` arity |
| relevance | change a node tag's class, drop a node's tags, change a constant's parameter or result class, change a constructor field's class |
| middle end | drop, duplicate or swap steps, change a shrink round count, add or drop an inline callee, flip a specialisation mask bit or add a decision, change the shrink bounds, truncate the steps |
| allocation | change an operand's or terminator's location, drop, add or move an edit, change a block-entry fact, change the slot count, swap two functions' allocations |
| frames | change a frame's size, a slot's or a save's offset, the outgoing-argument count; drop a layout |
| order | swap, drop, duplicate or move a block; rotate a group |

Each mutant is **rejected** (its stage and code are tallied), or accepted
with the **same object**, or accepted with a **different object**, which is
then run on the entry's model inputs on the typed x86 machine and the byte
machine (both, from `cx_init`; and natively at the test size with `--cc`)
and must return the original's result. A resource failure (`heap`,
`stack`, `natOverflow`) is an allowed extra outcome and is counted; so is
any result on an input where SrcEval, under the mutant's own table and
annotation, is stuck or times out (the top theorem's `GoesWrong` disjunct:
a relevance annotation the checker accepts can make the source stuck). Any
other difference fails the suite. -/

namespace CompilatrixTests.Pipeline.Mutants

open Compilatrix Compilatrix.Recheck CompilatrixTests.Src
open CompilatrixTests.Support (RngM Rng)
open CompilatrixTests.Backend (Exit)

abbrev Mut := Cert → RngM (Option Cert)

/-! ## Helpers -/

def swapAt {α : Type} (xs : List α) (i j : Nat) : List α :=
  match xs[i]?, xs[j]? with
  | some a, some b => (xs.set i b).set j a
  | _, _ => xs

def insertAt {α : Type} (xs : List α) (i : Nat) (x : α) : List α := xs.take i ++ x :: xs.drop i

/-- Modify a random element for which `f` gives a change. -/
def modifyRandom {α : Type} (xs : List α) (f : α → RngM (Option α)) : RngM (Option (List α)) := do
  if xs.isEmpty then return none
  -- a few positions, until one of them has a change
  for _ in [0:8] do
    let i ← RngM.below xs.length
    if let some x := xs[i]? then
      if let some y ← f x then return some (xs.set i y)
  return none

def bump (n : Nat) : RngM Nat := do
  match ← RngM.below 4 with
  | 0 => return n + 1
  | 1 => return n - 1
  | 2 => return 0
  | _ => return n + 1 + (← RngM.below 8)

def randomPropWhen : RngM Src.PropWhen := do
  if ← RngM.chance 50 then return .never else return .allZero (if ← RngM.chance 50 then [] else [0])

def randomRel : RngM Src.Rel := do
  match ← RngM.below 3 with
  | 0 => return .rel
  | 1 => return .proof (← randomPropWhen)
  | _ => return .type

def otherRel (r : Src.Rel) : RngM Src.Rel := do
  for _ in [0:8] do
    let r' ← randomRel
    if r' != r then return r'
  return if r == .rel then Src.Rel.prf else .rel

/-! ## Table -/

def tableCol (c : Cert) (t : Src.Table.TableCert) : Cert := { c with table := t }

def tableDrop : Mut := fun c => do
  if c.table.resolve.isEmpty then return none
  let i ← RngM.below c.table.resolve.length
  return some (tableCol c { c.table with resolve := c.table.resolve.eraseIdx i })

def tableRetarget : Mut := fun c => do
  let r ← modifyRandom c.table.resolve fun (f, e) => do
    match e with
    | .eqn thm => return some (f, .eqn (thm + 1 + (← RngM.below 5)))
    | .csimp g thm => return some (f, .csimp (g + 1) thm)
    | _ => return none
  return r.map fun rs => tableCol c { c.table with resolve := rs }

def tableKind : Mut := fun c => do
  let r ← modifyRandom c.table.resolve fun (f, e) => do
    let e' : Src.Table.Entry := match e with
      | .eqn _ => .case
      | .case => .prim .add
      | .prim _ => .eqn f
      | .csimp _ thm => .eqn thm
    return some (f, e')
  return r.map fun rs => tableCol c { c.table with resolve := rs }

def tableAdd : Mut := fun c => do
  let f ← RngM.below 60
  let e : Src.Table.Entry ← match ← RngM.below 3 with
    | 0 => pure .case
    | 1 => pure (.eqn (← RngM.below 60))
    | _ => pure (.prim .add)
  return some (tableCol c { c.table with resolve := (f, e) :: c.table.resolve })

def tableRecKind : Mut := fun c => do
  if (← RngM.chance 50) && !c.table.recKind.isEmpty then
    let i ← RngM.below c.table.recKind.length
    return some (tableCol c { c.table with recKind := c.table.recKind.eraseIdx i })
  return some (tableCol c { c.table with recKind := (← RngM.below 60) :: c.table.recKind })

def tableLazy : Mut := fun c => do
  let r ← modifyRandom c.table.lazy fun (f, n) => do return some (f, ← bump n)
  return r.map fun ls => tableCol c { c.table with lazy := ls }

/-! ## Relevance -/

def relCol (c : Cert) (a : Src.Relevance.Ann) : Cert := { c with relevance := a }

def otherTag : Src.Relevance.Tag → RngM Src.Relevance.Tag
  | .lam r pw => do
    if ← RngM.chance 50 then return .lam (← otherRel r) pw
    return .lam r (if pw == .never then Src.PropWhen.always else .never)
  | .arg r => do return .arg (← otherRel r)
  | .letE r => do return .letE (← otherRel r)

def relTag : Mut := fun c => do
  let r ← modifyRandom c.relevance.nodes fun (k, ts) => do
    let ts' ← modifyRandom ts fun t => do return some (← otherTag t)
    return ts'.map (k, ·)
  return r.map fun ns => relCol c { c.relevance with nodes := ns }

def relNode : Mut := fun c => do
  let ns := c.relevance.nodes
  if ns.isEmpty then return none
  let i ← RngM.below ns.length
  if ← RngM.chance 50 then return some (relCol c { c.relevance with nodes := ns.eraseIdx i })
  let r ← modifyRandom ns fun (k, ts) => do
    if ts.isEmpty then return none
    return some (k, ts.eraseIdx (← RngM.below ts.length))
  return r.map fun ns => relCol c { c.relevance with nodes := ns }

def relConst : Mut := fun c => do
  let r ← modifyRandom c.relevance.consts.toList fun (k, cr) => do
    if (← RngM.chance 30) || cr.params.isEmpty then
      return some (k, { cr with result := ← otherRel cr.result })
    let ps ← modifyRandom cr.params fun p => do return some (← otherRel p)
    return ps.map fun ps => (k, { cr with params := ps })
  return r.map fun cs => relCol c { c.relevance with consts := Src.NatMap.ofList cs }

def relCtor : Mut := fun c => do
  let r ← modifyRandom c.relevance.ctors.toList fun (k, cr) => do
    let fs ← modifyRandom cr.fields fun f => do
      match f with
      | .keep => return some Src.Relevance.FieldClass.prf
      | .proof _ => return some .keep
      | .type => return some .keep
    return fs.map fun fs => (k, { fields := fs })
  return r.map fun cs => relCol c { c.relevance with ctors := Src.NatMap.ofList cs }

/-! ## The middle end -/

def midCol (c : Cert) (steps : List Anf.Pipeline.Step) : Cert := { c with mid := { c.mid with steps } }

def midDrop : Mut := fun c => do
  if c.mid.steps.isEmpty then return none
  return some (midCol c (c.mid.steps.eraseIdx (← RngM.below c.mid.steps.length)))

def midDup : Mut := fun c => do
  let i ← RngM.below c.mid.steps.length
  match c.mid.steps[i]? with
  | some s => return some (midCol c (insertAt c.mid.steps i s))
  | none => return none

def midSwap : Mut := fun c => do
  if c.mid.steps.length < 2 then return none
  let i ← RngM.below (c.mid.steps.length - 1)
  return some (midCol c (swapAt c.mid.steps i (i + 1)))

def midRounds : Mut := fun c => do
  let r ← modifyRandom c.mid.steps fun
    | .shrink rs => do return (← modifyRandom rs fun n => do return some (← bump n)).map .shrink
    | _ => return none
  return r.map (midCol c)

def midInline : Mut := fun c => do
  let r ← modifyRandom c.mid.steps fun
    | .inline round => do
      if (← RngM.chance 50) || round.isEmpty then
        return some (.inline ((← RngM.below 12, [← RngM.below 12]) :: round))
      let r ← modifyRandom round fun (g, cs) => do
        if cs.isEmpty then return some (g, [← RngM.below 12])
        return some (g, cs.eraseIdx (← RngM.below cs.length))
      return r.map .inline
    | _ => return none
  return r.map (midCol c)

def midMask : Mut := fun c => do
  let r ← modifyRandom c.mid.steps fun
    | .specialize sc => do
      if (← RngM.chance 30) || sc.decisions.isEmpty then
        let mask ← (List.range (1 + (← RngM.below 7))).mapM fun _ => RngM.chance 50
        let d : Anf.Specialize.Decision := { caller := ← RngM.below 6, callee := ← RngM.below 6, mask }
        return some (.specialize { sc with decisions := d :: sc.decisions })
      let ds ← modifyRandom sc.decisions fun d => do
        if d.mask.isEmpty then return none
        let i ← RngM.below d.mask.length
        return some { d with mask := d.mask.set i !(d.mask[i]?.getD false) }
      return ds.map fun ds => .specialize { sc with decisions := ds }
    | _ => return none
  return r.map (midCol c)

def midParams : Mut := fun c => do
  let p := c.mid.shrink
  let k ← RngM.below 200
  let p' := if ← RngM.chance 50 then { p with caseOfCase := k } else { p with smallJoin := k % 60 }
  return some { c with mid := { c.mid with shrink := p' } }

def midTruncate : Mut := fun c => do
  return some (midCol c (c.mid.steps.take (← RngM.below c.mid.steps.length)))

/-! ## Allocation -/

def allocatable : Array X86.GPR :=
  #[.rax, .rcx, .rdx, .rbx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

def randomLoc : RngM Xv.Loc := do
  match ← RngM.weighted [6, 2, 1, 1] with
  | 0 => return .reg (← RngM.pick allocatable)
  | 1 => return .slot (← RngM.below 3)
  | 2 => return .inArg (← RngM.below 2)
  | _ => return .outArg (← RngM.below 2)

def otherLoc (l : Xv.Loc) : RngM Xv.Loc := do
  for _ in [0:8] do
    let l' ← randomLoc
    if l' != l then return l'
  return .slot 7

def allocCol (c : Cert) (f : Xv.Alloc.Output → RngM (Option Xv.Alloc.Output)) : RngM (Option Cert) := do
  return (← modifyRandom c.alloc f).map fun os => { c with alloc := os }

def blockCol (f : Xv.Alloc.BlockOut → RngM (Option Xv.Alloc.BlockOut)) (o : Xv.Alloc.Output) :
    RngM (Option Xv.Alloc.Output) := do
  return (← modifyRandom o.blocks f).map fun bs => { o with blocks := bs }

def allocLoc : Mut := fun c => allocCol c <| blockCol fun b => do
  let r ← modifyRandom b.locs fun ls => modifyRandom ls fun l => do return some (← otherLoc l)
  return r.map fun ls => { b with locs := ls }

def allocTermLoc : Mut := fun c => allocCol c <| blockCol fun b => do
  let r ← modifyRandom b.termLocs fun l => do return some (← otherLoc l)
  return r.map fun ls => { b with termLocs := ls }

def allocEdit : Mut := fun c => allocCol c <| blockCol fun b => do
  match ← RngM.below 3 with
  | 0 =>
    if b.edits.isEmpty then return none
    return some { b with edits := b.edits.eraseIdx (← RngM.below b.edits.length) }
  | 1 =>
    let e := Xv.Alloc.Edit.move (← randomLoc) (.reg (← RngM.pick allocatable))
    return some { b with edits := insertAt b.edits (← RngM.below (b.edits.length + 1)) (← RngM.below (b.locs.length + 1), e) }
  | _ =>
    let r ← modifyRandom b.edits fun (i, e) => do return some (← bump i, e)
    return r.map fun es => { b with edits := es }

def allocCert : Mut := fun c => allocCol c <| blockCol fun b => do
  match ← RngM.below 3 with
  | 0 =>
    if b.cert.isEmpty then return none
    return some { b with cert := b.cert.eraseIdx (← RngM.below b.cert.length) }
  | 1 =>
    let r ← modifyRandom b.cert fun (l, vs) => do return some (← otherLoc l, vs)
    return r.map fun cs => { b with cert := cs }
  | _ =>
    let r ← modifyRandom b.cert fun (l, vs) => do return some (l, (← RngM.below 20) :: vs)
    return r.map fun cs => { b with cert := cs }

def allocSlots : Mut := fun c => allocCol c fun o => do return some { o with numSlots := ← bump o.numSlots }

def allocSwap : Mut := fun c => do
  if c.alloc.length < 2 then return none
  let i ← RngM.below c.alloc.length
  let j ← RngM.below c.alloc.length
  if i == j then return none
  return some { c with alloc := swapAt c.alloc i j }

/-! ## Frames -/

def frameCol (c : Cert) (f : Xv.Stacking.FrameLayout → RngM (Option Xv.Stacking.FrameLayout)) :
    RngM (Option Cert) := do
  return (← modifyRandom c.frames f).map fun fs => { c with frames := fs }

def frameSize : Mut := fun c => frameCol c fun l => do
  let d := 8 * (1 + (← RngM.below 3))
  return some { l with size := if ← RngM.chance 50 then l.size + d else l.size - d }

def frameSlot : Mut := fun c => frameCol c fun l => do
  let r ← modifyRandom l.slotOff fun o => do return some (if ← RngM.chance 50 then o + 8 else o - 8)
  return r.map fun s => { l with slotOff := s }

def frameSave : Mut := fun c => frameCol c fun l => do
  if (← RngM.chance 30) && !l.saveOff.isEmpty then
    return some { l with saveOff := l.saveOff.eraseIdx (← RngM.below l.saveOff.length) }
  if (← RngM.chance 30) then
    return some { l with saveOff := (← RngM.pick #[X86.GPR.rbx, .r12, .r13, .r14], l.size) :: l.saveOff }
  let r ← modifyRandom l.saveOff fun (g, o) => do return some (g, if ← RngM.chance 50 then o + 8 else o - 8)
  return r.map fun s => { l with saveOff := s }

def frameOut : Mut := fun c => frameCol c fun l => do return some { l with outArgs := ← bump l.outArgs }

def frameDrop : Mut := fun c => do
  if c.frames.isEmpty then return none
  return some { c with frames := c.frames.eraseIdx (← RngM.below c.frames.length) }

/-! ## Order -/

def orderCol (c : Cert) (f : List Nat → RngM (Option (List Nat))) : RngM (Option Cert) := do
  return (← modifyRandom c.order f).map fun o => { c with order := o }

def orderSwap : Mut := fun c => orderCol c fun g => do
  if g.length < 2 then return none
  return some (swapAt g (← RngM.below g.length) (← RngM.below g.length))

def orderDrop : Mut := fun c => orderCol c fun g => do
  if g.isEmpty then return none
  return some (g.eraseIdx (← RngM.below g.length))

def orderDup : Mut := fun c => orderCol c fun g => do
  match g[← RngM.below g.length]? with
  | some b => return some (insertAt g (← RngM.below (g.length + 1)) b)
  | none => return none

def orderMove : Mut := fun c => do
  if c.order.length < 2 then return none
  let i ← RngM.below c.order.length
  let j ← RngM.below c.order.length
  match c.order[i]? with
  | some (b :: rest) =>
    if i == j then return none
    let o := c.order.set i rest
    return some { c with order := o.set j (b :: (o[j]?.getD [])) }
  | _ => return none

def orderRotate : Mut := fun c => orderCol c fun
  | b :: rest@(_ :: _) => return some (rest ++ [b])
  | _ => return none

/-! ## Running the mutants -/

def classes : List (String × Mut) :=
  [("table.drop", tableDrop), ("table.retarget", tableRetarget), ("table.kind", tableKind),
   ("table.add", tableAdd), ("table.recKind", tableRecKind), ("table.lazy", tableLazy),
   ("relevance.tag", relTag), ("relevance.node", relNode), ("relevance.const", relConst),
   ("relevance.ctor", relCtor),
   ("mid.drop", midDrop), ("mid.dup", midDup), ("mid.swap", midSwap), ("mid.rounds", midRounds),
   ("mid.inline", midInline), ("mid.mask", midMask), ("mid.params", midParams), ("mid.truncate", midTruncate),
   ("alloc.loc", allocLoc), ("alloc.termLoc", allocTermLoc), ("alloc.edit", allocEdit), ("alloc.cert", allocCert),
   ("alloc.slots", allocSlots), ("alloc.swap", allocSwap),
   ("frames.size", frameSize), ("frames.slot", frameSlot), ("frames.save", frameSave), ("frames.out", frameOut),
   ("frames.drop", frameDrop),
   ("order.swap", orderSwap), ("order.drop", orderDrop), ("order.dup", orderDup), ("order.move", orderMove),
   ("order.rotate", orderRotate)]

structure Tally where
  mutants : Nat := 0
  rejected : Nat := 0
  same : Nat := 0
  /-- Accepted with a different object that agrees on every tested input. -/
  agree : Nat := 0
  /-- Inputs where a mutant's object failed with an allowed resource. -/
  resource : Nat := 0
  /-- Inputs where SrcEval under the mutant's own certificate is stuck or
  times out, and the object's result differs. -/
  stuckSource : Nat := 0
  /-- Rejections by `stage: code`. -/
  codes : List (String × Nat) := []
  deriving Inhabited

def Tally.reject (t : Tally) (key : String) : Tally :=
  { t with rejected := t.rejected + 1
           codes := match t.codes.lookup key with
             | some n => (t.codes.filter (·.1 != key)) ++ [(key, n + 1)]
             | none => t.codes ++ [(key, 1)] }

/-- SrcEval on the mutant's own program is stuck or times out. -/
def sourceStuck (a : Artifact) (root : Root) (xs : List Nat) : IO Bool := do
  match ← CompilatrixTests.Lam.runSrc a.src 100000 root.const xs with
  | .stuck | .timeout => pure true
  | _ => pure false

/-- The accepted mutant `a'` against the original's expected exits on the
model inputs (typed x86 and the byte machine), and natively at the test size. -/
def behaves (a : Assert) (label : String) (orig a' : Artifact) (bench : String)
    (native : Option Rt.Native.Tools) (t : Tally) : IO Tally := do
  let some root := a'.roots.head? | throw (IO.userError s!"{label}: no root")
  let some oroot := orig.roots.head? | throw (IO.userError s!"{label}: no root")
  let c := compiledOf orig
  let mem ← IO.ofExcept (CompilatrixTests.Rt.initRegion c.lir)
  let c' := compiledOf a'
  let ms ← IO.ofExcept ((CompilatrixTests.Rt.Machine.initMachines c').mapError (s!"{label} cx_init: " ++ ·))
  let mut t := t
  let judge := fun (xs : List Nat) (want got : Exit) (t : Tally) => do
    if got == want then return t
    if got.status == 1 || got.status == 2 || got.status == 3 then return { t with resource := t.resource + 1 }
    if ← sourceStuck a' root xs then return { t with stuckSource := t.stuckSource + 1 }
    expect a false s!"{label} {xs}: the mutant's object gives {got.status}:{got.value}, \
      the original {want.status}:{want.value}"
    return t
  for xs in CompilatrixTests.Rt.Levels.modelArgs bench do
    let some want := CompilatrixTests.Rt.Levels.lirExpect c oroot.fn xs mem
      | throw (IO.userError s!"{label} {xs}: no original result")
    let got ← match CompilatrixTests.Rt.Machine.runExport c' root.symbol (xs.map UInt64.ofNat) ms with
      | .ok (e, _) => pure e
      | .error e => do expect a false s!"{label} {xs}: the mutant's object on the machines: {e}"; pure want
    t ← judge xs want got t
    a.modify (· + 1)
  if let some nt := native then
    let (args, want) ← CompilatrixTests.Src.Bench.testCase bench
    let exe ← link nt s!"mutant_{label.replace " " "_" |>.replace "." "_"}" a'.object root.symbol
    let lines ← Rt.Native.run exe { stack := 1 <<< 28 } [args]
    for l in lines do
      t ← judge args ⟨0, UInt64.ofNat (2 * want + 1)⟩ (exitOf l) t
      a.modify (· + 1)
  return t

/-- `count` mutants of each class for one entry. -/
def entry (a : Assert) (name : String) (count : Nat) (seed : Nat) (native : Option Rt.Native.Tools) :
    IO (List (String × Tally)) := do
  let inp ← benchInput name
  let cfg := Config.forInput {} inp
  let (cert, orig) ← compileIn name inp
  let mut out := []
  let mut seen : List ByteArray := []
  for (cls, mutate) in classes do
    let mut t : Tally := {}
    let mut g := Rng.ofSeed (UInt64.ofNat (seed * 7919 + cls.length * 131 + name.length))
    for i in [0:count] do
      let (m, g') := (mutate cert).run g
      g := g'
      let some m := m | continue
      t := { t with mutants := t.mutants + 1 }
      match ← IO.lazyPure fun _ => run cfg inp.program m with
      | .error e => t := t.reject s!"{e.stage.name}: {e.code}"
      | .ok a' =>
        if a'.object == orig.object then t := { t with same := t.same + 1 }
        else
          -- run each distinct object once
          if seen.contains a'.object then t := { t with agree := t.agree + 1 }
          else
            seen := a'.object :: seen
            let before := t.resource + t.stuckSource
            t ← behaves a s!"{name} {cls} {i}" orig a' name native t
            if t.resource + t.stuckSource == before then t := { t with agree := t.agree + 1 }
    out := out ++ [(cls, t)]
  return out

def render (t : Tally) : String :=
  let codes := ", ".intercalate (t.codes.map fun (k, n) => s!"{k} ×{n}")
  s!"{t.mutants} mutants: rejected {t.rejected}, same object {t.same}, different and agreeing {t.agree}, \
    resource {t.resource}, stuck source {t.stuckSource}{if codes.isEmpty then "" else s!" [{codes}]"}"

def run (a : Assert) (count seed : Nat) (native : Option Rt.Native.Tools) : IO (Array String) := do
  let mut totals : List (String × Tally) := classes.map fun (c, _) => (c, {})
  for name in benchNames do
    let per ← entry a name count seed native
    totals := totals.map fun (c, t) =>
      let u := (per.lookup c).getD {}
      (c, { mutants := t.mutants + u.mutants, rejected := t.rejected + u.rejected, same := t.same + u.same
            agree := t.agree + u.agree, resource := t.resource + u.resource, stuckSource := t.stuckSource + u.stuckSource
            codes := u.codes.foldl (fun cs (k, n) => match cs.lookup k with
              | some m => (cs.filter (·.1 != k)) ++ [(k, m + n)]
              | none => cs ++ [(k, n)]) t.codes })
  let all := totals.foldl (fun n (_, t) => n + t.mutants) 0
  let rejected := totals.foldl (fun n (_, t) => n + t.rejected) 0
  let same := totals.foldl (fun n (_, t) => n + t.same) 0
  let agree := totals.foldl (fun n (_, t) => n + t.agree) 0
  return #[s!"{all} mutants over the five entries: {rejected} rejected, {same} the same object, \
    {agree} a different object agreeing on every tested input"] ++
    (totals.map fun (c, t) => s!"  {c}: {render t}").toArray

end CompilatrixTests.Pipeline.Mutants
