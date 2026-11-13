import IxCCTests.Recheck.P1Twin.Twin

/-! The mutant pass. At sampled calls of a run the twin makes on a program the checks accept, (1) the
real call: exact `Pre`, and where it holds `Post`, `Pre` of every child step (`pre_step`, the shielded
exception excepted) and `Reads`; (2) mutants of the call's values: those `Pre` accepts are run (SrcEval)
and checked the same way; a failure is a counterexample to `preserve`/`pre_step`/`reads_live` when
`SortAgree` holds from the mutant (checked by a sub-run of the twin in `sortOnly` mode). A mutant `Pre`
rejects is classified by the clauses whose disabling alone makes `Pre` hold ("broken alone"); where it
then fails, with `SortAgree` holding, the clause is exercised at the mutant's step case. -/

namespace IxCCTests.Recheck.P1Twin

open IxCC IxCC.Src IxCC.Src.Relevance IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical
open IxCC.Sem (Result)

/-- The pass's sampling, deterministic: the same seed and budgets give the same counts. -/
structure PassCfg where
  repaired : Bool := true
  /-- Visits sampled per step case per program (at the visit counts 1, 2, 4, 8, ...). -/
  samples : Nat := 8
  /-- Mutants checked per (class, step case) per program. -/
  perClass : Nat := 12
  /-- Checks (real calls and mutants) per program; past it the program's run continues unsampled. -/
  maxChecks : Nat := 600
  /-- Rotates each call's mutant list (0: the generation order). -/
  seed : Nat := 0
  /-- Print each mutant before it is checked (to find one that aborts the process). -/
  trace : Bool := false
  /-- `Live`'s depth cut. -/
  depth : Nat := 12
  deriving Inhabited

/-- Aggregates over a process. -/
structure Agg where
  cls : IO.Ref (Std.HashMap String (Array Nat))
  table : IO.Ref (Std.HashMap String (Array Nat))
  real : IO.Ref (Std.HashMap String (Array Nat))
  realRej : IO.Ref (Std.HashMap String Nat)
  examples : IO.Ref (Std.HashMap String (Array String))
  findings : IO.Ref Nat
  /-- Rejected mutants per (program, class, step case, the clause broken alone). -/
  sole : IO.Ref (Std.HashMap String Nat)

def Agg.new : IO Agg := do
  return { cls := ← IO.mkRef {}, table := ← IO.mkRef {}, real := ← IO.mkRef {}, realRej := ← IO.mkRef {},
           examples := ← IO.mkRef {}, findings := ← IO.mkRef 0, sole := ← IO.mkRef {} }

def bumpArr (r : IO.Ref (Std.HashMap String (Array Nat))) (key : String) (i : Nat) (n : Nat := 8) : IO Unit :=
  r.modify fun m =>
    let a := m.getD key (Array.replicate n 0)
    m.insert key (a.modify i (· + 1))

def Agg.example (g : Agg) (key : String) (s : String) (keep : Nat := 3) : IO Unit :=
  g.examples.modify fun m =>
    let a := m.getD key #[]
    if a.size < keep then m.insert key (a.push s) else m

/-- Class counters: generated, Pre accepted, Pre undecided (depth cut), Post fails, a child's Pre
fails, Reads fails, of the failing ones SortAgree fails (excused), counterexamples. -/
def iGen := 0
def iAcc := 1
def iCut := 2
def iPost := 3
def iStep := 4
def iReads := 5
def iSortX := 6
def iFind := 7

/-- Per program. -/
structure PState where
  label : String
  cfg : PassCfg
  agg : Agg
  ex : ECx
  base : TCx
  checks : IO.Ref Nat
  visits : IO.Ref (Std.HashMap String Nat)
  sampled : IO.Ref (Std.HashMap String Nat)
  perCls : IO.Ref (Std.HashMap String Nat)
  stopped : IO.Ref Bool
  /-- Reached special heads with `erasedMinors` (partial applications that are not `Whole`). -/
  erasedElims : List (Head × Levels)
  unreachedDefn : Option CId
  quotCtorsErased : List CId
  /-- `ShapeOk.ctorUnique` on the program (a hypothesis of `preserve`; a failure where it is false is excused). -/
  shapeOk : Bool

structure Outcome where
  post : Bool
  steps : List String
  reads : Bool
  res : String

def Outcome.fails (o : Outcome) : Bool := !o.post || !o.steps.isEmpty || !o.reads

def Outcome.render (o : Outcome) : String :=
  s!"result {o.res}; Post {if o.post then "holds" else "FAILS"}; child Pre fails at {o.steps}; Reads {if o.reads then "holds" else "FAILS"}"

def levelsOf (q : Profile) : Levels := q.map fun z => if z then 0 else 1

def bumpLs (ls : Levels) : Option Levels :=
  if ls.any (· != 0) then some (ls.map fun n => if n == 0 then 0 else n + 1) else none

def flipLs (ls : Levels) : Option Levels :=
  match ls with
  | [] => none
  | l :: rest => some ((if l == 0 then 1 else 0) :: rest)

/-- `ls` with a zero at each of the positions `zs` (extended with ones where shorter). -/
def zeroAt (zs : List Nat) (ls : Levels) : Levels :=
  let n := max ls.length ((zs.foldl max 0) + 1)
  (List.range n).map fun i => if zs.contains i then 0 else ls.getD i 1

def irrM (ls : Levels) : Slot := .val (.irr none [] ls)

/-- The step classifier and the child steps whose `Pre` fails (exact `false`). -/
def outcomes (x : ECx) (more : List Term.Arg) (c : Call) : Outcome :=
  let r := callResult x.p c
  let (post, _) := runEM (postM x c r)
  let steps := (children x.p more c).filterMap fun (n, c', more') =>
    if shieldedStep c n c' then none
    else if (runEM (preM x more' c')).1 then none else some n
  let (reads, _) := runEM (readsM x c)
  { post, steps, reads, res := r.shape }

/-- The `SortAgree` clauses a run from `c` violates (the twin in `sortOnly` mode). -/
def sortRun (ps : PState) (more : List Term.Arg) (c : Call) : IO (List String) := do
  let counts ← IO.mkRef []
  let notes ← IO.mkRef []
  let noop : Call → List Term.Arg → IO Unit := fun _ _ => pure ()
  let sub : TCx := { ps.base with counts := counts, notes := notes, visit := noop, sortOnly := true }
  let _ ← tCall sub more c
  let cs ← sub.counts.get
  return (cs.filter (·.1.startsWith "VIOLATION (")).map fun (k, _) => ((k.drop 11).take 1).toString

def sortCl : String → Option Cl
  | "a" => some .sortA | "c" => some .sortC | "d" => some .sortD | "e" => some .sortE | "f" => some .sortF
  | _ => none

/-- The clauses whose disabling alone makes `Pre` hold (exactly). -/
def soleClauses (x : ECx) (more : List Term.Arg) (c : Call) : List Cl :=
  (preClauses x.repaired).filter fun cl => runEM (preM { x with dis := [cl] } more c) == (true, false)

def childDetail (x : ECx) (more : List Term.Arg) (c : Call) : List String :=
  (children x.p more c).filterMap fun (n, c', more') =>
    if shieldedStep c n c' then none
    else if (runEM (preM x more' c')).1 then none
    else some s!"{n} [{", ".intercalate ((soleClauses x more' c').map Cl.name)}] {callShort c'}"

/-! ## Mutation operators -/

/-- The slots of a call, with whether `Pre` asks `LiveSlot` of a non-marker there, and the rebuild. -/
def slotPos (x : ECx) (c : Call) : List (String × Slot × Bool × (Slot → Option Call)) :=
  match c with
  | .eval k ls ρ t =>
    let (_, vis) := termCB x.p x.ann (profileOf ls) [] t
    (ρ.zipIdx.take 16).map fun (s, i) => (s!"ρ[{i}]", s, vis.contains i && !shieldedB i ρ t,
      fun s' => some (.eval k ls (ρ.set i s') t))
  | .apply k f s =>
    let read := match f with
      | .clo b _ _ _ ls => !b.rel.irrAt ls
      | .pap h ls args => !headIgnoresB x.ann h ls args.length
      | _ => false
    [("f", .val f, true, fun s' => match s' with | .val v => some (.apply k v s) | _ => none),
     ("s", s, read, fun s' => some (.apply k f s'))]
  | .applyAll k f ss =>
    ("f", .val f, true, fun s' => match s' with | .val v => some (.applyAll k v ss) | _ => none) ::
    (ss.zipIdx.take 8).map fun (s, i) => (s!"ss[{i}]", s, false, fun s' => some (.applyAll k f (ss.set i s')))
  | .fire k h ls args =>
    (args.zipIdx.take 16).map fun (s, i) => (s!"arg{i}", s, !headIgnoresB x.ann h ls i,
      fun s' => some (.fire k h ls (args.set i s')))
  | .force k s => [("s", s, false, fun s' => some (.force k s'))]
  | .forceAll k ss => (ss.zipIdx.take 8).map fun (s, i) => (s!"ss[{i}]", s, false, fun s' => some (.forceAll k (ss.set i s')))
  | _ => []

def lamsOver (n : Nat) (body : Term) : Term :=
  (List.range n).foldl (fun t _ => .lam {} (.sort .zero) t) body

/-- A minor whose `i`-th of `n` λs is relevant and returned. -/
def readingMinor (n i : Nat) (ls : Levels) : Value :=
  match lamsOver n (.var (n - 1 - i)) with
  | .lam b d body => .clo b d body [] ls
  | t => .clo {} (.sort .zero) t [] ls

/-- The minors present in `args` of eliminator head `h` over a field written erased: (position, the
first such field, the minor's field count). -/
def erasedMinorPositions (x : ECx) (h : Head) (args : List Slot) : List (Nat × Nat × Nat) :=
  match headConst? h with
  | none => []
  | some c => match elimShape? x.p c with
    | none => []
    | some shape => shape.minors.filterMap fun (pos, _, kidx) =>
      match args[pos]?, ruleCtorFields x.p x.ann shape.recr kidx with
      | some _, some (k, fields) =>
        ((List.range fields.length).find? (fieldWrittenErased x.p k ·)).map fun i => (pos, i, fields.length)
      | _, _ => none

/-- Value mutations: (class, value). -/
def valueOps (ps : PState) (v : Value) : List (String × Value) :=
  let x := ps.ex
  match v with
  | .con c ls pars fs =>
    let base := (if fs.isEmpty then [] else [("dropField", Value.con c ls pars fs.dropLast)]) ++
      [("addField", .con c ls pars (fs ++ [.lit 0])), ("addField", .con c ls pars (fs ++ [.irr none [] ls]))] ++
      ((bumpLs ls).map fun l => [("lsSame", Value.con c l pars fs)]).getD [] ++
      ((flipLs ls).map fun l => [("conLevels", Value.con c l pars fs)]).getD [] ++
      (ps.erasedElims.take 1).map (fun (h, l) => ("whole", Value.con c ls pars (fs.set 0 (.pap h l [])))) ++
      -- aimed at `SortCoherent` (d)/(f): the value at levels where field `i` (a `proof when` field, not
      -- written erased) is dropped, a marker there; F2 then meets a rule λ, E6 a projection, at the run's levels
      ((fs.zipIdx.take 8).filterMap fun (_, i) =>
        match (x.ann.ctorRel? c).bind (·.fields[i]?) with
        | some (.proof (.allZero zs)) =>
          if zs.isEmpty || fieldWrittenErased x.p c i then none
          else some ("sortField", Value.con c (zeroAt zs ls) pars (fs.set i (.irr none [] (zeroAt zs ls))))
        | _ => none)
    let perField := (fs.zipIdx.take 8).flatMap fun (w, i) =>
      if w.isIrr then [("markerLive", Value.con c ls pars (fs.set i (.lit 0)))]
      else if readsFieldB x.p x.ann x.ch c ls i then [("readMarker", Value.con c ls pars (fs.set i (.irr none [] ls)))]
      else [("unreadMarker", Value.con c ls pars (fs.set i (.irr none [] ls)))]
    base ++ perField
  | .clo b d body ρ ls =>
    let (_, vis) := termCB x.p x.ann (profileOf ls) [] (.lam b d body)
    ((bumpLs ls).map fun l => [("lsSame", Value.clo b d body ρ l)]).getD [] ++
    ((flipLs ls).map fun l => [("cloLevels", Value.clo b d body ρ l)]).getD [] ++
    [("cloBody", .clo b d (.sort .zero) ρ ls), ("idClo", .clo {} (.sort .zero) (.var 0) [] ls)] ++
    (ps.unreachedDefn.map fun c' => [("cloRef", Value.clo b d (.const c' []) ρ ls)]).getD [] ++
    (x.ch.reached.take 1).map (fun c => ("cloUnivs", Value.clo b d (.const c (List.replicate (lvlsOf x.p c + 1) .zero)) ρ ls)) ++
    ((vis.eraseDups.take 4).filterMap fun i =>
      match ρ[i]? with
      | some s => if markerB s then some ("markerLive", Value.clo b d body (ρ.set i (.val (.lit 0))) ls)
        else if shieldedB i ρ (.lam b d body) then some ("unreadMarker", Value.clo b d body (ρ.set i (irrM ls)) ls)
        else some ("readMarker", Value.clo b d body (ρ.set i (irrM ls)) ls)
      | none => none)
  | .pap h ls args =>
    let ar := x.p.headArity h
    -- the exponent rule: no mutation that moves arguments of `Nat.pow`/`Nat.shiftLeft` (a case's
    -- argument shifted into the exponent aborts the compiled evaluator, `lean_nat_pow`, above 2^32 - 1)
    let shifts := !(h == .prim .pow || h == .prim .shiftLeft)
    (if args.isEmpty || !shifts then [] else [("papArgs", Value.pap h ls args.dropLast)]) ++
    (if args.length + 1 < ar && shifts then [("papArgs", Value.pap h ls (args ++ [.val (.lit 0)])),
       ("papArgs", Value.pap h ls (args ++ [irrM ls]))] else []) ++
    (if args.length < ar && shifts then [("arity", Value.pap h ls (args ++ List.replicate (ar - args.length) (.val (.lit 0))))]
     else []) ++
    ((bumpLs ls).map fun l => [("lsSame", Value.pap h l args)]).getD [] ++
    ((flipLs ls).map fun l => [("seenBreak", Value.pap h l args)]).getD [] ++
    (erasedMinorPositions x h args).map (fun (pos, i, n) => ("minorRead", Value.pap h ls (args.set pos (.val (readingMinor n i ls))))) ++
    ((args.zipIdx.take 8).filterMap fun (a, j) =>
      if markerB a then some ("markerLive", Value.pap h ls (args.set j (.val (.lit 0))))
      else if headIgnoresB x.ann h ls j then some ("unreadMarker", Value.pap h ls (args.set j (irrM ls)))
      else some ("readMarker", Value.pap h ls (args.set j (irrM ls))))
  | _ => []

/-- Slot mutations at a position (`read`: `Pre` asks `LiveSlot` of a non-marker there). -/
def slotOps (ps : PState) (k : Nat) (ls : Levels) (s : Slot) (read : Bool) : List (String × Slot) :=
  let mk := if markerB s then [("markerLive", Slot.val (.lit 0))]
    else [(if read then "readMarker" else "unreadMarker", irrM ls)]
  let wh := (ps.erasedElims.take 1).map fun (h, l) => ("whole", Slot.val (.pap h l []))
  match s with
  | .val v => mk ++ wh ++ (valueOps ps v).map fun (n, v') => (n, Slot.val v')
  | .name t ρ l =>
    let forced := match force ps.ex.p k s with
      | .ok v => [("nameToVal", Slot.val v)] ++ (valueOps ps v).map fun (n, v') => (n, Slot.val v')
      | _ => []
    mk ++ wh ++ [("nameBody", .name (.sort .zero) ρ l)] ++ forced

def callLs : Call → Option Levels
  | .eval _ ls .. | .evalConst _ ls _ | .headValue _ ls _ | .fire _ _ ls _ => some ls
  | _ => none

def withLs (c : Call) (ls : Levels) : Call :=
  match c with
  | .eval k _ ρ t => .eval k ls ρ t
  | .evalConst k _ c => .evalConst k ls c
  | .headValue k _ h => .headValue k ls h
  | .fire k h _ args => .fire k h ls args
  | c => c

/-- A constructor value of `ind`'s first constructor (literal fields), or a literal for `Nat`. -/
def synthMajor (p : Program) (ind : CId) (np : Nat) (ls : Levels) : Value :=
  if some ind == p.known.nat then .lit 0 else
  match p.decl? ind with
  | some (.induct _ _ _ _ _ (k :: _)) => match p.decl? k with
    | some (.ctor _ _ _ _ _ nf _) => .con k ls (List.replicate np (.val (.lit 0))) (List.replicate nf (.lit 0))
    | _ => .lit 0
  | _ => .lit 0

/-- Swapped heads: `.recr c`, `.quotMk c`, `.cases c` for a reached `c` whose `specialHead?` is another
head; levels of one of `c`'s instances; the arguments resized, and literals with a synthesized major. -/
def swapOps (ps : PState) (c : Call) : List (String × Call) :=
  match c with
  | .fire k h _ args =>
    let x := ps.ex
    let cands := x.ch.reached.flatMap fun r => [Head.recr r, .quotMk r, .cases r].filter fun h' =>
      h' != h && specialHead? x.p r != some h' && x.p.headArity h' > 0
    -- the ones whose declaration is of the head's kind (a table entry hides it) first
    let kindOk : Head → Bool := fun h' => match h', headConst? h' with
      | .recr _, some r => (match x.p.decl? r with | some (.recr ..) => true | _ => false)
      | .quotMk _, some r => x.p.isQuotCtor r
      | _, _ => false
    let ordered := (cands.filter kindOk ++ cands.filter (!kindOk ·)).take 4
    ordered.flatMap fun h' =>
      match headConst? h' with
      | none => []
      | some r =>
        match (x.insts.getD r []).head? with
        | none => []
        | some q =>
          let ls' := levelsOf q
          let ar := x.p.headArity h'
          let resized := (args.take ar) ++ List.replicate (ar - min ar args.length) (.val (.lit 0))
          let lits := (List.range ar).map fun _ => Slot.val (.lit 0)
          let synth : List Slot := match h' with
            | .recr r => match x.p.decl? r with
              | some (.recr _ _ _ np nmot nmin ni ind _ _) =>
                lits.set (np + nmot + nmin + ni) (.val (synthMajor x.p ind np ls'))
              | _ => lits
            | .cases cc => match x.p.table.resolveOf cc with
              | some (.case r') => match x.p.decl? r' with
                | some (.recr _ _ _ np _ _ ni ind _ _) => lits.set (np + 1 + ni) (.val (synthMajor x.p ind np ls'))
                | _ => lits
              | _ => lits
            | _ => lits
          [("swapHead", Call.fire k h' ls' resized), ("swapHead", Call.fire k h' ls' synth)]
  | _ => []

/-- Quot.lift's quotient replaced by a `Quot.mk` value with a marker element, for every quot
constructor declaration writing its element erased (and the value's own). -/
def quotElemOps (ps : PState) (c : Call) : List (String × Call) :=
  match c with
  | .fire k (.quotLift cl) ls args =>
    match args[5]? with
    | some q =>
      match force ps.ex.p k q with
      | .ok (.con c' l' pars [_]) =>
        (ps.quotCtorsErased ++ [c']).eraseDups.map (fun c'' =>
          ("quotElem", Call.fire k (.quotLift cl) ls (args.set 5 (.val (.con c'' l' pars [.irr none [] l']))))) ++
        -- aimed at `SortCoherent` (e): the program's own `Quot.mk` value at levels where its element's class
        -- is irrelevant (an element not written erased), a marker element
        (match ((ps.ex.ann.constRel? c').bind (·.params[2]?) : Option Rel) with
          | some (.proof (.allZero zs)) =>
            if zs.isEmpty then [] else
            [("sortElem", Call.fire k (.quotLift cl) ls (args.set 5 (.val (.con c' (zeroAt zs l') pars [.irr none [] (zeroAt zs l')]))))]
          | _ => [])
      | _ => []
    | none => []
  | _ => []

/-- A marker at a `case` key's minor or at `Quot.lift`'s function, at the levels of another reached
instance where that position is irrelevant. -/
def minorMarkerOps (ps : PState) (c : Call) : List (String × Call) :=
  let x := ps.ex
  match c with
  | .fire k h ls args =>
    let positions : List Nat := match h with
      | .quotLift _ => [3]
      | .cases cc => match x.p.table.resolveOf cc with
        | some (.case r) => match x.p.decl? r with
          | some (.recr _ _ _ np _ nmin ni _ _ _) => (List.range nmin).map (np + 1 + ni + 1 + ·)
          | _ => []
        | _ => []
      | _ => []
    match headConst? h with
    | none => []
    | some cc =>
      ((x.insts.getD cc []).map levelsOf ++ [ls]).flatMap fun ls' =>
        positions.filterMap fun pos =>
          if headIgnoresB x.ann h ls' pos && pos < args.length then
            some ("minorMarker", Call.fire k h ls' (args.set pos (irrM ls')))
          else none
  | _ => []

def callOps (ps : PState) (c : Call) : List (String × Call) :=
  let x := ps.ex
  let lsOps := match callLs c with
    | some ls => ((bumpLs ls).map fun l => [("lsSame", withLs c l)]).getD [] ++
        ((flipLs ls).map fun l => [("seenBreak", withLs c l)]).getD []
    | none => []
  let minorRead := match c with
    | .fire k h ls args => (erasedMinorPositions x h args).map fun (pos, i, n) =>
        ("minorRead", Call.fire k h ls (args.set pos (.val (readingMinor n i ls))))
    | .apply k (.pap h ls args) _ =>
      (erasedMinorPositions x h (args ++ [default])).filterMap fun (pos, i, n) =>
        if pos == args.length then some ("minorRead", Call.apply k (.pap h ls args) (.val (readingMinor n i ls)))
        else none
    | _ => []
  lsOps ++ minorRead ++ swapOps ps c ++ quotElemOps ps c ++ minorMarkerOps ps c

def callK : Call → Nat
  | .eval k .. | .evalConst k .. | .headValue k .. | .apply k .. | .applyAll k .. | .fire k .. | .force k _
  | .forceAll k _ => k

def mutants (ps : PState) (c : Call) : List (String × Call) :=
  let ls := (callLs c).getD []
  let k := callK c
  let fromSlots := (slotPos ps.ex c).flatMap fun (_, s, read, rebuild) =>
    (slotOps ps k ls s read).filterMap fun (n, s') => (rebuild s').map (n, ·)
  callOps ps c ++ fromSlots

/-! ## The pass at one call -/

def PState.recordFinding (ps : PState) (kind : String) (cls : String) (cs : String) (more : List Term.Arg)
    (c : Call) (o : Outcome) : IO Unit := do
  if ps.shapeOk then ps.agg.findings.modify (· + 1)
  let tag := if ps.shapeOk then "FINDING" else "EXCUSED (ShapeOk.ctorUnique false)"
  IO.println s!"{tag}\t{kind}\t{cls}\t{cs}\t{ps.label}"
  IO.println s!"  state: {callShort c}"
  IO.println s!"  {o.render}"
  for d in childDetail ps.ex more c do IO.println s!"  child: {d}"

/-- The exponent rule (RO's filter for the cases, applied to mutants): a mutant that saturates
`Nat.pow` or `Nat.shiftLeft` with an exponent above 2^32 - 1 is not run (compiled `Nat.pow`,
`lean_nat_pow`, aborts the process there; SrcEval's meaning is total). -/
def bigExp : Call → Bool
  | .apply _ (.pap (.prim op) _ args) s => expArg op (args ++ [s])
  | .fire _ (.prim op) _ args => expArg op args
  | _ => false
where expArg (op : PrimOp) (args : List Slot) : Bool :=
  (op == .pow || op == .shiftLeft) && match (args[1]? : Option Slot) with
    | some (.val (.lit n)) => decide (n > 4294967295)
    | _ => false

def PState.checkMutant (ps : PState) (cls cs : String) (more : List Term.Arg) (m : Call) : IO Unit := do
  let g := ps.agg
  if bigExp m then
    bumpArr g.cls s!"(exponent rule: not run)\t{cs}" iGen
    return
  let key := s!"{cls}\t{cs}"
  bumpArr g.cls key iGen
  let x := ps.ex
  let (ok, cutp) := runEM (preM x more m)
  if ok && !cutp then
    bumpArr g.cls key iAcc
    let o := outcomes x more m
    if !o.post then bumpArr g.cls key iPost
    if !o.steps.isEmpty then bumpArr g.cls key iStep
    if !o.reads then bumpArr g.cls key iReads
    if o.fails then
      let sv ← sortRun ps more m
      if sv.isEmpty then
        bumpArr g.cls key iFind
        ps.recordFinding "Pre-accepted mutant" cls cs more m o
      else
        bumpArr g.cls key iSortX
        match sv.eraseDups with
        | [one] => match sortCl one with
          | some cl =>
            bumpArr g.table s!"{cl.name}\t{cs}" 0 3
            bumpArr g.table s!"{cl.name}\t{cs}" 1 3
            g.example s!"{cl.name}\t{cs}" s!"[{cls}] {ps.label}: {callShort m} :: {o.render}"
          | none => pure ()
        | _ => pure ()
  else if ok then bumpArr g.cls key iCut
  else
    let sole := soleClauses x more m
    for cl in sole do
      g.sole.modify fun mp => let k := s!"{ps.label}\t{cls}\t{cs}\t{cl.name}"; mp.insert k (mp.getD k 0 + 1)
    if !sole.isEmpty then
      -- exercised: the invariant without the clause (Pre, Post and the children's Pre alike) is not
      -- preserved at this mutant, SortAgree holding
      for cl in sole do
        bumpArr g.table s!"{cl.name}\t{cs}" 0 3
        let o := outcomes { x with dis := [cl] } more m
        if o.fails then
          let sv ← sortRun ps more m
          if sv.isEmpty then
            bumpArr g.table s!"{cl.name}\t{cs}" 1 3
            g.example s!"{cl.name}\t{cs}" s!"[{cls}] {ps.label}: {callShort m} :: {o.render}"
          else bumpArr g.table s!"{cl.name}\t{cs}" 2 3

/-- Real-call counters: checked, Pre holds, Pre undecided, Pre fails, Post fails, child Pre fails,
Reads fails, counterexamples. -/
def PState.checkReal (ps : PState) (cs : String) (more : List Term.Arg) (c : Call) : IO Unit := do
  let g := ps.agg
  bumpArr g.real cs 0
  let x := ps.ex
  let (ok, cutp) := runEM (preM x more c)
  if !ok then
    bumpArr g.real cs 3
    let sole := soleClauses x more c
    let leaf := if sole.isEmpty then "several" else ", ".intercalate (sole.map Cl.name)
    g.realRej.modify fun m => m.insert s!"{cs}\t{leaf}" (m.getD s!"{cs}\t{leaf}" 0 + 1)
    g.example s!"REAL {cs}\t{leaf}" s!"{ps.label}: {callShort c}" 2
  else if cutp then bumpArr g.real cs 2
  else
    bumpArr g.real cs 1
    let o := outcomes x more c
    if !o.post then bumpArr g.real cs 4
    if !o.steps.isEmpty then bumpArr g.real cs 5
    if !o.reads then bumpArr g.real cs 6
    if o.fails then
      let sv ← sortRun ps more c
      if sv.isEmpty then
        bumpArr g.real cs 7
        ps.recordFinding "real call" "-" cs more c o

def isPow2 (n : Nat) : Bool := n > 0 && (n &&& (n - 1)) == 0

/-- `xs` rotated left by `n`. -/
def rotate {α : Type} (xs : List α) (n : Nat) : List α :=
  if xs.isEmpty then xs else let k := n % xs.length; xs.drop k ++ xs.take k

def PState.visit (ps : PState) (c : Call) (more : List Term.Arg) : IO Unit := do
  if ← ps.stopped.get then return
  if (← ps.checks.get) ≥ ps.cfg.maxChecks then
    ps.stopped.set true
    IO.println s!"PASS {ps.label}: check budget {ps.cfg.maxChecks} reached"
    return
  let cs := caseOf ps.ex.p c
  let n := (← ps.visits.get).getD cs 0 + 1
  ps.visits.modify (·.insert cs n)
  if !isPow2 n then return
  let s := (← ps.sampled.get).getD cs 0
  if s ≥ ps.cfg.samples then return
  ps.sampled.modify (·.insert cs (s + 1))
  if ps.cfg.trace then
    IO.println s!"TRACE real {cs}: {callShort c}"
    (← IO.getStdout).flush
  ps.checks.modify (· + 1)
  ps.checkReal cs more c
  let ms := mutants ps c
  for (cls, m) in rotate ms (if ps.cfg.seed == 0 then 0 else ps.cfg.seed * 2654435761 + n * 40503 + cs.length) do
    let key := s!"{cls}\t{cs}"
    let used := (← ps.perCls.get).getD key 0
    if used < ps.cfg.perClass && (← ps.checks.get) < ps.cfg.maxChecks then
      ps.perCls.modify (·.insert key (used + 1))
      ps.checks.modify (· + 1)
      if ps.cfg.trace then
        IO.println s!"TRACE {cls} {cs}: {callShort m}"
        (← IO.getStdout).flush
      ps.checkMutant cls cs more m

/-- A twin context whose visits run the pass. -/
def passCx (agg : Agg) (cfg : PassCfg) (label : String) (p : Program) (ann : Ann) (ch : Checked) : IO TCx := do
  let base ← newCx p ann ch
  if !ctorUniqueB p then
    IO.println s!"PASS {label}: ShapeOk.ctorUnique is false, a hypothesis of preserve: no pass"
    return base
  let ex := { ECx.make p ann ch cfg.repaired with depth := cfg.depth }
  let erasedElims := ch.reached.filterMap fun c =>
    match elimShape? p c, specialHead? p c, (ex.insts.getD c []).head? with
    | some shape, some h, some q => if erasedMinors p shape then some (h, levelsOf q) else none
    | _, _, _ => none
  let unreachedDefn := (List.range p.size).find? fun c =>
    !ex.reached.contains c && match p.decl? c with
      | some (.defn .defn .safe 0 _ _) => true
      | _ => false
  let quotCtorsErased := (List.range p.size).filter fun c =>
    match p.decl? c with
    | some (.quot .ctor _ ty) => (erasedParams ty).contains 2
    | _ => false
  let checks ← IO.mkRef 0
  let visits ← IO.mkRef {}
  let sampled ← IO.mkRef {}
  let perCls ← IO.mkRef {}
  let stopped ← IO.mkRef false
  let ps : PState := { label := label, cfg := cfg, agg := agg, ex := ex, base := base, checks := checks, visits := visits, sampled := sampled, perCls := perCls, stopped := stopped, erasedElims := erasedElims, unreachedDefn := unreachedDefn, quotCtorsErased := quotCtorsErased, shapeOk := ctorUniqueB p }
  return { base with visit := ps.visit }

/-- `m`'s entries in key order. -/
def sorted {α : Type} (m : Std.HashMap String α) : List (String × α) :=
  m.toList.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- Print the aggregates as tab-separated lines, in key order. -/
def Agg.print (g : Agg) : IO Unit := do
  for (k, a) in sorted (← g.cls.get) do IO.println s!"CLASS\t{k}\t{"\t".intercalate (a.toList.map toString)}"
  for (k, a) in sorted (← g.table.get) do IO.println s!"TABLE\t{k}\t{"\t".intercalate (a.toList.map toString)}"
  for (k, a) in sorted (← g.real.get) do IO.println s!"REAL\t{k}\t{"\t".intercalate (a.toList.map toString)}"
  for (k, n) in sorted (← g.realRej.get) do IO.println s!"REALREJ\t{k}\t{n}"
  for (k, a) in sorted (← g.examples.get) do
    for e in a do IO.println s!"EXAMPLE\t{k}\t{(e.take 900).toString}"
  IO.println s!"FINDINGS {← g.findings.get}"

end IxCCTests.Recheck.P1Twin
