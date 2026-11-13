import IxCC.Src.Relevance.Check
import IxCC.Src.Semantics
import Std.Data.HashMap
import Std.Data.HashSet

/-! Executable forms of P1's invariants (`P1/Defs.lean`), exact where the definitions are decidable,
with one switch per leaf clause (`Cl`) so that a mutant can be classified by the clauses it breaks.

* `Frame`, `Live.clo`, `LiveSlot.name`: the profile is `profileOf ls` (the only one `Agree` allows up to
  trailing `true`s, which no `irrP` reads), and the binder classes are the least ones: `.rel` exactly at
  the free variables `TermC`'s walk visits at a relevant position (C1 asks nothing else of them), `.type`
  elsewhere. Every other conjunct of `TermC`/`EnvOk` is monotone in that choice, so the existential
  holds iff it holds at this choice.
* `Live` recursion is depth-bounded; a cut answers `true` and is recorded, so a `true` with no cut and
  every `false` are exact.
* `repaired` adds the repairs (i)-(iv) of the definitions landing (`MarkersPlaced`, `specialHead?` in
  `HeadSeen`). -/

namespace IxCCTests.Recheck.P1Twin

open IxCC IxCC.Src IxCC.Src.Relevance IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical
open IxCC.Sem (Result)

/-- A call of SrcEval's mutual block (`P1.Call`). -/
inductive Call where
  | eval (k : Nat) (ls : Levels) (ρ : Env) (t : Term)
  | evalConst (k : Nat) (ls : Levels) (c : CId)
  | headValue (k : Nat) (ls : Levels) (h : Head)
  | apply (k : Nat) (f : Value) (s : Slot)
  | applyAll (k : Nat) (f : Value) (ss : List Slot)
  | fire (k : Nat) (h : Head) (ls : Levels) (args : List Slot)
  | force (k : Nat) (s : Slot)
  | forceAll (k : Nat) (ss : List Slot)
  deriving Inhabited

/-- The leaf clauses. A clause is "broken alone" by a mutant when disabling it alone makes `Pre` hold. -/
inductive Cl where
  | conRead | conWhole | conCount | conQuot
  | cloTermC | cloRefs | cloUnivs
  | papArgs | papArity | fnLive
  | slotWhole | nameTermC | nameRefs | nameUnivs
  | envSlots
  | frTerm | frRefs | frUnivs
  | fireArity | fireLive
  | fitClo | fitPap
  | minors
  | seenInst | seenWord | seenSpecial
  | ecInst
  | forceSlot
  | sortA | sortC | sortD | sortE | sortF
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

def Cl.name : Cl → String
  | .conRead => "Live.con: a read field Live" | .conWhole => "Live.con: fields Whole"
  | .conCount => "Live.con: MarkersPlaced.count (i)" | .conQuot => "Live.con: MarkersPlaced.quotElem (iv)"
  | .cloTermC => "Live.clo: TermOk.c (TermC)" | .cloRefs => "Live.clo: TermOk.refs" | .cloUnivs => "Live.clo: TermOk.univs"
  | .fnLive => "Pre apply/applyAll: the function Live (a marker)" | .papArgs => "Live.pap: args LiveSlot" | .papArity => "Live.pap: length < arity"
  | .slotWhole => "LiveSlot.val: Whole" | .nameTermC => "LiveSlot.name: TermC" | .nameRefs => "LiveSlot.name: refs"
  | .nameUnivs => "LiveSlot.name: univs"
  | .envSlots => "EnvOk: relevant mentioned unshielded slots LiveSlot"
  | .frTerm => "Frame: TermC ∨ prefix ∨ bare const" | .frRefs => "Frame: RefsHandled" | .frUnivs => "Frame: univsOk"
  | .fireArity => "FireOk.arity" | .fireLive => "FireOk.live"
  | .fitClo => "SlotFits.clo" | .fitPap => "SlotFits.pap: LiveSlot unless ignored marker"
  | .minors => "MinorsIgnore (Live.pap, SlotFits, FireOk)"
  | .seenInst => "HeadSeen: instance" | .seenWord => "HeadSeen: word entry" | .seenSpecial => "HeadSeen: specialHead? (iii)"
  | .ecInst => "Pre evalConst: instance"
  | .forceSlot => "Pre force: LiveSlot ∨ marker"
  | .sortA => "SortCoherent (a) E7" | .sortC => "SortCoherent (c) F5" | .sortD => "SortCoherent (d) F2/F3"
  | .sortE => "SortCoherent (e) F8" | .sortF => "SortCoherent (f) E6"

/-- The clauses of `Pre` (and of the invariants it unfolds to) before the repairs. -/
def preClauses (repaired : Bool) : List Cl :=
  [.conRead, .conWhole, .cloTermC, .cloRefs, .cloUnivs, .papArgs, .papArity, .fnLive, .slotWhole,
   .nameTermC, .nameRefs, .nameUnivs, .envSlots, .frTerm, .frRefs, .frUnivs, .fireArity, .fireLive,
   .fitClo, .fitPap, .minors, .seenInst, .seenWord, .ecInst, .forceSlot] ++
  (if repaired then [.conCount, .conQuot, .seenSpecial] else [])

structure ECx where
  p : Program
  ann : Ann
  ch : Checked
  insts : Std.HashMap CId (List Profile)
  reached : Std.HashSet CId
  repaired : Bool := false
  dis : List Cl := []
  depth : Nat := 12

def ECx.make (p : Program) (ann : Ann) (ch : Checked) (repaired : Bool := false) : ECx :=
  let insts := ch.instances.foldl (fun (m : Std.HashMap CId (List Profile)) (c, q) =>
    m.insert c (q :: (m.getD c []))) {}
  { p, ann, ch, insts, reached := Std.HashSet.ofList ch.reached, repaired }

def ECx.en (x : ECx) (c : Cl) : Bool :=
  !x.dis.contains c && (x.repaired || !(c == .conCount || c == .conQuot || c == .seenSpecial))

/-! ## Decidable pieces -/

def agreeB (ls : Levels) (q : Profile) : Bool :=
  (List.range (max ls.length q.length)).all fun i => q.getD i true == (ls.getD i 0 == 0)

def instAt (x : ECx) (c : CId) (ls : Levels) : Bool :=
  (x.insts.getD c []).any (agreeB ls)

def headConst? : Head → Option CId
  | .ctor c | .quotMk c | .quotLift c | .recr c | .cases c => some c
  | .prim _ | .word .. => none

def headSeenB (x : ECx) (ls : Levels) (h : Head) : Bool :=
  (match headConst? h with
    | some c => (!x.en .seenSpecial || specialHead? x.p c == some h) && (!x.en .seenInst || instAt x c ls)
    | none => true) &&
  (match h with
    | .word w op => !x.en .seenWord || x.ch.reached.any fun c =>
        match x.p.table.resolveOf c with
        | some (.word w' op' _) => w' == w && op' == op
        | _ => false
    | _ => true)

def headIgnoresB (ann : Ann) (h : Head) (ls : Levels) (j : Nat) : Bool :=
  match headConst? h with
  | some c => match ann.constRel? c with
    | some cr => (cr.params[j]?.map (·.irrAt ls)).getD false
    | none => false
  | none => false

def markerB : Slot → Bool
  | .val (.irr ..) => true
  | _ => false

def ignoresNextB (ann : Ann) : Value → Bool
  | .clo b _ _ _ ls => b.rel.irrAt ls
  | .pap h ls args => headIgnoresB ann h ls args.length
  | _ => true

def ignoresSlotB : Slot → Nat → Bool
  | .val (.clo b d body _ ls), i => ((lamRels (.lam b d body))[i]?.map (·.irrAt ls)).getD false
  | .val (.pap ..), _ => false
  | .val _, _ => true
  | .name t _ ls, i => ((lamRels t)[i]?.map (·.irrAt ls)).getD false

def minorsIgnoreB (p : Program) (ann : Ann) (h : Head) (args : List Slot) : Bool :=
  match headConst? h with
  | none => true
  | some c =>
    match elimShape? p c with
    | none => true
    | some shape => shape.minors.all fun (pos, _, kidx) =>
      match args[pos]?, ruleCtorFields p ann shape.recr kidx with
      | some s, some (k, fields) =>
        (List.range fields.length).all fun i => !fieldWrittenErased p k i || ignoresSlotB s i
      | _, _ => true

def shieldedB (x : Nat) (ρ : Env) (t : Term) : Bool :=
  match t.spineL with
  | (.var h, args) =>
    h != x && (List.range args.length).any fun n =>
      (match args[n]? with | some a => a.1 == .var x | none => false) &&
      (match ρ[h]? with | some s => ignoresSlotB s n | none => false) &&
      (List.range args.length).all fun m => m == n || (match args[m]? with
        | some a => !mentionsVar x a.1 | none => true)
  | _ => false

def readsFieldB (p : Program) (ann : Ann) (ch : Checked) (c : CId) (ls : Levels) (i : Nat) : Bool :=
  match p.decl? c with
  | some (.quot .ctor ..) => !((((ann.constRel? c).bind (·.params[2]?)).map (·.irrAt ls)).getD false)
  | _ => ch.keeps c ls i

def wholeB (p : Program) : Value → Bool
  | .pap h _ _ => match headConst? h with
    | some c => match elimShape? p c with
      | some shape => !erasedMinors p shape
      | none => true
    | none => true
  | _ => true

def wholeTermB (p : Program) (t : Term) : Bool :=
  match t.spineL with
  | (.const c _, args) => match elimShape? p c with
    | some shape => !erasedMinors p shape || decide (shape.arity ≤ args.length)
    | none => true
  | _ => true

def lvlsOf (p : Program) (c : CId) : Nat := ((p.decl? c).map Decl.lvls).getD 0

def refsHandledB (x : ECx) (q : Profile) (t : Term) : Bool :=
  (t.relevantRefs q []).all fun (c, q') =>
    decide (x.p.size ≤ c) || (x.insts.getD c []).contains (q'.normalize (lvlsOf x.p c))

/-- `MarkersPlaced` (repairs (i), (iv)). -/
def markersPlacedCountB (p : Program) (c : CId) (fs : List Value) : Bool :=
  match p.decl? c with
  | some (.ctor _ _ _ _ _ nf _) =>
    !((List.range fs.length).any fun i => (fs[i]?.map (·.isIrr)).getD false && fieldWrittenErased p c i) ||
      fs.length == nf
  | _ => true

def markersPlacedQuotB (p : Program) (c : CId) (fs : List Value) : Bool :=
  match fs[0]?, p.decl? c with
  | some v, some (.quot .ctor _ ty) => !v.isIrr || !(erasedParams ty).contains 2
  | _, _ => true

/-- `ShapeOk.ctorUnique`, executable: no two constructor declarations share an inductive and an
index. -/
def ctorUniqueB (p : Program) : Bool :=
  let keys := (List.range p.size).filterMap fun c =>
    match p.decl? c with
    | some (.ctor _ _ ind j _ _ _) => some (ind * 4294967296 + j)
    | _ => none
  let sorted := keys.mergeSort (· ≤ ·)
  (sorted.zip sorted.tail).all fun (a, b) => a != b

/-! ## Tier C at one term (`TermC`, `SpineC`, `HeadC`, `ElimC`, `MinorC`, `ParamsC`, `BetaC`), with
the free variables visited at a relevant position (relative to the term's outer environment). -/

def paramsCB (prof q : Profile) : List Term.Arg → List Rel → Bool
  | (_, _, a) :: args, r :: params => r.irrP q == a.irrP prof && paramsCB prof q args params
  | _, _ => true

def betaCB (prof : Profile) (args : List Term.Arg) (binders : List Rel) : Bool :=
  (args.zip binders).all fun ((_, _, a), r) => r.irrP prof == a.irrP prof

def minorCB (p : Program) (prof qc : Profile) (k : CId) (bs : List Rel) (fields : List FieldClass) : Bool :=
  ((List.range (min bs.length fields.length)).all fun i =>
    match bs[i]?, fields[i]? with
    | some b, some cls => !cls.dropP qc || b.irrP prof
    | _, _ => true) &&
  ((List.range fields.length).all fun i => decide (i < bs.length) || !fieldWrittenErased p k i)

def elimCB (p : Program) (ann : Ann) (prof : Profile) (c : CId) (us : List IxCC.Ixon.Univ)
    (args : List Term.Arg) : Bool :=
  match elimShape? p c with
  | none => true
  | some shape =>
    (decide (shape.arity ≤ args.length) || !erasedMinors p shape) &&
    (decide (args.length < shape.arity) ||
      ((match args[shape.major]? with
        | some a => !a.2.2.irrP prof || (((p.table.recKindOf shape.recr).map
            (fun k => RecKind.atProfile (prof.inst us) k)).getD .ordinary).allowsIrrMajor
        | none => true) &&
       shape.minors.all fun (pos, _, rule) =>
         match args[pos]?, ruleCtorFields p ann shape.recr rule with
         | some (minor, _, a), some (k, fields) =>
           a.irrP prof || minorCB p prof (ctorProfile p shape.recr (prof.inst us)) k (lamRels minor) fields
         | _, _ => true))

def headCB (p : Program) (ann : Ann) (prof : Profile) : Term → List Term.Arg → Bool
  | .const c us, args =>
    (match ann.constRel? c with
      | some rel => paramsCB prof (prof.inst us) args rel.params
      | none => true) && elimCB p ann prof c us args
  | .lam b d t, args => betaCB prof args (lamRels (.lam b d t))
  | _, _ => true

/-- C5 at a constant. -/
def c5B (ann : Ann) (prof : Profile) (c : CId) (us : List IxCC.Ixon.Univ) : Bool :=
  match ann.constRel? c with
  | some rel => !rel.result.irrP (prof.inst us)
  | none => true

mutual
/-- `TermC p ann prof (inner ++ outer) t`: `(holds, free variables visited)`; `inner` are the classes
bound inside the walked term so far (innermost first). -/
partial def termCB (p : Program) (ann : Ann) (prof : Profile) (inner : List Rel) : Term → Bool × List Nat
  | .var i =>
    if i < inner.length then (match inner[i]? with | some r => !r.irrP prof | none => true, [])
    else (true, [i - inner.length])
  | .const c us => (c5B ann prof c us && (match elimShape? p c with
      | some shape => !erasedMinors p shape
      | none => true), [])
  | .lam b _ t =>
    let (ok, vs) := termCB p ann prof (b.rel :: inner) t
    ((!(b.contract.uses == .erased) || b.rel.irrP prof) && ok, vs)
  | .letE c r _ v b =>
    let (okv, vsv) := if r.irrP prof then (true, []) else termCB p ann prof inner v
    let (okb, vsb) := termCB p ann prof (r :: inner) b
    ((!(c.binder.uses == .erased) || r.irrP prof) && okv && okb, vsv ++ vsb)
  | .proj s i e =>
    let projOk := match onlyCtor? p s with
      | some k => match ann.ctorRel? k with
        | some rel => match rel.fields[i]? with
          | some cls => !cls.alwaysDropped
          | none => true
        | none => true
      | none => true
    let (ok, vs) := termCB p ann prof inner e
    (projOk && ok, vs)
  | .app f a m r =>
    let t := Term.app f a m r
    let hOk := headCB p ann prof t.spineL.1 t.spineL.2
    let (okf, vsf) := spineCB p ann prof inner f
    let (oka, vsa) := if r.irrP prof then (true, []) else termCB p ann prof inner a
    (hOk && okf && oka, vsf ++ vsa)
  | .natLit _ | .strLit _ => (true, [])
  | .sort _ | .pi .. => (false, [])

partial def spineCB (p : Program) (ann : Ann) (prof : Profile) (inner : List Rel) : Term → Bool × List Nat
  | .app f a _ r =>
    let (okf, vsf) := spineCB p ann prof inner f
    let (oka, vsa) := if r.irrP prof then (true, []) else termCB p ann prof inner a
    (okf && oka, vsf ++ vsa)
  | .const c us => (c5B ann prof c us, [])
  | t => termCB p ann prof inner t
end

/-! ## `Live`, `LiveSlot`, `EnvOk` (exec; `StateM Bool` records a depth cut) -/

abbrev EM := StateM Bool

def cut : EM Bool := do set true; pure true

def allM {α : Type} (xs : List α) (f : α → EM Bool) : EM Bool := do
  for a in xs do
    if !(← f a) then return false
  return true

/-- The least binder classes for `ρ` and `t`'s visited free variables. -/
def leastBs (n : Nat) (visited : List Nat) : List Rel :=
  (List.range n).map fun i => if visited.contains i then .rel else .type

mutual
partial def liveM (x : ECx) (d : Nat) (v : Value) : EM Bool := do
  if d == 0 then return (← cut)
  match v with
  | .lit _ | .str _ => pure true
  | .irr .. => pure false
  | .con c ls _ fs =>
    if x.en .conCount && !markersPlacedCountB x.p c fs then return false
    if x.en .conQuot && !markersPlacedQuotB x.p c fs then return false
    allM (List.range fs.length) fun i => do
      match fs[i]? with
      | some w =>
        if x.en .conWhole && !wholeB x.p w then return false
        if w.isIrr then
          pure (!readsFieldB x.p x.ann x.ch c ls i || !x.en .conRead)
        else liveM x (d - 1) w
      | none => pure true
  | .clo b dm body ρ ls => termLiveM x (d - 1) .cloTermC .cloRefs .cloUnivs ls ρ (.lam b dm body)
  | .pap h ls args =>
    if x.en .papArity && !decide (args.length < x.p.headArity h) then return false
    if !headSeenB x ls h then return false
    if x.en .minors && !minorsIgnoreB x.p x.ann h args then return false
    allM (List.range args.length) fun j => do
      match args[j]? with
      | some s =>
        if headIgnoresB x.ann h ls j && markerB s then pure true
        else liveSlotM x (d - 1) .papArgs s
      | none => pure true

/-- `LiveSlot s`, where the conjunct asking for it is `site` (the leaf a marker slot breaks). -/
partial def liveSlotM (x : ECx) (d : Nat) (site : Cl) : Slot → EM Bool
  | .val v => do
    if v.isIrr then return !x.en site
    if x.en .slotWhole && !wholeB x.p v then return false
    liveM x d v
  | .name t ρ ls => termLiveM x d .nameTermC .nameRefs .nameUnivs ls ρ t

/-- `∃ q bs, Agree ls q ∧ TermOk q bs t ∧ EnvOk ls bs ρ t`. -/
partial def termLiveM (x : ECx) (d : Nat) (cT cR cU : Cl) (ls : Levels) (ρ : Env) (t : Term) : EM Bool := do
  let q := profileOf ls
  let (ok, vis) := termCB x.p x.ann q [] t
  if x.en cT && !ok then return false
  if x.en cR && !refsHandledB x q t then return false
  if x.en cU && !univsOk x.p t then return false
  envM x d ls ρ t vis

partial def envM (x : ECx) (d : Nat) (_ls : Levels) (ρ : Env) (t : Term) (vis : List Nat) : EM Bool :=
  allM vis.eraseDups fun i =>
    match ρ[i]? with
    | some s => if shieldedB i ρ t then pure true else liveSlotM x d .envSlots s
    | none => pure true
end

/-- Run an `EM Bool`: `(answer, cut)`. -/
def runEM (m : EM Bool) : Bool × Bool := m.run false

/-! ## `Pre`, `Post`, `Reads` -/

/-- `Frame` (`more`: the arguments of the enclosing spine past `t`, when `t` is a spine prefix). -/
def frameM (x : ECx) (ls : Levels) (ρ : Env) (t : Term) (more : List Term.Arg) : EM Bool := do
  let q := profileOf ls
  if x.en .frRefs && !refsHandledB x q t then return false
  if x.en .frUnivs && !univsOk x.p t then return false
  let (okT, visT) := termCB x.p x.ann q [] t
  let (okS, visS) := spineCB x.p x.ann q [] t
  let full := Term.mkApps t more
  let okP := !more.isEmpty && okS && headCB x.p x.ann q full.spineL.1 full.spineL.2
  let okB := match t with
    | .const c _ => match elimShape? x.p c with
      | some shape => !erasedMinors x.p shape
      | none => true
    | _ => false
  -- the least classes of the disjunct that holds (the bare constant visits nothing)
  if okT then envM x x.depth ls ρ t visT
  else if okP then envM x x.depth ls ρ t visS
  else if okB then pure true
  else if !x.en .frTerm then envM x x.depth ls ρ t visT
  else pure false

def slotFitsM (x : ECx) : Value → Slot → EM Bool
  | .clo b _ _ _ ls, s => if b.rel.irrAt ls then pure true else liveSlotM x x.depth .fitClo s
  | .pap h ls args, s => do
    if x.en .minors && !minorsIgnoreB x.p x.ann h (args ++ [s]) then return false
    if headIgnoresB x.ann h ls args.length && markerB s then pure true
    else liveSlotM x x.depth .fitPap s
  | _, _ => pure true

partial def allFitM (x : ECx) (k : Nat) (f : Value) : List Slot → EM Bool
  | [] => pure true
  | s :: ss => do
    if !(← slotFitsM x f s) then return false
    match apply x.p k f s with
    | .ok v => allFitM x k v ss
    | _ => pure true

def fireOkM (x : ECx) (h : Head) (ls : Levels) (args : List Slot) : EM Bool := do
  if x.en .fireArity && args.length != x.p.headArity h then return false
  if !headSeenB x ls h then return false
  if x.en .minors && !minorsIgnoreB x.p x.ann h args then return false
  allM (List.range args.length) fun j =>
    match args[j]? with
    | some s => if headIgnoresB x.ann h ls j && markerB s then pure true else liveSlotM x x.depth .fireLive s
    | none => pure true

def forceOkM (x : ECx) (s : Slot) : EM Bool :=
  if markerB s then pure true else liveSlotM x x.depth .forceSlot s

/-- `Pre` (`more` is used at an evaluation only). -/
def preM (x : ECx) (more : List Term.Arg) : Call → EM Bool
  | .eval _ ls ρ t => frameM x ls ρ t more
  | .evalConst _ ls c => pure (decide (x.p.size ≤ c) || !x.en .ecInst || instAt x c ls)
  | .headValue _ ls h => pure (headSeenB x ls h)
  | .apply _ f s => do
    if f.isIrr then return !x.en .fnLive
    if !(← liveM x x.depth f) then return false
    slotFitsM x f s
  | .applyAll k f ss => do
    if f.isIrr then return !x.en .fnLive
    if !(← liveM x x.depth f) then return false
    allFitM x k f ss
  | .fire _ h ls args => fireOkM x h ls args
  | .force _ s => forceOkM x s
  | .forceAll _ ss => allM ss (forceOkM x)

/-- A call's result through SrcEval. -/
inductive Res where
  | one (r : Result Value)
  | many (r : Result (List Value))

def callResult (p : Program) : Call → Res
  | .eval k ls ρ t => .one (eval p k ls ρ t)
  | .evalConst k ls c => .one (evalConst p k ls c)
  | .headValue k ls h => .one (headValue p k ls h)
  | .apply k f s => .one (apply p k f s)
  | .applyAll k f ss => .one (applyAll p k f ss)
  | .fire k h ls args => .one (fire p k h ls args)
  | .force k s => .one (force p k s)
  | .forceAll k ss => .many (forceAll p k ss)

def Res.shape : Res → String
  | .one (.ok v) => v.shape
  | .many (.ok vs) => s!"[{vs.length} values]"
  | .one .stuck | .many .stuck => "stuck"
  | .one .trap | .many .trap => "trap"
  | .one .timeout | .many .timeout => "timeout"
  | _ => "resource"

/-- `Post` on the call's result (`true` where the call does not return). Full checks (no clause
disabled); a `false` is exact. -/
def postM (x : ECx) (c : Call) (r : Res) : EM Bool := do
  -- the clauses `x` disables are left out of `Post` too (the invariant without them)
  match c, r with
  | .eval _ _ _ t, .one (.ok v) => do
    if !(← liveM x x.depth v) then return false
    pure (!wholeTermB x.p t || wholeB x.p v)
  | .evalConst _ _ c, .one (.ok v) => do
    if !(← liveM x x.depth v) then return false
    let pre := match elimShape? x.p c with
      | some shape => !erasedMinors x.p shape
      | none => true
    pure (!pre || wholeB x.p v)
  | .headValue _ _ h, .one (.ok v) => do
    if !(← liveM x x.depth v) then return false
    let pre := match headConst? h with
      | some c => match elimShape? x.p c with
        | some shape => !erasedMinors x.p shape
        | none => true
      | none => true
    pure (!pre || wholeB x.p v)
  | .apply _ f _, .one (.ok v) | .applyAll _ f _, .one (.ok v) => do
    if !(← liveM x x.depth v) then return false
    pure (!wholeB x.p f || wholeB x.p v)
  | .fire .., .one (.ok v) => do
    if !(← liveM x x.depth v) then return false
    pure (wholeB x.p v)
  | .force .., .one (.ok v) => do
    if !v.isIrr && !(← liveM x x.depth v) then return false
    pure (wholeB x.p v)
  | .forceAll .., .many (.ok vs) => allM vs fun v => do
    if !v.isIrr && !(← liveM x x.depth v) then return false
    pure (wholeB x.p v)
  | _, _ => pure true

/-- `Reads` of the call (`true` where it reads nothing or does not get that far). -/
def readsM (x : ECx) : Call → EM Bool
  | .apply k f s => match apply x.p k f s with
    | .ok _ => liveM x x.depth f
    | _ => pure true
  | .eval k ls ρ (.proj s i e) => match eval x.p k ls ρ e with
    | .ok v => match x.p.projectField s i v with
      | .ok w => do pure ((← liveM x x.depth v) && (← liveM x x.depth w))
      | _ => pure true
    | _ => pure true
  | .fire (k + 1) (.recr r) ls args =>
    match x.p.decl? r, ((x.p.table.recKindOf r).map (·.atLevels ls) : Option RecKind) with
    | some (.recr _ _ _ np nmot nmin ni ind _ _), some RecKind.ordinary =>
      match force x.p k (args.getD (np + nmot + nmin + ni) default) with
      | .ok major => if (x.p.selectRule ind np major).isSome then liveM x x.depth major else pure true
      | _ => pure true
    | _, _ => pure true
  | .fire (k + 1) (.cases c) ls args => match x.p.table.resolveOf c with
    | some (.case r) =>
      match x.p.decl? r, ((x.p.table.recKindOf r).map (·.atLevels ls) : Option RecKind) with
      | some (.recr _ _ _ np _ _ ni ind _ _), some RecKind.ordinary =>
        match force x.p k (args.getD (np + 1 + ni) default) with
        | .ok major => if (x.p.selectRule ind np major).isSome then liveM x x.depth major else pure true
        | _ => pure true
      | _, _ => pure true
    | _ => pure true
  | .fire (k + 1) (.quotLift _) _ [_, _, _, _, _, q] => match force x.p k q with
    | .ok (.con c' l' ps [a]) => if x.p.isQuotCtor c' then liveM x x.depth (.con c' l' ps [a]) else pure true
    | _ => pure true
  | _ => pure true

/-! ## One step (`P1.Step`, one case per call site; the premises by SrcEval) -/

/-- `recChosen`/`caseChosen`'s computations, as `fire` makes them. -/
def recChosenR (p : Program) (k : Nat) (ls : Levels) (np nmot nmin ni : Nat) (ind : CId)
    (kind : RecKind) (args : List Slot) : Result (Nat × List Slot) :=
  match kind with
  | .empty => .trap
  | .ordinary =>
    match force p k (args.getD (np + nmot + nmin + ni) default) with
    | .ok major => Result.ofOption (p.selectRule ind np major)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .subsingleton _ srcs =>
    let indices := (args.drop (np + nmot + nmin)).take ni
    .ok (0, srcs.map fun
      | .index i => indices.getD i (Slot.irrNone ls)
      | .proof => Slot.irrNone ls)

def caseChosenR (p : Program) (k : Nat) (ls : Levels) (np ni : Nat) (ind : CId) (kind : RecKind)
    (args : List Slot) : Result (Nat × List Slot) :=
  match kind with
  | .empty => .trap
  | .ordinary =>
    match force p k (args.getD (np + 1 + ni) default) with
    | .ok major => Result.ofOption (p.selectRule ind np major)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .subsingleton _ srcs =>
    .ok (0, srcs.map fun
      | .index i => args.getD (np + 1 + i) (Slot.irrNone ls)
      | .proof => Slot.irrNone ls)

/-- The children of a call, each with its `Step` constructor's name, and for an evaluation the
arguments of the enclosing spine past its term (`appFun` passes the spine's). -/
def children (p : Program) (more : List Term.Arg) : Call → List (String × Call × List Term.Arg)
  | .eval k ls ρ t =>
    match t with
    | .var i => match ρ[i]? with
      | some s => [("var", .force k s, [])]
      | none => []
    | .letE _ r _ v b =>
      if r.irrAt ls then [("letIrr", .eval k ls (.val (.irr (some v) ρ ls) :: ρ) b, [])]
      else [("letVal", .eval k ls ρ v, [])] ++ match eval p k ls ρ v with
        | .ok x => [("letBody", .eval k ls (.val x :: ρ) b, [])]
        | _ => []
    | .proj _ _ e => [("proj", .eval k ls ρ e, [])]
    | .app f a m r => [("appFun", .eval k ls ρ f, (a, m, r) :: more)] ++
      match eval p k ls ρ f with
      | .ok fv =>
        if r.irrAt ls then [("appIrr", .apply k fv (.val (.irr (some a) ρ ls)), [])]
        else match m with
          | .strict => [("appArg", .eval k ls ρ a, [])] ++ match eval p k ls ρ a with
            | .ok x => [("appStrict", .apply k fv (.val x), [])]
            | _ => []
          | .byName => [("appName", .apply k fv (.name a ρ ls), [])]
      | _ => []
    | .const c us => [("const", .evalConst k (us.map (evalUniv ls)) c, [])]
    | _ => []
  | .evalConst k ls c =>
    match p.table.resolveOf c with
    | some (.prim op) => [("prim", .headValue k ls (.prim op), [])]
    | some (.word w op _) => [("word", .headValue k ls (.word w op), [])]
    | some (.csimp g vs _) => match k with
      | k + 1 => [("csimp", .eval k ls [] (.const g vs), [])]
      | 0 => []
    | some (.eqn _ body) => match k with
      | k + 1 => [("eqn", .eval k ls [] body, [])]
      | 0 => []
    | some (.case _) => [("case", .headValue k ls (.cases c), [])]
    | none => match p.decl? c with
      | some (.ctor ..) => [("ctor", .headValue k ls (.ctor c), [])]
      | some (.recr ..) => [("recr", .headValue k ls (.recr c), [])]
      | some (.quot .ctor ..) => [("quotMk", .headValue k ls (.quotMk c), [])]
      | some (.quot .lift ..) => [("quotLift", .headValue k ls (.quotLift c), [])]
      | some (.defn .defn .safe _ _ v) => match k with
        | k + 1 => [("defn", .eval k ls [] v, [])]
        | 0 => []
      | some (.defn .opaq .safe _ _ v) =>
        if p.table.isOpaqueByValue c then match k with
          | k + 1 => [("opaq", .eval k ls [] v, [])]
          | 0 => []
        else []
      | _ => []
  | .headValue k ls h => if p.headArity h == 0 then [("nullary", .fire k h ls [], [])] else []
  | .apply k f s =>
    match f with
    | .clo b _ body ρ ls =>
      if b.propWhen.allowsBeta ls then match k with
        | k + 1 => [("beta", .eval k ls (s :: ρ) body, [])]
        | 0 => []
      else []
    | .pap h ls args =>
      if (args ++ [s]).length == p.headArity h then [("papFire", .fire k h ls (args ++ [s]), [])] else []
    | _ => []
  | .applyAll k f ss =>
    match ss with
    | s :: rest => [("allHead", .apply k f s, [])] ++ match apply p k f s with
      | .ok v => [("allRest", .applyAll k v rest, [])]
      | _ => []
    | [] => []
  | .fire k h ls args =>
    match h with
    | .ctor c => match p.decl? c with
      | some (.ctor _ _ _ _ np _ _) => [("ctorArgs", .forceAll k (args.drop np), [])]
      | _ => []
    | .quotMk _ => match args with
      | [_, _, a] => [("mkArg", .force k a, [])]
      | _ => []
    | .quotLift _ => match k, args with
      | k + 1, [_, _, _, f, _, q] => [("liftQuot", .force k q, [])] ++ match force p k q with
        | .ok (.con c' _ _ [a]) =>
          if p.isQuotCtor c' then [("liftFun", .force k f, [])] ++ match force p k f with
            | .ok fv => [("liftApply", .apply k fv (.val a), [])]
            | _ => []
          else []
        | _ => []
      | _, _ => []
    | .recr r => match k with
      | k + 1 =>
        match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
        | some (.recr _ _ _ np nmot nmin ni ind rules _), some kind =>
          (if kind == .ordinary then [("recMajor", .force k (args.getD (np + nmot + nmin + ni) default), [])]
           else []) ++
          match recChosenR p k ls np nmot nmin ni ind kind args with
          | .ok (j, fields) => match rules[j]? with
            | some rule =>
              let slots := args.take (np + nmot + nmin) ++ fields
              match peelLams slots.length rule.rhs with
              | some body => [("recRule", .eval k ls slots.reverse body, [])]
              | none => []
            | none => []
          | _ => []
        | _, _ => []
      | 0 => []
    | .cases c => match k with
      | k + 1 =>
        match p.table.resolveOf c with
        | some (.case r) =>
          match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
          | some (.recr _ _ _ np _ _ ni ind _ _), some kind =>
            (if kind == .ordinary then [("caseMajor", .force k (args.getD (np + 1 + ni) default), [])]
             else []) ++
            match caseChosenR p k ls np ni ind kind args with
            | .ok (j, fields) =>
              let ms := args.getD (np + 1 + ni + 1 + j) default
              [("caseMinor", .force k ms, [])] ++ match force p k ms with
                | .ok mv => [("caseApply", .applyAll k mv fields, [])]
                | _ => []
            | _ => []
          | _, _ => []
        | _ => []
      | 0 => []
    | .prim _ => [("primArgs", .forceAll k args, [])]
    | .word .. => [("wordArgs", .forceAll k args, [])]
  | .force k s =>
    match s, k with
    | .name t ρ ls, k + 1 => [("forceName", .eval k ls ρ t, [])]
    | _, _ => []
  | .forceAll k ss =>
    match ss with
    | s :: rest => [("allForce", .force k s, [])] ++ match force p k s with
      | .ok _ => [("allForceRest", .forceAll k rest, [])]
      | _ => []
    | [] => []

/-- `pre_step`'s one exception: the evaluation of a variable its spine shields. -/
def shieldedStep (parent : Call) (step : String) (child : Call) : Bool :=
  match parent, step, child with
  | .eval _ _ ρ (.app f (.var x) m r), "appArg", .eval _ _ _ (.var _) => shieldedB x ρ (.app f (.var x) m r)
  | _, _, _ => false

/-- The step case of a call (PA's names). -/
def caseOf (p : Program) : Call → String
  | .eval _ ls _ t => match t with
    | .var _ => "E1 var" | .sort _ | .pi .. => "E2 sort/Π" | .natLit _ | .strLit _ => "E3 lit"
    | .lam .. => "E4 λ" | .letE .. => "E5 let" | .proj .. => "E6 proj"
    | .app _ _ _ r => if r.irrAt ls then "E7 app (irr arg)" else "E7 app"
    | .const .. => "E8 const"
  | .evalConst .. => "E8 δ"
  | .headValue .. => "headValue"
  | .apply _ f _ => match f with
    | .clo .. => "A1 β" | .pap .. => "A2 pap" | _ => "A3 stuck"
  | .applyAll .. => "applyAll"
  | .fire _ h ls _ => match h with
    | .ctor _ => "F1 ctor"
    | .recr r => match ((p.table.recKindOf r).map (·.atLevels ls) : Option RecKind) with
      | some .ordinary => "F2 recr" | some (.subsingleton ..) => "F3 recr subsingleton"
      | some .empty => "F4 recr empty" | none => "F2 recr (no kind)"
    | .cases _ => "F5 cases" | .prim _ => "F6 prim" | .word .. => "F6w word"
    | .quotMk _ => "F7 Quot.mk" | .quotLift _ => "F8 Quot.lift"
  | .force .. => "force"
  | .forceAll .. => "forceAll"

def termShort (t : Term) : String := (((repr t).pretty 100).take 160).toString

mutual
partial def valShort : Nat → Value → String
  | _, .lit n => s!"lit {n}"
  | _, .str _ => "str"
  | 0, v => v.shape
  | d + 1, .con c ls _ fs => s!"con {c}@{ls} [{", ".intercalate (fs.map (valShort d))}]"
  | _, .clo b _ body ρ ls => s!"clo(rel {repr b.rel}, ρ {ρ.length})@{ls} {((termShort body).take 60).toString}"
  | d + 1, .pap h ls args => s!"pap {repr h}@{ls} [{", ".intercalate (args.map (slotShort d))}]"
  | _, .irr .. => "□"
partial def slotShort : Nat → Slot → String
  | d, .val v => valShort d v
  | _, .name t _ ls => s!"name@{ls} {((termShort t).take 60).toString}"
end

def callShort : Call → String
  | .eval k ls ρ t => s!"eval k={k} ls={ls} ρ=[{", ".intercalate (ρ.map (slotShort 2))}] {termShort t}"
  | .evalConst k ls c => s!"evalConst k={k} ls={ls} {c}"
  | .headValue k ls h => s!"headValue k={k} ls={ls} {repr h}"
  | .apply k f s => s!"apply k={k} {valShort 3 f} ← {slotShort 3 s}"
  | .applyAll k f ss => s!"applyAll k={k} {valShort 3 f} ← [{", ".intercalate (ss.map (slotShort 3))}]"
  | .fire k h ls args => s!"fire k={k} {repr h} ls={ls} [{", ".intercalate (args.map (slotShort 3))}]"
  | .force k s => s!"force k={k} {slotShort 3 s}"
  | .forceAll k ss => s!"forceAll k={k} [{", ".intercalate (ss.map (slotShort 3))}]"

end IxCCTests.Recheck.P1Twin
