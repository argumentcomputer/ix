import IxCC.Own.Plain.Semantics

/-! # The ownership checker's suite: an instrumented Own-level interpreter

`Own.Plain.eval` without the clock, counting events: steps, allocations (cells), increments
(calls, and how many found an immediate), decrements (calls, and on immediates), cells freed,
cells live and the peak. The heap operations are the production ones (`Own.Plain.evalRhs`,
`Own.Rc.inc`, `Own.Rc.releaseOne`); a free is a `releaseOne` of a cell at count one. Its results
are compared with the production `Own.Plain.run` (`Main`). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned

open IxCC IxCC.Own.Plain
open IxCC.Own (RVal Heap Env)
open IxCC.Fir (Var FunId)

structure Counts where
  steps : Nat := 0
  allocs : Nat := 0
  incs : Nat := 0
  incImm : Nat := 0
  decs : Nat := 0
  decImm : Nat := 0
  frees : Nat := 0
  live : Nat := 0
  peak : Nat := 0
  calls : Nat := 0
  /-- A function to watch, and how often it was entered. -/
  watch : Nat := 0
  hits : Nat := 0
  /-- A hash of the reference-count operations on cells, in order (`inc`, `dec`, each release
  step of a cascade, each free, with its location). -/
  heapHash : UInt64 := 0
  /-- A hash of every node run, in order (kind and variable). -/
  fullHash : UInt64 := 0
  /-- A hash of the `inc`/`dec` actions that found an immediate, in order. -/
  immHash : UInt64 := 0
  deriving Repr, Inhabited

abbrev M := ExceptT String (StateM Counts)

def mixH (h : UInt64) (a b : Nat) : UInt64 :=
  (h * 1099511628211) ^^^ UInt64.ofNat (a * 1000003 + b + 1)

def event (kind v : Nat) : M Unit :=
  modify fun c => { c with fullHash := mixH c.fullHash kind v }

def heapEvent (kind : Nat) (v : RVal) : M Unit :=
  match v with
  | .loc l => modify fun c => { c with heapHash := mixH c.heapHash kind l }
  | _ => pure ()

def immEvent (kind x : Nat) (v : RVal) : M Unit :=
  match v with
  | .loc _ => pure ()
  | _ => modify fun c => { c with immHash := mixH c.immHash kind x }

instance {α : Type} : Inhabited (M α) := ⟨throw "uninhabited"⟩

def tick (budget : Nat) : M Unit := do
  let c ← get
  if c.steps ≥ budget then throw "step budget exhausted"
  set { c with steps := c.steps + 1 }

partial def dropCounted (H : Heap) : List RVal → M Heap
  | [] => pure H
  | v :: ps => do
    let freed := match v with
      | .loc l => match H.cell? l with | some (.live 1 .dyn _) => true | _ => false
      | _ => false
    match Own.Rc.releaseOne H v ps with
    | none => throw "release refused (an invalid dec)"
    | some (H', ps') =>
      heapEvent (if freed then 3 else 4) v
      if freed then modify fun c => { c with frees := c.frees + 1, live := c.live - 1 }
      dropCounted H' ps'

def actionI (ρ : Env) (H : Heap) : Action → M Heap
  | .inc x n => do
    let some v := ρ.get? x | throw s!"inc of unbound v{x}"
    let isLoc := match v with | .loc _ => true | _ => false
    modify fun c => { c with incs := c.incs + 1, incImm := c.incImm + (if isLoc then 0 else 1) }
    event 10 x
    heapEvent 1 v
    immEvent 1 x v
    match Own.Rc.inc H v n with
    | some H' => pure H'
    | none => throw s!"inc v{x} refused"
  | .dec x => do
    let some v := ρ.get? x | throw s!"dec of unbound v{x}"
    let isLoc := match v with | .loc _ => true | _ => false
    modify fun c => { c with decs := c.decs + 1, decImm := c.decImm + (if isLoc then 0 else 1) }
    event 11 x
    heapEvent 2 v
    immEvent 2 x v
    dropCounted H [v]

mutual
partial def evalI (P : Program) (budget : Nat) (ρ : Env) (J : List JEntry) (H : Heap) :
    Code → M (RVal × Heap)
  | .act a c => do tick budget; evalI P budget ρ J (← actionI ρ H a) c
  | .bind x (.call f args) c => do
    tick budget
    event 12 x
    let some vs := Own.evalArgs ρ args | throw "call arguments"
    let (v, H') ← callI P budget f vs H
    evalI P budget (ρ.insert x v) J H' c
  | .bind x r c => do
    tick budget
    event 12 x
    let before := H.size
    match evalRhs P.tables ρ H r with
    | .ok (v, H') =>
      if H'.size > before then
        heapEvent 5 (.loc before)
        modify fun s => let live := s.live + 1
          { s with allocs := s.allocs + 1, live, peak := max s.peak live }
      evalI P budget (ρ.insert x v) J H' c
    | .trap => throw "trap"
    | _ => throw "rhs stuck"
  | .jp j ps _ rec body c => do
    tick budget
    evalI P budget ρ ({ id := j, charged := false, env := ρ, params := ps, body, isRec := rec } :: J) H c
  | .jmp j args => do
    tick budget
    event 14 j
    let some (e, rest) := lookupJ j J | throw "jump target"
    let some vs := Own.evalArgs ρ args | throw "jump arguments"
    evalI P budget (Own.bindAll e.env e.params vs) (e.after rest) H e.body
  | .case x alts d => do
    tick budget
    event 15 x
    let some v := ρ.get? x | throw "case of unbound"
    let some (key, _) := v.asCtor P.source.known H | throw "case stuck"
    match alts.find? (fun (.mk k _) => k == key) with
    | some (.mk _ b) => evalI P budget ρ J H b
    | none => match d with
      | some b => evalI P budget ρ J H b
      | none => throw "no alternative"
  | .ret a => do
    tick budget
    event 16 0
    let some v := Own.evalArg ρ a | throw "return"
    pure (v, H)
  | .tcall f args => do
    tick budget
    event 17 f
    let some vs := Own.evalArgs ρ args | throw "tail call arguments"
    callI P budget f vs H
  | .trap => throw "trap"

partial def callI (P : Program) (budget : Nat) (f : FunId) (vs : List RVal) (H : Heap) :
    M (RVal × Heap) := do
  modify fun c => { c with calls := c.calls + 1, hits := c.hits + (if f == c.watch then 1 else 0) }
  event 18 f
  match P.source.fun? f, P.bodies.get? f with
  | some fd, some body => evalI P budget (Own.bindAll .leaf (fd.params.map (·.1)) vs) [] H body
  | _, _ => throw s!"call of f{f}"
end

def runI (P : Program) (budget : Nat) (f : FunId) (args : List RVal) (watch : Nat := 0) :
    Except String (RVal × Heap) × Counts :=
  (callI P budget f args {}).run.run { watch }

end IxCCTests.Own.Owned
