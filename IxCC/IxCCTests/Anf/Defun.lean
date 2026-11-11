import IxCCTests.Anf.Support
import IxCCTests.Support.LamGen
import IxCC.Anf.Pipeline
import IxCC.Anf.Defun
import IxCC.Fir.Lower
import IxCC.Rt.Layout

/-! P8 (`Anf.defun`, `docs/closures-design.md`): the Anf evaluator before and
after the pass.

* **The value relation, executable** (`rel`): literals and □ equal,
  constructors pointwise, a source closure against the cell of its key, whose
  global is the translation of the closure's code (re-derived here from the
  source code: its captures, its renamed body) and whose fields are the
  captured values and the arguments supplied so far; a function global's
  closure against the field-less cell of its key; and, for a root applied to
  fewer arguments than it takes (Anf's `run` builds the root's closure itself),
  two closures with the same arity and related arguments. On first-order
  values it is equality.
* **Agreement** (`compareRoot`) at several clocks, on every root applied to
  its arity and to one argument less: a source value has a related target
  value at a larger clock (the target charges the dispatcher's call as well);
  a source timeout at a clock is a target timeout at the same clock (the
  timeout clause); a source trap a target trap; a stuck source imposes
  nothing.
* **The output**: `Anf.FirstOrder`, `WellScoped` (when the input is),
  `Fir.lower` accepts it, the middle end's size check passes.
* **Hand-written programs** covering every row of the translation table and
  every application case (exact, partial, over-applied through one and
  several closures, through a stored closure, `app f []`, a literal, a
  constructor and □ applied), captures (none, several, out of order, from
  `case` fields and join parameters, nested λs), by-name thunks and erased
  arguments, recursion through closures; the declines (cell fields, tag
  space) at and past their limits; the input checks; and the over-applied
  root that no first-order translation can match (`docs/closures-design.md`;
  the target is stuck where the source is not).
* **Generated programs** (`LamGen`): after P1, after a shrink, and after the
  whole Phase 1 middle end. -/

namespace IxCCTests.Anf.Defun

open IxCC IxCCTests.Src IxCCTests.Lam IxCCTests.Anf
open IxCC.Anf (Exp Bind Atom Alt GDef Val JClo GlobalId)
open IxCC.Sem (Result)

abbrev Program := IxCC.Anf.Program

/-! ## The value relation, executable -/

/-- The number of local functions in an expression, nested ones included. -/
partial def fnCount : Exp → Nat
  | .bind _ b e =>
    (match b with
     | .fn _ fb => 1 + fnCount fb
     | _ => 0) + fnCount e
  | .join _ _ b e => fnCount b + fnCount e
  | .case _ alts d => (alts.map (fnCount ·.body)).foldl (· + ·) 0 + (d.map fnCount).getD 0
  | .tick e => fnCount e
  | .jump .. | .ret _ | .trap => 0

/-- The global of `q` keyed `k`. -/
def globalOfKey (q : Program) (k : Key.GKey) : Option (GlobalId × GDef) :=
  q.globalList.find? (fun (_, gd) => decide (gd.key = k))

/-- The captures (fields at `j = 0`) of key `k`'s closures, from `q`'s table. -/
def capsOf (q : Program) (k : Key.GKey) : Option Nat := (q.ctor? (.clo k 0)).map (·.arity)

mutual

/-- Source value `v` against target value `w` (see the module note). -/
partial def rel (p q : Program) : Val → Val → Bool
  | .lit a, .lit b => a == b
  | .box, .box => true
  | .con c vs, .con c' ws => decide (c = c') && rels p q vs ws
  | .clos ρ n b got, .con (.clo k j) ws =>
    j == got.length && j < n &&
    match capsOf q k, globalOfKey q k with
    | some caps, some (_, gd) =>
      ws.length == caps + j && gd.ps.length == caps + n && rels p q got (ws.drop caps) &&
      match k with
      | .lam gk [i] =>
        -- re-derive the lifted global from the closure's code: the λ's
        -- nested functions were numbered just before it
        let start := i - fnCount b
        match Anf.Defun.exp { prog := p, g := 0, key := gk } (ρ.length + n) { next := start } b with
        | .ok (b', acc) =>
          let capsL := Anf.Defun.captures ρ.length (b'.free n)
          acc.next == i && capsL.length == caps &&
            gd.body.beq (Anf.Defun.Exp.renameVars (Anf.Defun.capRen capsL n) 0 b') &&
            rels p q (capsL.map fun x => ρ.getD x .box) (ws.take caps)
        | .error _ => false
      | _ =>
        -- a function global's closure: no environment, no captures
        ρ.isEmpty && caps == 0 &&
          (p.globalList.any fun (_, hd) => decide (hd.key = k) && hd.ps.length == n && hd.body.beq b)
    | _, _ => false
  | .clos _ n _ got, .clos _ n' _ got' => n == n' && rels p q got got'
  | _, _ => false

partial def rels (p q : Program) : List Val → List Val → Bool
  | [], [] => true
  | v :: vs, w :: ws => rel p q v w && rels p q vs ws
  | _, _ => false

end

/-- A value with no closure in it. -/
partial def firstOrderVal : Val → Bool
  | .clos .. => false
  | .con (.clo ..) _ => false
  | .con _ fs => fs.all firstOrderVal
  | _ => true

/-- Structural equality of first-order values. -/
partial def valEq : Val → Val → Bool
  | .lit a, .lit b => a == b
  | .box, .box => true
  | .con c vs, .con c' ws => decide (c = c') && vs.length == ws.length && (vs.zip ws).all fun (v, w) => valEq v w
  | _, _ => false

/-! ## Agreement -/

structure Tally where
  runs : Nat := 0
  ok : Nat := 0
  closures : Nat := 0
  timeout : Nat := 0
  trap : Nat := 0
  stuck : Nat := 0
  /-- The largest ratio of the target's least clock to the source's, in percent. -/
  maxRatio : Nat := 100
  deriving Inhabited

def Tally.render (t : Tally) : String :=
  s!"{t.runs} runs: ok {t.ok} ({t.closures} with closures in the result), timeout {t.timeout}, " ++
  s!"trap {t.trap}, stuck {t.stuck}; target least clock at most {t.maxRatio}% of the source's"

def Tally.add (t u : Tally) : Tally :=
  { runs := t.runs + u.runs, ok := t.ok + u.ok, closures := t.closures + u.closures
    timeout := t.timeout + u.timeout, trap := t.trap + u.trap, stuck := t.stuck + u.stuck
    maxRatio := max t.maxRatio u.maxRatio }

/-- How much more clock the target may need (two charges per saturated
dispatch, one more per over-application step). -/
def slack : Nat := 8

/-- Compare `p` and `q = defun p` on a root and arguments at `clock`. -/
def compareAt (a : Assert) (p q : Program) (root : GlobalId) (args : List Nat) (clock : Nat)
    (label : String) (t : Tally) : IO Tally := do
  let rp ← runAnf p clock root args
  let t := { t with runs := t.runs + 1 }
  let msg := fun (s : String) => s!"{label} root {root} {args} at {clock}: {s} (source {anfOutcome rp})"
  match rp with
  | .ok v =>
    let some lp ← leastClock (fun k => do return notTimeout (← runAnf p k root args)) clock
      | do expect a false (msg "no source least clock"); return t
    let some lq ← leastClock (fun k => do return notTimeout (← runAnf q k root args)) (slack * clock + 8)
      | do expect a false (msg s!"the target does not finish within {slack}× the clock"); return t
    -- the target never finishes earlier than the source (tick dominance)
    expect a (lq ≥ lp) (msg s!"the target finishes at {lq}, before the source's least clock {lp}")
    match ← runAnf q lq root args with
    | .ok w =>
      expect a (rel p q v w) (msg s!"values not related (source {v.shape}, target {w.shape})")
      if firstOrderVal v then
        expect a (valEq v w) (msg "first-order values differ")
        expect a (IxCC.Anf.readback p v == IxCC.Anf.readback q w) (msg "readback differs")
      let ratio := if lp == 0 then 100 else lq * 100 / lp
      return { t with ok := t.ok + 1, maxRatio := max t.maxRatio ratio
                      closures := t.closures + (if firstOrderVal v then 0 else 1) }
    | r => do expect a false (msg s!"the target gives {anfOutcome r}"); return t
  | .timeout =>
    let rq ← runAnf q clock root args
    expect a (anfOutcome rq == "timeout") (msg s!"timeout clause: the target gives {anfOutcome rq}")
    return { t with timeout := t.timeout + 1 }
  | .trap =>
    let rq ← runAnf q (slack * clock + 8) root args
    expect a (anfOutcome rq == "trap") (msg s!"a source trap is a target {anfOutcome rq}")
    return { t with trap := t.trap + 1 }
  | .stuck => return { t with stuck := t.stuck + 1 }
  | .resource _ => do expect a false (msg "Anf never fails for a resource"); return t

/-- Every root of `p`, applied to its arity and to one argument less, on each
argument value, at each clock. -/
def compareRoots (a : Assert) (p q : Program) (values : List Nat) (clocks : List Nat) (label : String)
    (t : Tally) : IO Tally := do
  let mut t := t
  for r in p.roots do
    let n := (p.arity? r).getD 0
    let sets := ((values.map fun v => List.replicate n v) ++
      (if n > 0 then values.map fun v => List.replicate (n - 1) v else [])).eraseDups
    for args in sets do
      for k in clocks do
        t ← compareAt a p q r args k label t
  return t

/-- The output's checks: first order, well scoped when the input is, accepted
by `Fir.lower` and by the middle end's size check. -/
def checkOutput (a : Assert) (p q : Program) (label : String) : IO Unit := do
  expect a (IxCC.Anf.firstOrder q) s!"{label}: the output is not FirstOrder"
  if IxCC.Anf.wellScoped p then
    expect a (IxCC.Anf.wellScoped q)
      s!"{label}: the output is not WellScoped (first bad global {IxCC.Anf.firstIllScoped q})\n{q.render}"
  match Fir.lower q with
  | .ok _ => expect a true ""
  | .error e => expect a false s!"{label}: Fir.lower refuses the output: {e.render}"
  match IxCC.Anf.Pipeline.checkGlobalNodes q with
  | .ok _ => expect a true ""
  | .error e => expect a false s!"{label}: {e}"

/-- `defun`, then the output checks and agreement. -/
def check (a : Assert) (p : Program) (values : List Nat) (clocks : List Nat) (label : String)
    (t : Tally) : IO Tally := do
  match IxCC.Anf.Defun.run p with
  | .error e => do expect a false s!"{label}: defun refuses: {e}\n{p.render}"; return t
  | .ok q =>
    checkOutput a p q label
    compareRoots a p q values clocks label t

/-! ## Hand-written programs -/

def natZ : Key.CtorKey := .src 1
def natS : Key.CtorKey := .src 2
def bF : Key.CtorKey := .src 3
def bT : Key.CtorKey := .src 4
def pairK : Key.CtorKey := .src 5
def bigK : Key.CtorKey := .src 6

def ctors : List Lam.CtorInfo :=
  [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
   { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
   { key := pairK, tag := 0, arity := 2 }, { key := bigK, tag := 0, arity := 255 }]

def known : Lam.Known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT }

def x (i : Nat) : Atom := .var i
def lit (n : Nat) : Atom := .lit (.nat n)
def b (bd : Bind) (e : Exp) : Exp := .bind IxCC.Anf.freshLet bd e
def fn (n : Nat) (body : Exp) : Bind := .fn (List.replicate n {}) body
def add (u v : Atom) : Bind := .prim .natAdd [u, v]
def mul (u v : Atom) : Bind := .prim .natMul [u, v]

/-- A global keyed by source constant `c`, of arity `n`. -/
def gd (c n : Nat) (body : Exp) : GDef := { key := .const c [], ps := List.replicate n {}, body }

def prog (gs : List GDef) (roots : List GlobalId) : Program :=
  { globals := Src.NatMap.ofList (gs.zipIdx.map fun (g, i) => (i, g)), size := gs.length
    roots, ctors, known }

/-- Named programs, each with the root's argument values. -/
def handWritten : List (String × Program × List Nat) :=
  [ -- fn with one capture, applied exactly
    ("capture one", prog [gd 0 1 (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0))))
        (b (.app (x 0) [lit 5]) (.ret (x 0))))] [0], [0, 3]),
    -- captures out of order and not contiguous: a, c and t, not b
    ("captures out of order", prog [gd 0 3 (b (mul (x 2) (lit 2))       -- t := a * 2
        (b (fn 2 (b (add (x 2) (x 5)) (b (add (x 0) (x 4)) (b (add (x 0) (x 3)) (b (add (x 0) (x 3))
          (.ret (x 0)))))))                                              -- t + a + c + p0 + p1
        (b (.app (x 0) [lit 10, lit 20]) (.ret (x 0)))))] [0], [1, 4]),
    -- nested λs: the inner captures the outer's parameter and the root's
    ("nested", prog [gd 0 1 (b (fn 1 (b (fn 1 (b (add (x 2) (x 1)) (b (add (x 0) (x 1)) (.ret (x 0)))))
          (.ret (x 0))))
        (b (.app (x 0) [lit 1]) (b (.app (x 0) [lit 2]) (.ret (x 0)))))] [0], [0, 7]),
    -- a function global's value, partially applied twice, then saturated
    ("global partial", prog [gd 0 1 (b (.glob 1) (b (.app (x 0) [x 1]) (b (.app (x 0) [lit 1])
          (b (.app (x 0) [lit 2]) (.ret (x 0)))))),
        gd 1 3 (b (add (x 2) (x 1)) (b (add (x 0) (x 1)) (.ret (x 0))))] [0], [0, 5]),
    -- over-application of a global that returns a closure
    ("global over", prog [gd 0 1 (b (.glob 1) (b (.app (x 0) [x 1, lit 3]) (.ret (x 0)))),
        gd 1 1 (b (fn 1 (b (mul (x 1) (x 0)) (.ret (x 0)))) (.ret (x 0)))] [0], [2, 6]),
    -- a closure stored in a constructor, projected, applied past its arity
    ("stored over", prog [gd 0 1 (b (fn 1 (b (fn 1 (b (add (x 1) (x 0)) (b (add (x 0) (x 3)) (.ret (x 0)))))
          (.ret (x 0))))
        (b (.con pairK [x 0, lit 7]) (b (.proj pairK 0 (x 0)) (b (.app (x 0) [lit 1, lit 2])
          (.ret (x 0))))))] [0], [0, 4]),
    -- three closures deep, applied to three arguments at once
    ("over three", prog [gd 0 1 (b (fn 1 (b (fn 1 (b (fn 1 (b (add (x 2) (x 1)) (b (add (x 0) (x 1))
          (b (add (x 0) (x 5)) (.ret (x 0)))))) (.ret (x 0)))) (.ret (x 0))))
        (b (.app (x 0) [lit 1, lit 2, lit 3]) (.ret (x 0))))] [0], [0, 2]),
    -- partial, then over-applied
    ("partial then over", prog [gd 0 1 (b (fn 2 (b (fn 1 (b (add (x 2) (x 1)) (b (add (x 0) (x 1))
          (.ret (x 0))))) (.ret (x 0))))
        (b (.app (x 0) [x 1]) (b (.app (x 0) [lit 2, lit 3]) (.ret (x 0)))))] [0], [0, 9]),
    -- a two-argument closure applied exactly
    ("exact two", prog [gd 0 1 (b (fn 2 (b (mul (x 1) (x 0)) (b (add (x 0) (x 3)) (.ret (x 0)))))
        (b (.app (x 0) [lit 3, lit 4]) (.ret (x 0))))] [0], [0, 1]),
    -- applying to no arguments returns the function
    ("app nothing", prog [gd 0 1 (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0))))
        (b (.app (x 0) []) (b (.app (x 0) [lit 1]) (.ret (x 0)))))] [0], [0, 1]),
    -- a CAF, and a CAF whose value is a closure
    ("cafs", prog [gd 0 1 (b (.glob 1) (b (.glob 2) (b (.app (x 0) [x 1]) (b (add (x 0) (x 3))
          (.ret (x 0)))))),
        gd 1 0 (.ret (lit 7)),
        gd 2 0 (b (fn 1 (b (add (x 0) (lit 1)) (.ret (x 0)))) (.ret (x 0)))] [0], [0, 2]),
    -- a by-name thunk forced by applying it to □
    ("thunk", prog [gd 0 1 (b (fn 1 (b (mul (x 1) (lit 2)) (.ret (x 0))))
        (b (.app (x 0) [.box]) (.ret (x 0))))] [0], [0, 6]),
    -- an erased argument passed through the dispatcher
    ("erased argument", prog [gd 0 1 (b (.glob 1) (b (.app (x 0) [.box, x 1]) (.ret (x 0)))),
        gd 1 2 (.ret (x 0))] [0], [0, 8]),
    -- a λ under a case alternative, capturing the field
    ("case field", prog [gd 0 1 (.case (x 0) [.mk natZ 0 (.ret (lit 0)),
        .mk natS 1 (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0)))) (b (.app (x 0) [lit 10]) (.ret (x 0))))]
        none)] [0], [0, 1, 5]),
    -- a λ in a join body, capturing the join parameter
    ("join parameter", prog [gd 0 1 (.join 1 false
        (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0)))) (b (.app (x 0) [lit 1]) (.ret (x 0))))
        (.jump 0 [x 0]))] [0], [0, 3]),
    -- recursion through a closure argument
    ("recursion", prog [gd 0 1 (b (fn 1 (b (add (x 0) (x 1)) (.ret (x 0)))) (b (.call 1 [x 0, x 1])
          (.ret (x 0)))),
        gd 1 2 (.case (x 0) [.mk natZ 0 (.ret (lit 0)),
          .mk natS 1 (b (.app (x 2) [x 0]) (b (.call 1 [x 3, x 1]) (b (add (x 1) (x 0)) (.ret (x 0)))))]
          none)] [0], [0, 1, 4]),
    -- composeClosure: a closure that grows on every iteration
    ("compose", prog [gd 0 2 (b (fn 1 (b (add (x 0) (lit 1)) (.ret (x 0)))) (b (.call 1 [x 2, x 0, x 1])
          (.ret (x 0)))),
        gd 1 3 (.case (x 2) [.mk natZ 0 (b (.app (x 1) [x 0]) (.ret (x 0))),
          .mk natS 1 (b (fn 1 (b (.app (x 3) [x 0]) (b (.app (x 4) [x 0]) (.ret (x 0)))))
            (b (.call 1 [x 1, x 0, x 4]) (.ret (x 0))))] none)] [0], [0, 1, 3]),
    -- a closure built in one global, applied in another (a dispatcher shared)
    ("cross global", prog [gd 0 1 (b (.call 1 [x 0]) (b (.call 2 [x 0, x 1]) (.ret (x 0)))),
        gd 1 1 (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0)))) (.ret (x 0))),
        gd 2 2 (b (.app (x 1) [x 0]) (.ret (x 0)))] [0], [0, 3]),
    -- applying a literal, □ and a constructor is stuck
    ("stuck heads", prog [gd 0 1 (b (.app (lit 3) [lit 1]) (.ret (x 0))),
        gd 1 1 (b (.app .box [lit 1]) (.ret (x 0))),
        gd 2 1 (b (.con pairK [lit 1, lit 2]) (b (.app (x 0) [lit 1]) (.ret (x 0)))),
        gd 3 1 (b (fn 1 (.ret (x 0))) (.ret (x 0)))] [0, 1, 2, 3], [0, 1]),
    -- a trap and a diverging application
    ("trap and loop", prog [gd 0 1 (b (fn 1 .trap) (b (.app (x 0) [lit 1]) (.ret (x 0)))),
        gd 1 1 (b (.glob 1) (b (.app (x 0) [x 1]) (.ret (x 0))))] [0, 1], [0]),
    -- a root returning a closure (applied to its arity: related values)
    ("closure root", prog [gd 0 1 (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0)))) (.ret (x 0))),
        gd 1 2 (b (fn 1 (b (add (x 2) (x 0)) (.ret (x 0)))) (.ret (x 0)))] [0, 1], [0, 2]) ]

/-- A global of `n` parameters whose λ captures all of them and takes `m`. -/
def wideCapture (n m : Nat) : Program :=
  let fields := (List.range 255).map fun i => if i < n then x (m + n - 1 - i) else lit 0
  prog [gd 0 n (b (.fn (List.replicate m {}) (b (.con bigK fields) (.ret (x 0)))) (.ret (x 0)))] [0]

/-- `count` escaping globals of `arity` parameters each. -/
def manyKeys (count arity : Nat) : Program :=
  let root := (List.range count).foldr (fun i e => b (.glob (i + 1)) e) (.ret (lit 0))
  prog (gd 0 0 root :: (List.range count).map fun i => gd (i + 1) arity (.ret (x 0))) [0]

def expectDecline (a : Assert) (p : Program) (code label : String) : IO Unit := do
  match IxCC.Anf.defun p with
  | .ok _ => expect a false s!"{label}: accepted, expected {code}"
  | .error e => expect a (e.startsWith code) s!"{label}: refused with {e}, expected {code}"

/-- Accepted, first order, with `keys` closure keys in the table (the full
output checks are quadratic in a table this large). -/
def expectAccept (a : Assert) (p : Program) (keys : Nat) (label : String) : IO Unit := do
  match IxCC.Anf.defun p with
  | .ok q =>
    expect a (IxCC.Anf.firstOrder q) s!"{label}: the output is not FirstOrder"
    expectEq a (q.ctors.length - p.ctors.length) keys s!"{label}: closure keys"
  | .error e => expect a false s!"{label}: refused: {e}"

/-- The declines and input checks. -/
def declines (a : Assert) : IO (Array String) := do
  expect a (IxCC.Anf.Defun.maxCellFields == Rt.maxFields) "maxCellFields is Rt.maxFields"
  expect a (IxCC.Anf.Defun.maxClosureKeys == Rt.maxTag + 1) "maxClosureKeys is Rt.maxTag + 1"
  -- cell fields: the captures and the arguments supplied, at most 254
  expectAccept a (wideCapture 254 1) 1 "254 captures, one parameter"
  expectDecline a (wideCapture 255 1) "defun.captures" "255 captures"
  expectDecline a (wideCapture 254 2) "defun.captures" "254 captures, two parameters"
  -- tags: one per closure key, at most 0x7F00
  expectAccept a (manyKeys 127 254) 32258 "32,258 closure keys"
  expectDecline a (manyKeys 129 254) "defun.tags" "32,766 closure keys"
  -- input checks
  expectDecline a (prog [gd 0 1 (b (.fn [] (.ret (lit 0))) (.ret (x 0)))] [0]) "defun.input"
    "a local function without parameters"
  expectDecline a (prog [gd 0 1 (b (fn 1 (.ret (x 3))) (.ret (x 0)))] [0]) "defun.input"
    "a capture out of scope"
  expectDecline a (prog [gd 0 1 (b (.glob 7) (.ret (x 0)))] [0]) "defun.input" "glob beyond the size"
  expectDecline a (prog [{ gd 0 1 (.ret (x 0)) with key := .dispatch 1 }] [0]) "defun.input"
    "a global keyed as a dispatcher"
  expectDecline a { prog [gd 0 1 (.ret (x 0))] [0] with
      ctors := ctors ++ [{ key := .clo (.const 0 []) 0, tag := 0, arity := 0 }] } "defun.input"
    "a closure key in the table"
  expectDecline a { prog [gd 0 1 (.ret (x 0))] [0] with
      known := { known with natZero := some (.clo (.const 0 []) 0) } } "defun.input"
    "a pinned constructor keyed as a closure"
  expectDecline a (prog [gd 0 1 (b (.glob 1) (b (.glob 2) (.ret (x 0)))), gd 5 1 (.ret (x 0)),
      gd 5 1 (.ret (x 0))] [0]) "defun.input" "two escaping globals with one key"
  return #["the declines at and past their limits, and the input checks"]

/-- The over-applied root that no first-order translation matches: the
source applies the closure the root returns, the target's `applyN` of the cell
is stuck. -/
def overAppliedRoot (a : Assert) : IO (Array String) := do
  let p := prog [gd 0 1 (b (fn 1 (b (add (x 1) (x 0)) (.ret (x 0)))) (.ret (x 0)))] [0]
  let q ← IO.ofExcept (IxCC.Anf.defun p)
  let rp ← runAnf p 10 0 [3, 5]
  let rq ← runAnf q 100 0 [3, 5]
  expect a (anfOutcome rp == "ok lit 8") s!"over-applied root, source: {anfOutcome rp}"
  expect a (anfOutcome rq == "stuck") s!"over-applied root, target: {anfOutcome rq}"
  return #["an over-applied root returning a closure: source 8, target stuck (the refinement holds \
    for inputs within the root's arity only)"]

def handWrittenRun (a : Assert) : IO (Array String) := do
  let mut t : Tally := {}
  for (label, p, values) in handWritten do
    -- `app f []` is not well scoped (P1 never makes it); P8 still maps it to `f`
    unless label == "app nothing" do
      expect a (IxCC.Anf.wellScoped p) s!"{label}: the hand-written program is not WellScoped\n{p.render}"
    t ← check a p values [3, 10, 200] label t
  return #[s!"{handWritten.length} programs: {t.render}"]

/-! ## Generated programs -/

def gclocks : List Nat := [4, 40, 3000]
def gvalues : List Nat := [0, 1, 2, 3, 5]

structure GStats where
  programs : Nat := 0
  rejected : Nat := 0
  withClosures : Nat := 0
  lifted : Nat := 0
  dispatchers : Nat := 0
  keys : Nat := 0
  /-- The largest `Defun.dispatchWork` of an output (the dispatchers' switch work). -/
  maxWork : Nat := 0
  tally : Tally := {}

/-- Closures left in a program: `fn`s, `app`s and function-valued `glob`s. -/
def residual (P : Program) : Bool :=
  let r := IxCC.Anf.Pipeline.residual P
  !(r.fns.isEmpty && r.apps.isEmpty && r.globs.isEmpty)

def generatedOne (a : Assert) (seed : Nat) (s : GStats) : IO GStats := do
  let L := Support.LamGen.ofSeed seed
  unless IxCC.Lam.wellFormed L && IxCC.Lam.modesOk L do return { s with rejected := s.rejected + 1 }
  let P1 ← IO.ofExcept ((IxCC.Anf.convert L).mapError (s!"seed {seed}: " ++ ·))
  let (_, P2, _) ← IO.ofExcept (IxCC.Anf.Shrink.produce {} P1)
  let tr ← IO.ofExcept ((IxCC.Anf.Pipeline.produce {} L).mapError (s!"seed {seed} produce: " ++ ·))
  let final := (tr.stages.getLast?.map (·.2)).getD P1
  let mut s := { s with programs := s.programs + 1 }
  for (stage, P) in [("P1", P1), ("P2", P2), ("pipeline", final)] do
    if residual P then s := { s with withClosures := s.withClosures + 1 }
    match IxCC.Anf.Defun.run P with
    | .ok q =>
      let lifted := q.globalList.filter (fun (_, g) => g.key matches .lam ..) |>.length
      let disps := q.globalList.filter (fun (_, g) => g.key matches .dispatch _) |>.length
      s := { s with lifted := s.lifted + lifted, dispatchers := s.dispatchers + disps
                    keys := s.keys + (q.ctors.length - P.ctors.length)
                    maxWork := max s.maxWork (IxCC.Anf.Defun.dispatchWork P disps (q.ctors.length - P.ctors.length)) }
      checkOutput a P q s!"seed {seed} {stage}"
      s := { s with tally := ← compareRoots a P q gvalues gclocks s!"seed {seed} {stage}" s.tally }
    | .error e => expect a false s!"seed {seed} {stage}: defun refuses: {e}"
  return s

def generated (a : Assert) (count : Nat) : IO (Array String) := do
  let mut s : GStats := {}
  for seed in [0:count] do
    s ← generatedOne a seed s
  return #[s!"{s.programs} programs ({s.rejected} rejected by WellFormed/ModesOk), 3 stages each, \
    {s.withClosures} with closures; {s.lifted} lifted λs, {s.dispatchers} dispatchers, {s.keys} closure keys; \
    the largest dispatcher switch work {s.maxWork} (cap {IxCC.Anf.maxBackWork})",
    s!"  {s.tally.render}"]

/-- The section of `tests-anf`. -/
def run (a : Assert) (count : Nat := 300) : IO (Array String) := do
  let mut out := #[]
  out := out ++ (← handWrittenRun a)
  out := out ++ (← declines a)
  out := out ++ (← overAppliedRoot a)
  out := out ++ (← generated a count)
  return out

end IxCCTests.Anf.Defun
