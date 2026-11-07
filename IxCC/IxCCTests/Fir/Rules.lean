import IxCCTests.Fir.Support

/-! The rules of Fir, Own and Cfg on hand-written programs (design note 03
§2.1, §3.2, §4.4, §7):

* **charges** (03 C6): function entry, tail calls and recursive jumps; a
  jump into a join point is free, recursive or not; sequenced calls cost
  the depth at Fir and Own and the total at Cfg; a nested join point inside a
  recursive one charges the recursive jump; exact least clocks at each
  level, with a timeout one below;
* **values**: `Nat` peeling in `case` and `proj`, Boolean primitives,
  allocation under both policies (static cells under `.immortal`, dynamic
  ones under `.rc`), field-less constructors as immediates, projection from
  a cell, the default arm; □, a wrong key and a missing alternative are
  stuck at every level (06 S38, 03 C5); `trap`;
* **Anf → Fir** on hand-written Anf with join points (recursive and not), a
  CAF, constructors, projections of literals, literal scrutinees and tail
  calls, compared level by level (`compareRun`);
* **well-formedness**: planted violations of `Fir.WellFormed` and
  `Cfg.WellFormed` are rejected with their reason, and mutants outside the
  immortal fragment are rejected by `Own.checkImmortal`. -/

namespace IxCCTests.Fir.Rules

open IxCC IxCCTests.Src IxCCTests.Anf IxCCTests.Fir
open IxCC.Fir (Code Rhs Arg Alt Rep)
open IxCC.Sem (Result)

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201
def pairK : Key.CtorKey := .src 300

def ctors : List Lam.CtorInfo :=
  [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
   { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
   { key := pairK, tag := 0, arity := 2 }]

def known : Lam.Known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT }

def info (c : Key.CtorKey) : Fir.CtorInfo := (Fir.CtorInfo.ofKey ctors c).getD default

def v (x : Nat) : Arg := .var x
def n (k : Nat) : Arg := .lit (.nat k)

/-- A Fir program from function bodies with their parameter lists. -/
def prog (fs : List (List Nat × Code)) : FProgram :=
  let funs := fs.zipIdx.map fun ((ps, body), i) =>
    (i, ({ key := .const i [], params := ps.map (·, Rep.tobj), body, vars := 64, joins := 8 } : Fir.Fun))
  { funs := Src.NatMap.ofList funs, size := fs.length, exports := List.range fs.length, ctors, known }

/-- Its Own and Cfg levels. -/
def levels (F : FProgram) : OProgram × CProgram :=
  let O := Own.immortal F
  (O, Cfg.lower O)

/-- `f0 x = ret x`; `f1 x = y := call f0 x; ret y`; `f2 x = y := f0 x; z := f0 y;
ret z` (depth 2, total 3); `f3 x = tcall f0 x`; `f4 x = jp j y = ret y in jmp j x`
(free); `f5 n = loop` (a recursive join counting `n` down, `n` charged jumps);
`f6 n` a loop whose recursive jump is inside a nested join point; `f7 n = tcall f7`
down to 0 (a self tail call); `f8`/`f9` allocation; `f10` Booleans; `f11` stuck
and trap cases by argument. -/
def rules : FProgram := prog
  [ ([0], .ret (v 0)),
    ([0], .bind 1 (.call 0 [v 0]) (.ret (v 1))),
    ([0], .bind 1 (.call 0 [v 0]) (.bind 2 (.call 0 [v 1]) (.ret (v 2)))),
    ([0], .tcall 0 [v 0]),
    ([0], .jp 0 [1] false (.ret (v 1)) (.jmp 0 [v 0])),
    ([0], .jp 0 [1, 2] true
        (.case 1 [.mk natZ (.ret (v 2)),
                  .mk natS (.bind 3 (.proj 1 natS 0) (.bind 4 (.prim .natAdd [v 2, n 1])
                    (.jmp 0 [v 3, v 4])))] none)
        (.jmp 0 [v 0, n 0])),
    ([0], .jp 0 [1] true
        (.case 1 [.mk natZ (.ret (n 42)),
                  .mk natS (.bind 2 (.proj 1 natS 0)
                    (.jp 1 [3] false (.jmp 0 [v 3]) (.jmp 1 [v 2])))] none)
        (.jmp 0 [v 0])),
    ([0], .case 0 [.mk natZ (.ret (n 7)),
                   .mk natS (.bind 1 (.proj 0 natS 0) (.tcall 7 [v 1]))] none),
    ([0], .bind 1 (.ctor (info pairK) [v 0, v 0])
        (.bind 2 (.ctor (info pairK) [v 1, n 7]) (.bind 3 (.proj 2 pairK 0)
          (.bind 4 (.proj 3 pairK 1) (.bind 5 (.ctor (info pairK) [v 4, v 2]) (.ret (v 5))))))),
    ([0], .bind 1 (.ctor (info bT) []) (.case 1 [.mk bF (.ret (n 0))] (some (.ret (v 1))))),
    ([0, 1], .bind 2 (.prim .natBle [v 0, v 1])
        (.case 2 [.mk bT (.ret (n 1)), .mk bF (.ret (n 0))] none)),
    ([0], .case 0 [.mk natZ (.bind 1 (.arg .erased) (.case 1 [.mk natZ (.ret (n 0))] none)),
        .mk natS (.bind 2 (.proj 0 natS 0) (.case 2
          [.mk natZ (.bind 3 (.prim .natAdd [.erased, n 1]) (.ret (v 3))),
           .mk natS (.bind 4 (.proj 2 natS 0) (.case 4
             [.mk natZ (.bind 5 (.proj 4 natS 0) (.ret (v 5))),
              .mk natS (.bind 6 (.proj 4 natS 0) (.case 6
                [.mk natZ (.bind 7 (.proj 0 pairK 0) (.ret (v 7))),
                 .mk natS (.bind 8 (.proj 6 natS 0) (.case 8
                   [.mk natZ .trap] none))] none))] none))] none))] none) ]

/-- Least clocks of a run at Fir, Own and Cfg, with timeouts one below. -/
def clocks (a : Assert) (F : FProgram) (f : Nat) (args : List Nat) (label : String)
    (fir cfg : Nat) : IO Unit := do
  let (O, C) := levels F
  let rf ← runFir F fir f args
  expect a (!isTimeout rf) s!"{label}: Fir at {fir} gives {firOutcome rf}"
  if fir > 0 then
    expect a (isTimeout (← runFir F (fir - 1) f args)) s!"{label}: Fir finishes below {fir}"
  let ro ← runOwn .immortal O fir f args
  expect a (sameFirOwn rf ro) s!"{label}: Own at {fir} gives {ownOutcome ro}"
  if fir > 0 then
    expect a (isTimeout (← runOwn .immortal O (fir - 1) f args)) s!"{label}: Own finishes below {fir}"
  let rc ← runCfg .immortal C cfg f args
  expect a (rc == ro) s!"{label}: Cfg at {cfg} gives {ownOutcome rc}"
  if cfg > 0 then
    expect a (isTimeout (← runCfg .immortal C (cfg - 1) f args)) s!"{label}: Cfg finishes below {cfg}"

def outcomeIs (a : Assert) (F : FProgram) (f : Nat) (args : List Nat) (want : String)
    (label : String) : IO Unit := do
  let (O, C) := levels F
  let rf ← runFir F 1000 f args
  expect a (firOutcome rf == want) s!"{label}: Fir {firOutcome rf}, expected {want}"
  for pol in [Own.AllocPol.immortal, .rc] do
    let ro ← runOwn pol O 1000 f args
    expect a (sameFirOwn rf ro) s!"{label}: Own {ownOutcome ro}"
    let rc ← runCfg pol C 100000 f args
    expect a (rc == ro) s!"{label}: Cfg {ownOutcome rc}, Own {ownOutcome ro}"

def natIs (a : Assert) (F : FProgram) (f : Nat) (args : List Nat) (want : Nat) (label : String) :
    IO Unit := do
  outcomeIs a F f args s!"ok lit {want}" label
  match ← runFir F 1000 f args with
  | .ok w => expect a (IxCC.Fir.readback w == some (.nat want)) s!"{label}: readback"
  | _ => pure ()

def semantics (a : Assert) : IO Unit := do
  let F := rules
  match IxCC.Fir.check F with
  | .ok () => expect a true ""
  | .error e => expect a false s!"rules: not WellFormed: {e}"
  let (O, C) := levels F
  match IxCC.Cfg.check C with
  | .ok () => expect a true ""
  | .error e => expect a false s!"rules: Cfg not WellFormed: {e}\n{C.render}"
  expect a (Own.checkImmortal O) "rules: Own outside the fragment"
  -- charges
  clocks a F 0 [5] "entry" 1 1
  clocks a F 1 [5] "call" 2 2
  clocks a F 2 [5] "two sequenced calls (depth 2, total 3)" 2 3
  clocks a F 3 [5] "tail call" 2 2
  clocks a F 4 [5] "a free jump into a join point" 1 1
  for k in [0, 1, 4, 30] do
    clocks a F 5 [k] s!"a recursive join point over {k}" (k + 1) (k + 1)
    clocks a F 6 [k] s!"a recursive jump from a nested join point, {k}" (k + 1) (k + 1)
    clocks a F 7 [k] s!"a self tail call over {k}" (k + 1) (k + 1)
  natIs a F 5 [30] 30 "loop result"
  natIs a F 6 [3] 42 "nested loop result"
  natIs a F 7 [9] 7 "self tail call result"
  expect a (IxCC.Cfg.backEdges C == 3)
    s!"rules: {IxCC.Cfg.backEdges C} back edges, expected 3 (two recursive joins, one self tail call)"
  -- allocation
  for pol in [Own.AllocPol.immortal, .rc] do
    match ← runOwn pol O 10 8 [3] with
    | .ok (w, H) =>
      expect a (H.cells.size == 3) s!"alloc ({reprStr pol}): {H.cells.size} cells, expected 3"
      let mode := if pol == .immortal then Own.OMode.static else .dyn
      expect a (H.cells.all fun | .live 1 m _ => m == mode | _ => false)
        s!"alloc ({reprStr pol}): cells not live 1 {reprStr mode}"
      expect a (H.readback w == some (.ctor 0 [.nat 3, .ctor 0 [.ctor 0 [.nat 3, .nat 3], .nat 7]]))
        s!"alloc ({reprStr pol}): readback {repr (H.readback w)}"
      if pol == .immortal then expect a H.immortalOk "alloc: immortal invariant"
      expect a ((← runCfg pol C 10 8 [3]) == .ok (w, H)) s!"alloc ({reprStr pol}): Cfg heap differs"
    | r => expect a false s!"alloc: Own gives {ownOutcome r}"
  -- a field-less constructor is an immediate: no cell
  match ← runOwn .immortal O 10 9 [0] with
  | .ok (w, H) =>
    expect a (H.cells.size == 0 && w == .ctor0 (info bT)) s!"ctor0: {w.shape}, {H.cells.size} cells"
    expect a (H.readback w == some (.ctor 1 [])) "ctor0 readback"
  | r => expect a false s!"ctor0: {ownOutcome r}"
  outcomeIs a F 9 [0] "ok ctor#1/0" "the default arm"
  natIs a F 10 [2, 3] 1 "natBle true"
  natIs a F 10 [3, 2] 0 "natBle false"
  -- stuck and trap: □ scrutinee, □ primitive, wrong key on a Nat, projection of a Nat
  -- as a pair, a missing alternative, trap
  outcomeIs a F 11 [0] "stuck" "case on □"
  outcomeIs a F 11 [1] "stuck" "a primitive on □"
  outcomeIs a F 11 [2] "stuck" "proj natSucc of 0"
  outcomeIs a F 11 [3] "stuck" "proj pair of 3"
  outcomeIs a F 11 [4] "trap" "trap"
  outcomeIs a F 11 [5] "stuck" "no alternative"

/-! ## Anf → Fir on hand-written Anf -/

open IxCC.Anf (Exp Bind Atom GDef) in
/-- Anf programs the K1 pipeline never produces: a recursive join point
(a loop), a non-recursive join point jumped to from two arms, a CAF, a pair
built and projected, a projection of a literal (stuck in Anf, not in Fir),
a literal scrutinee, a tail call through ticks. -/
def anfProgram : AProgram :=
  let x := fun (i : Nat) => Atom.var i
  let lit := fun (k : Nat) => Atom.lit (.nat k)
  let b := fun (bd : Bind) (e : Exp) => Exp.bind Anf.freshLet bd e
  let loop : Exp :=   -- sum n = loop n 0 with a recursive join point
    .join 2 true
      (.tick (.case (x 1) [.mk natZ 0 (.ret (x 0)),
        .mk natS 1 (b (.prim .natAdd [x 1, x 2]) (.jump 0 [x 1, x 0]))] none))
      (.jump 0 [x 0, lit 0])
  let twoArms : Exp :=   -- f n = join j y = y + 1 in case n (0 ⇒ j 10) (m+1 ⇒ j m)
    .join 1 false (b (.prim .natAdd [x 0, lit 1]) (.ret (x 0)))
      (.case (x 0) [.mk natZ 0 (.jump 0 [lit 10]), .mk natS 1 (.tick (.jump 0 [x 0]))] none)
  let pair : Exp :=   -- g n = let p := (n, 7) in p.1 + p.0
    b (.con pairK [x 0, lit 7]) (b (.proj pairK 1 (x 0)) (b (.proj pairK 0 (x 1))
      (b (.prim .natAdd [x 1, x 0]) (.ret (x 0)))))
  let caf : Exp := b (.prim .natAdd [lit 20, lit 22]) (.ret (x 0))
  let useCaf : Exp := b (.glob 3) (b (.prim .natAdd [x 0, x 1]) (.ret (x 0)))
  let projLit : Exp := b (.proj natS 0 (lit 5)) (.ret (x 0))
  let litCase : Exp := .case (lit 3) [.mk natZ 0 (.ret (lit 0)), .mk natS 1 (.ret (x 0))] none
  let tailTicks : Exp := b (.call 0 [x 0]) (.tick (.tick (.ret (x 0))))
  let gs : List GDef :=
    [{ key := .const 0 [], ps := [{}], body := loop },
     { key := .const 1 [], ps := [{}], body := twoArms },
     { key := .const 2 [], ps := [{}], body := pair },
     { key := .const 3 [], ps := [], body := caf },
     { key := .const 4 [], ps := [{}], body := useCaf },
     { key := .const 5 [], ps := [{}], body := projLit },
     { key := .const 6 [], ps := [{}], body := litCase },
     { key := .const 7 [], ps := [{}], body := tailTicks }]
  { globals := Src.NatMap.ofList (gs.zipIdx.map fun (g, i) => (i, g)), size := gs.length
    roots := List.range gs.length, ctors, known }

def anf (a : Assert) : IO (Array String) := do
  let L ← IO.ofExcept (lower anfProgram)
  checkLevels a L "hand-written Anf"
  let mut t : Tally := {}
  for (g, argss) in [(0, [[0], [1], [5], [40]]), (1, [[0], [1], [6]]), (2, [[3]]), (3, [[]]),
      (4, [[1]]), (5, [[0]]), (6, [[0]]), (7, [[4]])] do
    for xs in argss do
      t ← compareRun a L none g xs 100000 s!"hand-written Anf g{g}" t
  -- the tail call through ticks is a `tcall`; the projection of a literal is
  -- stuck in Anf and 4 in Fir (a target may be less stuck)
  let isTail : Code → Bool
    | .tcall 0 _ => true
    | _ => false
  expect a ((L.fir.fun? 7).any (isTail ·.body)) "a call before ticks and ret is not a tail call"
  expect a ((← runAnf L.anf 10 5 [0]) matches .stuck) "Anf projects a literal"
  natIs a L.fir 5 [0] 4 "Fir projects the literal 5 as succ"
  -- a `let borrow` site names the variable it binds (v2), not the temporary
  -- holding the projected literal (v1)
  let bc := IxCC.Ixon.V3.LetContract.borrow true
  let gd : Anf.GDef :=
    { key := .const 0 [], ps := [{}], body := .bind bc (.proj natS 0 (.lit (.nat 5))) (.ret (.var 0)) }
  let borrowProg : AProgram :=
    { anfProgram with globals := Src.NatMap.ofList [(0, gd)], size := 1, roots := [0] }
  match IxCC.Fir.lower borrowProg with
  | .ok F =>
    let sites := ((F.fun? 0).map (·.letContracts.map (·.1))).getD []
    expect a (sites == [2]) s!"the borrow site is recorded on {sites}, expected [2]"
  | .error e => expect a false s!"borrow program: {e.render}"
  return #[s!"hand-written Anf: {sizes L}", s!"  {t.render}"]

/-! ## Well-formedness and the fragment -/

def rejects (a : Assert) (F : FProgram) (why : String) (label : String) : IO Unit := do
  match IxCC.Fir.check F with
  | .ok () => expect a false s!"{label}: accepted"
  | .error e => expect a ((e.splitOn why).length > 1) s!"{label}: rejected for {e}, expected {why}"

def cfgRejects (a : Assert) (C : CProgram) (why : String) (label : String) : IO Unit := do
  match IxCC.Cfg.check C with
  | .ok () => expect a false s!"{label}: accepted"
  | .error e => expect a ((e.splitOn why).length > 1) s!"{label}: rejected for {e}, expected {why}"

/-- Replace function 0's body. -/
def withBody (F : FProgram) (c : Code) : FProgram :=
  match F.fun? 0 with
  | some fd => { F with funs := F.funs.insert 0 { fd with body := c } }
  | none => F

/-- Replace function `f`'s block list in a Cfg program. -/
def withBlocks (C : CProgram) (f : Nat) (g : List Cfg.Block → List Cfg.Block) : CProgram :=
  match C.fun? f with
  | some fd => { C with funs := C.funs.insert f { fd with blocks := g fd.blocks } }
  | none => C

def mapIdx {α : Type} (i : Nat) (h : α → α) (xs : List α) : List α :=
  xs.zipIdx.map fun (x, j) => if i == j then h x else x

/-- Replace function 0 of an Own program. -/
def withOwnFun (O : OProgram) (h : Own.Fun → Own.Fun) : OProgram :=
  match O.fun? 0 with
  | some fd => { O with funs := O.funs.insert 0 (h fd) }
  | none => O

def wellFormed (a : Assert) : IO (Array String) := do
  let F := rules
  rejects a (withBody F (.ret (v 9))) "out of scope" "an unbound variable"
  rejects a (withBody F (.bind 0 (.arg (n 1)) (.ret (v 0)))) "bound twice" "a parameter rebound"
  rejects a (withBody F (.jmp 3 [])) "out of scope" "a jump to no join point"
  rejects a (withBody F (.jp 0 [1] false (.jmp 0 [v 1]) (.jmp 0 [v 0])))
    "out of scope" "a non-recursive join point jumping to itself"
  rejects a (withBody F (.jp 0 [1] false (.ret (v 1)) (.jmp 0 []))) "arity" "a jump's arity"
  rejects a (withBody F (.bind 1 (.call 1 []) (.ret (v 1)))) "call of f1" "a call's arity"
  rejects a (withBody F (.bind 1 (.ctor { info pairK with tag := 3 } [v 0, v 0]) (.ret (v 1))))
    "ofKey" "a constructor with the wrong tag"
  rejects a (withBody F (.case 0 [.mk natZ .trap, .mk natZ .trap] none)) "repeat" "repeated keys"
  rejects a (withBody F (.bind 1 (.proj 0 pairK 2) (.ret (v 1)))) "index" "a projection index"
  rejects a (withBody F (.bind 1 (.prim .natAdd [v 0]) (.ret (v 1)))) "saturated" "a primitive"
  rejects a { F with funs := F.funs.insert 0 { (F.fun? 0).get! with params := [(0, .word)] } }
    "tobj" "a word parameter"
  rejects a { F with funs := F.funs.insert 1 { (F.fun? 1).get! with key := .const 0 [] } }
    "keys repeat" "repeated function keys"
  rejects a (withBody F (.bind 70 (.arg (n 1)) (.ret (v 70)))) "supply" "a variable past the supply"
  -- Cfg: take the loop functions' blocks and break them
  let (O, C) := levels F
  let loopBlocks := ((C.fun? 5).map (·.blocks)).getD []
  expect a (loopBlocks.length ≥ 3) s!"the loop has {loopBlocks.length} blocks"
  cfgRejects a (withBlocks C 5 (mapIdx 0 fun b => { b with term := .jump { target := 0, args := [] } }))
    "arity" "an edge's arity"
  cfgRejects a (withBlocks C 5 (mapIdx 0 fun b =>
      match b.term with
      | .jump e => { b with term := .jump { e with back := true } }
      | _ => b)) "back edge to a later block" "a forward edge marked back"
  cfgRejects a (withBlocks C 5 (fun bs => bs.map fun b =>
      match b.term with
      | .jump e => if e.back then { b with term := .jump { e with back := false } } else b
      | t => { b with term := t })) "forward edge to an earlier block" "a back edge marked forward"
  cfgRejects a (withBlocks C 5 (mapIdx 0 fun b =>
      { b with body := .bind 9 (.fir (.arg (v 60))) :: b.body })) "used before" "a use before its definition"
  cfgRejects a (withBlocks C 5 (mapIdx 0 fun b =>
      { b with body := .bind 0 (.fir (.arg (n 1))) :: b.body })) "defined twice" "a variable defined twice"
  -- a back edge whose target does not dominate its source: from the last arm to
  -- the other arm's block
  let lastB := loopBlocks.length - 1
  cfgRejects a (withBlocks C 5 (mapIdx lastB fun b =>
      { b with term := .jump { target := lastB - 1, args := [], back := true } }))
    "non-dominator" "a back edge to a non-dominator"
  -- Own: mutants outside the immortal fragment
  let mut mutants := 0
  let pairInfo := info pairK
  for (m, label) in [
      (withOwnFun O fun fd => { fd with regionFrame := true }, "a region frame"),
      (withOwnFun O fun fd => { fd with sig := { fd.sig with result := .unique true } }, "a unique result"),
      (withOwnFun O fun fd => { fd with sig := { fd.sig with params := [{ Own.PSig.plain .tobj with mode := .borrowed true }] } }, "a borrowed parameter"),
      (withOwnFun O fun fd => { fd with sig := { fd.sig with params := [] } }, "a missing signature"),
      (withOwnFun O fun fd => { fd with body := .bind 1 (.alloc pairInfo [v 0, v 0] (.unique true)) (.ret (v 1)) }, "a unique allocation"),
      (withOwnFun O fun fd => { fd with body := .bind 1 (.fir (.ctor pairInfo [v 0, v 0])) (.ret (v 1)) }, "a Fir ctor"),
      (withOwnFun O fun fd => { fd with body := .jp 0 [(1, Own.PSig.plain .tobj)] [(0, 1)] false (.ret (v 1)) (.jmp 0 [v 0]) }, "a nonempty φ"),
      (withOwnFun O fun fd => { fd with body := .jp 0 [(1, { Own.PSig.plain .tobj with kind := .unique false })] [] false (.ret (v 1)) (.jmp 0 [v 0]) }, "a unique join parameter"),
      ({ O with clones := [(0, 1)] }, "a clone")] do
    expect a (!Own.checkImmortal m) s!"Own.checkImmortal accepts {label}"
    mutants := mutants + 1
  -- and the fragment is exactly the embedding's image
  expect a (Own.checkImmortal (Own.immortal (Own.erase O))) "the embedding of an erasure"
  return #[s!"13 Fir and 6 Cfg violations rejected for their reason; {mutants} Own mutants rejected"]

def run (a : Assert) : IO (Array String) := do
  semantics a
  let out ← anf a
  return out ++ (← wellFormed a)

end IxCCTests.Fir.Rules
