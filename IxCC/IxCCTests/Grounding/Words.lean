import IxCCTests.Grounding.GradedHead
import IxCCTests.Grounding.LetWit
import IxCCGrounding.WordRoot

/-! # `tests-grounding`: the word family (step W)

The word family's check `groundCheckW` (`IxCCGrounding.WordRoot`: `groundCheck` with `noWord`
replaced by the decided word conjunct `word`) and the other decided hypotheses of
`rootSound_678AGpW_of_check` (`noCanonAB`, `litDefsB`, `instCheckB`, `headRegimeSB`), on `selEnv` of
the closure with the word entries' runtime references added (the tower's constructors, which no run
term names: `GradedHead.wordClosure`):

* **`grounding/words`** (30 word entries): every one holds, on the closure and at each of its seven
  roots (each root's own closure, its instance check seeded by the root alone); the family over six
  fields refuses it by `noWord` alone (asserted in `GradedHead`'s pass, which also asserts that the
  word family holds exactly where the family over six fields does, and on `grounding/words`).
* **`src-words`** (68 word entries; not one of the 51): every one holds, on the closure and at each
  of its four roots.
* **Planted on `grounding/words`**, at its first binary entry (`UInt64.add`) and that entry's width,
  each refused by the conjunct `word` alone (every other conjunct true; 12): at the tower, `ofFin`'s
  first binder datum made a proposition everywhere (`ifAllZero []`), `Fin`'s projection table
  removed, `LT.lt`'s result made `Sort 1`, `BitVec.toFin`'s projection made field 1, `Fin.mk` taken
  out of the closure; at the bridge, `x % size` in the tower replaced by `5`, `Nat.le.step`'s result
  made `Nat.le #2 #1`; at the entry, its theorem's `Nat.mod` made `Nat.div`, its two sides swapped,
  its head's stored type given no binder (fewer than the operation's arity), the entry relabelled as
  the unary `neg` (the wrong arity) and as `decLt` (a decision, which has no formula). -/

namespace IxCCTests.Grounding.Words

open IxCC IxCC.Grounding IxCCTests.Grounding
open Ix.Kernel (ConstantInfo Expr Level BinderMeta PropWhen)
open IxCC.Src (Term CId Width WordOp)
open IxCCTests.Src (Assert expect)

/-- The conjuncts of the word family's check that are false. -/
def failingW (i : Input) : List String :=
  (checkPartsW i.src i.env i.κ i.lpsOf i.ann i.Sl).filterMap fun (n, b) => if b then none else some n

/-- `i` read on `selEnv` of the closure `Sl`. -/
def onSel (i : Input) (Sl : List CId) : Input := { i with env := selEnv i.src i.env i.κ Sl, Sl }

/-- `instCheckB` with the instance set walked from `seeds`. -/
def instAt (i : Input) (seeds : List CId) : Bool :=
  match instWalk i.src seeds 1000000 with
  | some Inst => instCheckB i.src i.env i.κ i.lpsOf seeds Inst
  | none => false

/-- **The word family's decided hypotheses** on `j` (already on `selEnv`), the instance check seeded
by `seeds`. -/
def famW (j : Input) (seeds : List CId) : Bool :=
  (failingW j).isEmpty && noCanonAB j.src j.env j.κ j.Sl && litDefsB j.env && instAt j seeds &&
    GradedHead.sB j

/-- A root's own closure with the word entries' runtime references. -/
def rootClosure (i : Input) (rt : CId) : List CId :=
  let pins := [i.src.known.boolTrue, i.src.known.boolFalse].filterMap id
  GradedHead.wordClosure { i with Sl := CaseEmpty.reach i (rt :: pins.filter (· != rt)) }

/-- Every node of a kernel term rewritten bottom-up by `f` (applications and binders). -/
partial def rewrite (f : KExpr → KExpr) : KExpr → KExpr
  | .app g a => f (.app (rewrite f g) (rewrite f a))
  | .forallE A B m => f (.forallE (rewrite f A) (rewrite f B) m)
  | .lam A B m => f (.lam (rewrite f A) (rewrite f B) m)
  | e => f e

/-- A stored constant's type rewritten. -/
def mapType (env : KEnv) (k : KKey) (g : KExpr → KExpr) : KEnv :=
  mapConst env k fun
    | .defnInfo cv v h => .defnInfo { cv with type := g cv.type } v h
    | .thmInfo cv v => .thmInfo { cv with type := g cv.type } v
    | .ctorInfo cv np nf => .ctorInfo { cv with type := g cv.type } np nf
    | .indInfo cv caps => .indInfo { cv with type := g cv.type } caps
    | ci => ci

/-- The first `∀`'s binder datum made a proposition everywhere. -/
def propFirst : KExpr → KExpr
  | .forallE A B _ => .forallE A B { pw := .ifAllZero [] }
  | e => e

/-- The innermost `Sort 0` of a telescope made `Sort 1`. -/
def sortUp : KExpr → KExpr
  | .forallE A B m => .forallE A (sortUp B) m
  | .sort .zero => .sort (.succ .zero)
  | e => e

/-- The sides of an `@Eq T a b` under the binders swapped. -/
def swapEq : KExpr → KExpr
  | .forallE A B m => .forallE A (swapEq B) m
  | .app (.app (.app e T) a) b => .app (.app (.app e T) b) a
  | e => e

/-- The closure's first word entry of a binary operation. -/
def binEntry (i : Input) : Option (CId × Width × WordOp × CId) :=
  i.Sl.findSome? fun c => match i.src.table.resolveOf c with
    | some (.word w op thm) => if op.arity == 2 then some (c, w, op, thm) else none
    | _ => none

/-- The entry `c` relabelled as `op` in the program's table. -/
def relabel (i : Input) (c : CId) (w : Width) (op : WordOp) (thm : CId) : Input :=
  { i with src := { i.src with table := { i.src.table with
    resolve := i.src.table.resolve.insert c (.word w op thm) } } }

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let all ← GradedHead.allJobs
    let some (lw, sw, rw) := all.find? (·.1 == GradedHead.wordsLabel)
      | throw (IO.userError "no words closure")
    let (iw, _) ← loadClosure lw sw rw
    let (is, _) ← loadClosure "src-words" "fixtures/ixon-v4/src-words/words" []
    -- the closure and each root
    let mut lines : List String := []
    for (label, i, nRoots) in [(lw, iw, 7), ("src-words", is, 4)] do
      let slP := GradedHead.wordClosure i
      let jP := onSel i slP
      let roots := NoCanon.rootsOf i
      let okClo := famW jP roots
      let okRoots := roots.map fun rt => famW (onSel i (rootClosure i rt)) [rt]
      expect a (okClo && roots.length == nRoots && okRoots.all id)
        s!"words: {label}: on the closure (+{slP.length - i.Sl.length} runtime references) false \
          {failingW jP}, noCanonAB {noCanonAB jP.src jP.env jP.κ jP.Sl}, litDefsB {litDefsB jP.env}, \
          instCheckB {instAt jP roots}, headRegimeSB {GradedHead.sB jP}; {roots.length} roots \
          (expected {nRoots}), the family at each {okRoots}"
      lines := lines ++ [s!"{label}: on the closure and at each of its {roots.length} roots"]
    -- the planted controls on `grounding/words`, at its first binary entry and that entry's width
    let slP := GradedHead.wordClosure iw
    let jP := onSel iw slP
    let some (cE, wE, opE, thmE) := binEntry jP | throw (IO.userError "words: no binary entry")
    let some tk := towKeys? jP.src jP.κ wE | throw (IO.userError "words: no tower keys")
    let some (kB, _, kS) := bridgeKeys? jP.src jP.κ wE | throw (IO.userError "words: no bridge")
    let some ta := towAux? jP.env tk | throw (IO.userError "words: no tower keys")
    let some cF := jP.src.known.finMk | throw (IO.userError "words: no Fin.mk")
    let mod5 : KExpr → KExpr := fun e => if e == modK (.bvar 1) wE.size then litE 5 else e
    let modDiv : KExpr → KExpr := fun e =>
      if e == .const (primKey .mod) [] then .const (primKey .div) [] else e
    let stepBad : KExpr → KExpr := fun e =>
      if e == leApp tk.le (.bvar 2) (.app (.const Ix.Kernel.natSuccName []) (.bvar 1)) then
        leApp tk.le (.bvar 2) (.bvar 1)
      else e
    let toFin1 := mapConst jP.env ta.toFin fun
      | .defnInfo cv (.lam A (.lam B (.proj s _ e) m2) m1) h =>
        .defnInfo cv (.lam A (.lam B (.proj s 1 e) m2) m1) h
      | ci => ci
    let finTableless : KEnv :=
      { jP.env with consts := jP.env.consts.filter (·.name != Ix.Kernel.projTableName ta.fin) }
    let plants : List (String × Input) :=
      [("ofFin's first binder datum a proposition", { jP with env := mapType jP.env tk.b propFirst }),
       ("Fin's projection table removed", { jP with env := finTableless }),
       ("LT.lt's result Sort 1", { jP with env := mapType jP.env ta.lt sortUp }),
       ("BitVec.toFin's projection field 1", { jP with env := toFin1 }),
       ("Fin.mk out of the closure", onSel iw (slP.filter (· != cF))),
       ("the bridge's x % size replaced by 5", { jP with env := mapType jP.env kB (rewrite mod5) }),
       ("Nat.le.step's result Nat.le #2 #1", { jP with env := mapType jP.env kS (rewrite stepBad) }),
       ("the entry's theorem with Nat.div for Nat.mod",
         { jP with env := mapType jP.env (jP.κ thmE) (rewrite modDiv) }),
       ("the entry's theorem with its sides swapped",
         { jP with env := mapType jP.env (jP.κ thmE) swapEq }),
       ("the entry's head with no binder",
         { jP with env := mapType jP.env (jP.κ cE) fun _ => .sort .zero }),
       ("the entry relabelled neg (the wrong arity)", relabel jP cE wE .neg thmE),
       ("the entry relabelled decLt (a decision)", relabel jP cE wE .decLt thmE)]
    for (name, j) in plants do
      expect a (failingW j == ["word"]) s!"words: planted {name}: false {failingW j}, expected [word]"
    IO.println s!"words: the word family's decided hypotheses hold on {lines}; {plants.length} \
      planted controls (at {opE.leanName wE}) refused by the conjunct word alone"
    IO.println s!"tests-grounding (words): {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding (words): {error}"
    return false

end IxCCTests.Grounding.Words
