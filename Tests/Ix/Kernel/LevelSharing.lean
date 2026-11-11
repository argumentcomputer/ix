import IxCK.Kernel.Admission
import IxCK.Kernel.Cached.CoreC
import Ix.Address.Pure

/-! # Levels the ∀ rule shares (`lake test -- kernel-level-sharing`)

A ∀ whose domain and codomain are one shared type (`T (j+1) = T j → T j` in a
sharing table, or `let a(j+1) : Type := aj → aj`, which the annotation pass
substitutes) used to make the ∀ rule build `imax L_j (imax L_{j-1} …)`: a
level shared as a DAG of linear size and a tree of size `2^j`, which the level
library walks as a tree (`Level.simplify` from the sort comparison,
`levelHasParam` from every `.sort` node built). The kernel now builds the level
with `mk_imax`'s folds (`Level.mkIMax`) and reads the has-parameter bit from a
cached field (`Level.hasParamData`). Each case below is at a length that ends
only with both in place (`2^200` node visits without them); the assertions are
structural, the times printed are for reading.

* **acceptance**: the families measured when the cause was found, each a
  constant of a few hundred bytes checked by the certified entry over decoded
  records (`Ix.Kernel.Admission.checkConstants`): the `let` chain (`plain`), its
  arrow shared (`shared`), under a binder (`open`), at a universe parameter
  (`param`); and with no `let`, a chain of sharing entries (`dag`) and the same
  at a parameter (`paramdag`);
* **the level**: the executed core (`Ix.Kernel.Cached.coreKnotI .verified`)
  infers the chain `T 200` at both grades, and its sort is the two-node level
  `Prop`'s or `Sort u`'s chain started from;
* **the cached bit**: a `.sort` node over a level of depth 200 shared as a DAG
  (no parameter, so the walk could not stop early) is built and reads `false`;
* **the equality**: two equal levels of depth 200, each shared as a DAG and
  built apart (two chains at two parameters, `imax A_j B_j` and `imax B_j A_j`,
  which no fold merges), compare equal through the executed `==`
  (`Level.beqPtr`'s memoised descent, `Level.decMemo`), through `Expr.beq`'s
  level leaf, and through `Level.mkIMax`'s own test (which returns its first
  argument); without the memo each is `2^200` node visits;
* **levels that do not fold, compared only with equal ones**: over those chains,
  `def L.{u v} : A k → A k := fun x => x` (`mixedid`) and
  `def L.{u v} : (A k → A' k) → (A k → A' k) := fun f => f` (`mixeddouble`, with
  a second pair of chains whose levels equal the first's but are built apart)
  are accepted at 200 through the certified entry: every comparison of their
  levels is between equal levels, which `==` decides; without the memo each is
  `2^200` node visits;
* **what stays exposed**: two chains at two parameters whose levels `mk_max`
  cannot fold (`A (j+1) = A j → B j`, `B (j+1) = B j → A j`, `mixeddag`), with
  the declared sort `Sort (max (u+1) (v+1))`, equal to the inferred one only
  after normalisation: at length 10 the constant is accepted, and its inferred
  level is still a DAG whose tree has more than 1,000 nodes, so the comparison
  of the declared sort with it doubles per step (as in Lean's own kernel). -/

namespace Tests.LevelSharing

open Ix.Kernel (Level Expr BinderMeta)

abbrev IE := _root_.Ixon.Expr

/-! ## The constants -/

def arrow : IE := _root_.Ixon.Expr.leanAll (.var 0) (.var 1)

/-- `let a0 : Type := first; let a(j+1) : Type := arr; …; Type`. -/
def letType (k : Nat) (arr : IE) (first : IE := .sort 0) : IE := Id.run do
  let mut body : IE := .sort 1
  for _ in [0:k] do
    body := _root_.Ixon.Expr.leanLet false (.sort 1) arr body
  return _root_.Ixon.Expr.leanLet false (.sort 1) first body

/-- `Prop`, `Type`. -/
def univs : Array _root_.Ixon.Univ := #[.zero, .succ .zero]
/-- `Sort u`, `Sort (u+1)`. -/
def univsU : Array _root_.Ixon.Univ := #[.var 0, .succ (.var 0)]
/-- `Sort u`, `Sort v`, `u+1`, `v+1`, `max (u+1) (v+1)`. -/
def univsUV : Array _root_.Ixon.Univ :=
  #[.var 0, .var 1, .succ (.var 0), .succ (.var 1), .max (.succ (.var 0)) (.succ (.var 1))]

/-- `T 1 = S → S` (`S` the sort `.sort 0` names), `T (j+1) = T j → T j`;
entry `j` is `T (j+1)`. -/
def dagTable (k : Nat) : Array IE :=
  (Array.range k).map fun j =>
    if j == 0 then _root_.Ixon.Expr.leanAll (.sort 0) (.sort 0)
    else _root_.Ixon.Expr.leanAll (.share (j - 1).toUInt64) (.share (j - 1).toUInt64)

/-- `A 1 = Sort u → Sort v`, `B 1 = Sort v → Sort u`, `A (j+1) = A j → B j`,
`B (j+1) = B j → A j`; entries `2j` and `2j+1`. -/
def mixedTable (k : Nat) : Array IE := Id.run do
  let mut t : Array IE := #[]
  for j in [0:k] do
    if j == 0 then
      t := t.push (_root_.Ixon.Expr.leanAll (.sort 0) (.sort 1))
      t := t.push (_root_.Ixon.Expr.leanAll (.sort 1) (.sort 0))
    else
      let a := (2 * (j - 1)).toUInt64
      let b := (2 * (j - 1) + 1).toUInt64
      t := t.push (_root_.Ixon.Expr.leanAll (.share a) (.share b))
      t := t.push (_root_.Ixon.Expr.leanAll (.share b) (.share a))
  return t

def defn (lvls : UInt64) (ty val : IE) (sharing : Array IE) (us : Array _root_.Ixon.Univ) :
    _root_.Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, lvls, ty, val⟩, sharing, #[], us⟩

/-- The families, at length `k ≥ 1`. -/
def family (k : Nat) : List (String × _root_.Ixon.Constant) :=
  let top : IE := .share (k - 1).toUInt64
  [("plain", defn 0 (letType k arrow) (.sort 0) #[] univs),
   ("shared", defn 0 (letType k (.share 0)) (.sort 0) #[arrow] univs),
   ("open", defn 0 (_root_.Ixon.Expr.leanAll (.sort 1) (letType k arrow (.var 0)))
      (_root_.Ixon.Expr.leanLam (.sort 1) (.sort 0)) #[] univs),
   ("dag", defn 0 (.sort 1) top (dagTable k) univs),
   ("param", defn 1 (letType k arrow) (.sort 0) #[] univsU),
   ("paramdag", defn 1 (.sort 1) top (dagTable k) univsU)]

/-- `def L.{u v} : Sort (max (u+1) (v+1)) := A k`. -/
def mixeddag (k : Nat) : _root_.Ixon.Constant :=
  defn 2 (.sort 4) (.share (2 * (k - 1)).toUInt64) (mixedTable k) univsUV

/-- `A`, `B` as in `mixedTable`, and a second pair `A' 1 = Sort u → (Sort v → Sort v)`,
`B' 1 = (Sort v → Sort v) → Sort u` under the same recurrences, whose levels equal
`A`'s and `B`'s but are built apart; entries `4j` to `4j+3`. -/
def doubleTable (k : Nat) : Array IE := Id.run do
  let mut t : Array IE := #[]
  let vv : IE := _root_.Ixon.Expr.leanAll (.sort 1) (.sort 1)
  for j in [0:k] do
    if j == 0 then
      t := t.push (_root_.Ixon.Expr.leanAll (.sort 0) (.sort 1))
      t := t.push (_root_.Ixon.Expr.leanAll (.sort 1) (.sort 0))
      t := t.push (_root_.Ixon.Expr.leanAll (.sort 0) vv)
      t := t.push (_root_.Ixon.Expr.leanAll vv (.sort 0))
    else
      let b := 4 * (j - 1)
      for (x, y) in [(0, 1), (1, 0), (2, 3), (3, 2)] do
        t := t.push (_root_.Ixon.Expr.leanAll (.share (b + x).toUInt64) (.share (b + y).toUInt64))
  return t

/-- Two constants whose levels do not fold but whose comparisons are between
equal levels: `def L.{u v} : A k → A k := fun x => x` (`mixedid`) and
`def L.{u v} : (A k → A' k) → (A k → A' k) := fun f => f` (`mixeddouble`, where
the ∀ rule's fold compares `A k`'s level with `A' k`'s, equal and built apart). -/
def mixedEqual (k : Nat) : List (String × _root_.Ixon.Constant) :=
  let a : IE := .share (2 * (k - 1)).toUInt64
  let a4 : IE := .share (4 * (k - 1)).toUInt64
  let a' : IE := .share (4 * (k - 1) + 2).toUInt64
  let f := _root_.Ixon.Expr.leanAll a4 a'
  [("mixedid", defn 2 (_root_.Ixon.Expr.leanAll a a) (_root_.Ixon.Expr.leanLam a (.var 0))
      (mixedTable k) univsUV),
   ("mixeddouble", defn 2 (_root_.Ixon.Expr.leanAll f f) (_root_.Ixon.Expr.leanLam f (.var 0))
      (doubleTable k) univsUV)]

/-- Check one constant with the certified entry over decoded records. -/
def check (c : _root_.Ixon.Constant) : IO (Except String Nat × Nat) := do
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let addr := Address.blake3Pure (_root_.Ixon.serConstant c)
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ =>
    Ix.Kernel.Admission.checkConstants Address.blake3Pure table [(addr, c)] []
      (fun _ => some (Ix.Kernel.ReducibilityHint.regular 1))
  let t1 ← IO.monoMsNow
  return (match r with
    | .ok env => .ok env.consts.length
    | .error e => .error s!"{e}", t1 - t0)

/-! ## The level, through the executed core -/

/-- Whether a level's tree has at most `cap` nodes (at most `cap` visited). -/
def sizeAtMost (cap : Nat) (l : Level) : Bool := Id.run do
  let mut stack : List Level := [l]
  for _ in [0:cap] do
    match stack with
    | [] => return true
    | x :: rest =>
      stack := match x with
        | .succ a => a :: rest
        | .max a b | .imax a b => a :: b :: rest
        | _ => rest
  return stack.isEmpty

def never : BinderMeta := { pw := .never }

/-- `T 0 = Sort u`, `T (j+1) = T j → T j`, each `T j` one object. -/
def dagTerm (u : Level) : Nat → Expr .anon
  | 0 => .sort u
  | n + 1 => let t := dagTerm u n; .forallE t t never

/-- `A (j+1) = A j → B j`, `B (j+1) = B j → A j` from `Sort u`, `Sort v`. -/
def mixedTerms : Nat → Expr .anon × Expr .anon
  | 0 => (.sort (.param 0), .sort (.param 1))
  | n + 1 => let (a, b) := mixedTerms n; (.forallE a b never, .forallE b a never)

/-- The executed core's inferred type of a closed term, at the full or the
io grade, in the empty environment. -/
def infer (io : Bool) (e : Expr .anon) : Except String (Expr .anon) :=
  let core := Ix.Kernel.Cached.coreKnotI .verified
    (Ix.Kernel.mkFEnv (⟨[]⟩ : Ix.Kernel.Env .anon)) Ix.Kernel.checkFuel
  match StateT.run (if io then core.inferIO 0 e else core.infer 0 e) {} with
  | .ok (t, _) => .ok t
  | .error _ => .error "the core refused it"

/-- `imax L L` nested `n` deep, `L` one object at each depth. -/
def dagLevel : Nat → Level
  | 0 => .zero
  | n + 1 => let l := dagLevel n; .imax l l

/-- `A 0 = u`, `B 0 = v`, `A (j+1) = imax A_j B_j`, `B (j+1) = imax B_j A_j`,
each one object per depth: DAGs of linear size whose trees double per step. -/
def mixedLevels : Nat → Level × Level
  | 0 => (.param 0, .param 1)
  | n + 1 => let (a, b) := mixedLevels n; (.imax a b, .imax b a)

/-- The same levels built apart: a second function, so that the compiled
test cannot share its result with `mixedLevels`'. -/
def mixedLevelsApart : Nat → Level × Level
  | 0 => (.param 0, .param 1)
  | n + 1 => let (a, b) := mixedLevelsApart n; (.imax a b, .imax b a)

def run : IO UInt32 := do
  IO.println "kernel-level-sharing: levels the ∀ rule shares"
  let mut failed := 0
  let k := 200
  for (name, c) in family k do
    let (r, ms) ← check c
    match r with
    | .ok n =>
      IO.println s!"  {name} k={k}: accepted ({n} constants), {(_root_.Ixon.serConstant c).size} bytes, {ms} ms"
    | .error e =>
      IO.println s!"  {name} k={k}: REFUSED: {e}"
      failed := failed + 1
  for (label, u) in [("Prop", Level.zero), ("Sort u", Level.param 0)] do
    for io in [false, true] do
      let grade := if io then "io" else "full"
      match infer io (dagTerm u k) with
      | .ok (.sort l) =>
        let ok := l == .succ u && sizeAtMost 2 l
        IO.println s!"  T {k} over {label}, {grade} grade: the sort's level has {if sizeAtMost 2 l then "at most 2" else "MORE THAN 2"} nodes{if ok then "" else "  FAILED"}"
        unless ok do failed := failed + 1
      | .ok _ =>
        IO.println s!"  T {k} over {label}, {grade} grade: not a sort  FAILED"
        failed := failed + 1
      | .error e =>
        IO.println s!"  T {k} over {label}, {grade} grade: refused: {e}  FAILED"
        failed := failed + 1
  let s : Expr .anon := .sort (dagLevel k)
  let okBit := !s.hasLP
  IO.println s!"  a sort over a level of depth {k} shared as a DAG: has-parameter bit {s.hasLP}{if okBit then "" else "  FAILED"}"
  unless okBit do failed := failed + 1
  -- the equality on two equal DAG levels built apart
  let (a, b) := mixedLevels k
  let (a', b') := mixedLevelsApart k
  let eqCases : List (String × Bool × Bool) :=
    [("A == A' (built apart)", a == a', true),
     ("B == B' (built apart)", b == b', true),
     ("A == B'", a == b', false),
     ("Sort A == Sort A' (Expr.beq)", (Expr.sort a : Expr .anon) == Expr.sort a', true),
     ("mkIMax A A' == A (the fold's test)", Level.mkIMax a a' == a, true)]
  for (label, got, want) in eqCases do
    IO.println s!"  depth {k}, {label}: {got}{if got == want then "" else "  FAILED"}"
    unless got == want do failed := failed + 1
  -- levels that do not fold, compared only with equal levels: through the entry
  for (name, c) in mixedEqual k do
    let (r, ms) ← check c
    match r with
    | .ok n =>
      IO.println s!"  {name} k={k}: accepted ({n} constants), {(_root_.Ixon.serConstant c).size} bytes, {ms} ms"
    | .error e =>
      IO.println s!"  {name} k={k}: REFUSED: {e}"
      failed := failed + 1
  -- what stays exposed: the levels of two interleaved chains do not fold
  let km := 10
  let (r, ms) ← check (mixeddag km)
  let accepted := match r with | .ok _ => true | .error _ => false
  let tree := match infer false (mixedTerms km).1 with
    | .ok (.sort l) => !sizeAtMost 1000 l
    | _ => false
  IO.println s!"  mixeddag k={km}: {if accepted then "accepted" else "REFUSED"} in {ms} ms; its level's tree has {if tree then "more than 1,000" else "AT MOST 1,000"} nodes (not folded, as expected)"
  unless accepted && tree do failed := failed + 1
  (← IO.getStdout).flush
  if failed == 0 then
    IO.println "kernel-level-sharing: every case passed"
    return 0
  IO.eprintln s!"kernel-level-sharing: {failed} cases failed"
  return 1

end Tests.LevelSharing
