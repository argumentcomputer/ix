import IxCK.Kernel.Admission
import IxCK.Kernel.Cached.CoreC
import Ix.Address.Pure
import Ix.KernelDisplay.Render

/-! # Levels the ∀ rule shares (`lake test -- kernel-level-sharing`)

A ∀ whose domain and codomain are one shared type (`T (j+1) = T j → T j` in a
sharing table, or `let a(j+1) : Type := aj → aj`, which the annotation pass
substitutes) makes the ∀ rule build `imax L_j (imax L_{j-1} …)`: a level
shared as a DAG of linear size and a tree of size `2^j`. The rule's level is
upstream's `imax u v`, unfolded; what keeps the kernel polynomial is in the
executed tier: the has-parameter bit is a cached field
(`Level.hasParamData`), the level walks are memoised on shared levels
(`Level.simplify`, `leqCore`, `zeronessOf`, `isNeverZero`, `==`), and the
cached core hash-conses the ∀ rule's levels (`Cached.internLM`), so that the
level the binder loop builds again for a telescope's tail is the object built
before (without it the `let` chain is cubic: 9 s at 2,000 `let`s). Each case
below is at a length that ends only with these in place; the times printed
are for reading, except the two bounded ones.

* **acceptance**: the families measured when the cause was found, each a
  constant of a few hundred bytes checked by the certified entry over decoded
  records (`Ix.Kernel.Admission.checkConstants`): the `let` chain (`plain`), its
  arrow shared (`shared`), under a binder (`open`), at a universe parameter
  (`param`); and with no `let`, a chain of sharing entries (`dag`) and the same
  at a parameter (`paramdag`);
* **the long chains, bounded**: `plain` and `param` at 2,000 `let`s (a 14 KB
  constant) each accepted within `longBoundMs`. Quadratic, as here, they take
  about 1 s and 1.4 s on the build box under load; without the hash-consing
  they are cubic and take 9 s and 13 s, and the case fails;
* **chains whose tail is checked already, bounded**: `plain` and `dag` at
  16,000 steps and `dagequal` (a function between two copies of the chain
  `T 8,000` in one sharing table, so the declared type and the value's type are
  equal terms annotated apart) each accepted within `stopBoundMs`; without the
  binder loops' stop at a residual the memo holds they are quadratic and
  fail; and the λ chain `lamlet` at 2,000, timed but not bounded (still
  quadratic, in `Level.zeronessOf`);
* **the level**: the executed core (`Ix.Kernel.Cached.coreKnotI .verified`)
  infers the chain `T 200` at both grades; its sort's level is the ∀ rule's
  `imax` chain, a tree of more than 1,000 nodes, and is decided equivalent to
  `succ u` (`Level.isEquiv`);
* **the failure, rendered**: the core's failure on `(fun x : Prop => x) (T 500)`
  (an application type mismatch, whose display holds the argument's sort, a
  level whose tree has `2^500` leaves) in each mode, `.anon`, `.meta` and
  `.source`, is printed (`Ix.KernelDisplay.renderFailure`) and its sort printed
  as the display prints a term (`renderTerm`), within `renderBoundMs` and
  `renderBoundChars`: the printer shows at most `maxLevelNodes` `imax` nodes and
  `⋯` past them;
* **the cached bit**: a `.sort` node over a level of depth 200 shared as a DAG
  (no parameter, so the walk could not stop early) is built and reads `false`;
* **the equality**: two equal levels of depth 200, each shared as a DAG and
  built apart (two chains at two parameters, `imax A_j B_j` and `imax B_j A_j`,
  which no fold merges), compare equal through the executed `==`
  (`Level.beqPtr`'s memoised descent, `Level.decMemo`), through `Expr.beq`'s
  level leaf, and through `Level.isEquiv`'s first test; without the memo each
  is `2^200` node visits;
* **levels that do not fold, compared only with equal ones**: over those chains,
  `def L.{u v} : A k → A k := fun x => x` (`mixedid`) and
  `def L.{u v} : (A k → A' k) → (A k → A' k) := fun f => f` (`mixeddouble`, with
  a second pair of chains whose levels equal the first's but are built apart)
  are accepted at 200 through the certified entry: every comparison of their
  levels is between equal levels, which `==` decides; without the memo each is
  `2^200` node visits;
* **levels compared with unequal ones** (the memoised level walks:
  `Level.simplify`, `leqCore`, `subst`, `zeronessOf`, `isNeverZero`, each run
  with a per-call memo on large levels): two chains at two parameters whose
  levels the official kernel's `mk_max` cannot fold (`A (j+1) = A j → B j`, `B (j+1) = B j → A j`,
  `mixeddag`), declared `Sort (max (u+1) (v+1))`, equal to the inferred sort
  only after normalisation, whose inferred level at length 10 is still a DAG
  with a tree of more than 1,000 nodes; and `imaxswap` (a chain of `imax` over
  parameters compared with a permutation of itself), `deltamax` and
  `deltazero` (unfolding a chain of definitions each instantiating the previous
  at `max u u`; the second makes the ∀ rule read the resulting sort). Each is
  accepted at a length that ends only with the memos (`imaxswap` at 40,
  the others at 200);
* **the reduction from satisfiability**: the comparison of levels with `imax`
  is coNP-hard (section below), so a family stays exponential for any
  complete comparison; its generator, with the two controls run on the
  kernel: an unsatisfiable formula's constant is accepted, a satisfiable
  one's refused (6 variables). -/

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

def defnR (lvls : UInt64) (ty val : IE) (sharing : Array IE) (refs : Array Address)
    (us : Array _root_.Ixon.Univ) : _root_.Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, lvls, ty, val⟩, sharing, refs, us⟩

def defn (lvls : UInt64) (ty val : IE) (sharing : Array IE) (us : Array _root_.Ixon.Univ) :
    _root_.Ixon.Constant :=
  defnR lvls ty val sharing #[] us

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

/-! ## Families the memoised level walks close

`imaxswap n`: `def S.{u0 … u(n-1)} : Sort (succ L) := Sort L'`, `L` the chain
`imax u0 (imax u1 (… u(n-1)))`, `L'` the same with `u0` and `u1` swapped: equal
levels of `2n − 1` nodes, no sharing. `leqCore` distributes
`imax a (imax x y)` into a `max` whose halves distribute the same suffixes
again: `2^(n-1)` calls at least without its memo. -/

/-- `imax u(i) (imax u(i+1) (… u(n-1)))` over the listed parameter indices. -/
def imaxChain : List Nat → _root_.Ixon.Univ
  | [] => .zero
  | [i] => .var i.toUInt64
  | i :: rest => .imax (.var i.toUInt64) (imaxChain rest)

def imaxswap (n : Nat) : _root_.Ixon.Constant :=
  let idx := List.range n
  let l' := imaxChain (match idx with | a :: b :: rest => b :: a :: rest | x => x)
  defn n.toUInt64 (.sort 1) (.sort 0) #[] #[l', .succ (imaxChain idx)]

/-- The address of a constant, as the entry computes it. -/
def addrOf (c : _root_.Ixon.Constant) : Address := Address.blake3Pure (_root_.Ixon.serConstant c)

/-- `succ^n u`. -/
def succs : Nat → _root_.Ixon.Univ
  | 0 => .var 0
  | n + 1 => .succ (succs n)

/-- `D0.{u} : Sort (u + top) := Sort (u + top - 1)`, `Dj.{u} : Sort (u + top) :=
D(j-1).{max u u}` for `j = 1 … k`, then `last` with the address of `Dk`:
unfolding `Dk.{v}` instantiates `max u u` `k` times, and `Level.subst` puts one
object at both sides of each `max`, a level of `k` distinct nodes and a tree
of `2^k`. -/
def deltaChain (k top : Nat) (last : Address → _root_.Ixon.Constant) :
    List _root_.Ixon.Constant := Id.run do
  let d0 := defn 1 (.sort 2) (.sort 1) #[] #[.var 0, succs (top - 1), succs top]
  let mut cs := #[d0]
  let mut prev := addrOf d0
  for _ in [0:k] do
    let dj := defnR 1 (.sort 1) (.ref 0 #[2]) #[] #[prev] #[.var 0, succs top, .max (.var 0) (.var 0)]
    cs := cs.push dj
    prev := addrOf dj
  return (cs.push (last prev)).toList

/-- `deltamax k`: `top = 2`, then `X.{v} : Dk.{v} := Sort v`; the declared
sort `Sort (L_k + 2)` is compared with `Sort (v + 2)` (`simplify`, `leqCore`). -/
def deltamax (k : Nat) : List _root_.Ixon.Constant :=
  deltaChain k 2 fun prev => defnR 1 (.ref 0 #[0]) (.sort 0) #[] #[prev] #[.var 0]

/-- `deltazero k`: `top = 1`, then `Y.{v} : Sort (imax (v+1) v) := ∀ x : Dk.{v}, x`:
the ∀ rule meets the codomain sort `L_k` (its `zeronessOf`), and the sort
comparison splits on `v`, substituting into `L_k`. -/
def deltazero (k : Nat) : List _root_.Ixon.Constant :=
  deltaChain k 1 fun prev =>
    defnR 1 (.sort 1) (_root_.Ixon.Expr.leanAll (.ref 0 #[0]) (.var 0)) #[] #[prev]
      #[.var 0, .imax (.succ (.var 0)) (.var 0)]

/-! ## The comparison is coNP-hard: the reduction from satisfiability

A CNF formula φ over variables `1 … n` (clauses of literals `±i`) becomes the
constant `def S.{x1 y1 … xn yn} : Sort (succ R) := Sort (max G R)`, accepted
exactly when `G ≤ R` at every assignment of the parameters, which holds
exactly when φ is unsatisfiable (`docs/kernel.md`, "Running time"):

* each variable `i` becomes two parameters, `xi` (index `2(i-1)`, nonzero:
  "i true") and `yi` (index `2(i-1)+1`, nonzero: "i false");
* `2` is `succ (succ zero)`, and `imaxAll [c1, …, cm]` is
  `imax (… (imax 2 c1) …) cm`. Its value is never above `max 2 c1 … cm`,
  and when every parameter is `0` or `1` it is at least `2` exactly when
  no `cj` is zero (`imax a b` is `0` where `b` is, else `max a b`);
* `G = imaxAll [max x1 y1, …, max xn yn]`;
* a clause `C` becomes `T_C = imaxAll` of the complements of its literals
  (`yi` for `i`, `xi` for `-i`);
* `R = max (T_C1, …, T_Cm, x1, y1, …, xn, yn)`.

Why: `G` is at most `max 2` (its parameters) and `R` at least every
parameter, so `G ≤ R` can fail only where every parameter is `0` or `1`;
there `G` is `2` when each pair has a nonzero member and at most `1`
otherwise, and `R ≤ 1` exactly when each `T_C` has a zero parameter. So
`G ≤ R` fails exactly where each pair has a nonzero member and each clause
has a literal whose complement is `0`. Reading `i` as true where `yi = 0`
makes every such literal true, so φ is satisfied; and an assignment that
satisfies φ gives such a valuation (`xi = 1, yi = 0` where `i` is true,
`xi = 0, yi = 1` where it is false).

`G` has `4n + 3` nodes and `R` has `2 |φ| + 4m + 4n − 1` (`|φ|` literal
occurrences, `m` clauses): the instance is linear in the formula. -/

/-- A CNF formula: clauses of literals `±i`, variables numbered from 1. -/
abbrev Cnf := List (List Int)

def two : _root_.Ixon.Univ := .succ (.succ .zero)

/-- The parameter of variable `i` (from 1): `xi` if `pos`, else `yi`. -/
def litParam (i : Nat) (pos : Bool) : _root_.Ixon.Univ :=
  .var (if pos then 2 * (i - 1) else 2 * (i - 1) + 1).toUInt64

def imaxAll (cs : List _root_.Ixon.Univ) : _root_.Ixon.Univ := cs.foldl (fun acc c => .imax acc c) two

def maxAll : List _root_.Ixon.Univ → _root_.Ixon.Univ
  | [] => .zero
  | [c] => c
  | c :: cs => .max c (maxAll cs)

/-- The constant of the reduction for `φ` over `n` variables. -/
def cnfConst (n : Nat) (φ : Cnf) : _root_.Ixon.Constant :=
  let g := imaxAll ((List.range n).map fun i => .max (litParam (i + 1) true) (litParam (i + 1) false))
  let ts := φ.map fun cl => imaxAll (cl.map fun l => litParam l.natAbs (l < 0))
  let ps := (List.range n).flatMap fun i => [litParam (i + 1) true, litParam (i + 1) false]
  let r := maxAll (ts ++ ps)
  defn (2 * n).toUInt64 (.sort 0) (.sort 1) #[] #[.succ r, .max g r]

/-- `1 ∧ (¬1 ∨ 2) ∧ … ∧ (¬(n-1) ∨ n) ∧ ¬n`: unsatisfiable, and exponential for
the kernel's comparison (measured: about ×4 per two variables). -/
def cnfChain (n : Nat) : Cnf :=
  [[1]] ++ ((List.range (n - 1)).map fun (i : Nat) => [-((i : Int) + 1), (i : Int) + 2]) ++
    [[-(n : Int)]]

/-- The same chain without its last clause: satisfiable (every variable true). -/
def cnfChainSat (n : Nat) : Cnf := (cnfChain n).dropLast

/-- Check constants, in order, with the certified entry over decoded records. -/
def checkAll (cs : List _root_.Ixon.Constant) : IO (Except String Nat × Nat) := do
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ =>
    Ix.Kernel.Admission.checkConstants Address.blake3Pure table (cs.map fun c => (addrOf c, c)) []
      (fun _ => some (Ix.Kernel.ReducibilityHint.regular 1))
  let t1 ← IO.monoMsNow
  return (match r with
    | .ok env => .ok env.consts.length
    | .error e => .error s!"{e}", t1 - t0)

/-- Check one constant with the certified entry over decoded records. -/
def check (c : _root_.Ixon.Constant) : IO (Except String Nat × Nat) := checkAll [c]

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

/-! ## Chains whose tail is checked already: bounds

The binder-telescope loops stop at a closed residual the memo already
holds (`Ix.Kernel.Cached.peelFuelToM`), and a level is simplified through
the declaration's memo (`Ix.Kernel.Cached.simplifyMemoC`). Without the
first, every step of a chain re-peeled the whole telescope below it, and
annotation rebuilt it as fresh nodes: quadratic time and memory, and two
annotations of one chain shared nothing, so comparing them visited about
`k²/2` pairs. -/

/-- `U 0 = Prop → Prop`, `U (j+1) = Prop → U j`; entry `j` is `U j`. -/
def lamTable (k : Nat) : Array IE :=
  (Array.range (k + 1)).map fun j =>
    if j == 0 then _root_.Ixon.Expr.leanAll (.sort 0) (.sort 0)
    else _root_.Ixon.Expr.leanAll (.sort 0) (.share (j - 1).toUInt64)

/-- `lamlet k`: `def L : Type := let a0 : U 0 := fun x : Prop => x;
let a(j+1) : U (j+1) := fun _ : Prop => aj; …; Prop`, a chain of λ
telescopes, each step a `fun` over the previous value. -/
def lamLet (k : Nat) : _root_.Ixon.Constant := Id.run do
  let mut body : IE := .sort 0
  for i in [0:k] do
    let j := k - i
    body := _root_.Ixon.Expr.leanLet false (.share j.toUInt64)
      (_root_.Ixon.Expr.leanLam (.sort 0) (.var 1)) body
  return defn 0 (.sort 1)
    (_root_.Ixon.Expr.leanLet false (.share 0) (_root_.Ixon.Expr.leanLam (.sort 0) (.var 0)) body)
    (lamTable k) univs

/-- `dagequal k`: `def E : T k → T k := fun x : T' k => x`, `T'` a second copy
of the chain in the same sharing table: the value's inferred type and the
declared type are equal terms annotated apart. -/
def dagEqual (k : Nat) : _root_.Ixon.Constant :=
  let copy : Array IE := (Array.range k).map fun j =>
    if j == 0 then _root_.Ixon.Expr.leanAll (.sort 0) (.sort 0)
    else _root_.Ixon.Expr.leanAll (.share (k + j - 1).toUInt64) (.share (k + j - 1).toUInt64)
  let top : IE := .share (k - 1).toUInt64
  let top' : IE := .share (2 * k - 1).toUInt64
  defn 0 (_root_.Ixon.Expr.leanAll top top) (_root_.Ixon.Expr.leanLam top' (.var 0))
    (dagTable k ++ copy) univs

/-- The bound on `plain` and `dag` at 16,000 steps and `dagequal` at 8,000.
Measured on the build box under load: 916, 283 and 159 ms with the stop;
without it 4,112, 2,637 and 3,510 ms already at 4,000 steps, about four to
five times more per doubling. The bound is at least five times the time
measured with the stop. -/
def stopBoundMs : Nat := 5000

/-! ## The long chains and the rendered failure: bounds -/

/-- The bound on `plain` and `param` at 2,000 `let`s through the certified
entry. Measured on the build box at load 30 to 45: about 1,000 and 1,400 ms
with the hash-consing, 8,900 and 13,400 ms without it (cubic); the bound sits
between, with a factor of about 3.5 for a slower or busier runner. -/
def longBoundMs : Nat := 5000

/-- The bound on printing the failure about a level whose tree has `2^500`
leaves, and on its length: the printer shows at most `maxLevelNodes` (64)
`imax` nodes of a level and at most `maxSteps` (5,000) nodes of a term. -/
def renderBoundMs : Nat := 2000
def renderBoundChars : Nat := 100000

/-- `T 0 = Prop`, `T (j+1) = T j → T j` at any mode. -/
def dagTermAt (md : Ix.Kernel.Mode) : Nat → Expr md
  | 0 => .sort .zero
  | n + 1 => let t := dagTermAt md n; .forallE t t never

/-- The executed core on `(fun x : Prop => x) (T k)` at mode `md`: an
application type mismatch whose display (outside `.anon`) holds the
argument's inferred sort `Sort L`, `L` the ∀ rule's level of `T k` (`k` shared
`imax` nodes, a tree of `2^k` leaves); with that sort, inferred alone. -/
def mismatchAt (md : Ix.Kernel.Mode) (k : Nat) :
    Except String (Ix.Kernel.CheckError md × Expr md) :=
  let core := Ix.Kernel.Cached.coreKnotI .verified
    (Ix.Kernel.mkFEnv (⟨[]⟩ : Ix.Kernel.Env md)) Ix.Kernel.checkFuel
  let t := dagTermAt md k
  let e : Expr md := .app (.lam (.sort .zero) (.bvar 0) never) t
  match StateT.run (core.infer 0 e) {}, StateT.run (core.infer 0 t) {} with
  | .error err, .ok (ty, _) => .ok (err, ty)
  | .ok _, _ => .error "the core accepted the mismatch"
  | _, .error _ => .error "the core refused T k"

/-- The failure as `renderFailure` prints it (its head: the display's terms
are read only with the display-only `unsafe` read,
`Ix.KernelDisplay.peekAll`, which this safe test does not take) and the sort
as `renderTerm` prints it, which is how `renderFailure` prints each of the
display's terms. -/
def renderBoth {md : Ix.Kernel.Mode} (err : Ix.Kernel.CheckError md) (ty : Expr md) : String × String :=
  (Ix.KernelDisplay.renderFailure {} err, Ix.KernelDisplay.renderTerm {} ty)

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
  -- the long chains: quadratic with the hash-consing, cubic without it
  let kl := 2000
  for (name, c) in (family kl).filter (fun p => p.1 == "plain" || p.1 == "param") do
    let (r, ms) ← check c
    let ok := (match r with | .ok _ => true | .error _ => false) && ms ≤ longBoundMs
    IO.println s!"  {name} k={kl}: {match r with | .ok n => s!"accepted ({n} constants)" | .error e => s!"REFUSED: {e}"}, {(_root_.Ixon.serConstant c).size} bytes, {ms} ms (bound {longBoundMs} ms){if ok then "" else "  FAILED"}"
    unless ok do failed := failed + 1
  -- chains whose tail is checked already: linear with the telescope stop,
  -- quadratic without it
  let stops : List (String × _root_.Ixon.Constant) :=
    (family 16000).filter (fun p => p.1 == "plain" || p.1 == "dag") ++
      [("dagequal", dagEqual 8000)]
  for (name, c) in stops do
    let (r, ms) ← check c
    let ok := (match r with | .ok _ => true | .error _ => false) && ms ≤ stopBoundMs
    IO.println s!"  {name} (telescope stop): {match r with | .ok n => s!"accepted ({n} constants)" | .error e => s!"REFUSED: {e}"}, {(_root_.Ixon.serConstant c).size} bytes, {ms} ms (bound {stopBoundMs} ms){if ok then "" else "  FAILED"}"
    unless ok do failed := failed + 1
  -- the λ chain: accepted, its time printed, not bounded (still quadratic:
  -- `Level.zeronessOf` walks the ∀ rule's level of each step's type)
  let (r, ms) ← check (lamLet 2000)
  let okL := match r with | .ok _ => true | .error _ => false
  IO.println s!"  lamlet k=2000: {match r with | .ok n => s!"accepted ({n} constants)" | .error e => s!"REFUSED: {e}"}, {ms} ms (not bounded){if okL then "" else "  FAILED"}"
  unless okL do failed := failed + 1
  -- the failure about such a level, rendered in each mode (only the printing
  -- is timed)
  let kr := 500
  for md in [Ix.Kernel.Mode.anon, .meta, .source] do
    let (ok, shown) ← match ← IO.lazyPure fun _ => mismatchAt md kr with
      | .ok (err, ty) => do
        let t0 ← IO.monoMsNow
        let (head, sort) ← IO.lazyPure fun _ => renderBoth err ty
        let t1 ← IO.monoMsNow
        let n := head.length + sort.length
        let isMismatch := (head.splitOn "application type mismatch").length > 1
        let elided := (sort.splitOn "⋯").length > 1
        pure (isMismatch && elided && t1 - t0 ≤ renderBoundMs && n ≤ renderBoundChars,
          s!"printed in {t1 - t0} ms, {n} characters; the sort: {(sort.take 100).toString}…")
      | .error e => pure (false, e)
    IO.println s!"  the failure about T {kr}'s sort, mode {repr md}: {shown}{if ok then "" else "  FAILED"}"
    unless ok do failed := failed + 1
  for (label, u) in [("Prop", Level.zero), ("Sort u", Level.param 0)] do
    for io in [false, true] do
      let grade := if io then "io" else "full"
      match infer io (dagTerm u k) with
      | .ok (.sort l) =>
        -- the rule's level `imax L L` at every step: a tree of `2^k` nodes,
        -- equal to `succ u` in every assignment, which the memoised walks decide
        let t0 ← IO.monoMsNow
        let eqv := Level.isEquiv l (.succ u)
        let t1 ← IO.monoMsNow
        let big := !sizeAtMost 1000 l
        let ok := big && eqv == some true
        IO.println s!"  T {k} over {label}, {grade} grade: the sort's level has {if big then "more than 1,000" else "AT MOST 1,000"} tree nodes and is equivalent to succ u: {repr eqv} in {t1 - t0} ms{if ok then "" else "  FAILED"}"
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
     ("isEquiv A A' (the sort comparison's first test)", Level.isEquiv a a' == some true, true)]
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
  -- levels that do not fold, compared with unequal ones: the memoised walks.
  -- Their trees stay large (the folds cannot merge them) ...
  let km := 10
  let tree := match infer false (mixedTerms km).1 with
    | .ok (.sort l) => !sizeAtMost 1000 l
    | _ => false
  IO.println s!"  mixeddag's level at k={km}: its tree has {if tree then "more than 1,000" else "AT MOST 1,000"} nodes (not folded, as expected)"
  unless tree do failed := failed + 1
  -- ... and the families are accepted at lengths that end only with the memos
  -- (`simplify`, `leqCore`, `subst`, `zeronessOf`, `isNeverZero`): each is at
  -- least `2^39` steps without them.
  let memoCases : List (String × List _root_.Ixon.Constant) :=
    [("imaxswap n=40", [imaxswap 40]), ("deltamax k=200", deltamax 200),
     ("mixeddag k=200", [mixeddag 200]), ("deltazero k=200", deltazero 200)]
  for (name, cs) in memoCases do
    let (r, ms) ← checkAll cs
    let bytes := cs.foldl (fun n c => n + (_root_.Ixon.serConstant c).size) 0
    match r with
    | .ok n => IO.println s!"  {name}: accepted ({n} constants), {bytes} bytes, {ms} ms"
    | .error e =>
      IO.println s!"  {name}: REFUSED: {e}"
      failed := failed + 1
  -- the reduction from satisfiability (coNP-hardness of the comparison): an
  -- unsatisfiable formula is accepted, a satisfiable one refused. Verdicts only:
  -- the comparison is exponential on this family, so the size is small.
  let nc := 6
  for (name, φ, want) in [("unsatisfiable chain", cnfChain nc, true),
      ("satisfiable chain", cnfChainSat nc, false)] do
    let (r, ms) ← check (cnfConst nc φ)
    let got := match r with | .ok _ => true | .error _ => false
    IO.println s!"  CNF reduction, {name}, {nc} variables: {if got then "accepted" else "refused"} in {ms} ms{if got == want then "" else "  FAILED"}"
    unless got == want do failed := failed + 1
  (← IO.getStdout).flush
  if failed == 0 then
    IO.println "kernel-level-sharing: every case passed"
    return 0
  IO.eprintln s!"kernel-level-sharing: {failed} cases failed"
  return 1

end Tests.LevelSharing
