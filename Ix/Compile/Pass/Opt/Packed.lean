/- # The proof-justified passes: shared data (packed images, the collapse renaming, the dependents rule)

## Contract
Input: a changed block with a collapsed class (Pass 1: some class of two or
more members), whose recursor images are **packed** (design document §4.2
step 3): `img(r) = λ ps ms mins is t. unwrap_p (ρ.{ℓ} ps M⃗ N⃗ is t)` with `ρ`
the Ix recursor of the major's slot, each Ix motive `M_k` built from the
Lean motives of slot `k`'s class (`m_i` single, `λ ys. m_i ys ×' True`
lifted, `λ ys. m_{i₁} ys ×' … ×' m_{i_n} ys` a tuple, Lean order inside the
class) and `ℓ = max 1 u` when some slot is a tuple (`u` otherwise).

Output, for the passes O7 and O8 (no term is rewritten here):
* `readPacked`: `ρ`, its universe arguments and the **slot classes** (which
  Lean motives Ix slot `k` packs), read off the image, so the
  correspondence is the image generator's (by motive type, §4.2 step 1);
* `collapseRenaming`: the name map of the collapse on the block's own
  names, every member to its class's first member and its constructors to
  that member's constructors by position (members of one class are
  structurally equal, constructors included, Def 2.2), which is what
  compilation does to them: one class is one Ix inductive, so two
  arguments that agree under the renaming compile to the same bytes
  ("identical after compilation", the side condition of O7);
* `singleLevels`: the universe arguments of `ρ` (and of its `casesOn`,
  `recOn`) at Lean's motive universe `u` instead of the packing's `ℓ`;
* `pjAllowed`: the guard every proof-justified pass applies last (below).

## Faithfulness
Nothing is rewritten here. The facts the passes use: the image computes as
Lean's recursor (its rules hold by `rfl`, `pass3` suite); `unwrap_p` is a
primitive projection of a `PProd`/`And` (§4.2 step 3).

**The dependents rule (design document §1.4, order constraint 4).** A
proof-justified rewrite replaces a subterm `e` of a definition `c` by a term
`e′` with `e = e′` provable but not convertible. `c`'s own value keeps its
type (`e` and `e′` have the same type, the Lean motive at the major), and
closed computations with `c` still reduce (both sides agree by ι on every
constructor-headed argument), so `rfl` and `decide` on closed values still
hold. What can fail is a *dependent* `d` whose type-check unfolds `c` at an
open argument and compares the result with Lean's shape of `e`: such a `d`
mentions that shape, i.e. one of the changed block's image-kind auxiliaries
(`rec`, `recOn`, `casesOn`, `below`, `brecOn`, `.go`, `.eq`). The rule the
passes implement, the conservative choice the design document leaves open
(flagged for the owner in the A6p report):

> rewrite `c` only when no constant outside `c`'s block references both `c`
> and an image-kind auxiliary of the changed block being rewritten;
> otherwise keep the faithful image (**demotion**).

Two kinds of dependent are not counted, because Lean builds them so that
they check against either value (`isCarriedDependent`, as the clique side
carries equation lemmas): Lean's `T.noConfusion` over `T.noConfusionType`,
and the equation compiler's outputs over a matcher (`f`, `q._f`,
`q._sunfold`, `q._unsafe_rec`).

A dependent that unfolds `c` without mentioning the block's auxiliaries
compares `c` with itself or with other rewritten constants (each side is
rewritten consistently) or with closed values. The rule only decides
totality, never soundness: a missed dependent fails the kernels on its own
constant (a compile-time or check-time rejection, never an unsound
acceptance; old plan §3.5 requirement 2), and the `pass3` suite checks every
fixture constant, every dependent included, with the three kernels.

The rule is also why the passes fire only in the value of a definition
(`Translate.RwState.site`): a type, or a theorem's proof, is checked against
statements that may unfold `e`, and opaque constants and theorems are never
unfolded, so nothing is gained there.

## Canonicity
The renaming, the slot classes and `ρ` depend on Pass 1's classes and the
image (canonical data); the guard depends on the input's reference graph
(`CompileEnv.p3BlockRefs`): a constant outside `c`'s closure can demote `c`,
which a closure compile of `c` alone does not see (the same dependence as the
clique side's demotion; A7, determinism, open).

## Side condition and fallback
A reading that fails (no `ρ` at the head under the projections, a variable
out of place, a level count that is neither Lean's nor Lean's plus one at
`0`) makes the pass decline; the occurrence keeps its baseline, the faithful
image (§0.1).

## Non-canonical set and evidence
A demoted constant keeps its baseline and is recorded with the cause
`DEMOTED` (`Tests/Ix/Compile/NonCanonical.lean`, `nonCanonicalPasses`).
Evidence: the per-pass fixtures `O7Collapse`, `O8Cases`.
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Image.Expr
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Canon (getAppFnArgs replaceConstNames substLevel)

/-- Strip the projections (and metadata) around a packed image's
application (`unwrap`, §4.2 step 5). -/
def stripProjs : Expr → Expr
  | .proj _ _ s _ => stripProjs s
  | .mdata _ s _ => stripProjs s
  | e => e

/-- The telescope positions of the loose variables of `e` (variables of a
λ-telescope of `arity` binders whose body is `e`), in first-occurrence
order. -/
def telescopeVars (arity : Nat) (e : Expr) : Array Nat := go e 0 #[]
where
  go : Expr → Nat → Array Nat → Array Nat
    | .bvar i _, d, acc =>
      if i ≥ d && i - d < arity then
        let p := arity - 1 - (i - d)
        if acc.contains p then acc else acc.push p
      else acc
    | .app f a _, d, acc => go a d (go f d acc)
    | .lam _ t b _ _, d, acc | .forallE _ t b _ _, d, acc => go b (d + 1) (go t d acc)
    | .letE _ t v b _ _, d, acc => go b (d + 1) (go v d (go t d acc))
    | .proj _ _ s _, d, acc | .mdata _ s _, d, acc => go s d acc
    | _, _, acc => acc

/-- The packed shape of an image (see the module docstring). -/
structure PackedShape where
  leanRec : Name
  levelParams : Array Name
  np : Nat
  nm : Nat
  nmin : Nat
  ni : Nat
  /-- The Ix recursor of the major's slot. -/
  ixRec : Name
  /-- Its universe arguments in the image, over `levelParams`. -/
  ixLevels : Array Level
  /-- Ix slot `k` packs Lean motives `slots[k]` (Lean order). -/
  slots : Array (Array Nat)
  /-- The Ix recursor's minor count. -/
  ixMinors : Nat
  deriving Inhabited

def PackedShape.arity (s : PackedShape) : Nat := s.np + s.nm + s.nmin + s.ni + 1

/-- Read a packed image: `ρ` under the projections, the parameters, indices
and major in place, and the Lean motives each Ix motive packs. -/
def readPacked (leanRec : Name) (levelParams : Array Name) (np nm nmin ni : Nat) (value : Expr)
    (ixRecInfo : Name → Option RecursorVal) : Option PackedShape := do
  let arity := np + nm + nmin + ni + 1
  let body ← stripLams arity value
  let (h, args) := getAppFnArgs (stripProjs body)
  let .const ρ ls _ := h | none
  let iv ← ixRecInfo ρ
  if iv.numParams != np || iv.numIndices != ni then none
  if args.size != np + iv.numMotives + iv.numMinors + ni + 1 then none
  let pos? := fun (e : Expr) => match e with
    | .bvar k _ => if k < arity then some (arity - 1 - k) else none
    | _ => none
  for i in [0:np] do
    if pos? args[i]! != some i then none
  for i in [0:ni + 1] do
    if pos? args[np + iv.numMotives + iv.numMinors + i]! != some (np + nm + nmin + i) then none
  let mut slots : Array (Array Nat) := #[]
  for k in [0:iv.numMotives] do
    let vs := (telescopeVars arity args[np + k]!).filterMap fun p =>
      if np ≤ p && p < np + nm then some (p - np) else none
    if vs.isEmpty then none
    slots := slots.push vs
  return { leanRec, levelParams, np, nm, nmin, ni, ixRec := ρ, ixLevels := ls, slots,
           ixMinors := iv.numMinors }

/-- The packed shape of the image of Lean recursor `r` of block `b`. -/
def OptBlock.packed? (env : OptEnv) (b : OptBlock) (r : Name) : Option PackedShape := do
  let (lps, img) ← b.images.get? r
  let some (.recInfo rv) := env.const? r | none
  readPacked r lps rv.numParams rv.numMotives rv.numMinors rv.numIndices img b.ixRecs.get?

/-- The collapse renaming of block `b` (see the module docstring). -/
def collapseRenaming (env : OptEnv) (b : OptBlock) : Std.HashMap Name Name := Id.run do
  let mut m : Std.HashMap Name Name := {}
  for x in b.all do
    let some cls := b.classOf.get? x | continue
    let some rep := cls[0]? | continue
    if rep == x then continue
    m := m.insert x rep
    match env.const? x, env.const? rep with
    | some (.inductInfo ix), some (.inductInfo ir) =>
      for (c, c') in ix.ctors.zip ir.ctors do m := m.insert c c'
    | _, _ => pure ()
  return m

/-- Two arguments agree after compilation: α-equal (binder names and binder
info are metadata) once the collapse renaming is applied. -/
def agreeAfterCompile (ren : Std.HashMap Name Name) (a b : Expr) : Bool :=
  Ix.Compile.Image.alphaEq (replaceConstNames ren a) (replaceConstNames ren b)

/-- The universe arguments of `ρ` (and of its `casesOn`, `recOn`) at the
occurrence's levels `us`, with Lean's motive universe in place of the
packing's `ℓ` (`max 1 u`): Lean's recursor has an elimination universe
(its first parameter) exactly when `ρ` has one, unless a Prop member gained
large elimination, where the image already instantiates `ρ` at `0`. -/
def singleLevels (env : OptEnv) (s : PackedShape) (us : Array Level) : Option (Array Level) := do
  let some (.recInfo rv) := env.const? s.leanRec | none
  let x ← rv.all[0]?
  let some (.inductInfo iv) := env.const? x | none
  let leanElim := rv.cnst.levelParams.size > iv.cnst.levelParams.size
  let ls ← if s.ixLevels.size == s.levelParams.size then
      if leanElim then
        let u ← s.levelParams[0]?
        some (s.ixLevels.set! 0 (Level.mkParam u))
      else some s.ixLevels
    else if s.ixLevels.size == s.levelParams.size + 1 then
      match s.ixLevels[0]? with
      | some (Level.zero _) => some s.ixLevels
      | _ => none
    else none
  return ls.map (substLevel s.levelParams us)

/-- The last string component of a name. -/
def lastComponent : Name → String
  | .str _ s _ => s
  | _ => ""

/-- Dependents the rule does not count, because Lean builds them in a way that
type-checks against either value of the constant:
* Lean's `T.noConfusion` over `T.noConfusionType`: its value (`Eq.ndrec`
  over `T.casesOn (motive := λ t. T.noConfusionType P t t) t ms`)
  instantiates `T.noConfusionType` generically in both motives, where no
  unfolding happens, and at constructor applications in the minors'
  expected types, where Lean's value and the rewritten one both reduce (ι)
  to the same type;
* the equation compiler's outputs over a matcher `p.match_k`: the function
  `p` itself and any structural handler `q._f`, smart unfolding `q._sunfold`
  or `q._unsafe_rec` (Lean shares a matcher between functions with the same
  patterns, so `q` need not be `p`): each applies the matcher to a motive,
  discriminants and alternatives, whose typing reads the matcher's type,
  never its value.
(As the clique side carries the members' equation lemmas.) -/
def isCarriedDependent (c d : Name) : Bool :=
  match c with
  | .str p "noConfusionType" _ => d == Name.mkStr p "noConfusion"
  | .str p m _ =>
    m.startsWith "match_" &&
      (d == p || ["_f", "_sunfold", "_unsafe_rec"].contains (lastComponent d))
  | _ => false

/-- The dependents rule over the input's block reference graph (`refs`:
block key ↦ the names its members reference outside the block) and the
image-kind heads of the changed blocks (`heads`: head ↦ block key): the first
block (by key) that references the definition `c` and a head of the changed
block `key`. Only `key`'s heads are consulted: they are registered before
`c`'s block compiles (`c` references one of them), so the answer does not
depend on the schedule. Evaluated only when a proof-justified pass's own
side condition holds (`pjAllowed` is its last check). -/
def demotionIn (refs : Std.HashMap Name (Std.HashSet Name)) (heads : Std.HashMap Name Name)
    (c key : Name) : Option String := Id.run do
  let mut found : Option Name := none
  for (lo, rs) in refs do
    if !rs.contains c then continue
    if isCarriedDependent c lo then continue
    if !rs.toList.any fun h => heads.get? h == some key then continue
    found := match found with
      | some f => if lo.pretty < f.pretty then some lo else some f
      | none => some lo
  return found.map fun d => s!"dependent {d.pretty} references {c.pretty} and an auxiliary of the block of {key.pretty}"

/-- The guard of every proof-justified pass, applied last: the occurrence is
in the value of a definition (`Occ.site`) that no dependent demotes (the
dependents rule, module docstring). -/
def pjAllowed (env : OptEnv) (b : OptBlock) (o : Occ) : Bool :=
  match o.site, b.all[0]? with
  | some c, some key => (env.demotion c key).isNone
  | _, _ => false

end Ix.Compile.Pass.Opt

end
