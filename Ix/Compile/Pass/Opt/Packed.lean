/- # The proof-justified passes: shared data (packed images, the collapse renaming, the site guard)

## Contract
Input: a changed block with a collapsed class (Pass 1: some class of two or
more members), whose recursor images are **packed** (design document §4.2
step 3): `img(r) = λ ps ms mins is t. unwrap_p (ρ.{ℓ} ps M⃗ N⃗ is t)` with `ρ`
the Ix recursor of the major's slot, each Ix motive `M_k` built from the
Lean motives of slot `k`'s class (`m_i` single, `λ ys. m_i ys ×' True`
lifted, `λ ys. m_{i₁} ys ×' … ×' m_{i_n} ys` a tuple, Lean order inside the
class) and `ℓ = max 1 u` when some slot is a tuple (`u` otherwise).

Output, for the passes O7–O12 (no term is rewritten here):
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
* `pjAllowed`: the site guard every proof-justified pass applies last.

## Faithfulness
Nothing is rewritten here. The facts the passes use: the image computes as
Lean's recursor (its rules hold by `rfl`, `pass3` suite); `unwrap_p` is a
primitive projection of a `PProd`/`And` (§4.2 step 3).

**Where a proof-justified rewrite goes (decision 5, D1).** A
proof-justified pass replaces a subterm `e` of a definition `c` by a term
`e′` with `e = e′` provable but not convertible. The Lean name `c` keeps
its faithful, convertible form (the baseline: the image path's term), so
every caller of `c`, including one whose type-check unfolds `c` to Lean's
shape, checks as before. The rewritten value is stored under the reserved
name `c._ix` (`ixFormName`, with `c`'s type), and `c` is recorded in the
switch-on non-canonical set with the pass as its cause. A caller that wants
the canonical form refers to `c._ix` itself (callers adapt, never the
callee). Nothing renames references automatically: a canonical constant
refers to its dependencies by their Lean names, so it stays well typed (a
raw renaming `d ↦ d._ix` is not conversion-preserving). No pass reads a constant's dependents, the
environment beyond the closure, or the schedule.

## Canonicity
The renaming, the slot classes and `ρ` depend on Pass 1's classes and the
image (canonical data); the guard depends on the occurrence's position
only.

## Side condition and fallback
A reading that fails (no `ρ` at the head under the projections, a variable
out of place, a level count that is neither Lean's nor Lean's plus one at
`0`) makes the pass decline; no `_ix` form is emitted for that occurrence,
which keeps its baseline (§0.1).

## Non-canonical set and evidence
The Lean name of every constant with an `_ix` form is non-canonical with the
pass as its cause (`Tests/Ix/Compile/NonCanonical.lean`,
`nonCanonicalPasses`). Evidence: the per-pass fixtures `O7Collapse`,
`O8Cases`, `O9Split`, `O10O12Collapse`, `O11bNoConfusion`.
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

/-- The site guard of every proof-justified pass, applied last: the
occurrence is in the value of a canonical `_ix` constant (`Occ.site`,
`Translate.RwState.site`), never under a Lean name (decision 5, D1: the Lean
name keeps the faithful form). Nothing about the constant's dependents, the
environment or the schedule is read. -/
def pjAllowed (o : Occ) : Bool := o.site.isSome

end Ix.Compile.Pass.Opt

end
