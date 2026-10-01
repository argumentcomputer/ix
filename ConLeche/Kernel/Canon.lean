module

public import ConLeche.Kernel.Env

@[expose] public section

/-!
# The level-parameter canonical form the pinned blocks are matched up to

A stream's `Nat` block and the checker's pinned one are the same
declaration when they agree up to the names Lean's exporter picks
freely: binder names, binder annotations and level-parameter names.
This module is that canonical form and the lockstep comparisons built
on it.

It sits in the KERNEL because the matching does (task #293): the
decoder emits the file's records and nothing else, and it is
`checkDecl` that recognises a block as one of the five pinned basis
blocks, and a `#QUOT` record (or the `Quot.sound` axiom record) as the
pinned quotient package's.  Until then this lived in
`ConLeche/Frontend/Export.lean`, beside the parser that did the
matching.
-/

namespace ConLeche

/-- Rename level parameters (for basis-block matching up to
level-parameter names). -/
def canonLevel (m : Name → Name) : Level → Level
  | .zero => .zero
  | .succ u => .succ (canonLevel m u)
  | .max u v => .max (canonLevel m u) (canonLevel m v)
  | .imax u v => .imax (canonLevel m u) (canonLevel m v)
  | .param n => .param (m n)

/-- Erase binder names *and binder annotations* and rename level
parameters: the alpha/renaming canonical form used to match a parsed
inductive block against a pinned basis block (Lean's exports use
auto-bound universe names and hygienic binder names, both semantically
irrelevant).

Task #142, pin-side normalization: the parser already maps every
stream binder to `.default`, and both sides of every
`ConstantInfo.canon` comparison go through here, so erasing the
annotation here is what kept the two sides consistent while the pinned
literals still carried the real `BinderInfo`s of their `Init.Prelude`
signatures.  Since task #203 the pin builder
(`ConLeche/Kernel/Basis/Builder.lean`) emits `.anonymous` at `.default`
and the parser emits `.anonymous` too, so the name/annotation erasure
here is the identity on both sides; what this canonical form still
*does* is rename level parameters and reset `pw` (the pin side is
annotated, the stream side is at the parse placeholder). -/
def canonExpr (m : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty => .fvar idx (canonExpr m ty)
  | .sort u => .sort (canonLevel m u)
  | .const n us => .const n (us.map (canonLevel m))
  | .app f a => .app (canonExpr m f) (canonExpr m a)
  | .lam ty b _ => .lam (canonExpr m ty) (canonExpr m b) ⟨.never⟩
  | .forallE ty b _ =>
      .forallE (canonExpr m ty) (canonExpr m b) ⟨.never⟩
  | .letE ty v b => .letE (canonExpr m ty) (canonExpr m v)
      (canonExpr m b)
  | .lit l => .lit l
  | .proj s i e => .proj s i (canonExpr m e)

/-- The level-parameter renaming a constant's own parameter list
induces: the `i`-th parameter becomes `⟨i⟩`, anything else is left
alone. -/
def canonNameMap (ps : List Name) : Name → Name := fun n =>
  match ps.findIdx? (fun p => p == n) with
  | some i => .num .anonymous i
  | none => n

/-- Canonical form of a constant's common data (name kept, level
parameters numbered, type renamed). -/
def ConstantVal.canon (cv : ConstantVal) : ConstantVal :=
  { cv with
    levelParams := (List.range cv.levelParams.length).map (.num .anonymous ·),
    type := canonExpr (canonNameMap cv.levelParams) cv.type }

/-- Canonical form of a stored constant for basis matching. -/
def ConstantInfo.canon (ci : ConstantInfo) : ConstantInfo :=
  let ps := ci.toConstantVal.levelParams
  let m : Name → Name := canonNameMap ps
  let cv : ConstantVal := ConstantVal.canon ci.toConstantVal
  match ci with
  | .axiomInfo _ => .axiomInfo cv
  | .defnInfo _ v hint => .defnInfo cv (canonExpr m v) hint
  | .thmInfo _ v => .thmInfo cv (canonExpr m v)
  | .indInfo _ _ => .indInfo cv {}
  | .ctorInfo _ nP nF => .ctorInfo cv nP nF
  | .recInfo _ mI rP rules => .recInfo cv mI rP
      (rules.map fun r => { r with rhs := canonExpr m r.rhs })
  -- table entries never occur in parsed input; identity keeps the
  -- match total
  | .projInfo e => .projInfo e

/-! ### Comparing canonical forms in lockstep (task #226)

Two places ask "is this record the same declaration as that pinned
one, up to level-parameter names?" — the `Quot.sound` axiom record and
the four quotient records against the `quot` basis pin, and a block
against one of the five basis pins.  Both are `checkDecl`'s since task
#293 (`basisPinHit`, `quotPinHit`, `ConLeche/Kernel/Basis.lean`); a
third, the built-in prelude's dedupe, went with that task.  Each used
to build `ConstantInfo.canon` of BOTH sides and compare the results.
That is `O(tree)` on the stream side, because `canonExpr` rebuilds
every node: `tests/e2e/tower_axiom.ndjson` and `tower_quot.ndjson` — a
depth-60 shared tower (`2^60` nodes unshared) under `Quot.sound` and
under `Quot` — exhaust memory on it.

The `canonEq*` functions below are the SPECIFICATIONS, spelled exactly
that way; the `*Fast` twins beside them descend both terms **together**
and stop at the first disagreement, and are swapped in by `@[csimp]`.
Wherever the two sides agree they have the pin's shape, so the walk is
bounded by the PIN's tree size — a few dozen nodes — however large the
stream side; where they disagree it stops there.  Same verdict on
every input; only the work changes.

The **name pre-filter of task #215 stays in front** of the block
comparison: `canon` renames only level parameters, so a block can match
a pin only when its members' names are the pin's, member for member,
and that test is a handful of `Name` comparisons. -/

/-- Lockstep twin of `canonExpr m a == canonExpr m' b`
(`canonExprEqFast_iff`). -/
def canonExprEqFast (m m' : Name → Name) : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i t, .fvar j t' => i == j && canonExprEqFast m m' t t'
  | .sort u, .sort v => canonLevel m u == canonLevel m' v
  | .const n us, .const n' us' =>
      n == n' && us.map (canonLevel m) == us'.map (canonLevel m')
  | .app f a, .app f' a' =>
      canonExprEqFast m m' f f' && canonExprEqFast m m' a a'
  | .lam t b _, .lam t' b' _ =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' b b'
  | .forallE t b _, .forallE t' b' _ =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' b b'
  | .letE t v b, .letE t' v' b' =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' v v' &&
        canonExprEqFast m m' b b'
  | .lit l, .lit l' => l == l'
  | .proj s i e, .proj s' i' e' =>
      s == s' && i == i' && canonExprEqFast m m' e e'
  | _, _ => false

/-- **The agreement for expressions.**  `canonExpr` preserves every
node's constructor (it rewrites only levels, and resets the binder
metadata to the same constant on both sides), so the two canonical
forms are equal iff the originals agree constructor by constructor
down to their leaves — which is what the descent tests. -/
theorem canonExprEqFast_iff (m m' : Name → Name) :
    ∀ a b : Expr, canonExprEqFast m m' a b = true ↔ canonExpr m a = canonExpr m' b := by
  intro a
  induction a with
  | bvar i => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | fvar i t ih =>
    intro b; cases b <;> simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ih]
  | sort u => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | const n us => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | app f a ihf iha =>
    intro b; cases b <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ihf, iha]
  | lam t b m iht ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihb]
  | forallE t b m iht ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihv, ihb, and_assoc]
  | lit l => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | proj s i e ih =>
    intro b; cases b <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ih, and_assoc]

/-- The common data of a canonical form is the canonical form of the
common data: `ConstantInfo.canon` rebuilds `toConstantVal` the same
way in every arm but the table one, which is the identity (a table
never occurs in parsed input).  The quotient records — parsed
`axiomInfo`s, pinned `indInfo`/`ctorInfo`/`recInfo`/`axiomInfo`s — are
compared at this projection. -/
theorem ConstantInfo.canon_toConstantVal :
    ∀ {ci : ConstantInfo}, (∀ t, ci ≠ .projInfo t) →
      (ConstantInfo.canon ci).toConstantVal = ConstantVal.canon ci.toConstantVal := by
  intro ci h
  cases ci <;> first | rfl | exact absurd rfl (h _)

/-- A `Bool` identity from the `= true` equivalence. -/
private theorem boolEq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Two constants have the same canonical common data.  (`decide (· =
·)` is what `==` unfolds to at these `DecidableEq` types, so this is
the comparison the call sites used to spell inline.) -/
def ConstantVal.canonEq (cv cv' : ConstantVal) : Bool :=
  decide (ConstantVal.canon cv = ConstantVal.canon cv')

/-- `ConstantVal.canonEq` in lockstep.  The numbered level-parameter
lists are equal exactly when they are equally long. -/
def ConstantVal.canonEqFast (cv cv' : ConstantVal) : Bool :=
  cv.name == cv'.name && cv.levelParams.length == cv'.levelParams.length &&
    canonExprEqFast (canonNameMap cv.levelParams) (canonNameMap cv'.levelParams)
      cv.type cv'.type

theorem ConstantVal.canonEqFast_iff (cv cv' : ConstantVal) :
    ConstantVal.canonEqFast cv cv' = true ↔
      ConstantVal.canon cv = ConstantVal.canon cv' := by
  simp only [ConstantVal.canonEqFast, ConstantVal.canon, Bool.and_eq_true,
    beq_iff_eq, canonExprEqFast_iff, ConstantVal.mk.injEq, and_assoc]
  constructor
  · rintro ⟨hn, hl, ht⟩; exact ⟨hn, by rw [hl], ht⟩
  · rintro ⟨hn, hl, ht⟩
    exact ⟨hn, by simpa using congrArg List.length hl, ht⟩

@[csimp] theorem ConstantVal.canonEq_eq_canonEqFast :
    @ConstantVal.canonEq = @ConstantVal.canonEqFast := by
  funext cv cv'
  exact boolEq_of_iff (by
    simp only [ConstantVal.canonEq, decide_eq_true_eq, ConstantVal.canonEqFast_iff])

/-- Rule lists compared through the canonical form of each rule's
right-hand side (`ConstantInfo.canon`'s recursor arm). -/
def canonRulesEqFast (m m' : Name → Name) : List RecRule → List RecRule → Bool
  | [], [] => true
  | r :: rs, r' :: rs' =>
      ({ r with rhs := .bvar 0 } == { r' with rhs := .bvar 0 }) &&
        canonExprEqFast m m' r.rhs r'.rhs && canonRulesEqFast m m' rs rs'
  | _, _ => false

theorem canonRulesEqFast_iff (m m' : Name → Name) :
    ∀ rs rs' : List RecRule,
      canonRulesEqFast m m' rs rs' = true ↔
        rs.map (fun r => { r with rhs := canonExpr m r.rhs }) =
          rs'.map (fun r => { r with rhs := canonExpr m' r.rhs }) := by
  intro rs
  induction rs with
  | nil => intro rs'; cases rs' <;> simp [canonRulesEqFast]
  | cons r rs ih =>
    intro rs'; cases rs' with
    | nil => simp [canonRulesEqFast]
    | cons r' rs' =>
      cases r; cases r'
      simp only [canonRulesEqFast, Bool.and_eq_true, ih, List.map_cons,
        List.cons.injEq, beq_iff_eq, RecRule.mk.injEq, canonExprEqFast_iff]
      constructor <;> (intro h; simp_all)

/-- Two stored constants have the same canonical form. -/
def ConstantInfo.canonEq (ci ci' : ConstantInfo) : Bool :=
  decide (ConstantInfo.canon ci = ConstantInfo.canon ci')

/-- `ConstantInfo.canonEq` in lockstep. -/
def ConstantInfo.canonEqFast : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo cv, .axiomInfo cv' => ConstantVal.canonEqFast cv cv'
  | .defnInfo cv v h, .defnInfo cv' v' h' =>
      ConstantVal.canonEqFast cv cv' &&
        canonExprEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) v v' && h == h'
  | .thmInfo cv v, .thmInfo cv' v' =>
      ConstantVal.canonEqFast cv cv' &&
        canonExprEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) v v'
  | .indInfo cv _, .indInfo cv' _ => ConstantVal.canonEqFast cv cv'
  | .ctorInfo cv nP nF, .ctorInfo cv' nP' nF' =>
      ConstantVal.canonEqFast cv cv' && nP == nP' && nF == nF'
  | .recInfo cv mI rP rules, .recInfo cv' mI' rP' rules' =>
      ConstantVal.canonEqFast cv cv' && mI == mI' && rP == rP' &&
        canonRulesEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) rules rules'
  | .projInfo t, .projInfo t' => t == t'
  | _, _ => false

theorem ConstantInfo.canonEqFast_iff (ci ci' : ConstantInfo) :
    ConstantInfo.canonEqFast ci ci' = true ↔
      ConstantInfo.canon ci = ConstantInfo.canon ci' := by
  cases ci <;> cases ci' <;>
    simp [ConstantInfo.canonEqFast, ConstantInfo.canon, ConstantInfo.toConstantVal,
      Bool.and_eq_true, ConstantVal.canonEqFast_iff, canonExprEqFast_iff,
      canonRulesEqFast_iff, and_assoc]

@[csimp] theorem ConstantInfo.canonEq_eq_canonEqFast :
    @ConstantInfo.canonEq = @ConstantInfo.canonEqFast := by
  funext ci ci'
  exact boolEq_of_iff (by
    simp only [ConstantInfo.canonEq, decide_eq_true_eq, ConstantInfo.canonEqFast_iff])

/-- Two blocks are the same, member for member, up to the canonical
form. -/
def canonEqList (xs ys : List ConstantInfo) : Bool :=
  decide (xs.map ConstantInfo.canon = ys.map ConstantInfo.canon)

/-- `canonEqList` in lockstep. -/
def canonEqListFast : List ConstantInfo → List ConstantInfo → Bool
  | [], [] => true
  | x :: xs, y :: ys => ConstantInfo.canonEqFast x y && canonEqListFast xs ys
  | _, _ => false

theorem canonEqListFast_iff :
    ∀ xs ys : List ConstantInfo,
      canonEqListFast xs ys = true ↔
        xs.map ConstantInfo.canon = ys.map ConstantInfo.canon := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp [canonEqListFast]
  | cons x xs ih =>
    intro ys; cases ys with
    | nil => simp [canonEqListFast]
    | cons y ys =>
      simp [canonEqListFast, Bool.and_eq_true, ConstantInfo.canonEqFast_iff, ih]

@[csimp] theorem canonEqList_eq_canonEqListFast :
    @canonEqList = @canonEqListFast := by
  funext xs ys
  exact boolEq_of_iff (by
    simp only [canonEqList, decide_eq_true_eq, canonEqListFast_iff])

end ConLeche
