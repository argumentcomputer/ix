module

public import ConLeche.Kernel.Expr

@[expose] public section

/-!
# Level operations

Implementation of universe level comparison, following the official kernel /
nanoda (`level.rs` there): `simplify` normalizes, `leqCore` decides
`eval l ≤ eval r + diff` with the same case order as nanoda's `leq_core`
(so reduction happens the same way), and antisymmetry gives equivalence.

`leqCore`'s termination argument is nontrivial (the `imax` by-cases rule
substitutes into both sides), so it takes fuel.  Running out of fuel — or
hitting a case that is unreachable for simplified input — is reported as
`none`, which callers must treat as an internal error, never as a verdict.

Soundness of all of this (w.r.t. evaluation of levels into `Nat`) is proved
in `ConLeche.Verify.Level`.
-/

namespace ConLeche.Level

/-- Substitute level parameters: `subst ks vs l` replaces `param k` by the
corresponding `v`.  Unlisted parameters remain. -/
def subst (ks : List Name) (vs : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (subst ks vs l)
  | .max l r => .max (subst ks vs l) (subst ks vs r)
  | .imax l r => .imax (subst ks vs l) (subst ks vs r)
  | .param n => go ks vs n
where
  go : List Name → List Level → Name → Level
  | k :: ks, v :: vs, n => if k = n then v else go ks vs n
  | _, _, n => .param n

/-- Are all parameters of `l` among `params`? -/
def allParamsDefined (params : List Name) : Level → Bool
  | .zero => true
  | .succ l => allParamsDefined params l
  | .max l r | .imax l r => allParamsDefined params l && allParamsDefined params r
  | .param n => params.contains n

/-- Is this level provably nonzero at every parameter assignment
(official kernel `is_never_zero`)?  Syntactic and incomplete, exactly
as the reference: `succ` is, `max` if either side is, `imax` if the
right side is; `zero` and `param` are not. -/
def isNeverZero : Level → Bool
  | .zero => false
  | .param _ => false
  | .succ _ => true
  | .max l r => isNeverZero l || isNeverZero r
  | .imax _ r => isNeverZero r

/-- `max` of two simplified levels, pulling out common `succ`s. -/
def combining : Level → Level → Level
  | .zero, r => r
  | l, .zero => l
  | .succ l, .succ r => .succ (combining l r)
  | l, r => .max l r

/-- Normalize a level: resolve `max`/`imax` where possible. -/
def simplify : Level → Level
  | .zero => .zero
  | .param n => .param n
  | .succ l => .succ (simplify l)
  | .max l r => combining (simplify l) (simplify r)
  | .imax l r =>
    let ls := simplify l
    let rs := simplify r
    if ls = .zero || ls = .succ .zero then rs
    else match rs with
      | .zero => .zero
      | .succ _ => combining ls rs
      | _ => .imax ls rs

mutual

/-- Decide `eval l ≤ eval r + diff` for simplified `l`, `r`. -/
def leqCore (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if l = .zero ∧ diff ≥ 0 then some true
    else if r = .zero ∧ diff < 0 then some false
    else rest fuel l r diff

/-- The cases after the cheap `zero` short-cuts, in nanoda's order. -/
def rest (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .param a, .param x => some (a = x && diff ≥ 0)
  | .param _, .zero => some false
  | .zero, .param _ => some (diff ≥ 0)
  | .succ s, _ => leqCore fuel s r (diff - 1)
  | _, .succ s => leqCore fuel l s (diff + 1)
  | .max a b, _ => do
    if ← leqCore fuel a r diff then leqCore fuel b r diff else pure false
  | .param _, .max x y => do
    if ← leqCore fuel l x diff then pure true else leqCore fuel l y diff
  | .zero, .max x y => do
    if ← leqCore fuel l x diff then pure true else leqCore fuel l y diff
  | _, _ =>
    match l, r with
    | .imax a b, .imax x y =>
      if a = x && b = y && diff ≥ 0 then some true else imaxRules fuel l r diff
    | _, _ => imaxRules fuel l r diff

/-- The `imax` rules (nanoda's cases 10–15): case-split on a parameter, or
distribute a nested `max`/`imax` on the right of an `imax`. -/
def imaxRules (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .imax _ (.param p), _ => byCases fuel p l r diff
  | _, .imax _ (.param p) => byCases fuel p l r diff
  | .imax a (.imax x y), _ => leqCore fuel (.max (.imax a y) (.imax x y)) r diff
  | .imax a (.max x y), _ => leqCore fuel (simplify (.max (.imax a x) (.imax a y))) r diff
  | _, .imax x (.imax j k) => leqCore fuel l (.max (.imax x k) (.imax j k)) diff
  | _, .imax x (.max j k) => leqCore fuel l (simplify (.max (.imax x j) (.imax x k))) diff
  | _, _ => none  -- unreachable for simplified input; an internal error

/-- Split on the parameter `p` being zero or positive. -/
def byCases (fuel : Nat) (p : Name) (l r : Level) (diff : Int) : Option Bool := do
  let l0 := simplify (subst [p] [.zero] l)
  let r0 := simplify (subst [p] [.zero] r)
  if ← leqCore fuel l0 r0 diff then
    let ls := simplify (subst [p] [.succ (.param p)] l)
    let rs := simplify (subst [p] [.succ (.param p)] r)
    leqCore fuel ls rs diff
  else pure false

end

/-- A generous fuel bound for `leqCore`; exceeded only by pathological input
(then reported as an internal error, not a verdict). -/
def defaultFuel : Nat := 10000

/-- Decide `l ≤ r` semantically; `none` is an internal error. -/
def leq (l r : Level) : Option Bool :=
  leqCore defaultFuel (simplify l) (simplify r) 0

/-- Decide semantic equality of two levels; `none` is an internal error.
Syntactic equality decides directly — first on the levels themselves
(`l == r`, which is pointer- and hash-first, task #176 P2), then on
their simplified forms (the reference kernels' fast path); otherwise
antisymmetric `leq`, short-circuited.

**Conformance note (restrictions-are-findings, task #176 P2).**  The
first disjunct is what official's `is_equivalent` does and con-leche did
not: `bool is_equivalent(level const & lhs, level const & rhs) {
return lhs == rhs || normalize(lhs) == normalize(rhs); }`
(`level.cpp:518`).  It is *provably redundant* here — `l = r` implies
`simplify l = simplify r` — so the alignment is verdict-neutral by
construction, not merely accept-superset: `isEquiv_eq_withoutPtr` and
`isEquiv_of_beq` (`Verify/Level.lean`) pin both directions.  What it
buys is speed: `simplify` allocates, `l == r` on a shared level is one
pointer compare. -/
def isEquiv (l r : Level) : Option Bool := do
  if l == r then pure true
  else if simplify l = simplify r then pure true
  else if ← leq l r then leq r l else pure false

/-- Decide pointwise semantic equality of two level lists (`false` on length
mismatch). -/
def isEquivList : List Level → List Level → Option Bool
  | [], [] => some true
  | l :: ls, r :: rs => do
    if ← isEquiv l r then isEquivList ls rs else pure false
  | _, _ => some false

/-- Is this level syntactically `zero` after simplification?  (Sound but
incomplete zero test; matches what the checker needs.) -/
def isZero (l : Level) : Bool := simplify l = .zero

/-- Certainly nonzero under *every* level assignment (`succ`-headed
somewhere along every `max`, and along the `imax` right spine).
Conservative: `false` does not mean "can be zero". -/
def isNonZero : Level → Bool
  | .zero => false
  | .succ _ => true
  | .max a b => a.isNonZero || b.isNonZero
  | .imax _ b => b.isNonZero
  | .param _ => false

/-- The zero-ness datum of a level (task #161): the exact reading of
`{φ | eval φ l = 0}`.  `ConLeche.Verify.PropWhen` proves
`(zeronessOf l).holds φ = (eval φ l == 0)`.  Case notes: a `max` is
zero iff both sides are (`inter`); an `imax` is zero iff its right
side is (`eval (imax a b) = if eval b = 0 then 0 else max …`). -/
def zeronessOf : Level → PropWhen
  | .zero => .ifAllZero []
  | .succ _ => .never
  | .param n => .ifAllZero [n]
  | .max a b => (zeronessOf a).inter (zeronessOf b)
  | .imax _ b => zeronessOf b

/-- Push a level-parameter substitution through a zero-ness datum
(task #161): each parameter becomes its replacement's datum,
intersected — `Z(subst ks vs l)` is exactly
`substPW ks vs (zeronessOf l)` (`Verify.PropWhen.zeronessOf_subst`).
Canonical on output (`PropWhen.bindZ`, task #194): an unlisted
parameter reproduces `ifAllZero [n]`, so instantiating a declaration
at its own parameters is the identity here too (`substPW_self`) —
unconditionally, because every datum is canonical by construction. -/
def substPW (ks : List Name) (vs : List Level) (pw : PropWhen) :
    PropWhen :=
  pw.bindZ fun n => zeronessOf (subst.go ks vs n)

end ConLeche.Level

namespace ConLeche

/-- No duplicates in a list of names. -/
def Name.nodup : List Name → Bool
  | [] => true
  | n :: ns => !ns.contains n && Name.nodup ns

/-- Is this a `_model`-suffixed name (the shape of model companions)? -/
def Name.isModelSuffix : Name → Bool
  | .str _ "_model" => true
  | _ => false

/-- Is this shaped like an installed projection function's name
(`(T.proj).i`, the modeled path's projection functions) or a
projection table's (`(T.projTable).0`, task #175 S1)?  Both shapes
are reserved for the checker's own installs. -/
def Name.isProjFnShape : Name → Bool
  | .num (.str _ "proj") _ => true
  | .num (.str _ "projTable") _ => true
  | _ => false

/-- Substitute level parameters throughout an expression (sorts and
constant level arguments). -/
def Expr.instantiateLevelParams (ks : List Name) (us : List Level) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty => .fvar idx (ty.instantiateLevelParams ks us)
  | .sort u => .sort (Level.subst ks us u)
  | .const n vs => .const n (vs.map (Level.subst ks us))
  | .app f a => .app (f.instantiateLevelParams ks us) (a.instantiateLevelParams ks us)
  | .lam ty body m =>
    .lam (ty.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
      ⟨Level.substPW ks us m.pw⟩
  | .forallE ty body m =>
    .forallE (ty.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
      ⟨Level.substPW ks us m.pw⟩
  | .letE ty val body => .letE (ty.instantiateLevelParams ks us)
      (val.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
  | .lit l => .lit l
  | .proj s i e => .proj s i (e.instantiateLevelParams ks us)

/-- Are all level parameters occurring in `e` among `params`?  Binder
prop-ness data included (task #161): their parameters are level
parameters of the term — `instantiateLevelParams` substitutes into
them, and its composition law needs them covered exactly as it needs
the levels'. -/
def Expr.allLevelParamsDefined (params : List Name) : Expr → Bool
  | .bvar _ => true
  | .fvar _ t => t.allLevelParamsDefined params
  | .sort u => u.allParamsDefined params
  | .const _ us => us.all (Level.allParamsDefined params)
  | .app f a => f.allLevelParamsDefined params && a.allLevelParamsDefined params
  | .lam t b m | .forallE t b m =>
    t.allLevelParamsDefined params && b.allLevelParamsDefined params
      && m.pw.paramsDefined params
  | .letE t v b => t.allLevelParamsDefined params && v.allLevelParamsDefined params
      && b.allLevelParamsDefined params
  | .lit _ => true
  | .proj _ _ e => e.allLevelParamsDefined params

/-! ### `allLevelParamsDefined`, memoized (task #210 Part B)

The recursor-generation checks ask it of the recursor's type and of
every rule body; a tree walk does not finish on a DAG-shared field
type (task #215's `tower_struct`).  Swapped in by `@[csimp]` (the
arrangement of `ConLeche/Kernel/ExprOps.lean`): kernel-checked, no
trust point, the pure walk stays the spec.  Keyed by the node, dropped
after each call (the answer depends on `params`). -/

/-- The memo's invariant: every recorded answer is the real one. -/
def LPMemoInv (params : List Name) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (r : Bool), memo[k]? = some r → r = k.allLevelParamsDefined params

theorem LPMemoInv.empty {params : List Name} : LPMemoInv params {} := by
  intro k r h; simp at h

theorem LPMemoInv.insert {params : List Name} {memo : Std.HashMap Expr Bool}
    (hm : LPMemoInv params memo) {e : Expr} {r : Bool}
    (heq : r = e.allLevelParamsDefined params) :
    LPMemoInv params (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `allLevelParamsDefined`. -/
def Expr.allLevelParamsDefinedGo (params : List Name) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (true, memo)
  | .sort u => (u.allParamsDefined params, memo)
  | .const _ us => (us.all (Level.allParamsDefined params), memo)
  | .lit _ => (true, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ t => allLevelParamsDefinedGo params memo t
        | .app f a =>
          let (b₁, memo) := allLevelParamsDefinedGo params memo f
          let (b₂, memo) := allLevelParamsDefinedGo params memo a
          (b₁ && b₂, memo)
        | .lam t b m =>
          let (b₁, memo) := allLevelParamsDefinedGo params memo t
          let (b₂, memo) := allLevelParamsDefinedGo params memo b
          (b₁ && b₂ && m.pw.paramsDefined params, memo)
        | .forallE t b m =>
          let (b₁, memo) := allLevelParamsDefinedGo params memo t
          let (b₂, memo) := allLevelParamsDefinedGo params memo b
          (b₁ && b₂ && m.pw.paramsDefined params, memo)
        | .letE t v b =>
          let (b₁, memo) := allLevelParamsDefinedGo params memo t
          let (b₂, memo) := allLevelParamsDefinedGo params memo v
          let (b₃, memo) := allLevelParamsDefinedGo params memo b
          (b₁ && b₂ && b₃, memo)
        | .proj _ _ sub => allLevelParamsDefinedGo params memo sub
        | e => (e.allLevelParamsDefined params, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `allLevelParamsDefined`.** -/
theorem Expr.allLevelParamsDefinedGo_spec {params : List Name} :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), LPMemoInv params memo →
      (allLevelParamsDefinedGo params memo e).1 = e.allLevelParamsDefined params ∧
        LPMemoInv params (allLevelParamsDefinedGo params memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [allLevelParamsDefinedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [allLevelParamsDefined, h1], ?_⟩
      exact h2.insert (by simp [allLevelParamsDefined, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [allLevelParamsDefined, h1, h3], ?_⟩
      exact h4.insert (by simp [allLevelParamsDefined, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [allLevelParamsDefined, h1, h3], ?_⟩
      exact h4.insert (by simp [allLevelParamsDefined, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [allLevelParamsDefined, h1, h3], ?_⟩
      exact h4.insert (by simp [allLevelParamsDefined, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [allLevelParamsDefined, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [allLevelParamsDefined, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [allLevelParamsDefinedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [allLevelParamsDefined, h1], ?_⟩
      exact h2.insert (by simp [allLevelParamsDefined, h1])

/-- The executed `allLevelParamsDefined` (one memoized DAG walk). -/
def Expr.allLevelParamsDefinedFast (params : List Name) (e : Expr) : Bool :=
  (allLevelParamsDefinedGo params {} e).1

@[csimp] theorem Expr.allLevelParamsDefined_eq_allLevelParamsDefinedFast :
    @Expr.allLevelParamsDefined = @Expr.allLevelParamsDefinedFast := by
  funext params e
  exact (allLevelParamsDefinedGo_spec e {} LPMemoInv.empty).1.symm

end ConLeche
