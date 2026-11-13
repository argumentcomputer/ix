module

public import IxCK.Kernel.Expr
public import IxCK.Kernel.LevelGeran

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
in `Ix.Kernel.Verify.Level`.
-/

namespace Ix.Kernel.Level

/-! ### Per-call memos on shared levels

The level functions are written as tree recursions, and a level the
kernel builds can be shared as a DAG whose tree is exponentially larger:
the ∀ rule builds `imax L (imax L' …)`, and unfolding a definition
instantiated at `max u u` puts one object at both sides of each `max`.
The executed forms of `isNeverZero`, `simplify`, `zeronessOf` and
`leqCore` (whose case split substitutes with the memoised `substMemo`)
remember, for one call, the result at every node (for `leqCore`, every
subproblem) they have finished, so a node reached again
is a lookup and a result is shared where its input was. A memo is a hash
map keyed by the level itself: the hash is the cached field and the
equality is `Level.beq`, a pointer test on a shared node
(`Level.beqPtr`). Its invariant is that every entry is the specified
function of its key (`MemoInv`, the arrangement of
`allLevelParamsDefinedGo` below). A level below a small tree size
(`sizeLeft`, `smallWalk`, `smallLeq`) runs instead through an exact copy
of the plain recursion (`…Plain`), so ordinary levels pay a bounded size
test and no map. Each executed form (`…Fast`) is proved equal to its
specification on both branches and substituted by `@[csimp]`; the
specifications are what every statement and rule reads. -/

/-- The invariant of a per-call memo of `f`: every entry is `f` of its key. -/
def MemoInv {β : Type} (f : Level → β) (m : Std.HashMap Level β) : Prop :=
  ∀ (k : Level) (v : β), m[k]? = some v → v = f k

theorem MemoInv.empty {β : Type} {f : Level → β} : MemoInv f {} := by
  intro k v h; simp at h

theorem MemoInv.insert {β : Type} {f : Level → β} {m : Std.HashMap Level β}
    (hm : MemoInv f m) {l : Level} {v : β} (hv : v = f l) : MemoInv f (m.insert l v) := by
  intro k v' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact hv
  · exact hm k v' hk

/-- `n` minus the tree size of `l` while that stays positive, else `0`: a
walk of at most `n` nodes that allocates nothing, with which the executed
forms below send a small level to the plain recursion (`smallWalk`,
`smallLeq`). Which branch runs never changes a result: both are proved
equal to the specification. -/
def sizeLeft : Nat → Level → Nat
  | 0, _ => 0
  | n + 1, .succ a => sizeLeft n a
  | n + 1, .max a b => sizeLeft (sizeLeft n a) b
  | n + 1, .imax a b => sizeLeft (sizeLeft n a) b
  | n + 1, _ => n

/-- Below this tree size a level walk runs as the plain recursion. -/
def smallWalk : Nat := 64

/-- Below this combined tree size of its operands `leqCore` runs as the
plain recursion (a bounded amount of work: the operands are small). -/
def smallLeq : Nat := 32

/-- The most subproblems one memoised `leqCore` call remembers. The memo is a
cache, so a full one changes no answer; the cap keeps its memory bounded on
the comparisons that stay exponential (the problem is coNP-hard,
`docs/kernel.md`, "Running time"), whose distinct subproblems grow as the
time does. -/
def leqMemoCap : Nat := 1048576

/-- Substitute level parameters: `subst ks vs l` replaces `param k` by the
corresponding `v`.  Unlisted parameters remain. -/
def subst (ks : List LevelParam) (vs : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (subst ks vs l)
  | .max l r => .max (subst ks vs l) (subst ks vs r)
  | .imax l r => .imax (subst ks vs l) (subst ks vs r)
  | .param n => go ks vs n
where
  go : List LevelParam → List Level → LevelParam → Level
  | k :: ks, v :: vs, n => if k = n then v else go ks vs n
  | _, _, n => .param n

/-- `subst ks vs`, memoised per call on the nodes it has substituted: a
level shared as a DAG is walked, and its image built, once per node. -/
def substGo (ks : List LevelParam) (vs : List Level) (m : Std.HashMap Level Level) :
    Level → Level × Std.HashMap Level Level
  | .zero => (.zero, m)
  | .param n => (subst.go ks vs n, m)
  | l@(.succ a) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := substGo ks vs m a
      let v := Level.succ p.1
      (v, p.2.insert l v)
  | l@(.max a b) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := substGo ks vs m a
      let q := substGo ks vs p.2 b
      let v := Level.max p.1 q.1
      (v, q.2.insert l v)
  | l@(.imax a b) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := substGo ks vs m a
      let q := substGo ks vs p.2 b
      let v := Level.imax p.1 q.1
      (v, q.2.insert l v)

/-- **The memoised walk is `subst`**, and it keeps the memo's invariant. -/
theorem substGo_spec (ks : List LevelParam) (vs : List Level) :
    ∀ (l : Level) (m : Std.HashMap Level Level), MemoInv (subst ks vs) m →
      (substGo ks vs m l).1 = subst ks vs l ∧ MemoInv (subst ks vs) (substGo ks vs m l).2 := by
  intro l
  induction l with
  | zero => intro m hm; exact ⟨rfl, hm⟩
  | param n => intro m hm; exact ⟨rfl, hm⟩
  | succ a ih =>
    intro m hm
    rw [substGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := ih m hm
      have hv : Level.succ (substGo ks vs m a).1 = subst ks vs (.succ a) := by rw [h1]; rfl
      exact ⟨hv, h2.insert hv⟩
  | max a b iha ihb =>
    intro m hm
    rw [substGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := iha m hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : Level.max (substGo ks vs m a).1 (substGo ks vs (substGo ks vs m a).2 b).1
          = subst ks vs (.max a b) := by rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | imax a b iha ihb =>
    intro m hm
    rw [substGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := iha m hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : Level.imax (substGo ks vs m a).1 (substGo ks vs (substGo ks vs m a).2 b).1
          = subst ks vs (.imax a b) := by rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩

/-- `subst` by the memoised walk, from an empty memo. Not swapped in for
`subst` (instantiation substitutes into the input's own levels, which are
trees, on every constant reference): `leqCore`'s case split on a large
level calls it (`byCasesGo`), the one place that substitutes into a level
the kernel built. -/
def substMemo (ks : List LevelParam) (vs : List Level) (l : Level) : Level :=
  (substGo ks vs {} l).1

theorem substMemo_eq (ks : List LevelParam) (vs : List Level) (l : Level) :
    substMemo ks vs l = subst ks vs l :=
  (substGo_spec ks vs l {} MemoInv.empty).1

/-- Are all parameters of `l` among `params`? -/
def allParamsDefined (params : List LevelParam) : Level → Bool
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

/-- `isNeverZero`, memoised per call on the `max` nodes it has read (the
only nodes where it branches; an `imax` spine is followed as the plain walk
follows it). -/
def isNeverZeroGo (m : Std.HashMap Level Bool) : Level → Bool × Std.HashMap Level Bool
  | .zero => (false, m)
  | .param _ => (false, m)
  | .succ _ => (true, m)
  | l@(.max a b) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := isNeverZeroGo m a
      let q := isNeverZeroGo p.2 b
      let v := p.1 || q.1
      (v, q.2.insert l v)
  | .imax _ b => isNeverZeroGo m b

theorem isNeverZeroGo_spec : ∀ (l : Level) (m : Std.HashMap Level Bool), MemoInv isNeverZero m →
    (isNeverZeroGo m l).1 = isNeverZero l ∧ MemoInv isNeverZero (isNeverZeroGo m l).2 := by
  intro l
  induction l with
  | zero => intro m hm; exact ⟨rfl, hm⟩
  | param n => intro m hm; exact ⟨rfl, hm⟩
  | succ a _ => intro m hm; exact ⟨rfl, hm⟩
  | max a b iha ihb =>
    intro m hm
    rw [isNeverZeroGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := iha m hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : ((isNeverZeroGo m a).1 || (isNeverZeroGo (isNeverZeroGo m a).2 b).1)
          = isNeverZero (.max a b) := by rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | imax a b _ ihb =>
    intro m hm
    obtain ⟨h3, h4⟩ := ihb m hm
    exact ⟨by rw [isNeverZeroGo, h3]; rfl, by rw [isNeverZeroGo]; exact h4⟩

/-- `isNeverZero` itself under another name (the walk on a small level). -/
def isNeverZeroPlain : Level → Bool
  | .zero => false
  | .param _ => false
  | .succ _ => true
  | .max l r => isNeverZeroPlain l || isNeverZeroPlain r
  | .imax _ r => isNeverZeroPlain r

theorem isNeverZeroPlain_eq : ∀ l, isNeverZeroPlain l = isNeverZero l := by
  intro l; induction l <;> simp_all [isNeverZeroPlain, isNeverZero]

/-- The executed `isNeverZero`: the plain walk on a small level, the
memoised walk on a large one. -/
def isNeverZeroFast (l : Level) : Bool :=
  if sizeLeft smallWalk l != 0 then isNeverZeroPlain l else (isNeverZeroGo {} l).1

@[csimp] theorem isNeverZero_eq_isNeverZeroFast : @isNeverZero = @isNeverZeroFast := by
  funext l
  unfold isNeverZeroFast
  split
  · exact (isNeverZeroPlain_eq l).symm
  · exact (isNeverZeroGo_spec l {} MemoInv.empty).1.symm

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

/-! ### `simplify` on shared levels

`simplify` recurses into both children of every `max` and `imax`, so on a
level shared as a DAG (the ∀ rule's levels, and levels that unfolding
instantiates at `max u u`) it visits the tree and builds its result as a
tree: `2^k` steps and nodes for a level of `k` distinct nodes. The
executed `simplify` is `simplifyFast`: `simplifyGo` remembers per call
the result at every node it has simplified, so a node reached again is a
lookup and its result is shared in the output. -/

/-- `simplify`'s `imax` step on simplified arguments. -/
def simplifyIMax (ls rs : Level) : Level :=
  if ls == .zero || ls == .succ .zero then rs
  else match rs with
    | .zero => .zero
    | .succ _ => combining ls rs
    | _ => .imax ls rs

theorem simplify_imax_eq (l r : Level) :
    simplify (.imax l r) = simplifyIMax (simplify l) (simplify r) := by
  rfl

/-- The memo of one `simplify` call: levels already simplified. -/
abbrev SimpMemo := Std.HashMap Level Level

/-- `simplify`, memoised per call on the nodes it has simplified. -/
def simplifyGo (m : SimpMemo) : Level → Level × SimpMemo
  | .zero => (.zero, m)
  | .param n => (.param n, m)
  | l@(.succ a) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := simplifyGo m a
      let v := Level.succ p.1
      (v, p.2.insert l v)
  | l@(.max a b) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := simplifyGo m a
      let q := simplifyGo p.2 b
      let v := combining p.1 q.1
      (v, q.2.insert l v)
  | l@(.imax a b) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := simplifyGo m a
      let q := simplifyGo p.2 b
      let v := simplifyIMax p.1 q.1
      (v, q.2.insert l v)

/-- **The memoised walk is `simplify`**, and it keeps the memo's invariant. -/
theorem simplifyGo_spec : ∀ (l : Level) (m : SimpMemo), MemoInv simplify m →
    (simplifyGo m l).1 = simplify l ∧ MemoInv simplify (simplifyGo m l).2 := by
  intro l
  induction l with
  | zero => intro m hm; exact ⟨rfl, hm⟩
  | param n => intro m hm; exact ⟨rfl, hm⟩
  | succ a ih =>
    intro m hm
    rw [simplifyGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := ih m hm
      have hv : Level.succ (simplifyGo m a).1 = simplify (.succ a) := by rw [h1]; rfl
      exact ⟨hv, h2.insert hv⟩
  | max a b iha ihb =>
    intro m hm
    rw [simplifyGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := iha m hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : combining (simplifyGo m a).1 (simplifyGo (simplifyGo m a).2 b).1
          = simplify (.max a b) := by rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | imax a b iha ihb =>
    intro m hm
    rw [simplifyGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := iha m hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : simplifyIMax (simplifyGo m a).1 (simplifyGo (simplifyGo m a).2 b).1
          = simplify (.imax a b) := by rw [h1, h3, simplify_imax_eq]
      exact ⟨hv, h4.insert hv⟩

/-- `simplify` itself under another name (the walk on a small level). -/
def simplifyPlain : Level → Level
  | .zero => .zero
  | .param n => .param n
  | .succ l => .succ (simplifyPlain l)
  | .max l r => combining (simplifyPlain l) (simplifyPlain r)
  | .imax l r => simplifyIMax (simplifyPlain l) (simplifyPlain r)

theorem simplifyPlain_eq : ∀ l, simplifyPlain l = simplify l := by
  intro l
  induction l with
  | zero => rfl
  | param n => rfl
  | succ a ih => rw [simplifyPlain, ih]; rfl
  | max a b iha ihb => rw [simplifyPlain, iha, ihb]; rfl
  | imax a b iha ihb => rw [simplifyPlain, iha, ihb, simplify_imax_eq]

/-- The executed `simplify`: the plain walk on a small level, the
memoised walk on a large one. -/
def simplifyFast (l : Level) : Level :=
  if sizeLeft smallWalk l != 0 then simplifyPlain l else (simplifyGo {} l).1

@[csimp] theorem simplify_eq_simplifyFast : @simplify = @simplifyFast := by
  funext l
  unfold simplifyFast
  split
  · exact (simplifyPlain_eq l).symm
  · exact (simplifyGo_spec l {} MemoInv.empty).1.symm

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
    -- Ix: nanoda's branch-by-branch split is incomplete here.
    -- `x + k` is two of Géran's sublevels (`x + k` where `x` is nonzero,
    -- `k` where it is zero), and the two may be dominated in different
    -- branches, as in `v + 1 ≤ max (imax (max (u+2) (v+1)) v) 1`.  When
    -- both branches fail, `Geran.leq` decides the case; it is sound and
    -- complete (`Verify/LevelGeran.lean`).
    if ← leqCore fuel l x diff then pure true
    else if ← leqCore fuel l y diff then pure true
    else pure (Geran.leq l r diff)
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
def byCases (fuel : Nat) (p : LevelParam) (l r : Level) (diff : Int) : Option Bool := do
  let l0 := simplify (subst [p] [.zero] l)
  let r0 := simplify (subst [p] [.zero] r)
  if ← leqCore fuel l0 r0 diff then
    let ls := simplify (subst [p] [.succ (.param p)] l)
    let rs := simplify (subst [p] [.succ (.param p)] r)
    leqCore fuel ls rs diff
  else pure false

end

/-! ### `leqCore` on repeated subproblems

`leqCore` solves the same subproblem again wherever two of its branches
meet it: the distribution `imax a (imax x y) ↦ max (imax a y) (imax x y)`
is followed by a split of the `max` whose two halves distribute the same
`y` again, so a chain of `n` `imax` over parameters compared with a
permutation of itself takes `2^n` calls with `O(n³)` distinct
subproblems; and the `max` splits of a level shared as a DAG meet each
shared node once per path. On operands of more than `smallLeq` nodes the
executed `leqCore` (`leqCoreFast`) is `leqCoreMemo`: the same mutual
recursion with the same case order, remembering per call the answer to
every subproblem it has solved, keyed by `(fuel, l, r, diff)`
(`LeqKey`). The key carries the fuel, so an
entry is exactly one call of `rest` and the memo changes no answer,
`none` included; the memo's invariant is that every entry is `rest` of
its key (`LeqMemo.Inv`), and `leqCoreGo_spec` proves the walk is
`leqCore`. Its level tests use `==` (`Level.beqPtr` when executed) where
`rest` writes `=`; the two are the same decision (`Level.beq` is
`decide (a = b)`). A call remembers at most `leqMemoCap` subproblems; past
that it solves new ones without recording them, which costs time and
changes no answer (an entry is only ever a cached answer of `rest`). -/

/-- A subproblem of `leqCore`: one call of `rest`. -/
structure LeqKey where
  fuel : Nat
  l : Level
  r : Level
  diff : Int

instance : BEq LeqKey :=
  ⟨fun a b => a.fuel == b.fuel && a.l == b.l && a.r == b.r && a.diff == b.diff⟩

instance : Hashable LeqKey :=
  ⟨fun k => mixHash (mixHash (hash k.fuel) k.l.hashData) (mixHash k.r.hashData (hash k.diff))⟩

instance : LawfulBEq LeqKey where
  eq_of_beq {a b} h := by
    have h' : (a.fuel == b.fuel && a.l == b.l && a.r == b.r && a.diff == b.diff) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    cases a; cases b; simp_all
  rfl {a} := by
    show (a.fuel == a.fuel && a.l == a.l && a.r == a.r && a.diff == a.diff) = true
    simp

/-- The memo of one `leqCore` call: subproblems already solved. -/
abbrev LeqMemo := Std.HashMap LeqKey (Option Bool)

/-- The memo's invariant: every entry is `rest` of its key. -/
def LeqMemo.Inv (m : LeqMemo) : Prop :=
  ∀ (k : LeqKey) (v : Option Bool), m[k]? = some v → v = rest k.fuel k.l k.r k.diff

theorem LeqMemo.Inv.empty : LeqMemo.Inv {} := by
  intro k v h; simp at h

theorem LeqMemo.Inv.insert {m : LeqMemo} (hm : m.Inv) {k : LeqKey} {v : Option Bool}
    (hv : v = rest k.fuel k.l k.r k.diff) : LeqMemo.Inv (m.insert k v) := by
  intro k' v' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact hv
  · exact hm k' v' hk

mutual

/-- `leqCore`, memoised per call on the subproblems `rest` solves. -/
def leqCoreGo (fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo) :
    Option Bool × LeqMemo :=
  match fuel with
  | 0 => (none, m)
  | fuel + 1 =>
    if l = .zero ∧ diff ≥ 0 then (some true, m)
    else if r = .zero ∧ diff < 0 then (some false, m)
    else
      match m[(⟨fuel, l, r, diff⟩ : LeqKey)]? with
      | some v => (v, m)
      | none =>
        let p := restGo fuel l r diff m
        (p.1, if p.2.size < leqMemoCap then p.2.insert ⟨fuel, l, r, diff⟩ p.1 else p.2)

/-- `rest`, memoised. -/
def restGo (fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo) :
    Option Bool × LeqMemo :=
  match l, r with
  | .param a, .param x => (some (a = x && diff ≥ 0), m)
  | .param _, .zero => (some false, m)
  | .zero, .param _ => (some (diff ≥ 0), m)
  | .succ s, _ => leqCoreGo fuel s r (diff - 1) m
  | _, .succ s => leqCoreGo fuel l s (diff + 1) m
  | .max a b, _ =>
    let p := leqCoreGo fuel a r diff m
    match p.1 with
    | some true => leqCoreGo fuel b r diff p.2
    | v => (v, p.2)
  | .param _, .max x y =>
    let p := leqCoreGo fuel l x diff m
    match p.1 with
    | some false =>
      let q := leqCoreGo fuel l y diff p.2
      match q.1 with
      | some false => (some (Geran.leq l r diff), q.2)
      | v => (v, q.2)
    | v => (v, p.2)
  | .zero, .max x y =>
    let p := leqCoreGo fuel l x diff m
    match p.1 with
    | some false => leqCoreGo fuel l y diff p.2
    | v => (v, p.2)
  | _, _ =>
    match l, r with
    | .imax a b, .imax x y =>
      if a == x && b == y && diff ≥ 0 then (some true, m) else imaxRulesGo fuel l r diff m
    | _, _ => imaxRulesGo fuel l r diff m

/-- `imaxRules`, memoised. -/
def imaxRulesGo (fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo) :
    Option Bool × LeqMemo :=
  match l, r with
  | .imax _ (.param p), _ => byCasesGo fuel p l r diff m
  | _, .imax _ (.param p) => byCasesGo fuel p l r diff m
  | .imax a (.imax x y), _ => leqCoreGo fuel (.max (.imax a y) (.imax x y)) r diff m
  | .imax a (.max x y), _ => leqCoreGo fuel (simplify (.max (.imax a x) (.imax a y))) r diff m
  | _, .imax x (.imax j k) => leqCoreGo fuel l (.max (.imax x k) (.imax j k)) diff m
  | _, .imax x (.max j k) => leqCoreGo fuel l (simplify (.max (.imax x j) (.imax x k))) diff m
  | _, _ => (none, m)

/-- `byCases`, memoised. -/
def byCasesGo (fuel : Nat) (p : LevelParam) (l r : Level) (diff : Int) (m : LeqMemo) :
    Option Bool × LeqMemo :=
  let l0 := simplify (substMemo [p] [.zero] l)
  let r0 := simplify (substMemo [p] [.zero] r)
  let q := leqCoreGo fuel l0 r0 diff m
  match q.1 with
  | some true =>
    let ls := simplify (substMemo [p] [.succ (.param p)] l)
    let rs := simplify (substMemo [p] [.succ (.param p)] r)
    leqCoreGo fuel ls rs diff q.2
  | v => (v, q.2)

end

/-- What `leqCoreGo_spec` proves of a step of the memoised walk: it
computes `f` and keeps the memo's invariant. -/
def LeqGoAgrees (g : Option Bool × LeqMemo) (f : Option Bool) : Prop :=
  g.1 = f ∧ g.2.Inv

/-- `max` on the left: `g₂` runs on `some true` (`do if ← f₁ then f₂ else pure false`). -/
private theorem agree_and {r₁ : Option Bool × LeqMemo} {f₁ f₂ : Option Bool}
    {g₂ : LeqMemo → Option Bool × LeqMemo}
    (h₁ : LeqGoAgrees r₁ f₁) (h₂ : ∀ m : LeqMemo, m.Inv → LeqGoAgrees (g₂ m) f₂) :
    LeqGoAgrees (match r₁.1 with
      | some true => g₂ r₁.2
      | v => (v, r₁.2)) (do if ← f₁ then f₂ else pure false) := by
  obtain ⟨e₁, i₁⟩ := h₁
  obtain ⟨e₂, i₂⟩ := h₂ _ i₁
  rcases f₁ with _ | ⟨_ | _⟩ <;>
    simp [LeqGoAgrees, Bind.bind, Option.bind, Pure.pure, e₁, e₂, i₁, i₂]

/-- `zero` against a `max`: `g₂` runs on `some false`
(`do if ← f₁ then pure true else f₂`). -/
private theorem agree_orElse {r₁ : Option Bool × LeqMemo} {f₁ f₂ : Option Bool}
    {g₂ : LeqMemo → Option Bool × LeqMemo}
    (h₁ : LeqGoAgrees r₁ f₁) (h₂ : ∀ m : LeqMemo, m.Inv → LeqGoAgrees (g₂ m) f₂) :
    LeqGoAgrees (match r₁.1 with
      | some false => g₂ r₁.2
      | v => (v, r₁.2)) (do if ← f₁ then pure true else f₂) := by
  obtain ⟨e₁, i₁⟩ := h₁
  obtain ⟨e₂, i₂⟩ := h₂ _ i₁
  rcases f₁ with _ | ⟨_ | _⟩ <;>
    simp [LeqGoAgrees, Bind.bind, Option.bind, Pure.pure, e₁, e₂, i₁, i₂]

/-- A parameter against a `max`: both branches, then Géran on two `some false`. -/
private theorem agree_or {r₁ : Option Bool × LeqMemo} {f₁ f₂ : Option Bool} {G : Bool}
    {g₂ : LeqMemo → Option Bool × LeqMemo}
    (h₁ : LeqGoAgrees r₁ f₁) (h₂ : ∀ m : LeqMemo, m.Inv → LeqGoAgrees (g₂ m) f₂) :
    LeqGoAgrees (match r₁.1 with
      | some false =>
        match (g₂ r₁.2).1 with
        | some false => (some G, (g₂ r₁.2).2)
        | v => (v, (g₂ r₁.2).2)
      | v => (v, r₁.2))
      (do if ← f₁ then pure true else if ← f₂ then pure true else pure G) := by
  obtain ⟨e₁, i₁⟩ := h₁
  obtain ⟨e₂, i₂⟩ := h₂ _ i₁
  rcases f₁ with _ | ⟨_ | _⟩ <;> rcases f₂ with _ | ⟨_ | _⟩ <;>
    simp [LeqGoAgrees, Bind.bind, Option.bind, Pure.pure, e₁, e₂, i₁, i₂]

/-- Two `imax` with equal arguments: the same test, written with `==`. -/
private theorem agree_imaxEq {a b x y : Level} {diff : Int} {m : LeqMemo}
    {g : Option Bool × LeqMemo} {f : Option Bool} (hm : m.Inv) (h : LeqGoAgrees g f) :
    LeqGoAgrees
      (if (a == x && b == y && decide (diff ≥ 0)) = true then (some true, m) else g)
      (if (decide (a = x) && decide (b = y) && decide (diff ≥ 0)) = true then some true
        else f) := by
  have e : (a == x && b == y && decide (diff ≥ 0))
      = (decide (a = x) && decide (b = y) && decide (diff ≥ 0)) := rfl
  rw [e]
  by_cases hc : (decide (a = x) && decide (b = y) && decide (diff ≥ 0)) = true
  · rw [if_pos hc, if_pos hc]; exact ⟨rfl, hm⟩
  · rw [if_neg hc, if_neg hc]; exact h

/-- **The memoised walk is `leqCore`**, and it keeps the memo's invariant. -/
theorem leqCoreGo_spec : ∀ (fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo), m.Inv →
    LeqGoAgrees (leqCoreGo fuel l r diff m) (leqCore fuel l r diff) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l r diff m hm
    rw [leqCoreGo, leqCore]; exact ⟨rfl, hm⟩
  | succ fuel ih =>
    have hbc : ∀ p l r diff (m : LeqMemo), m.Inv →
        LeqGoAgrees (byCasesGo fuel p l r diff m) (byCases fuel p l r diff) := by
      intro p l r diff m hm
      rw [byCasesGo, byCases]
      simp only [substMemo_eq]
      exact agree_and (g₂ := leqCoreGo fuel _ _ _) (ih _ _ _ _ hm) (fun m hm => ih _ _ _ _ hm)
    have him : ∀ l r diff (m : LeqMemo), m.Inv →
        LeqGoAgrees (imaxRulesGo fuel l r diff m) (imaxRules fuel l r diff) := by
      intro l r diff m hm
      rcases l with _ | _ | _ | ⟨_, _ | _ | _ | _ | _⟩ | _ <;>
        rcases r with _ | _ | _ | ⟨_, _ | _ | _ | _ | _⟩ | _ <;>
        (unfold imaxRulesGo imaxRules; try dsimp only) <;>
        first
        | exact ⟨rfl, hm⟩
        | exact hbc _ _ _ _ _ hm
        | exact ih _ _ _ _ hm
    have hrest : ∀ l r diff (m : LeqMemo), m.Inv →
        LeqGoAgrees (restGo fuel l r diff m) (rest fuel l r diff) := by
      intro l r diff m hm
      rcases l with _ | _ | _ | _ | _ <;> rcases r with _ | _ | _ | _ | _ <;>
        (unfold restGo rest; try dsimp only) <;>
        first
        | exact ⟨rfl, hm⟩
        | exact ih _ _ _ _ hm
        | exact agree_and (g₂ := leqCoreGo fuel _ _ _) (ih _ _ _ _ hm) (fun m hm => ih _ _ _ _ hm)
        | exact agree_orElse (g₂ := leqCoreGo fuel _ _ _) (ih _ _ _ _ hm)
            (fun m hm => ih _ _ _ _ hm)
        | exact agree_or (g₂ := leqCoreGo fuel _ _ _) (ih _ _ _ _ hm) (fun m hm => ih _ _ _ _ hm)
        | exact agree_imaxEq hm (him _ _ _ _ hm)
        | exact him _ _ _ _ hm
    intro l r diff m hm
    rw [leqCoreGo, leqCore]
    by_cases h₁ : l = .zero ∧ diff ≥ 0
    · rw [if_pos h₁, if_pos h₁]; exact ⟨rfl, hm⟩
    · rw [if_neg h₁, if_neg h₁]
      by_cases h₂ : r = .zero ∧ diff < 0
      · rw [if_pos h₂, if_pos h₂]; exact ⟨rfl, hm⟩
      · rw [if_neg h₂, if_neg h₂]
        split
        · rename_i v hv
          exact ⟨hm _ _ hv, hm⟩
        · obtain ⟨e, i⟩ := hrest l r diff m hm
          refine ⟨e, ?_⟩
          dsimp only
          split
          · exact i.insert (k := ⟨fuel, l, r, diff⟩) e
          · exact i

/-- The executed `leqCore`: one memoised walk from an empty memo. -/
def leqCoreMemo (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  (leqCoreGo fuel l r diff {}).1

/-! ### `leqCore` with a budget

The memo makes the families above polynomial, but the comparison is
coNP-hard (`docs/kernel.md`, "Running time"), so a small hostile level can
still make `leqCore` solve exponentially many distinct subproblems
(`imaxswap` and `cnfChain` in `Tests/Ix/Kernel/LevelSharing.lean`), and
`Geran.leq` decomposes a level into sublevels whose number can be
exponential in the level's size. `leqCoreB budget` is the memoised walk
`leqCoreGo` with a count of its work beside the memo, which gives up
(`none`) when the count would pass `budget`. The memo is the same map with
the same entries as `leqCoreGo`'s (the count is a separate number), so a
run that does not give up is `leqCoreGo`'s run step for step, and its
answer is `leqCore`'s (`leqCoreB_eq`; `none` from `leqCore` itself, when
the depth fuel runs out, stays `some none`).

What it counts, in one number `n` threaded through the walk:
* each subproblem the walk solves anew (a memo miss: one new memo entry
  while the memo is below `leqMemoCap`). At a miss the walk gives up if `n`
  has reached `budget`, so a run makes at most `budget` of them;
* at each call of `Geran.leq l r diff` (the `(param, max)` case when both
  branches fail), the sublevels of its operands (`geranSubs`, a bound on
  the lengths of `Geran.decomposeAux`'s lists, `decomposeAux_length_le`),
  added to `n`; past `budget` it gives up.

And each Géran call has a cap of its own, `budget / 16`: its operands'
trees must have fewer than `budget / 16` nodes together (`sizeLeft`, which
visits at most that many) and at most `budget / 16` sublevels
(`geranCost`), or the walk gives up. The tree bound comes first because
`geranSubs` is a tree recursion and a shared level's tree can be
exponentially larger than its DAG.

The count starts from a given value and is returned (`leqCoreBFrom`), so
the two directions of one equivalence test can share one budget;
`leqCoreB` is one direction from zero. -/

/-- Géran's sublevels of `l` and its condition sets: `(geranSubs l).1`
bounds the number of sublevels `Geran.decomposeAux` adds for `l`, at any
condition set and offset (`decomposeAux_length_le`), and `(geranSubs l).2`
is the number of `l`'s condition sets (`geranSubs_nzConds`). A tree
recursion: `geranCost` bounds the tree first. -/
def geranSubs : Level → Nat × Nat
  | .zero => (1, 0)
  | .succ a => ((geranSubs a).1, 1)
  | .max a b =>
    let p := geranSubs a
    let q := geranSubs b
    (p.1 + q.1, p.2 + q.2)
  | .imax a b =>
    let p := geranSubs a
    let q := geranSubs b
    (q.1 + q.2 * p.1, q.2)
  | .param _ => (2, 1)

theorem geranSubs_nzConds : ∀ l : Level, (Geran.nzConds l).length = (geranSubs l).2
  | .zero => rfl
  | .succ _ => rfl
  | .max a b => by
    simp only [Geran.nzConds, geranSubs, List.length_append, geranSubs_nzConds a,
      geranSubs_nzConds b]
  | .imax _ b => by simp only [Geran.nzConds, geranSubs, geranSubs_nzConds b]
  | .param _ => rfl

theorem decomposeAux_length_le : ∀ (l : Level) (path : List LevelParam) (k : Nat)
    (acc : List Geran.Sub),
    (Geran.decomposeAux path k l acc).length ≤ (geranSubs l).1 + acc.length
  | .zero, _, _, _ => by simp only [Geran.decomposeAux, geranSubs, List.length_cons] <;> omega
  | .succ u, path, k, acc => by
    simpa only [Geran.decomposeAux, geranSubs] using decomposeAux_length_le u path (k + 1) acc
  | .max u v, path, k, acc => by
    have h₁ := decomposeAux_length_le u path k acc
    have h₂ := decomposeAux_length_le v path k (Geran.decomposeAux path k u acc)
    simp only [Geran.decomposeAux, geranSubs] <;> omega
  | .imax u v, path, k, acc => by
    have hfold : ∀ (cs : List (List LevelParam)) (a : List Geran.Sub),
        (cs.foldl (fun acc c => Geran.decomposeAux (c ++ path) k u acc) a).length ≤
          cs.length * (geranSubs u).1 + a.length := by
      intro cs
      induction cs with
      | nil => intro a; simp
      | cons c cs ih =>
        intro a
        have h₁ := decomposeAux_length_le u (c ++ path) k a
        have h₂ := ih (Geran.decomposeAux (c ++ path) k u a)
        simp only [List.foldl_cons, List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega
    have h₁ := decomposeAux_length_le v path k acc
    have h₂ := hfold (Geran.nzConds v) (Geran.decomposeAux path k v acc)
    rw [geranSubs_nzConds] at h₂
    simp only [Geran.decomposeAux, geranSubs] <;> omega
  | .param _, _, _, _ => by
    simp only [Geran.decomposeAux, geranSubs]
    split <;> simp only [List.length_cons] <;> omega

/-- What one call `Geran.leq l r diff` adds to the count: the sublevels of
its operands, when the call is within the per-call cap `cap` (its operands'
trees have fewer than `cap` nodes together, and at most `cap` sublevels);
`none` past the cap. Its time is bounded by `cap`: the tree is measured by
`sizeLeft`, which stops after `cap` nodes, before `geranSubs` walks it. -/
def geranCost (cap : Nat) (l r : Level) : Option Nat :=
  if sizeLeft (sizeLeft cap l) r == 0 then none
  else
    let c := (geranSubs l).1 + (geranSubs r).1
    if c ≤ cap then some c else none

/-- A call of `Geran.leq` in the counted walk (`restBGo`): its cost added
to the count `n`, giving up past the cap `budget / 16` or the budget. -/
def geranStepB (budget : Nat) (l r : Level) (diff : Int) (m : LeqMemo) (n : Nat) :
    Option (Option Bool × LeqMemo × Nat) :=
  (geranCost (budget / 16) l r).bind fun c =>
    if budget < n + c then none else some (some (Geran.leq l r diff), m, n + c)

mutual

/-- `leqCoreGo` with a budget: `n` is the count so far (above); `none` when
the walk gives up, else `leqCoreGo`'s result and the count after. -/
def leqCoreBGo (budget fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo) (n : Nat) :
    Option (Option Bool × LeqMemo × Nat) :=
  match fuel with
  | 0 => some (none, m, n)
  | fuel + 1 =>
    if l = .zero ∧ diff ≥ 0 then some (some true, m, n)
    else if r = .zero ∧ diff < 0 then some (some false, m, n)
    else
      match m[(⟨fuel, l, r, diff⟩ : LeqKey)]? with
      | some v => some (v, m, n)
      | none =>
        if budget ≤ n then none
        else (restBGo budget fuel l r diff m (n + 1)).map fun p =>
          (p.1, if p.2.1.size < leqMemoCap then p.2.1.insert ⟨fuel, l, r, diff⟩ p.1 else p.2.1,
            p.2.2)

/-- `restGo` with a budget. -/
def restBGo (budget fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo) (n : Nat) :
    Option (Option Bool × LeqMemo × Nat) :=
  match l, r with
  | .param a, .param x => some (some (a = x && diff ≥ 0), m, n)
  | .param _, .zero => some (some false, m, n)
  | .zero, .param _ => some (some (diff ≥ 0), m, n)
  | .succ s, _ => leqCoreBGo budget fuel s r (diff - 1) m n
  | _, .succ s => leqCoreBGo budget fuel l s (diff + 1) m n
  | .max a b, _ =>
    (leqCoreBGo budget fuel a r diff m n).bind fun p =>
      match p.1 with
      | some true => leqCoreBGo budget fuel b r diff p.2.1 p.2.2
      | v => some (v, p.2.1, p.2.2)
  | .param _, .max x y =>
    (leqCoreBGo budget fuel l x diff m n).bind fun p =>
      match p.1 with
      | some false =>
        (leqCoreBGo budget fuel l y diff p.2.1 p.2.2).bind fun q =>
          match q.1 with
          | some false => geranStepB budget l r diff q.2.1 q.2.2
          | v => some (v, q.2.1, q.2.2)
      | v => some (v, p.2.1, p.2.2)
  | .zero, .max x y =>
    (leqCoreBGo budget fuel l x diff m n).bind fun p =>
      match p.1 with
      | some false => leqCoreBGo budget fuel l y diff p.2.1 p.2.2
      | v => some (v, p.2.1, p.2.2)
  | _, _ =>
    match l, r with
    | .imax a b, .imax x y =>
      if a == x && b == y && diff ≥ 0 then some (some true, m, n)
      else imaxRulesBGo budget fuel l r diff m n
    | _, _ => imaxRulesBGo budget fuel l r diff m n

/-- `imaxRulesGo` with a budget. -/
def imaxRulesBGo (budget fuel : Nat) (l r : Level) (diff : Int) (m : LeqMemo) (n : Nat) :
    Option (Option Bool × LeqMemo × Nat) :=
  match l, r with
  | .imax _ (.param p), _ => byCasesBGo budget fuel p l r diff m n
  | _, .imax _ (.param p) => byCasesBGo budget fuel p l r diff m n
  | .imax a (.imax x y), _ => leqCoreBGo budget fuel (.max (.imax a y) (.imax x y)) r diff m n
  | .imax a (.max x y), _ =>
    leqCoreBGo budget fuel (simplify (.max (.imax a x) (.imax a y))) r diff m n
  | _, .imax x (.imax j k) => leqCoreBGo budget fuel l (.max (.imax x k) (.imax j k)) diff m n
  | _, .imax x (.max j k) =>
    leqCoreBGo budget fuel l (simplify (.max (.imax x j) (.imax x k))) diff m n
  | _, _ => some (none, m, n)

/-- `byCasesGo` with a budget. -/
def byCasesBGo (budget fuel : Nat) (p : LevelParam) (l r : Level) (diff : Int) (m : LeqMemo)
    (n : Nat) : Option (Option Bool × LeqMemo × Nat) :=
  let l0 := simplify (substMemo [p] [.zero] l)
  let r0 := simplify (substMemo [p] [.zero] r)
  (leqCoreBGo budget fuel l0 r0 diff m n).bind fun q =>
    match q.1 with
    | some true =>
      let ls := simplify (substMemo [p] [.succ (.param p)] l)
      let rs := simplify (substMemo [p] [.succ (.param p)] r)
      leqCoreBGo budget fuel ls rs diff q.2.1 q.2.2
    | v => some (v, q.2.1, q.2.2)

end

/-- What `leqCoreBGo_agrees` proves of a step of the counted walk: it gave
up, or it is the memoised walk's step `g` (answer and memo) with some count. -/
def LeqBAgrees (gb : Option (Option Bool × LeqMemo × Nat)) (g : Option Bool × LeqMemo) : Prop :=
  gb = none ∨ ∃ k, gb = some (g.1, g.2, k)

/-- `max` on the left (and the case split): the second call runs on `some true`. -/
private theorem bagree_and {gb₁ : Option (Option Bool × LeqMemo × Nat)}
    {g₁ : Option Bool × LeqMemo}
    {gb₂ : LeqMemo → Nat → Option (Option Bool × LeqMemo × Nat)}
    {g₂ : LeqMemo → Option Bool × LeqMemo}
    (h₁ : LeqBAgrees gb₁ g₁) (h₂ : ∀ m k, LeqBAgrees (gb₂ m k) (g₂ m)) :
    LeqBAgrees
      (gb₁.bind fun p =>
        match p.1 with
        | some true => gb₂ p.2.1 p.2.2
        | v => some (v, p.2.1, p.2.2))
      (match g₁.1 with
        | some true => g₂ g₁.2
        | v => (v, g₁.2)) := by
  rcases h₁ with h | ⟨k, h⟩
  · exact Or.inl (by rw [h]; rfl)
  · rw [h]
    obtain ⟨v, m⟩ := g₁
    rcases v with _ | ⟨_ | _⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact h₂ m k

/-- `zero` against a `max`: the second call runs on `some false`. -/
private theorem bagree_orElse {gb₁ : Option (Option Bool × LeqMemo × Nat)}
    {g₁ : Option Bool × LeqMemo}
    {gb₂ : LeqMemo → Nat → Option (Option Bool × LeqMemo × Nat)}
    {g₂ : LeqMemo → Option Bool × LeqMemo}
    (h₁ : LeqBAgrees gb₁ g₁) (h₂ : ∀ m k, LeqBAgrees (gb₂ m k) (g₂ m)) :
    LeqBAgrees
      (gb₁.bind fun p =>
        match p.1 with
        | some false => gb₂ p.2.1 p.2.2
        | v => some (v, p.2.1, p.2.2))
      (match g₁.1 with
        | some false => g₂ g₁.2
        | v => (v, g₁.2)) := by
  rcases h₁ with h | ⟨k, h⟩
  · exact Or.inl (by rw [h]; rfl)
  · rw [h]
    obtain ⟨v, m⟩ := g₁
    rcases v with _ | ⟨_ | _⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact h₂ m k
    · exact Or.inr ⟨k, rfl⟩

/-- A parameter against a `max`: both branches, then Géran on two `some false`. -/
private theorem bagree_or {gb₁ : Option (Option Bool × LeqMemo × Nat)}
    {g₁ : Option Bool × LeqMemo}
    {gb₂ : LeqMemo → Nat → Option (Option Bool × LeqMemo × Nat)}
    {g₂ : LeqMemo → Option Bool × LeqMemo}
    {gb₃ : LeqMemo → Nat → Option (Option Bool × LeqMemo × Nat)} {G : Bool}
    (h₁ : LeqBAgrees gb₁ g₁) (h₂ : ∀ m k, LeqBAgrees (gb₂ m k) (g₂ m))
    (h₃ : ∀ m k, LeqBAgrees (gb₃ m k) (some G, m)) :
    LeqBAgrees
      (gb₁.bind fun p =>
        match p.1 with
        | some false =>
          (gb₂ p.2.1 p.2.2).bind fun q =>
            match q.1 with
            | some false => gb₃ q.2.1 q.2.2
            | v => some (v, q.2.1, q.2.2)
        | v => some (v, p.2.1, p.2.2))
      (match g₁.1 with
        | some false =>
          match (g₂ g₁.2).1 with
          | some false => (some G, (g₂ g₁.2).2)
          | v => (v, (g₂ g₁.2).2)
        | v => (v, g₁.2)) := by
  rcases h₁ with h | ⟨k, h⟩
  · exact Or.inl (by rw [h]; rfl)
  · rw [h]
    obtain ⟨v, m⟩ := g₁
    rcases v with _ | ⟨_ | _⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact bagree_orElse (gb₂ := gb₃) (g₂ := fun m => (some G, m)) (h₂ m k) h₃
    · exact Or.inr ⟨k, rfl⟩

/-- Two `imax` with equal arguments: the same test in both walks. -/
private theorem bagree_imaxEq {a b x y : Level} {diff : Int} {m : LeqMemo} {n : Nat}
    {gb : Option (Option Bool × LeqMemo × Nat)} {g : Option Bool × LeqMemo}
    (h : LeqBAgrees gb g) :
    LeqBAgrees
      (if (a == x && b == y && decide (diff ≥ 0)) = true then some (some true, m, n) else gb)
      (if (a == x && b == y && decide (diff ≥ 0)) = true then (some true, m) else g) := by
  by_cases hc : (a == x && b == y && decide (diff ≥ 0)) = true
  · rw [if_pos hc, if_pos hc]; exact Or.inr ⟨n, rfl⟩
  · rw [if_neg hc, if_neg hc]; exact h

/-- Géran's step: it gives up, or it is the memoised walk's Géran answer. -/
private theorem bagree_geran (budget : Nat) (l r : Level) (diff : Int) (m : LeqMemo) (n : Nat) :
    LeqBAgrees (geranStepB budget l r diff m n) (some (Geran.leq l r diff), m) := by
  unfold geranStepB
  cases geranCost (budget / 16) l r with
  | none => exact Or.inl rfl
  | some c =>
    show LeqBAgrees (if budget < n + c then none else some (some (Geran.leq l r diff), m, n + c)) _
    by_cases hb : budget < n + c
    · rw [if_pos hb]; exact Or.inl rfl
    · rw [if_neg hb]; exact Or.inr ⟨n + c, rfl⟩

/-- **The counted walk is the memoised walk until it gives up.** -/
theorem leqCoreBGo_agrees (budget : Nat) : ∀ (fuel : Nat) (l r : Level) (diff : Int)
    (m : LeqMemo) (n : Nat),
    LeqBAgrees (leqCoreBGo budget fuel l r diff m n) (leqCoreGo fuel l r diff m) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l r diff m n
    rw [leqCoreBGo, leqCoreGo]; exact Or.inr ⟨n, rfl⟩
  | succ fuel ih =>
    have hbc : ∀ p l r diff (m : LeqMemo) n,
        LeqBAgrees (byCasesBGo budget fuel p l r diff m n) (byCasesGo fuel p l r diff m) := by
      intro p l r diff m n
      rw [byCasesBGo, byCasesGo]
      dsimp only
      exact bagree_and (gb₂ := leqCoreBGo budget fuel _ _ _) (g₂ := leqCoreGo fuel _ _ _)
        (ih _ _ _ _ _) (fun m k => ih _ _ _ _ _)
    have him : ∀ l r diff (m : LeqMemo) n,
        LeqBAgrees (imaxRulesBGo budget fuel l r diff m n) (imaxRulesGo fuel l r diff m) := by
      intro l r diff m n
      rcases l with _ | _ | _ | ⟨_, _ | _ | _ | _ | _⟩ | _ <;>
        rcases r with _ | _ | _ | ⟨_, _ | _ | _ | _ | _⟩ | _ <;>
        (unfold imaxRulesBGo imaxRulesGo; try dsimp only) <;>
        first
        | exact Or.inr ⟨n, rfl⟩
        | exact hbc _ _ _ _ _ _
        | exact ih _ _ _ _ _
    have hrest : ∀ l r diff (m : LeqMemo) n,
        LeqBAgrees (restBGo budget fuel l r diff m n) (restGo fuel l r diff m) := by
      intro l r diff m n
      rcases l with _ | _ | _ | _ | _ <;> rcases r with _ | _ | _ | _ | _ <;>
        (unfold restBGo restGo; try dsimp only) <;>
        first
        | exact Or.inr ⟨n, rfl⟩
        | exact ih _ _ _ _ _
        | exact bagree_and (gb₂ := leqCoreBGo budget fuel _ _ _) (g₂ := leqCoreGo fuel _ _ _)
            (ih _ _ _ _ _) (fun m k => ih _ _ _ _ _)
        | exact bagree_orElse (gb₂ := leqCoreBGo budget fuel _ _ _) (g₂ := leqCoreGo fuel _ _ _)
            (ih _ _ _ _ _) (fun m k => ih _ _ _ _ _)
        | exact bagree_or (gb₂ := leqCoreBGo budget fuel _ _ _) (g₂ := leqCoreGo fuel _ _ _)
            (gb₃ := geranStepB budget _ _ _) (ih _ _ _ _ _) (fun m k => ih _ _ _ _ _)
            (fun m k => bagree_geran budget _ _ _ m k)
        | exact bagree_imaxEq (him _ _ _ _ _)
        | exact him _ _ _ _ _
    intro l r diff m n
    rw [leqCoreBGo, leqCoreGo]
    by_cases h₁ : l = .zero ∧ diff ≥ 0
    · rw [if_pos h₁, if_pos h₁]; exact Or.inr ⟨n, rfl⟩
    · rw [if_neg h₁, if_neg h₁]
      by_cases h₂ : r = .zero ∧ diff < 0
      · rw [if_pos h₂, if_pos h₂]; exact Or.inr ⟨n, rfl⟩
      · rw [if_neg h₂, if_neg h₂]
        cases m[(⟨fuel, l, r, diff⟩ : LeqKey)]? with
        | some _ => exact Or.inr ⟨n, rfl⟩
        | none =>
          dsimp only
          by_cases hb : budget ≤ n
          · rw [if_pos hb]; exact Or.inl rfl
          · rw [if_neg hb]
            rcases hrest l r diff m (n + 1) with h | ⟨k, h⟩
            · exact Or.inl (by rw [h]; rfl)
            · exact Or.inr ⟨k, by rw [h]; rfl⟩

/-- `leqCore fuel l r diff` with a budget, from the count `n` already spent:
`none` when the count would pass `budget` (`leqCoreB` above), else
`leqCore`'s answer and the count after. With it the two directions of one
equivalence test share one budget: the second starts from the first's count. -/
def leqCoreBFrom (budget fuel : Nat) (l r : Level) (diff : Int) (n : Nat) :
    Option (Option Bool × Nat) :=
  (leqCoreBGo budget fuel l r diff {} n).map fun p => (p.1, p.2.2)

/-- `leqCore fuel l r diff` with a budget (above): `none` when the walk
gives up, which happens when its count of new memo entries and Géran
sublevels would pass `budget` or a Géran call passes its cap `budget / 16`;
otherwise `some` of `leqCore`'s answer (`leqCoreB_eq`). -/
def leqCoreB (budget fuel : Nat) (l r : Level) (diff : Int) : Option (Option Bool) :=
  (leqCoreBFrom budget fuel l r diff 0).map (·.1)

theorem leqCoreBFrom_eq (budget fuel : Nat) (l r : Level) (diff : Int) (n : Nat) :
    leqCoreBFrom budget fuel l r diff n = none ∨
      ∃ n', leqCoreBFrom budget fuel l r diff n = some (leqCore fuel l r diff, n') := by
  unfold leqCoreBFrom
  rcases leqCoreBGo_agrees budget fuel l r diff {} n with h | ⟨k, h⟩
  · exact Or.inl (by rw [h]; rfl)
  · refine Or.inr ⟨k, ?_⟩
    rw [h, ← (leqCoreGo_spec fuel l r diff {} LeqMemo.Inv.empty).1]
    rfl

/-- **A budgeted comparison gives up or answers as `leqCore`.** -/
theorem leqCoreB_eq (b fuel : Nat) (l r : Level) (d : Int) :
    leqCoreB b fuel l r d = none ∨ leqCoreB b fuel l r d = some (leqCore fuel l r d) := by
  unfold leqCoreB
  rcases leqCoreBFrom_eq b fuel l r d 0 with h | ⟨k, h⟩
  · exact Or.inl (by rw [h]; rfl)
  · exact Or.inr (by rw [h]; rfl)

mutual

/-- `leqCore` itself under another name (the recursion on small operands). -/
def leqCorePlain (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if l = .zero ∧ diff ≥ 0 then some true
    else if r = .zero ∧ diff < 0 then some false
    else restPlain fuel l r diff

/-- `rest` under another name. -/
def restPlain (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .param a, .param x => some (a = x && diff ≥ 0)
  | .param _, .zero => some false
  | .zero, .param _ => some (diff ≥ 0)
  | .succ s, _ => leqCorePlain fuel s r (diff - 1)
  | _, .succ s => leqCorePlain fuel l s (diff + 1)
  | .max a b, _ => do
    if ← leqCorePlain fuel a r diff then leqCorePlain fuel b r diff else pure false
  | .param _, .max x y => do
    if ← leqCorePlain fuel l x diff then pure true
    else if ← leqCorePlain fuel l y diff then pure true
    else pure (Geran.leq l r diff)
  | .zero, .max x y => do
    if ← leqCorePlain fuel l x diff then pure true else leqCorePlain fuel l y diff
  | _, _ =>
    match l, r with
    | .imax a b, .imax x y =>
      if a = x && b = y && diff ≥ 0 then some true else imaxRulesPlain fuel l r diff
    | _, _ => imaxRulesPlain fuel l r diff

/-- `imaxRules` under another name. -/
def imaxRulesPlain (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .imax _ (.param p), _ => byCasesPlain fuel p l r diff
  | _, .imax _ (.param p) => byCasesPlain fuel p l r diff
  | .imax a (.imax x y), _ => leqCorePlain fuel (.max (.imax a y) (.imax x y)) r diff
  | .imax a (.max x y), _ => leqCorePlain fuel (simplify (.max (.imax a x) (.imax a y))) r diff
  | _, .imax x (.imax j k) => leqCorePlain fuel l (.max (.imax x k) (.imax j k)) diff
  | _, .imax x (.max j k) => leqCorePlain fuel l (simplify (.max (.imax x j) (.imax x k))) diff
  | _, _ => none

/-- `byCases` under another name. -/
def byCasesPlain (fuel : Nat) (p : LevelParam) (l r : Level) (diff : Int) : Option Bool := do
  let l0 := simplify (subst [p] [.zero] l)
  let r0 := simplify (subst [p] [.zero] r)
  if ← leqCorePlain fuel l0 r0 diff then
    let ls := simplify (subst [p] [.succ (.param p)] l)
    let rs := simplify (subst [p] [.succ (.param p)] r)
    leqCorePlain fuel ls rs diff
  else pure false

end

theorem leqCorePlain_eq : ∀ (fuel : Nat) (l r : Level) (diff : Int),
    leqCorePlain fuel l r diff = leqCore fuel l r diff := by
  intro fuel
  induction fuel with
  | zero => intro l r diff; rw [leqCorePlain, leqCore]
  | succ fuel ih =>
    have hbc : ∀ p l r diff, byCasesPlain fuel p l r diff = byCases fuel p l r diff := by
      intro p l r diff; rw [byCasesPlain, byCases]; simp only [ih]
    have him : ∀ l r diff, imaxRulesPlain fuel l r diff = imaxRules fuel l r diff := by
      intro l r diff
      rcases l with _ | _ | _ | ⟨_, _ | _ | _ | _ | _⟩ | _ <;>
        rcases r with _ | _ | _ | ⟨_, _ | _ | _ | _ | _⟩ | _ <;>
        (unfold imaxRulesPlain imaxRules; try dsimp only) <;> simp only [ih, hbc]
    have hrest : ∀ l r diff, restPlain fuel l r diff = rest fuel l r diff := by
      intro l r diff
      rcases l with _ | _ | _ | _ | _ <;> rcases r with _ | _ | _ | _ | _ <;>
        (unfold restPlain rest; try dsimp only) <;> simp only [ih, him]
    intro l r diff
    rw [leqCorePlain, leqCore]
    simp only [hrest]

/-- The executed `leqCore`: the plain recursion on small operands, the
memoised walk otherwise. -/
def leqCoreFast (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  if sizeLeft (sizeLeft smallLeq l) r != 0 then leqCorePlain fuel l r diff
  else leqCoreMemo fuel l r diff

@[csimp] theorem leqCore_eq_leqCoreFast : @leqCore = @leqCoreFast := by
  funext fuel l r diff
  unfold leqCoreFast leqCoreMemo
  split
  · exact (leqCorePlain_eq fuel l r diff).symm
  · exact (leqCoreGo_spec fuel l r diff {} LeqMemo.Inv.empty).1.symm

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
`{φ | eval φ l = 0}`.  `Ix.Kernel.Verify.PropWhen` proves
`(zeronessOf l).holds φ = (eval φ l == 0)`.  Case notes: a `max` is
zero iff both sides are (`inter`); an `imax` is zero iff its right
side is (`eval (imax a b) = if eval b = 0 then 0 else max …`). -/
def zeronessOf : Level → PropWhen
  | .zero => .ifAllZero []
  | .succ _ => .never
  | .param n => .ifAllZero [n]
  | .max a b => (zeronessOf a).inter (zeronessOf b)
  | .imax _ b => zeronessOf b

/-- `zeronessOf`, memoised per call on the `max` nodes it has read (the
only nodes where it branches; an `imax` spine is followed as the plain walk
follows it). The ∀ rule asks it of the codomain's sort. -/
def zeronessGo (m : Std.HashMap Level PropWhen) : Level → PropWhen × Std.HashMap Level PropWhen
  | .zero => (.ifAllZero [], m)
  | .succ _ => (.never, m)
  | .param n => (.ifAllZero [n], m)
  | l@(.max a b) =>
    match m[l]? with
    | some v => (v, m)
    | none =>
      let p := zeronessGo m a
      let q := zeronessGo p.2 b
      let v := p.1.inter q.1
      (v, q.2.insert l v)
  | .imax _ b => zeronessGo m b

theorem zeronessGo_spec : ∀ (l : Level) (m : Std.HashMap Level PropWhen), MemoInv zeronessOf m →
    (zeronessGo m l).1 = zeronessOf l ∧ MemoInv zeronessOf (zeronessGo m l).2 := by
  intro l
  induction l with
  | zero => intro m hm; exact ⟨rfl, hm⟩
  | param n => intro m hm; exact ⟨rfl, hm⟩
  | succ a _ => intro m hm; exact ⟨rfl, hm⟩
  | max a b iha ihb =>
    intro m hm
    rw [zeronessGo]
    split
    · rename_i v hv
      exact ⟨hm _ _ hv, hm⟩
    · obtain ⟨h1, h2⟩ := iha m hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : (zeronessGo m a).1.inter (zeronessGo (zeronessGo m a).2 b).1
          = zeronessOf (.max a b) := by rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | imax a b _ ihb =>
    intro m hm
    obtain ⟨h3, h4⟩ := ihb m hm
    exact ⟨by rw [zeronessGo, h3]; rfl, by rw [zeronessGo]; exact h4⟩

/-- `zeronessOf` itself under another name (the walk on a small level). -/
def zeronessOfPlain : Level → PropWhen
  | .zero => .ifAllZero []
  | .succ _ => .never
  | .param n => .ifAllZero [n]
  | .max a b => (zeronessOfPlain a).inter (zeronessOfPlain b)
  | .imax _ b => zeronessOfPlain b

theorem zeronessOfPlain_eq : ∀ l, zeronessOfPlain l = zeronessOf l := by
  intro l; induction l <;> simp_all [zeronessOfPlain, zeronessOf]

/-- The executed `zeronessOf`: the plain walk on a small level, the
memoised walk on a large one. -/
def zeronessOfFast (l : Level) : PropWhen :=
  if sizeLeft smallWalk l != 0 then zeronessOfPlain l else (zeronessGo {} l).1

@[csimp] theorem zeronessOf_eq_zeronessOfFast : @zeronessOf = @zeronessOfFast := by
  funext l
  unfold zeronessOfFast
  split
  · exact (zeronessOfPlain_eq l).symm
  · exact (zeronessGo_spec l {} MemoInv.empty).1.symm

/-- Push a level-parameter substitution through a zero-ness datum
(task #161): each parameter becomes its replacement's datum,
intersected — `Z(subst ks vs l)` is exactly
`substPW ks vs (zeronessOf l)` (`Verify.PropWhen.zeronessOf_subst`).
Canonical on output (`PropWhen.bindZ`, task #194): an unlisted
parameter reproduces `ifAllZero [n]`, so instantiating a declaration
at its own parameters is the identity here too (`substPW_self`) —
unconditionally, because every datum is canonical by construction. -/
def substPW (ks : List LevelParam) (vs : List Level) (pw : PropWhen) :
    PropWhen :=
  pw.bindZ fun n => zeronessOf (subst.go ks vs n)

end Ix.Kernel.Level

namespace Ix.Kernel

/-- No duplicates in a list of level parameters. -/
def LevelParam.nodup : List LevelParam → Bool
  | [] => true
  | n :: ns => !ns.contains n && LevelParam.nodup ns

/-- Substitute level parameters throughout an expression (sorts and
constant level arguments). -/
def Expr.instantiateLevelParams (ks : List LevelParam) (us : List Level) : Expr md → Expr md
  | .bvar i => .bvar i
  | .fvar idx ty => .fvar idx (ty.instantiateLevelParams ks us)
  | .sort u => .sort (Level.subst ks us u)
  | .const n vs => .const n (vs.map (Level.subst ks us))
  | .app f a => .app (f.instantiateLevelParams ks us) (a.instantiateLevelParams ks us)
  | .lam ty body m =>
    .lam (ty.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
      { m with pw := Level.substPW ks us m.pw }
  | .forallE ty body m =>
    .forallE (ty.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
      { m with pw := Level.substPW ks us m.pw }
  | .letE ty val body lmeta => .letE (ty.instantiateLevelParams ks us)
      (val.instantiateLevelParams ks us) (body.instantiateLevelParams ks us) lmeta
  | .lit l => .lit l
  | .proj s i e => .proj s i (e.instantiateLevelParams ks us)

/-- Are all level parameters occurring in `e` among `params`?  Binder
prop-ness data included (task #161): their parameters are level
parameters of the term — `instantiateLevelParams` substitutes into
them, and its composition law needs them covered exactly as it needs
the levels'. -/
def Expr.allLevelParamsDefined (params : List LevelParam) : Expr md → Bool
  | .bvar _ => true
  | .fvar _ t => t.allLevelParamsDefined params
  | .sort u => u.allParamsDefined params
  | .const _ us => us.all (Level.allParamsDefined params)
  | .app f a => f.allLevelParamsDefined params && a.allLevelParamsDefined params
  | .lam t b m | .forallE t b m =>
    t.allLevelParamsDefined params && b.allLevelParamsDefined params
      && m.pw.paramsDefined params
  | .letE t v b _ => t.allLevelParamsDefined params && v.allLevelParamsDefined params
      && b.allLevelParamsDefined params
  | .lit _ => true
  | .proj _ _ e => e.allLevelParamsDefined params

/-! ### `allLevelParamsDefined`, memoized (task #210 Part B)

The recursor-generation checks ask it of the recursor's type and of
every rule body; a tree walk does not finish on a DAG-shared field
type (task #215's `tower_struct`).  Swapped in by `@[csimp]` (the
arrangement of `IxCK/Kernel/ExprOps.lean`): kernel-checked, no
trust point, the pure walk stays the spec.  Keyed by the node, dropped
after each call (the answer depends on `params`). -/

/-- The memo's invariant: every recorded answer is the real one. -/
def LPMemoInv (params : List LevelParam) (memo : Std.HashMap (Expr md) Bool) : Prop :=
  ∀ (k : Expr md) (r : Bool), memo[k]? = some r → r = k.allLevelParamsDefined params

theorem LPMemoInv.empty {params : List LevelParam} : (LPMemoInv (md := md)) params {} := by
  intro k r h; simp at h

theorem LPMemoInv.insert {params : List LevelParam} {memo : Std.HashMap (Expr md) Bool}
    (hm : LPMemoInv params memo) {e : Expr md} {r : Bool}
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
def Expr.allLevelParamsDefinedGo (params : List LevelParam) (memo : Std.HashMap (Expr md) Bool) :
    (Expr md) → Bool × Std.HashMap (Expr md) Bool
  | .bvar _ => (true, memo)
  | .sort u => (u.allParamsDefined params, memo)
  | .const _ us => (us.all (Level.allParamsDefined params), memo)
  | .lit _ => (true, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap (Expr md) Bool :=
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
        | .letE t v b _ =>
          let (b₁, memo) := allLevelParamsDefinedGo params memo t
          let (b₂, memo) := allLevelParamsDefinedGo params memo v
          let (b₃, memo) := allLevelParamsDefinedGo params memo b
          (b₁ && b₂ && b₃, memo)
        | .proj _ _ sub => allLevelParamsDefinedGo params memo sub
        | e => (e.allLevelParamsDefined params, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `allLevelParamsDefined`.** -/
theorem Expr.allLevelParamsDefinedGo_spec {params : List LevelParam} :
    ∀ (e : Expr md) (memo : Std.HashMap (Expr md) Bool), LPMemoInv params memo →
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
  | letE ty val body _ iht ihv ihb =>
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
def Expr.allLevelParamsDefinedFast (params : List LevelParam) (e : Expr md) : Bool :=
  (allLevelParamsDefinedGo params {} e).1

@[csimp] theorem Expr.allLevelParamsDefined_eq_allLevelParamsDefinedFast :
    @Expr.allLevelParamsDefined = @Expr.allLevelParamsDefinedFast := by
  funext md params e
  exact (allLevelParamsDefinedGo_spec e {} LPMemoInv.empty).1.symm

end Ix.Kernel
