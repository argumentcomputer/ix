module

public import ConLeche.Kernel.Level
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern): its constructors are `public` but the module is
not `@[expose]`d, so a `cases`-then-`rfl` proof about a datum cannot
see the reduct.  `import all` gives that view HERE only; nothing this
module exports depends on it. -/
import all ConLeche.Kernel.PropWhen

@[expose] public section

/-!
# Expression operations

`instantiate1` opens a binder body: the bound variable `bvar 0` is replaced
by a given expression (in practice an `fvar`, which is closed, so no
de Bruijn shifting of the replacement is needed).

`sizeB` is the termination measure for functions that recurse into
instantiated binder bodies: it counts expression nodes but gives every
`fvar` size 1 regardless of its annotated type.  Instantiating a `bvar`
(size 1) with an `fvar` (size 1) preserves it (`sizeB_instantiate1`), so
`sizeB body < sizeB (forallE n ty body)` keeps holding after opening.
-/

namespace ConLeche.Expr

/-- Replace `bvar d` by `v` in `e`, where `d` counts the binders passed on
the way (callers start at the default `d = 0`).  `v` must be closed with
respect to bound variables (an `fvar`, a constant, …); it is not shifted.
Loose `bvar`s above `d` are lowered by one. -/
def instantiate1 (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i = d then v else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1 f v d) (instantiate1 a v d)
  | .lam ty body bi => .lam (instantiate1 ty v d) (instantiate1 body v (d + 1)) bi
  | .forallE ty body bi => .forallE (instantiate1 ty v d) (instantiate1 body v (d + 1)) bi
  | .letE ty val body =>
    .letE (instantiate1 ty v d) (instantiate1 val v d) (instantiate1 body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1 e v d)

/-! ### `instantiate1`, memoized (task #215)

The third row of task #213's tree-size-budget audit: `instantiate1`
inside `openPisAtFvars` (`ConLeche/Kernel/CheckerBase.lean`) opens a
`∀`-telescope one binder at a time, and each step rebuilds the whole
remaining telescope — `O(tree)` per binder on a DAG-shared type.

As with `renameConsts` above, the memoized walk is swapped in by
`@[csimp]`: kernel-checked, no trust point, and the pure definition
stays what every proof consumes.  The memo is keyed by the *node and
the cursor* (`instantiate1`'s answer depends on both) and dropped after
each call, since it also depends on `v`. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def Inst1MemoInv (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → r = instantiate1 k.1 v k.2

theorem Inst1MemoInv.empty {v : Expr} : Inst1MemoInv v {} := by
  intro k r h; simp at h

theorem Inst1MemoInv.insert {v : Expr} {memo : Std.HashMap (Expr × Nat) Expr}
    (hm : Inst1MemoInv v memo) {e : Expr} {d : Nat} {r : Expr}
    (heq : r = instantiate1 e v d) :
    Inst1MemoInv v (memo.insert (e, d) r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `instantiate1`. -/
def instantiate1Go (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr)
    (e : Expr) (d : Nat) : Expr × Std.HashMap (Expr × Nat) Expr :=
  match e with
  | .bvar i => (if i = d then v else if i > d then .bvar (i - 1) else .bvar i, memo)
  | .fvar idx ty => (.fvar idx ty, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[(e, d)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
        match e with
        | .app f a =>
          let (f', memo) := instantiate1Go v memo f d
          let (a', memo) := instantiate1Go v memo a d
          (.app f' a', memo)
        | .lam ty body bi =>
          let (t, memo) := instantiate1Go v memo ty d
          let (b, memo) := instantiate1Go v memo body (d + 1)
          (.lam t b bi, memo)
        | .forallE ty body bi =>
          let (t, memo) := instantiate1Go v memo ty d
          let (b, memo) := instantiate1Go v memo body (d + 1)
          (.forallE t b bi, memo)
        | .letE ty val body =>
          let (t, memo) := instantiate1Go v memo ty d
          let (w, memo) := instantiate1Go v memo val d
          let (b, memo) := instantiate1Go v memo body (d + 1)
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := instantiate1Go v memo sub d
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert (e, d) r)

/-- **The memoized walk is `instantiate1`.** -/
theorem instantiate1Go_spec {v : Expr} :
    ∀ (e : Expr) (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr),
      Inst1MemoInv v memo →
      (instantiate1Go v memo e d).1 = instantiate1 e v d ∧
        Inst1MemoInv v (instantiate1Go v memo e d).2 := by
  intro e
  induction e with
  | bvar i => intro d memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro d memo hm; exact ⟨rfl, hm⟩
  | sort u => intro d memo hm; exact ⟨rfl, hm⟩
  | const n us => intro d memo hm; exact ⟨rfl, hm⟩
  | lit l => intro d memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro d memo hm
    rw [instantiate1Go]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha d memo hm
      obtain ⟨h3, h4⟩ := ihb d _ h2
      refine ⟨by simp [instantiate1, h1, h3], ?_⟩
      exact h4.insert (by simp [instantiate1, h1, h3])
  | lam ty body bi iht ihb =>
    intro d memo hm
    rw [instantiate1Go]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht d memo hm
      obtain ⟨h3, h4⟩ := ihb (d + 1) _ h2
      refine ⟨by simp [instantiate1, h1, h3], ?_⟩
      exact h4.insert (by simp [instantiate1, h1, h3])
  | forallE ty body bi iht ihb =>
    intro d memo hm
    rw [instantiate1Go]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht d memo hm
      obtain ⟨h3, h4⟩ := ihb (d + 1) _ h2
      refine ⟨by simp [instantiate1, h1, h3], ?_⟩
      exact h4.insert (by simp [instantiate1, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro d memo hm
    rw [instantiate1Go]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht d memo hm
      obtain ⟨h3, h4⟩ := ihv d _ h2
      obtain ⟨h5, h6⟩ := ihb (d + 1) _ h4
      refine ⟨by simp [instantiate1, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [instantiate1, h1, h3, h5])
  | proj s i sub ih =>
    intro d memo hm
    rw [instantiate1Go]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih d memo hm
      refine ⟨by simp [instantiate1, h1], ?_⟩
      exact h2.insert (by simp [instantiate1, h1])

/-- The executed `instantiate1` (one memoized DAG walk). -/
def instantiate1Fast (e v : Expr) (d : Nat := 0) : Expr :=
  (instantiate1Go v {} e d).1

@[csimp] theorem instantiate1_eq_instantiate1Fast :
    @instantiate1 = @instantiate1Fast := by
  funext e v d
  exact (instantiate1Go_spec e d {} Inst1MemoInv.empty).1.symm

/-- Bulk instantiation (task #50): substitute the replacement list `vs`
for the bound variables `bvar d, bvar (d + 1), …` in one traversal —
`vs[0]` replaces `bvar d` (the *innermost* binder of a peeled
telescope), `vs[i]` replaces `bvar (d + i)`; loose `bvar`s above the
range are lowered by `vs.length`.

The semantics is by construction the *fold* of `instantiate1`:

  `instantiateList e (v :: vs) d
     = (instantiateList e vs (d + 1)).instantiate1 v d`

(`instantiateList_cons`, unconditional) — so a chain that consumes a
spine `a₁ … aₖ` outermost-first equals one call at the accumulator list
`[aₖ, …, a₁]`.  In the fold, a replacement inserted early is traversed
again by the later `instantiate1` passes; the `bvar` case reproduces
this by recursing into the replacement with the *earlier-listed*
entries (`vs.take i` — the substitutions the fold applies after
inserting `vs[i]`).  On `bvar`-closed replacements (every checker call
site) that recursion is the identity, and the cost is a single
traversal of `e` instead of `vs.length` traversals. -/
def instantiateList (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar j =>
    if j < d then .bvar j
    else if h : j - d < vs.length then
      instantiateList vs[j - d] (vs.take (j - d)) d
    else .bvar (j - vs.length)
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiateList f vs d) (instantiateList a vs d)
  | .lam ty body bi =>
    .lam (instantiateList ty vs d) (instantiateList body vs (d + 1)) bi
  | .forallE ty body bi =>
    .forallE (instantiateList ty vs d) (instantiateList body vs (d + 1)) bi
  | .letE ty val body =>
    .letE (instantiateList ty vs d) (instantiateList val vs d)
      (instantiateList body vs (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiateList e vs d)
termination_by (vs.length, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp [List.length_take]; omega)
    | (apply Prod.Lex.right; simp; omega)

/-! ### `instantiateList`, memoized (task #210 Part B)

`openPisAtFvars` (`ConLeche/Kernel/CheckerBase.lean`) instantiates
each domain of a telescope in one `instantiateList` pass — a tree walk
that does not finish on a DAG-shared domain (task #215's
`tower_struct`).  The same `@[csimp]` arrangement as `instantiate1`
above, keyed by the node and the cursor with the replacement list
fixed; the `bvar` case (the recursion into a replacement, the identity
at every checker site) is the pure function's. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def InstLMemoInv (vs : List Expr) (memo : Std.HashMap (Expr × Nat) Expr) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → r = instantiateList k.1 vs k.2

theorem InstLMemoInv.empty {vs : List Expr} : InstLMemoInv vs {} := by
  intro k r h; simp at h

theorem InstLMemoInv.insert {vs : List Expr} {memo : Std.HashMap (Expr × Nat) Expr}
    (hm : InstLMemoInv vs memo) {e : Expr} {d : Nat} {r : Expr}
    (heq : r = instantiateList e vs d) :
    InstLMemoInv vs (memo.insert (e, d) r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `instantiateList`. -/
def instantiateListGo (vs : List Expr) (memo : Std.HashMap (Expr × Nat) Expr)
    (e : Expr) (d : Nat) : Expr × Std.HashMap (Expr × Nat) Expr :=
  match e with
  | .bvar j => (instantiateList (.bvar j) vs d, memo)
  | .fvar idx ty => (.fvar idx ty, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[(e, d)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
        match e with
        | .app f a =>
          let (f', memo) := instantiateListGo vs memo f d
          let (a', memo) := instantiateListGo vs memo a d
          (.app f' a', memo)
        | .lam ty body bi =>
          let (t, memo) := instantiateListGo vs memo ty d
          let (b, memo) := instantiateListGo vs memo body (d + 1)
          (.lam t b bi, memo)
        | .forallE ty body bi =>
          let (t, memo) := instantiateListGo vs memo ty d
          let (b, memo) := instantiateListGo vs memo body (d + 1)
          (.forallE t b bi, memo)
        | .letE ty val body =>
          let (t, memo) := instantiateListGo vs memo ty d
          let (w, memo) := instantiateListGo vs memo val d
          let (b, memo) := instantiateListGo vs memo body (d + 1)
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := instantiateListGo vs memo sub d
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert (e, d) r)

/-- **The memoized walk is `instantiateList`.** -/
theorem instantiateListGo_spec {vs : List Expr} :
    ∀ (e : Expr) (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr),
      InstLMemoInv vs memo →
      (instantiateListGo vs memo e d).1 = instantiateList e vs d ∧
        InstLMemoInv vs (instantiateListGo vs memo e d).2 := by
  intro e
  induction e with
  | bvar i => intro d memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ =>
    intro d memo hm; exact ⟨by show (Expr.fvar i ty, memo).1 = _; rw [instantiateList], hm⟩
  | sort u => intro d memo hm; exact ⟨by show (Expr.sort u, memo).1 = _; rw [instantiateList], hm⟩
  | const n us =>
    intro d memo hm; exact ⟨by show (Expr.const n us, memo).1 = _; rw [instantiateList], hm⟩
  | lit l => intro d memo hm; exact ⟨by show (Expr.lit l, memo).1 = _; rw [instantiateList], hm⟩
  | app a b iha ihb =>
    intro d memo hm
    rw [instantiateListGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha d memo hm
      obtain ⟨h3, h4⟩ := ihb d _ h2
      refine ⟨by rw [instantiateList]; simp [h1, h3], ?_⟩
      exact h4.insert (by rw [instantiateList]; simp [h1, h3])
  | lam ty body bi iht ihb =>
    intro d memo hm
    rw [instantiateListGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht d memo hm
      obtain ⟨h3, h4⟩ := ihb (d + 1) _ h2
      refine ⟨by rw [instantiateList]; simp [h1, h3], ?_⟩
      exact h4.insert (by rw [instantiateList]; simp [h1, h3])
  | forallE ty body bi iht ihb =>
    intro d memo hm
    rw [instantiateListGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht d memo hm
      obtain ⟨h3, h4⟩ := ihb (d + 1) _ h2
      refine ⟨by rw [instantiateList]; simp [h1, h3], ?_⟩
      exact h4.insert (by rw [instantiateList]; simp [h1, h3])
  | letE ty val body iht ihv ihb =>
    intro d memo hm
    rw [instantiateListGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht d memo hm
      obtain ⟨h3, h4⟩ := ihv d _ h2
      obtain ⟨h5, h6⟩ := ihb (d + 1) _ h4
      refine ⟨by rw [instantiateList]; simp [h1, h3, h5], ?_⟩
      exact h6.insert (by rw [instantiateList]; simp [h1, h3, h5])
  | proj s i sub ih =>
    intro d memo hm
    rw [instantiateListGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih d memo hm
      refine ⟨by rw [instantiateList]; simp [h1], ?_⟩
      exact h2.insert (by rw [instantiateList]; simp [h1])

/-- The executed `instantiateList` (one memoized DAG walk). -/
def instantiateListFast (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  (instantiateListGo vs {} e d).1

@[csimp] theorem instantiateList_eq_instantiateListFast :
    @instantiateList = @instantiateListFast := by
  funext e vs d
  exact (instantiateListGo_spec e d {} InstLMemoInv.empty).1.symm

/-- Bump every loose bound variable `≥ cutoff` by `amount`.  Used to
transport a constructor-telescope field domain (parameters, then prior
fields) into a recursor-rule telescope (parameters, motive, minors,
then prior fields): parameter references must skip the extra motive
and minor binders, and by the zeta expansion's substitution to carry
open let-values under binders. -/
def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c then .bvar (i + amount) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (liftLooseBVars amount c a) (liftLooseBVars amount c b)
  | c, .lam ty body m =>
    .lam (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body) m
  | c, .forallE ty body m =>
    .forallE (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body) m
  | c, .letE ty v body =>
    .letE (liftLooseBVars amount c ty) (liftLooseBVars amount c v)
      (liftLooseBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (liftLooseBVars amount c e)

/-! ### `liftLooseBVars`, memoized (task #210 Part B)

The recursor generators lift every constructor field domain into the
rule and recursor telescopes; on a DAG-shared field type the tree walk
does not finish (task #215's `tower_struct`).  The same `@[csimp]`
arrangement as `instantiate1` above; keyed by the node and the cutoff,
dropped after each call (the answer depends on `amount`). -/

/-- The memo's invariant: every recorded answer is the real one. -/
def LiftMemoInv (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → r = liftLooseBVars amount k.2 k.1

theorem LiftMemoInv.empty {amount : Nat} : LiftMemoInv amount {} := by
  intro k r h; simp at h

theorem LiftMemoInv.insert {amount : Nat} {memo : Std.HashMap (Expr × Nat) Expr}
    (hm : LiftMemoInv amount memo) {e : Expr} {c : Nat} {r : Expr}
    (heq : r = liftLooseBVars amount c e) :
    LiftMemoInv amount (memo.insert (e, c) r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `liftLooseBVars`. -/
def liftLooseBVarsGo (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr)
    (e : Expr) (c : Nat) : Expr × Std.HashMap (Expr × Nat) Expr :=
  match e with
  | .bvar i => (if i ≥ c then .bvar (i + amount) else .bvar i, memo)
  | .fvar i ty => (.fvar i ty, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[(e, c)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
        match e with
        | .app a b =>
          let (a', memo) := liftLooseBVarsGo amount memo a c
          let (b', memo) := liftLooseBVarsGo amount memo b c
          (.app a' b', memo)
        | .lam ty body m =>
          let (t, memo) := liftLooseBVarsGo amount memo ty c
          let (b, memo) := liftLooseBVarsGo amount memo body (c + 1)
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := liftLooseBVarsGo amount memo ty c
          let (b, memo) := liftLooseBVarsGo amount memo body (c + 1)
          (.forallE t b m, memo)
        | .letE ty v body =>
          let (t, memo) := liftLooseBVarsGo amount memo ty c
          let (w, memo) := liftLooseBVarsGo amount memo v c
          let (b, memo) := liftLooseBVarsGo amount memo body (c + 1)
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := liftLooseBVarsGo amount memo sub c
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert (e, c) r)

/-- **The memoized walk is `liftLooseBVars`.** -/
theorem liftLooseBVarsGo_spec {amount : Nat} :
    ∀ (e : Expr) (c : Nat) (memo : Std.HashMap (Expr × Nat) Expr),
      LiftMemoInv amount memo →
      (liftLooseBVarsGo amount memo e c).1 = liftLooseBVars amount c e ∧
        LiftMemoInv amount (liftLooseBVarsGo amount memo e c).2 := by
  intro e
  induction e with
  | bvar i => intro c memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro c memo hm; exact ⟨rfl, hm⟩
  | sort u => intro c memo hm; exact ⟨rfl, hm⟩
  | const n us => intro c memo hm; exact ⟨rfl, hm⟩
  | lit l => intro c memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro c memo hm
    rw [liftLooseBVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha c memo hm
      obtain ⟨h3, h4⟩ := ihb c _ h2
      refine ⟨by simp [liftLooseBVars, h1, h3], ?_⟩
      exact h4.insert (by simp [liftLooseBVars, h1, h3])
  | lam ty body bi iht ihb =>
    intro c memo hm
    rw [liftLooseBVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht c memo hm
      obtain ⟨h3, h4⟩ := ihb (c + 1) _ h2
      refine ⟨by simp [liftLooseBVars, h1, h3], ?_⟩
      exact h4.insert (by simp [liftLooseBVars, h1, h3])
  | forallE ty body bi iht ihb =>
    intro c memo hm
    rw [liftLooseBVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht c memo hm
      obtain ⟨h3, h4⟩ := ihb (c + 1) _ h2
      refine ⟨by simp [liftLooseBVars, h1, h3], ?_⟩
      exact h4.insert (by simp [liftLooseBVars, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro c memo hm
    rw [liftLooseBVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht c memo hm
      obtain ⟨h3, h4⟩ := ihv c _ h2
      obtain ⟨h5, h6⟩ := ihb (c + 1) _ h4
      refine ⟨by simp [liftLooseBVars, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [liftLooseBVars, h1, h3, h5])
  | proj s i sub ih =>
    intro c memo hm
    rw [liftLooseBVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih c memo hm
      refine ⟨by simp [liftLooseBVars, h1], ?_⟩
      exact h2.insert (by simp [liftLooseBVars, h1])

/-- The executed `liftLooseBVars` (one memoized DAG walk). -/
def liftLooseBVarsFast (amount c : Nat) (e : Expr) : Expr :=
  (liftLooseBVarsGo amount {} e c).1

@[csimp] theorem liftLooseBVars_eq_liftLooseBVarsFast :
    @liftLooseBVars = @liftLooseBVarsFast := by
  funext amount c e
  exact (liftLooseBVarsGo_spec e c {} LiftMemoInv.empty).1.symm

/-! ### `resetMeta` (task #210 Part D)

Every binder's datum reset to the parse placeholder `⟨.never⟩`: the
stream's recursor rules are compared syntactically against the
generated ones (official's replay compares an exported recursor
structurally with the one it generates), and the generated body is
built from ANNOTATED pieces — the stored constructor's normalised field
telescopes and index expressions — while the stream's carries the
placeholder everywhere.  The pure walk is the spec; the executed one is
memoized by `@[csimp]` (the `mentionsConst` arrangement). -/

def resetMeta : Expr → Expr
  | .app f a => .app (resetMeta f) (resetMeta a)
  | .lam ty b _ => .lam (resetMeta ty) (resetMeta b) ⟨.never⟩
  | .forallE ty b _ => .forallE (resetMeta ty) (resetMeta b) ⟨.never⟩
  | .letE ty v b => .letE (resetMeta ty) (resetMeta v) (resetMeta b)
  | .proj s i e => .proj s i (resetMeta e)
  | .fvar i ty => .fvar i (resetMeta ty)
  | e => e

/-- The memo's invariant: every recorded answer is the real one. -/
def ResetMemoInv (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ (k r : Expr), memo[k]? = some r → r = resetMeta k

theorem ResetMemoInv.empty : ResetMemoInv {} := by
  intro k r h; simp at h

theorem ResetMemoInv.insert {memo : Std.HashMap Expr Expr} (hm : ResetMemoInv memo)
    {e r : Expr} (heq : r = resetMeta e) : ResetMemoInv (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `resetMeta`. -/
def resetMetaGo (memo : Std.HashMap Expr Expr) : Expr → Expr × Std.HashMap Expr Expr
  | .bvar i => (.bvar i, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | .fvar i ty =>
          let (t, memo) := resetMetaGo memo ty
          (.fvar i t, memo)
        | .app f a =>
          let (f', memo) := resetMetaGo memo f
          let (a', memo) := resetMetaGo memo a
          (.app f' a', memo)
        | .lam ty body _ =>
          let (t, memo) := resetMetaGo memo ty
          let (b, memo) := resetMetaGo memo body
          (.lam t b ⟨.never⟩, memo)
        | .forallE ty body _ =>
          let (t, memo) := resetMetaGo memo ty
          let (b, memo) := resetMetaGo memo body
          (.forallE t b ⟨.never⟩, memo)
        | .letE ty val body =>
          let (t, memo) := resetMetaGo memo ty
          let (w, memo) := resetMetaGo memo val
          let (b, memo) := resetMetaGo memo body
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := resetMetaGo memo sub
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `resetMeta`.** -/
theorem resetMetaGo_spec :
    ∀ (e : Expr) (memo : Std.HashMap Expr Expr), ResetMemoInv memo →
      (resetMetaGo memo e).1 = resetMeta e ∧ ResetMemoInv (resetMetaGo memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [resetMetaGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [resetMeta, h1], ?_⟩
      exact h2.insert (by simp [resetMeta, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [resetMetaGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [resetMeta, h1, h3], ?_⟩
      exact h4.insert (by simp [resetMeta, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [resetMetaGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [resetMeta, h1, h3], ?_⟩
      exact h4.insert (by simp [resetMeta, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [resetMetaGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [resetMeta, h1, h3], ?_⟩
      exact h4.insert (by simp [resetMeta, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [resetMetaGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [resetMeta, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [resetMeta, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [resetMetaGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [resetMeta, h1], ?_⟩
      exact h2.insert (by simp [resetMeta, h1])

/-- The executed `resetMeta` (one memoized DAG walk). -/
def resetMetaFast (e : Expr) : Expr := (resetMetaGo {} e).1

@[csimp] theorem resetMeta_eq_resetMetaFast : @resetMeta = @resetMetaFast := by
  funext e
  exact (resetMetaGo_spec e {} ResetMemoInv.empty).1.symm

/-- Lower every loose bound variable `≥ cutoff + amount` by `amount`
(loose variables inside the window `[cutoff, cutoff + amount)` are left
untouched — callers certify their absence by the `liftLooseBVars`
roundtrip).  Used by the nested-rule shape certification to read a
recursor's constructor-parameter instantiations out of the
major-premise domain (an `mI`-binder context) into the rule-prefix
context (`rP` binders): `p = (p.lowerBVars (mI - rP) 0).liftLooseBVars
(mI - rP) 0` holds exactly when `p` mentions no index variable. -/
def lowerBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c + amount then .bvar (i - amount) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (lowerBVars amount c a) (lowerBVars amount c b)
  | c, .lam ty body m =>
    .lam (lowerBVars amount c ty) (lowerBVars amount (c + 1) body) m
  | c, .forallE ty body m =>
    .forallE (lowerBVars amount c ty) (lowerBVars amount (c + 1) body) m
  | c, .letE ty v body =>
    .letE (lowerBVars amount c ty) (lowerBVars amount c v)
      (lowerBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (lowerBVars amount c e)

/-- Replace `bvar d` by `v`, *lifting* `v`'s loose `bvar`s past the
binders crossed on the way — the general capture-avoiding substitution
for an open `v` (unlike `instantiate1`, which requires `v` to be
`bvar`-closed).  Let-values are open terms. -/
def instantiate1Lift (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i =>
    if i = d then Expr.liftLooseBVars d 0 v
    else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1Lift f v d) (instantiate1Lift a v d)
  | .lam ty body bi =>
    .lam (instantiate1Lift ty v d) (instantiate1Lift body v (d + 1)) bi
  | .forallE ty body bi =>
    .forallE (instantiate1Lift ty v d) (instantiate1Lift body v (d + 1)) bi
  | .letE ty val body =>
    .letE (instantiate1Lift ty v d) (instantiate1Lift val v d)
      (instantiate1Lift body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1Lift e v d)

/-- Node count with `fvar` counted as a leaf (its annotated type ignored).
Termination measure for recursion into instantiated binder bodies. -/
def sizeB : Expr → Nat
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lit _ => 1
  | .app f a => sizeB f + sizeB a + 1
  | .lam ty body _ | .forallE ty body _ => sizeB ty + sizeB body + 1
  | .letE ty val body => sizeB ty + sizeB val + sizeB body + 1
  | .proj _ _ e => sizeB e + 1

/-- Instantiating with a size-1 replacement preserves `sizeB`. -/
theorem sizeB_instantiate1 (v : Expr) (hv : sizeB v = 1) :
    ∀ (e : Expr) (d : Nat), sizeB (instantiate1 e v d) = sizeB e := by
  intro e
  induction e <;> intro d <;> simp [instantiate1, sizeB, *]
  case bvar i =>
    split
    · exact hv
    · split <;> rfl

/-- Close a binder body: replace `fvar d …` leaves by `bvar k`, bumping
`k` under binders — the inverse of `instantiate1` with a fresh variable
(`fvar` type annotations are not descended into; a well-scoped term has no
`fvar d` inside another variable's annotation). -/
def abstract1 (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx ty => if idx = d then .bvar k else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstract1 f d k) (abstract1 a d k)
  | .lam ty body m => .lam (abstract1 ty d k) (abstract1 body d (k + 1)) m
  | .forallE ty body m => .forallE (abstract1 ty d k) (abstract1 body d (k + 1)) m
  | .letE ty val body =>
    .letE (abstract1 ty d k) (abstract1 val d k) (abstract1 body d (k + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstract1 e d k)

/-- Bulk abstraction (task #72): close `k` binders in one traversal —
replace `fvar (d + i) …` leaves (`i < k`) by the bound variable of the
`i`-th binder counted outermost-first, i.e. `bvar (c + (d + k - 1 - idx))`
at the traversal cursor `c` (bumped under binders; `fvar` type
annotations are not descended into, as in `abstract1`).  The semantics
is by construction the *fold* of `abstract1`, innermost binder first:

  `abstractRange e d (k + 1) c
     = abstractRange (e.abstract1 (d + k) c) d k (c + 1)`

(`abstractRange_succ`, `ConLeche/Verify/Abstract.lean`) — so the nested
per-binder `abstract1` chain of a telescope rebuild equals one
`abstractRange` pass per binder domain and one over the leaf. -/
def abstractRange (e : Expr) (d k : Nat) (c : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx ty =>
    if d ≤ idx ∧ idx < d + k then .bvar (c + (d + k - 1 - idx))
    else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstractRange f d k c) (abstractRange a d k c)
  | .lam ty body m =>
    .lam (abstractRange ty d k c) (abstractRange body d k (c + 1)) m
  | .forallE ty body m =>
    .forallE (abstractRange ty d k c) (abstractRange body d k (c + 1)) m
  | .letE ty val body =>
    .letE (abstractRange ty d k c) (abstractRange val d k c)
      (abstractRange body d k (c + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstractRange e d k c)

/-- Full node count, including `fvar` type annotations.  Termination
measure for predicates that recurse into annotations (but never into
instantiated bodies). -/
def sizeF : Expr → Nat
  | .bvar _ | .sort _ | .const .. | .lit _ => 1
  | .fvar _ ty => sizeF ty + 1
  | .app f a => sizeF f + sizeF a + 1
  | .lam ty body _ | .forallE ty body _ => sizeF ty + sizeF body + 1
  | .letE ty val body => sizeF ty + sizeF val + sizeF body + 1
  | .proj _ _ e => sizeF e + 1

/-- All reachable `fvar` leaves, including (hereditarily) those inside
their type annotations. -/
def fvarLeaves : Expr → List (Nat × Expr)
  | .fvar idx ty => (idx, ty) :: fvarLeaves ty
  | .app f a => fvarLeaves f ++ fvarLeaves a
  | .lam ty b _ | .forallE ty b _ => fvarLeaves ty ++ fvarLeaves b
  | .letE t v b => fvarLeaves t ++ fvarLeaves v ++ fvarLeaves b
  | .proj _ _ e => fvarLeaves e
  | _ => []
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Scope check: every reachable `fvar` index is below `d`,
hereditarily through annotations (the `Bool` mirror of the
verification-side `WScoped`).

Not on any per-memo-op path (task #43): the executed knot's cache
operations run unguarded, justified by the proven call discipline
(`ConLeche/Verify/Cached/DiscC*.lean`; the memoized knot's own
discipline, `ConLeche/Verify/Disc.lean`, went with that knot at task
#221).  Remaining executable call sites are the
scope guards on checker-fabricated terms in `ConLeche/Kernel/Core.lean`
(the stuck-major rescues in `majorToCtor`; the projection
eliminations went with task #175 wiring W5), each O(small
fabricated term) once per fabrication.  TODO(cleanup, task #26):
interning should cache the fvar range per node, making those O(1). -/
def wscopedB : (d : Nat) → Expr → Bool
  | d, .fvar idx ty => idx < d && wscopedB idx ty
  | d, .app f a => wscopedB d f && wscopedB d a
  | d, .lam ty body _ => wscopedB d ty && wscopedB d body
  | d, .forallE ty body _ => wscopedB d ty && wscopedB d body
  | d, .letE ty val body =>
    wscopedB d ty && wscopedB d val && wscopedB d body
  | d, .proj _ _ e => wscopedB d e
  | _, .bvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => true
termination_by _ e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Are all bound-variable references bound within the expression (below
`k` at the root)?  Input declarations must satisfy `looseBVarsBounded 0`.
The pure walk is the specification; the executed function is the
`O(1)` loose-bvar field read (`looseBVarsBoundedFast`, `@[csimp]`
below, task #210 Part B). -/
def looseBVarsBounded (k : Nat) : Expr → Bool
  | .bvar i => i < k
  | .fvar _ _ => true
  | .sort _ | .const _ _ | .lit _ => true
  | .app f a => looseBVarsBounded k f && looseBVarsBounded k a
  | .lam ty body _ | .forallE ty body _ =>
    looseBVarsBounded k ty && looseBVarsBounded (k + 1) body
  | .letE ty val body =>
    looseBVarsBounded k ty && looseBVarsBounded k val && looseBVarsBounded (k + 1) body
  | .proj _ _ e => looseBVarsBounded k e

/-- Is the expression a λ?  The λ-rule's codomain-sort check (task
#152) fires once per λ *chain* — at the innermost binder, whose body
is not itself a λ — because that is the granularity the interned
binder-telescope loop (task #72) can reproduce. -/
def isLam : Expr → Bool
  | .lam .. => true
  | _ => false

/-- The prop-ness annotation of a λ node's meta, `none` off λs — the
head reading the task-#161 chain rule consumes (an outer λ's codomain
prop-ness is its body-λ's own annotation).  Total, so the walks
commute with it structurally (`lamPw_instantiateList_fvars`,
`lamPw_shiftFrom` in `ConLeche/Verify`). -/
def lamPw : Expr → Option PropWhen
  | .lam _ _ mbI => some mbI.pw
  | _ => none

/-- The ∀ twin of `lamPw`: a ∀ node's prop-ness datum, read off the
node.  Task #161 P5 repair — `annotPwPi` reads it to realise the
telescope collapse (`zeronessOf (imax u v) = zeronessOf v`) as a chain
rule, exactly as `annotPwLam` reads `lamPw`. -/
def forallPw : Expr → Option PropWhen
  | .forallE _ _ mbI => some mbI.pw
  | _ => none

/-- Does the expression contain any free variable (`fvar`)?  Input
declarations must be `fvar`-free; the checker introduces `fvar`s only
internally when opening binders. -/
def hasFvar : Expr → Bool
  | .bvar _ | .sort _ | .const .. | .lit _ => false
  | .fvar .. => true
  | .app f a => hasFvar f || hasFvar a
  | .lam ty body _ | .forallE ty body _ => hasFvar ty || hasFvar body
  | .letE ty val body => hasFvar ty || hasFvar val || hasFvar body
  | .proj _ _ e => hasFvar e

/-- The head of an application spine. -/
def getAppFn : Expr → Expr
  | .app f _ => getAppFn f
  | e => e

/-- The arguments of an application spine, outermost last. -/
def getAppArgs : Expr → List Expr
  | .app f a => getAppArgs f ++ [a]
  | _ => []

/-- Apply to a list of arguments. -/
def mkAppN (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => mkAppN (.app f a) as

/-- Rename constants throughout (including inside `fvar` type
annotations and `proj` type names); levels and binders untouched.  Used
to compare a modeled inductive's members against their `_model`
counterparts. -/
def renameConsts (f : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i (renameConsts f ty)
  | .sort u => .sort u
  | .const n us => .const (f n) us
  | .app a b => .app (renameConsts f a) (renameConsts f b)
  | .lam ty body m => .lam (renameConsts f ty) (renameConsts f body) m
  | .forallE ty body m =>
    .forallE (renameConsts f ty) (renameConsts f body) m
  | .letE ty v body =>
    .letE (renameConsts f ty) (renameConsts f v) (renameConsts f body)
  | .lit l => .lit l
  -- Task #175 wiring W5: a `.proj` node's struct name is NOT renamed.
  -- The renaming exists for the modeled-block contract (a public
  -- block's types against its `_model` artifacts, compared with `==`
  -- since task #205, and the fire comparands); a block's own projections can never be
  -- spelled inside its types (their entries do not exist when the
  -- types are annotated), and a `.proj` on any *other* structure names
  -- it the same on both sides — so the rename never had a matching
  -- case here.  Fixing the name keeps the entry-kind readings
  -- (`denote`/`denoteMeta`, which consult the table at the struct name)
  -- rename-invariant by construction (DESIGN, "W5 opening seam").
  | .proj s i e => .proj s i (renameConsts f e)

/-! ### `renameConsts`, memoized (task #215)

`renameConsts` is a plain structural **rebuild**, so on a DAG-shared
argument it costs `O(tree)`, not `O(DAG)` — the second row of task
#213's tree-size-budget audit, and one of the two walkers that kept the
budget on inductive blocks.  It is on the executed path of the modeled
inductive install (`ConLeche/Kernel/Inductives/Modeled.lean`,
`ConLeche/Kernel/DeclCheck.lean`), which meets whole annotated member
types.

The memoized walk below is swapped in by `@[csimp]`, so this is a
*kernel-checked* replacement of the compiled code and no trust point:
the pure definition above is what every proof consumes, and
`renameConstsGo_spec` proves the two equal.  The memo is keyed by the
node itself — the probe is the cached `data` word plus `Expr.beq`,
whose first test is pointer equality — and it is dropped after each
call, since the answer depends on `f`.

No cutoff and no exclusivity read here (unlike `Expr.beqMemo` and the
walks of `ConLeche/Cached/ExprOpsC.lean`, which memoise only what
`withExclusive` reports shared): `renameConsts` is reached only from
the modeled install, once per member type, never from a hot
small-term path — measured on `init-full` at the task's gate. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def RenameMemoInv (f : Name → Name) (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ k v, memo[k]? = some v → v = renameConsts f k

theorem RenameMemoInv.empty {f : Name → Name} : RenameMemoInv f {} := by
  intro k v h; simp at h

theorem RenameMemoInv.insert {f : Name → Name} {memo : Std.HashMap Expr Expr}
    (hm : RenameMemoInv f memo) {e r : Expr} (heq : r = renameConsts f e) :
    RenameMemoInv f (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- Memoized `renameConsts`. -/
def renameConstsGo (f : Name → Name) (memo : Std.HashMap Expr Expr) :
    Expr → Expr × Std.HashMap Expr Expr
  | e@(.bvar _) => (e, memo)
  | e@(.sort _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | .const n us => (.const (f n) us, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | .fvar i ty =>
          let (t, memo) := renameConstsGo f memo ty
          (.fvar i t, memo)
        | .app a b =>
          let (a', memo) := renameConstsGo f memo a
          let (b', memo) := renameConstsGo f memo b
          (.app a' b', memo)
        | .lam ty body m =>
          let (t, memo) := renameConstsGo f memo ty
          let (b, memo) := renameConstsGo f memo body
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := renameConstsGo f memo ty
          let (b, memo) := renameConstsGo f memo body
          (.forallE t b m, memo)
        | .letE ty v body =>
          let (t, memo) := renameConstsGo f memo ty
          let (v', memo) := renameConstsGo f memo v
          let (b, memo) := renameConstsGo f memo body
          (.letE t v' b, memo)
        | .proj s i sub =>
          let (u, memo) := renameConstsGo f memo sub
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `renameConsts`.** -/
theorem renameConstsGo_spec {f : Name → Name} :
    ∀ (e : Expr) {memo : Std.HashMap Expr Expr}, RenameMemoInv f memo →
      (renameConstsGo f memo e).1 = renameConsts f e ∧
        RenameMemoInv f (renameConstsGo f memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [renameConstsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [renameConsts, h1], ?_⟩
      exact h2.insert (by simp [renameConsts, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [renameConstsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [renameConsts, h1, h3], ?_⟩
      exact h4.insert (by simp [renameConsts, h1, h3])
  | lam ty body m iht ihb =>
    intro memo hm
    rw [renameConstsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [renameConsts, h1, h3], ?_⟩
      exact h4.insert (by simp [renameConsts, h1, h3])
  | forallE ty body m iht ihb =>
    intro memo hm
    rw [renameConstsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [renameConsts, h1, h3], ?_⟩
      exact h4.insert (by simp [renameConsts, h1, h3])
  | letE ty v body iht ihv ihb =>
    intro memo hm
    rw [renameConstsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      refine ⟨by simp [renameConsts, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [renameConsts, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [renameConstsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [renameConsts, h1], ?_⟩
      exact h2.insert (by simp [renameConsts, h1])

/-- The executed `renameConsts` (one memoized DAG walk). -/
def renameConstsFast (f : Name → Name) (e : Expr) : Expr :=
  (renameConstsGo f {} e).1

@[csimp] theorem renameConsts_eq_renameConstsFast :
    @renameConsts = @renameConstsFast := by
  funext f e
  exact (renameConstsGo_spec e RenameMemoInv.empty).1.symm

/-- Strip `k` leading lambdas: the binder list (outermost first) and
the body. -/
def stripLams : Nat → Expr → Option (List (Expr × BinderMeta) × Expr)
  | 0, e => some ([], e)
  | k + 1, .lam ty b m =>
    (stripLams k b).map fun (bs, e) => ((ty, m) :: bs, e)
  | _ + 1, _ => none

/-- Strip `k` leading `∀`s: the binder list (outermost first) and the
body. -/
def stripPis : Nat → Expr → Option (List (Expr × BinderMeta) × Expr)
  | 0, e => some ([], e)
  | k + 1, .forallE ty b m =>
    (stripPis k b).map fun (bs, e) => ((ty, m) :: bs, e)
  | _ + 1, _ => none

/-- The body of a syntactic `∀`-telescope (the expression itself when
it is not a `∀`). -/
def piResult : Expr → Expr
  | .forallE _ b _ => piResult b
  | e => e

/-- Instantiate a `∀`-telescope with arguments, in order. -/
def instPis : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ body _, a :: as => instPis (body.instantiate1 a) as
  | _, _ :: _ => none

/-- Instantiate the leading `∀`-binders at the given arguments,
returning each binder's (progressively instantiated) domain together
with the fully instantiated residual. -/
def instPisAt : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e)
  | a :: as, .forallE dom body _ =>
    (instPisAt as (body.instantiate1 a)).map fun (ds, rest) =>
      (dom :: ds, rest)
  | _ :: _, _ => none

/-- `instPisAt` for `λ`-binders. -/
def instLamsAt : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e)
  | a :: as, .lam dom body _ =>
    (instLamsAt as (body.instantiate1 a)).map fun (ds, rest) =>
      (dom :: ds, rest)
  | _ :: _, _ => none

/-! ### Bulk telescope instantiation (task: fields-raw near-cubic)

`instPisAt`/`instLamsAt` fold `instantiate1` over the argument list, so
each argument re-traverses the whole remaining telescope — quadratic in
the telescope, and the per-projection outer loop of the direct
simple-structure install made that cubic.  The `*F` variants below
compute the *same value* (`instPisAtF_eq`/`instLamsAtF_eq`,
`ConLeche/Verify/FastOps.lean`) in **one** pass: the raw binders are
peeled structurally while the pending substitutions accumulate, and
each domain (and the residual) receives them in a single
`instantiateList` traversal.  When the raw telescope is shorter than
the argument list (a binder only *created* by substitution) the `Go`
walk reports `none` and the wrapper falls back to the sequential
spec — so the equality is unconditional. -/

/-- Core of `instPisAtF`: `acc` holds the pending substitutions,
innermost binder first.  Computes
`instPisAt args (e.instantiateList acc)` whenever `e` raw-strips
`args.length` `∀`-binders (`instPisAtFGo_sound`), `none` otherwise. -/
def instPisAtFGo (acc : List Expr) : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e.instantiateList acc)
  | a :: as, .forallE dom body _ =>
    (instPisAtFGo (a :: acc) as body).map fun (ds, rest) =>
      (dom.instantiateList acc :: ds, rest)
  | _ :: _, _ => none

/-- One-pass `instPisAt` (equal to it: `instPisAtF_eq`). -/
def instPisAtF (args : List Expr) (e : Expr) : Option (List Expr × Expr) :=
  match instPisAtFGo [] args e with
  | some r => some r
  | none => instPisAt args e

/-- Core of `instLamsAtF` (the `λ` counterpart of `instPisAtFGo`). -/
def instLamsAtFGo (acc : List Expr) : List Expr → Expr → Option (List Expr × Expr)
  | [], e => some ([], e.instantiateList acc)
  | a :: as, .lam dom body _ =>
    (instLamsAtFGo (a :: acc) as body).map fun (ds, rest) =>
      (dom.instantiateList acc :: ds, rest)
  | _ :: _, _ => none

/-- One-pass `instLamsAt` (equal to it: `instLamsAtF_eq`). -/
def instLamsAtF (args : List Expr) (e : Expr) : Option (List Expr × Expr) :=
  match instLamsAtFGo [] args e with
  | some r => some r
  | none => instLamsAt args e

/-- The type annotation of a free-variable leaf (the expression itself
otherwise; used to read the domains off an opened telescope's
variables). -/
def fvarTypeD : Expr → Expr
  | .fvar _ ty => ty
  | e => e

/-- Instantiate a telescope-context expression at an argument spine:
`bvar t` is replaced by the first argument, descending (the per-domain
effect of peeling a `t + 1`-binder telescope at the spine; the
verification's `instSeq`).  Used to evaluate a nested-auxiliary rule's
stored constructor-parameter instantiations at the recursor's actual
arguments. -/
def instSpine : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSpine as (t - 1) (e.instantiate1 a t)

/-- A recursor rule is *canonical* when its constructor's parameters
are exactly the recursor's own leading arguments: the major premise's
type applies the eliminated family to the first `cnP` telescope
variables.  Rules for nested auxiliary constructors (whose parameters
are instantiations like `Array Syntax`) are not canonical; they are
stored `.nested` when the certification against the model's `iota_j`
theorem succeeds (see `checkIotaThmN`) and `.inert` otherwise —
`iotaRec` never fires an inert rule, so it carries no fold
obligation. -/
def recRulePlain (recTy : Expr) (mI rP cnP : Nat) : Bool :=
  decide (cnP ≤ rP) && decide (rP ≤ mI) &&
  match recTy.stripPis mI with
  | some (_, .forallE dom _ _) =>
    dom.getAppArgs.take cnP ==
      (List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))
  | _ => false

/-- Convert the first `k` `∀`-binders into `λ`-binders over a body.

The copied binder metadata keeps only the display info: a ∀'s `pw`
claims the *codomain*'s prop-ness, which is not the λ's claim (the sort
of the body's *type*), so carrying it over would be a wrong annotation.
The result is emitted at the parse placeholder `.never` and **every
consumer must run the annotate pass over it before storing or using
it** — audited: `CheckerS.checkProjRule` and `CheckerBase`'s projection
rule builder feed `ops.annotate` (DESIGN.md, task #161,
manufacture-site audit row 9; the third consumer, `annotateProjRec`,
went with task #175 wiring W5). -/
def pisToLams : Nat → Expr → Expr → Option Expr
  | 0, _, body => some body
  | k + 1, .forallE ty rest _, body =>
    (pisToLams k rest body).map fun b => .lam ty b ⟨.never⟩
  | _ + 1, _, _ => none

/-- Replace the body under the first `k` `∀`-binders (binder domains and
names kept, codomain-sort annotations reset — the caller annotates). -/
def replacePiBody : Nat → Expr → Expr → Option Expr
  | 0, _, b => some b
  | k + 1, .forallE ty rest m, b =>
    (replacePiBody k rest b).map fun r => .forallE ty r ⟨m.pw⟩
  | _ + 1, _, _ => none

/-- The length of the leading `∀`-telescope. -/
def piArity : Expr → Nat
  | .forallE _ b _ => piArity b + 1
  | _ => 0

/-- The result sort at the end of a `∀`-telescope. -/
def resultSort : Expr → Option Level
  | .forallE _ b _ => resultSort b
  | .sort u => some u
  | _ => none

/-! ## Derived-field spec functions, and their exactness

The four `@[computed_field]`s of `Expr` (`ConLeche/Kernel/Expr.lean`) are
declared by their recurrences; these are the same recurrences written
as ordinary definitions, together with the equivalences that make a
field read license the traversal cutoff it guards.  Self-contained:
they mention nothing but `Expr`.

They lived in `ConLeche/Kernel/ArenaWF.lean` (the parallel-array
exactness proofs) and `ConLeche/Verify/IExpr.lean` until task #172's
interned removal; the cached engine's field facts
(`ConLeche/Verify/Cached/Erase.lean`) are stated against them. -/

/-- The least `k` with `looseBVarsBounded k` (the spec function of the
eager `bvarBs` entries). -/
def _root_.ConLeche.Expr.bvarBound : Expr → Nat
  | .bvar i => i + 1
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max f.bvarBound a.bvarBound
  | .lam ty body _ | .forallE ty body _ =>
    max ty.bvarBound (body.bvarBound - 1)
  | .letE ty val body =>
    max (max ty.bvarBound val.bvarBound) (body.bvarBound - 1)
  | .proj _ _ e => e.bvarBound

/-- `bvarBound` is exact for `looseBVarsBounded`. -/
theorem looseBVarsBounded_iff {x : Expr} :
    ∀ {k : Nat}, x.looseBVarsBounded k = true ↔ x.bvarBound ≤ k := by
  induction x <;> intro k <;>
    (try simp [Expr.looseBVarsBounded, Expr.bvarBound, Nat.max_le, *]) <;>
    omega

/-- The least `d` with `fvarsBelow d` (the spec function of the eager
`fvarBs` entries; `fvar` type annotations are not descended, matching
`fvarsBelow` and the abstraction traversals). -/
def _root_.ConLeche.Expr.fvarRange : Expr → Nat
  | .fvar idx _ => idx + 1
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max f.fvarRange a.fvarRange
  | .lam ty body _ | .forallE ty body _ =>
    max ty.fvarRange body.fvarRange
  | .letE ty val body =>
    max (max ty.fvarRange val.fvarRange) body.fvarRange
  | .proj _ _ e => e.fvarRange

/-- A term is fvar-free iff its range is zero. -/
theorem hasFvar_eq_false_iff {x : Expr} :
    x.hasFvar = false ↔ x.fvarRange = 0 := by
  induction x <;>
    simp_all [Expr.hasFvar, Expr.fvarRange, Nat.max_eq_zero_iff,
      and_assoc]

/-- A term has a reachable fvar leaf iff its range is nonzero. -/
theorem fvarRange_bne_zero {x : Expr} : (x.fvarRange != 0) = x.hasFvar := by
  cases hh : x.hasFvar with
  | false => simp [hasFvar_eq_false_iff.mp hh]
  | true =>
    have hne : x.fvarRange ≠ 0 := by
      intro h0
      rw [hasFvar_eq_false_iff.mpr h0] at hh
      cases hh
    simpa using hne

/-! ## The saturated branch of the packed range fields (task #167)

`Expr.bvarBRaw`/`Expr.fvarBRaw` (`Kernel/Expr.lean`) are the packed
word's 15-bit range fields; they *saturate* at `satRange`.  The
accessors the checker reads — `Expr.bvarB`, `Expr.fvarB` — stay
**exact**: below saturation they are the field, and at saturation they
fall back to a memoized recomputation of the very same recurrence.

Two consequences, and they are the point of the design:

* **no lemma weakens** — `bvarB_eq`/`fvarB_eq`
  (`Verify/Cached/Erase.lean`) are still plain equations with the spec
  functions, so no skip site grows a guard and no invariant is
  threaded anywhere;
* **what saturation costs is time, not truth** — the `O(1)` field read
  becomes an `O(DAG)` walk, and only on a term with `satRange` loose
  bvars (or fvar levels).  The measured maxima on the real streams are
  213 (`init-full`), 488 (`grind-ring-5`) and 4000 (`app-lam`, the
  deepest artificial workload) against `satRange = 32767`.

The walks are **memoized** (an `Std.HashMap` keyed by the node) so
that even the fallback stays linear in the DAG rather than the
unfolded tree — the standing "no unmemoized traversals in executable
paths" rule applies to the saturated branch too. -/

/-- Memoized `bvarBound` (the saturated branch's exact recomputation). -/
def bvarBoundGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .bvar i => (i + 1, memo)
      | .fvar _ _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := bvarBoundGo memo f
        let (ra, memo) := bvarBoundGo memo a
        (max rf ra, memo)
      | .lam ty body _ | .forallE ty body _ =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rb, memo) := bvarBoundGo memo body
        (max rt (rb - 1), memo)
      | .letE ty val body =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rv, memo) := bvarBoundGo memo val
        let (rb, memo) := bvarBoundGo memo body
        (max (max rt rv) (rb - 1), memo)
      | .proj _ _ sub => bvarBoundGo memo sub
    (r, memo.insert e r)

@[inherit_doc bvarBoundGo]
def bvarBoundMemo (e : Expr) : Nat := (bvarBoundGo {} e).1

/-- Memoized `fvarRange` (the saturated branch's exact
recomputation). -/
def fvarRangeGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .fvar idx _ => (idx + 1, memo)
      | .bvar _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := fvarRangeGo memo f
        let (ra, memo) := fvarRangeGo memo a
        (max rf ra, memo)
      | .lam ty body _ | .forallE ty body _ =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rb, memo) := fvarRangeGo memo body
        (max rt rb, memo)
      | .letE ty val body =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rv, memo) := fvarRangeGo memo val
        let (rb, memo) := fvarRangeGo memo body
        (max (max rt rv) rb, memo)
      | .proj _ _ sub => fvarRangeGo memo sub
    (r, memo.insert e r)

@[inherit_doc fvarRangeGo]
def fvarRangeMemo (e : Expr) : Nat := (fvarRangeGo {} e).1

/-- **The loose-bvar bound the checker reads**: the packed field, or —
on the saturated branch alone — the exact memoized recomputation.
Equal to `Expr.bvarBound` unconditionally (`bvarB_eq`). -/
@[inline] def bvarB (e : Expr) : Nat :=
  let r := e.bvarBRaw
  if r == satRange then bvarBoundMemo e else r

/-- **The fvar range the checker reads**: the packed field, or — on the
saturated branch alone — the exact memoized recomputation.  Equal to
`Expr.fvarRange` unconditionally (`fvarB_eq`). -/
@[inline] def fvarB (e : Expr) : Nat :=
  let r := e.fvarBRaw
  if r == satRange then fvarRangeMemo e else r


/-! ### The range fields are exact; `looseBVarsBounded` and `hasFvar` read them (task #210 Part B)

Moved here from `Verify/Cached/Erase.lean` (task #172 B3a) so that the
executed `looseBVarsBounded` and `hasFvar` can be the `O(1)` field
reads: the tree walks did not finish on task #215's `tower_struct` (a
depth-60 DAG tower in a structure field), where the recursor-generation
checks ask them of the block's types.  Swapped in by `@[csimp]`, as the
memos above: kernel-checked, no trust point, the pure walks stay the
specs. -/

/-- The packed loose-bvar field is `bvarBound` wherever it did not
saturate. -/
theorem bvarBRaw_exact : ∀ e : Expr, e.bvarBRaw < satRange →
    e.bvarBRaw = bvarBound e := by
  intro e
  induction e with
  | bvar i => intro h; simp_all [satRange, bvarBound]; omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ =>
    intro _; simp [bvarBound]
  | app f a ihf iha =>
    intro h
    rw [bvarBRaw_app] at h ⊢
    rw [ihf (by omega), iha (by omega), bvarBound]
  | lam ty b m iht ihb =>
    intro h
    rw [bvarBRaw_lam] at h ⊢
    have hb : b.bvarBRaw ≠ satRange := by
      intro hb'; rw [hb'] at h; simp at h; omega
    have hb2 : b.bvarBRaw < satRange := by
      have := bvarBRaw_lt b; simp [satRange] at *; omega
    rw [if_neg hb, iht (by omega), ihb hb2, bvarBound]
  | forallE ty b m iht ihb =>
    intro h
    rw [bvarBRaw_forallE] at h ⊢
    have hb : b.bvarBRaw ≠ satRange := by
      intro hb'; rw [hb'] at h; simp at h; omega
    have hb2 : b.bvarBRaw < satRange := by
      have := bvarBRaw_lt b; simp [satRange] at *; omega
    rw [if_neg hb, iht (by omega), ihb hb2, bvarBound]
  | letE ty v b iht ihv ihb =>
    intro h
    rw [bvarBRaw_letE] at h ⊢
    have hb : b.bvarBRaw ≠ satRange := by
      intro hb'; rw [hb'] at h; simp at h; omega
    have hb2 : b.bvarBRaw < satRange := by
      have := bvarBRaw_lt b; simp [satRange] at *; omega
    rw [if_neg hb, iht (by omega), ihv (by omega), ihb hb2, bvarBound]
  | proj s i sub ih =>
    intro h
    rw [bvarBRaw_proj] at h ⊢
    rw [ih h, bvarBound]

/-- The `bvarBound` walk's memo invariant. -/
def MemoBInv (memo : Std.HashMap Expr Nat) : Prop :=
  ∀ (e : Expr) (r : Nat), memo[e]? = some r → r = bvarBound e

theorem MemoBInv.empty : MemoBInv {} := by
  intro e r h; simp at h

theorem MemoBInv.insert {memo : Std.HashMap Expr Nat} (hm : MemoBInv memo)
    {e : Expr} {r : Nat} (heq : r = bvarBound e) :
    MemoBInv (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← (beq_iff_eq ..).mp hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The memoized `bvarBound` walk agrees with `bvarBound`.** -/
theorem bvarBoundGo_spec : ∀ (e : Expr) {memo : Std.HashMap Expr Nat},
    MemoBInv memo →
      (bvarBoundGo memo e).1 = bvarBound e ∧
        MemoBInv (bvarBoundGo memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | fvar idx ty _ | sort u | const n us | lit l =>
    intro memo hm
    rw [bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | app f a ihf iha =>
    intro memo hm
    rw [bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ihf hm
      obtain ⟨h2, hm2⟩ := iha hm1
      refine ⟨by simp [h1, h2, bvarBound], hm2.insert ?_⟩
      simp [h1, h2, bvarBound]
  | lam ty b m iht ihb | forallE ty b m iht ihb =>
    intro memo hm
    rw [bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihb hm1
      refine ⟨by simp [h1, h2, bvarBound], hm2.insert ?_⟩
      simp [h1, h2, bvarBound]
  | letE ty v b iht ihv ihb =>
    intro memo hm
    rw [bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihv hm1
      obtain ⟨h3, hm3⟩ := ihb hm2
      refine ⟨by simp [h1, h2, h3, bvarBound], hm3.insert ?_⟩
      simp [h1, h2, h3, bvarBound]
  | proj s i sub ih =>
    intro memo hm
    rw [bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ih hm
      refine ⟨by simp [h1, bvarBound], hm1.insert ?_⟩
      simp [h1, bvarBound]

@[inherit_doc bvarBoundGo_spec]
theorem bvarBoundMemo_eq (e : Expr) :
    bvarBoundMemo e = bvarBound e :=
  (bvarBoundGo_spec e MemoBInv.empty).1

/-- The `bvarB` field is `bvarBound`. -/
theorem bvarB_eq : ∀ e : Expr, e.bvarB = bvarBound e := by
  intro e
  show (if e.bvarBRaw == satRange then bvarBoundMemo e
    else e.bvarBRaw) = _
  split
  · rename_i h; exact bvarBoundMemo_eq e
  · rename_i h
    have hne : e.bvarBRaw ≠ satRange := by simpa using h
    have := bvarBRaw_lt e
    exact bvarBRaw_exact e (by simp [satRange] at *; omega)

/-- The packed fvar-range field is `fvarRange` wherever it did not
saturate. -/
theorem fvarBRaw_exact : ∀ e : Expr, e.fvarBRaw < satRange →
    e.fvarBRaw = fvarRange e := by
  intro e
  induction e with
  | fvar idx _ _ => intro h; simp_all [satRange, fvarRange]; omega
  | bvar _ | sort _ | const _ _ | lit _ => intro _; simp [fvarRange]
  | app f a ihf iha =>
    intro h
    rw [fvarBRaw_app] at h ⊢
    rw [ihf (by omega), iha (by omega), fvarRange]
  | lam ty b m iht ihb =>
    intro h
    rw [fvarBRaw_lam] at h ⊢
    rw [iht (by omega), ihb (by omega), fvarRange]
  | forallE ty b m iht ihb =>
    intro h
    rw [fvarBRaw_forallE] at h ⊢
    rw [iht (by omega), ihb (by omega), fvarRange]
  | letE ty v b iht ihv ihb =>
    intro h
    rw [fvarBRaw_letE] at h ⊢
    rw [iht (by omega), ihv (by omega), ihb (by omega), fvarRange]
  | proj s i sub ih =>
    intro h
    rw [fvarBRaw_proj] at h ⊢
    rw [ih h, fvarRange]

/-- The `fvarRange` walk's memo invariant. -/
def MemoFInv (memo : Std.HashMap Expr Nat) : Prop :=
  ∀ (e : Expr) (r : Nat), memo[e]? = some r → r = fvarRange e

theorem MemoFInv.empty : MemoFInv {} := by
  intro e r h; simp at h

theorem MemoFInv.insert {memo : Std.HashMap Expr Nat} (hm : MemoFInv memo)
    {e : Expr} {r : Nat} (heq : r = fvarRange e) :
    MemoFInv (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← (beq_iff_eq ..).mp hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The memoized `fvarRange` walk agrees with `fvarRange`.** -/
theorem fvarRangeGo_spec : ∀ (e : Expr) {memo : Std.HashMap Expr Nat},
    MemoFInv memo →
      (fvarRangeGo memo e).1 = fvarRange e ∧
        MemoFInv (fvarRangeGo memo e).2 := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro memo hm
    rw [fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | bvar i | sort u | const n us | lit l =>
    intro memo hm
    rw [fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | app f a ihf iha =>
    intro memo hm
    rw [fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ihf hm
      obtain ⟨h2, hm2⟩ := iha hm1
      refine ⟨by simp [h1, h2, fvarRange], hm2.insert ?_⟩
      simp [h1, h2, fvarRange]
  | lam ty b m iht ihb | forallE ty b m iht ihb =>
    intro memo hm
    rw [fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihb hm1
      refine ⟨by simp [h1, h2, fvarRange], hm2.insert ?_⟩
      simp [h1, h2, fvarRange]
  | letE ty v b iht ihv ihb =>
    intro memo hm
    rw [fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihv hm1
      obtain ⟨h3, hm3⟩ := ihb hm2
      refine ⟨by simp [h1, h2, h3, fvarRange], hm3.insert ?_⟩
      simp [h1, h2, h3, fvarRange]
  | proj s i sub ih =>
    intro memo hm
    rw [fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ih hm
      refine ⟨by simp [h1, fvarRange], hm1.insert ?_⟩
      simp [h1, fvarRange]

@[inherit_doc fvarRangeGo_spec]
theorem fvarRangeMemo_eq (e : Expr) :
    fvarRangeMemo e = fvarRange e :=
  (fvarRangeGo_spec e MemoFInv.empty).1

/-- The `fvarB` field is `fvarRange`. -/
theorem fvarB_eq : ∀ e : Expr, e.fvarB = fvarRange e := by
  intro e
  show (if e.fvarBRaw == satRange then fvarRangeMemo e
    else e.fvarBRaw) = _
  split
  · rename_i h; exact fvarRangeMemo_eq e
  · rename_i h
    have hne : e.fvarBRaw ≠ satRange := by simpa using h
    have := fvarBRaw_lt e
    exact fvarBRaw_exact e (by simp [satRange] at *; omega)

/-- The executed `hasFvar`: the fvar-range field read. -/
def hasFvarFast (e : Expr) : Bool := e.fvarB != 0

@[csimp] theorem hasFvar_eq_hasFvarFast : @hasFvar = @hasFvarFast := by
  funext e
  unfold hasFvarFast
  rw [fvarB_eq]
  exact fvarRange_bne_zero.symm

/-- The executed `looseBVarsBounded`: the loose-bvar field read. -/
def looseBVarsBoundedFast (k : Nat) (e : Expr) : Bool := decide (e.bvarB ≤ k)

@[csimp] theorem looseBVarsBounded_eq_looseBVarsBoundedFast :
    @looseBVarsBounded = @looseBVarsBoundedFast := by
  funext k e
  unfold looseBVarsBoundedFast
  rw [bvarB_eq]
  by_cases h : e.bvarBound ≤ k
  · rw [looseBVarsBounded_iff.mpr h, decide_eq_true h]
  · rw [decide_eq_false h]
    cases hb : looseBVarsBounded k e with
    | false => rfl
    | true => exact absurd (looseBVarsBounded_iff.mp hb) h


/-! ### `abstract1` reads the fvar-range field, and memoizes
(tasks #226, #233)

`abstract1` closes a binder body by turning `fvar d` leaves into
`bvar k`, and it rebuilds every node on the way — so on a
DAG-shared term it is `O(tree)`.  It is the walk the native install
route runs per binder (`closeTelescope`, `normPosDom` in
`Kernel/Inductives/SumInstall.lean`), and
`tests/e2e/tower_proj.ndjson` — a two-field structure whose field
types carry a depth-60 shared tower — exhausts memory on it.

The remedy is the ONE the packed range fields already license (task
#210 Part B, and the cached twin `Cached.abstract1` has had it all
along): **a node whose fvar range is at or below `d` contains no
`fvar d`, so abstraction returns it unchanged.**  Every closed
subterm — which is what a shared tower is — is answered by an `O(1)`
field read.  `abstract1_of_fvarRange_le` is the identity, `fvarB_eq`
says the field is the range, and `@[csimp]` swaps the guarded walk in
for the pure one: kernel-checked, no trust point, and the pure
definition stays the one every proof consumes.

**The cutoff is not the whole answer** (task #233).  It stops the walk
at a subterm that cannot contain `fvar d`; it cannot stop it at one
that does.  A tower built *over* the very variable being abstracted —
`tests/e2e/tower_usedlater.ndjson`, whose field type is a depth-60
doubling tower on the first field, which the install opens as an fvar
— has `fvarB > d` at every shared node, so the rebuild is entered once
per path.  So the walk below is BOTH: the `O(1)` cutoff first, then
`abstract1Go`'s memo, keyed by the node and the binder cursor. -/

/-- Abstraction at or above the fvar range is the identity. -/
theorem abstract1_of_fvarRange_le :
    ∀ (e : Expr) (d k : Nat), e.fvarRange ≤ d → abstract1 e d k = e := by
  intro e
  induction e <;> intro d k h <;>
    simp_all [abstract1, Expr.fvarRange, Nat.max_le] <;> omega

/-- The memo's invariant: every recorded answer is the real one. -/
def Abs1MemoInv (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → r = abstract1 k.1 d k.2

theorem Abs1MemoInv.empty {d : Nat} : Abs1MemoInv d {} := by
  intro k r h; simp at h

theorem Abs1MemoInv.insert {d : Nat} {memo : Std.HashMap (Expr × Nat) Expr}
    (hm : Abs1MemoInv d memo) {e : Expr} {k : Nat} {r : Expr}
    (heq : r = abstract1 e d k) :
    Abs1MemoInv d (memo.insert (e, k) r) := by
  intro key r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm key r' hk

/-- The executed `abstract1`: the fvar-range field read cuts the walk
off at every node that cannot contain `fvar d`, and the memo shares
the rebuild of every node that can (task #233 — the cutoff and the
memo are complementary: a term whose shared tower is built *over* the
fvar being abstracted passes the cutoff at every node and was rebuilt
once per path).  The memo is keyed by the node and the binder cursor
`k` (the abstraction target `bvar k` moves under binders) and dropped
after each call, since it also depends on `d`. -/
def abstract1Go (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr)
    (e : Expr) (k : Nat) : Expr × Std.HashMap (Expr × Nat) Expr :=
  if e.fvarB ≤ d then (e, memo) else
  match e with
  | .bvar i => (.bvar i, memo)
  | .fvar idx ty => (if idx = d then .bvar k else .fvar idx ty, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[(e, k)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
        match e with
        | .app f a =>
          let (f', memo) := abstract1Go d memo f k
          let (a', memo) := abstract1Go d memo a k
          (.app f' a', memo)
        | .lam ty body m =>
          let (t, memo) := abstract1Go d memo ty k
          let (b, memo) := abstract1Go d memo body (k + 1)
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := abstract1Go d memo ty k
          let (b, memo) := abstract1Go d memo body (k + 1)
          (.forallE t b m, memo)
        | .letE ty val body =>
          let (t, memo) := abstract1Go d memo ty k
          let (w, memo) := abstract1Go d memo val k
          let (b, memo) := abstract1Go d memo body (k + 1)
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := abstract1Go d memo sub k
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert (e, k) r)

/-- **The memoized walk is `abstract1`.** -/
theorem abstract1Go_spec {d : Nat} :
    ∀ (e : Expr) (k : Nat) (memo : Std.HashMap (Expr × Nat) Expr),
      Abs1MemoInv d memo →
      (abstract1Go d memo e k).1 = abstract1 e d k ∧
        Abs1MemoInv d (abstract1Go d memo e k).2 := by
  intro e
  induction e with
  | bvar i =>
    intro k memo hm
    rw [abstract1Go]; split <;> exact ⟨rfl, hm⟩
  | sort u =>
    intro k memo hm
    rw [abstract1Go]; split <;> exact ⟨rfl, hm⟩
  | const n us =>
    intro k memo hm
    rw [abstract1Go]; split <;> exact ⟨rfl, hm⟩
  | lit l =>
    intro k memo hm
    rw [abstract1Go]; split <;> exact ⟨rfl, hm⟩
  | fvar i ty _ =>
    intro k memo hm
    rw [abstract1Go]; split
    · rename_i h
      exact ⟨(abstract1_of_fvarRange_le _ d k (by rwa [← fvarB_eq])).symm, hm⟩
    · exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro k memo hm
    rw [abstract1Go]
    split
    · rename_i h
      exact ⟨(abstract1_of_fvarRange_le _ d k (by rwa [← fvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ihf k memo hm
        obtain ⟨h3, h4⟩ := iha k _ h2
        refine ⟨by simp [abstract1, h1, h3], ?_⟩
        exact h4.insert (by simp [abstract1, h1, h3])
  | lam ty body m iht ihb =>
    intro k memo hm
    rw [abstract1Go]
    split
    · rename_i h
      exact ⟨(abstract1_of_fvarRange_le _ d k (by rwa [← fvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht k memo hm
        obtain ⟨h3, h4⟩ := ihb (k + 1) _ h2
        refine ⟨by simp [abstract1, h1, h3], ?_⟩
        exact h4.insert (by simp [abstract1, h1, h3])
  | forallE ty body m iht ihb =>
    intro k memo hm
    rw [abstract1Go]
    split
    · rename_i h
      exact ⟨(abstract1_of_fvarRange_le _ d k (by rwa [← fvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht k memo hm
        obtain ⟨h3, h4⟩ := ihb (k + 1) _ h2
        refine ⟨by simp [abstract1, h1, h3], ?_⟩
        exact h4.insert (by simp [abstract1, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro k memo hm
    rw [abstract1Go]
    split
    · rename_i h
      exact ⟨(abstract1_of_fvarRange_le _ d k (by rwa [← fvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht k memo hm
        obtain ⟨h3, h4⟩ := ihv k _ h2
        obtain ⟨h5, h6⟩ := ihb (k + 1) _ h4
        refine ⟨by simp [abstract1, h1, h3, h5], ?_⟩
        exact h6.insert (by simp [abstract1, h1, h3, h5])
  | proj sn i sub ih =>
    intro k memo hm
    rw [abstract1Go]
    split
    · rename_i h
      exact ⟨(abstract1_of_fvarRange_le _ d k (by rwa [← fvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih k memo hm
        refine ⟨by simp [abstract1, h1], ?_⟩
        exact h2.insert (by simp [abstract1, h1])

@[inherit_doc abstract1Go]
def abstract1Fast (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  (abstract1Go d {} e k).1

@[csimp] theorem abstract1_eq_abstract1Fast :
    @abstract1 = @abstract1Fast := by
  funext e d k
  exact (abstract1Go_spec e k {} Abs1MemoInv.empty).1.symm

/-! ### `lowerBVars` reads the loose-bvar bound, and memoizes

`lowerBVars` rebuilds every node it walks, so on a DAG-shared term it
is `O(tree)` — the same shape `abstract1` had before task #233.  It is
the walk the modeled route runs on the rule-prefix pins
(`Kernel/Inductives/Modeled.lean`, `Kernel/DeclCheck.lean`) and the
in-process modeller runs on the nested rung's motives, pins and
domains (`Frontend/InModel/Nested.lean`), and
`tests/e2e/tower_nested.ndjson` — a nested block whose constructor
carries a depth-60 shared tower over the constructor's own first
field — exhausts memory on it.

Both remedies, as `abstract1` carries both: a node whose loose-bvar
bound is at or below `c + amount` holds no variable the lowering
moves, so it comes back unchanged from an `O(1)` field read; and where
the bound is above it, the memo — keyed by the node and the CUTOFF,
which shifts under binders — shares the rebuild across the paths that
reach a shared node. -/

/-- Lowering a term whose loose variables all sit below the window is
the identity. -/
theorem lowerBVars_of_bvarBound_le :
    ∀ (e : Expr) (amount c : Nat), e.bvarBound ≤ c + amount →
      lowerBVars amount c e = e := by
  intro e
  induction e with
  | bvar i =>
    intro amount c h
    rw [Expr.bvarBound] at h
    rw [lowerBVars, if_neg (by omega)]
  | fvar i ty _ => intro amount c _; rfl
  | sort u => intro amount c _; rfl
  | const n us => intro amount c _; rfl
  | lit l => intro amount c _; rfl
  | app f a ihf iha =>
    intro amount c h
    rw [Expr.bvarBound, Nat.max_le] at h
    rw [lowerBVars, ihf amount c h.1, iha amount c h.2]
  | lam ty body m iht ihb =>
    intro amount c h
    rw [Expr.bvarBound, Nat.max_le] at h
    rw [lowerBVars, iht amount c h.1, ihb amount (c + 1) (by omega)]
  | forallE ty body m iht ihb =>
    intro amount c h
    rw [Expr.bvarBound, Nat.max_le] at h
    rw [lowerBVars, iht amount c h.1, ihb amount (c + 1) (by omega)]
  | letE ty val body iht ihv ihb =>
    intro amount c h
    rw [Expr.bvarBound, Nat.max_le, Nat.max_le] at h
    rw [lowerBVars, iht amount c h.1.1, ihv amount c h.1.2,
      ihb amount (c + 1) (by omega)]
  | proj sn i sub ih =>
    intro amount c h
    rw [Expr.bvarBound] at h
    rw [lowerBVars, ih amount c h]

/-- The memo's invariant: every recorded answer is the real one. -/
def LowerMemoInv (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → r = lowerBVars amount k.2 k.1

theorem LowerMemoInv.empty {amount : Nat} : LowerMemoInv amount {} := by
  intro k r h; simp at h

theorem LowerMemoInv.insert {amount : Nat} {memo : Std.HashMap (Expr × Nat) Expr}
    (hm : LowerMemoInv amount memo) {e : Expr} {c : Nat} {r : Expr}
    (heq : r = lowerBVars amount c e) :
    LowerMemoInv amount (memo.insert (e, c) r) := by
  intro key r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm key r' hk

@[inherit_doc lowerBVars_of_bvarBound_le]
def lowerBVarsGo (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr)
    (e : Expr) (c : Nat) : Expr × Std.HashMap (Expr × Nat) Expr :=
  if e.bvarB ≤ c + amount then (e, memo) else
  match e with
  | .bvar i => (if i ≥ c + amount then .bvar (i - amount) else .bvar i, memo)
  | .fvar idx ty => (.fvar idx ty, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[(e, c)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
        match e with
        | .app f a =>
          let (f', memo) := lowerBVarsGo amount memo f c
          let (a', memo) := lowerBVarsGo amount memo a c
          (.app f' a', memo)
        | .lam ty body m =>
          let (t, memo) := lowerBVarsGo amount memo ty c
          let (b, memo) := lowerBVarsGo amount memo body (c + 1)
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := lowerBVarsGo amount memo ty c
          let (b, memo) := lowerBVarsGo amount memo body (c + 1)
          (.forallE t b m, memo)
        | .letE ty val body =>
          let (t, memo) := lowerBVarsGo amount memo ty c
          let (w, memo) := lowerBVarsGo amount memo val c
          let (b, memo) := lowerBVarsGo amount memo body (c + 1)
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := lowerBVarsGo amount memo sub c
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert (e, c) r)

/-- **The memoized walk is `lowerBVars`.** -/
theorem lowerBVarsGo_spec {amount : Nat} :
    ∀ (e : Expr) (c : Nat) (memo : Std.HashMap (Expr × Nat) Expr),
      LowerMemoInv amount memo →
      (lowerBVarsGo amount memo e c).1 = lowerBVars amount c e ∧
        LowerMemoInv amount (lowerBVarsGo amount memo e c).2 := by
  intro e
  induction e with
  | bvar i =>
    intro c memo hm
    rw [lowerBVarsGo]
    split
    · rename_i h
      exact ⟨(lowerBVars_of_bvarBound_le _ amount c (by rwa [← bvarB_eq])).symm, hm⟩
    · exact ⟨rfl, hm⟩
  | sort u =>
    intro c memo hm
    rw [lowerBVarsGo]; split <;> exact ⟨rfl, hm⟩
  | const n us =>
    intro c memo hm
    rw [lowerBVarsGo]; split <;> exact ⟨rfl, hm⟩
  | lit l =>
    intro c memo hm
    rw [lowerBVarsGo]; split <;> exact ⟨rfl, hm⟩
  | fvar i ty _ =>
    intro c memo hm
    rw [lowerBVarsGo]; split <;> exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro c memo hm
    rw [lowerBVarsGo]
    split
    · rename_i h
      exact ⟨(lowerBVars_of_bvarBound_le _ amount c (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ihf c memo hm
        obtain ⟨h3, h4⟩ := iha c _ h2
        refine ⟨by simp [lowerBVars, h1, h3], ?_⟩
        exact h4.insert (by simp [lowerBVars, h1, h3])
  | lam ty body m iht ihb =>
    intro c memo hm
    rw [lowerBVarsGo]
    split
    · rename_i h
      exact ⟨(lowerBVars_of_bvarBound_le _ amount c (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht c memo hm
        obtain ⟨h3, h4⟩ := ihb (c + 1) _ h2
        refine ⟨by simp [lowerBVars, h1, h3], ?_⟩
        exact h4.insert (by simp [lowerBVars, h1, h3])
  | forallE ty body m iht ihb =>
    intro c memo hm
    rw [lowerBVarsGo]
    split
    · rename_i h
      exact ⟨(lowerBVars_of_bvarBound_le _ amount c (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht c memo hm
        obtain ⟨h3, h4⟩ := ihb (c + 1) _ h2
        refine ⟨by simp [lowerBVars, h1, h3], ?_⟩
        exact h4.insert (by simp [lowerBVars, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro c memo hm
    rw [lowerBVarsGo]
    split
    · rename_i h
      exact ⟨(lowerBVars_of_bvarBound_le _ amount c (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht c memo hm
        obtain ⟨h3, h4⟩ := ihv c _ h2
        obtain ⟨h5, h6⟩ := ihb (c + 1) _ h4
        refine ⟨by simp [lowerBVars, h1, h3, h5], ?_⟩
        exact h6.insert (by simp [lowerBVars, h1, h3, h5])
  | proj sn i sub ih =>
    intro c memo hm
    rw [lowerBVarsGo]
    split
    · rename_i h
      exact ⟨(lowerBVars_of_bvarBound_le _ amount c (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih c memo hm
        refine ⟨by simp [lowerBVars, h1], ?_⟩
        exact h2.insert (by simp [lowerBVars, h1])

@[inherit_doc lowerBVarsGo]
def lowerBVarsFast (amount : Nat) (c : Nat) (e : Expr) : Expr :=
  (lowerBVarsGo amount {} e c).1

@[csimp] theorem lowerBVars_eq_lowerBVarsFast :
    @lowerBVars = @lowerBVarsFast := by
  funext amount c e
  exact (lowerBVarsGo_spec e c {} LowerMemoInv.empty).1.symm

/-! ### `instantiate1Lift` reads the loose-bvar bound, and memoizes

The pure capture-avoiding substitution is the last of the three
rebuilds on an install path without either guard (the cached engine's
twin, `Cached.instantiate1Lift`, has carried both since task #214):
`Frontend/ProjRec` and `structProjBodiesGo` run it down a constructor
telescope, and the in-process modeller's nested rung runs it through
the specialised container.  `tests/e2e/tower_nested.ndjson` is what
walks it.  Same arrangement as `abstract1`: the `O(1)` bound read
first, the memo — keyed by the node and the CURSOR `d`, which shifts
under binders — behind it. -/

/-- Substituting for a variable no loose variable reaches is the
identity. -/
theorem instantiate1Lift_of_bvarBound_le :
    ∀ (e : Expr) (v : Expr) (d : Nat), e.bvarBound ≤ d →
      instantiate1Lift e v d = e := by
  intro e
  induction e with
  | bvar i =>
    intro v d h
    rw [Expr.bvarBound] at h
    rw [instantiate1Lift, if_neg (by omega), if_neg (by omega)]
  | fvar i ty _ => intro v d _; rfl
  | sort u => intro v d _; rfl
  | const n us => intro v d _; rfl
  | lit l => intro v d _; rfl
  | app f a ihf iha =>
    intro v d h
    rw [Expr.bvarBound, Nat.max_le] at h
    rw [instantiate1Lift, ihf v d h.1, iha v d h.2]
  | lam ty body m iht ihb =>
    intro v d h
    rw [Expr.bvarBound, Nat.max_le] at h
    rw [instantiate1Lift, iht v d h.1, ihb v (d + 1) (by omega)]
  | forallE ty body m iht ihb =>
    intro v d h
    rw [Expr.bvarBound, Nat.max_le] at h
    rw [instantiate1Lift, iht v d h.1, ihb v (d + 1) (by omega)]
  | letE ty val body iht ihv ihb =>
    intro v d h
    rw [Expr.bvarBound, Nat.max_le, Nat.max_le] at h
    rw [instantiate1Lift, iht v d h.1.1, ihv v d h.1.2,
      ihb v (d + 1) (by omega)]
  | proj sn i sub ih =>
    intro v d h
    rw [Expr.bvarBound] at h
    rw [instantiate1Lift, ih v d h]

/-- The memo's invariant: every recorded answer is the real one. -/
def Inst1LMemoInv (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → r = instantiate1Lift k.1 v k.2

theorem Inst1LMemoInv.empty {v : Expr} : Inst1LMemoInv v {} := by
  intro k r h; simp at h

theorem Inst1LMemoInv.insert {v : Expr} {memo : Std.HashMap (Expr × Nat) Expr}
    (hm : Inst1LMemoInv v memo) {e : Expr} {d : Nat} {r : Expr}
    (heq : r = instantiate1Lift e v d) :
    Inst1LMemoInv v (memo.insert (e, d) r) := by
  intro key r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm key r' hk

@[inherit_doc instantiate1Lift_of_bvarBound_le]
def instantiate1LiftGo (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr)
    (e : Expr) (d : Nat) : Expr × Std.HashMap (Expr × Nat) Expr :=
  if e.bvarB ≤ d then (e, memo) else
  match e with
  | .bvar i =>
    (if i = d then Expr.liftLooseBVars d 0 v
     else if i > d then .bvar (i - 1) else .bvar i, memo)
  | .fvar idx ty => (.fvar idx ty, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | e =>
    match memo[(e, d)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
        match e with
        | .app f a =>
          let (f', memo) := instantiate1LiftGo v memo f d
          let (a', memo) := instantiate1LiftGo v memo a d
          (.app f' a', memo)
        | .lam ty body m =>
          let (t, memo) := instantiate1LiftGo v memo ty d
          let (b, memo) := instantiate1LiftGo v memo body (d + 1)
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := instantiate1LiftGo v memo ty d
          let (b, memo) := instantiate1LiftGo v memo body (d + 1)
          (.forallE t b m, memo)
        | .letE ty val body =>
          let (t, memo) := instantiate1LiftGo v memo ty d
          let (w, memo) := instantiate1LiftGo v memo val d
          let (b, memo) := instantiate1LiftGo v memo body (d + 1)
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u, memo) := instantiate1LiftGo v memo sub d
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert (e, d) r)

/-- **The memoized walk is `instantiate1Lift`.** -/
theorem instantiate1LiftGo_spec {v : Expr} :
    ∀ (e : Expr) (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr),
      Inst1LMemoInv v memo →
      (instantiate1LiftGo v memo e d).1 = instantiate1Lift e v d ∧
        Inst1LMemoInv v (instantiate1LiftGo v memo e d).2 := by
  intro e
  induction e with
  | bvar i =>
    intro d memo hm
    rw [instantiate1LiftGo]
    split
    · rename_i h
      exact ⟨(instantiate1Lift_of_bvarBound_le _ v d (by rwa [← bvarB_eq])).symm, hm⟩
    · exact ⟨rfl, hm⟩
  | sort u =>
    intro d memo hm
    rw [instantiate1LiftGo]; split <;> exact ⟨rfl, hm⟩
  | const n us =>
    intro d memo hm
    rw [instantiate1LiftGo]; split <;> exact ⟨rfl, hm⟩
  | lit l =>
    intro d memo hm
    rw [instantiate1LiftGo]; split <;> exact ⟨rfl, hm⟩
  | fvar i ty _ =>
    intro d memo hm
    rw [instantiate1LiftGo]; split <;> exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro d memo hm
    rw [instantiate1LiftGo]
    split
    · rename_i h
      exact ⟨(instantiate1Lift_of_bvarBound_le _ v d (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ihf d memo hm
        obtain ⟨h3, h4⟩ := iha d _ h2
        refine ⟨by simp [instantiate1Lift, h1, h3], ?_⟩
        exact h4.insert (by simp [instantiate1Lift, h1, h3])
  | lam ty body m iht ihb =>
    intro d memo hm
    rw [instantiate1LiftGo]
    split
    · rename_i h
      exact ⟨(instantiate1Lift_of_bvarBound_le _ v d (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht d memo hm
        obtain ⟨h3, h4⟩ := ihb (d + 1) _ h2
        refine ⟨by simp [instantiate1Lift, h1, h3], ?_⟩
        exact h4.insert (by simp [instantiate1Lift, h1, h3])
  | forallE ty body m iht ihb =>
    intro d memo hm
    rw [instantiate1LiftGo]
    split
    · rename_i h
      exact ⟨(instantiate1Lift_of_bvarBound_le _ v d (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht d memo hm
        obtain ⟨h3, h4⟩ := ihb (d + 1) _ h2
        refine ⟨by simp [instantiate1Lift, h1, h3], ?_⟩
        exact h4.insert (by simp [instantiate1Lift, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro d memo hm
    rw [instantiate1LiftGo]
    split
    · rename_i h
      exact ⟨(instantiate1Lift_of_bvarBound_le _ v d (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht d memo hm
        obtain ⟨h3, h4⟩ := ihv d _ h2
        obtain ⟨h5, h6⟩ := ihb (d + 1) _ h4
        refine ⟨by simp [instantiate1Lift, h1, h3, h5], ?_⟩
        exact h6.insert (by simp [instantiate1Lift, h1, h3, h5])
  | proj sn i sub ih =>
    intro d memo hm
    rw [instantiate1LiftGo]
    split
    · rename_i h
      exact ⟨(instantiate1Lift_of_bvarBound_le _ v d (by rwa [← bvarB_eq])).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih d memo hm
        refine ⟨by simp [instantiate1Lift, h1], ?_⟩
        exact h2.insert (by simp [instantiate1Lift, h1])

@[inherit_doc instantiate1LiftGo]
def instantiate1LiftFast (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  (instantiate1LiftGo v {} e d).1

@[csimp] theorem instantiate1Lift_eq_instantiate1LiftFast :
    @instantiate1Lift = @instantiate1LiftFast := by
  funext e v d
  exact (instantiate1LiftGo_spec e d {} Inst1LMemoInv.empty).1.symm

/-- Instantiate the leading `∀`-binders at *open* arguments, returning
the residual.  Unlike `instPisAt` this uses the general
capture-avoiding substitution (`instantiate1Lift`), so an argument may
mention loose `bvar`s of the surrounding context — which is what
building a projection's type out of the constructor telescope needs.

It sits BELOW the `@[csimp]` equation above deliberately: a `csimp`
replacement reaches the code generated for declarations elaborated
after it, so a caller written earlier in this file would compile
against the unguarded walk. -/
def instPisAtLift : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body _ => instPisAtLift as (body.instantiate1Lift a)
  | _ :: _, _ => none

/-! ## Pointer-equality shortcut -/

/-- Structural expression equality with a physical-equality shortcut
(definitionally `a == b`).  Used to validate interned-environment
entries against the stored constant they cache: the entry was created
from the very object stored in the environment, so the pointer test
succeeds without walking either expression. -/
@[inline] def exprPtrBEq (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => a == b) (fun h => by subst h; simp)

/-! ## Level-parameter occurrence, and the substitution shortcuts

`Level.hasParam` / `Expr.hasLevelParam` are the spec functions of the
`hasLP` computed field (`ConLeche/Kernel/Expr.lean`); the lemmas below
are the shortcuts a `false` reading licenses.  Self-contained, and the
cached engine's field facts (`ConLeche/Verify/Cached/Erase.lean`) are
stated against them.  They lived in `ConLeche/Kernel/ArenaWF.lean` until
task #172. -/

/-- Whether a level mentions any parameter (the spec function of the
eager `lparamBs` entries; official kernel `level.cpp` `has_param`,
task #87). -/
def _root_.ConLeche.Level.hasParam : Level → Bool
  | .param _ => true
  | .zero => false
  | .succ u => u.hasParam
  | .max u v | .imax u v => u.hasParam || v.hasParam

/-- Substitution is the identity on param-free levels. -/
theorem _root_.ConLeche.Level.subst_eq_self {ks : List Name}
    {vs : List Level} {l : Level} (h : l.hasParam = false) :
    l.subst ks vs = l := by
  induction l <;> simp_all [Level.hasParam, Level.subst]

/-- Parameter definedness is trivial on param-free levels. -/
theorem _root_.ConLeche.Level.allParamsDefined_of_not_hasParam
    {params : List Name} {l : Level} (h : l.hasParam = false) :
    l.allParamsDefined params = true := by
  induction l <;> simp_all [Level.hasParam, Level.allParamsDefined]

/-- Whether an expression mentions any level parameter (the spec
function of the eager `eparamBs` entries; `fvar` type annotations
included, matching `Expr.instantiateLevelParams`; binder prop-ness
data included since task #161 — `instantiateLevelParams` substitutes
into them, so the shortcut must see their parameters). -/
def _root_.ConLeche.Expr.hasLevelParam : Expr → Bool
  | .bvar _ | .lit _ => false
  | .sort u => u.hasParam
  | .const _ us => us.any Level.hasParam
  | .fvar _ ty => ty.hasLevelParam
  | .app f a => f.hasLevelParam || a.hasLevelParam
  | .lam ty body m | .forallE ty body m =>
    ty.hasLevelParam || body.hasLevelParam || m.pw.hasParams
  | .letE ty val body =>
    ty.hasLevelParam || val.hasLevelParam || body.hasLevelParam
  | .proj _ _ e => e.hasLevelParam

/-- `substPW` is the identity on parameter-free data (`never` and
`ifAllZero []`) — the meta half of the has-param shortcut's
soundness. -/
theorem _root_.ConLeche.Level.substPW_eq_self {ks : List Name}
    {us : List Level} {pw : PropWhen} (h : pw.hasParams = false) :
    Level.substPW ks us pw = pw := by
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    cases ps with
    | nil => rfl
    | cons p ps => simp at h

/-- Parameter-free data are defined under any parameter list. -/
theorem _root_.ConLeche.PropWhen.paramsDefined_of_not_hasParams
    {params : List Name} {pw : PropWhen} (h : pw.hasParams = false) :
    pw.paramsDefined params = true := by
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    cases ps with
    | nil => rfl
    | cons p ps => simp at h

/-- Level-parameter instantiation is the identity on level-param-free
expressions. -/
theorem _root_.ConLeche.Expr.instantiateLevelParams_eq_self
    {ks : List Name} {us : List Level} {x : Expr}
    (h : x.hasLevelParam = false) :
    x.instantiateLevelParams ks us = x := by
  induction x with
  | bvar i => rfl
  | lit l => rfl
  | sort u =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, Level.subst_eq_self h]
  | const nm vs =>
    simp only [Expr.hasLevelParam, List.any_eq_false] at h
    have hmap : vs.map (Level.subst ks us) = vs := by
      induction vs with
      | nil => rfl
      | cons v t iht =>
        simp only [List.map_cons]
        rw [Level.subst_eq_self (by simpa using h v (by simp)),
          iht fun w hw => h w (by simp [hw])]
    simp [Expr.instantiateLevelParams, hmap]
  | fvar idx ty ih =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, ih h]
  | app f a ihf iha =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    simp [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.instantiateLevelParams, iht ht, ihb hb,
      Level.substPW_eq_self hm]
  | forallE ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.instantiateLevelParams, iht ht, ihb hb,
      Level.substPW_eq_self hm]
  | letE ty val body iht ihv ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    simp [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj sp j e ihe =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, ihe h]


/-! ### `instantiateLevelParams` reads the level-param flag, and memoizes

The cached engine's twin (`Cached.instLevelParams`) has had both since
task #210 Part B; the pure walk, which the install paths and the
in-process modeller run, had neither.  `tests/e2e/tower_mutual.ndjson`
is what walks it — the modeller's generated declarations carry the
block's constructor domains, and the substitution rebuilds each shared
node once per path.

The `hasLP` field read answers "this node mentions no level parameter"
in `O(1)`, and on a tower of ordinary applications that is the whole
answer; the memo behind it covers the case the flag cannot — a shared
node that *does* mention a parameter, reached along many paths. -/

/-- The `hasLP` field's level walkers are `Level.hasParam` and its
list fold (the cached tier re-proves these facts, and `hasLP_eq`
itself, in `ConLeche/Verify/Cached/Erase.lean`; the layering keeps the
two apart). -/
theorem Expr.levelHasParam_eq : ∀ u : Level, levelHasParam u = u.hasParam := by
  intro u
  induction u <;> simp_all [levelHasParam, Level.hasParam]

@[inherit_doc Expr.levelHasParam_eq]
theorem Expr.levelsHaveParam_eq : ∀ us : List Level,
    levelsHaveParam us = us.any Level.hasParam := by
  intro us
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp [levelsHaveParam, List.any_cons, Expr.levelHasParam_eq, ih]

/-- The `hasLP` field is `Expr.hasLevelParam`. -/
theorem Expr.hasLP_eq : ∀ e : Expr, e.hasLP = e.hasLevelParam := by
  intro e
  induction e <;>
    simp_all [Expr.hasLevelParam, Expr.levelHasParam_eq, Expr.levelsHaveParam_eq]

/-- The memo's invariant: every recorded answer is the real one. -/
def ILPMemoInv (ks : List Name) (us : List Level) (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ (k : Expr) (r : Expr), memo[k]? = some r → r = k.instantiateLevelParams ks us

theorem ILPMemoInv.empty {ks : List Name} {us : List Level} : ILPMemoInv ks us {} := by
  intro k r h; simp at h

theorem ILPMemoInv.insert {ks : List Name} {us : List Level}
    {memo : Std.HashMap Expr Expr} (hm : ILPMemoInv ks us memo) {e r : Expr}
    (heq : r = e.instantiateLevelParams ks us) :
    ILPMemoInv ks us (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

@[inherit_doc Expr.hasLP_eq]
def Expr.instLPGo (ks : List Name) (us : List Level)
    (memo : Std.HashMap Expr Expr) (e : Expr) : Expr × Std.HashMap Expr Expr :=
  if !e.hasLP then (e, memo) else
  match e with
  | .bvar i => (.bvar i, memo)
  | .lit l => (.lit l, memo)
  | .sort u => (.sort (Level.subst ks us u), memo)
  | .const n vs => (.const n (vs.map (Level.subst ks us)), memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | .fvar idx ty =>
          let (t, memo) := instLPGo ks us memo ty
          (.fvar idx t, memo)
        | .app f a =>
          let (f', memo) := instLPGo ks us memo f
          let (a', memo) := instLPGo ks us memo a
          (.app f' a', memo)
        | .lam ty body m =>
          let (t, memo) := instLPGo ks us memo ty
          let (b, memo) := instLPGo ks us memo body
          (.lam t b ⟨Level.substPW ks us m.pw⟩, memo)
        | .forallE ty body m =>
          let (t, memo) := instLPGo ks us memo ty
          let (b, memo) := instLPGo ks us memo body
          (.forallE t b ⟨Level.substPW ks us m.pw⟩, memo)
        | .letE ty val body =>
          let (t, memo) := instLPGo ks us memo ty
          let (w, memo) := instLPGo ks us memo val
          let (b, memo) := instLPGo ks us memo body
          (.letE t w b, memo)
        | .proj s i sub =>
          let (u', memo) := instLPGo ks us memo sub
          (.proj s i u', memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `instantiateLevelParams`.** -/
theorem Expr.instLPGo_spec {ks : List Name} {us : List Level} :
    ∀ (e : Expr) (memo : Std.HashMap Expr Expr), ILPMemoInv ks us memo →
      (instLPGo ks us memo e).1 = e.instantiateLevelParams ks us ∧
        ILPMemoInv ks us (instLPGo ks us memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [instLPGo]; split <;> exact ⟨rfl, hm⟩
  | lit l =>
    intro memo hm
    rw [instLPGo]; split <;> exact ⟨rfl, hm⟩
  | sort u =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · exact ⟨rfl, hm⟩
  | const n vs =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · exact ⟨rfl, hm⟩
  | fvar idx ty ih =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih memo hm
        refine ⟨by simp [Expr.instantiateLevelParams, h1], ?_⟩
        exact h2.insert (by simp [Expr.instantiateLevelParams, h1])
  | app f a ihf iha =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ihf memo hm
        obtain ⟨h3, h4⟩ := iha _ h2
        refine ⟨by simp [Expr.instantiateLevelParams, h1, h3], ?_⟩
        exact h4.insert (by simp [Expr.instantiateLevelParams, h1, h3])
  | lam ty body m iht ihb =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht memo hm
        obtain ⟨h3, h4⟩ := ihb _ h2
        refine ⟨by simp [Expr.instantiateLevelParams, h1, h3], ?_⟩
        exact h4.insert (by simp [Expr.instantiateLevelParams, h1, h3])
  | forallE ty body m iht ihb =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht memo hm
        obtain ⟨h3, h4⟩ := ihb _ h2
        refine ⟨by simp [Expr.instantiateLevelParams, h1, h3], ?_⟩
        exact h4.insert (by simp [Expr.instantiateLevelParams, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht memo hm
        obtain ⟨h3, h4⟩ := ihv _ h2
        obtain ⟨h5, h6⟩ := ihb _ h4
        refine ⟨by simp [Expr.instantiateLevelParams, h1, h3, h5], ?_⟩
        exact h6.insert (by simp [Expr.instantiateLevelParams, h1, h3, h5])
  | proj sn i sub ih =>
    intro memo hm
    rw [instLPGo]
    split
    · rename_i h
      exact ⟨(instantiateLevelParams_eq_self
        (by rw [← Expr.hasLP_eq]; simpa using h)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih memo hm
        refine ⟨by simp [Expr.instantiateLevelParams, h1], ?_⟩
        exact h2.insert (by simp [Expr.instantiateLevelParams, h1])

@[inherit_doc Expr.instLPGo]
def Expr.instLPFast (ks : List Name) (us : List Level) (e : Expr) : Expr :=
  (Expr.instLPGo ks us {} e).1

@[csimp] theorem Expr.instantiateLevelParams_eq_instLPFast :
    @Expr.instantiateLevelParams = @Expr.instLPFast := by
  funext ks us e
  exact (instLPGo_spec e {} ILPMemoInv.empty).1.symm

/-- Level-parameter definedness is trivial on level-param-free
expressions. -/
theorem _root_.ConLeche.Expr.allLevelParamsDefined_of_not_hasLevelParam
    {params : List Name} {x : Expr} (h : x.hasLevelParam = false) :
    x.allLevelParamsDefined params = true := by
  induction x with
  | lam ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.allLevelParamsDefined, iht ht, ihb hb,
      PropWhen.paramsDefined_of_not_hasParams hm]
  | forallE ty body m iht ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hm⟩ := h
    simp [Expr.allLevelParamsDefined, iht ht, ihb hb,
      PropWhen.paramsDefined_of_not_hasParams hm]
  | const nm vs =>
    simp only [Expr.hasLevelParam, List.any_eq_false] at h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    exact fun v hv =>
      Level.allParamsDefined_of_not_hasParam (by simpa using h v hv)
  | sort u =>
    simp only [Expr.hasLevelParam] at h
    exact Level.allParamsDefined_of_not_hasParam h
  | _ =>
    simp_all [Expr.hasLevelParam, Expr.allLevelParamsDefined]

end ConLeche.Expr
