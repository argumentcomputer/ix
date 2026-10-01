module

public import ConLeche.Cached.StateC
public import ConLeche.Verify.Cached.OpsC
public import ConLeche.Verify.Fueled

public section

/-!
# The cached-core faithfulness kit (task #163, batch 5)

The relation and combinators for proving that the cached clone core
(`ConLeche/Cached/CoreC.lean`) simulates the pure fueled families — the
port of `ConLeche/Verify/SimI.lean` minus the arena, and (task #172 B3a)
minus the erasure: the cached and pure sides are *the same terms*, so
the value relation is equality.

* `CSOK mode env s` — the cached-state invariant: the lazy
  stored-constant caches hold `RelC`-related conversions of the
  level-instantiated stored data and every entry-point memo entry is
  backed by a pure run at some fuel, valid at every depth at which the
  key is well scoped (`ISOK`'s `CacheOK` shape, with no denotation to
  transport along).
* `SimC mode env s₀ P c p` — a successful cached run of `c` from `s₀`
  preserves `CSOK` and produces a value `P`-related to a successful run
  of the fueled computation `p` at some fuel.
* `CEff mode env s₀ Q c` — a twin-only effect (conversion, cache fill):
  no fueled counterpart, just invariant preservation plus a value fact.

Two systematic deletions against `SimAt` carry through every ported
walk: there is **no `Ext`** (no arena to extend) and the value relation
is **state-free** (no denotation to transport).  Everything else keeps
`SimAt`'s names and argument order, so the `DiscI*` walks port by local
edits.

Memo clauses obey the binding rule of the P1 freeze: a clause asserts
facts that are a **function of the key**, never `WFc` of keys — a `beq`
collision pins the stored key to the query (`beq_sound`, which since
B3a is `eq_of_beq`).
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## Lawful keys

The memo tables of `CState` are keyed by `Expr`, `Level`, `Name` and
tuples/lists of those.  `Erase.lean` supplies the `Expr` instances and
`OpsC.lean` the `Expr × β` products; everything else is `LawfulBEq`
(all keys are `DecidableEq`-derived) except *lists of `Expr`*, which
inherit the component instances the same way products do. -/

section ProdKey

private theorem prod_beq {α β : Type} [BEq α] [BEq β] (a c : α) (b d : β) :
    ((a, b) == (c, d)) = ((a == c) && (b == d)) := rfl

private theorem prod_hash {α β : Type} [Hashable α] [Hashable β] (a : α)
    (b : β) : hash (a, b) = mixHash (hash a) (hash b) := rfl

instance {α β : Type} [BEq α] [BEq β] [EquivBEq α] [EquivBEq β] :
    EquivBEq (α × β) where
  symm := by
    intro p q h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    rw [prod_beq, Bool.and_eq_true] at h
    rw [prod_beq, Bool.and_eq_true]
    exact ⟨BEq.symm h.1, BEq.symm h.2⟩
  trans := by
    intro p q t h₁ h₂
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    obtain ⟨e, f⟩ := t
    rw [prod_beq, Bool.and_eq_true] at h₁ h₂
    rw [prod_beq, Bool.and_eq_true]
    exact ⟨BEq.trans h₁.1 h₂.1, BEq.trans h₁.2 h₂.2⟩
  rfl := by
    intro p
    obtain ⟨a, b⟩ := p
    rw [prod_beq, Bool.and_eq_true]
    exact ⟨BEq.refl a, BEq.refl b⟩

instance {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    [LawfulHashable α] [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq := by
    intro p q h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    rw [prod_beq, Bool.and_eq_true] at h
    rw [prod_hash, prod_hash, LawfulHashable.hash_eq _ _ h.1,
      LawfulHashable.hash_eq _ _ h.2]

end ProdKey

section ListKey

variable {α : Type} [BEq α]

private theorem list_beq_cons {a b : α} {as bs : List α} :
    ((a :: as) == (b :: bs)) = (a == b && as == bs) := rfl

private theorem list_beq_nil_cons {b : α} {bs : List α} :
    (([] : List α) == (b :: bs)) = false := rfl

private theorem list_beq_cons_nil {a : α} {as : List α} :
    ((a :: as) == ([] : List α)) = false := rfl

variable [EquivBEq α]

instance : EquivBEq (List α) where
  symm := by
    intro a
    induction a with
    | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons y ys => rw [list_beq_nil_cons] at h; exact nomatch h
    | cons x xs ih =>
      intro b h
      cases b with
      | nil => rw [list_beq_cons_nil] at h; exact nomatch h
      | cons y ys =>
        rw [list_beq_cons, Bool.and_eq_true] at h ⊢
        exact ⟨BEq.symm h.1, ih h.2⟩
  trans := by
    intro a
    induction a with
    | nil =>
      intro b c h₁ h₂
      cases b with
      | nil => exact h₂
      | cons y ys => rw [list_beq_nil_cons] at h₁; exact nomatch h₁
    | cons x xs ih =>
      intro b c h₁ h₂
      cases b with
      | nil => rw [list_beq_cons_nil] at h₁; exact nomatch h₁
      | cons y ys =>
        cases c with
        | nil => rw [list_beq_cons_nil] at h₂; exact nomatch h₂
        | cons z zs =>
          rw [list_beq_cons, Bool.and_eq_true] at h₁ h₂ ⊢
          exact ⟨BEq.trans h₁.1 h₂.1, ih h₁.2 h₂.2⟩
  rfl := by
    intro a
    induction a with
    | nil => rfl
    | cons x xs ih =>
      rw [list_beq_cons, Bool.and_eq_true]
      exact ⟨BEq.refl x, ih⟩

omit [EquivBEq α] in
/-- `List`'s hash is a `foldl` of `mixHash`, so `BEq`-equal lists fold
to the same value from any seed. -/
private theorem list_hash_fold [Hashable α] [LawfulHashable α] :
    ∀ {a b : List α}, (a == b) = true → ∀ r : UInt64,
      List.foldl (fun r (x : α) => mixHash r (Hashable.hash x)) r a
        = List.foldl (fun r (x : α) => mixHash r (Hashable.hash x)) r b := by
  intro a
  induction a with
  | nil =>
    intro b h r
    cases b with
    | nil => rfl
    | cons y ys => rw [list_beq_nil_cons] at h; exact nomatch h
  | cons x xs ih =>
    intro b h r
    cases b with
    | nil => rw [list_beq_cons_nil] at h; exact nomatch h
    | cons y ys =>
      rw [list_beq_cons, Bool.and_eq_true] at h
      simp only [List.foldl_cons, LawfulHashable.hash_eq _ _ h.1]
      exact ih h.2 _

instance [Hashable α] [LawfulHashable α] : LawfulHashable (List α) where
  hash_eq := fun _ _ h => list_hash_fold h 7

end ListKey

/-! ## The value relations -/

/-- The cached counterpart of a denotation fact.  State-free — there is
no arena to be relative to — and, since task #172 B3b, **equality**: it
was `WFc v' ∧ v' = v`, the invariant conjunct went with `WFc`, and one
type made the second conjunct an equation between the two sides
themselves.  The name is kept because the whole `DiscC` family is
written in it, and it still marks *which* side is which. -/
@[expose] def RelC (v' : Expr) (v : Expr) : Prop := v' = v

theorem RelC.erase {v' : Expr} {v : Expr} (h : RelC v' v) : v' = v := h

/-- `RelC` determines the pure value. -/
theorem RelC.det {v' : Expr} {a b : Expr} (ha : RelC v' a)
    (hb : RelC v' b) : a = b := ha.symm.trans hb

/-- `RelC` determines the cached value. -/
theorem RelC.det' {a b : Expr} {v : Expr} (ha : RelC a v)
    (hb : RelC b v) : a = b := ha.trans hb.symm

/-- Every expression is related to itself (there is one type). -/
theorem RelC.refl (x : Expr) : RelC x x := by rfl

/-- The list-level relation: the `DiscC` walks' replacement for the
arena's `DenL`. -/
@[expose] def RelCL (l : List Expr) (xs : List Expr) : Prop := l = xs

namespace RelCL

theorem nil : RelCL [] [] := by rfl

theorem cons {x : Expr} {v : Expr} {l : List Expr} {xs : List Expr}
    (hx : RelC x v) (hl : RelCL l xs) : RelCL (x :: l) (v :: xs) := by
  rw [show x = v from hx, show l = xs from hl]; rfl

/-- The list projection. -/
theorem map {l : List Expr} {xs : List Expr} (h : RelCL l xs) :
    l = xs := h

theorem intro {l : List Expr} {xs : List Expr}
    (hm : l = xs) : RelCL l xs := hm

theorem nil_inv {xs : List Expr} (h : RelCL [] xs) : xs = [] := h.symm

theorem cons_inv {x : Expr} {l : List Expr} {xs : List Expr}
    (h : RelCL (x :: l) xs) :
    ∃ v vs, xs = v :: vs ∧ RelC x v ∧ RelCL l vs :=
  ⟨x, l, h.symm, rfl, rfl⟩

theorem length {l : List Expr} {xs : List Expr} (h : RelCL l xs) :
    l.length = xs.length := by rw [h]

theorem append {l₁ l₂ : List Expr} {xs₁ xs₂ : List Expr}
    (h₁ : RelCL l₁ xs₁) (h₂ : RelCL l₂ xs₂) :
    RelCL (l₁ ++ l₂) (xs₁ ++ xs₂) := by
  rw [show l₁ = xs₁ from h₁, show l₂ = xs₂ from h₂]; rfl

theorem reverse {l : List Expr} {xs : List Expr} (h : RelCL l xs) :
    RelCL l.reverse xs.reverse := by
  rw [show l = xs from h]; rfl

/-- `RelCL` determines the pure list. -/
theorem det {l : List Expr} {xs ys : List Expr} (hx : RelCL l xs)
    (hy : RelCL l ys) : xs = ys := hx.symm.trans hy

end RelCL

/-! ## The state invariant -/

/-- The cached-state invariant (see the module docstring): the port of
`ISOK` with every denotation leg replaced by `RelC`/`eraseC` and every
arena index key replaced by the tree key it became.  No arena clause,
no tiers.

The memo clauses are *erasure-functions of their keys* — the binding
rule of the P1 freeze — so a `beq` collision, which pins the stored key
to the query only up to erasure, preserves them. -/
structure CSOK (mode : CheckMode) (env : Env) (s : CState) : Prop where
  constTy : ∀ n us i, s.constTyAt[(n, us)]? = some i → ∃ ci,
    env.find? n = some ci ∧
    RelC i (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us)
  constVal : ∀ n us i, s.constValAt[(n, us)]? = some i → ∃ cv v h,
    env.find? n = some (.defnInfo cv v h) ∧
    RelC i (v.instantiateLevelParams cv.levelParams us)
  ruleRhs : ∀ c j us i, s.ruleRhsAt[(c, j, us)]? = some i →
    ∃ cv mI rP rules rl,
    env.find? c = some (.recInfo cv mI rP rules) ∧
    rules.find? (fun r' => r'.ctor == j) = some rl ∧
    RelC i (rl.rhs.instantiateLevelParams cv.levelParams us)
  whnfCoreC : ∀ k v, s.whnfCoreC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnfCore mode env F d k = .ok v
  whnfC : ∀ k v, s.whnfC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnf mode env F d k = .ok v
  inferC : ∀ k v, s.inferC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      inferTypeCore mode env F d k = .ok v
  /-- The io memo's clause (task #172 B4, the task-#170 memo ruling):
  an entry is backed by an io-*slot* run — the WEAKER invariant, since
  at the gated mode the slot witnesses fewer checks than `inferC`'s
  clause consumes.  A hit here never serves a full-infer query (the
  maps are separate), which is exactly what lets this clause be
  weaker. -/
  inferIOC : ∀ k v, s.inferIOC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      inferTypeIO mode env F d k = .ok v
  annotC : ∀ k v, s.annotC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      annotateCore mode env F d k = .ok v
  defeqC : ∀ a b r, s.defeqC[(a, b)]? = some r →
    ∃ F, ∀ d, (Expr.wscopedB d a) = true → (Expr.wscopedB d b) = true →
      isDefEqCore mode env F d a b = .ok r
  lsimp : ∀ u v, s.lsimpC[u]? = some v → v = Level.simplify u
  lnz : ∀ u b, s.lnzC[u]? = some b → b = Level.isNonZero u
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → Level.isEquiv l r = some b
  /-- The converted-constant cache is self-certifying: each entry's
  cached term is `RelC`-related to the very `Expr` object it is tagged
  with.  The clause never mentions `env`, so it survives every flush
  and every environment transition. -/
  ienv : ∀ (nm : Name) (ent : CConstE), s.ienv[nm]? = some ent →
    RelC ent.ty ent.tyE ∧
    ∀ vE vi, ent.val = some (vE, vi) → RelC vi vE
  instC : ∀ (k : Expr) (vs : List Expr) (d : Nat) (r : Expr),
    s.instC[(k, vs, d)]? = some r →
      r = (Expr.instantiateList k vs d)

/-- The environment-free residue: exactly the clauses `flushC`
preserves — the level-operation memos and the self-certifying
converted-constant cache.  (There is no arena clause: the port of
`ISOKF` loses `wf` along with the arena.) -/
structure CSOKF (s : CState) : Prop where
  lsimp : ∀ u v, s.lsimpC[u]? = some v → v = Level.simplify u
  lnz : ∀ u b, s.lnzC[u]? = some b → b = Level.isNonZero u
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → Level.isEquiv l r = some b
  ienv : ∀ (nm : Name) (ent : CConstE), s.ienv[nm]? = some ent →
    RelC ent.ty ent.tyE ∧
    ∀ vE vi, ent.val = some (vE, vi) → RelC vi vE

/-- Every invariant state carries the residue. -/
theorem CSOK.residue {env : Env} {s : CState} (h : CSOK mode env s) :
    CSOKF s := ⟨h.lsimp, h.lnz, h.eqv, h.ienv⟩

/-- The empty state satisfies the invariant for any environment. -/
theorem CSOK.empty (env : Env) : CSOK mode env ({} : CState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros; simp_all)

/-- The empty state carries the residue. -/
theorem CSOKF.empty : CSOKF ({} : CState) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intros; simp_all)

/-! ## Flush

`flushC` drops every environment-dependent cache, so from the residue
it re-establishes the full invariant *for any environment* — the
transition lemma the declaration fold uses (the port of
`flushS_isok`). -/

theorem flushC_run (s : CState) : flushC s = .ok ((), s.flushed) := rfl

/-- After a flush the invariant holds for any environment: the
surviving components are the residue and the dropped caches' clauses
are vacuous. -/
theorem flushC_csok {env' : Env} {s : CState} (hs : CSOKF s) :
    CSOK mode env' s.flushed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.lsimp, hs.lnz, hs.eqv,
    hs.ienv, ?_⟩ <;> (intros; simp_all [CState.flushed])

/-- Flushing preserves the residue (it touches none of its
components). -/
theorem CSOKF.flushed {s : CState} (hs : CSOKF s) : CSOKF s.flushed :=
  ⟨hs.lsimp, hs.lnz, hs.eqv, hs.ienv⟩

/-! ## The simulation and effect relations -/

/-- A successful cached run from `s₀` preserves the invariant and its
value is `P`-related to the value of a successful fueled run.  The
port of `SimAt` minus the arena extension and minus the state in the
value relation. -/
@[expose] def SimC (mode : CheckMode) (env : Env) (s₀ : CState) {β α : Type}
    (P : β → α → Prop) (c : CheckCM β) (p : FueledM α) : Prop :=
  ∀ v' s', c s₀ = .ok (v', s') →
    CSOK mode env s' ∧ ∃ v, P v' v ∧ ∃ F, p.val F = .ok v

/-- A twin-only effect: invariant preservation and a value fact — no
fueled counterpart. -/
@[expose] def CEff (mode : CheckMode) (env : Env) (s₀ : CState) {β : Type}
    (Q : β → Prop) (c : CheckCM β) : Prop :=
  ∀ v' s', c s₀ = .ok (v', s') → CSOK mode env s' ∧ Q v'

/-- The result relation for expression-valued entry points: the cached
term is related to the fueled value, well scoped at the ambient
depth. -/
@[expose] def RelEC (d : Nat) (v' : Expr) (v : Expr) : Prop :=
  RelC v' v ∧ Expr.WScoped d v

/-- The result relation for `Bool` and other data results. -/
@[expose] def RelVC {α : Type} (b a : α) : Prop := b = a

/-- The result relation for optional expression results. -/
@[expose] def RelOC (d : Nat) : Option Expr → Option Expr → Prop
  | none, none => True
  | some j, some v => RelEC d j v
  | _, _ => False

namespace SimC

variable {env : Env} {s₀ : CState}

protected theorem pure {β α : Type} {P : β → α → Prop}
    {b : β} {a : α} (hs : CSOK mode env s₀) (h : P b a) :
    SimC mode env s₀ P (pure b) (pure a) := by
  intro v' s' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, a, h, 0, rfl⟩

protected theorem throw {β α : Type} {P : β → α → Prop}
    {e : CheckError} {p : FueledM α} :
    SimC mode env s₀ P (throw e) p := by
  intro v' s' hr
  exact nomatch hr

/-- Bind: run the first components, hand the continuation the
intermediate state (with the invariant and the value relation). -/
protected theorem bind {β β' α α' : Type}
    {P : β → α → Prop} {Q : β' → α' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'}
    {p : FueledM α} {q : α → FueledM α'}
    (hx : SimC mode env s₀ P c p)
    (hf : ∀ s₁ b a, CSOK mode env s₁ → P b a →
      SimC mode env s₁ Q (k b) (q a)) :
    SimC mode env s₀ Q (c >>= k) (p >>= q) := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx b s₁ hc
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf s₁ b a hs₁ hP v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

/-- Left bind: a twin-only effect before the simulated remainder. -/
protected theorem bind_left {β β' α : Type}
    {Q : β → Prop} {P : β' → α → Prop}
    {c : CheckCM β} {k : β → CheckCM β'} {p : FueledM α}
    (hx : CEff mode env s₀ Q c)
    (hf : ∀ s₁ b, CSOK mode env s₁ → Q b → SimC mode env s₁ P (k b) p) :
    SimC mode env s₀ P (c >>= k) p := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, hQ⟩ := hx b s₁ hc
    exact hf s₁ b hs₁ hQ v' s' hr

/-- Peel a pure value bound on the twin side. -/
protected theorem bind_pure_left {β β' α : Type}
    {P : β' → α → Prop} {c : β} {k : β → CheckCM β'}
    {p : FueledM α}
    (h : SimC mode env s₀ P (k c) p) :
    SimC mode env s₀ P (pure c >>= k) p := by
  intro v' s' hr
  apply h v' s'
  simpa only [Bind.bind, StateT.bind, pure, StateT.pure, Except.pure,
    Except.bind] using hr

/-- Peel a pure value bound on the fueled side. -/
protected theorem bind_pure_right {β α α' : Type}
    {P : β → α' → Prop} {c : CheckCM β} {a : α}
    {k : α → FueledM α'}
    (h : SimC mode env s₀ P c (k a)) :
    SimC mode env s₀ P c (pure a >>= k) := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', v, hP, F, hp⟩

/-- A twin-side `throw` composed with anything never succeeds. -/
protected theorem throw_bind {β β' α : Type}
    {P : β' → α → Prop} {er : CheckError}
    {k : β → CheckCM β'} {p : FueledM α} :
    SimC mode env s₀ P ((throw er : CheckCM β) >>= k) p := by
  intro v' s' hr
  exact nomatch hr

/-- Peel a pure read: same state, the continuation at the value.
(Task #198: the port of the retired `withStore` peel — the cached
checker's syntactic reads are plain `pure`s.) -/
protected theorem pureB {β α γ : Type} {P : β → α → Prop}
    {x : γ} {k : γ → CheckCM β} {p : FueledM α}
    (h : SimC mode env s₀ P (k x) p) :
    SimC mode env s₀ P ((pure x : CheckCM γ) >>= k) p := by
  intro v' s' hr
  apply h v' s'
  simpa only [Bind.bind, StateT.bind, pure,
    StateT.pure, Except.pure, Except.bind] using hr

/-- Bind that *remembers* the first component's fueled run: the
continuation may consume the existence of a successful pure run. -/
protected theorem bindR {β β' α α' : Type}
    {P : β → α → Prop} {Q : β' → α' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'}
    {p : FueledM α} {q : α → FueledM α'}
    (hx : SimC mode env s₀ P c p)
    (hf : ∀ s₁ b a, CSOK mode env s₁ → P b a → (∃ F, p.val F = .ok a) →
      SimC mode env s₁ Q (k b) (q a)) :
    SimC mode env s₀ Q (c >>= k) (p >>= q) := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx b s₁ hc
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf s₁ b a hs₁ hP ⟨F₁, hp₁⟩ v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

/-- Strengthen the value relation using the fueled run's success. -/
protected theorem wp {β α : Type} {P Q : β → α → Prop}
    {c : CheckCM β} {p : FueledM α}
    (h : SimC mode env s₀ P c p)
    (himp : ∀ v' v, P v' v → (∃ F, p.val F = .ok v) → Q v' v) :
    SimC mode env s₀ Q c p := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', v, himp v' v hP ⟨F, hp⟩, F, hp⟩

/-- Weaken the fueled side: any computation whose successful values
subsume `p`'s (at some fuel) can replace it. -/
protected theorem wr {β α : Type} {P : β → α → Prop}
    {c : CheckCM β} {p q : FueledM α}
    (h : SimC mode env s₀ P c p)
    (himp : ∀ (v : α) (F : Nat), p.val F = .ok v → ∃ F', q.val F' = .ok v) :
    SimC mode env s₀ P c q := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hp⟩ := h v' s' hr
  obtain ⟨F', hq⟩ := himp v F hp
  exact ⟨hs', v, hP, F', hq⟩

/-- Weaken the value relation. -/
protected theorem mono {β α : Type} {P Q : β → α → Prop}
    {c : CheckCM β} {p : FueledM α}
    (hPQ : ∀ b a, P b a → Q b a) (h : SimC mode env s₀ P c p) :
    SimC mode env s₀ Q c p := by
  intro v' s' hr
  obtain ⟨hs', a, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', a, hPQ v' a hP, F, hp⟩

protected theorem liftFueled {α : Type} (what : String) (o : Option α)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (liftFueled what o) (liftFueled what o) := by
  cases o with
  | some a => exact SimC.pure hs rfl
  | none => exact SimC.throw

end SimC

namespace CEff

variable {env : Env} {s₀ : CState}

protected theorem pure {β : Type} {Q : β → Prop} {b : β}
    (hs : CSOK mode env s₀) (h : Q b) : CEff mode env s₀ Q (pure b) := by
  intro v' s' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, h⟩

protected theorem throw {β : Type} {Q : β → Prop} {e : CheckError} :
    CEff mode env s₀ Q (throw e) := by
  intro v' s' hr
  exact nomatch hr

protected theorem bind {β β' : Type} {Q : β → Prop} {R : β' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'}
    (hx : CEff mode env s₀ Q c)
    (hf : ∀ s₁ b, CSOK mode env s₁ → Q b → CEff mode env s₁ R (k b)) :
    CEff mode env s₀ R (c >>= k) := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, hQ⟩ := hx b s₁ hc
    exact hf s₁ b hs₁ hQ v' s' hr

@[inherit_doc SimC.pureB]
protected theorem pureB {β γ : Type} {Q : β → Prop}
    {x : γ} {k : γ → CheckCM β}
    (h : CEff mode env s₀ Q (k x)) :
    CEff mode env s₀ Q ((pure x : CheckCM γ) >>= k) := by
  intro v' s' hr
  apply h v' s'
  simpa only [Bind.bind, StateT.bind, pure,
    StateT.pure, Except.pure, Except.bind] using hr

end CEff

end ConLeche.Cached
