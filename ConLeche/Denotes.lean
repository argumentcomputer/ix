module

public import ConLeche.Kernel.Core
public import ConLeche.Verify.Level
public import ConLeche.SetModel.Ops
public import ConLeche.SetTheory.Derive.Sigma

@[expose] public section

/-!
# What a checker term denotes, and what a model of an environment is

This module is the *statement* half of the main theorem: it says what it
means for the environment the checker builds to have a model in a set
theory `V`.  It is written to be read top to bottom in one sitting —
three one-line helpers, the relation `Denotes`, the structure `Model` —
and it imports nothing from the proof tiers.  The theorem itself is
stated in `ConLeche/Challenge.lean` (with `sorry`) and proved in
`ConLeche/MainTheorem.lean`.

## The relation

`Denotes cval env φ ρ e v` says: the checker term `e` denotes the set
`v`, when

* every constant `n` at every assignment `ψ` of naturals to its
  universe parameters (`LevelParam`, a name) denotes the set `cval n ψ`,
* `env` is the environment (read only to learn a constant's universe
  parameters and a structure's projection table),
* `φ` assigns a natural to every universe parameter in scope, and
* `ρ` assigns a set to every de Bruijn index (`BVarIdx`) in scope.

There is one rule per syntax form and no rule at all for a free
variable (`fvar`), a `let` or a term that does not resolve, so such a
term denotes nothing.  That is the right reading for stored constants:
the checker stores every constant's type as a **closed** term — bound
variables are de Bruijn indices under their binders, there is no
`fvar`, and its annotation pass has replaced every `let` by its
reduct — and the relation reads a binder's body by pushing the bound
value onto `ρ`, with no renaming and no instantiation.

The two clauses that carry the type theory:

* **Binders read their regime off the checker's own annotation, and
  the annotation must be right.**  The checker records on every
  `∀`/`λ` node *when* the body is a proposition, as a datum
  `pw : PropWhen` ("iff all of these universe parameters are `0`",
  `ConLeche/Kernel/PropWhen.lean`); `regime φ pw` is `0` exactly when
  that holds at `φ`.  A `∀` in regime `0` denotes a truth value
  (`piR 0`, the proposition "every `x ∈ A` has a `y ∈ B x`"), and a `λ`
  in regime `0` denotes the one canonical proof (`lamR 0`); above `0`
  they denote the set of dependent function graphs and the literal
  graph (`piR`/`lamR`, `ConLeche/SetModel/Ops.lean`).  So propositions
  are subsets of a one-element set: proof irrelevance and
  impredicativity are built into the reading, and no typing is
  consulted.  A binder may be read in regime `0` only if its body
  really is a proposition there — its fibres are truth values (`univ 0`
  is the set of truth values), or, at a `λ`, its values are the proof
  point — so a term whose annotation is wrong has no denotation, and
  `Model.mem` below, by demanding one for every stored type, certifies
  every such annotation the checker stored.  The bodies are read on
  the domain only: `piR`/`lamR` look at nothing else.
* **Projections read a pair chain.**  A structure value is a
  right-nested pair chain; `field i p` is its `i`-th component
  (`sfst ∘ ssnd^i`).  When the environment holds a projection table
  for the structure (`env.findProj?`, every structure installed
  natively), field `i` sits at position `i + entry.off` of the chain
  (`off` records where field `0` sits: the chain may start with a
  constructor tag).  Without a table only the two fields `0`/`1` of a
  bare pair denote, by `sfst`/`ssnd` — the pinned pair the checker's
  own inductive models are built from.

A universe level denotes a natural (`Level.eval φ u`, the ordinary
evaluation with `imax u 0 = 0`), and `Sort u` denotes the `u`-th
universe of the chain `V` provides.  A constant is used at a list of
levels `us`; `Level.substFn φ ps us` is the assignment sending the
constant's own parameters `ps` to the values of `us` at `φ`
(`ConLeche/Verify/Level.lean`).  A literal denotes what its constructor
form denotes — the checker's own `natLitToConstructor`
(`n + 1` ↦ `Nat.succ (lit n)`) and `strLitToConstructor`
(`String.ofList [Char.ofNat (lit c₁), …]`).

`Denotes_functional`, proved just below the relation, states that a
term has at most one denotation, so `∃ T, Denotes … T ∧ …` below is a
statement about *the* denotation.

## The set theory

`SetTheory V` (`ConLeche/SetTheory/Core.lean`) is membership `∈ˢ` with
extensionality, pairing, union, power set, regularity, replacement, and
an ω-chain of Grothendieck universes.  The reading uses these derived
sets (`ConLeche/SetTheory/Derive/*`, each a few lines): `empty`; the
Kuratowski pair with its projections `sfst`/`ssnd`; `graph F A`, the
graph of `F` on `A`, and `app f a`, the value of a graph at a point
(`app pt _ = pt`: a proof applied to anything is a proof); `piSet A B`,
the graphs in `(x : A) → B x`; the proof point `pt`, the truth values
`truthVal p` (`{pt}` if `p`, `∅` otherwise), and `univ n`, the `n`-th
universe, with `univ 0` the set of truth values.
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

/-- A universe parameter: a name. -/
abbrev LevelParam := Name

/-- A de Bruijn index: the number of binders between a variable's
occurrence and its binder. -/
abbrev BVarIdx := Nat

variable {V : Type w} [SetTheory V]

/-- Extend a variable environment: the innermost binder gets `x`, every
other index moves up by one. -/
def push (x : V) (ρ : BVarIdx → V) : BVarIdx → V
  | 0 => x
  | i + 1 => ρ i

/-- A binder's regime at `φ`: `0` (a proposition) exactly when the
checker's annotation says the body is one at `φ`, `1` otherwise. -/
def regime (φ : LevelParam → Nat) (pw : PropWhen) : Nat :=
  if pw.holds φ then 0 else 1

/-- Component `i` of a right-nested pair chain `⟨x₀, ⟨x₁, ⟨x₂, …⟩⟩⟩`. -/
noncomputable def field : Nat → V → V
  | 0, p => sfst p
  | i + 1, p => field i (ssnd p)

/-- `Denotes cval env φ ρ e v`: the term `e` denotes the set `v`.  See
the module docstring. -/
inductive Denotes (cval : Name → (LevelParam → Nat) → V) (env : Env) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr → V → Prop
  /-- a bound variable denotes what the environment assigns it -/
  | bvar {ρ : BVarIdx → V} {i : BVarIdx} :
      Denotes cval env φ ρ (.bvar i) (ρ i)
  /-- `Sort u` denotes the universe at the level `u` evaluates to -/
  | sort {ρ : BVarIdx → V} {u : Level} :
      Denotes cval env φ ρ (.sort u) (univ (Level.eval φ u))
  /-- a stored constant, used at as many levels as it has parameters,
  denotes its `cval` at the assignment those levels induce -/
  | const {ρ : BVarIdx → V} {n : Name} {us : List Level} {ci : ConstantInfo}
      (hf : env.find? n = some ci)
      (hlen : us.length = ci.toConstantVal.levelParams.length) :
      Denotes cval env φ ρ (.const n us)
        (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
  /-- an application denotes the value of the function's graph at the
  argument -/
  | app {ρ : BVarIdx → V} {f a : Expr} {F X : V}
      (hf : Denotes cval env φ ρ f F) (ha : Denotes cval env φ ρ a X) :
      Denotes cval env φ ρ (.app f a) (app F X)
  /-- a `λ` denotes the graph of its body over its domain, or the
  canonical proof in regime `0` — which it may be read in only if the
  body really denotes a proof (`pt`) on the domain -/
  | lam {ρ : BVarIdx → V} {ty body : Expr} {m : BinderMeta} {A : V} {F : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hF : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (F x))
      (hP : regime φ m.pw = 0 → ∀ x, x ∈ˢ A → F x = pt) :
      Denotes cval env φ ρ (.lam ty body m) (lamR (regime φ m.pw) A F)
  /-- a `∀` denotes the set of dependent function graphs over its
  domain, or a truth value in regime `0` — which it may be read in only
  if the body really denotes a truth value on the domain -/
  | pi {ρ : BVarIdx → V} {ty body : Expr} {m : BinderMeta} {A : V} {B : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hB : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (B x))
      (hP : regime φ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
      Denotes cval env φ ρ (.forallE ty body m) (piR (regime φ m.pw) A B)
  /-- a projection at a stored table reads the field's position in the
  pair chain -/
  | proj_table {ρ : BVarIdx → V} {T : Name} {i : Nat} {e : Expr} {entry : ProjEntry} {P : V}
      (ht : env.findProj? T i = some entry) (he : Denotes cval env φ ρ e P) :
      Denotes cval env φ ρ (.proj T i e) (field (i + entry.off) P)
  /-- field `0` of a bare pair -/
  | proj_fst {ρ : BVarIdx → V} {T : Name} {e : Expr} {P : V}
      (ht : env.findProj? T 0 = none) (he : Denotes cval env φ ρ e P) :
      Denotes cval env φ ρ (.proj T 0 e) (sfst P)
  /-- field `1` of a bare pair -/
  | proj_snd {ρ : BVarIdx → V} {T : Name} {e : Expr} {P : V}
      (ht : env.findProj? T 1 = none) (he : Denotes cval env φ ρ e P) :
      Denotes cval env φ ρ (.proj T 1 e) (ssnd P)
  /-- a `Nat` literal denotes what its constructor form denotes -/
  | natLit {ρ : BVarIdx → V} {n : Nat} {X : V}
      (h : Denotes cval env φ ρ (natLitToConstructor n) X) :
      Denotes cval env φ ρ (.lit (.natVal n)) X
  /-- a `String` literal denotes what its constructor form denotes -/
  | strLit {ρ : BVarIdx → V} {s : String} {X : V}
      (h : Denotes cval env φ ρ (strLitToConstructor s) X) :
      Denotes cval env φ ρ (.lit (.strVal s)) X

/-- **A term has at most one denotation.**  Every rule of `Denotes` is
determined by the term's syntax form — the two `proj` rules that could
overlap are separated by whether the environment holds a projection
table — so the relation is a partial function, and `∃ T, Denotes … T ∧ …`
in `Model.mem` below is a statement about *the* denotation. -/
theorem Denotes_functional {V : Type w} [SetTheory V]
    {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {e : Expr} {v w : V}
    (hv : Denotes cval env φ ρ e v) (hw : Denotes cval env φ ρ e w) :
    v = w := by
  induction hv generalizing w with
  | bvar => cases hw; rfl
  | sort => cases hw; rfl
  | const hf _ =>
    cases hw with
    | const hf' _ => rw [hf] at hf'; cases hf'; rfl
  | app _ _ ihf iha =>
    cases hw with
    | app hf' ha' => rw [ihf hf', iha ha']
  | lam _ _ _ ihA ihF =>
    cases hw with
    | lam hA' hF' _ =>
      obtain rfl := ihA hA'
      exact ConLeche.SetModel.lamR_congr fun x hx => ihF x hx (hF' x hx)
  | pi _ _ _ ihA ihB =>
    cases hw with
    | pi hA' hB' _ =>
      obtain rfl := ihA hA'
      exact ConLeche.SetModel.piR_congr fun x hx => ihB x hx (hB' x hx)
  | proj_table ht _ ih =>
    cases hw with
    | proj_table ht' he' => rw [ht] at ht'; cases ht'; rw [ih he']
    | proj_fst ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_snd ht' _ => rw [ht] at ht'; exact nomatch ht'
  | proj_fst ht _ ih =>
    cases hw with
    | proj_table ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_fst _ he' => rw [ih he']
  | proj_snd ht _ ih =>
    cases hw with
    | proj_table ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_snd _ he' => rw [ih he']
  | natLit _ ih =>
    cases hw with
    | natLit h' => exact ih h'
  | strLit _ ih =>
    cases hw with
    | strLit h' => exact ih h'

/-- **A model of the environment `env` in the set theory `V`**: one
assignment `cval` of a set to every constant at every level
assignment — fixed once, for the whole environment — under which every
stored constant is a member of what its type denotes, the built-in
`False` is the empty set, and the built-in `Eq` is set equality.

The interpretation of the constants *is* the model: there is nothing
else to choose (`Sort`, `∀`, `λ`, application and projection are read
by fixed set operations).  `mem` is what makes every stored theorem
true — a theorem `t : P` is a constant whose type `P` denotes a truth
value, and `cval t φ ∈ˢ ⟦P⟧` says that truth value is `{pt}` — and
`false_empty` is what makes truth mean something: a proof of `False`
would be a member of `∅`.

`False` and `Eq` are both built in (the checker installs them from its
own pins and rejects a stream that declares them otherwise), so the
last two fields are facts about the checker's own constants, not
hypotheses about the input; each is stated of whatever the stored
constant denotes, so it says nothing when nothing is stored.

The model says nothing about *definitional* equalities — a
definition's unfolding, an inductive type's iota rules, η — because it
does not have to, and `eq_equality` is what discharges that debt: any
such equality a reader cares about can be stated as a theorem `h : a = b`
and proved by `rfl`; the checker accepts it; `mem` puts `cval h φ` in
what `Eq A a b` denotes, which by `eq_equality` is `eqv ⟦a⟧ ⟦b⟧`; and
`eqv x y` is inhabited only when `x = y` (`SetTheory.mem_eqv`).  So the
two sides of every accepted equation denote the same set.  Types are
the whole statement; values are the checker's business. -/
structure Model (V : Type w) [SetTheory V] (env : Env) where
  /-- the set a constant denotes, per level assignment -/
  cval : Name → (LevelParam → Nat) → V
  /-- every stored constant is a member of what its type denotes, at
  every level assignment (and every variable environment — the type
  is closed) -/
  mem : ∀ c ∈ env.consts, ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
    ∃ T, Denotes cval env φ ρ c.toConstantVal.type T ∧ cval c.name φ ∈ˢ T
  /-- whatever the built-in `False` denotes is the empty set -/
  false_empty : ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (F : V),
    Denotes cval env φ ρ (.const falseName []) F → F = empty
  /-- whatever the built-in `Eq` denotes is set equality: at a type `A`
  of the universe the level `u` names, and two of its members `a` and
  `b`, `@Eq.{u} A a b` denotes the truth value of `a = b`.  The three
  membership premises are the graph's domains — `Eq`'s denotation is a
  three-fold graph over `univ (Level.eval φ u)`, then over `A`, then
  over `A` again, and a graph read off its domain says nothing -/
  eq_equality : ∀ (u : Level) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (E A a b : V),
    Denotes cval env φ ρ (.const eqName [u]) E →
    A ∈ˢ univ (Level.eval φ u) → a ∈ˢ A → b ∈ˢ A →
    app (app (app E A) a) b = eqv a b

end ConLeche
