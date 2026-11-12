module

public import IxC.Kernel.Core
public import IxC.Kernel.Verify.Level
public import IxC.Kernel.SetModel.Ops
public import IxC.Kernel.SetTheory.Derive.Sigma
public import IxC.Kernel.Basis.Names

@[expose] public section

/-!
# What a checker term denotes, and what a model of an environment is

This module is the *statement* half of the main theorem: it says what it
means for the environment the checker builds to have a model in a set
theory `V`.  It is written to be read top to bottom in one sitting —
three one-line helpers, the relation `Denotes`, the structure `Model` —
and it imports nothing from the proof tiers.  The theorem itself is
stated in `IxC/Kernel/Challenge.lean` (with `sorry`) and proved in
`IxC/Kernel/MainTheorem.lean`.

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
  `IxC/Kernel/PropWhen.lean`); `regime φ pw` is `0` exactly when
  that holds at `φ`.  A `∀` in regime `0` denotes a truth value
  (`piR 0`, the proposition "every `x ∈ A` has a `y ∈ B x`"), and a `λ`
  in regime `0` denotes the one canonical proof (`lamR 0`); above `0`
  they denote the set of dependent function graphs and the literal
  graph (`piR`/`lamR`, `IxC/Kernel/SetModel/Ops.lean`).  So propositions
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
(`IxC/Kernel/Verify/Level.lean`).  A literal denotes what its constructor
form denotes — the checker's own `natLitToConstructor`
(`n + 1` ↦ `Nat.succ (lit n)`) and `strLitToConstructor`
(`String.ofList [Char.ofNat (lit c₁), …]`).

`Denotes_functional`, proved just below the relation, states that a
term has at most one denotation, so `∃ T, Denotes … T ∧ …` below is a
statement about *the* denotation.

## The set theory

`SetTheory V` (`IxC/Kernel/SetTheory/Core.lean`) is membership `∈ˢ` with
extensionality, pairing, union, power set, regularity, replacement, and
an ω-chain of Grothendieck universes.  The reading uses these derived
sets (`IxC/Kernel/SetTheory/Derive/*`, each a few lines): `empty`; the
Kuratowski pair with its projections `sfst`/`ssnd`; `graph F A`, the
graph of `F` on `A`, and `app f a`, the value of a graph at a point
(`app pt _ = pt`: a proof applied to anything is a proof); `piSet A B`,
the graphs in `(x : A) → B x`; the proof point `pt`, the truth values
`truthVal p` (`{pt}` if `p`, `∅` otherwise), and `univ n`, the `n`-th
universe, with `univ 0` the set of truth values.
-/

namespace Ix.Kernel

open SetTheory Ix.Kernel.SetModel

universe w

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
inductive Denotes (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr md → V → Prop
  /-- a bound variable denotes what the environment assigns it -/
  | bvar {ρ : BVarIdx → V} {i : BVarIdx} :
      Denotes cval env φ ρ (.bvar i) (ρ i)
  /-- `Sort u` denotes the universe at the level `u` evaluates to -/
  | sort {ρ : BVarIdx → V} {u : Level} :
      Denotes cval env φ ρ (.sort u) (univ (Level.eval φ u))
  /-- a stored constant, used at as many levels as it has parameters,
  denotes its `cval` at the assignment those levels induce -/
  | const {ρ : BVarIdx → V} {n : Key md} {us : List Level} {ci : ConstantInfo md}
      (hf : env.find? n = some ci)
      (hlen : us.length = ci.toConstantVal.levelParams.length) :
      Denotes cval env φ ρ (.const n us)
        (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
  /-- an application denotes the value of the function's graph at the
  argument -/
  | app {ρ : BVarIdx → V} {f a : Expr md} {F X : V}
      (hf : Denotes cval env φ ρ f F) (ha : Denotes cval env φ ρ a X) :
      Denotes cval env φ ρ (.app f a) (app F X)
  /-- a `λ` denotes the graph of its body over its domain, or the
  canonical proof in regime `0` — which it may be read in only if the
  body really denotes a proof (`pt`) on the domain -/
  | lam {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {A : V} {F : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hF : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (F x))
      (hP : regime φ m.pw = 0 → ∀ x, x ∈ˢ A → F x = pt) :
      Denotes cval env φ ρ (.lam ty body m) (lamR (regime φ m.pw) A F)
  /-- a `∀` denotes the set of dependent function graphs over its
  domain, or a truth value in regime `0` — which it may be read in only
  if the body really denotes a truth value on the domain -/
  | pi {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {A : V} {B : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hB : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (B x))
      (hP : regime φ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
      Denotes cval env φ ρ (.forallE ty body m) (piR (regime φ m.pw) A B)
  /-- a projection at a stored table reads the field's position in the
  pair chain -/
  | proj_table {ρ : BVarIdx → V} {T : Key md} {i : Nat} {e : Expr md} {entry : ProjEntry md} {P : V}
      (ht : env.findProj? T i = some entry) (he : Denotes cval env φ ρ e P) :
      Denotes cval env φ ρ (.proj T i e) (field (i + entry.off) P)
  /-- field `0` of a bare pair -/
  | proj_fst {ρ : BVarIdx → V} {T : Key md} {e : Expr md} {P : V}
      (ht : env.findProj? T 0 = none) (he : Denotes cval env φ ρ e P) :
      Denotes cval env φ ρ (.proj T 0 e) (sfst P)
  /-- field `1` of a bare pair -/
  | proj_snd {ρ : BVarIdx → V} {T : Key md} {e : Expr md} {P : V}
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
    {cval : Key md → (LevelParam → Nat) → V} {env : Env md} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {e : Expr md} {v w : V}
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
      exact Ix.Kernel.SetModel.lamR_congr fun x hx => ihF x hx (hF' x hx)
  | pi _ _ _ ihA ihB =>
    cases hw with
    | pi hA' hB' _ =>
      obtain rfl := ihA hA'
      exact Ix.Kernel.SetModel.piR_congr fun x hx => ihB x hx (hB' x hx)
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

/-! ## Telescopes, and the computation rules of recursors

The ι law below needs two notions beyond `Denotes`: a list of terms denoting a list of
sets, and a list of sets fitting a telescope. -/

/-- `DenotesList cval env φ ρ es vs`: the terms `es` denote the sets `vs`, one by one. -/
inductive DenotesList (cval : Key md → (LevelParam → Nat) → V) (env : Env md)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) : List (Expr md) → List V → Prop
  | nil : DenotesList cval env φ ρ [] []
  | cons {e : Expr md} {es : List (Expr md)} {v : V} {vs : List V} :
      Denotes cval env φ ρ e v → DenotesList cval env φ ρ es vs →
      DenotesList cval env φ ρ (e :: es) (v :: vs)

/-- **Sets fitting a telescope**: `Fits cval env φ ρ T xs ρ' R` says the sets `xs` are, in
order, members of the domains of `T`'s leading `∀`s, each domain read with the earlier
sets bound (`push`, as `Denotes` reads a binder's body); `R` is what remains of `T`, and
`ρ'` the variable environment with all of `xs` bound. Arguments fit a function's type
exactly when each is a member of its type. -/
inductive Fits (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr md → List V → (BVarIdx → V) → Expr md → Prop
  | nil {ρ : BVarIdx → V} {T : Expr md} : Fits cval env φ ρ T [] ρ T
  | cons {ρ ρ' : BVarIdx → V} {A B R : Expr md} {m : BinderMeta} {X x : V} {xs : List V} :
      Denotes cval env φ ρ A X → x ∈ˢ X → Fits cval env φ (push x ρ) B xs ρ' R →
      Fits cval env φ ρ (.forallE A B m) (x :: xs) ρ' R

/-- **ι, the computation rule of one stored recursor rule.** At a stored recursor `r`
(`recInfo cv mI rP rules`) and a rule `rl` of it, whose constructor `C` is stored with `nP`
parameters and `nF` fields:
the recursor applied to its arguments `xs` (parameters, motives, minor premises,
indices) and to a constructor application `C ys` equals the rule's right-hand side
applied to the prefix `xs.take rP` (parameters, motives, minor premises) and to the
constructor's fields `ys.drop nP`, whenever the arguments are members of their types
and the constructor's parameters and indices are the ones the major premise's type
gives. Precisely, at every level assignment `φ` and every level arguments `us` of the
recursor:

* `xs` fit the recursor's type, which then reads `∀ t : D.{ls} as, _` at `σ`: the major
  premise's type is the family `D` at levels `ls` and arguments `as`;
* the constructor is used at those levels `ls`, so the recursor's and the constructor's
  levels line up as Lean's do (a family's recursor carries the family's level parameters,
  and one more for the motive when it eliminates into every universe; an auxiliary
  recursor of a nested family uses the nested occurrence's levels); `ys` fit its type,
  which then reads `RC` at `σC`, and `C ys` is a member of the major premise's type;
* the constructor's parameters `ys.take nP` are what the major premise's parameter
  arguments `as.take nP` denote, and the constructor result's index arguments
  `RC.getAppArgs.drop nP` denote the recursor's indices `xs.drop rP`.

The last two premises are exactly what Lean's typing of the redex supplies: the major
premise `C ys` must have the type the recursor's telescope gives it, `D.{ls} as`, while
the constructor's type gives it the type `RC`, the same family at the constructor's
parameters and its own indices; the two agree only if the parameters and the indices
do.

The right-hand side is part of the conclusion: at such a redex it denotes. Without that,
a stored right-hand side that denotes nothing (a wrong binder annotation) would make the
rule say nothing. -/
def IotaRule (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (r : Key md)
    (cv : ConstantVal md) (mI rP : Nat) (rl : RecRule md) : Prop :=
  ∀ (cvC : ConstantVal md) (nP nF : Nat),
    env.find? rl.ctor = some (.ctorInfo cvC nP nF) →
    ∀ (us : List Level) (φ : LevelParam → Nat) (ρ σ σC : BVarIdx → V) (xs ys : List V)
      (dom body RC : Expr md) (m : BinderMeta) (D : Key md) (ls : List Level) (R K X : V),
      us.length = cv.levelParams.length → xs.length = mI → ys.length = nP + nF →
      Denotes cval env φ ρ (.const r us) R →
      Fits cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us) xs σ
        (.forallE dom body m) →
      dom.getAppFn = .const D ls → Denotes cval env φ σ dom X →
      Denotes cval env φ ρ (.const rl.ctor ls) K →
      Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC →
      ys.foldl app K ∈ˢ X →
      DenotesList cval env φ σ (dom.getAppArgs.take nP) (ys.take nP) →
      DenotesList cval env φ σC (RC.getAppArgs.drop nP) (xs.drop rP) →
      ∃ H, Denotes cval env φ ρ (rl.rhs.instantiateLevelParams cv.levelParams us) H ∧
        (xs ++ [ys.foldl app K]).foldl app R = (xs.take rP ++ ys.drop nP).foldl app H

/-- **ι at every stored recursor rule** (`IotaRule`). -/
def IotaLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (rl : RecRule md),
    env.find? r = some (.recInfo cv mI rP rules) → rl ∈ rules → IotaRule cval env r cv mI rP rl

/-- **Unit-like η at a family the kernel flags unit-like** (`IndCaps.unitlike`; Lean's
`is_def_eq_unit_like`): at levels `us` and parameters `ts` that fit the family's type (as
many as the flag's parameter count), any two members of the family's instance are equal.
Every stored family with the flag, the pinned `PUnit` among them. The kernel sets the flag
on a natively installed block exactly at Lean's criterion: one constructor, no index, no
field (`nativeCapsAt_unitlike_iff`). -/
def UnitLikeLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (T : Key md) (cvT : ConstantVal md) (caps : IndCaps md),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    ∀ (us : List Level) (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (ts : List V) (R : Expr md)
      (F x y : V),
      us.length = cvT.levelParams.length → ts.length = caps.unitParams →
      Denotes cval env φ ρ (.const T us) F →
      Fits cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams us) ts σ R →
      x ∈ˢ ts.foldl app F → y ∈ˢ ts.foldl app F → x = y

/-- **The projection table of a stored structure, and its two laws** (Lean's reduction
of a projection of a constructor, and structure η). At a stored inductive `T` with a
projection table — the table `Denotes` reads `.proj T i e` through (`proj_table`: field `j`
of a value is component `j + entry.off` of its pair chain) — at field `i`:

* **the table is `T`'s**: `T` has the table's universe parameters and its type is
  `∀ (params), Sort structSort`, at the table's parameter count and structure sort; the
  table's constructor `C` is stored as a constructor at the table's parameter and field
  counts and at `T`'s universe parameters, and its type is
  `∀ (params) (fields), T.{lps} params`: a constructor of `T` at `T`'s own parameters,
  with no index. These are facts about stored types, which a stored structure's
  declaration fixes;
* **the projection of a constructor**: at universe arguments `us` and arguments `ys`
  (parameters, then fields) that fit `C`'s type, field `i` of `C ys` is the field
  `ys[nP + i]`, under the table's `Prop` guard: wherever the structure sort is `0`
  at `us`, so is the projection's guard level (Lean's `infer_proj`: a projection out of a
  proposition is a proof). Where the guard fails the structure is a proposition at
  `us`, so `C ys` is the proof point and its projections are too (`mem` of `T` and of
  `C`, through the two types above);
* **structure η**: at parameters `ts` that fit `T`'s type, every member `x` of
  `T.{us} ts` is `C` applied to `ts` and to `x`'s own fields.

Together they fix what the table's offset reads: the two laws read the same
components. -/
def ProjLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md) (cvT : ConstantVal md) (capsT : IndCaps md),
    env.findProj? T i = some entry → env.find? T = some (.indInfo cvT capsT) →
    cvT.levelParams = entry.levelParams ∧
    (∃ bs, cvT.type.stripPis entry.numParams = some (bs, .sort entry.structSort)) ∧
    ∃ cvC : ConstantVal md,
      env.find? entry.ctor = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
      cvC.levelParams = entry.levelParams ∧
      (∃ bs, cvC.type.stripPis (entry.numParams + entry.numFields) = some (bs,
        Expr.mkAppN (.const T (entry.levelParams.map .param))
          ((List.range entry.numParams).map fun k =>
            .bvar (entry.numFields + entry.numParams - 1 - k)))) ∧
      ∀ (us : List Level) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (F K : V),
        us.length = entry.levelParams.length →
        Denotes cval env φ ρ (.const T us) F → Denotes cval env φ ρ (.const entry.ctor us) K →
        ((Level.eval (Level.substFn φ entry.levelParams us) entry.structSort = 0 →
            Level.eval (Level.substFn φ entry.levelParams us) entry.fieldSort = 0) →
          ∀ (σ : BVarIdx → V) (R : Expr md) (ys : List V),
            ys.length = entry.numParams + entry.numFields →
            Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams us) ys σ R →
            field (i + entry.off) (ys.foldl app K) = ys.getD (entry.numParams + i) empty) ∧
        ∀ (σ : BVarIdx → V) (R : Expr md) (ts : List V) (x : V),
          ts.length = entry.numParams →
          Fits cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams us) ts σ R →
          x ∈ˢ ts.foldl app F →
          x = (ts ++ (List.range entry.numFields).map fun j => field (j + entry.off) x).foldl
            app K

/-- **The binary `Nat` operations with a `Nat` value that the kernel computes on
literals**, at their role keys, each with Lean's function: so `a / 0 = 0`, `a % 0 = a`,
and `a ^ b` at every exponent. -/
def natArithOps : List (Key md × (Nat → Nat → Nat)) :=
  [(natAddName, Nat.add), (natSubName, Nat.sub), (natMulName, Nat.mul), (natPowName, Nat.pow),
   (natDivName, Nat.div), (natModName, Nat.mod), (natGcdName, Nat.gcd),
   (natLandName, Nat.land), (natLorName, Nat.lor), (natXorName, Nat.xor),
   (natShiftLeftName, Nat.shiftLeft), (natShiftRightName, Nat.shiftRight)]

/-- **The two `Nat` comparisons the kernel computes on literals**, at their role keys,
each with Lean's function (its value is `Bool.true` or `Bool.false`). -/
def natCmpOps : List (Key md × (Nat → Nat → Bool)) :=
  [(natBeqName, Nat.beq), (natBleName, Nat.ble)]

/-- **The `Nat` operations on literals compute as Lean's do**: at every role a stored
definition binds — `Nat.pred`, the twelve arithmetic operations (`natArithOps`) and the two
comparisons (`natCmpOps`) — the operation applied to literals denotes what the literal of
Lean's value (or the `Bool` constructor of it) denotes, at every pair of literals. This is
what lets the kernel reduce such an application to a literal without unfolding the
operation. -/
def NatLitLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  (∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? natPredName = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a : Nat) (X : V),
      Denotes cval env φ ρ (.app (.const natPredName []) (.lit (.natVal a))) X →
      Denotes cval env φ ρ (.lit (.natVal (a - 1))) X) ∧
  (∀ (c : Key md) (f : Nat → Nat → Nat), (c, f) ∈ natArithOps →
    ∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? c = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a b : Nat) (X : V),
      Denotes cval env φ ρ (.app (.app (.const c []) (.lit (.natVal a))) (.lit (.natVal b))) X →
      Denotes cval env φ ρ (.lit (.natVal (f a b))) X) ∧
  ∀ (c : Key md) (f : Nat → Nat → Bool), (c, f) ∈ natCmpOps →
    ∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? c = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a b : Nat) (X : V),
      Denotes cval env φ ρ (.app (.app (.const c []) (.lit (.natVal a))) (.lit (.natVal b))) X →
      Denotes cval env φ ρ (.const (if f a b then boolTrueName else boolFalseName) []) X

/-- **`Nat.add`'s recurrences at every natural**: the kernel rewrites `Nat.add b k` at a
non-literal `b` (an offset's successor step, adding zero, offsets in conversion), so at the
role a stored definition binds, `x + 0 = x` and `x + succ y = succ (x + y)` for every
member `x`, `y` of what `Nat` denotes. -/
def NatAddLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? natAddName = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (N Z S A : V),
      Denotes cval env φ ρ (.const natName []) N →
      Denotes cval env φ ρ (.const natZeroName []) Z →
      Denotes cval env φ ρ (.const natSuccName []) S →
      Denotes cval env φ ρ (.const natAddName []) A →
      ∀ x y, x ∈ˢ N → y ∈ˢ N →
        app (app A x) Z = x ∧ app (app A x) (app S y) = app S (app (app A x) y)

/-- **A graded reading** (`D` a denotation relation, such as `Denotes cval env φ`): every
application in the term applies a function that denotes a member of a dependent product to an
argument that denotes a member of the product's domain (Lean's typing of the application, read
in the sets), through every binder at every member of its domain. `Denotes` reads an
application at any argument, and β computes only on the domain (`SetModel.app_lamR`), so a
reduction that fires β with no certificate is sound on graded readings only. -/
def GradedBy (D : (BVarIdx → V) → Expr md → V → Prop) : (BVarIdx → V) → Expr md → Prop
  | ρ, .app f a => GradedBy D ρ f ∧ GradedBy D ρ a ∧
      ∃ (r : Nat) (A F X : V) (B : V → V), D ρ f F ∧ D ρ a X ∧ F ∈ˢ piR r A B ∧ X ∈ˢ A ∧
        (r = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)
  | ρ, .lam ty b _ =>
    GradedBy D ρ ty ∧ ∀ A, D ρ ty A → ∀ x, x ∈ˢ A → GradedBy D (push x ρ) b
  | ρ, .forallE ty b _ =>
    GradedBy D ρ ty ∧ ∀ A, D ρ ty A → ∀ x, x ∈ˢ A → GradedBy D (push x ρ) b
  | ρ, .proj _ _ e => GradedBy D ρ e
  | _, _ => True

/-- **Stored terms are graded**: every stored constant's type, and every stored definition's
value, has a graded reading (`GradedBy`) at every level assignment and variable environment.
The kernel stores only terms it has typed; this is what that typing says in the sets. -/
def GradedLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ c ∈ env.consts, ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
    GradedBy (Denotes cval env φ) ρ c.toConstantVal.type ∧
    ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
      c = .defnInfo cv value hint → GradedBy (Denotes cval env φ) ρ value

/-- **A model of the environment `env` in the set theory `V`**: one
assignment `cval` of a set to every constant at every level
assignment — fixed once, for the whole environment — under which every
stored constant is a member of what its type denotes, the built-in
`False` is the empty set, the built-in `Eq` is set equality, the built-in
`PUnit` has one member, the same at every level, every
stored definition is what its value denotes, every stored recursor rule
computes as Lean's does, the kernel's η laws hold at stored structures and
unit-like families, the `Nat` operations compute on literals, every
stored type and value applies functions on their domains, and a
constant's value reads only its own level parameters.

The interpretation of the constants *is* the model: there is nothing
else to choose (`Sort`, `∀`, `λ`, application and projection are read
by fixed set operations).  `mem` is what makes every stored theorem
true — a theorem `t : P` is a constant whose type `P` denotes a truth
value, and `cval t φ ∈ˢ ⟦P⟧` says that truth value is `{pt}` — and
`false_empty` is what makes truth mean something: a proof of `False`
would be a member of `∅`.

`False`, `Eq` and `PUnit` are built in (the checker installs them from its
own pins and rejects a stream that declares them otherwise), so
`false_empty`, `eq_equality` and `punit_unit` are facts about the checker's
own constants, not hypotheses about the input; each is stated of whatever
the stored constant denotes, so it says nothing when nothing is stored.

**The constants mean what Lean means.**  Membership alone lets a
constant denote any inhabitant of its type: with `mem` and nothing
else, `def P : Prop := False` and `theorem t : P` have a model in which
`P` is true.  So the model also keeps Lean's definitional equalities
where they are laws of stored constants:

* **δ** (`defn_value`): a stored definition denotes what its value
  denotes.  Theorems need no such law: a theorem's statement is a
  proposition, whose only possible member is `pt`, so a theorem denotes
  what any proof of its statement denotes (which is why the checker may
  unfold one).  An opaque constant is stored with no value.
* **ι** (`iota_rule`): every stored recursor rule computes as Lean's
  does (`IotaRule`): the recursor at arguments that fit its type and at
  a constructor application of its major premise's family is the rule's
  right-hand side at the prefix and the constructor's fields.  The
  quotient's computation rules are among them: `Quot.lift` and
  `Quot.ind` are stored as recursors.
* **unit-like η** (`unit_like`): at a family the kernel flags unit-like,
  any two members of an instance are equal (`UnitLikeLaw`).
* **projections and structure η** (`proj_law`): a stored structure's
  projection table is the structure's own, a projection of its
  constructor is the field, and every member of an instance is the
  constructor at its own fields (`ProjLaw`).
* **`Nat` literals** (`lit_ops`): `Nat.pred` and the fourteen binary
  operations the kernel computes on literals do so as Lean's functions
  (`NatLitLaw`), and `Nat.add` satisfies its recurrences at every natural
  (`nat_add`, `NatAddLaw`).
* **graded stored terms** (`graded`): every stored type and definition value applies each
  function to an argument in its domain (`GradedLaw`), as the kernel's typing of the term
  says. `Denotes` reads an application anywhere, so without this law a stored value could
  denote an off-domain application that β, fired without a certificate, would change.

The kernel's other generic definitional equalities do not depend on
`cval`: they hold in every model because of how `Denotes` reads terms.

* **β**: a `λ` denotes the graph of its body over its domain, and a
  graph applied to a point of its domain is the body's value there; in
  regime `0` both are the proof point (`SetModel.app_lamR`).
* **function η**: a member of a `∀` set is the graph of its own
  applications over the domain, or `pt` in regime `0`
  (`SetModel.lamR_eta`).
* **proof irrelevance**: a proposition denotes a subset of `{pt}`, so
  its members are all equal (`SetModel.subsingleton_of_mem_univZero`).
* **ζ**: a stored term has no `let` (the checker's annotation pass
  replaces each by its reduct), and `Denotes` reads none.
* **literals**: a `Nat` or `String` literal denotes its constructor
  form, by `Denotes`' own rules, so the literal `n + 1` and
  `Nat.succ n` denote the same set. -/
structure Model (V : Type w) [SetTheory V] (env : Env md) where
  /-- the set a constant denotes, per level assignment -/
  cval : Key md → (LevelParam → Nat) → V
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
  /-- whatever the built-in `PUnit` denotes has one member at most, and the same one at
  every level: a member of `PUnit.{us}` at `φ` and a member of `PUnit.{vs}` at `ψ` are
  equal. The checker identifies any two terms whose types reduce to `PUnit`, whatever
  the levels (its unit-like test reads the head only) -/
  punit_unit : ∀ (us vs : List Level) (φ ψ : LevelParam → Nat) (ρ ρ' : BVarIdx → V)
    (P Q x y : V),
    Denotes cval env φ ρ (.const punitName us) P →
    Denotes cval env ψ ρ' (.const punitName vs) Q → x ∈ˢ P → y ∈ˢ Q → x = y
  /-- **δ**: every stored definition denotes what its value denotes, at
  every level assignment (and every variable environment — the value is
  closed).  A use `c.{us}` denotes `cval c` at the assignment `us`
  induces, which is where the value is read too -/
  defn_value : ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
      Denotes cval env φ ρ value (cval cv.name φ)
  /-- **ι**: every stored recursor rule computes as Lean's does (`IotaRule`) -/
  iota_rule : IotaLaw cval env
  /-- **unit-like η** at every family the kernel flags unit-like (`UnitLikeLaw`) -/
  unit_like : UnitLikeLaw cval env
  /-- **projections and structure η** at every stored structure's projection table, which
  is the structure's own (`ProjLaw`) -/
  proj_law : ProjLaw cval env
  /-- **the `Nat` operations on literals** compute as Lean's do (`NatLitLaw`) -/
  lit_ops : NatLitLaw cval env
  /-- **`Nat.add`'s recurrences** at every natural (`NatAddLaw`) -/
  nat_add : NatAddLaw cval env
  /-- **stored terms are graded**: every stored type and definition value applies functions
  on their domains only (`GradedLaw`) -/
  graded : GradedLaw cval env
  /-- a stored constant's value depends on the level assignment only through its own
  level parameters (so a use of it reads its levels, and nothing else) -/
  cval_params : ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂

/-! ## Semantic consistency -/

/-- Semantic consistency of an environment `env`: no accepted constant in
`env.consts` has type `False` (`.const falseName []`). -/
def Consistent (env : Env md) : Prop :=
  ∀ ci ∈ env.consts, ci.toConstantVal.type = .const falseName [] → False

/-- **Any environment with a model in `V` is semantically consistent.** -/
theorem consistent_of_model (V : Type w) [SetTheory V] {env : Env md}
    (hM : Nonempty (Model V env)) : Consistent env := by
  obtain ⟨M⟩ := hM
  intro ci hci hty
  obtain ⟨T, hDen, hmem⟩ := M.mem ci hci (fun _ => 0) (fun _ => empty)
  rw [hty] at hDen
  have hT : T = empty := M.false_empty (fun _ => 0) (fun _ => empty) T hDen
  rw [hT] at hmem
  exact not_mem_empty _ hmem

/-- A model of `env` directly witnesses `Consistent env`. -/
theorem Model.consistent {env : Env md} (M : Model V env) : Consistent env :=
  consistent_of_model V ⟨M⟩

end Ix.Kernel
