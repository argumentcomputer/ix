module

public import ConLeche.Kernel.Checker
public import ConLeche.Verify.Level
public import ConLeche.Verify.EnvWF
public import ConLeche.Term.Const

public section

/-!
# Denotation of kernel expressions into the erased term language

`denote cval env φ d e` maps a kernel `Expr` to a `ConLeche.Term.Term`.

**Provenance note (task #209).**  This function was written as the
front half of a *declarative* verification lane: a typing judgment
`HasType` over `Term` with a model above it.  That lane is gone
(tasks #148, #190, #209) and `denote` survives as the semantics
tier's reading of a stored term.  The design rationale below names
rules of the deleted judgment where that is what decided a clause's
shape; those names no longer resolve to anything in the tree, and are
kept because the *reasons* still bind — see DESIGN.md's task #209
section.

The clauses in one line each:

| `Expr` node | `denote` |
|---|---|
| `.sort u` | `some (.sort (u.eval φ))` |
| `.fvar idx` | `some (.bvar (d - 1 - idx))` |
| `.const n us` | the valuation, `cval n (Level.substFn φ ps us)` |
| `.forallE ty body` | `.pi ⟦ty⟧ ⟦body opened⟧` |
| `.lam ty body` | `.lam ⟦ty⟧ ⟦body opened⟧` |
| `.app f a` | `.app ⟦f⟧ ⟦a⟧` |
| `.proj` | `.fst ⟦e⟧` / `.snd ⟦e⟧` |
| `.lit (.natVal n)` | `natLitT ⟦zero⟧ ⟦succ⟧ n` |
| `.letE` | `none` — there is no `letE` former |

Four properties of that reading are worth stating rather than reading
off the table.

## There is no free-variable valuation

A free variable's term is determined by its own `fvar` index together
with the current depth: `fvar d` opened at depth `d` is de Bruijn index
`0` under one binder, `1` under two, i.e. `.bvar (d' - 1 - d)` at depth
`d'`.  So `denote` takes no environment of variable values — the leaf
clause computes what such an environment would have stored — and the
predicate that constrains the free variables is `CtxOk`, over the de
Bruijn context `Δ`.

## Delta is `rfl`, because `denote` never delta-reduces

`denote` does *not* unfold a constant: it reads the constant's value out
of the valuation `cval`, and the environment invariant records that a
definition's valuation is the denotation of its body.  A delta step in
the checker is therefore an *equation between denotations that already
holds*, not a rule of the type theory — which is the concrete sense in
which the reduction strategy drops out of the consistency argument.
The recursion over the environment lives in the *incremental
construction of the valuation* as declarations install, which is
`EnvModel`'s own induction and needs no separate termination argument.

## There is no `let` in the term language

**Every clause maps a constructor to a constructor** — or, at `letE`,
to `none`.  That is not cosmetic, and the `letE` clause is where it was
decided.  The principle to preserve, if any clause is ever tempted to
compute:

> **A structural `denote` is what keeps the bridge's substitution
> metatheory small.**

A `denote` that performed a substitution — emitting `b.inst ⟦value⟧`
for a `letE` — would force this layer's metatheory to prove that
lifting commutes with instantiation, and then that lifting commutes
with lifting, and the swamp `ConLeche/Term/Subst.lean` is proud of
avoiding (lean4lean's 123 syntactic lemmas) would reappear one layer
down.

The term language does not carry a `letE` former either, for the reason
that made one dead weight: **no stored expression carries a `let`**.
`annotateBody` is the one pass that meets a `letE` node from the
stream, and it runs the official `infer_let` triple and returns the
ζ *reduct*; every other kernel arm that could meet a `letE` —
`whnfCore`'s ζ step, `inferBody`'s and `inferBodyIO`'s triples — is a
positive `.internal` error.  So the clause is `none` and the `letE`
case of every reduction walk and every transport lemma is **vacuous**:
they all carry `denote… = some _` as a premise.

## Projections, and why the layer grew a former for them

A `.proj` node carries an index and a subject, and nothing else: the
pair's type arguments `A` and `B` are not in it — the checker recovers
them at *use* time, by whnf-ing the subject's inferred type
(`ConLeche/Kernel/Core.lean`, the `.proj` clause of `annotateBody`).  A
denotation that is a function of the expression alone therefore cannot
emit a constant applied to `A` and `B`, and a *relational* denotation is
not an option either: the defeq claim of the fuel induction needs both
sides denoted by the *same* function, or the two existentials do not
meet.

So the term language has untyped projection formers
(`ConLeche/Term/Syntax.lean`: `fst`/`snd`), carrying exactly what the
checker's node carries beyond the index, and typed by reading `A` and
`B` off the premise.  This clause decodes the index with
`Term.projPair?`, whose `none` branch is the `i < 2` guard, and the
alphabet comes out *smaller* for it: `psigmaFst` and `psigmaSnd` are
derivable from the formers and are not `BConst`s.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- A valuation of the environment's constants by *terms* of the
declarative type theory — level-polymorphically, each constant being a
function of the level-parameter assignment.  The exact transpose of
`ConLeche.ConstVal V = Name → (Name → Nat) → V`. -/
abbrev TConstVal := Name → (Name → Nat) → Term

/-- The term of a `Nat` literal: the `Nat.succ` valuation iterated on
the `Nat.zero` valuation.  Transpose of `natLitVal`.

Note that this is *unary and never evaluated*: nothing in the bridge
computes it, and the literal fast paths are discharged by lemma
families proved by meta-level induction on the literal (task #119, the
`Nat` interface), never by exhibiting a derivation of the size of the
numeral. -/
@[expose] def natLitT (zv sv : Term) : Nat → Term
  | 0 => zv
  | n + 1 => .app sv (natLitT zv sv n)

/-- The character-list part of a string literal's constructor form.
Transpose of `charListVal`. -/
@[expose] def charListT (nilV consV ofNatV zv sv : Term) : List Char → Term
  | [] => nilV
  | c :: cs =>
    .app (.app consV (.app ofNatV (natLitT zv sv c.toNat)))
      (charListT nilV consV ofNatV zv sv cs)

/-- The stored level-parameter list of a constant (`[]` when absent).
Transpose of `ConLeche.Env.levelParamsAt`; restated here because
`ConLeche/TTVerify/*` does not import the set model. -/
@[expose] def levelParamsAt (env : Env) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- The term of a `String` literal: the denotation of its constructor
form (`strLitToConstructor`), written out — each constant valued
exactly as the `.const` clause values it on that form.  Transpose of
`strLitVal`. -/
@[expose] def strLitT (cval : TConstVal) (env : Env) (φ : Name → Nat) (s : String) :
    Term :=
  .app (cval stringOfListName (Level.substFn φ [] []))
    (charListT
      (.app (cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
        (cval charName (Level.substFn φ [] [])))
      (.app (cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
        (cval charName (Level.substFn φ [] [])))
      (cval charOfNatName (Level.substFn φ [] []))
      (cval natZeroName (Level.substFn φ [] []))
      (cval natSuccName (Level.substFn φ [] []))
      s.toList)

/-- The tower projection's `Term` spelling (task #175 wiring W3):
`.fst ∘ .snd^i` — the erase image of the P reading's `projAV`
(`SetBase/TowerLeaf.lean`), interpreting to `projS i` on the tuple
tier's carriers.  Depends only on the index. -/
@[expose] def projNV : Nat → Term → Term
  | 0, e => .fst e
  | i + 1, e => projNV i (.snd e)

/-- Denote an expression under constant valuation `cval`, level
assignment `φ` and binder depth `d`.  See the module docstring, in
particular for the absent free-variable valuation, for `letE`, and for
the `.proj` clause. -/
@[expose] def denote (cval : TConstVal) (env : Env) (φ : Name → Nat) :
    (d : Nat) → Expr → Option Term
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE ty body m =>
    match denote cval env φ d ty with
    | none => none
    | some A =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => none
      | some B => some (.pi A B)
  | d, .lam ty body m =>
    match denote cval env φ d ty with
    | none => none
    | some A =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => none
      | some b => some (.lam A b)
  | d, .app f a =>
    match denote cval env φ d f, denote cval env φ d a with
    | some vf, some va => some (.app vf va)
    | _, _ => none
  | _, .letE _ _ _ =>
    -- **`none` by design** (task #241): `Term` has no `letE` former.
    -- See "There is no `let` in the term language" above.
    none
  | d, .proj sn i e =>
    -- the transpose of `interpExpr`'s clause, the pair side's index
    -- decoded by `projPair?`; a tower-backed entry (task #175 wiring W3)
    -- reads field `i` by the uniform iterated spelling instead — the
    -- entry key consumed at the reading, never carried in the syntax
    match denote cval env φ d e with
    | none => none
    | some ve =>
      match env.findProj? sn i with
      | some entry => some (projNV (i + entry.off) ve)
      | none => Term.projPair? i ve
  | _, .lit (.natVal n) =>
    -- guarded exactly like the checker's literal paths
    if natLitSupported env then
      some (natLitT (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, .lit (.strVal s) =>
    if strLitSupported env then some (strLitT cval env φ s) else none
  | _, _ => none
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Denotation of a closed expression (as they appear in declarations).
Transpose of `interpClosed`. -/
@[expose] def denoteClosed (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (e : Expr) : Option Term :=
  denote cval env φ 0 e

/-! ## Clause equations

`denote` is defined by well-founded recursion on `Expr.sizeB` (like
`interpExpr`), so its clauses are not definitional; these are the
rewrite rules every consumer uses. -/

@[simp] theorem denote_sort (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (u : Level) :
    denote cval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denote]

@[simp] theorem denote_fvar (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d idx : Nat) (ty : Expr) :
    denote cval env φ d (.fvar idx ty) = some (.bvar (d - 1 - idx)) := by
  rw [denote]

theorem denote_const (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (n : Name) (us : List Level) :
    denote cval env φ d (.const n us) =
      match env.find? n with
      | some ci =>
        if us.length = ci.toConstantVal.levelParams.length then
          some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
        else none
      | none => none := by
  rw [denote]

theorem denote_app (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (f a : Expr) :
    denote cval env φ d (.app f a) =
      match denote cval env φ d f, denote cval env φ d a with
      | some vf, some va => some (.app vf va)
      | _, _ => none := by
  rw [denote]

theorem denote_forallE (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (ty body : Expr) (m : BinderMeta) :
    denote cval env φ d (.forallE ty body m) =
      match denote cval env φ d ty with
      | none => none
      | some A =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
        | none => none
        | some B => some (.pi A B) := by
  rw [denote]

theorem denote_lam (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (ty body : Expr) (m : BinderMeta) :
    denote cval env φ d (.lam ty body m) =
      match denote cval env φ d ty with
      | none => none
      | some A =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
        | none => none
        | some b => some (.lam A b) := by
  rw [denote]

theorem denote_letE (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (ty val body : Expr) :
    denote cval env φ d (.letE ty val body) = none := by
  rw [denote]

theorem denote_proj (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (T : Name) (i : Nat) (e : Expr) :
    denote cval env φ d (.proj T i e) =
      match denote cval env φ d e with
      | none => none
      | some ve =>
        match env.findProj? T i with
        | some entry => some (projNV (i + entry.off) ve)
        | none => Term.projPair? i ve := by
  rw [denote]

@[simp] theorem denote_bvar (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d i : Nat) : denote cval env φ d (.bvar i) = none := by
  rw [denote] <;> simp

theorem denote_natLit (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d n : Nat) :
    denote cval env φ d (.lit (.natVal n)) =
      (if natLitSupported env then
        some (natLitT (cval natZeroName (Level.substFn φ [] []))
          (cval natSuccName (Level.substFn φ [] [])) n)
      else none) := by
  rw [denote]

theorem denote_strLit (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (s : String) :
    denote cval env φ d (.lit (.strVal s)) =
      (if strLitSupported env then some (strLitT cval env φ s) else none) := by
  rw [denote]

end ConLeche.Verify
