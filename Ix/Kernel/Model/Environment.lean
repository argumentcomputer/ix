/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Environment.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the `ConstantFact.recursor`, `ConstantFact.structure`, `ConstantFact.quotient`, and
`ConstantFact.quotientLift` constructors
(arities read by the kernel, with trivial meaning) and their cases, and
`NaturalMeaning.succApp` (the successor is a function whose domain contains
every numeral).
R1: `ConstantFact.quotientLift` also names the equality family's admitted
eliminator, which Ixon stores as its own record; its meaning is unchanged.
A5: `NatOp`, `NatTest`, `ConstantFact.natOp` and `ConstantFact.natTest`, values of
operations and tests on numerals.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Context
import Ix.Kernel.Model.QuotientValues
import Ix.Kernel.Const

namespace Ix.Kernel.Model

open SetTheory

universe u v

/-- A closed equation includes the whole rule telescope as lambdas. Its data
does not authorize reduction; an admitted model must establish its equality. -/
structure ConstantEquation (β : Type u) where
  lhs : AExpr β
  rhs : AExpr β
deriving DecidableEq

/-- A numeric operation evaluated on literals. An entry carries it as a fact
only after the operation's defining equations were checked against the
environment without that fact (`Certified/Natural/Arithmetic.lean`). -/
inductive NatOp where
  | pred | add | sub | mul | pow
deriving DecidableEq, Repr

/-- The operation on numbers; an operation of one argument ignores the second. -/
def NatOp.eval : NatOp → Nat → Nat → Nat
  | .pred, a, _ => a - 1
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .pow, a, b => a ^ b

/-- A test on numbers, evaluated on literals to one of two constants, as
`Nat.beq` and `Nat.ble` evaluate to `Bool.true` or `Bool.false`. -/
inductive NatTest where
  | beq | ble
deriving DecidableEq, Repr

def NatTest.eval : NatTest → Nat → Nat → Bool
  | .beq, a, b => a == b
  | .ble, a, b => decide (a ≤ b)

/-- Data describing additional proved behavior of an admitted declaration.
Only semantic producers may publish these facts; the certificate supplies
no proof of their meaning. -/
inductive ConstantFact (β : Type u) where
  | typed (expression type : AExpr β)
  | natural (zero succ : ConstRef β)
  /-- The arities of a recursor and, per rule, its constructor with the field count; read by
  the kernel to drive iota reduction. Carries no meaning: the equations and typed facts do. -/
  | recursor (nparams nminors nindices : Nat) (rules : List (ConstRef β × Nat))
  /-- The arities of a structure: the kernel reads them to type projections and to reduce and
  eta-expand through the published facts. Carries no meaning. -/
  | structure (nparams nfields : Nat)
  /-- The entry is one of the quotient primitives; the former and the constructor are pinned
  to their set-theoretic values, the eliminator carries no meaning. -/
  | quotient (kind : QuotKind)
  /-- The entry is the quotient lift, pinned to its value over the named equality family.
  `recursor` names that family's admitted eliminator, which the lift's computation rule
  uses to read the family as equality; Ixon stores it as its own record, so it is named
  rather than assumed to follow the family. It carries no meaning of its own. -/
  | quotientLift (eq recursor : ConstRef β)
  /-- The entry computes `op` on numerals. -/
  | natOp (op : NatOp)
  /-- The entry computes `test` on numerals, as the constant `yes` or `no`. -/
  | natTest (test : NatTest) (yes no : ConstRef β)
deriving DecidableEq

structure NaturalMeaning {β : Type u} {V : Type v} [SetTheory V]
    (constants : Assignment β V) (family zero succ : ConstRef β) : Prop where
  member : ∀ n, Numeral.value n ∈ˢ constants family []
  /-- The admitted zero/successor carrier contains only finite numerals. -/
  complete : ∀ x, x ∈ˢ constants family [] → ∃ n, x = Numeral.value n
  zeroValue : constants zero [] = Numeral.value 0
  succValue : ∀ n, SetTheory.app (constants succ []) (Numeral.value n) = Numeral.value (n + 1)
  /-- The successor is a function whose domain contains every numeral; this is
  what an application of it to a literal needs to be well denoted. -/
  succApp : ∀ n, ∃ (v : Nat) (A : V) (B : V → V), constants succ [] ∈ˢ SetModel.piR v A B ∧
    Numeral.value n ∈ˢ A ∧ ∀ x, x ∈ˢ A → B x ∈ˢ SetTheory.univ v

/-- An operation's constant applied to numerals. -/
noncomputable def NatOp.apply {V : Type v} [SetTheory V] : NatOp → V → Nat → Nat → V
  | .pred, f, a, _ => app f (Numeral.value a)
  | .add, f, a, b | .sub, f, a, b | .mul, f, a, b | .pow, f, a, b =>
    app (app f (Numeral.value a)) (Numeral.value b)

def ConstantFact.Meaning {β : Type u} {V : Type v} [SetTheory V]
    (constants : Assignment β V) (owner : ConstRef β) (levels : List Nat) (env : Nat → V) :
    ConstantFact β → Prop
  | .typed e type => WellDenoted constants levels env e ∧ WellDenoted constants levels env type ∧
      interp constants levels env e ∈ˢ interp constants levels env type
  | .natural zero succ => levels = [] ∧ NaturalMeaning constants owner zero succ
  | .recursor .. => True
  | .structure .. => True
  | .quotient .type => constants owner levels = Quotient.formerValue (levels.getD 0 0)
  | .quotient .ctor => constants owner levels = Quotient.constructorValue (levels.getD 0 0)
  | .quotient .lift | .quotient .ind => True
  | .quotientLift eq _ =>
    constants owner levels = Quotient.liftValue constants eq (levels.getD 0 0) (levels.getD 1 0)
  | .natOp op => levels = [] ∧
    ∀ a b, op.apply (constants owner []) a b = Numeral.value (op.eval a b)
  | .natTest test yes no => levels = [] ∧
    ∀ a b, app (app (constants owner []) (Numeral.value a)) (Numeral.value b) =
      if test.eval a b then constants yes [] else constants no []

/-- An entry becomes available to the checker only after admission of its
primitive realization, safe checked body, or atomic inductive realization.
An absent body does not license axioms or reduction equations. -/
structure ConstantEntry (β : Type u) where
  universes : Nat
  type : AExpr β
  body : Option (AExpr β)
  equations : List (ConstantEquation β) := []
  facts : List (ConstantFact β) := []

abbrev Environment (β : Type u) := ConstRef β → Option (ConstantEntry β)

/-- Meaning of an exact dependency interface. A declaration producer must
establish these facts for every universe instance and context valuation. -/
structure Realizes {β : Type u} {V : Type v} [SetTheory V]
    (constants : Assignment β V) (entries : Environment β) : Prop where
  typeValid : ∀ r entry, entries r = some entry → ∀ levels,
    levels.length = entry.universes → ∀ env,
      WellDenoted constants levels env entry.type
  member : ∀ r entry, entries r = some entry → ∀ levels,
    levels.length = entry.universes → ∀ env,
      constants r levels ∈ˢ interp constants levels env entry.type
  bodyValid : ∀ r entry, entries r = some entry → ∀ body, entry.body = some body →
    ∀ levels, levels.length = entry.universes → ∀ env,
      WellDenoted constants levels env body
  bodyValue : ∀ r entry, entries r = some entry → ∀ body, entry.body = some body →
    ∀ levels, levels.length = entry.universes → ∀ env,
      constants r levels = interp constants levels env body
  equationValue : ∀ r entry, entries r = some entry → ∀ equation ∈ entry.equations,
    ∀ levels, levels.length = entry.universes → ∀ env,
      interp constants levels env equation.lhs = interp constants levels env equation.rhs
  factMeaning : ∀ r entry, entries r = some entry → ∀ fact ∈ entry.facts,
    ∀ levels, levels.length = entry.universes → ∀ env, fact.Meaning constants r levels env

end Ix.Kernel.Model
