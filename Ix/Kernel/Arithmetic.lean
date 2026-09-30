/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer
import Ix.Kernel.Env
import Ix.Kernel.Certified.Checker

/-! # Numeric operations on literals: equations and meaning

A definition whose type is `N → N → N` or `N → N`, for a natural family `N`,
may compute one of the operations of `NatOp`. The kernel checks the
operation's defining equations by conversion, with variables for the
arguments, in the environment where the definition is installed without any
arithmetic fact of its own, so literal evaluation cannot take part in its own
justification. By induction on numerals the equations determine the operation's
values (`BinaryEquations.meaning`, `PredEquations.meaning`), which is the
meaning of the published `ConstantFact.natOp`.

| Operation | At `0` | At `m + 1` | Needs |
|---|---|---|---|
| `add` | `n + 0 = n` | `n + (m+1) = succ (n + m)` | |
| `sub` | `n - 0 = n` | `n - (m+1) = pred (n - m)` | `pred` |
| `mul` | `n * 0 = 0` | `n * (m+1) = n * m + n` | `add` |
| `pow` | `n ^ 0 = 1` | `n ^ (m+1) = n ^ m * n` | `mul` |
| `pred` | `pred 0 = 0` | `pred (m+1) = m` | |

A definition of type `N → N → B` may compute a test (`NatTest`), evaluated to
the constants `yes` and `no` read off its values at `0, 0` and `1, 0`; what
`B` is does not matter to the meaning (as in con-leche):

| Test | `0, 0` | `0, m+1` | `n+1, 0` | `n+1, m+1` |
|---|---|---|---|---|
| `beq` | `yes` | `no` | `no` | `beq n m` |
| `ble` | `yes` (any `m`) | | `no` | `ble n m` |

These are the recurrences Lean's `Nat` operations are defined by, as in
con-leche. No name is trusted: which definition computes which operation is
decided by the equations alone. -/

namespace Ix.Kernel.Arithmetic

open Model Model.SetTheory

universe u v

variable {β : Type u}

/-- The natural family, as the type of a variable. -/
def natType (nat : ConstRef β) : AExpr β := .const nat []

/-- A binary operation's constant applied to two arguments. -/
def applied (r : ConstRef β) (x y : AExpr β) : AExpr β := .app (.app (.const r []) x) y

/-- The successor applied to an argument. -/
def succOf (succ : ConstRef β) (x : AExpr β) : AExpr β := .app (.const succ []) x

/-- One variable of the natural family. -/
def unaryContext (nat : ConstRef β) : Context β := Context.push (natType nat) []

/-- Two variables of the natural family: `#1` is `n` and `#0` is `m`. -/
def binaryContext (nat : ConstRef β) : Context β := Context.push (natType nat) (unaryContext nat)

/-- What a binary operation is at `n` and `0`, with `n` as `#0`. -/
def baseRhs (nat : ConstRef β) : NatOp → AExpr β
  | .mul => .natLit nat 0
  | .pow => .natLit nat 1
  | .add | .sub | .pred => .bvar 0

/-- What a binary operation is at `n` and `m + 1`, in terms of its value at
`n` and `m`. `helper` computes the operation the recurrence uses. -/
def stepRhs (succ r helper : ConstRef β) : NatOp → AExpr β
  | .add => succOf succ (applied r (.bvar 1) (.bvar 0))
  | .sub => .app (.const helper []) (applied r (.bvar 1) (.bvar 0))
  | .mul | .pow => applied helper (applied r (.bvar 1) (.bvar 0)) (.bvar 1)
  | .pred => .bvar 0

/-- The operation a binary operation's recurrence uses, if any. -/
def helperOp : NatOp → Option NatOp
  | .sub => some .pred
  | .mul => some .add
  | .pow => some .mul
  | .add | .pred => none

/-- An equation established by conversion between formed sides. -/
def Holds (entries : Environment β) (Γ : Context β) (lhs rhs : AExpr β) : Prop :=
  ConvClaim.{u,v} entries Γ lhs rhs ∧ FormedClaim.{u,v} entries Γ lhs ∧
    FormedClaim.{u,v} entries Γ rhs

/-- The checked defining equations of a binary operation. -/
structure BinaryEquations (entries : Environment β) (nat succ r helper : ConstRef β)
    (op : NatOp) : Prop where
  base : Holds.{u,v} entries (unaryContext nat) (applied r (.bvar 0) (.natLit nat 0))
    (baseRhs nat op)
  step : Holds.{u,v} entries (binaryContext nat) (applied r (.bvar 1) (succOf succ (.bvar 0)))
    (stepRhs succ r helper op)

/-- The checked defining equations of the predecessor. -/
structure PredEquations (entries : Environment β) (nat succ r : ConstRef β) : Prop where
  base : Holds.{u,v} entries [] (.app (.const r []) (.natLit nat 0)) (.natLit nat 0)
  step : Holds.{u,v} entries (unaryContext nat) (.app (.const r []) (succOf succ (.bvar 0)))
    (.bvar 0)

/-- The checked defining equations of `beq`. -/
structure BeqEquations (entries : Environment β) (nat succ r yes no : ConstRef β) : Prop where
  zeroZero : Holds.{u,v} entries [] (applied r (.natLit nat 0) (.natLit nat 0)) (.const yes [])
  zeroSucc : Holds.{u,v} entries (unaryContext nat) (applied r (.natLit nat 0) (succOf succ (.bvar 0)))
    (.const no [])
  succZero : Holds.{u,v} entries (unaryContext nat) (applied r (succOf succ (.bvar 0)) (.natLit nat 0))
    (.const no [])
  succSucc : Holds.{u,v} entries (binaryContext nat)
    (applied r (succOf succ (.bvar 1)) (succOf succ (.bvar 0))) (applied r (.bvar 1) (.bvar 0))

/-- The checked defining equations of `ble`. -/
structure BleEquations (entries : Environment β) (nat succ r yes no : ConstRef β) : Prop where
  zero : Holds.{u,v} entries (unaryContext nat) (applied r (.natLit nat 0) (.bvar 0)) (.const yes [])
  succZero : Holds.{u,v} entries (unaryContext nat) (applied r (succOf succ (.bvar 0)) (.natLit nat 0))
    (.const no [])
  succSucc : Holds.{u,v} entries (binaryContext nat)
    (applied r (succOf succ (.bvar 1)) (succOf succ (.bvar 0))) (applied r (.bvar 1) (.bvar 0))

/-- The checked defining equations of a test. -/
def TestEquations (entries : Environment β) (nat succ r yes no : ConstRef β) : NatTest → Prop
  | .beq => BeqEquations.{u,v} entries nat succ r yes no
  | .ble => BleEquations.{u,v} entries nat succ r yes no

/-- A natural family with its zero and successor. -/
def NaturalFamily (entries : Environment β) (nat zero succ : ConstRef β) : Prop :=
  ∃ entry, entries nat = some entry ∧ .natural zero succ ∈ entry.facts ∧ entry.universes = 0

/-- A constant that computes `op`. -/
def Computes (entries : Environment β) (r : ConstRef β) (op : NatOp) : Prop :=
  ∃ entry, entries r = some entry ∧ .natOp op ∈ entry.facts ∧ entry.universes = 0

/-- A fact's meaning in every realization, at the empty universe instance. -/
def FactClaim (entries : Environment β) (r : ConstRef β) (fact : ConstantFact β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ env : Nat → V, fact.Meaning constants r [] env

variable {entries : Environment β} {V : Type v} [SetTheory V] {constants : Assignment β V}

theorem NaturalFamily.meaning {nat zero succ : ConstRef β} (h : NaturalFamily entries nat zero succ)
    (hM : Realizes constants entries) : NaturalMeaning constants nat zero succ := by
  obtain ⟨entry, he, hf, hu⟩ := h
  exact (hM.factMeaning nat entry he _ hf [] (by simp [hu]) fun _ => empty).2

theorem Computes.value {r : ConstRef β} {op : NatOp} (h : Computes entries r op)
    (hM : Realizes constants entries) (a b : Nat) :
    op.apply (constants r []) a b = Numeral.value (op.eval a b) := by
  obtain ⟨entry, he, hf, hu⟩ := h
  exact (hM.factMeaning r entry he _ hf [] (by simp [hu]) fun _ => empty).2 a b

theorem unary_valid {nat zero succ : ConstRef β} (hN : NaturalMeaning constants nat zero succ)
    (a : Nat) (env : Nat → V) :
    (unaryContext nat).Valid constants [] (Valuation.cons (Numeral.value a) env) := by
  intro i A hi
  cases i with
  | zero =>
    simp only [unaryContext, Context.push, natType, AExpr.liftN, List.map_nil,
      List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨trivial, by simpa only [interp, List.map_nil, Valuation.cons_zero, Valuation.cons_succ] using hN.member a⟩
  | succ i => simp [unaryContext, Context.push] at hi

theorem binary_valid {nat zero succ : ConstRef β} (hN : NaturalMeaning constants nat zero succ)
    (a b : Nat) (env : Nat → V) :
    (binaryContext nat).Valid constants []
      (Valuation.cons (Numeral.value b) (Valuation.cons (Numeral.value a) env)) := by
  intro i A hi
  match i with
  | 0 =>
    simp only [binaryContext, unaryContext, Context.push, natType, AExpr.liftN, List.map_nil,
      List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨trivial, by simpa only [interp, List.map_nil, Valuation.cons_zero, Valuation.cons_succ] using hN.member b⟩
  | 1 =>
    simp only [binaryContext, unaryContext, Context.push, natType, AExpr.liftN, List.map_nil,
      List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨trivial, by simpa only [interp, List.map_nil, Valuation.cons_zero, Valuation.cons_succ] using hN.member a⟩
  | i + 2 => simp [binaryContext, unaryContext, Context.push] at hi

theorem Holds.eval {Γ : Context β} {lhs rhs : AExpr β} (h : Holds.{u,v} entries Γ lhs rhs)
    (hM : Realizes constants entries) {env : Nat → V} (hΓ : Γ.Valid constants [] env) :
    interp constants [] env lhs = interp constants [] env rhs :=
  h.1 V constants hM [] env hΓ (h.2.1 V constants hM [] env hΓ) (h.2.2 V constants hM [] env hΓ)

/-- A binary operation's values on numerals follow from its value at `0` and
its recurrence, by induction on the second argument. -/
theorem binary_values (F : V) (op : NatOp) (hbin : op ≠ .pred)
    (h0 : ∀ a, app (app F (Numeral.value a)) (Numeral.value 0) = Numeral.value (op.eval a 0))
    (h1 : ∀ a b, app (app F (Numeral.value a)) (Numeral.value b) = Numeral.value (op.eval a b) →
      app (app F (Numeral.value a)) (Numeral.value (b + 1)) = Numeral.value (op.eval a (b + 1)))
    (a b : Nat) : op.apply F a b = Numeral.value (op.eval a b) := by
  have hv : app (app F (Numeral.value a)) (Numeral.value b) = Numeral.value (op.eval a b) := by
    induction b with
    | zero => exact h0 a
    | succ b ih => exact h1 a b ih
  cases op with
  | pred => exact absurd rfl hbin
  | _ => exact hv

theorem BinaryEquations.meaning {nat zero succ r helper : ConstRef β} {op : NatOp}
    (h : BinaryEquations.{u,v} entries nat succ r helper op) (hbin : op ≠ .pred)
    (hN : NaturalFamily entries nat zero succ)
    (hH : ∀ hop, helperOp op = some hop → Computes entries helper hop) :
    FactClaim.{u,v} entries r (.natOp op) := by
  intro V _ constants hM env
  have nm := hN.meaning hM
  refine ⟨rfl, binary_values (constants r []) op hbin (fun a => ?_) (fun a b ih => ?_)⟩
  · have he := h.base.eval hM (unary_valid nm a env)
    cases op <;>
      simp only [applied, baseRhs, interp, List.map_nil, Valuation.cons_zero, NatOp.eval,
        Nat.add_zero, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero] at he ⊢ <;>
      first | exact absurd rfl hbin | exact he
  · have he := h.step.eval hM (binary_valid nm a b env)
    simp only [applied, succOf, interp, List.map_nil, Valuation.cons_zero,
      Valuation.cons_succ, nm.succValue] at he
    rw [he]
    cases op with
    | pred => exact absurd rfl hbin
    | add =>
      simp only [stepRhs, succOf, applied, interp, List.map_nil, Valuation.cons_zero,
        Valuation.cons_succ, NatOp.eval] at ih ⊢
      rw [ih, nm.succValue]
      congr 1
    | sub =>
      have hp := (hH .pred rfl).value hM (a - b) 0
      simp only [stepRhs, applied, interp, List.map_nil, Valuation.cons_zero,
        Valuation.cons_succ, NatOp.eval, NatOp.apply] at ih hp ⊢
      rw [ih, hp]
      congr 1
    | mul =>
      have hp := (hH .add rfl).value hM (a * b) a
      simp only [stepRhs, applied, interp, List.map_nil, Valuation.cons_zero,
        Valuation.cons_succ, NatOp.eval, NatOp.apply] at ih hp ⊢
      rw [ih, hp, Nat.mul_succ]
    | pow =>
      have hp := (hH .mul rfl).value hM (a ^ b) a
      simp only [stepRhs, applied, interp, List.map_nil, Valuation.cons_zero,
        Valuation.cons_succ, NatOp.eval, NatOp.apply] at ih hp ⊢
      rw [ih, hp, Nat.pow_succ]

theorem PredEquations.meaning {nat zero succ r : ConstRef β}
    (h : PredEquations.{u,v} entries nat succ r) (hN : NaturalFamily entries nat zero succ) :
    FactClaim.{u,v} entries r (.natOp .pred) := by
  intro V _ constants hM env
  have nm := hN.meaning hM
  refine ⟨rfl, fun a _ => ?_⟩
  cases a with
  | zero =>
    have he := h.base.eval hM (Context.valid_nil constants [] env)
    simpa only [interp, List.map_nil, NatOp.apply, NatOp.eval] using he
  | succ a =>
    have he := h.step.eval hM (unary_valid nm a env)
    simp only [succOf, interp, List.map_nil, Valuation.cons_zero, nm.succValue] at he
    simpa only [NatOp.apply, NatOp.eval, Nat.add_sub_cancel] using he

/-- A test's values on numerals follow from its values at zero and its
recurrence, by induction on the first argument. -/
theorem test_values (F Y N : V) (test : NatTest)
    (hzero : ∀ b, app (app F (Numeral.value 0)) (Numeral.value b) = if test.eval 0 b then Y else N)
    (hsz : ∀ a, app (app F (Numeral.value (a + 1))) (Numeral.value 0) = N)
    (hss : ∀ a b, app (app F (Numeral.value (a + 1))) (Numeral.value (b + 1)) =
      app (app F (Numeral.value a)) (Numeral.value b)) :
    ∀ a b, app (app F (Numeral.value a)) (Numeral.value b) = if test.eval a b then Y else N := by
  intro a
  induction a with
  | zero => exact hzero
  | succ a ih =>
    intro b
    cases b with
    | zero => rw [hsz]; cases test <;> simp [NatTest.eval]
    | succ b => rw [hss, ih]; cases test <;> simp [NatTest.eval]

theorem TestEquations.meaning {nat zero succ r yes no : ConstRef β} {test : NatTest}
    (h : TestEquations.{u,v} entries nat succ r yes no test)
    (hN : NaturalFamily entries nat zero succ) :
    FactClaim.{u,v} entries r (.natTest test yes no) := by
  intro V _ constants hM env
  have nm := hN.meaning hM
  have succ_arg : ∀ x, app (constants succ []) (Numeral.value x) = Numeral.value (x + 1) :=
    nm.succValue
  refine ⟨rfl, ?_⟩
  cases test with
  | beq =>
    have h : BeqEquations.{u,v} entries nat succ r yes no := h
    refine test_values _ _ _ .beq (fun b => ?_) (fun a => ?_) (fun a b => ?_)
    · cases b with
      | zero =>
        have he := h.zeroZero.eval hM (Context.valid_nil constants [] env)
        simp only [applied, interp, List.map_nil] at he
        simpa [NatTest.eval] using he
      | succ b =>
        have he := h.zeroSucc.eval hM (unary_valid nm b env)
        simp only [applied, succOf, interp, List.map_nil, Valuation.cons_zero, succ_arg] at he
        simpa [NatTest.eval] using he
    · have he := h.succZero.eval hM (unary_valid nm a env)
      simpa only [applied, succOf, interp, List.map_nil, Valuation.cons_zero, succ_arg] using he
    · have he := h.succSucc.eval hM (binary_valid nm a b env)
      simpa only [applied, succOf, interp, List.map_nil, Valuation.cons_zero, Valuation.cons_succ,
        succ_arg] using he
  | ble =>
    have h : BleEquations.{u,v} entries nat succ r yes no := h
    refine test_values _ _ _ .ble (fun b => ?_) (fun a => ?_) (fun a b => ?_)
    · have he := h.zero.eval hM (unary_valid nm b env)
      simp only [applied, interp, List.map_nil, Valuation.cons_zero] at he
      simpa [NatTest.eval] using he
    · have he := h.succZero.eval hM (unary_valid nm a env)
      simpa only [applied, succOf, interp, List.map_nil, Valuation.cons_zero, succ_arg] using he
    · have he := h.succSucc.eval hM (binary_valid nm a b env)
      simpa only [applied, succOf, interp, List.map_nil, Valuation.cons_zero, Valuation.cons_succ,
        succ_arg] using he

/-! ## Checking the equations -/

open Certified (CheckedClaim)

variable [DecidableEq β]

/-- Establish an equation: both sides are inferred, hence formed, and they
convert. -/
def checkEquation (fuel : Nat) (entries : Environment β) (Γ : Context β) (lhs rhs : AExpr β) :
    Option (CheckedClaim.{u} (Holds.{u,v} entries Γ lhs rhs)) :=
  match inferA.{u,v} fuel entries Γ lhs, inferA.{u,v} fuel entries Γ rhs with
  | .ok ⟨_, hl⟩, .ok ⟨_, hr⟩ =>
    match isDefEq.{u,v} fuel entries Γ lhs rhs with
    | .ok ⟨hc⟩ => some ⟨⟨hc, hl.formed, hr.formed⟩⟩
    | .error _ => none
  | _, _ => none

def checkBinary (fuel : Nat) (entries : Environment β) (nat succ r helper : ConstRef β)
    (op : NatOp) : Option (CheckedClaim.{u} (BinaryEquations.{u,v} entries nat succ r helper op)) := do
  let ⟨base⟩ ← checkEquation.{u,v} fuel entries (unaryContext nat)
    (applied r (.bvar 0) (.natLit nat 0)) (baseRhs nat op)
  let ⟨step⟩ ← checkEquation.{u,v} fuel entries (binaryContext nat)
    (applied r (.bvar 1) (succOf succ (.bvar 0))) (stepRhs succ r helper op)
  pure ⟨⟨base, step⟩⟩

def checkPred (fuel : Nat) (entries : Environment β) (nat succ r : ConstRef β) :
    Option (CheckedClaim.{u} (PredEquations.{u,v} entries nat succ r)) := do
  let ⟨base⟩ ← checkEquation.{u,v} fuel entries [] (.app (.const r []) (.natLit nat 0))
    (.natLit nat 0)
  let ⟨step⟩ ← checkEquation.{u,v} fuel entries (unaryContext nat)
    (.app (.const r []) (succOf succ (.bvar 0))) (.bvar 0)
  pure ⟨⟨base, step⟩⟩

def checkTest (fuel : Nat) (entries : Environment β) (nat succ r yes no : ConstRef β) :
    (test : NatTest) → Option (CheckedClaim.{u} (TestEquations.{u,v} entries nat succ r yes no test))
  | .beq => do
    let ⟨zeroZero⟩ ← checkEquation.{u,v} fuel entries []
      (applied r (.natLit nat 0) (.natLit nat 0)) (.const yes [])
    let ⟨zeroSucc⟩ ← checkEquation.{u,v} fuel entries (unaryContext nat)
      (applied r (.natLit nat 0) (succOf succ (.bvar 0))) (.const no [])
    let ⟨succZero⟩ ← checkEquation.{u,v} fuel entries (unaryContext nat)
      (applied r (succOf succ (.bvar 0)) (.natLit nat 0)) (.const no [])
    let ⟨succSucc⟩ ← checkEquation.{u,v} fuel entries (binaryContext nat)
      (applied r (succOf succ (.bvar 1)) (succOf succ (.bvar 0))) (applied r (.bvar 1) (.bvar 0))
    pure ⟨(⟨zeroZero, zeroSucc, succZero, succSucc⟩ : BeqEquations.{u,v} entries nat succ r yes no)⟩
  | .ble => do
    let ⟨zero⟩ ← checkEquation.{u,v} fuel entries (unaryContext nat)
      (applied r (.natLit nat 0) (.bvar 0)) (.const yes [])
    let ⟨succZero⟩ ← checkEquation.{u,v} fuel entries (unaryContext nat)
      (applied r (succOf succ (.bvar 0)) (.natLit nat 0)) (.const no [])
    let ⟨succSucc⟩ ← checkEquation.{u,v} fuel entries (binaryContext nat)
      (applied r (succOf succ (.bvar 1)) (succOf succ (.bvar 0))) (applied r (.bvar 1) (.bvar 0))
    pure ⟨(⟨zero, succZero, succSucc⟩ : BleEquations.{u,v} entries nat succ r yes no)⟩

def decideComputes (entries : Environment β) (r : ConstRef β) (op : NatOp) :
    Option (CheckedClaim.{u} (Computes entries r op)) :=
  match he : entries r with
  | some entry =>
    if hf : ConstantFact.natOp op ∈ entry.facts then
      if hu : entry.universes = 0 then some ⟨⟨entry, he, hf, hu⟩⟩ else none
    else none
  | none => none

/-- Whether a normal form is the literal `n`: a literal, zero, or a successor
of a literal or of zero. -/
def isNumeral (zero succ : ConstRef β) (n : Nat) : AExpr β → Bool
  | .natLit _ m => m == n
  | .const z [] => z == zero && n == 0
  | .app (.const s []) (.natLit _ m) => s == succ && m + 1 == n
  | .app (.const s []) (.const z []) => s == succ && z == zero && n == 1
  | _ => false

/-- The binary operations a definition may compute, read off the normal form
of its value at `#0` and `0`; the equations decide. -/
def binaryCandidates (zero succ : ConstRef β) (atZero : AExpr β) : List NatOp :=
  match atZero with
  | .bvar 0 => [.add, .sub]
  | e => if isNumeral zero succ 0 e then [.mul] else if isNumeral zero succ 1 e then [.pow] else []

/-- A checked arithmetic fact of a constant, with its meaning. -/
structure CheckedFact (entries : Environment β) (r : ConstRef β) : Type u where
  fact : ConstantFact β
  claim : FactClaim.{u,v} entries r fact
  scope : fact.Scope 0

/-- The operation a binary definition computes, if its equations check. -/
def certifyBinary (fuel : Nat) (natOps : List (NatOp × ConstRef β)) (entries : Environment β)
    (nat zero succ r : ConstRef β) (hN : NaturalFamily entries nat zero succ) :
    Option (CheckedFact.{u,v} entries r) :=
  let atZero := (whnf.{u,v} fuel entries (unaryContext nat) (applied r (.bvar 0) (.natLit nat 0))).result
  (binaryCandidates zero succ atZero).firstM fun op =>
    if hbin : op = .pred then none else
    match hh : helperOp op with
    | none => do
      let ⟨eqs⟩ ← checkBinary.{u,v} fuel entries nat succ r r op
      pure ⟨.natOp op, eqs.meaning hbin hN (fun _ h => by rw [hh] at h; cases h), rfl⟩
    | some hop => do
      let helper ← natOps.lookup hop
      let ⟨hc⟩ ← decideComputes entries helper hop
      let ⟨eqs⟩ ← checkBinary.{u,v} fuel entries nat succ r helper op
      pure ⟨.natOp op, eqs.meaning hbin hN (fun _ h => by rw [hh] at h; cases h; exact hc), rfl⟩

/-- The test a definition of type `N → N → B` computes, if its equations
check: the outcomes are its values at `0, 0` and `1, 0`. -/
def certifyTest (fuel : Nat) (entries : Environment β) (nat zero succ r : ConstRef β)
    (hN : NaturalFamily entries nat zero succ) : Option (CheckedFact.{u,v} entries r) :=
  let value (a : Nat) : AExpr β :=
    (whnf.{u,v} fuel entries [] (applied r (.natLit nat a) (.natLit nat 0))).result
  match value 0, value 1 with
  | .const yes [], .const no [] =>
    if yes = no then none else
    [NatTest.beq, .ble].firstM fun test => do
      let ⟨eqs⟩ ← checkTest.{u,v} fuel entries nat succ r yes no test
      pure ⟨.natTest test yes no, eqs.meaning hN, rfl⟩
  | _, _ => none

/-- The arithmetic fact of a definition of type `N → N → N`, `N → N` or
`N → N → B`, for a natural family `N`, if its defining equations check. -/
def certify (fuel : Nat) (natOps : List (NatOp × ConstRef β)) (entries : Environment β)
    (r : ConstRef β) (type : AExpr β) : Option (CheckedFact.{u,v} entries r) :=
  let family : (nat : ConstRef β) →
      Option ((zero succ : ConstRef β) ×' NaturalFamily entries nat zero succ) :=
    fun nat =>
      match hn : entries nat with
      | some entry =>
        match findNatural entry.facts with
        | some ⟨(zero, succ), hf⟩ =>
          if hu : entry.universes = 0 then some ⟨zero, succ, entry, hn, hf, hu⟩ else none
        | none => none
      | none => none
  match type with
  | .forallE _ (.const nat []) (.forallE _ (.const a []) (.const b [])) =>
    if a = nat then do
      let ⟨zero, succ, hN⟩ ← family nat
      if b = nat then certifyBinary.{u,v} fuel natOps entries nat zero succ r hN
      else certifyTest.{u,v} fuel entries nat zero succ r hN
    else none
  | .forallE _ (.const nat []) (.const a []) =>
    if a = nat then do
      let ⟨_, succ, hN⟩ ← family nat
      let ⟨eqs⟩ ← checkPred.{u,v} fuel entries nat succ r
      pure ⟨.natOp .pred, eqs.meaning hN, rfl⟩
    else none
  | _ => none

end Ix.Kernel.Arithmetic
