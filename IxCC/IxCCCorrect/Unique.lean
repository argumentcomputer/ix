import IxCK.Kernel.Admission.TierTheorems
import IxCCGrounding.BigNatBridge
import IxCCCorrect.Tiers

/-!
# The answer is unique (`IxCCCorrect.Unique`)

`Agrees claim acc xs answer` says the target applied to `xs` and the answer's term denote the same
set in every model of the admitted environment. On its own that does not pin the answer down: if
no model exists every number agrees, and a model may identify two numerals. This module states
when it does:

```lean
agrees_unique : (∃ V : Type u, Nonempty (SetTheory V)) → numeralBasisB acc.env kNe = true →
  claim.abi.result = .nat → Agrees claim acc xs a → Agrees claim acc xs b → a = b
```

**What it rests on.**

* A model exists: the kernel's main theorem for the tiered entry
  (`Ix.Kernel.Admission.checkConstantsWith_has_model`, here as `accepted_has_model`), in any set
  theory; that some set theory with the kernel's universes exists is the hypothesis.
* Numerals are separated in it: the grounding library proves `litSet_inj`
  (`IxCCGrounding.BigNatBridge`) from the model's numeral law at `Nat.beq` (`lit_ops`) once
  `Bool.true ≠ Bool.false`, and proves that (`bool_true_ne_false`) from `eq_equality` and
  `false_empty` **given a stored theorem `Bool.true = Bool.false → False`**.

So uniqueness is conditional on the committed environment: `numeralBasisB acc.env kNe` decides that
it stores `Nat` and its constructors, `Bool` and its constructors, `Eq`, `Nat.beq` as a definition
without level parameters, and at the key `kNe` a constant of type
`@Eq.{1} Bool Bool.true Bool.false → False`. The first three hold wherever `groundCheck` accepts a
program that uses them; **the last two are constants a compiled program's closure need not
contain**. No law of `Ix.Kernel.Model` separates `Bool.true` from `Bool.false` without such a
constant (or a stored recursor to eliminate into `Prop` with), so an environment without them has,
as far as the model's laws say, models that identify numerals. A front end that wants the
functional statement to determine the answer adds the two witnesses to the committed environment.

Stated at a `Nat` result. At an enumeration result uniqueness is constructor disjointness in the
model, which needs the enumeration's own stored recursor; not here.
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Grounding

universe u

/-- **The environment the kernel installed has a model in every set theory**
(`checkConstantsWith_has_model`, through the tiered entry's accept that `Accepted` carries). -/
theorem accepted_has_model (V : Type u) [Ix.Kernel.SetTheory V]
    (acc : Src.KernelFront.Accepted) : Nonempty (Model V acc.env) := by
  obtain ⟨-, t, pre, constants, -, -, -, hc⟩ :=
    Ix.Kernel.Admission.checkBytesTieredUsing_ok acc.accepted
  exact Ix.Kernel.Admission.checkConstantsWith_has_model V
    (Ix.Kernel.Admission.checkConstantsTiered_ok V hc).1

/-- **What separates numerals in a model of `env`**, each a stored fact: `Nat` and its
constructors, `Bool` and its constructors, the built-in `Eq`, `Nat.beq` without level parameters,
the `Nat` roles stored as definitions, and at `kNe` a constant of type
`Bool.true = Bool.false → False`. -/
structure NumeralBasis (env : KEnv) (kNe : KKey) : Prop where
  nat : NatBasis env
  bool : BoolBasis env
  eq : EqBasis env
  beq : NatBeqStored env
  litDefs : LitDefs env
  ne : BoolTrueNeFalseStored env kNe

/-- `NumeralBasis`, decided. -/
def numeralBasisB (env : KEnv) (kNe : KKey) : Bool :=
  natBasisB env && boolBasisB env && eqBasisB env && natBeqStoredB env && litDefsB env &&
    boolTrueNeFalseB env kNe

theorem numeralBasis_of_check {env : KEnv} {kNe : KKey} (h : numeralBasisB env kNe = true) :
    NumeralBasis env kNe := by
  simp only [numeralBasisB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨natBasis_of h1, boolBasis_of_check h2, eqBasis_of_check h3, natBeqStored_of_check h4,
    litDefs_of_check h5, boolTrueNeFalse_of_check h6⟩

/-- **Two numerals with the same denotation as one term are equal**, where a model of the
environment exists and the environment stores what separates numerals. -/
theorem sameDenotation_lit_unique {env : KEnv} {kNe : KKey} (hB : NumeralBasis env kNe)
    {V : Type u} [Ix.Kernel.SetTheory V] (M : Model V env) {t : KExpr} {a b : Nat}
    (ha : SameDenotation.{u} env t (litE a)) (hb : SameDenotation.{u} env t (litE b)) : a = b := by
  obtain ⟨X, hX, hXa⟩ := ha V M (fun _ => 0) (fun _ => empty)
  obtain ⟨Y, hY, hYb⟩ := hb V M (fun _ => 0) (fun _ => empty)
  obtain rfl : X = Y := Denotes_functional hX hY
  have hF := natFacts M hB.nat (fun _ => 0)
  have h1 : X = litSet M (fun _ => 0) a := (lit_den M hF (fun _ => empty) a X).mp hXa
  have h2 : X = litSet M (fun _ => 0) b := (lit_den M hF (fun _ => empty) b X).mp hYb
  exact litSet_inj M (natAccel_of_litOps M.lit_ops hB.litDefs) hB.nat hB.bool hB.beq
    (bool_true_ne_false M hB.eq hB.bool hB.ne (fun _ => 0)) (h1.symm.trans h2)

/-- **The answer is unique** at a `Nat` result: two answers that agree with the kernel meaning of
the claim's target on the same arguments are equal, if a set theory with the kernel's universes
exists and the admitted environment stores what separates numerals (`numeralBasisB`). -/
theorem agrees_unique {claim : Claim} {acc : Src.KernelFront.Accepted} {kNe : KKey}
    (hV : ∃ V : Type u, Nonempty (Ix.Kernel.SetTheory V))
    (hB : numeralBasisB acc.env kNe = true) (hres : claim.abi.result = ResTy.nat)
    {xs : List Nat} {a b : Answer} (ha : Agrees.{u} claim acc xs a) (hb : Agrees.{u} claim acc xs b) :
    a = b := by
  obtain ⟨V, ⟨inst⟩⟩ := hV
  haveI : Ix.Kernel.SetTheory V := inst
  obtain ⟨M⟩ := accepted_has_model V acc
  unfold Agrees at ha hb
  obtain ⟨t1, o1, hk1, ht1, hs1⟩ := ha
  obtain ⟨t2, o2, hk2, ht2, hs2⟩ := hb
  rw [hk1] at hk2
  cases hk2
  cases a with
  | node _ _ => simp [answerTerm, hres] at ht1
  | nat na =>
    cases b with
    | node _ _ => simp [answerTerm, hres] at ht2
    | nat nb =>
      simp only [answerTerm, hres, Option.some.injEq] at ht1 ht2
      subst ht1
      subst ht2
      exact congrArg Answer.nat (sameDenotation_lit_unique (numeralBasis_of_check hB) M hs1 hs2)

end IxCC.Correct
