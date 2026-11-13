import IxVMRefinement.Iota.Major
import IxVMRefinement.Iota.Certs
import IxVMRefinement.Iota.RecKernel
import IxVMRefinement.Whnf.Basic
import IxVMRefinement.Core.Roles
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Lib.Words
import IxC.Kernel.Semantics.BasisRules
import IxC.Kernel.Verify.PropWhen
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Verify.Shift

/-! # `red_quot`: the quotient's ι

`Quot.lift` and `Quot.ind` are stored recursors of the pinned basis (`EnvFacts.quotBasis`), with
one rule each, for `Quot.mk` (`Ix.Kernel.Semantics.quotLiftRule`, `quotIndRule`). IxVM checks the
major's head is the constant the table binds to `Quot.mk`, with three arguments and its level
equal to the eliminator's first, and returns the rule's right-hand side already β-reduced: the
function (`Quot.lift`) or the minor premise (`Quot.ind`) applied to the packed element.

In the model that is `Red.iota` at the stored recursor, then one `β` per binder of the rule's
right-hand side. The right-hand side's binders before the last are the eliminator's own binders
(same domains, same zero-ness data: `QuotTele`), so `quot_certs`' walk of the eliminator's type
certifies each of those `β`s (a skipped slot is a `never` datum, a gated `β`); the last `β` is
`quot_certs`' last premise, or gated at a never-zero motive level of `Quot.lift`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red Certs Infer DefEq)
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Helpers -/

theorem quot_tml_lbb {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {As : List KExpr} {p : SourceValue F} (hAs : TmL κ d Γ h As p) :
    ∀ a ∈ As, a.looseBVarsBounded 0 = true := by
  induction hAs with
  | nil _ => intro a ha; cases ha
  | cons _ hx _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Tm.looseBVarsBounded hx
    · exact ih a ha

theorem quot_inst_closed {a : KExpr} (ha : a.looseBVarsBounded 0 = true) :
    ∀ v k, a.instantiate1 v k = a := fun v k =>
  Ix.Kernel.Expr.instantiate1_eq_self (Ix.Kernel.Expr.looseBVarsBounded_mono (Nat.zero_le k) ha)

theorem quot_evalEqList_length {φ : Ix.Kernel.LevelParam → Nat} :
    ∀ {us vs : List KLevel}, Ix.Kernel.Level.EvalEqList φ us vs → us.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [quot_evalEqList_length h.2]
  | [], _ :: _, h => (h : False).elim
  | _ :: _, [], h => (h : False).elim

theorem quot_lvEqList_length {us vs : List KLevel} (h : LvEqList us vs) :
    us.length = vs.length :=
  quot_evalEqList_length (h fun _ => 0)

theorem quot_mul3_one {s : F} {p q : Prop} [Decidable p] [Decidable q]
    (h : (1 : F) = s * (if p then 1 else 0) * (if q then 1 else 0)) : s ≠ 0 ∧ p ∧ q := by
  by_cases hp : p
  · by_cases hq : q
    · refine ⟨fun hs => ?_, hp, hq⟩
      rw [hs, zero_mul, zero_mul] at h
      exact one_ne_zero h
    · rw [ite_eq_right hq, mul_zero] at h
      exact absurd h one_ne_zero
  · rw [ite_eq_right hp, mul_zero, zero_mul] at h
    exact absurd h one_ne_zero

theorem quot_list1 {α : Type} : ∀ {l : List α}, l.length = 1 → ∃ a, l = [a]
  | [a], _ => ⟨a, rfl⟩
  | [], h | _ :: _ :: _, h => by simp only [List.length_cons, List.length_nil] at h <;> omega

theorem quot_list2 {α : Type} : ∀ {l : List α}, l.length = 2 → ∃ a b, l = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩
  | [], h | [_], h | _ :: _ :: _ :: _, h => by
    simp only [List.length_cons, List.length_nil] at h <;> omega

theorem quot_list3 {α : Type} : ∀ {l : List α}, l.length = 3 → ∃ a b c, l = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => by
    simp only [List.length_cons, List.length_nil] at h <;> omega

theorem quot_list5 {α : Type} : ∀ {l : List α}, 5 ≤ l.length →
    ∃ a0 a1 a2 a3 a4 rest, l = a0 :: a1 :: a2 :: a3 :: a4 :: rest
  | a0 :: a1 :: a2 :: a3 :: a4 :: rest, _ => ⟨a0, a1, a2, a3, a4, rest, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => by
    simp only [List.length_cons, List.length_nil] at h <;> omega

theorem quot_list6 {α : Type} : ∀ {l : List α}, 6 ≤ l.length →
    ∃ a0 a1 a2 a3 a4 a5 rest, l = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest, _ => ⟨a0, a1, a2, a3, a4, a5, rest, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h => by
    simp only [List.length_cons, List.length_nil] at h <;> omega

theorem quot_val_lit (k : Nat) (hk : k < 18446744069414584321) :
    ZMod.val ((k : Nat) : F) = k :=
  NatAux.val_natCast hk

/-- The level the circuit compares (`Quot.mk`'s) is semantically the eliminator's first. -/
theorem quot_lev {us mus ls mls : List KLevel} {m0 l0 : KLevel}
    (hus : LvEqList us ls) (hmus : LvEqList mus mls) (hml : mls.length = 1)
    (hm : mls[0]? = some m0) (hl : ls[0]? = some l0)
    (heq : ∀ φ, Ix.Kernel.Level.eval φ m0 = Ix.Kernel.Level.eval φ l0) :
    ∀ φ, Ix.Kernel.Level.EvalEqList φ mus (us.take 1) := by
  intro φ
  have h1 := hmus φ
  have h2 := hus φ
  rcases mls with _ | ⟨z, _ | ⟨z', zt⟩⟩
  · simp at hml
  · have hz : z = m0 := by simpa using hm
    subst hz
    rcases ls with _ | ⟨l, lt⟩
    · simp at hl
    · have hl' : l = l0 := by simpa using hl
      subst hl'
      rcases mus with _ | ⟨m, _ | ⟨m', mt⟩⟩
      · exact (h1 : False).elim
      · rcases us with _ | ⟨u, ut⟩
        · exact (h2 : False).elim
        · exact ⟨h1.1.trans ((heq φ).trans h2.1.symm), trivial⟩
      · exact (h1.2 : False).elim
  · simp at hml

/-! ## Telescopes of the rule's right-hand side -/

/-- The first `n` binders of a `∀`-telescope and of a `λ`-telescope have the same domains and
the same zero-ness data. -/
inductive QuotTele : Nat → KExpr → KExpr → Prop where
  | zero {T R : KExpr} : QuotTele 0 T R
  | succ {n : Nat} {ty BT BR : KExpr} {m mR : Ix.Kernel.BinderMeta} :
      m.pw = mR.pw → QuotTele n BT BR → QuotTele (n + 1) (.forallE ty BT m) (.lam ty BR mR)

theorem QuotTele.inst {n : Nat} {T R : KExpr} (ht : QuotTele n T R) (a : KExpr) :
    ∀ j, QuotTele n (T.instantiate1 a j) (R.instantiate1 a j) := by
  induction ht with
  | zero => intro j; exact .zero
  | @succ n ty BT BR m mR hm _ ih =>
    intro j
    show QuotTele (n + 1) (.forallE (ty.instantiate1 a j) (BT.instantiate1 a (j + 1)) m)
      (.lam (ty.instantiate1 a j) (BR.instantiate1 a (j + 1)) mR)
    exact .succ hm (ih (j + 1))

theorem QuotTele.instLP {n : Nat} {T R : KExpr} (ht : QuotTele n T R)
    (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    QuotTele n (T.instantiateLevelParams ks us) (R.instantiateLevelParams ks us) := by
  induction ht with
  | zero => exact .zero
  | @succ n ty BT BR m mR hm _ ih =>
    show QuotTele (n + 1)
      (.forallE (ty.instantiateLevelParams ks us) (BT.instantiateLevelParams ks us)
        { m with pw := Ix.Kernel.Level.substPW ks us m.pw })
      (.lam (ty.instantiateLevelParams ks us) (BR.instantiateLevelParams ks us)
        { mR with pw := Ix.Kernel.Level.substPW ks us mR.pw })
    exact .succ (congrArg (Ix.Kernel.Level.substPW ks us) hm) ih

/-- The body of a binder, instantiated with the argument. -/
def quotBody : KExpr → KExpr → KExpr
  | .lam _ b _, a => b.instantiate1 a
  | .forallE _ b _, a => b.instantiate1 a
  | e, _ => e

/-- The term after one binder per argument. -/
def quotPeel : List KExpr → KExpr → KExpr
  | [], e => e
  | a :: as, e => quotPeel as (quotBody e a)

/-- **`β` along matching binders**: a certificate walk of the `∀`-telescope over the arguments
licenses one `β` per argument of the `λ`-telescope (a skipped slot has datum `never`: a gated
`β`; a certified one: `Red.beta`). -/
theorem quot_red_tele {env : Ix.Kernel.Env .anon} {d : Nat} (rest : List KExpr) :
    ∀ (args : List KExpr) {T R : KExpr} {zs : List KExpr}, QuotTele args.length T R →
      Certs env d true T (args ++ zs) →
      Certs env d true (quotPeel args T) zs ∧
        Red env d (Ix.Kernel.Expr.mkAppN R (args ++ rest))
          (Ix.Kernel.Expr.mkAppN (quotPeel args R) rest)
  | [], T, R, zs, _, hc => ⟨hc, .refl⟩
  | a :: as, T, R, zs, ht, hc => by
    rw [List.length_cons] at ht
    cases ht with
    | @succ n ty BT BR m mR hm ht' =>
      rw [List.cons_append] at hc
      have key : Certs env d true (BT.instantiate1 a) (as ++ zs) ∧
          Red env d (.app (.lam ty BR mR) a) (BR.instantiate1 a) := by
        cases hc with
        | skip hl hn hc' => exact ⟨hc', .betaGate (by rw [← hm]; exact hn)⟩
        | cert hi hd hc' => exact ⟨hc', .beta hi hd⟩
      obtain ⟨hc', hr⟩ := key
      obtain ⟨h1, h2⟩ := quot_red_tele rest as (ht'.inst a 0) hc'
      exact ⟨h1, .trans (red_mkAppN (as ++ rest) hr) h2⟩

/-! ## The stored eliminators -/

theorem quotMkA_ctor :
    (Ix.Kernel.quotMkA (md := .anon)) = .ctorInfo Ix.Kernel.quotMkA.toConstantVal 2 1 := rfl

theorem quotLift_tele :
    QuotTele 5 (Ix.Kernel.quotLiftA (md := .anon)).toConstantVal.type
      (Ix.Kernel.Semantics.quotLiftRule (md := .anon)).rhs :=
  .succ rfl (.succ rfl (.succ rfl (.succ rfl (.succ rfl .zero))))

theorem quotInd_tele :
    QuotTele 4 (Ix.Kernel.quotIndA (md := .anon)).toConstantVal.type
      (Ix.Kernel.Semantics.quotIndRule (md := .anon)).rhs :=
  .succ rfl (.succ rfl (.succ rfl (.succ rfl .zero)))

/-- `Quot.lift`'s right-hand side after the parameters, the motive, the function and the
coherence: `fun a => f a`. -/
theorem quotLift_peel (u0 u1 : KLevel) {a0 a1 a2 a3 a4 : KExpr}
    (c0 : ∀ v k, a0.instantiate1 v k = a0) (c1 : ∀ v k, a1.instantiate1 v k = a1)
    (c2 : ∀ v k, a2.instantiate1 v k = a2) (c3 : ∀ v k, a3.instantiate1 v k = a3)
    (c4 : ∀ v k, a4.instantiate1 v k = a4) :
    quotPeel [a0, a1, a2, a3, a4]
        ((Ix.Kernel.Semantics.quotLiftRule (md := .anon)).rhs.instantiateLevelParams
          [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]) =
      .lam a0 (.app a3 (.bvar 0))
        { pw := (Ix.Kernel.Level.substPW [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]
          (.ifAllZero [Ix.Kernel.vN])) } := by
  simp [quotPeel, quotBody, Ix.Kernel.Semantics.quotLiftRule,
    Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.instantiate1, c0, c1, c2, c3, c4]
  try rfl

/-- `Quot.ind`'s right-hand side after the parameters, the motive and the minor premise:
`fun a => mk a`. -/
theorem quotInd_peel (u0 : KLevel) {a0 a1 a2 a3 : KExpr}
    (c0 : ∀ v k, a0.instantiate1 v k = a0) (c1 : ∀ v k, a1.instantiate1 v k = a1)
    (c2 : ∀ v k, a2.instantiate1 v k = a2) (c3 : ∀ v k, a3.instantiate1 v k = a3) :
    quotPeel [a0, a1, a2, a3]
        ((Ix.Kernel.Semantics.quotIndRule (md := .anon)).rhs.instantiateLevelParams
          [Ix.Kernel.uN] [u0]) =
      .lam a0 (.app a3 (.bvar 0))
        { pw := Ix.Kernel.Level.substPW [Ix.Kernel.uN] [u0] (.ifAllZero []) } := by
  simp [quotPeel, quotBody, Ix.Kernel.Semantics.quotIndRule,
    Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.instantiate1, c0, c1, c2, c3]
  try rfl

/-- `Quot.lift`'s motive level read off the instantiated datum. -/
theorem quotLift_substPW (u0 u1 : KLevel) :
    Ix.Kernel.Level.substPW [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1] (.ifAllZero [Ix.Kernel.vN]) =
      Ix.Kernel.Level.zeronessOf u1 :=
  (Ix.Kernel.Level.zeronessOf_subst [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]
    (.param Ix.Kernel.vN)).symm

/-! ## The kernel step -/

/-- **`Quot.lift`'s ι**: `Red.iota` at the stored `Quot.lift`, then the right-hand side's six
`β`s. -/
theorem quot_lift_red (c : Ctx) (hc : CoreFacts c) {d : Nat} {a b : Bytes.Address}
    {us mus : List KLevel} {As QA : List KExpr} {a3 q2 : KExpr}
    (haddr : c.t.addressOf? .quotLift = some (ixAddr a)) (hin : c.inForce .quotLift)
    (hmk : c.t.addressOf? .quotMk = some (ixAddr b))
    (hus : us.length = 2) (hmus : mus.length = 1)
    (hlev : ∀ φ, Ix.Kernel.Level.EvalEqList φ mus (us.take 1))
    (hAl : 6 ≤ As.length) (hAc : ∀ x ∈ As, x.looseBVarsBounded 0 = true)
    (hQA : QA.length = 3)
    (hred : Red c.env d (As.getD 5 (.bvar 0))
      (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA))
    (h3 : As[3]? = some a3) (h2 : QA[2]? = some q2)
    (hcT : ∀ ci, c.env.find? (c.κ (ixAddr a)) = some ci →
      Specs.Whnf.CertsR c.env d true
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)
        (As.take 5 ++ [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]))
    (hcM : ∀ ci, c.env.find? (c.κ (ixAddr b)) = some ci →
      Specs.Whnf.CertsR c.env d true
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams mus) QA)
    (hlast : (∃ v, us[1]? = some v ∧ v.isNeverZero = true) ∨
      ∃ ta, Infer c.env .io d (QA.getD 2 (.bvar 0)) ta ∧
        DefEq c.env d ta ((As.take 5 ++
          [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]).getD 0 (.bvar 0))) :
    Red c.env d (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr a)) us) As)
      (Ix.Kernel.Expr.mkAppN (.app a3 q2) (As.drop 6)) := by
  have hwf := hc.env.tableWf
  have hka : c.κ (ixAddr a) = Ix.Kernel.quotLiftName := keyOf_of_addressOf hwf haddr
  have hkb : c.κ (ixAddr b) = Ix.Kernel.quotMkName := keyOf_of_addressOf hwf hmk
  have hq : c.inForce .quot := Ctx.inForce_of_block_or_dep hwf hin (.inl (by decide))
  have hfL : c.env.find? Ix.Kernel.quotLiftName = some Ix.Kernel.quotLiftA :=
    hc.env.quotBasis hq Ix.Kernel.quotLiftA (by simp [Ix.Kernel.BasisKind.declsA])
  have hfM : c.env.find? Ix.Kernel.quotMkName = some Ix.Kernel.quotMkA :=
    hc.env.quotBasis hq Ix.Kernel.quotMkA (by simp [Ix.Kernel.BasisKind.declsA])
  rw [hka, hkb] at hcT
  rw [hkb] at hcM hred
  rw [hka]
  obtain ⟨u0, u1, rfl⟩ := quot_list2 hus
  obtain ⟨m0, rfl⟩ := quot_list1 hmus
  obtain ⟨q0, q1, x2, rfl⟩ := quot_list3 hQA
  obtain ⟨a0, a1, a2, y3, a4, a5, rest, rfl⟩ := quot_list6 hAl
  have e3 : a3 = y3 := (by simpa using h3 : y3 = a3).symm
  subst e3
  have e2 : q2 = x2 := (by simpa using h2 : x2 = q2).symm
  subst e2
  have c0 := quot_inst_closed (hAc a0 (by simp))
  have c1 := quot_inst_closed (hAc a1 (by simp))
  have c2 := quot_inst_closed (hAc a2 (by simp))
  have c3 := quot_inst_closed (hAc a3 (by simp))
  have c4 := quot_inst_closed (hAc a4 (by simp))
  -- the walks
  have hcert1 : Certs c.env d true
      ((Ix.Kernel.quotLiftA (md := .anon)).toConstantVal.type.instantiateLevelParams
        [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1])
      ([a0, a1, a2, a3, a4] ++
        [Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotMkName [m0]) [q0, q1, q2]]) :=
    Specs.Whnf.CertsR.toCerts (hcT _ hfL)
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _ rfl)
  have hcert2 : Certs c.env d true
      ((Ix.Kernel.quotMkA (md := .anon)).toConstantVal.type.instantiateLevelParams
        [Ix.Kernel.uN] [m0]) [q0, q1, q2] :=
    Specs.Whnf.CertsR.toCerts (hcM _ hfM)
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _ rfl)
  -- `Red.iota` at the stored `Quot.lift`
  have heA : (Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotLiftName [u0, u1])
      [a0, a1, a2, a3, a4, a5]).getAppArgs = [a0, a1, a2, a3, a4, a5] := by
    rw [getAppArgs_mkAppN]; rfl
  have hMA : (Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotMkName [m0]) [q0, q1, q2]).getAppArgs =
      [q0, q1, q2] := by
    rw [getAppArgs_mkAppN]; rfl
  have hiota := Ix.Kernel.Rules.Red.iota (env := c.env) (d := d)
    (e := Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotLiftName [u0, u1]) [a0, a1, a2, a3, a4, a5])
    (c := Ix.Kernel.quotLiftName) (us := [u0, u1]) (cv := Ix.Kernel.quotLiftA.toConstantVal)
    (mI := 5) (rP := 5) (rules := [Ix.Kernel.Semantics.quotLiftRule])
    (major := Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotMkName [m0]) [q0, q1, q2])
    (cj := Ix.Kernel.quotMkName) (usj := [m0]) (cvj := Ix.Kernel.quotMkA.toConstantVal)
    (cnP := 2) (cnF := 1) (rl := Ix.Kernel.Semantics.quotLiftRule) (residual := .bvar 0)
    (by rw [getAppFn_mkAppN]; rfl)
    (hfL.trans (congrArg some (Ix.Kernel.Semantics.quotLiftA_eq (md := .anon))))
    (by rw [heA]; rfl) rfl (by rw [heA]; exact hred) (by rw [getAppFn_mkAppN]; rfl)
    (hfM.trans (congrArg some quotMkA_ctor))
    (by first | rfl | simp [Ix.Kernel.Semantics.quotLiftRule])
    (by rw [hMA]; rfl)
    (by first | decide | simp [Ix.Kernel.Semantics.quotLiftRule])
    (by rw [heA]; exact hlev)
    (fun h => absurd h (by first | decide |
      simp [Ix.Kernel.RecRule.compareParams, Ix.Kernel.Semantics.quotLiftRule]))
    (by rw [heA]; exact hcert1) (by rw [hMA]; exact hcert2)
    (fun h => absurd rfl h) (fun h => absurd rfl h)
  rw [heA, hMA] at hiota
  -- the right-hand side's `β`s
  obtain ⟨-, hchain⟩ := quot_red_tele [q2] [a0, a1, a2, a3, a4]
    (quotLift_tele.instLP [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]) hcert1
  rw [quotLift_peel u0 u1 c0 c1 c2 c3 c4] at hchain
  have hbody : (Ix.Kernel.Expr.app a3 (.bvar 0)).instantiate1 q2 = .app a3 q2 := by
    simp [Ix.Kernel.Expr.instantiate1, c3]
  have hlastR : Red c.env d
      (.app (.lam a0 (.app a3 (.bvar 0))
        { pw := (Ix.Kernel.Level.substPW [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]
          (.ifAllZero [Ix.Kernel.vN])) }) q2) (.app a3 q2) := by
    rw [← hbody]
    rcases hlast with ⟨v, hv, hnz⟩ | ⟨ta, hi, hd⟩
    · have hv1 : u1 = v := by simpa using hv
      subst hv1
      refine .betaGate ?_
      show (Ix.Kernel.Level.substPW [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]
        (.ifAllZero [Ix.Kernel.vN])).isNever = true
      rw [quotLift_substPW, ← Ix.Kernel.Level.isNeverZero_eq_isNever]
      exact hnz
    · exact .beta hi hd
  have hmain : Red c.env d
      (Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotLiftName [u0, u1]) [a0, a1, a2, a3, a4, a5])
      (.app a3 q2) :=
    .trans hiota (.trans hchain hlastR)
  exact red_mkAppN rest hmain

/-- **`Quot.ind`'s ι**: `Red.iota` at the stored `Quot.ind`, then the right-hand side's five
`β`s. -/
theorem quot_ind_red (c : Ctx) (hc : CoreFacts c) {d : Nat} {a b : Bytes.Address}
    {us mus : List KLevel} {As QA : List KExpr} {a3 q2 : KExpr}
    (haddr : c.t.addressOf? .quotInd = some (ixAddr a)) (hin : c.inForce .quotInd)
    (hmk : c.t.addressOf? .quotMk = some (ixAddr b))
    (hus : us.length = 1) (hmus : mus.length = 1)
    (hlev : ∀ φ, Ix.Kernel.Level.EvalEqList φ mus (us.take 1))
    (hAl : 5 ≤ As.length) (hAc : ∀ x ∈ As, x.looseBVarsBounded 0 = true)
    (hQA : QA.length = 3)
    (hred : Red c.env d (As.getD 4 (.bvar 0))
      (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA))
    (h3 : As[3]? = some a3) (h2 : QA[2]? = some q2)
    (hcT : ∀ ci, c.env.find? (c.κ (ixAddr a)) = some ci →
      Specs.Whnf.CertsR c.env d true
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)
        (As.take 4 ++ [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]))
    (hcM : ∀ ci, c.env.find? (c.κ (ixAddr b)) = some ci →
      Specs.Whnf.CertsR c.env d true
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams mus) QA)
    (hlast : ∃ ta, Infer c.env .io d (QA.getD 2 (.bvar 0)) ta ∧
        DefEq c.env d ta ((As.take 4 ++
          [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]).getD 0 (.bvar 0))) :
    Red c.env d (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr a)) us) As)
      (Ix.Kernel.Expr.mkAppN (.app a3 q2) (As.drop 5)) := by
  have hwf := hc.env.tableWf
  have hka : c.κ (ixAddr a) = Ix.Kernel.quotIndName := keyOf_of_addressOf hwf haddr
  have hkb : c.κ (ixAddr b) = Ix.Kernel.quotMkName := keyOf_of_addressOf hwf hmk
  have hq : c.inForce .quot := Ctx.inForce_of_block_or_dep hwf hin (.inl (by decide))
  have hfI : c.env.find? Ix.Kernel.quotIndName = some Ix.Kernel.quotIndA :=
    hc.env.quotBasis hq Ix.Kernel.quotIndA (by simp [Ix.Kernel.BasisKind.declsA])
  have hfM : c.env.find? Ix.Kernel.quotMkName = some Ix.Kernel.quotMkA :=
    hc.env.quotBasis hq Ix.Kernel.quotMkA (by simp [Ix.Kernel.BasisKind.declsA])
  rw [hka, hkb] at hcT
  rw [hkb] at hcM hred
  rw [hka]
  obtain ⟨u0, rfl⟩ := quot_list1 hus
  obtain ⟨m0, rfl⟩ := quot_list1 hmus
  obtain ⟨q0, q1, x2, rfl⟩ := quot_list3 hQA
  obtain ⟨a0, a1, a2, y3, a4, rest, rfl⟩ := quot_list5 hAl
  have e3 : a3 = y3 := (by simpa using h3 : y3 = a3).symm
  subst e3
  have e2 : q2 = x2 := (by simpa using h2 : x2 = q2).symm
  subst e2
  have c0 := quot_inst_closed (hAc a0 (by simp))
  have c1 := quot_inst_closed (hAc a1 (by simp))
  have c2 := quot_inst_closed (hAc a2 (by simp))
  have c3 := quot_inst_closed (hAc a3 (by simp))
  have hcert1 : Certs c.env d true
      ((Ix.Kernel.quotIndA (md := .anon)).toConstantVal.type.instantiateLevelParams
        [Ix.Kernel.uN] [u0])
      ([a0, a1, a2, a3] ++
        [Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotMkName [m0]) [q0, q1, q2]]) :=
    Specs.Whnf.CertsR.toCerts (hcT _ hfI)
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _ rfl)
  have hcert2 : Certs c.env d true
      ((Ix.Kernel.quotMkA (md := .anon)).toConstantVal.type.instantiateLevelParams
        [Ix.Kernel.uN] [m0]) [q0, q1, q2] :=
    Specs.Whnf.CertsR.toCerts (hcM _ hfM)
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _ rfl)
  have heA : (Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotIndName [u0])
      [a0, a1, a2, a3, a4]).getAppArgs = [a0, a1, a2, a3, a4] := by
    rw [getAppArgs_mkAppN]; rfl
  have hMA : (Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotMkName [m0]) [q0, q1, q2]).getAppArgs =
      [q0, q1, q2] := by
    rw [getAppArgs_mkAppN]; rfl
  have hiota := Ix.Kernel.Rules.Red.iota (env := c.env) (d := d)
    (e := Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotIndName [u0]) [a0, a1, a2, a3, a4])
    (c := Ix.Kernel.quotIndName) (us := [u0]) (cv := Ix.Kernel.quotIndA.toConstantVal)
    (mI := 4) (rP := 4) (rules := [Ix.Kernel.Semantics.quotIndRule])
    (major := Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotMkName [m0]) [q0, q1, q2])
    (cj := Ix.Kernel.quotMkName) (usj := [m0]) (cvj := Ix.Kernel.quotMkA.toConstantVal)
    (cnP := 2) (cnF := 1) (rl := Ix.Kernel.Semantics.quotIndRule) (residual := .bvar 0)
    (by rw [getAppFn_mkAppN]; rfl)
    (hfI.trans (congrArg some (Ix.Kernel.Semantics.quotIndA_eq (md := .anon))))
    (by rw [heA]; rfl) rfl (by rw [heA]; exact hred) (by rw [getAppFn_mkAppN]; rfl)
    (hfM.trans (congrArg some quotMkA_ctor))
    (by first | rfl | simp [Ix.Kernel.Semantics.quotIndRule])
    (by rw [hMA]; rfl)
    (by first | decide | simp [Ix.Kernel.Semantics.quotIndRule])
    (by rw [heA]; exact hlev)
    (fun h => absurd h (by first | decide |
      simp [Ix.Kernel.RecRule.compareParams, Ix.Kernel.Semantics.quotIndRule]))
    (by rw [heA]; exact hcert1) (by rw [hMA]; exact hcert2)
    (fun h => absurd rfl h) (fun h => absurd rfl h)
  rw [heA, hMA] at hiota
  obtain ⟨-, hchain⟩ := quot_red_tele [q2] [a0, a1, a2, a3]
    (quotInd_tele.instLP [Ix.Kernel.uN] [u0]) hcert1
  rw [quotInd_peel u0 c0 c1 c2 c3] at hchain
  have hbody : (Ix.Kernel.Expr.app a3 (.bvar 0)).instantiate1 q2 = .app a3 q2 := by
    simp [Ix.Kernel.Expr.instantiate1, c3]
  have hlastR : Red c.env d
      (.app (.lam a0 (.app a3 (.bvar 0))
        { pw := Ix.Kernel.Level.substPW [Ix.Kernel.uN] [u0] (.ifAllZero []) }) q2)
      (.app a3 q2) := by
    rw [← hbody]
    obtain ⟨ta, hi, hd⟩ := hlast
    exact .beta hi hd
  have hmain : Red c.env d
      (Ix.Kernel.Expr.mkAppN (.const Ix.Kernel.quotIndName [u0]) [a0, a1, a2, a3, a4])
      (.app a3 q2) :=
    .trans hiota (.trans hchain hlastR)
  exact red_mkAppN rest hmain

/-! ## The step -/

/-- `KernelWhnf::red_quot`: at a spine long enough for the major premise and levels of the
eliminator's count, the major is head-normalized (`whnf`) to `Quot.mk` (by its role) with three
arguments at the eliminator's first level, `quot_certs` certifies the walks, and the result is
the function (`Quot.lift`) or the minor premise (`Quot.ind`) applied to the packed element and
the rest of the spine. -/
theorem red_quot_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_quot" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.red_quot c args h r h' calls := by
  intro rc il addr lvls sp types hargs good hrc d Γ htypes a us As hrole ha hus hAs x hr
  subst hargs
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, (n = 0 ∨ n = 1) ∧ il = .field (n : F) := by
    rcases hrole with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨1, .inr rfl, by rw [Nat.cast_one]⟩
    · exact ⟨0, .inl rfl, by rw [Nat.cast_zero]⟩
  rcases Obs.«KernelWhnf::red_quot».obs ev with
    ⟨v1, m19, x27, y28, m29, cs38, v42, m51, cs59, cs73, v76, x83, y84, m85, cs94, v118, m119,
      cs129, v133, m143, cs151, m178, cs189, x_qh, x_qargs, x_mk_addr, x_mk_lvls, m246, x253,
      y254, m255, x261, y262, m263, cs272, v277, m293, cs301, cs307, v310, x317, m319, cs328,
      cs342, v345, x352, m354, cs363, m389, cs400, v403, v404, m406, cs414, m433, cs441, m464,
      cs475, v482, m516, cs524, v527, m530, cs538, v596, m597, cs607, v628, m637, cs645, v649,
      m651, v664, m673, cs681, m700, cs708, v712, op16, ev61, ev40, ev96, op112, op90, ev75, op34,
      ev153, ev131, ev191, ld227, ev303, ev274, ev330, op324, ev309, op268, ev365, op359, ev344,
      op260, ev416, ev443, ev402, ev540, ev526, ev477, ev609, he629, hm659, ev683, op733, ev710,
      ev647, he735, hc736⟩ | _ | _ | _ | _ | _
  · subst he735 hc736
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he629)
    have hnb : n ≤ 1 := by omega
    -- the heaps
    have e61 := ObsFn.heap_extends ev61
    have e40 := ObsFn.heap_extends ev40
    have e96 := ObsFn.heap_extends ev96
    have e75 := ObsFn.heap_extends ev75
    have e153 := ObsFn.heap_extends ev153
    have e131 := ObsFn.heap_extends ev131
    have e191 := ObsFn.heap_extends ev191
    have e303 := ObsFn.heap_extends ev303
    have e274 := ObsFn.heap_extends ev274
    have e330 := ObsFn.heap_extends ev330
    have e309 := ObsFn.heap_extends ev309
    have e365 := ObsFn.heap_extends ev365
    have e344 := ObsFn.heap_extends ev344
    have e416 := ObsFn.heap_extends ev416
    have e443 := ObsFn.heap_extends ev443
    have e402 := ObsFn.heap_extends ev402
    have e540 := ObsFn.heap_extends ev540
    have e526 := ObsFn.heap_extends ev526
    have e477 := ObsFn.heap_extends ev477
    have e609 := ObsFn.heap_extends ev609
    have e683 := ObsFn.heap_extends ev683
    have e710 := ObsFn.heap_extends ev710
    have e659 : Heap.Extends m673 m651 := by rw [hm659]; exact Heap.Extends.snoc _ _
    have H29 := e61.trans e40
    have H19 := H29.trans (e96.trans e75)
    have H143 := H19.trans e153
    have G178 := e131.trans e191
    have H178 := H143.trans G178
    have F255 := e303.trans (e274.trans (e330.trans e309))
    have F246 := F255.trans (e365.trans e344)
    have F516 := F246.trans (e416.trans (e443.trans (e402.trans (e540.trans e526))))
    have H263 := H178.trans (e303.trans e274)
    have H406 := H178.trans (F246.trans e416)
    have H389 := H406.trans (e443.trans e402)
    have H516 := H389.trans (e540.trans e526)
    have H464 := H516.trans e477
    have H651 := H464.trans (e609.trans (e683.trans e659))
    -- the major's index and the spine's length
    have hv1 := NatAux.add_ok op16
    subst hv1
    have hval4 : ZMod.val ((4 : F) + (n : F)) = 4 + n := by
      rw [show ((4 : F) + (n : F)) = ((4 + n : Nat) : F) by simp]
      exact quot_val_lit _ (by omega)
    obtain ⟨hv42, -⟩ := Lib.Lists.length_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev61)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs)
    subst hv42
    have hAsb : As.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [sp], h⟩) (by simp) (by simp)
      hAs
    obtain ⟨-, -, hx27, hx27', -⟩ := Lib.less_than_fields_field ev40
    -- the level count
    obtain ⟨ls, hls, hlseq⟩ := hus
    have hls29 : RepList klevelListEnum RepKLevel m29 ls lvls := by
      rw [klevelListEnum_eq]; exact KernelLevels.RepKLevelList.mono hls H29
    obtain ⟨hx83, -⟩ := Lib.Lists.length_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev96)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hls29)
    subst hx83
    have hlsb : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], m29⟩) (by simp)
      (by simp) hls29
    have hy84 := NatAux.add_ok op112
    subst hy84
    have hv76 := NatAux.sub_ok op90
    subst hv76
    obtain ⟨hy28, -⟩ := Lib.is_zero_field ev75
    subst hy28
    have hx27one : x27 = .field 1 := by
      rcases hx27' with rfl | rfl
      · have h0 := NatAux.field_inj (NatAux.mul_ok op34)
        rw [zero_mul] at h0
        exact absurd h0 one_ne_zero
      · rfl
    subst hx27one
    have hAlen : 4 + n < As.length := by
      have h0 := hx27.mp rfl
      rwa [hval4, quot_val_lit As.length (by omega)] at h0
    have hlslen : ls.length = 1 + n := by
      have h1 := NatAux.field_inj (NatAux.mul_ok op34)
      have hz : ((ls.length : F) - (1 + (n : F))) = 0 := by
        by_contra hne
        rw [ite_eq_right hne, mul_zero] at h1
        exact one_ne_zero h1
      have h2 : ((ls.length : Nat) : F) = ((1 + n : Nat) : F) := by
        push_cast; exact sub_eq_zero.mp hz
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h2
    have huslen : us.length = 1 + n := (quot_lvEqList_length hlseq).trans hlslen
    -- the major premise, head-normalized
    obtain ⟨⟨a5, ha5, hta5⟩, -⟩ := Lib.Lists.lookup_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev153)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono H19 hAs)
    rw [hval4] at ha5
    obtain ⟨Q, hQ, hredQ⟩ := ih.get (.whnf .whnf) (by lt_calls) ev131 rc v133 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono H143 hrc) d Γ (types_mono H143 htypes) a5
      (Tm.mono e153 hta5)
    obtain ⟨hd0, sp0, H, QA, he1, hH, hQA, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev191 v118 rfl (good.sub fun z hz => by simp [hz]) d Γ 0 Q hQ
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨b, mus, rfl, hb, hmus⟩ := hH.const_of_load ld227
    have hQA0 : c.tml d Γ m178 QA x_qargs := hQA
    -- the role, the argument count and the level count of the major's head
    obtain ⟨rfl, -⟩ := ih.get (.roles .role_quot_mk) (by lt_calls) ev303 rfl
    have hQA263 : c.tml d Γ m263 QA x_qargs := tml_mono (e303.trans e274) hQA0
    obtain ⟨hx317, -⟩ := Lib.Lists.length_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev330)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hQA263)
    subst hx317
    have hQAb : QA.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_qargs], m263⟩) (by simp)
      (by simp) hQA263
    have hv310 := NatAux.sub_ok op324
    subst hv310
    obtain ⟨hy262, -⟩ := Lib.is_zero_field ev309
    subst hy262
    obtain ⟨s, -, rfl, -⟩ := NatAux.binop_fields op268
    have hx253 := NatAux.mul_ok op268
    subst hx253
    obtain ⟨mls, hmls, hmuseq⟩ := hmus
    have hmls255 : RepList klevelListEnum RepKLevel m255 mls x_mk_lvls := by
      rw [klevelListEnum_eq]; exact KernelLevels.RepKLevelList.mono hmls F255
    obtain ⟨hx352, -⟩ := Lib.Lists.length_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev365)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hmls255)
    subst hx352
    have hmlsb : mls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_mk_lvls], m255⟩) (by simp)
      (by simp) hmls255
    have hv345 := NatAux.sub_ok op359
    subst hv345
    obtain ⟨hy254, -⟩ := Lib.is_zero_field ev344
    subst hy254
    obtain ⟨hs0, hq3, hml1⟩ := quot_mul3_one (NatAux.field_inj (NatAux.mul_ok op260))
    have hQA3 : QA.length = 3 := by
      have h2 : ((QA.length : Nat) : F) = ((3 : Nat) : F) := by
        rw [Nat.cast_ofNat]; exact sub_eq_zero.mp hq3
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h2
    have hmlslen : mls.length = 1 := by
      have h2 : ((mls.length : Nat) : F) = ((1 : Nat) : F) := by
        rw [Nat.cast_one]; exact sub_eq_zero.mp hml1
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h2
    have hmuslen : mus.length = 1 := (quot_lvEqList_length hmuseq).trans hmlslen
    obtain ⟨hmkaddr, hmkin⟩ := ih.get (.roles .role_is) (by lt_calls) ev274 rc x_mk_addr b .quotMk
      rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (H178.trans e303) hrc)
      (Bytes.repAddressRef_heapMono₂ addrTy e303 hb) (fun e => hs0 (Value.field.inj e))
    -- the levels compared
    have hmls246 : RepList klevelListEnum RepKLevel m246 mls x_mk_lvls := by
      rw [klevelListEnum_eq]; exact KernelLevels.RepKLevelList.mono hmls F246
    obtain ⟨⟨ml0, hml0, hrml0⟩, -⟩ := Lib.Lists.lookup_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol]; exact ev416)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hmls246)
    rw [ZMod.val_zero] at hml0
    have hls406 : RepList klevelListEnum RepKLevel m406 ls lvls := by
      rw [klevelListEnum_eq]; exact KernelLevels.RepKLevelList.mono hls H406
    obtain ⟨⟨l0, hl0, hrl0⟩, -⟩ := Lib.Lists.lookup_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol]; exact ev443)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hls406)
    rw [ZMod.val_zero] at hl0
    obtain ⟨hleq, -⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev402 v403 v404 rfl
      (good.sub fun z hz => by simp [hz]).2 ml0 l0 (hrml0.mono (e416.trans e443))
      (hrl0.mono e443)
    have hle : KernelLevels.levelEqual ml0 l0 = true := by
      by_contra hne
      rw [ite_eq_right hne] at hleq
      exact NatAux.field_one_ne_zero hleq
    have hlev := quot_lev hlseq hmuseq hmlslen hml0 hl0
      (fun φ => KernelLevels.levelEqual_eq_true_sound hle φ)
    -- the walks
    obtain ⟨-, hpre⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev540)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono H389 hAs)
    rw [hval4, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hpre
    have hra := Lib.Lists.snoc_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev526)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hpre)
      (Tm.mono (e191.trans (e303.trans (e274.trans (e330.trans (e309.trans (e365.trans
        (e344.trans (e416.trans (e443.trans (e402.trans e540)))))))))) hQ)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hra
    have hRA : c.tml d Γ m516 (As.take (4 + n) ++
        [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]) v482 := hra
    have hRAlen : (As.take (4 + n) ++
        [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]).length = 5 + n := by
      simp only [List.length_append, List.length_take, List.length_singleton]; omega
    have hroleQ : ((Value.field (n : F) : SourceValue F) = .field 1 ∧
          c.t.addressOf? .quotLift = some (ixAddr a) ∧ c.inForce .quotLift ∧
          (As.take (4 + n) ++ [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]).length =
            6 ∧ us.length = 2) ∨
        ((Value.field (n : F) : SourceValue F) = .field 0 ∧
          c.t.addressOf? .quotInd = some (ixAddr a) ∧ c.inForce .quotInd ∧
          (As.take (4 + n) ++ [Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA]).length =
            5 ∧ us.length = 1) := by
      rcases hrole with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · have hn1 : n = 1 := by
          rcases hn with rfl | rfl
          · exact absurd (Value.field.inj h1) (by simp)
          · rfl
        exact .inl ⟨h1, h2, h3, by omega, by omega⟩
      · have hn0 : n = 0 := by
          rcases hn with rfl | rfl
          · rfl
          · exact absurd (Value.field.inj h1) (by simp)
        exact .inr ⟨h1, h2, h3, by omega, by omega⟩
    obtain ⟨hcT, hcM, hlast⟩ := ih.get (.whnf .quot_certs) (by lt_calls) ev477 rc
      (.field (n : F)) addr lvls v482 x_mk_addr x_mk_lvls x_qargs types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono H516 hrc) d Γ (types_mono H516 htypes)
      a b us mus _ QA (Bytes.repAddressRef_heapMono₂ addrTy H516 ha)
      ⟨ls, KernelLevels.RepKLevelList.mono hls H516, hlseq⟩ hRA
      (Bytes.repAddressRef_heapMono₂ addrTy F516 hb)
      ⟨mls, KernelLevels.RepKLevelList.mono hmls F516, hmuseq⟩
      (tml_mono F516 hQA0) hroleQ hmkaddr hmkin hQA3
      NatAux.field_one_ne_zero
    -- the reduct
    have hv3 : ZMod.val (3 : F) = 3 := by
      have h0 := quot_val_lit 3 (by omega)
      rwa [Nat.cast_ofNat] at h0
    have hv2 : ZMod.val (2 : F) = 2 := by
      have h0 := quot_val_lit 2 (by omega)
      rwa [Nat.cast_ofNat] at h0
    obtain ⟨⟨a3, ha3, hta3⟩, -⟩ := Lib.Lists.lookup_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev609)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono H464 hAs)
    rw [hv3] at ha3
    obtain ⟨⟨q2, hq2i, hq2⟩, -⟩ := Lib.Lists.lookup_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev683)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (F516.trans (e477.trans e609)) hQA0)
    rw [hv2] at hq2i
    have happ : Tm c.κ d Γ m651 0 (.app a3 q2) (.ptr (.enum kexprEnum) m673.length) :=
      .app (by rw [hm659]; simp) (Tm.mono (e609.trans (e683.trans e659)) hta3)
        (Tm.mono (e683.trans e659) hq2)
    have hv712 := NatAux.add_ok op733
    subst hv712
    have hval5 : ZMod.val ((4 : F) + (n : F) + 1) = 4 + n + 1 := by
      rw [show ((4 : F) + (n : F) + 1) = ((4 + n + 1 : Nat) : F) by simp]
      exact quot_val_lit _ (by omega)
    obtain ⟨-, hdrop, -⟩ := Lib.Lists.drop_spec (4 + n + 1) (t := kexprTy) (R := TmE c.κ d Γ)
      hval5 (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev710)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono H651 hAs)
    rw [hval5, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hdrop
    have hres := ih.get (.whnf .apply_spine) (by lt_calls) ev647 _ v649 rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 (.app a3 q2) (As.drop (4 + n + 1))
      (Tm.mono e710 happ) (tml_mono e710 hdrop)
    refine ⟨_, hres, ?_⟩
    -- the kernel's reduction
    have hAc := quot_tml_lbb hAs
    have hred' : Red c.env d (As.getD (4 + n) (.bvar 0))
        (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr b)) mus) QA) := by
      rw [List.getD_eq_getElem?_getD, ha5]; exact hredQ
    rcases hn with rfl | rfl
    · rcases hrole with ⟨h1, -⟩ | ⟨-, haddr, hin⟩
      · exact absurd (Value.field.inj h1) (by simp)
      · obtain ⟨h1, -⟩ | hl := hlast
        · exact absurd (Value.field.inj h1) (by simp)
        · exact quot_ind_red c hc haddr hin hmkaddr huslen hmuslen hlev (by omega) hAc hQA3
            hred' ha3 hq2i hcT hcM hl
    · rcases hrole with ⟨-, haddr, hin⟩ | ⟨h1, -⟩
      · exact quot_lift_red c hc haddr hin hmkaddr huslen hmuslen hlev (by omega) hAc hQA3
          hred' ha3 hq2i hcT hcM (hlast.imp (fun hl => hl.2) id)
      · exact absurd (Value.field.inj h1) (by simp)
  all_goals exact (tag_zero_ne_one
    ((‹r = .tuple [.field 0, _]› : r = _).symm.trans hr)).elim

/-! ## `quot_certs` -/

theorem quot_lvEqList_getElem? {us ls : List KLevel} (h : LvEqList us ls) :
    ∀ (i : Nat) {l : KLevel}, ls[i]? = some l → ∃ u, us[i]? = some u ∧ LvEq u l := by
  intro i l hl
  induction i generalizing us ls with
  | zero =>
    rcases ls with _ | ⟨l0, ls'⟩
    · simp at hl
    · have he : l0 = l := by simpa using hl
      subst he
      rcases us with _ | ⟨u0, us'⟩
      · exact (h fun _ => 0).elim
      · exact ⟨u0, rfl, fun φ => (h φ).1⟩
  | succ i ih =>
    rcases ls with _ | ⟨l0, ls'⟩
    · simp at hl
    · rcases us with _ | ⟨u0, us'⟩
      · exact (h fun _ => 0).elim
      · exact ih (fun φ => (h φ).2) (by simpa using hl)

theorem quot_subst_singleton_cons (p : Ix.Kernel.LevelParam) (m0 : KLevel)
    (mrest : List KLevel) :
    ∀ (l : KLevel), Ix.Kernel.Level.subst [p] (m0 :: mrest) l = Ix.Kernel.Level.subst [p] [m0] l
  | .zero => rfl
  | .succ l => congrArg Ix.Kernel.Level.succ (quot_subst_singleton_cons p m0 mrest l)
  | .max a b => congrArg₂ Ix.Kernel.Level.max (quot_subst_singleton_cons p m0 mrest a)
      (quot_subst_singleton_cons p m0 mrest b)
  | .imax a b => congrArg₂ Ix.Kernel.Level.imax (quot_subst_singleton_cons p m0 mrest a)
      (quot_subst_singleton_cons p m0 mrest b)
  | .param _ => rfl

theorem quot_instLP_singleton_cons (p : Ix.Kernel.LevelParam) (m0 : KLevel)
    (mrest : List KLevel) :
    ∀ (e : KExpr),
      e.instantiateLevelParams [p] (m0 :: mrest) = e.instantiateLevelParams [p] [m0]
  | .bvar _ => rfl
  | .fvar idx ty => congrArg (Ix.Kernel.Expr.fvar idx) (quot_instLP_singleton_cons p m0 mrest ty)
  | .sort u => congrArg Ix.Kernel.Expr.sort (quot_subst_singleton_cons p m0 mrest u)
  | .const n ls => congrArg (Ix.Kernel.Expr.const n) (List.map_congr_left fun l _ =>
      quot_subst_singleton_cons p m0 mrest l)
  | .app f a => congrArg₂ Ix.Kernel.Expr.app (quot_instLP_singleton_cons p m0 mrest f)
      (quot_instLP_singleton_cons p m0 mrest a)
  | .lam ty b m => by
      simp only [Ix.Kernel.Expr.instantiateLevelParams,
        quot_instLP_singleton_cons p m0 mrest ty, quot_instLP_singleton_cons p m0 mrest b]
      rfl
  | .forallE ty b m => by
      simp only [Ix.Kernel.Expr.instantiateLevelParams,
        quot_instLP_singleton_cons p m0 mrest ty, quot_instLP_singleton_cons p m0 mrest b]
      rfl
  | .letE ty v b m => by
      simp only [Ix.Kernel.Expr.instantiateLevelParams,
        quot_instLP_singleton_cons p m0 mrest ty, quot_instLP_singleton_cons p m0 mrest v,
        quot_instLP_singleton_cons p m0 mrest b]
  | .lit _ => rfl
  | .proj s i e => congrArg (Ix.Kernel.Expr.proj s i) (quot_instLP_singleton_cons p m0 mrest e)

theorem quot_posOf_inst_cons {p : Ix.Kernel.LevelParam} {m0 : KLevel} {mrest : List KLevel}
    {e : KExpr} (h : e.allLevelParamsDefined [p] = true) :
    (posOf [p] e).instantiateLevelParams (List.range (m0 :: mrest).length) (m0 :: mrest) =
      e.instantiateLevelParams [p] (m0 :: mrest) := by
  unfold posOf
  rw [inst_inst (by simp [posLevels]) e h, quot_instLP_singleton_cons]
  have hmap : (posLevels [p]).map (Ix.Kernel.Level.subst (List.range (m0 :: mrest).length)
      (m0 :: mrest)) = [m0] := by
    simp only [posLevels, List.length_singleton, List.range_one, List.map_cons, List.map_nil,
      List.length_cons]
    rw [List.range_eq_range', List.range'_succ]
    simp [Ix.Kernel.Level.subst, Ix.Kernel.Level.subst.go]
  rw [hmap]

theorem quotLift_forallsNever (u0 u1 : KLevel) (h : u1.isNeverZero = true) :
    Specs.Whnf.forallsNever 6
      ((Ix.Kernel.quotLiftA (md := .anon)).toConstantVal.type.instantiateLevelParams
        [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]) := by
  have hpw : (Ix.Kernel.Level.substPW [Ix.Kernel.uN, Ix.Kernel.vN] [u0, u1]
      (.ifAllZero [Ix.Kernel.vN])).isNever = true := by
    rw [quotLift_substPW, ← Ix.Kernel.Level.isNeverZero_eq_isNever]
    exact h
  exact ⟨hpw, hpw, hpw, hpw, hpw, hpw, trivial⟩

theorem quotMk_forallsNever (m0 : KLevel) (mrest : List KLevel) (h : m0.isNeverZero = true) :
    Specs.Whnf.forallsNever 3
      ((Ix.Kernel.quotMkA (md := .anon)).toConstantVal.type.instantiateLevelParams
        [Ix.Kernel.uN] (m0 :: mrest)) := by
  have hpw : (Ix.Kernel.Level.substPW [Ix.Kernel.uN] (m0 :: mrest)
      (.ifAllZero [Ix.Kernel.uN])).isNever = true := by
    have hs : Ix.Kernel.Level.substPW [Ix.Kernel.uN] (m0 :: mrest) (.ifAllZero [Ix.Kernel.uN]) =
        Ix.Kernel.Level.zeronessOf m0 :=
      (Ix.Kernel.Level.zeronessOf_subst [Ix.Kernel.uN] (m0 :: mrest)
        (.param Ix.Kernel.uN)).symm
    rw [hs, ← Ix.Kernel.Level.isNeverZero_eq_isNever]
    exact h
  exact ⟨hpw, hpw, hpw, trivial⟩

private theorem quot_certs_seg1 {c : Ctx} {calls cs60 : List (Call F)} (ih : IH c calls)
    (hle : cs60.length ≤ calls.length)
    {rc il addr lvls ra mk mklvls ma types v57 : SourceValue F} {h m58 : Heap F}
    {us : List KLevel}
    (sg : Obs.«KernelWhnf::quot_certs».Seg1 rc il addr lvls ra mk mklvls ma types h v57 m58 cs60)
    (hus : LvListRep h us lvls) :
    Heap.Extends h m58 ∧
      (v57 = .field 1 → il = .field 1 ∧ ∃ v, us[1]? = some v ∧ v.isNeverZero = true) := by
  rcases sg with ⟨cs18, v21, m23, cs31, hv14, ev33, ev20, hc49⟩ | ⟨hne50, he54, he55, hc56⟩
  · subst hc49
    have e33 := ObsFn.heap_extends ev33
    have e20 := ObsFn.heap_extends ev20
    refine ⟨e33.trans e20, fun hv57 => ?_⟩
    obtain ⟨ls, hls, hlseq⟩ := hus
    have hls' : RepList klevelListEnum RepKLevel h ls lvls := by
      rw [klevelListEnum_eq]; exact hls
    obtain ⟨⟨l1, hl1, hrl1⟩, -⟩ := Lib.Lists.lookup_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol]; exact ev33)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hls')
    have hv1 : ZMod.val (1 : F) = 1 := by
      have h0 := quot_val_lit 1 (by omega)
      rwa [Nat.cast_one] at h0
    rw [hv1] at hl1
    obtain ⟨hr1, -⟩ := ih.get (.levelOps .level_is_not_zero)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev20 v21 rfl l1
      (hrl1.mono e33)
    rw [hv57] at hr1
    have hnz := WhnfAux.isNeverZero_of_answer hr1
    obtain ⟨u1, hu1, heq1⟩ := quot_lvEqList_getElem? hlseq 1 hl1
    exact ⟨hv14, u1, hu1, (WhnfAux.isNeverZero_congr heq1).trans hnz⟩
  · subst he55
    exact ⟨Heap.Extends.refl _, fun hv => absurd (he54.symm.trans hv) (by simp)⟩

private theorem quot_certs_seg2 (c : Ctx) (hc : CoreFacts c) {calls cs320 : List (Call F)}
    (ih : IH c calls) (good : Good c calls) (hsub : ∀ z ∈ cs320, z ∈ calls)
    (hle : cs320.length ≤ calls.length)
    {v57 rc il addr lvls ra mk mklvls ma types : SourceValue F} {m58 m318 : Heap F}
    {d : Nat} {Γ : Nat → KExpr} {a : Bytes.Address} {us : List KLevel} {RA MA : List KExpr}
    (sg : Obs.«KernelWhnf::quot_certs».Seg2 v57 rc il addr lvls ra mk mklvls ma types m58
      (.field 1) m318 cs320)
    (hsg1 : v57 = .field 1 → il = .field 1 ∧ ∃ v, us[1]? = some v ∧ v.isNeverZero = true)
    (hrc : c.rc m58 rc) (htypes : c.types Γ m58 d types) (ha : RepAddr m58 a addr)
    (hus : LvListRep m58 us lvls) (hRA : c.tml d Γ m58 RA ra) (hMA : c.tml d Γ m58 MA ma)
    (hrole : (il = .field 1 ∧ c.t.addressOf? .quotLift = some (ixAddr a) ∧ c.inForce .quotLift ∧
        RA.length = 6 ∧ us.length = 2) ∨
      (il = .field 0 ∧ c.t.addressOf? .quotInd = some (ixAddr a) ∧ c.inForce .quotInd ∧
        RA.length = 5 ∧ us.length = 1))
    (hMA3 : MA.length = 3) :
    Heap.Extends m58 m318 ∧
      (∀ ci, c.env.find? (c.κ (ixAddr a)) = some ci →
        Specs.Whnf.CertsR c.env d true
          (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) RA) ∧
      ((il = .field 1 ∧ ∃ v, us[1]? = some v ∧ v.isNeverZero = true) ∨
        ∃ ta, Infer c.env .io d (MA.getD 2 (.bvar 0)) ta ∧
          DefEq c.env d ta (RA.getD 0 (.bvar 0))) := by
  have hwf := hc.env.tableWf
  rcases sg with ⟨hv79, _, he81, hc82⟩ |
    ⟨m88, cs99, v103, m115, cs123, v126, m129, cs137, v140, m142, p147, cs153, m179, cs205,
      v209, v210, m220, cs228, v232, m242, cs250, m276, cs284, hne83, ev155, ld149, ev139, ev125,
      hm187, ev101, ev252, ev230, ev286, ev207, hc309⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he314, _, _⟩
  · subst he81
    obtain ⟨hil1, v, hv, hvnz⟩ := hsg1 hv79
    rcases hrole with ⟨-, haddr, hin, hRA6, hus2⟩ | ⟨hil0, -⟩
    · have hka : c.κ (ixAddr a) = Ix.Kernel.quotLiftName := keyOf_of_addressOf hwf haddr
      have hq : c.inForce .quot := Ctx.inForce_of_block_or_dep hwf hin (.inl (by decide))
      have hfL : c.env.find? Ix.Kernel.quotLiftName = some Ix.Kernel.quotLiftA :=
        hc.env.quotBasis hq Ix.Kernel.quotLiftA (by simp [Ix.Kernel.BasisKind.declsA])
      obtain ⟨u0, u1, rfl⟩ := quot_list2 hus2
      have hv1 : u1 = v := by simpa using hv
      subst hv1
      refine ⟨Heap.Extends.refl _, ?_, .inl ⟨hil1, u1, rfl, hvnz⟩⟩
      intro ci hci
      rw [hka, hfL] at hci
      obtain rfl := Option.some.inj hci
      exact certsR_of_forallsNever RA _ (by rw [hRA6]; exact quotLift_forallsNever u0 u1 hvnz)
    · exact absurd (hil1.symm.trans hil0) NatAux.field_one_ne_zero
  · subst hc309
    have e155 := ObsFn.heap_extends ev155
    have e139 := ObsFn.heap_extends ev139
    have e125 := ObsFn.heap_extends ev125
    have e187 : Heap.Extends m115 m179 := by rw [hm187]; exact Heap.Extends.snoc _ _
    have e101 := ObsFn.heap_extends ev101
    have e252 := ObsFn.heap_extends ev252
    have e230 := ObsFn.heap_extends ev230
    have e286 := ObsFn.heap_extends ev286
    have e207 := ObsFn.heap_extends ev207
    have E129 := e155.trans e139
    have E179 := E129.trans (e125.trans e187)
    have E88 := E179.trans e101
    have E242 := E88.trans e252
    have E220 := E242.trans e230
    have E276 := E220.trans e286
    obtain ⟨ci0, hfind0, v0, hv0, hrep0⟩ := ih.get (.callees .get_ci)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev155 addr a rfl
      (good.sub fun z hz => hsub z (by simp [hz])) ha
    rw [ld149] at hv0
    injection hv0 with hv0
    subst hv0
    obtain ⟨hcty, -⟩ := ih.get (.infer .const_type_of)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev139 v140 ci0 rfl
      (good.sub fun z hz => hsub z (by simp [hz])) hrep0
    have hinst := ih.get (.subst .expr_inst_levels)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev125 v126 lvls rfl
      (good.sub fun z hz => hsub z (by simp [hz])) Γ 0 _ us (hcty 0 Γ) (LvListRep.mono E129 hus)
    obtain ⟨-, halpd0, -⟩ := hc.env.store.wf _ (List.mem_of_find?_eq_some hfind0)
    have halpd0' : ci0.toConstantVal.type.allLevelParamsDefined ci0.toConstantVal.levelParams =
        true := halpd0
    have huslen0 : us.length = ci0.toConstantVal.levelParams.length := by
      rcases hrole with ⟨-, haddr, hin, -, hus2⟩ | ⟨-, haddr, hin, -, hus1⟩
      · have hka : c.κ (ixAddr a) = Ix.Kernel.quotLiftName := keyOf_of_addressOf hwf haddr
        have hq : c.inForce .quot := Ctx.inForce_of_block_or_dep hwf hin (.inl (by decide))
        have hfL : c.env.find? Ix.Kernel.quotLiftName = some Ix.Kernel.quotLiftA :=
          hc.env.quotBasis hq Ix.Kernel.quotLiftA (by simp [Ix.Kernel.BasisKind.declsA])
        rw [hka, hfL] at hfind0
        obtain rfl := Option.some.inj hfind0
        exact hus2
      · have hka : c.κ (ixAddr a) = Ix.Kernel.quotIndName := keyOf_of_addressOf hwf haddr
        have hq : c.inForce .quot := Ctx.inForce_of_block_or_dep hwf hin (.inl (by decide))
        have hfI : c.env.find? Ix.Kernel.quotIndName = some Ix.Kernel.quotIndA :=
          hc.env.quotBasis hq Ix.Kernel.quotIndA (by simp [Ix.Kernel.BasisKind.declsA])
        rw [hka, hfI] at hfind0
        obtain rfl := Option.some.inj hfind0
        exact hus1
    rw [huslen0, posOf_inst huslen0 halpd0'] at hinst
    have hnil179 : c.tml d Γ m179 [] (.ptr (.enum kexprListEnum) m115.length) := by
      subst hm187; exact TmL.store_nil m115
    have hcr0 := ih.get (.whnf .certs_all)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev101 rc v103 ra _
      types rfl (good.sub fun z hz => hsub z (by simp [hz])) (RCRep.mono E179 hrc) d Γ
      (types_mono E179 htypes) _ [] RA ((hinst.of_depth_zero d).mono e187) hnil179
      (tml_mono E179 hRA) NatAux.field_one_ne_zero
    rw [Ix.Kernel.Expr.instantiateList_nil] at hcr0
    have hv2 : ZMod.val (2 : F) = 2 := by
      have h0 := quot_val_lit 2 (by omega)
      rwa [Nat.cast_ofNat] at h0
    obtain ⟨⟨q2, hq2, htq2⟩, -⟩ := Lib.Lists.lookup_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev252)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono E88 hMA)
    rw [hv2] at hq2
    obtain ⟨ta, hta, hinf⟩ := ih.get (.infer .k_infer_only)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev230 rc v232 types rfl
      (good.sub fun z hz => hsub z (by simp [hz])) (RCRep.mono E242 hrc) d Γ
      (types_mono E242 htypes) q2 (Tm.mono e252 htq2)
    obtain ⟨⟨r0, hr0_lk, htr0⟩, -⟩ := Lib.Lists.lookup_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev286)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono E220 hRA)
    rw [ZMod.val_zero] at hr0_lk
    have hde := ih.get (.defEq .k_is_def_eq)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev207 rc v209 v210 types
      rfl (good.sub fun z hz => hsub z (by simp [hz])) (RCRep.mono E276 hrc) d Γ
      (types_mono E276 htypes) ta r0 (Tm.mono e286 hta) (Tm.mono e286 htr0) NatAux.field_one_ne_zero
    refine ⟨E276.trans e207, ?_, .inr ⟨ta, ?_, ?_⟩⟩
    · intro ci hci
      rw [hfind0] at hci
      obtain rfl := Option.some.inj hci
      exact CertsR.lic_true hcr0
    · rwa [List.getD_eq_getElem?_getD, hq2]
    · rwa [List.getD_eq_getElem?_getD, hr0_lk]
  · exact absurd he314 NatAux.field_one_ne_zero

/-- **`KernelWhnf::quot_certs`**: the eliminator's walk (gated by `Quot.lift`'s never-zero motive
level, or certified together with the last `β`'s conversion), then `Quot.mk`'s walk (gated by its
never-zero level, or certified). -/
theorem quot_certs_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::quot_certs" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.quot_certs c args h r h' calls := by
  intro rc il addr lvls ra mk mklvls ma types hargs good hrc d Γ htypes a b us mus RA MA
    ha hus hRA hb hmus hMA hrole hmk hmkin hMA3 hr
  subst hargs
  have hwf := hc.env.tableWf
  have hkb : c.κ (ixAddr b) = Ix.Kernel.quotMkName := keyOf_of_addressOf hwf hmk
  have hqM : c.inForce .quot := Ctx.inForce_of_block_or_dep hwf hmkin (.inl (by decide))
  have hfM : c.env.find? Ix.Kernel.quotMkName = some Ix.Kernel.quotMkA :=
    hc.env.quotBasis hqM Ix.Kernel.quotMkA (by simp [Ix.Kernel.BasisKind.declsA])
  rcases Obs.«KernelWhnf::quot_certs».obs ev with
    ⟨v57, m58, cs60, m318, cs320, m341, cs352, v355, m357, cs365, sg65, sg325, ev367, ev354,
      he387, he388, hc389⟩ |
    ⟨v57, m58, cs60, m318, cs320, v340, m341, cs352, v355, m357, cs365, cs397, v401, m413, cs421,
      v424, m427, cs435, v438, m440, p445, cs451, m477, sg65, sg325, ev367, ev354, hne390, ev453,
      ld447, ev437, ev423, hm485, ev399, hc496⟩ |
    ⟨_, _, _, _, _, _, _, _, _, he501, _, _⟩
  · subst hc389
    obtain ⟨e1, hsg1⟩ := quot_certs_seg1 ih (by simp only [List.length_append]; omega) sg65 hus
    obtain ⟨e2, hcT, hlast⟩ := quot_certs_seg2 c hc ih good (fun z hz => by simp [hz])
      (by simp only [List.length_append]; omega) sg325 hsg1 (RCRep.mono e1 hrc)
      (types_mono e1 htypes) (Bytes.repAddressRef_heapMono₂ addrTy e1 ha) (LvListRep.mono e1 hus)
      (tml_mono e1 hRA) (tml_mono e1 hMA) hrole hMA3
    have E318 := e1.trans e2
    obtain ⟨mls, hmls, hmuseq⟩ := hmus
    have hmls318 : RepList klevelListEnum RepKLevel m318 mls mklvls := by
      rw [klevelListEnum_eq]; exact KernelLevels.RepKLevelList.mono hmls E318
    obtain ⟨⟨ml0, hml0, hrml0⟩, -⟩ := Lib.Lists.lookup_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol]; exact ev367)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hmls318)
    rw [ZMod.val_zero] at hml0
    obtain ⟨hrM, -⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev354 v355 rfl ml0
      (hrml0.mono (ObsFn.heap_extends ev367))
    have hnz0 := WhnfAux.isNeverZero_of_answer hrM
    obtain ⟨m0, hm0, heqm0⟩ := quot_lvEqList_getElem? hmuseq 0 hml0
    have hm0nz : m0.isNeverZero = true := (WhnfAux.isNeverZero_congr heqm0).trans hnz0
    rcases mus with _ | ⟨m0', mrest⟩
    · simp at hm0
    · have hm0eq : m0' = m0 := by simpa using hm0
      subst hm0eq
      refine ⟨hcT, ?_, hlast⟩
      intro ci hci
      rw [hkb, hfM] at hci
      obtain rfl := Option.some.inj hci
      exact certsR_of_forallsNever MA _ (by rw [hMA3]; exact quotMk_forallsNever m0' mrest hm0nz)
  · subst hc496
    obtain ⟨e1, hsg1⟩ := quot_certs_seg1 ih (by simp only [List.length_append]; omega) sg65 hus
    obtain ⟨e2, hcT, hlast⟩ := quot_certs_seg2 c hc ih good (fun z hz => by simp [hz])
      (by simp only [List.length_append]; omega) sg325 hsg1 (RCRep.mono e1 hrc)
      (types_mono e1 htypes) (Bytes.repAddressRef_heapMono₂ addrTy e1 ha) (LvListRep.mono e1 hus)
      (tml_mono e1 hRA) (tml_mono e1 hMA) hrole hMA3
    have E318 := e1.trans e2
    have e367 := ObsFn.heap_extends ev367
    have e354 := ObsFn.heap_extends ev354
    have e453 := ObsFn.heap_extends ev453
    have e437 := ObsFn.heap_extends ev437
    have e423 := ObsFn.heap_extends ev423
    have e485 : Heap.Extends m413 m477 := by rw [hm485]; exact Heap.Extends.snoc _ _
    have E341 := E318.trans (e367.trans e354)
    have E427 := E341.trans (e453.trans e437)
    have E477 := E427.trans (e423.trans e485)
    obtain ⟨mls, hmls, hmuseq⟩ := hmus
    have hmls318 : RepList klevelListEnum RepKLevel m318 mls mklvls := by
      rw [klevelListEnum_eq]; exact KernelLevels.RepKLevelList.mono hmls E318
    obtain ⟨⟨ml0, hml0, -⟩, -⟩ := Lib.Lists.lookup_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol]; exact ev367)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hmls318)
    rw [ZMod.val_zero] at hml0
    obtain ⟨m0, hm0, -⟩ := quot_lvEqList_getElem? hmuseq 0 hml0
    rcases mus with _ | ⟨m0', mrest⟩
    · simp at hm0
    · have hm0eq : m0' = m0 := by simpa using hm0
      subst hm0eq
      obtain ⟨ciM, hfindM, vM, hvM, hrepM⟩ := ih.get (.callees .get_ci) (by lt_calls) ev453 mk b rfl
        (good.sub fun z hz => by simp [hz]) (Bytes.repAddressRef_heapMono₂ addrTy E341 hb)
      rw [ld447] at hvM
      injection hvM with hvM
      subst hvM
      have hciM : ciM = Ix.Kernel.quotMkA := by
        rw [hkb, hfM] at hfindM
        exact (Option.some.inj hfindM).symm
      subst hciM
      obtain ⟨hctyM, -⟩ := ih.get (.infer .const_type_of) (by lt_calls) ev437 v438
        Ix.Kernel.quotMkA rfl (good.sub fun z hz => by simp [hz]) hrepM
      have hinstM := ih.get (.subst .expr_inst_levels) (by lt_calls) ev423 v424 mklvls rfl
        (good.sub fun z hz => by simp [hz]) Γ 0 _ (m0' :: mrest) (hctyM 0 Γ)
        ⟨mls, KernelLevels.RepKLevelList.mono hmls E427, hmuseq⟩
      obtain ⟨-, halpdM, -⟩ := hc.env.store.wf _ (List.mem_of_find?_eq_some hfM)
      have halpdM' :
          (Ix.Kernel.quotMkA (md := .anon)).toConstantVal.type.allLevelParamsDefined
            [Ix.Kernel.uN] = true := halpdM
      change c.tmk 0 Γ 0 m413
        ((posOf [Ix.Kernel.uN]
          (Ix.Kernel.quotMkA (md := .anon)).toConstantVal.type).instantiateLevelParams
          (List.range (m0' :: mrest).length) (m0' :: mrest)) v401 at hinstM
      rw [quot_posOf_inst_cons halpdM'] at hinstM
      have hnil477 : c.tml d Γ m477 [] (.ptr (.enum kexprListEnum) m413.length) := by
        subst hm485; exact TmL.store_nil m413
      have hcrM := ih.get (.whnf .certs_all) (by lt_calls) ev399 rc v401 ma _ types rfl
        (good.sub fun z hz => by simp [hz]) (RCRep.mono E477 hrc) d Γ (types_mono E477 htypes) _ []
        MA ((hinstM.of_depth_zero d).mono e485) hnil477 (tml_mono E477 hMA) hr
      rw [Ix.Kernel.Expr.instantiateList_nil] at hcrM
      refine ⟨hcT, ?_, hlast⟩
      intro ci hci
      rw [hkb, hfM] at hci
      obtain rfl := Option.some.inj hci
      exact CertsR.lic_true hcrM
  · exact absurd he501 hr

end IxVM.Refinement.Core
