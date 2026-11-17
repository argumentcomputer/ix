import IxVMRefinement.Decl.EtaOpen
import IxVMRefinement.StatementRel.BoolInhabit

/-! # A structure with a parameter, installed by IxC's checker

`Box : Type → Type`, `Box.mk : (α : Type) → α → Box α` and its recursor `Box.rec.{u}`, at three
role keys used as placeholders (`Iff`'s, no reserved basis name; the kernel evaluates the check
at role keys, as for the prelude's blocks), checked by IxC's own executable native check (fuel
16, evaluated by the Lean kernel) at the empty environment. The environment it installs (`boxEnv`: the projection table,
`Box.rec`, `Box.mk`, `Box`) has the kernel's model in every set theory (`boxEnv_ok`), stores
`Box` with the η capability, and `Box.mk` with one parameter, one field and never-zero binders
(`facts`). There `EtaStable` and the typing clause of `EtaUseFacts`, as stated, fail
(`not_etaStable`): the invariant `PrefixInv` cannot hold at an environment IxC accepts.
-/

universe u

namespace IxVM.Refinement.Decl.EtaOpenInstalled

open IxVM.Refinement.Core IxVM.Refinement.Decl
open Ix.Kernel (Env Expr Level ConstantVal ConstantInfo IndCaps BinderMeta Key RecRule
  NativeParts CheckM fueledOps checkNative nativeParts? basisPinHit)
open IxVM.Refinement.BoolInhabit (okOr ok_okOr)

/-- A binder never a proposition. -/
def nb : BinderMeta := { pw := .never }

/-- A binder whose codomain lives in `Sort u`. -/
def mu : BinderMeta := { pw := Level.zeronessOf (.param 0) }

def tk : KKey := .role .iff
def mk : KKey := .role .iffIntro
def rk : KKey := .role .iffRec

/-- `Box : Type → Type`. -/
def boxT : ConstantVal .anon :=
  ⟨tk, [], .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) nb⟩

/-- `Box.mk : (α : Type) → α → Box α`. -/
def boxMk : ConstantVal .anon :=
  ⟨mk, [], .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.app (.const tk []) (.bvar 1)) nb) nb⟩

def motiveTy : Expr .anon := .forallE (.app (.const tk []) (.bvar 0)) (.sort (.param 0)) nb

def minorTy : Expr .anon :=
  .forallE (.bvar 1) (.app (.bvar 1) (.app (.app (.const mk []) (.bvar 2)) (.bvar 0))) mu

/-- `Box.rec.{u} : (α : Type) → (motive : Box α → Sort u) → ((val : α) → motive (Box.mk α val))
→ (t : Box α) → motive t`. -/
def recTy : Expr .anon :=
  .forallE (.sort (.succ .zero)) (.forallE motiveTy (.forallE minorTy
    (.forallE (.app (.const tk []) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) mu) mu) mu) mu

def rhs : Expr .anon :=
  .lam (.sort (.succ .zero)) (.lam motiveTy (.lam minorTy (.lam (.bvar 2) (.app (.bvar 1) (.bvar 0)) nb) nb) nb) nb

def boxRec : ConstantVal .anon := ⟨rk, [0], recTy⟩

/-- The declared block: former, constructor, recursor. -/
def boxBlock : List (ConstantInfo .anon) :=
  [.indInfo boxT {}, .ctorInfo boxMk 1 1,
   .recInfo boxRec 3 3 [{ ctor := mk, nfields := 1, ctorParams := 0, fire := .inert, rhs := rhs }]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem boxBlock_notPin : (basisPinHit boxBlock).isNone = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem boxParts_isSome : (nativeParts? 1 boxBlock).isSome = true := by decide +kernel

def boxParts : NativeParts .anon := (nativeParts? 1 boxBlock).get boxParts_isSome

theorem boxParts_eq : nativeParts? 1 boxBlock = some boxParts :=
  (Option.some_get boxParts_isSome).symm

/-- **The environment IxC's native check installs** at the empty environment. -/
def boxEnv : Env .anon :=
  okOr (checkNative (m := CheckM .anon) (fueledOps .verified 16) Env.empty boxParts) Env.empty

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem boxCheck_ok :
    (checkNative (m := CheckM .anon) (fueledOps .verified 16) Env.empty boxParts).toBool = true := by
  decide +kernel

theorem boxCheck :
    checkNative (m := CheckM .anon) (fueledOps .verified 16) Env.empty boxParts = .ok boxEnv :=
  ok_okOr boxCheck_ok

theorem boxRun :
    Ix.Kernel.Semantics.DeclRun .verified 16
      (Ix.Kernel.Semantics.DeclIndRunDispatch .verified 16 Env.empty) Env.empty
      (.indDecl boxBlock 1) boxEnv := by
  have hpin : basisPinHit boxBlock = none := Option.isNone_iff_eq_none.mp boxBlock_notPin
  simp only [Ix.Kernel.Semantics.DeclRun, hpin, Ix.Kernel.Semantics.DeclIndRunDispatch,
    boxParts_eq]
  exact Ix.Kernel.Semantics.declNativeRun_of boxCheck

/-- **The installed environment carries the kernel's fold invariant**, in every set theory. -/
theorem boxEnv_ok (W : Type u) [Ix.Kernel.SetTheory W] :
    Ix.Kernel.Model.EnvModelOk W .verified boxEnv :=
  Ix.Kernel.Model.declStep_preserves (F := 16) (d := .indDecl boxBlock 1) rfl
    (Ix.Kernel.Model.EnvModelM.empty W .verified) Ix.Kernel.EtaFamiliesClosed.empty boxRun

/-- What the checks below read, in one evaluation. -/
def boxFacts : Bool :=
  (match boxEnv.find? tk with
   | some (.indInfo _ caps) => caps.eta && caps.etaCtor == some mk
   | _ => false) &&
  (match boxEnv.find? mk with
   | some (.ctorInfo cvc nP nF) =>
     nP == 1 && nF == 1 && cvc.type.looseBVarsBounded 0 &&
       (match cvc.type.stripPis 2 with
        | some (cbs, _) => cbs.all fun b => (Level.substPW cvc.levelParams [] b.2.pw).isNever
        | none => false) && cvc.levelParams.isEmpty
   | _ => false) &&
  boxEnv.consts.all fun c => match c with
    | .defnInfo _ v _ => v.looseBVarsBounded 0
    | .recInfo _ _ _ rules => rules.all (·.rhs.looseBVarsBounded 0)
    | _ => true

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem boxFacts_ok : boxFacts = true := by decide +kernel

/-- **What the refutation reads of the installed environment**: `Box` is stored with the η
capability at the constructor `Box.mk`; `Box.mk` is stored with one parameter and one field, a
closed type whose two binders are never zero, and no level parameter; no stored definition value
or rule right-hand side has a loose bound variable. -/
theorem facts :
    (∃ cvT caps, boxEnv.find? tk = some (.indInfo cvT caps) ∧ caps.eta = true ∧
      caps.etaCtor = some mk) ∧
    (∃ cvc cbs res, boxEnv.find? mk = some (.ctorInfo cvc 1 1) ∧
      cvc.type.looseBVarsBounded 0 = true ∧ cvc.type.stripPis (1 + 1) = some (cbs, res) ∧
      (∀ b ∈ cbs, (Level.substPW cvc.levelParams [] b.2.pw).isNever = true) ∧
      cvc.levelParams = []) ∧
    BClosedStore boxEnv := by
  have h := boxFacts_ok
  unfold boxFacts at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · revert h1
    generalize boxEnv.find? tk = o
    cases o with
    | none => intro h1; exact nomatch h1
    | some ci =>
      cases ci with
      | indInfo cvT caps =>
        intro h1
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        exact ⟨cvT, caps, rfl, h1.1, h1.2⟩
      | _ => intro h1; exact nomatch h1
  · revert h2
    generalize boxEnv.find? mk = o
    cases o with
    | none => intro h2; exact nomatch h2
    | some ci =>
      cases ci with
      | ctorInfo cvc nP nF =>
        intro h2
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        obtain ⟨⟨⟨⟨hnP, hnF⟩, hty⟩, hst⟩, hlp⟩ := h2
        subst hnP hnF
        revert hst
        cases hs : cvc.type.stripPis 2 with
        | none => intro hst; exact nomatch hst
        | some pr =>
          obtain ⟨cbs, res⟩ := pr
          intro hst
          simp only [List.all_eq_true] at hst
          exact ⟨cvc, cbs, res, rfl, hty, hs, hst, List.isEmpty_iff.mp hlp⟩
      | _ => intro h2; exact nomatch h2
  · have hall := List.all_eq_true.mp h3
    refine ⟨fun hf => ?_, fun hf rl hrl => ?_⟩
    · exact hall _ (List.mem_of_find?_eq_some hf)
    · exact List.all_eq_true.mp (hall _ (List.mem_of_find?_eq_some hf)) rl hrl

/-- **`EtaStable` and the typing clause of `EtaUseFacts` fail at the environment IxC's checker
installs for `Box`**, which has a model in every set theory (`boxEnv_ok`). -/
theorem not_etaStable :
    ¬ EtaStable boxEnv ∧ ∃ cvT caps, boxEnv.find? tk = some (.indInfo cvT caps) ∧
      caps.eta = true ∧ ¬ EtaUseFacts boxEnv tk mk cvT caps 1 1 := by
  obtain ⟨⟨cvT, caps, hT, heta, hctor⟩, ⟨cvc, cbs, res, hkc, hty, hst, hnev, hlp⟩, hS⟩ := facts
  have hus : ([] : List KLevel).length = cvc.levelParams.length := by simp [hlp]
  have h := not_etaStable_of_param hS hT heta hctor hkc hty hst hus hnev (Nat.le_refl 1)
    (Nat.le_refl 2)
  exact ⟨h.1, cvT, caps, hT, heta, h.2⟩

/-- **The prefix invariant does not hold at the environment IxC installs for `Box`**, at any
records, table and limit. -/
theorem not_prefixInv (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat) :
    ¬ PrefixInv.{u} E t lim boxEnv :=
  fun h => not_etaStable.1 h.etaStable

end IxVM.Refinement.Decl.EtaOpenInstalled
