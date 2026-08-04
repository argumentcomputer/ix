import Ix.Tc.Verify.Inductive.IngressExecution
import Ix.Tc.Verify.Check.PreTranslationCompatibility

/-!
# Shared executable inductive-fixture support

Concrete inductive fixtures need two small pieces of infrastructure which do
not depend on the fragment being exercised: compiler-shaped storage of a
mutual block and its projections, and a proof-producing translation of the
core binder syntax returned by anonymous ingress.  Keeping these here avoids
making indexed-recursive coverage depend on the Boolean enumeration fixture.
-/

namespace Ix.Tc.InductiveConcreteFixture

open Lean4Lean (VEnv VExpr)

/-- Store a constant at its production content address. -/
def storeConstant (env : Ixon.Env) (constant : Ixon.Constant) :
    Ixon.Env × Address :=
  let address := Address.blake3 (Ixon.serConstant constant)
  (env.storeConst address constant, address)

/-- Store a `muts` block together with every projection constant required by
anonymous ingress.  This is the physical layout emitted by the compiler. -/
def storeBlockWithProjections (env : Ixon.Env) (block : Ixon.Constant) :
    Ixon.Env × Address := Id.run do
  let (env, blockAddress) := storeConstant env block
  let mut env := env
  let .muts members := block.info | return (env, blockAddress)
  for h : index in [0:members.size] do
    let memberIndex := index.toUInt64
    match members[index] with
    | .defn _ =>
      env := (storeConstant env
        ⟨.dPrj ⟨memberIndex, blockAddress⟩, #[], #[], #[]⟩).1
    | .recr _ =>
      env := (storeConstant env
        ⟨.rPrj ⟨memberIndex, blockAddress⟩, #[], #[], #[]⟩).1
    | .indc ind =>
      env := (storeConstant env
        ⟨.iPrj ⟨memberIndex, blockAddress⟩, #[], #[], #[]⟩).1
      for constructorIndex in [0:ind.ctors.size] do
        env := (storeConstant env
          ⟨.cPrj ⟨memberIndex, constructorIndex.toUInt64, blockAddress⟩,
            #[], #[], #[]⟩).1
  return (env, blockAddress)

/-- Executable translation for the closed variable/sort/constant/application
and binder core used by generated inductive declarations and equations. -/
def translateCore? (theory : VEnv)
    (nameOf : Address → Option Lean.Name) : KExpr .anon → Option VExpr
  | .var index _ _ => some (.bvar index.toNat)
  | .sort level _ => some (.sort level.toVLevel)
  | .const id levels _ =>
      match nameOf id.addr with
      | none => none
      | some name =>
          match theory.constants name with
          | none => none
          | some constant =>
              if levels.size = constant.uvars then
                some (.const name (levels.toList.map KUniv.toVLevel))
              else none
  | .app fn argument _ => do
      return .app (← translateCore? theory nameOf fn)
        (← translateCore? theory nameOf argument)
  | .lam _ _ type body _ => do
      return .lam (← translateCore? theory nameOf type)
        (← translateCore? theory nameOf body)
  | .all _ _ type body _ => do
      return .forallE (← translateCore? theory nameOf type)
        (← translateCore? theory nameOf body)
  | _ => none

/-- Successful executable translation is a proof-relevant `RawExprRel`.
Native evaluation establishes only finite syntax equality; this theorem
assembles the trusted relation constructor by constructor. -/
theorem translateCore?_raw {theory : VEnv}
    {nameOf : Address → Option Lean.Name} {uvars : Nat}
    {ctx : List VExpr}
    {source : KExpr .anon} {target : VExpr}
    (success : translateCore? theory nameOf source = some target) :
    RawExprRel (uvars := uvars) theory nameOf RawProjRel.none ctx source
      target := by
  induction source generalizing ctx target with
  | var index name info =>
      simp only [translateCore?, Option.some.injEq] at success
      subst target
      exact .var
  | fvar => simp [translateCore?] at success
  | sort level info =>
      simp only [translateCore?, Option.some.injEq] at success
      subst target
      exact .sort
  | const id levels info =>
      simp only [translateCore?] at success
      split at success
      · contradiction
      · rename_i name hname
        split at success
        · contradiction
        · rename_i constant hconstant
          split at success
          · rename_i harity
            cases success
            exact .const hname hconstant harity
          · contradiction
  | app fn argument info ihFn ihArgument =>
      simp only [translateCore?] at success
      obtain ⟨fnTarget, hfn, success⟩ :=
        Option.bind_eq_some_iff.mp success
      obtain ⟨argumentTarget, hargument, success⟩ :=
        Option.bind_eq_some_iff.mp success
      cases success
      exact .app (ihFn hfn) (ihArgument hargument)
  | lam name bi type body info ihType ihBody =>
      simp only [translateCore?] at success
      obtain ⟨typeTarget, htype, success⟩ :=
        Option.bind_eq_some_iff.mp success
      obtain ⟨bodyTarget, hbody, success⟩ :=
        Option.bind_eq_some_iff.mp success
      cases success
      exact .lam (ihType htype) (ihBody hbody)
  | all name bi type body info ihType ihBody =>
      simp only [translateCore?] at success
      obtain ⟨typeTarget, htype, success⟩ :=
        Option.bind_eq_some_iff.mp success
      obtain ⟨bodyTarget, hbody, success⟩ :=
        Option.bind_eq_some_iff.mp success
      cases success
      exact .all (ihType htype) (ihBody hbody)
  | letE => simp [translateCore?] at success
  | prj => simp [translateCore?] at success
  | nat => simp [translateCore?] at success
  | str => simp [translateCore?] at success

/-! ## Executable scoping -/

/-- Boolean counterpart of the proof-only universe-scoping predicate. -/
def scopedUnivB (bound : Nat) : KUniv .anon → Bool
  | .zero _ => true
  | .succ u _ => scopedUnivB bound u
  | .max a b _ | .imax a b _ => scopedUnivB bound a && scopedUnivB bound b
  | .param index _ _ => decide (index.toNat < bound)

/-- Boolean counterpart of expression scoping, used by native fixture
evaluation without adding classical decision procedures. -/
def scopedExprB (depth : UInt64) (levelBound : Nat) :
    KExpr .anon → Bool
  | .var index _ _ => decide (index < depth)
  | .fvar .. => true
  | .sort u _ => scopedUnivB levelBound u
  | .const _ us _ => us.all (scopedUnivB levelBound)
  | .app fn argument _ =>
      scopedExprB depth levelBound fn && scopedExprB depth levelBound argument
  | .lam _ _ type body _ | .all _ _ type body _ =>
      scopedExprB depth levelBound type &&
        scopedExprB (depth + 1) levelBound body
  | .letE _ type value body _ _ =>
      scopedExprB depth levelBound type &&
        scopedExprB depth levelBound value &&
        scopedExprB (depth + 1) levelBound body
  | .prj _ _ value _ => scopedExprB depth levelBound value
  | .nat .. | .str .. => true

theorem scopedUnivB_eq_true_iff (bound : Nat) (u : KUniv .anon) :
    scopedUnivB bound u = true ↔ u.Scoped bound := by
  induction u with
  | zero => simp [scopedUnivB, KUniv.Scoped]
  | succ u _ ih => simpa [scopedUnivB, KUniv.Scoped] using ih
  | max a b _ iha ihb =>
      simp [scopedUnivB, KUniv.Scoped, iha, ihb]
  | imax a b _ iha ihb =>
      simp [scopedUnivB, KUniv.Scoped, iha, ihb]
  | param => simp [scopedUnivB, KUniv.Scoped]

theorem scopedExprB_eq_true_iff (depth : UInt64) (levelBound : Nat)
    (expression : KExpr .anon) :
    scopedExprB depth levelBound expression = true ↔
      expression.Scoped depth levelBound := by
  induction expression generalizing depth with
  | var => simp [scopedExprB, KExpr.Scoped]
  | fvar => simp [scopedExprB, KExpr.Scoped]
  | sort => simp [scopedExprB, KExpr.Scoped, scopedUnivB_eq_true_iff]
  | const =>
      simp only [scopedExprB, Array.all_eq_true,
        scopedUnivB_eq_true_iff, KExpr.Scoped]
      constructor
      · intro h u hu
        obtain ⟨index, hindex, rfl⟩ := Array.mem_iff_getElem.mp hu
        exact h index hindex
      · intro h index hindex
        exact h _ (Array.getElem_mem hindex)
  | app fn argument _ ihFn ihArgument =>
      simp [scopedExprB, KExpr.Scoped, ihFn, ihArgument]
  | lam _ _ type body _ ihType ihBody =>
      simp [scopedExprB, KExpr.Scoped, ihType, ihBody]
  | all _ _ type body _ ihType ihBody =>
      simp [scopedExprB, KExpr.Scoped, ihType, ihBody]
  | letE _ type value body _ _ ihType ihValue ihBody =>
      simp [scopedExprB, KExpr.Scoped, ihType, ihValue, ihBody, and_assoc]
  | prj _ _ value _ ihValue =>
      simp [scopedExprB, KExpr.Scoped, ihValue]
  | nat => simp [scopedExprB, KExpr.Scoped]
  | str => simp [scopedExprB, KExpr.Scoped]

instance kExprScopedDecidable (depth : UInt64) (levelBound : Nat)
    (expression : KExpr .anon) :
    Decidable (expression.Scoped depth levelBound) :=
  if h : scopedExprB depth levelBound expression = true then
    .isTrue ((scopedExprB_eq_true_iff depth levelBound expression).mp h)
  else
    .isFalse fun hscoped =>
      h ((scopedExprB_eq_true_iff depth levelBound expression).mpr hscoped)

end Ix.Tc.InductiveConcreteFixture
