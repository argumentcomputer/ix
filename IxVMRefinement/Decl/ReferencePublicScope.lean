import IxVMRefinement.Assembly.ReaderPublicKeys
import IxVMRefinement.Decl.ReferenceFrames

/-! # Raw public types across generated prefixes

The reader includes projection targets in its public-key guarantee. Since actual generated
checks preserve every public lookup, a raw definition type already resolves at the start of
its unit. Its scope can therefore omit the unit's fresh auxiliary names.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Refinement.Assembly (NonAuxKey isAux_eq_false_iff)

universe u

theorem public_resolves_eq {before after : Env .anon}
    (same : ∀ name, NonAuxKey name → after.find? name = before.find? name) :
    ∀ (e : Expr .anon), e.constsResolveBy (fun key => !key.isAux) = true →
      e.constsResolve after = e.constsResolve before := by
  intro e
  induction e with
  | bvar _ | sort _ => intro _; rfl
  | fvar _ ty ih => exact ih
  | const name levels =>
    intro publicKey
    have notAux : name.isAux = false := by
      simpa only [Expr.constsResolveBy, Bool.not_eq_true] using publicKey
    simp only [Expr.constsResolve, same name (isAux_eq_false_iff.mp notAux)]
  | app f a ihf iha =>
    intro publicKeys
    simp only [Expr.constsResolveBy, Bool.and_eq_true] at publicKeys
    simp only [Expr.constsResolve, ihf publicKeys.1, iha publicKeys.2]
  | lam ty body bm iht ihb | forallE ty body bm iht ihb =>
    intro publicKeys
    simp only [Expr.constsResolveBy, Bool.and_eq_true] at publicKeys
    simp only [Expr.constsResolve, iht publicKeys.1, ihb publicKeys.2]
  | letE ty value body bm iht ihv ihb =>
    intro publicKeys
    simp only [Expr.constsResolveBy, Bool.and_eq_true] at publicKeys
    simp only [Expr.constsResolve, iht publicKeys.1.1, ihv publicKeys.1.2, ihb publicKeys.2]
  | proj name i inner ih =>
    intro publicKeys
    simp only [Expr.constsResolveBy, Bool.and_eq_true, Bool.not_eq_true] at publicKeys
    simp only [Expr.constsResolve, same name (isAux_eq_false_iff.mp publicKeys.1), ih publicKeys.2]
  | lit literal =>
    intro _
    have roleSame : ∀ role, after.find? (.role role) = before.find? (.role role) := by
      intro role
      exact same _ (by intro base derived equal; cases equal)
    cases literal <;> simp only [Expr.constsResolve, natName, natZeroName, natSuccName,
      stringName, stringOfListName, listName, listNilName, listConsName, charName,
      charOfNatName, roleKey, roleSame]

/-- A checked public type uses only names that were present before its generated prefix. -/
theorem ReferenceReplay.public_type_scope {V : Type u} [SetTheory V]
    {fuel : Nat} {ev : Evidences .anon}
    {source target sourceMiddle targetMiddle : Env .anon}
    {completed generated : List (Declaration .anon)}
    (earlier : ReferenceReplay fuel ev Env.empty Env.empty completed source target)
    (auxiliary : ReferenceReplay fuel ev source target generated sourceMiddle targetMiddle)
    (allGenerated : ∀ d ∈ generated, d.isGenerated = true)
    {cv : ConstantVal .anon} {type : Expr .anon}
    (header : ConstantValRun .verified fuel targetMiddle cv type)
    (publicKeys : cv.type.constsResolveBy (fun key => !key.isAux) = true) :
    cv.type.Good (nameScope (namesOf completed)) := by
  have firstModel : EnvModelT V .verified target := earlier.checked.envModelT EnvModelT.empty
  have middleModel : EnvModelT V .verified targetMiddle := auxiliary.checked.envModelT firstModel
  obtain ⟨⟨model, _⟩, _⟩ := middleModel
  have store : Ix.Kernel.Open.StoreInv targetMiddle :=
    ⟨model.base2.wf, model.base2.rec_ctors, model.base2.proj_ok⟩
  have resolves := constantValRun_input_resolves store header
  have same := public_resolves_eq
    (fun _ publicName => auxiliary.generated_nonAux allGenerated publicName) cv.type publicKeys
  rw [same] at resolves
  apply expression_good_of_resolves ?_ cv.type resolves
  intro name present
  obtain ⟨ci, found⟩ := Option.isSome_iff_exists.mp present
  exact Key.good_nameScope.mpr (earlier.declaredScope name ci found)

end IxVM.Refinement.Decl
