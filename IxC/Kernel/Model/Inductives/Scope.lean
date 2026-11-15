module

public import IxC.Kernel.Inductives.Scope
public import IxC.Kernel.Model.Inductives.SumData
import IxC.Kernel.Model.Annot.BitRename

public section

namespace Ix.Kernel.Expr

theorem eraseFvarTypes_erasedEq (e : Expr md) : ErasedEq e (eraseFvarTypes e) := by
  induction e <;> simp_all [eraseFvarTypes, ErasedEq]

theorem constsResolve_shallow_of (env : Env md) (e : Expr md)
    (h : e.constsResolve env = true) : e.constsResolveShallow env = true := by
  unfold constsResolveShallow
  induction e <;> simp_all [eraseFvarTypes, constsResolve, Bool.and_eq_true]

end Ix.Kernel.Expr

namespace Ix.Kernel.Model

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.SetModel

/-- Pre-block scope outside free-variable annotations fixes the reading under every
interpretation of the fresh former. Indices and binder metadata are preserved by erasure. -/
theorem denoteMeta_acvalWith_shallow
    {acval : Key md → (LevelParam → Nat) → AnnotTerm} {T : Key md}
    {A₁ A₂ : (LevelParam → Nat) → AnnotTerm} {env₀ env : Env md} {φ : LevelParam → Nat}
    (hfresh : env₀.find? T = none) (d : Nat) (e : Expr md)
    (hcr : e.constsResolveShallow env₀ = true) :
    denoteMeta (acvalWith acval T A₁) env φ d e =
      denoteMeta (acvalWith acval T A₂) env φ d e := by
  calc
    _ = denoteMeta (acvalWith acval T A₁) env φ d e.eraseFvarTypes :=
      denoteMeta_erasedEq e.eraseFvarTypes_erasedEq d
    _ = denoteMeta (acvalWith acval T A₂) env φ d e.eraseFvarTypes :=
      denoteMeta_acvalWith_unmentioned₂ hfresh d e.eraseFvarTypes hcr
    _ = _ := (denoteMeta_erasedEq e.eraseFvarTypes_erasedEq d).symm

theorem DenoteMetaSpine.acvalWith_shallow
    {acval : Key md → (LevelParam → Nat) → AnnotTerm} {T : Key md}
    {A₁ A₂ : (LevelParam → Nat) → AnnotTerm} {env₀ env : Env md}
    (hfresh : env₀.find? T = none) {φ : LevelParam → Nat} {d : Nat} :
    ∀ {as : List (Expr md)} {vs : List AnnotTerm},
      (∀ e ∈ as, e.constsResolveShallow env₀ = true) →
      DenoteMetaSpine (acvalWith acval T A₁) env φ d as vs →
      DenoteMetaSpine (acvalWith acval T A₂) env φ d as vs
  | _, _, _, .nil => .nil
  | a :: _, _, hres, .cons ha htl =>
    .cons (by
        rw [← denoteMeta_acvalWith_shallow (A₁ := A₁) (A₂ := A₂) hfresh _ _
          (hres a List.mem_cons_self)]
        exact ha)
      (DenoteMetaSpine.acvalWith_shallow hfresh
        (fun e he => hres e (List.mem_cons_of_mem _ he)) htl)

universe u

theorem CtorDataI.Es_eq_shallow {V : Type u} [SetTheory V] {env : Env md}
    {acval : Key md → (LevelParam → Nat) → AnnotTerm} {T T' : Key md}
    {A₁ A₂ : (LevelParam → Nat) → AnnotTerm} {env₀ : Env md}
    {m₁ m₂ : EnvModel V env} (hac₁ : m₁.acval = acvalWith acval T' A₁)
    (hac₂ : m₂.acval = acvalWith acval T' A₂) (hfresh : env₀.find? T' = none)
    {lps : List LevelParam} {cvC : ConstantVal md} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List (Expr md)}
    {ds₁ ds₂ : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es₁ Es₂ : (LevelParam → Nat) → List AnnotTerm} {srcs₁ srcs₂ : List (Option Nat)}
    (h₁ : CtorDataI m₁ T lps cvC nP nF nIdx resSort isProp large idxArgs ds₁ Es₁ srcs₁)
    (h₂ : CtorDataI m₂ T lps cvC nP nF nIdx resSort isProp large idxArgs ds₂ Es₂ srcs₂)
    (hres : ∀ e ∈ idxArgs, e.constsResolveShallow env₀ = true) (φ : LevelParam → Nat) :
    Es₁ φ = Es₂ φ := by
  have hsp₁ := h₁.idxRead φ
  have hsp₂ := h₂.idxRead φ
  rw [hac₁] at hsp₁
  rw [hac₂] at hsp₂
  exact DenoteMetaSpine.unique (DenoteMetaSpine.acvalWith_shallow hfresh hres hsp₁) hsp₂

end Ix.Kernel.Model
