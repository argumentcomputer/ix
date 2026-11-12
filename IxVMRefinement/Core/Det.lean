import IxVMRefinement.Core.Rep
import Mathlib.Tactic.SplitIfs

/-! # Determinism of the term seam, up to level equivalence

A heap pointer represents at most one kernel term up to the semantic equality of its levels
(`Tm.det`): the images of one pointer differ only where `Tm` relates levels up to `LvEq`. Every
other part of the image (binder data included: `bmeta` reads the stored level's zero-ness,
which the heap determines) is a function of the heap. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

/-! ## Terms up to semantic level equality -/

/-- **Terms equal up to semantic level equality**: the same term, except that the levels of
sorts and constants are related by `LvEq`/`LvEqList`. -/
inductive ExprLvEq : KExpr → KExpr → Prop where
  | bvar {i : Nat} : ExprLvEq (.bvar i) (.bvar i)
  | fvar {i : Nat} {t₁ t₂ : KExpr} : ExprLvEq t₁ t₂ → ExprLvEq (.fvar i t₁) (.fvar i t₂)
  | sort {u v : KLevel} : LvEq u v → ExprLvEq (.sort u) (.sort v)
  | const {n : KKey} {us vs : List KLevel} : LvEqList us vs → ExprLvEq (.const n us) (.const n vs)
  | app {f₁ f₂ a₁ a₂ : KExpr} :
      ExprLvEq f₁ f₂ → ExprLvEq a₁ a₂ → ExprLvEq (.app f₁ a₁) (.app f₂ a₂)
  | lam {t₁ t₂ b₁ b₂ : KExpr} {m : Ix.Kernel.BinderMeta} :
      ExprLvEq t₁ t₂ → ExprLvEq b₁ b₂ → ExprLvEq (.lam t₁ b₁ m) (.lam t₂ b₂ m)
  | forallE {t₁ t₂ b₁ b₂ : KExpr} {m : Ix.Kernel.BinderMeta} :
      ExprLvEq t₁ t₂ → ExprLvEq b₁ b₂ → ExprLvEq (.forallE t₁ b₁ m) (.forallE t₂ b₂ m)
  | letE {t₁ t₂ v₁ v₂ b₁ b₂ : KExpr} {m : Ix.Kernel.LetMeta} :
      ExprLvEq t₁ t₂ → ExprLvEq v₁ v₂ → ExprLvEq b₁ b₂ →
        ExprLvEq (.letE t₁ v₁ b₁ m) (.letE t₂ v₂ b₂ m)
  | lit {l : Ix.Kernel.Literal} : ExprLvEq (.lit l) (.lit l)
  | proj {s : KKey} {i : Nat} {e₁ e₂ : KExpr} :
      ExprLvEq e₁ e₂ → ExprLvEq (.proj s i e₁) (.proj s i e₂)

theorem evalEqList_symm (φ : Ix.Kernel.LevelParam → Nat) :
    ∀ {us vs : List KLevel}, Ix.Kernel.Level.EvalEqList φ us vs →
      Ix.Kernel.Level.EvalEqList φ vs us
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, t⟩ => ⟨h.symm, evalEqList_symm φ t⟩

theorem evalEqList_trans (φ : Ix.Kernel.LevelParam → Nat) :
    ∀ {us vs ws : List KLevel}, Ix.Kernel.Level.EvalEqList φ us vs →
      Ix.Kernel.Level.EvalEqList φ vs ws → Ix.Kernel.Level.EvalEqList φ us ws
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, t₁⟩, ⟨h₂, t₂⟩ => ⟨h₁.trans h₂, evalEqList_trans φ t₁ t₂⟩

theorem LvEqList.symm {us vs : List KLevel} (h : LvEqList us vs) : LvEqList vs us :=
  fun φ => evalEqList_symm φ (h φ)

theorem LvEqList.trans {us vs ws : List KLevel} (h₁ : LvEqList us vs) (h₂ : LvEqList vs ws) :
    LvEqList us ws :=
  fun φ => evalEqList_trans φ (h₁ φ) (h₂ φ)

theorem ExprLvEq.refl : ∀ e : KExpr, ExprLvEq e e
  | .bvar _ => .bvar
  | .fvar _ t => .fvar (ExprLvEq.refl t)
  | .sort u => .sort (LvEq.refl u)
  | .const _ us => .const (LvEqList.refl us)
  | .app f a => .app (ExprLvEq.refl f) (ExprLvEq.refl a)
  | .lam t b _ => .lam (ExprLvEq.refl t) (ExprLvEq.refl b)
  | .forallE t b _ => .forallE (ExprLvEq.refl t) (ExprLvEq.refl b)
  | .letE t v b _ => .letE (ExprLvEq.refl t) (ExprLvEq.refl v) (ExprLvEq.refl b)
  | .lit _ => .lit
  | .proj _ _ e => .proj (ExprLvEq.refl e)

theorem ExprLvEq.symm {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) : ExprLvEq e₂ e₁ := by
  induction h with
  | bvar => exact .bvar
  | fvar _ ih => exact .fvar ih
  | sort hu => exact .sort hu.symm
  | const hus => exact .const hus.symm
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | lit => exact .lit
  | proj _ ih => exact .proj ih

theorem ExprLvEq.trans {e₁ e₂ e₃ : KExpr} (h₁ : ExprLvEq e₁ e₂) (h₂ : ExprLvEq e₂ e₃) :
    ExprLvEq e₁ e₃ := by
  induction h₁ generalizing e₃ with
  | bvar => exact h₂
  | fvar _ ih => cases h₂ with | fvar h => exact .fvar (ih h)
  | sort hu => cases h₂ with | sort hv => exact .sort (hu.trans hv)
  | const hus => cases h₂ with | const hvs => exact .const (hus.trans hvs)
  | app _ _ ihf iha => cases h₂ with | app hf ha => exact .app (ihf hf) (iha ha)
  | lam _ _ iht ihb => cases h₂ with | lam ht hb => exact .lam (iht ht) (ihb hb)
  | forallE _ _ iht ihb => cases h₂ with | forallE ht hb => exact .forallE (iht ht) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    cases h₂ with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  | lit => exact h₂
  | proj _ ih => cases h₂ with | proj h => exact .proj (ih h)

/-- Lifting respects level equivalence. -/
theorem ExprLvEq.lift {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) (n : Nat) :
    ∀ c, ExprLvEq (Ix.Kernel.Expr.liftLooseBVars n c e₁) (Ix.Kernel.Expr.liftLooseBVars n c e₂) := by
  induction h with
  | bvar => exact fun _ => ExprLvEq.refl _
  | fvar ht _ => intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .fvar ht
  | sort hu => intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .sort hu
  | const hus => intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .const hus
  | app _ _ ihf iha => intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .app (ihf c) (iha c)
  | lam _ _ iht ihb =>
    intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .lam (iht c) (ihb (c + 1))
  | forallE _ _ iht ihb =>
    intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .forallE (iht c) (ihb (c + 1))
  | letE _ _ _ iht ihv ihb =>
    intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .letE (iht c) (ihv c) (ihb (c + 1))
  | lit => exact fun _ => ExprLvEq.refl _
  | proj _ ih => intro c; simp only [Ix.Kernel.Expr.liftLooseBVars]; exact .proj (ih c)

/-- Capture-avoiding instantiation respects level equivalence. -/
theorem ExprLvEq.shift {v₁ v₂ : KExpr} (hv : ExprLvEq v₁ v₂) {e₁ e₂ : KExpr}
    (h : ExprLvEq e₁ e₂) : ∀ j, ExprLvEq (instShift v₁ j e₁) (instShift v₂ j e₂) := by
  induction h with
  | @bvar i =>
    intro j
    show ExprLvEq
      (if i = j then Ix.Kernel.Expr.liftLooseBVars j 0 v₁ else if j < i then .bvar (i - 1) else .bvar i)
      (if i = j then Ix.Kernel.Expr.liftLooseBVars j 0 v₂ else if j < i then .bvar (i - 1) else .bvar i)
    split_ifs <;> first | exact hv.lift j 0 | exact ExprLvEq.refl _
  | fvar ht _ => intro j; simp only [instShift]; exact .fvar ht
  | sort hu => intro j; simp only [instShift]; exact .sort hu
  | const hus => intro j; simp only [instShift]; exact .const hus
  | app _ _ ihf iha => intro j; simp only [instShift]; exact .app (ihf j) (iha j)
  | lam _ _ iht ihb => intro j; simp only [instShift]; exact .lam (iht j) (ihb (j + 1))
  | forallE _ _ iht ihb => intro j; simp only [instShift]; exact .forallE (iht j) (ihb (j + 1))
  | letE _ _ _ iht ihv ihb =>
    intro j; simp only [instShift]; exact .letE (iht j) (ihv j) (ihb (j + 1))
  | lit => exact fun _ => ExprLvEq.refl _
  | proj _ ih => intro j; simp only [instShift]; exact .proj (ih j)

/-! ## Determinism -/

theorem limbsVal_det {h : Heap F} {l₁ l₂ : List UInt64} {p : SourceValue F}
    (r₁ : RepList limbListEnum RepU64 h l₁ p) (r₂ : RepList limbListEnum RepU64 h l₂ p) :
    l₁ = l₂ :=
  IxVMRep.repList_det (fun a b => IxVMRep.repU64_det U32.Goldilocks.compatible a b) r₁ r₂

theorem bytes_det {h : Heap F} {b₁ b₂ : List UInt8} {p : SourceValue F}
    (r₁ : Bytes.RepByteStream byteListEnum h b₁ p) (r₂ : Bytes.RepByteStream byteListEnum h b₂ p) :
    b₁ = b₂ :=
  Bytes.repByteStream_inj U32.Goldilocks.compatible r₁ r₂

theorem addr_det {h : Heap F} {a₁ a₂ : Bytes.Address} {p : SourceValue F}
    (r₁ : Bytes.RepAddressRef addrTy h a₁ p) (r₂ : Bytes.RepAddressRef addrTy h a₂ p) : a₁ = a₂ :=
  IxVMRep.repAddressRef_det U32.Goldilocks.compatible r₁ r₂

/-- Two cells at one address are one value. -/
theorem cell_eq {h : Heap F} {addr : Nat} {v₁ v₂ : SourceValue F}
    (c₁ : h[addr]? = some v₁) (c₂ : h[addr]? = some v₂) : v₁ = v₂ := by
  rw [c₁] at c₂; injection c₂

/-- **The term seam is deterministic up to level equivalence.** -/
theorem Tm.det {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E₁ E₂ : KExpr} {p : SourceValue F} (r₁ : Tm κ d Γ h k E₁ p) (r₂ : Tm κ d Γ h k E₂ p) :
    ExprLvEq E₁ E₂ := by
  induction r₁ generalizing E₂ with
  | bvarLocal cell _ hi =>
    cases r₂ with
    | bvarLocal cell' _ _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; exact .bvar
    | bvarFree cell' _ hk _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; omega
    | sort cell' _ _ | const cell' _ _ _ | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _
    | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | bvarFree cell _ hk hd =>
    cases r₂ with
    | bvarLocal cell' _ hi =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; omega
    | bvarFree cell' _ _ _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; exact ExprLvEq.refl _
    | sort cell' _ _ | const cell' _ _ _ | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _
    | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | sort cell rl hu =>
    cases r₂ with
    | sort cell' rl' hu' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := rl.det rl'; subst this; exact .sort (hu.trans hu'.symm)
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | const cell' _ _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | const cell ra rls hus =>
    cases r₂ with
    | const cell' ra' rls' hus' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      have := rls.det rls'; subst this
      exact .const (hus.trans hus'.symm)
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | app cell _ _ ihf iha =>
    cases r₂ with
    | app cell' rf' ra' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      exact .app (ihf rf') (iha ra')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | lam cell _ _ rl iht ihb =>
    cases r₂ with
    | lam cell' rt' rb' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := rl.det rl'; subst this
      exact .lam (iht rt') (ihb rb')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _ | app cell' _ _
    | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | forallE cell _ _ rl iht ihb =>
    cases r₂ with
    | forallE cell' rt' rb' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := rl.det rl'; subst this
      exact .forallE (iht rt') (ihb rb')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _ | app cell' _ _
    | lam cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | letE cell _ _ _ iht ihv ihb =>
    cases r₂ with
    | letE cell' rt' rv' rb' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      exact (ihv rv').shift (ihb rb') 0
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litNat cell rl _ =>
    cases r₂ with
    | litNat cell' rl' _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := limbsVal_det rl rl'; subst this; exact .lit
    | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litStr cell rb hs =>
    cases r₂ with
    | litStr cell' rb' hs' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := bytes_det rb rb'; subst this
      rw [StrBytes] at hs hs'; rw [hs] at hs'; injection hs' with hs'; subst hs'; exact .lit
    | litNat cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | proj cell ra _ ihe =>
    cases r₂ with
    | proj cell' ra' re' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      exact .proj (ihe re')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this

end IxVM.Refinement.Core
