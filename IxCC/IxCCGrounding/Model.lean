import IxCCGrounding.Laws

/-!
# Small facts about `Denotes` in any model (`IxCCGrounding.Model`)

Inversion lemmas for the syntax forms, β on a λ *term* (which needs only the argument in the
domain: in regime `0` both sides are the proof point by the λ rule's own side condition), and
application of a member of a `∀` term's denotation.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {md : Mode}

theorem find_mem {env : Env md} {n : Key md} {ci : ConstantInfo md}
    (h : env.find? n = some ci) : ci ∈ env.consts :=
  List.mem_of_find?_eq_some h

theorem substFn_nil (φ : LevelParam → Nat) : Level.substFn φ [] [] = φ := funext fun _ => rfl

theorem substFn_param0 (φ : LevelParam → Nat) : Level.substFn φ [0] [.param 0] = φ := by
  funext n
  by_cases h : 0 = n
  · subst h; simp [Level.substFn, Level.eval]
  · simp [Level.substFn, h]

/-- `ifAllZero [0]` reads `0` exactly where the parameter `0` is `0`. -/
theorem regime_ifAllZero0 (φ : LevelParam → Nat) :
    regime φ (PropWhen.ifAllZero [0]) = 0 ↔ φ 0 = 0 := by
  simp [regime]

theorem regime_never (φ : LevelParam → Nat) : regime φ PropWhen.never = 1 := by
  simp [regime]

section Den

variable {cval : Key md → (LevelParam → Nat) → V} {env : Env md} {φ : LevelParam → Nat}

theorem den_bvar {ρ : BVarIdx → V} {i : Nat} {X : V} :
    Denotes cval env φ ρ (.bvar i) X ↔ X = ρ i :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .bvar⟩

theorem den_app {ρ : BVarIdx → V} {f a : Expr md} {X : V} :
    Denotes cval env φ ρ (.app f a) X ↔
      ∃ F A, Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a A ∧ X = app F A :=
  ⟨fun h => by cases h with | app hf ha => exact ⟨_, _, hf, ha, rfl⟩,
   fun ⟨_, _, hf, ha, h⟩ => h ▸ .app hf ha⟩

theorem den_sort {ρ : BVarIdx → V} {u : Level} {X : V} :
    Denotes cval env φ ρ (.sort u) X ↔ X = univ (Level.eval φ u) :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .sort⟩

/-- A stored constant without level parameters, used at none, denotes its `cval` at `φ`, in
every variable environment. -/
theorem den_const0 {ρ : BVarIdx → V} {n : Key md} {ci : ConstantInfo md} {X : V}
    (hf : env.find? n = some ci) (hl : ci.toConstantVal.levelParams = []) :
    Denotes cval env φ ρ (.const n []) X ↔ X = cval n φ := by
  constructor
  · intro h
    cases h with
    | const hf' _ =>
      rw [hf] at hf'; cases hf'; rw [hl, substFn_nil]
  · intro h
    subst h
    have h' := Denotes.const (cval := cval) (env := env) (φ := φ) (ρ := ρ) (us := []) hf
      (by rw [hl]; rfl)
    rwa [hl, substFn_nil] at h'

/-- A stored constant with the one level parameter `0`, used at `param 0`, denotes its `cval`
at `φ`. -/
theorem den_const_param0 {ρ : BVarIdx → V} {n : Key md} {ci : ConstantInfo md} {X : V}
    (hf : env.find? n = some ci) (hl : ci.toConstantVal.levelParams = [0]) :
    Denotes cval env φ ρ (.const n [.param 0]) X ↔ X = cval n φ := by
  constructor
  · intro h
    cases h with
    | const hf' _ =>
      rw [hf] at hf'; cases hf'; rw [hl, substFn_param0]
  · intro h
    subst h
    have h' := Denotes.const (cval := cval) (env := env) (φ := φ) (ρ := ρ) (us := [.param 0]) hf
      (by rw [hl]; rfl)
    rwa [hl, substFn_param0] at h'

theorem den_pi {ρ : BVarIdx → V} {A B : Expr md} {m : BinderMeta} {X : V} :
    Denotes cval env φ ρ (.forallE A B m) X ↔
      ∃ (Ad : V) (Bf : V → V), Denotes cval env φ ρ A Ad ∧
        (∀ x, x ∈ˢ Ad → Denotes cval env φ (push x ρ) B (Bf x)) ∧
        (regime φ m.pw = 0 → ∀ x, x ∈ˢ Ad → Bf x ∈ˢ univ 0) ∧ X = piR (regime φ m.pw) Ad Bf :=
  ⟨fun h => by cases h with | pi hA hB hP => exact ⟨_, _, hA, hB, hP, rfl⟩,
   fun ⟨_, _, hA, hB, hP, h⟩ => h ▸ .pi hA hB hP⟩

theorem den_lam {ρ : BVarIdx → V} {A b : Expr md} {m : BinderMeta} {X : V} :
    Denotes cval env φ ρ (.lam A b m) X ↔
      ∃ (Ad : V) (F : V → V), Denotes cval env φ ρ A Ad ∧
        (∀ x, x ∈ˢ Ad → Denotes cval env φ (push x ρ) b (F x)) ∧
        (regime φ m.pw = 0 → ∀ x, x ∈ˢ Ad → F x = pt) ∧ X = lamR (regime φ m.pw) Ad F :=
  ⟨fun h => by cases h with | lam hA hF hP => exact ⟨_, _, hA, hF, hP, rfl⟩,
   fun ⟨_, _, hA, hF, hP, h⟩ => h ▸ .lam hA hF hP⟩

/-- **β on a λ term**, at a point of its domain: the application is the body's denotation
with the point bound. No typing: in regime `0` both sides are the proof point. -/
theorem app_den_lam {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {X A x : V}
    (hX : Denotes cval env φ ρ (.lam ty body m) X) (hA : Denotes cval env φ ρ ty A)
    (hx : x ∈ˢ A) : ∃ Y, Denotes cval env φ (push x ρ) body Y ∧ app X x = Y := by
  obtain ⟨Ad, F, hA', hF, hP, rfl⟩ := den_lam.mp hX
  obtain rfl := Denotes_functional hA hA'
  refine ⟨F x, hF x hx, ?_⟩
  by_cases hr : regime φ m.pw = 0
  · rw [hr, lamR_zero, app_pt]; exact (hP hr x hx).symm
  · exact app_lamR_pos hr hx

/-- Application of a member of a `∀` term's denotation, at a point of the domain, lands in the
fibre. -/
theorem app_mem_den_pi {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {T A f x : V}
    (hT : Denotes cval env φ ρ (.forallE ty body m) T) (hA : Denotes cval env φ ρ ty A)
    (hf : f ∈ˢ T) (hx : x ∈ˢ A) :
    ∃ B, Denotes cval env φ (push x ρ) body B ∧ app f x ∈ˢ B := by
  obtain ⟨Ad, Bf, hA', hB, hP, rfl⟩ := den_pi.mp hT
  obtain rfl := Denotes_functional hA hA'
  exact ⟨Bf x, hB x hx, app_mem_piR hf hx (fun h0 y hy => by
    have := hP h0 y hy; rwa [univ_zero] at this)⟩

end Den

end IxCC.Grounding
