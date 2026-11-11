module

public import IxC.Kernel.Model.Open.Core
public import IxC.Kernel.Verify.StrLitExpr
import IxC.Kernel.Verify.EnvGuards

@[expose] public section

/-!
# The rules' soundness over the public `Model`: literals

`Denotes` reads a literal as its constructor form, so a literal's reading is fixed by the
model's values of the support constants. Where the kernel supports literals
(`natLitSupported`, `strLitSupported`: the support constants are stored at their pinned
types), `Model.mem` puts those values in the right sets, so

* a `Nat` literal denotes a member of what `Nat` denotes, and its constructor form is graded
  (`natLit_den`);
* a `String` literal denotes a member of what `String` denotes, and its constructor form
  (`String.ofList` of a `List.cons`/`List.nil` chain of `Char.ofNat` applications) is graded
  (`strLit_den`).

The rules `Red.natLit`, `Red.strLit`, `Infer.natLit` and `Infer.strLit` follow.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Stored constants in the sets -/

/-- **A stored constant at levels `us`** denotes its set at the assignment `us` induces, and
that set is a member of what its stored type denotes there (`Model.mem`). -/
theorem const_mem {n : Key md} {ci : ConstantInfo md} {lps : List LevelParam}
    {us : List Level} (hf : env.find? n = some ci) (hl : ci.toConstantVal.levelParams = lps)
    (hus : us.length = lps.length) (σ : Nat → V) :
    (∀ ρ, DenotesO M.cval env φ σ ρ (.const n us) (M.cval n (Level.substFn φ lps us))) ∧
    ∃ T, DenotesO M.cval env (Level.substFn φ lps us) σ ρ₀ ci.toConstantVal.type T ∧
      M.cval n (Level.substFn φ lps us) ∈ˢ T := by
  subst hl
  have hname : ci.name = n := find?_name hf
  obtain ⟨T, hT, hm⟩ := M.mem ci (List.mem_of_find?_eq_some hf)
    (Level.substFn φ ci.toConstantVal.levelParams us) ρ₀
  exact ⟨fun _ => .const hf hus, T, DenotesO.of_denotes hT, by rw [← hname]; exact hm⟩

omit [SetTheory V] in
theorem substFn_nil_eq (ψ : LevelParam → Nat) : Level.substFn ψ [] [] = ψ := by
  funext q
  rfl

/-- **A level-monomorphic stored constant** denotes `cval n φ`, a member of what its stored
type denotes. -/
theorem mono_const {n : Key md} {ci : ConstantInfo md} (hf : env.find? n = some ci)
    (hl : ci.toConstantVal.levelParams = []) (σ : Nat → V) :
    (∀ ρ, DenotesO M.cval env φ σ ρ (.const n []) (M.cval n φ)) ∧
    ∃ T, Den M φ σ ci.toConstantVal.type T ∧ M.cval n φ ∈ˢ T := by
  have h := const_mem (M := M) (φ := φ) (us := []) hf hl rfl σ
  rw [substFn_nil_eq] at h
  exact h

/-! ## `Nat` literals -/

/-- **A `∀` reading, inverted**: the product of its body's readings over its domain's. -/
theorem pi_inv {cval : Key md → (LevelParam → Nat) → V} {ψ : LevelParam → Nat} {σ : Nat → V}
    {ρ : BVarIdx → V} {ty body : Expr md} {m : BinderMeta} {v : V}
    (h : DenotesO cval env ψ σ ρ (.forallE ty body m) v) :
    ∃ (A : V) (B : V → V), v = piR (regime ψ m.pw) A B ∧ DenotesO cval env ψ σ ρ ty A ∧
      (∀ x, x ∈ˢ A → DenotesO cval env ψ σ (push x ρ) body (B x)) ∧
      (regime ψ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) := by
  cases h with
  | pi hA hB hP => exact ⟨_, _, rfl, hA, hB, hP⟩

/-- **The `Nat` basis in the sets**: `Nat.zero` denotes a member of what `Nat` does, and
`Nat.succ` a member of a product over it whose fibres are `Nat`'s set. -/
theorem nat_basis (hs : natLitSupported env = true) (σ : Nat → V) :
    ∃ (r : Nat) (B : V → V),
      (∀ ρ, DenotesO M.cval env φ σ ρ (.const natName []) (M.cval natName φ)) ∧
      (∀ ρ, DenotesO M.cval env φ σ ρ (.const natZeroName []) (M.cval natZeroName φ)) ∧
      (∀ ρ, DenotesO M.cval env φ σ ρ (.const natSuccName []) (M.cval natSuccName φ)) ∧
      M.cval natZeroName φ ∈ˢ M.cval natName φ ∧
      M.cval natSuccName φ ∈ˢ piR r (M.cval natName φ) B ∧
      (∀ x, x ∈ˢ M.cval natName φ → B x = M.cval natName φ) ∧
      (r = 0 → ∀ x, x ∈ˢ M.cval natName φ → B x ∈ˢ univ 0) := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlN, hlZ, hlS, -, htyZ, mb,
    htyS⟩ := natLitSupported_inv hs
  obtain ⟨hN, -⟩ := mono_const (M := M) (φ := φ) hfN hlN σ
  obtain ⟨hZ, TZ, hTZ, hZm⟩ := mono_const (M := M) (φ := φ) hfZ hlZ σ
  obtain ⟨hS, TS, hTS, hSm⟩ := mono_const (M := M) (φ := φ) hfS hlS σ
  have hTZ' : Den M φ σ cv0.type TZ := hTZ
  have hTS' : Den M φ σ cv1.type TS := hTS
  rw [htyZ] at hTZ'
  rw [htyS] at hTS'
  obtain rfl := DenotesO.functional hTZ' (hN ρ₀)
  obtain ⟨A, B, rfl, hA, hB, hP⟩ := pi_inv hTS'
  obtain rfl := DenotesO.functional hA (hN ρ₀)
  exact ⟨_, B, hN, hZ, hS, hZm, hSm,
    fun x hx => DenotesO.functional (hB x hx) (hN _), hP⟩

/-- **A `Nat` literal in the sets**: it denotes a member of what `Nat` denotes, and its
constructor form is graded. -/
theorem natLit_den (hs : natLitSupported env = true) (σ : Nat → V) :
    (∀ ρ, DenotesO M.cval env φ σ ρ (.const natName []) (M.cval natName φ)) ∧
      ∀ n : Nat, ∃ X, (∀ ρ, DenotesO M.cval env φ σ ρ (.lit (.natVal n)) X) ∧
        X ∈ˢ M.cval natName φ ∧ Gr M φ σ (natLitToConstructor n) := by
  obtain ⟨r, B, hN, hZ, hS, hZm, hSm, hBN, hP⟩ := nat_basis (M := M) (φ := φ) hs σ
  refine ⟨hN, fun n => ?_⟩
  induction n with
  | zero => exact ⟨_, fun ρ => .natLit (hZ ρ), hZm, True.intro⟩
  | succ k ih =>
    obtain ⟨X, hX, hXm, -⟩ := ih
    refine ⟨app (M.cval natSuccName φ) X, fun ρ => .natLit (.app (hS ρ) (hX ρ)), ?_, ?_⟩
    · have h := app_mem_piR hSm hXm (by rw [← univ_zero]; exact hP)
      rwa [hBN X hXm] at h
    · show Gr M φ σ (.app (.const natSuccName []) (.lit (.natVal k)))
      exact Gr.app_iff.2 ⟨True.intro, True.intro, r, _, _, X, B, hS ρ₀, hX ρ₀, hSm, hXm, hP⟩

/-- **A `Nat` literal unfolds to its constructor form** (`Red.natLit`). -/
theorem Red.natLit_sound {d n : Nat} (hs : natLitSupported env = true) :
    RedS M φ d (.lit (.natVal n)) (natLitToConstructor n) := by
  intro _
  refine ⟨Frame.of_closed (natLitToConstructor_hasFvar n)
      (natLitToConstructor_looseBVarsBounded n 0),
    LeavesSub.of_closed (natLitToConstructor_hasFvar n), fun σ _ v hv _ => ?_⟩
  obtain ⟨-, hlit⟩ := natLit_den (M := M) (φ := φ) hs σ
  obtain ⟨-, -, -, hg⟩ := hlit n
  cases hv with
  | natLit h => exact ⟨h, hg⟩

/-- **A `Nat` literal is typed `Nat`** (`Infer.natLit`). -/
theorem Infer.natLit_sound {g : Grade} {d n : Nat} (hs : natLitSupported env = true) :
    InferS M φ g d (.lit (.natVal n)) (.const natName []) := by
  cases g with
  | full =>
    intro _
    refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun σ _ => ?_⟩
    obtain ⟨hN, hlit⟩ := natLit_den (M := M) (φ := φ) hs σ
    obtain ⟨X, hX, hXm, -⟩ := hlit n
    exact ⟨X, _, hX ρ₀, True.intro, hN ρ₀, True.intro, hXm⟩
  | io =>
    intro _
    refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun σ _ v hv _ => ?_⟩
    obtain ⟨hN, hlit⟩ := natLit_den (M := M) (φ := φ) hs σ
    obtain ⟨X, hX, hXm, -⟩ := hlit n
    obtain rfl := DenotesO.functional hv (hX ρ₀)
    exact ⟨_, hN ρ₀, True.intro, hXm⟩

/-! ## `String` literals -/

/-- **A `String` literal in the sets**: it denotes a member of what `String` denotes, and its
constructor form is graded. The list's type `List.{0} Char` is read through `String.ofList`'s
domain; `List.nil` and `List.cons` are read at their instantiated level, which `cval_params`
lines up with it. -/
theorem strLit_den (hs : strLitSupported env = true) (σ : Nat → V) :
    (∀ ρ, DenotesO M.cval env φ σ ρ (.const stringName []) (M.cval stringName φ)) ∧
      ∀ s : String, ∃ X, (∀ ρ, DenotesO M.cval env φ σ ρ (.lit (.strVal s)) X) ∧
        X ∈ˢ M.cval stringName φ ∧ Gr M φ σ (strLitToConstructor s) := by
  obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL, hfN, hfC, hfH,
    hfF, hlS, hlO, hlL, hlN, hlC, hlH, hlF, -, htyH, ⟨mbO, htyO⟩, -, ⟨mbN, htyN⟩,
    ⟨mb1, mb2, mb3, htyC⟩, ⟨mbF, htyF⟩⟩ := strLitSupported_inv hs
  obtain ⟨hN, hlit⟩ := natLit_den (M := M) (φ := φ) hnat σ
  -- `String` and `Char`
  obtain ⟨hSTR, -⟩ := mono_const (M := M) (φ := φ) hfS hlS σ
  obtain ⟨hC, TH, hTH, hCm⟩ := mono_const (M := M) (φ := φ) hfH hlH σ
  rw [htyH] at hTH
  cases hTH
  have hC1 : ∀ (ψ : LevelParam → Nat) (p : LevelParam), Level.eval ψ (.param p) = 0 →
      M.cval charName φ ∈ˢ (univ (Level.eval ψ (.succ (.param p))) : V) := by
    intro ψ p hp
    have h : Level.eval ψ (.succ (.param p)) = Level.eval φ (.succ .zero) := by
      simp only [Level.eval] at hp ⊢
      rw [hp]
    rw [h]
    exact hCm
  -- `List.{l}` at any level of value `0` is `List.{0}`
  have hList : ∀ (ψ : LevelParam → Nat) (l : Level), Level.eval ψ l = 0 →
      M.cval listName (Level.substFn ψ [pL] [l]) =
        M.cval listName (Level.substFn φ [pL] [.zero]) := by
    intro ψ l hl0
    refine M.cval_params listName ciL hfL _ _ fun p hp => ?_
    rw [hlL, List.mem_singleton] at hp
    subst hp
    simp [Level.substFn, Level.eval, hl0]
  have hListApp : ∀ (ψ : LevelParam → Nat) (l : Level) (ρ : BVarIdx → V) (i : Nat) (Y : V),
      Level.eval ψ l = 0 →
      DenotesO M.cval env ψ σ ρ (.app (.const listName [l]) (.bvar i)) Y →
      Y = app (M.cval listName (Level.substFn φ [pL] [.zero])) (ρ i) := by
    intro ψ l ρ i Y hl0 hY
    have hc : DenotesO M.cval env ψ σ ρ (.const listName [l])
        (M.cval listName (Level.substFn ψ ciL.toConstantVal.levelParams [l])) :=
      .const hfL (by simp [hlL])
    rw [DenotesO.functional hY (.app hc .bvar), hlL, hList ψ l hl0]
  have hLT : ∀ ρ, DenotesO M.cval env φ σ ρ (.app (.const listName [.zero]) (.const charName []))
      (app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ)) := by
    intro ρ
    have hc : DenotesO M.cval env φ σ ρ (.const listName [.zero])
        (M.cval listName (Level.substFn φ ciL.toConstantVal.levelParams [.zero])) :=
      .const hfL (by simp [hlL])
    rw [hlL] at hc
    exact .app hc (hC ρ)
  -- `Char.ofNat` maps `Nat` into `Char`
  obtain ⟨hF, TF, hTF, hFm⟩ := mono_const (M := M) (φ := φ) hfF hlF σ
  rw [htyF] at hTF
  obtain ⟨AF, BF, rfl, hAF, hBF, hPF⟩ := pi_inv hTF
  obtain rfl := DenotesO.functional hAF (hN ρ₀)
  have hchar : ∀ c : Char, ∃ H, (∀ ρ, DenotesO M.cval env φ σ ρ
      (.app (.const charOfNatName []) (.lit (.natVal c.toNat))) H) ∧
      H ∈ˢ M.cval charName φ ∧
      Gr M φ σ (.app (.const charOfNatName []) (.lit (.natVal c.toNat))) := by
    intro c
    obtain ⟨X, hX, hXm, -⟩ := hlit c.toNat
    have h := app_mem_piR hFm hXm (by rw [← univ_zero]; exact hPF)
    rw [DenotesO.functional (hBF X hXm) (hC _)] at h
    exact ⟨_, fun ρ => .app (hF ρ) (hX ρ), h,
      Gr.app_iff.2 ⟨True.intro, True.intro, _, _, _, X, BF, hF ρ₀, hX ρ₀, hFm, hXm, hPF⟩⟩
  -- `List.nil.{0} Char`
  obtain ⟨hNIL, TN, hTN, hNILm⟩ := const_mem (M := M) (φ := φ) (us := [.zero]) hfN hlN rfl σ
  rw [htyN] at hTN
  obtain ⟨AN, BN, rfl, hAN, hBN, hPN⟩ := pi_inv hTN
  cases hAN
  have hp0N : Level.eval (Level.substFn φ [pN] [.zero]) (.param pN) = 0 := by
    simp [Level.substFn, Level.eval]
  have hCN := hC1 (Level.substFn φ [pN] [.zero]) pN hp0N
  have hnilm : app (M.cval listNilName (Level.substFn φ [pN] [.zero])) (M.cval charName φ) ∈ˢ
      app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) := by
    have h := app_mem_piR hNILm hCN (by rw [← univ_zero]; exact hPN)
    rw [hListApp (Level.substFn φ [pN] [.zero]) (.param pN) (push (M.cval charName φ) ρ₀) 0 _
      hp0N (hBN _ hCN)] at h
    exact h
  have hnilg : Gr M φ σ (.app (.const listNilName [.zero]) (.const charName [])) :=
    Gr.app_iff.2 ⟨True.intro, True.intro, _, _, _, _, BN, hNIL ρ₀, hC ρ₀, hNILm, hCN, hPN⟩
  -- `List.cons.{0} Char`
  obtain ⟨hCONS, TC, hTC, hCONSm⟩ := const_mem (M := M) (φ := φ) (us := [.zero]) hfC hlC rfl σ
  rw [htyC] at hTC
  obtain ⟨A1, B1, rfl, hA1, hB1, hP1⟩ := pi_inv hTC
  cases hA1
  have hp0C : Level.eval (Level.substFn φ [pC] [.zero]) (.param pC) = 0 := by
    simp [Level.substFn, Level.eval]
  have hCC := hC1 (Level.substFn φ [pC] [.zero]) pC hp0C
  obtain ⟨A2, B2, hY1, hA2, hB2, hP2⟩ := pi_inv (hB1 _ hCC)
  cases hA2
  have hB2v : ∀ h, h ∈ˢ M.cval charName φ →
      B2 h = piR (regime (Level.substFn φ [pC] [.zero]) mb3.pw)
        (app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ))
        (fun _ => app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ)) ∧
      (regime (Level.substFn φ [pC] [.zero]) mb3.pw = 0 →
        ∀ t, t ∈ˢ app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) →
          app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) ∈ˢ
            univ 0) := by
    intro h hh
    obtain ⟨A3, B3, hY2, hA3, hB3, hP3⟩ := pi_inv (hB2 h hh)
    have hA3v := hListApp (Level.substFn φ [pC] [.zero]) (.param pC) _ 1 _ hp0C hA3
    have hB3v : ∀ t, t ∈ˢ A3 →
        B3 t = app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) :=
      fun t ht => hListApp (Level.substFn φ [pC] [.zero]) (.param pC) _ 2 _ hp0C (hB3 t ht)
    subst hA3v
    refine ⟨by rw [hY2]; exact piR_congr hB3v, fun h0 t ht => ?_⟩
    rw [← hB3v t ht]
    exact hP3 h0 t ht
  have hcons : ∀ (H T : V), H ∈ˢ M.cval charName φ →
      T ∈ˢ app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) →
      ∀ (eH eT : Expr md), (∀ ρ, DenotesO M.cval env φ σ ρ eH H) → Gr M φ σ eH →
        (∀ ρ, DenotesO M.cval env φ σ ρ eT T) → Gr M φ σ eT →
        app (app (app (M.cval listConsName (Level.substFn φ [pC] [.zero]))
            (M.cval charName φ)) H) T ∈ˢ
          app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) ∧
        Gr M φ σ (.app (.app (.app (.const listConsName [.zero]) (.const charName [])) eH)
          eT) := by
    intro H T hH hT eH eT hdH hgH hdT hgT
    have m1 := app_mem_piR hCONSm hCC (by rw [← univ_zero]; exact hP1)
    rw [hY1] at m1
    have m2 := app_mem_piR m1 hH (by rw [← univ_zero]; exact hP2)
    obtain ⟨hB2H, hP3⟩ := hB2v H hH
    rw [hB2H] at m2
    have m3 := app_mem_piR m2 hT (by rw [← univ_zero]; exact hP3)
    have g1 : Gr M φ σ (.app (.const listConsName [.zero]) (.const charName [])) :=
      Gr.app_iff.2 ⟨True.intro, True.intro, _, _, _, _, B1, hCONS ρ₀, hC ρ₀, hCONSm, hCC, hP1⟩
    have g2 : Gr M φ σ (.app (.app (.const listConsName [.zero]) (.const charName [])) eH) :=
      Gr.app_iff.2 ⟨g1, hgH, _, _, _, H, B2, .app (hCONS ρ₀) (hC ρ₀), hdH ρ₀, m1, hH, hP2⟩
    exact ⟨m3, Gr.app_iff.2 ⟨g2, hgT, _, _, _, T, _, .app (.app (hCONS ρ₀) (hC ρ₀)) (hdH ρ₀),
      hdT ρ₀, m2, hT, hP3⟩⟩
  -- the character list
  have hlist : ∀ cs : List Char, ∃ T, (∀ ρ, DenotesO M.cval env φ σ ρ (strLitList cs) T) ∧
      T ∈ˢ app (M.cval listName (Level.substFn φ [pL] [.zero])) (M.cval charName φ) ∧
      Gr M φ σ (strLitList cs) := by
    intro cs
    induction cs with
    | nil => exact ⟨_, fun ρ => .app (hNIL ρ) (hC ρ), hnilm, hnilg⟩
    | cons c cs ih =>
      obtain ⟨T, hT, hTm, hTg⟩ := ih
      obtain ⟨H, hH, hHm, hHg⟩ := hchar c
      obtain ⟨hm, hg⟩ := hcons H T hHm hTm _ _ hH hHg hT hTg
      exact ⟨_, fun ρ => .app (.app (.app (hCONS ρ) (hC ρ)) (hH ρ)) (hT ρ), hm, hg⟩
  -- `String.ofList`
  obtain ⟨hO, TO, hTO, hOm⟩ := mono_const (M := M) (φ := φ) hfO hlO σ
  rw [htyO] at hTO
  obtain ⟨AO, BO, rfl, hAO, hBO, hPO⟩ := pi_inv hTO
  obtain rfl := DenotesO.functional hAO (hLT ρ₀)
  refine ⟨hSTR, fun s => ?_⟩
  obtain ⟨T, hT, hTm, hTg⟩ := hlist s.toList
  have h := app_mem_piR hOm hTm (by rw [← univ_zero]; exact hPO)
  rw [DenotesO.functional (hBO T hTm) (hSTR _)] at h
  have hD : ∀ ρ, DenotesO M.cval env φ σ ρ (strLitToConstructor s)
      (app (M.cval stringOfListName φ) T) := by
    intro ρ
    rw [strLitToConstructor_eq]
    exact .app (hO ρ) (hT ρ)
  have hG : Gr M φ σ (strLitToConstructor s) := by
    rw [strLitToConstructor_eq]
    exact Gr.app_iff.2 ⟨True.intro, hTg, _, _, _, T, BO, hO ρ₀, hT ρ₀, hOm, hTm, hPO⟩
  exact ⟨_, fun ρ => .strLit (hD ρ), h, hG⟩

/-- **A `String` literal unfolds to its constructor form** (`Red.strLit`). -/
theorem Red.strLit_sound {d : Nat} {s : String} (hs : strLitSupported env = true) :
    RedS M φ d (.lit (.strVal s)) (strLitToConstructor s) := by
  intro _
  refine ⟨Frame.of_closed (strLitToConstructor_hasFvar s) (strLitToConstructor_looseBVars s 0),
    LeavesSub.of_closed (strLitToConstructor_hasFvar s), fun σ _ v hv _ => ?_⟩
  obtain ⟨-, hlit⟩ := strLit_den (M := M) (φ := φ) hs σ
  obtain ⟨-, -, -, hg⟩ := hlit s
  cases hv with
  | strLit h => exact ⟨h, hg⟩

/-- **A `String` literal is typed `String`** (`Infer.strLit`). -/
theorem Infer.strLit_sound {g : Grade} {d : Nat} {s : String}
    (hs : strLitSupported env = true) :
    InferS M φ g d (.lit (.strVal s)) (.const stringName []) := by
  cases g with
  | full =>
    intro _
    refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun σ _ => ?_⟩
    obtain ⟨hS, hlit⟩ := strLit_den (M := M) (φ := φ) hs σ
    obtain ⟨X, hX, hXm, -⟩ := hlit s
    exact ⟨X, _, hX ρ₀, True.intro, hS ρ₀, True.intro, hXm⟩
  | io =>
    intro _
    refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun σ _ v hv _ => ?_⟩
    obtain ⟨hS, hlit⟩ := strLit_den (M := M) (φ := φ) hs σ
    obtain ⟨X, hX, hXm, -⟩ := hlit s
    obtain rfl := DenotesO.functional hv (hX ρ₀)
    exact ⟨_, hS ρ₀, True.intro, hXm⟩

end Ix.Kernel.Open
