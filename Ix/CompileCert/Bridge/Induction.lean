import Ix.CompileCert.Bridge.Rules
import IxC.Kernel.BasisA

/-!
# M7 X2: model-level induction

A recursor's typing law in the checker's model gives induction over the model's reading of the
inductive type, for **any** meta-level predicate (PLAN-L2a §2.0 B2(b), risk R8). The motive is the
graph of the predicate's truth values over the carrier (`predMotive`); `SetTheory V`'s separation
and replacement take arbitrary Lean predicates, so there is no definability side condition. At a
`Prop` motive (universe `0`) every minor premise's type is a truth value whose inhabitation is the
induction step, and the conclusion's fibre at `t` is `truthVal (P t)`, inhabited exactly when
`P t` holds.

* the set-level kit: `predMotive`, `predMotive_mem`, `app_predMotive`, `piR_inhabited` (a product is
  inhabited when every fibre is, in either regime), `inhabited_of_mem_piR`;
* inversion of the public reading at each syntax form (`denotes_pi_inv`, `denotes_app_inv`,
  `denotes_const_inv`, `denotes_bvar_inv`, `denotes_sort_inv`), the tool for reading an installed
  type's denotation off its syntax;
* the generic step (`model_telescope_inhabited`): an installed constant applied to a typed tuple
  (`InstalledTelescope`) lands in its result's reading, which is therefore inhabited;
* **the `Nat` instance** (`nat_induction`): in every strong model of a checked environment holding
  `Nat.rec`, `∀ n ∈ ⟦Nat⟧, P n` from `P ⟦Nat.zero⟧` and `∀ n ∈ ⟦Nat⟧, P n → P (⟦Nat.succ⟧ n)`, read
  off `Nat.rec`'s installed type (the checker's pinned, annotated `natRecA`) at universe `0`.
-/

namespace Ix.CompileCert.Bridge

open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel

universe u

section Kit

variable {V : Type u} [Kernel.SetTheory V]

/-- The motive a meta-level predicate defines on a carrier: the graph of its truth values. -/
noncomputable def predMotive (A : V) (P : V → Prop) : V := lamR 1 A (fun t => truthVal (P t))

theorem predMotive_mem (A : V) (P : V → Prop) {B : V → V} (hB : ∀ x, x ∈ˢ A → B x = univ 0) :
    predMotive A P ∈ˢ piR 1 A B :=
  lamR_mem fun x hx => by rw [hB x hx, univ_zero]; exact truthVal_mem_univZero _

theorem app_predMotive {A t : V} {P : V → Prop} (ht : t ∈ˢ A) :
    app (predMotive A P) t = truthVal (P t) :=
  app_lamR_pos (by decide) ht

/-- A product is inhabited when every fibre is, in either regime. -/
theorem piR_inhabited {r : Nat} {A : V} {B : V → V} (h : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) :
    ∃ f, f ∈ˢ piR r A B := by
  by_cases hr : r = 0
  · subst hr; exact ⟨pt, pt_mem_piR_zero h⟩
  · classical
    refine ⟨graph (fun x => if hx : x ∈ˢ A then Classical.choose (h x hx) else empty) A, ?_⟩
    rw [piR_pos hr]
    exact graph_mem_piSet fun x hx => by
      simp only [hx, ↓reduceDIte]; exact Classical.choose_spec (h x hx)

/-- A member of a product inhabits every fibre over the domain. -/
theorem inhabited_of_mem_piR {r : Nat} {A f : V} {B : V → V} (hf : f ∈ˢ piR r A B) :
    ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x := by
  by_cases hr : r = 0
  · subst hr; rw [piR_zero] at hf; exact of_mem_truthVal hf
  · intro x hx; exact ⟨app f x, app_mem_piR_pos hr hf hx⟩

end Kit

/-! ## Inversion of the public reading -/

section Inversion

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat} {ρ : Nat → V}

theorem denotes_bvar_inv {i : Nat} {T : V} (h : Denotes cval env φ ρ (.bvar i) T) : T = ρ i := by
  cases h; rfl

theorem denotes_sort_inv {l : Kernel.Level} {T : V} (h : Denotes cval env φ ρ (.sort l) T) :
    T = univ (Kernel.Level.eval φ l) := by
  cases h; rfl

theorem denotes_const_inv {n : Kernel.Name} {us : List Kernel.Level} {T : V}
    (h : Denotes cval env φ ρ (.const n us) T) :
    ∃ ci, env.find? n = some ci ∧ us.length = ci.toConstantVal.levelParams.length ∧
      T = cval n (Kernel.Level.substFn φ ci.toConstantVal.levelParams us) := by
  cases h with
  | const hf hlen => exact ⟨_, hf, hlen, rfl⟩

theorem denotes_app_inv {f a : Kernel.Expr} {T : V} (h : Denotes cval env φ ρ (.app f a) T) :
    ∃ F X, Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a X ∧ T = app F X := by
  cases h with
  | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

theorem denotes_pi_inv {ty body : Kernel.Expr} {m : Kernel.BinderMeta} {T : V}
    (h : Denotes cval env φ ρ (.forallE ty body m) T) :
    ∃ A B, Denotes cval env φ ρ ty A ∧
      (∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (B x)) ∧
      (Kernel.regime φ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) ∧
      T = piR (Kernel.regime φ m.pw) A B := by
  cases h with
  | pi hA hB hP => exact ⟨_, _, hA, hB, hP, rfl⟩

theorem denotes_lam_inv {ty body : Kernel.Expr} {m : Kernel.BinderMeta} {T : V}
    (h : Denotes cval env φ ρ (.lam ty body m) T) :
    ∃ A F, Denotes cval env φ ρ ty A ∧
      (∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (F x)) ∧
      (Kernel.regime φ m.pw = 0 → ∀ x, x ∈ˢ A → F x = pt) ∧
      T = lamR (Kernel.regime φ m.pw) A F := by
  cases h with
  | lam hA hF hP => exact ⟨_, _, hA, hF, hP, rfl⟩

/-- The generic step: an installed constant applied to a typed tuple lands in its result's
reading, which is therefore inhabited. -/
theorem model_telescope_inhabited (model : Kernel.Model V env) {c : Kernel.ConstantInfo}
    (installed : c ∈ env.consts) {finalρ : Nat → V} {result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope model.cval env φ ρ c.toConstantVal.type arguments finalρ result) :
    ∃ R, Denotes model.cval env φ finalρ result R ∧ ∃ y, y ∈ˢ R := by
  obtain ⟨R, hR, hm⟩ := typed.model_apply model installed
  exact ⟨R, hR, _, hm⟩

end Inversion

/-! ## The `Nat` instance -/

section Nat

variable {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}

/-- `Nat.rec`'s installed type: the checker's pinned, annotated `natRecA` (`IxC/Kernel/BasisA.lean`). -/
theorem natRecA_type : Kernel.natRecA.toConstantVal.type =
    .forallE (.forallE (.const Kernel.natName []) (.sort (.param Kernel.BasisDSL.uN)) ⟨.never⟩)
      (.forallE (.app (.bvar 0) (.const Kernel.natZeroName []))
        (.forallE
          (.forallE (.const Kernel.natName [])
            (.forallE (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const Kernel.natSuccName []) (.bvar 1)))
              ⟨.ifAllZero [Kernel.BasisDSL.uN]⟩)
            ⟨.ifAllZero [Kernel.BasisDSL.uN]⟩)
          (.forallE (.const Kernel.natName []) (.app (.bvar 3) (.bvar 0))
            ⟨.ifAllZero [Kernel.BasisDSL.uN]⟩)
          ⟨.ifAllZero [Kernel.BasisDSL.uN]⟩)
        ⟨.ifAllZero [Kernel.BasisDSL.uN]⟩)
      ⟨.ifAllZero [Kernel.BasisDSL.uN]⟩ := rfl

theorem natZeroA_type : Kernel.natZeroA.toConstantVal.type = .const Kernel.natName [] := rfl

theorem natSuccA_type :
    Kernel.natSuccA.toConstantVal.type = .forallE (.const Kernel.natName []) (.const Kernel.natName [])
      ⟨.never⟩ := rfl

/-- A pinned basis constant is the checker's annotated pin. -/
theorem pinned_natRec (strong : StrongInstalledModel V env) {ci : Kernel.ConstantInfo}
    (lookup : env.find? (Kernel.natName.str "rec") = some ci) : ci = Kernel.natRecA := by
  have h := (strong.internal.base2.basis_pinned _ ci lookup (by decide)).1
  rw [h]; rfl

theorem pinned_natZero (strong : StrongInstalledModel V env) {ci : Kernel.ConstantInfo}
    (lookup : env.find? Kernel.natZeroName = some ci) : ci = Kernel.natZeroA := by
  have h := (strong.internal.base2.basis_pinned _ ci lookup (by decide)).1
  rw [h]; rfl

theorem pinned_natSucc (strong : StrongInstalledModel V env) {ci : Kernel.ConstantInfo}
    (lookup : env.find? Kernel.natSuccName = some ci) : ci = Kernel.natSuccA := by
  have h := (strong.internal.base2.basis_pinned _ ci lookup (by decide)).1
  rw [h]; rfl

/-- A constant read at no universe arguments has one value at every assignment. -/
theorem cval_const_nil (strong : StrongInstalledModel V env) {n : Kernel.Name}
    {ci : Kernel.ConstantInfo} (lookup : env.find? n = some ci)
    (hlen : ([] : List Kernel.Level).length = ci.toConstantVal.levelParams.length)
    (first second : Kernel.Name → Nat) :
    strong.public.cval n first = strong.public.cval n second := by
  apply cvalLocal_of_strong strong n ci lookup
  intro p hp
  have : ci.toConstantVal.levelParams = [] := List.eq_nil_of_length_eq_zero hlen.symm
  rw [this] at hp; cases hp

theorem regime_never (ψ : Kernel.Name → Nat) : Kernel.regime ψ (Kernel.PropWhen.never) = 1 := by
  simp [Kernel.regime]

theorem regime_ifAllZero_u {ψ : Kernel.Name → Nat} (h : ψ Kernel.BasisDSL.uN = 0) :
    Kernel.regime ψ (Kernel.PropWhen.ifAllZero [Kernel.BasisDSL.uN]) = 0 := by
  simp [Kernel.regime, h]

/-- **Model-level induction on `Nat`** (R8): in every strong model of an environment holding
`Nat.rec`, a meta-level predicate true at `⟦Nat.zero⟧` and preserved by `⟦Nat.succ⟧` holds on all
of `⟦Nat⟧`. Read off `Nat.rec.{0}`'s installed type and its membership law; nothing else. -/
theorem nat_induction (strong : StrongInstalledModel V env) (φ : Kernel.Name → Nat)
    {ci : Kernel.ConstantInfo} (lookup : env.find? (Kernel.natName.str "rec") = some ci)
    (P : V → Prop)
    (hz : P (strong.public.cval Kernel.natZeroName φ))
    (hs : ∀ n, n ∈ˢ strong.public.cval Kernel.natName φ → P n →
      P (app (strong.public.cval Kernel.natSuccName φ) n)) :
    ∀ n, n ∈ˢ strong.public.cval Kernel.natName φ → P n := by
  intro n hn
  have pinned := pinned_natRec strong lookup
  subst pinned
  -- `Nat.rec.{0}`: the assignment sending its universe to `0`
  let ψ := Kernel.Level.substFn φ [Kernel.BasisDSL.uN] [.zero]
  have hψ : ψ Kernel.BasisDSL.uN = 0 := by simp [ψ, Kernel.Level.substFn, Kernel.Level.eval]
  have h0 := regime_ifAllZero_u hψ
  let ρ : Nat → V := fun _ => empty
  obtain ⟨T, hT, hmem⟩ := strong.public.mem Kernel.natRecA (Kernel.Semantics.Env.find?_mem lookup) ψ ρ
  rw [natRecA_type] at hT
  -- the motive binder
  obtain ⟨A₁, B₁, hA₁, hB₁, hP₁, rfl⟩ := denotes_pi_inv hT
  obtain ⟨N, Bs, hN, hBs, -, rfl⟩ := denotes_pi_inv hA₁
  obtain ⟨ciN, hfN, hlenN, rfl⟩ := denotes_const_inv hN
  have eN : ∀ ψ', strong.public.cval Kernel.natName ψ' = strong.public.cval Kernel.natName φ :=
    fun ψ' => cval_const_nil strong hfN hlenN ψ' φ
  have hBs' : ∀ x, x ∈ˢ strong.public.cval Kernel.natName
      (Kernel.Level.substFn ψ ciN.toConstantVal.levelParams []) → Bs x = univ 0 := by
    intro x hx; rw [denotes_sort_inv (hBs x hx)]; simp [Kernel.Level.eval, hψ]
  rw [regime_never] at *
  rw [eN] at hBs'
  -- Nat.zero and Nat.succ are installed, typed
  let M := predMotive (strong.public.cval Kernel.natName φ) P
  have hM : M ∈ˢ piR 1 (strong.public.cval Kernel.natName
      (Kernel.Level.substFn ψ ciN.toConstantVal.levelParams [])) Bs := by
    rw [eN]; exact predMotive_mem (strong.public.cval Kernel.natName φ) P hBs'
  rw [h0] at hmem hP₁
  obtain ⟨y₁, hy₁⟩ := inhabited_of_mem_piR hmem M hM
  -- the zero minor
  obtain ⟨A₂, B₂, hA₂, hB₂, hP₂, hB₁M⟩ := denotes_pi_inv (hB₁ M hM)
  rw [hB₁M, h0] at hy₁
  obtain ⟨F₂, Z, hF₂, hZ, rfl⟩ := denotes_app_inv hA₂
  rw [denotes_bvar_inv hF₂] at *
  obtain ⟨ciZ, hfZ, hlenZ, rfl⟩ := denotes_const_inv hZ
  have eZ : ∀ ψ', strong.public.cval Kernel.natZeroName ψ' =
      strong.public.cval Kernel.natZeroName φ := fun ψ' => cval_const_nil strong hfZ hlenZ ψ' φ
  have pZ := pinned_natZero strong hfZ
  subst pZ
  have hZN : strong.public.cval Kernel.natZeroName φ ∈ˢ (strong.public.cval Kernel.natName φ) := by
    obtain ⟨TZ, hTZ, hmZ⟩ := strong.public.mem Kernel.natZeroA (Kernel.Semantics.Env.find?_mem hfZ) φ ρ
    rw [natZeroA_type] at hTZ
    obtain ⟨ciN', hfN', hlenN', rfl⟩ := denotes_const_inv hTZ
    rw [cval_const_nil strong hfN' hlenN' _ φ] at hmZ
    exact hmZ
  rw [eZ] at hy₁
  have hzmem : (pt : V) ∈ˢ app (Kernel.push M ρ 0) (strong.public.cval Kernel.natZeroName φ) := by
    show (pt : V) ∈ˢ app M _
    rw [app_predMotive hZN]; exact pt_mem_truthVal hz
  obtain ⟨y₂, hy₂⟩ := inhabited_of_mem_piR hy₁ pt hzmem
  -- the successor minor
  obtain ⟨A₃, B₃, hA₃, hB₃, hP₃, hB₂z⟩ := denotes_pi_inv (hB₂ pt (by rw [eZ]; exact hzmem))
  rw [hB₂z, h0] at hy₂
  obtain ⟨N₃, B₃', hN₃, hB₃', -, rfl⟩ := denotes_pi_inv hA₃
  obtain ⟨ciN₃, hfN₃, hlenN₃, rfl⟩ := denotes_const_inv hN₃
  have eN₃ := cval_const_nil strong hfN₃ hlenN₃
    (Kernel.Level.substFn ψ ciN₃.toConstantVal.levelParams []) φ
  rw [eN₃] at hB₃' hy₂ hB₃
  rw [h0] at hy₂ hB₃
  have hsmem : ∃ s, s ∈ˢ piR 0 (strong.public.cval Kernel.natName φ) B₃' := by
    refine piR_inhabited fun k hk => ?_
    obtain ⟨Ak, Bk, hAk, hBk, -, hB₃k⟩ := denotes_pi_inv (hB₃' k hk)
    rw [hB₃k, h0]
    refine piR_inhabited fun h hh => ?_
    obtain ⟨Fk, Xk, hFk, hXk, rfl⟩ := denotes_app_inv hAk
    have hPk : P k := by
      have hh' := hh
      rw [denotes_bvar_inv hFk, denotes_bvar_inv hXk] at hh'
      change h ∈ˢ app M k at hh'
      rw [app_predMotive hk] at hh'
      exact of_mem_truthVal hh'
    obtain ⟨Fs, Xs, hFs, hXs, hBkh⟩ := denotes_app_inv (hBk h hh)
    rw [denotes_bvar_inv hFs] at hBkh
    obtain ⟨Fsc, Xk', hFsc, hXk', rfl⟩ := denotes_app_inv hXs
    rw [denotes_bvar_inv hXk'] at hBkh
    obtain ⟨ciS, hfS, hlenS, rfl⟩ := denotes_const_inv hFsc
    have pS := pinned_natSucc strong hfS
    subst pS
    rw [cval_const_nil strong hfS hlenS _ φ] at hBkh
    -- ⟦Nat.succ⟧ maps ⟦Nat⟧ into ⟦Nat⟧
    have hSk : app (strong.public.cval Kernel.natSuccName φ) k ∈ˢ (strong.public.cval Kernel.natName φ) := by
      obtain ⟨TS, hTS, hmS⟩ := strong.public.mem Kernel.natSuccA
        (Kernel.Semantics.Env.find?_mem hfS) φ ρ
      rw [natSuccA_type] at hTS
      obtain ⟨AS, BS, hAS, hBS, -, rfl⟩ := denotes_pi_inv hTS
      obtain ⟨ciA, hfA, hlenA, rfl⟩ := denotes_const_inv hAS
      rw [regime_never, cval_const_nil strong hfA hlenA _ φ] at hmS
      rw [cval_const_nil strong hfA hlenA _ φ] at hBS
      have hk' := app_mem_piR_pos (by decide) hmS hk
      obtain ⟨ciB, hfB, hlenB, hBk'⟩ := denotes_const_inv (hBS k hk)
      rw [hBk', cval_const_nil strong hfB hlenB _ φ] at hk'
      exact hk'
    refine ⟨pt, ?_⟩
    rw [hBkh]
    change (pt : V) ∈ˢ app M (app (strong.public.cval Kernel.natSuccName φ) k)
    rw [app_predMotive hSk]
    exact pt_mem_truthVal (hs k hk hPk)
  obtain ⟨s, hs₀⟩ := hsmem
  obtain ⟨y₃, hy₃⟩ := inhabited_of_mem_piR hy₂ s hs₀
  -- the conclusion's fibre
  obtain ⟨N₄, Bt, hN₄, hBt, -, hB₃s⟩ := denotes_pi_inv (hB₃ s hs₀)
  rw [hB₃s, h0] at hy₃
  obtain ⟨ciN₄, hfN₄, hlenN₄, rfl⟩ := denotes_const_inv hN₄
  rw [cval_const_nil strong hfN₄ hlenN₄ _ φ] at hy₃ hBt
  obtain ⟨y₄, hy₄⟩ := inhabited_of_mem_piR hy₃ n hn
  obtain ⟨Fn, Xn, hFn, hXn, hBtn⟩ := denotes_app_inv (hBt n hn)
  rw [hBtn, denotes_bvar_inv hFn, denotes_bvar_inv hXn] at hy₄
  change y₄ ∈ˢ app M n at hy₄
  rw [app_predMotive hn] at hy₄
  exact of_mem_truthVal hy₄

end Nat

end Ix.CompileCert.Bridge
