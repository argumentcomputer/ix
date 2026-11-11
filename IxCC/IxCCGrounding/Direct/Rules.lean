import IxCCGrounding.Direct.Eq
import IxCCGrounding.Direct.Subst
import IxCCGrounding.Runs
import IxCCGrounding.Case

/-!
# The typing rules and reductions the direct route uses (`IxCCGrounding.Direct.Rules`)

**Parts D and E.** The judgements the checker's soundness is stated in (`HasTy`, `ChecksAt`,
`DenEq`, `Reduces`, `FitsAt`, each quantifying over the environments that satisfy the context
and saying nothing where a term does not denote), and one lemma per rule the checker applies:

* typing: a variable by its context type, a constant by its stored type (`Model.mem`, at the
  assignment its levels induce, then `den_inst`), an application by the codomain at the argument
  (`app_mem_den_pi`, `den_inst1Lift`), a literal, a sort, a `∀` by the `imax` rule (the product
  lemma, copied below from the kernel's `Semantics/Univ.lean`, which is outside the closure this
  library imports), a λ whose datum does not hold by its own `∀` (`lamR_mem`);
* reductions, forward ("where the redex denotes, the reduct denotes the same"): β with the
  argument in the domain (`app_den_lam`, `den_inst1Lift`), δ (`Laws.defn_value`; in a
  proof-irrelevant set model a definition's set is its value's), the projection of a constructor
  (`Laws.proj_ctor`, at a structure that is never a proposition: in a proof-irrelevant set model its
  constructor is read in the graph regime and its image is the field tuple);
* conversion: equal denotations through reductions, binders and spines.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

theorem mkAppN_append : ∀ (args : List KExpr) (f a : KExpr),
    Expr.mkAppN f (args ++ [a]) = .app (Expr.mkAppN f args) a
  | [], _, _ => rfl
  | b :: args, f, a => mkAppN_append args (.app f b) a

theorem mkAppN_getApp : ∀ e : KExpr, Expr.mkAppN e.getAppFn e.getAppArgs = e
  | .app f a => by
    simp only [Expr.getAppFn, Expr.getAppArgs]
    rw [mkAppN_append, mkAppN_getApp f]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => rfl

/-- **The product in a universe: the `imax` rule** (copied from the kernel's
`IxCK/Kernel/Semantics/Univ.lean`, `piR_mem_univ`, outside the closure this library imports). -/
theorem piR_mem_univ' {V : Type w} [Ix.Kernel.SetTheory V] {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    piR v A B ∈ˢ (univ (if v = 0 then 0 else Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp only [↓reduceIte, univ_zero]
    exact piR_zero_mem_univZero
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    have hw : (Nat.max u v : Nat) ≠ 0 :=
      fun h => hv' (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))
    simp only [hv', ↓reduceIte]
    rw [piR_pos hv']
    exact (univ_isTGUniverse hw).piSet_mem
      (univ_mono (Nat.le_max_left u v) A hA)
      (fun x hx => univ_mono (Nat.le_max_right u v) _ (hB x hx))

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}
  {φ : LevelParam → Nat}

/-! ## The judgements -/

/-- **`e` has type `T`** in `Γ` at `φ`: wherever `Γ` is satisfied and `e` denotes, `T` denotes a
set holding it. -/
def HasTy (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (e T : KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∀ X, Denotes M.cval env φ ρ e X →
    ∃ Y, Denotes M.cval env φ ρ T Y ∧ X ∈ˢ Y

/-- **`a` checks against `A`**: wherever both denote, `a`'s denotation is a member of `A`'s. -/
def ChecksAt (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (a A : KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∀ X Y, Denotes M.cval env φ ρ a X → Denotes M.cval env φ ρ A Y →
    X ∈ˢ Y

/-- **`T` and `A` denote alike**: wherever both denote, the same set. -/
def DenEq (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (T A : KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∀ Y Y', Denotes M.cval env φ ρ T Y → Denotes M.cval env φ ρ A Y' →
    Y = Y'

/-- **`e` reduces to `e'`**: wherever `Γ` is satisfied and `e` denotes, `e'` denotes the same. -/
def Reduces (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (e e' : KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∀ Y, Denotes M.cval env φ ρ e Y → Denotes M.cval env φ ρ e' Y

/-- **`as` fit `T`** (as `Fits` reads it, syntactically): wherever `Γ` is satisfied, `T` denotes
and the arguments denote. -/
def FitsAt (M : Model V env) (φ : LevelParam → Nat) (Γ : List KExpr) (T : KExpr)
    (as : List KExpr) : Prop :=
  ∀ ρ, CtxSat M φ Γ ρ → ∀ TT Xs, Denotes M.cval env φ ρ T TT →
    DenotesList M.cval env φ ρ as Xs → ∃ σ R, Fits M.cval env φ ρ T Xs σ R

/-! ## Contexts and spines -/

theorem ctxSat_get : ∀ {Γ : List KExpr} {ρ : BVarIdx → V} {i : Nat} {A : KExpr},
    CtxSat M φ Γ ρ → Γ[i]? = some A →
      ∃ X, Denotes M.cval env φ (fun j => ρ (j + (i + 1))) A X ∧ ρ i ∈ˢ X
  | [], _, _, _, _, h => by simp at h
  | _ :: _, ρ, 0, A, hs, h => by
    cases hs with
    | cons _ hA hx =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, hA, hx⟩
  | _ :: _, ρ, i + 1, A, hs, h => by
    cases hs with
    | cons hΓ _ _ =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨X, hX, hm⟩ := ctxSat_get hΓ h
      exact ⟨X, hX, hm⟩

theorem ctxSat_push {Γ : List KExpr} {ρ : BVarIdx → V} {A : KExpr} {X x : V}
    (hρ : CtxSat M φ Γ ρ) (hA : Denotes M.cval env φ ρ A X) (hx : x ∈ˢ X) :
    CtxSat M φ (A :: Γ) (push x ρ) :=
  .cons (by rw [push_tail]; exact hρ) (by rw [push_tail]; exact hA) hx

theorem denotesIn_mkAppN_head {Γ : List KExpr} :
    ∀ (args : List KExpr) {h : KExpr}, DenotesIn M φ Γ (Expr.mkAppN h args) → DenotesIn M φ Γ h
  | [], _, hd => hd
  | _ :: args, _, hd => denotesIn_app_left (denotesIn_mkAppN_head args hd)

/-! ## Typing -/

theorem hasTy_of_reduces {Γ : List KExpr} {e T T' : KExpr} (h : HasTy M φ Γ e T)
    (hr : Reduces M φ Γ T T') : HasTy M φ Γ e T' := fun ρ hρ X hX => by
  obtain ⟨Y, hY, hm⟩ := h ρ hρ X hX
  exact ⟨Y, hr ρ hρ Y hY, hm⟩

theorem hasTy_of_reduct {Γ : List KExpr} {e e' T : KExpr} (h : HasTy M φ Γ e' T)
    (hr : Reduces M φ Γ e e') : HasTy M φ Γ e T := fun ρ hρ X hX =>
  h ρ hρ X (hr ρ hρ X hX)

theorem hasTy_bvar {Γ : List KExpr} {i : Nat} {A : KExpr} (h : Γ[i]? = some A) :
    HasTy M φ Γ (.bvar i) (A.liftLooseBVars (i + 1) 0) := by
  intro ρ hρ X hX
  rw [den_bvar] at hX
  subst hX
  obtain ⟨Y, hY, hm⟩ := ctxSat_get hρ h
  refine ⟨Y, (den_lift (i + 1) A 0 ρ Y).mpr ?_, hm⟩
  rw [skipEnv_zero]
  exact hY

theorem hasTy_const (hL : Laws M) {Γ : List KExpr} {k : KKey} {us : List Level}
    {ci : ConstantInfo .anon} (hf : env.find? k = some ci)
    (hd : ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true) :
    HasTy M φ Γ (.const k us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  intro ρ _ X hX
  cases hX with
  | const hf' _ =>
    rw [hf] at hf'
    cases hf'
    obtain ⟨T, hT, hm⟩ := mem_key M hf (Level.substFn φ ci.toConstantVal.levelParams us) ρ
    exact ⟨T, den_inst M hL (fun _ _ => rfl) hT hd, hm⟩

theorem hasTy_sort {Γ : List KExpr} {u : Level} :
    HasTy M φ Γ (.sort u) (.sort (.succ u)) := by
  intro ρ _ X hX
  rw [den_sort] at hX
  subst hX
  exact ⟨_, .sort, by simpa [Level.eval] using univ_mem_univ (V := V) (Level.eval φ u)⟩

theorem hasTy_lit (hN : NatBasis env) {Γ : List KExpr} {n : Nat} :
    HasTy M φ Γ (.lit (.natVal n)) (.const natName []) := by
  intro ρ _ X hX
  have hF := natFacts M hN φ
  have hX' := (lit_den M hF ρ n X).mp hX
  subst hX'
  exact ⟨_, (hF.natD ρ _).mpr rfl, lit_mem M hF n⟩

/-- **Application**: the codomain at the argument. -/
theorem hasTy_app {Γ : List KExpr} {F a A B : KExpr} {m : BinderMeta}
    (hF : HasTy M φ Γ F (.forallE A B m)) (ha : ChecksAt M φ Γ a A) :
    HasTy M φ Γ (.app F a) (B.instantiate1Lift a 0) := by
  intro ρ hρ X hX
  obtain ⟨Fv, Xa, hFv, hXa, rfl⟩ := den_app.mp hX
  obtain ⟨Y, hY, hm⟩ := hF ρ hρ Fv hFv
  obtain ⟨Ad, Bf, hAd, _, _, rfl⟩ := den_pi.mp hY
  have hxa := ha ρ hρ Xa Ad hXa hAd
  obtain ⟨Bx, hBx, hmem⟩ := app_mem_den_pi hY hAd hm hxa
  exact ⟨Bx, (den_inst1Lift0 hXa B Bx).mpr hBx, hmem⟩

/-- **A site in the graph regime**, from the function's `∀` type. -/
theorem siteOk_of_pi {Γ : List KExpr} {F a A B : KExpr} {m : BinderMeta}
    (hF : HasTy M φ Γ F (.forallE A B m)) (ha : ChecksAt M φ Γ a A) (hreg : regime φ m.pw ≠ 0)
    (hD : DenotesIn M φ Γ (.app F a)) : SiteOk M φ Γ F a := by
  intro ρ hρ
  obtain ⟨X, hX⟩ := hD ρ hρ
  obtain ⟨Fv, Xa, hFv, hXa, _⟩ := den_app.mp hX
  obtain ⟨Y, hY, hm⟩ := hF ρ hρ Fv hFv
  obtain ⟨Ad, Bf, hAd, _, _, rfl⟩ := den_pi.mp hY
  exact ⟨Fv, Xa, regime φ m.pw, Ad, Bf, hFv, hXa, hreg, hm, ha ρ hρ Xa Ad hXa hAd⟩

/-- **A site whose function is a λ in the graph regime**, its argument in the λ's domain. -/
theorem siteOk_of_lam {Γ : List KExpr} {D b a : KExpr} {m : BinderMeta}
    (ha : ChecksAt M φ Γ a D) (hreg : regime φ m.pw ≠ 0)
    (hD : DenotesIn M φ Γ (.app (.lam D b m) a)) : SiteOk M φ Γ (.lam D b m) a := by
  intro ρ hρ
  obtain ⟨X, hX⟩ := hD ρ hρ
  obtain ⟨L, Xa, hL', hXa, _⟩ := den_app.mp hX
  obtain ⟨Ad, F, hAd, _, _, rfl⟩ := den_lam.mp hL'
  exact ⟨_, Xa, regime φ m.pw, Ad, fun x => sing (F x), hL', hXa, hreg,
    lamR_mem fun _ _ => mem_sing.mpr rfl, ha ρ hρ Xa Ad hXa hAd⟩

/-- **A λ whose datum does not hold has its own `∀` as a type** (`lamR_mem`, the fibres chosen). -/
theorem hasTy_lam {Γ : List KExpr} {D b T : KExpr} {m : BinderMeta} (hreg : regime φ m.pw ≠ 0)
    (hb : HasTy M φ (D :: Γ) b T) : HasTy M φ Γ (.lam D b m) (.forallE D T m) := by
  intro ρ hρ X hX
  obtain ⟨Ad, F, hAd, hF, _, rfl⟩ := den_lam.mp hX
  have hfib : ∀ x, x ∈ˢ Ad → ∃ Y, Denotes M.cval env φ (push x ρ) T Y ∧ F x ∈ˢ Y :=
    fun x hx => hb (push x ρ) (ctxSat_push hρ hAd hx) (F x) (hF x hx)
  classical
  let Bf : V → V := fun x => if h : x ∈ˢ Ad then Classical.choose (hfib x h) else empty
  have hBf : ∀ x (hx : x ∈ˢ Ad), Bf x = Classical.choose (hfib x hx) := fun x hx => by simp only [Bf, hx, ↓reduceDIte]
  refine ⟨piR (regime φ m.pw) Ad Bf, .pi hAd (fun x hx => ?_) (fun h0 => absurd h0 hreg), ?_⟩
  · rw [hBf x hx]; exact (Classical.choose_spec (hfib x hx)).1
  · exact lamR_mem fun x hx => by rw [hBf x hx]; exact (Classical.choose_spec (hfib x hx)).2

/-- **A `∀` by the `imax` rule**, its datum its codomain sort's zero condition. -/
theorem hasTy_pi {Γ : List KExpr} {A B : KExpr} {m : BinderMeta} {u v : Level}
    (hA : HasTy M φ Γ A (.sort u)) (hB : HasTy M φ (A :: Γ) B (.sort v))
    (hz : m.pw.holds φ = (Level.eval φ v == 0)) :
    HasTy M φ Γ (.forallE A B m) (.sort (.imax u v)) := by
  intro ρ hρ X hX
  obtain ⟨Ad, Bf, hAd, hBf, _, rfl⟩ := den_pi.mp hX
  obtain ⟨U, hU, hAU⟩ := hA ρ hρ Ad hAd
  rw [den_sort] at hU
  subst hU
  have hBm : ∀ x, x ∈ˢ Ad → Bf x ∈ˢ (univ (Level.eval φ v) : V) := fun x hx => by
    obtain ⟨W, hW, hm⟩ := hB (push x ρ) (ctxSat_push hρ hAd hx) (Bf x) (hBf x hx)
    rw [den_sort] at hW
    rwa [hW] at hm
  refine ⟨_, .sort, ?_⟩
  have hr : piR (regime φ m.pw) Ad Bf = piR (Level.eval φ v) Ad Bf :=
    piR_zero_agree (by simp [regime, hz]) fun _ _ => rfl
  rw [hr]
  have := piR_mem_univ' hAU hBm
  simpa [Level.eval] using this

/-! ## Reductions -/

theorem reduces_refl {Γ : List KExpr} {e : KExpr} : Reduces M φ Γ e e := fun _ _ _ h => h

theorem reduces_trans {Γ : List KExpr} {e e' e'' : KExpr} (h1 : Reduces M φ Γ e e')
    (h2 : Reduces M φ Γ e' e'') : Reduces M φ Γ e e'' := fun ρ hρ Y h => h2 ρ hρ Y (h1 ρ hρ Y h)

/-- **β**, the argument in the λ's domain. -/
theorem reduces_beta {Γ : List KExpr} {D b a1 : KExpr} {m : BinderMeta} (rest : List KExpr)
    (ha : ChecksAt M φ Γ a1 D) :
    Reduces M φ Γ (Expr.mkAppN (.lam D b m) (a1 :: rest))
      (Expr.mkAppN (b.instantiate1Lift a1 0) rest) := by
  intro ρ hρ Y hY
  obtain ⟨F, Ys, hF, hYs, rfl⟩ := (den_mkAppN rest).mp hY
  obtain ⟨L, X1, hL', hX1, rfl⟩ := den_app.mp hF
  obtain ⟨Ad, Fb, hAd, _, _, rfl⟩ := den_lam.mp hL'
  obtain ⟨Z, hZ, hz⟩ := app_den_lam hL' hAd (ha ρ hρ X1 Ad hX1 hAd)
  rw [hz]
  exact (den_mkAppN rest).mpr ⟨Z, Ys, (den_inst1Lift0 hX1 b Z).mpr hZ, hYs, rfl⟩

/-- **δ** (`Laws.defn_value`, through `den_inst` for the levels). -/
theorem reduces_delta (hL : Laws M) {Γ : List KExpr} {k : KKey} {us : List Level}
    {cv : ConstantVal .anon} {val : KExpr} {hint : ReducibilityHint}
    (hf : env.find? k = some (.defnInfo cv val hint)) (hd : val.allLevelParamsDefined cv.levelParams = true)
    (args : List KExpr) :
    Reduces M φ Γ (Expr.mkAppN (.const k us) args)
      (Expr.mkAppN (val.instantiateLevelParams cv.levelParams us) args) := by
  intro ρ _ Y hY
  obtain ⟨K, Ys, hK, hYs, rfl⟩ := (den_mkAppN args).mp hY
  cases hK with
  | const hf' _ =>
    rw [hf] at hf'
    cases hf'
    -- δ in a proof-irrelevant set model: a definition's set is its value's
    have hv := hL.defn_value cv val hint (find_mem hf) (Level.substFn φ cv.levelParams us) ρ
    have hname : cv.name = k := by
      have := find_name hf
      simpa [ConstantInfo.toConstantVal] using this
    rw [hname] at hv
    exact (den_mkAppN args).mpr ⟨_, Ys, den_inst M hL (fun _ _ => rfl) hv hd, hYs, rfl⟩

/-! ## Checking and conversion -/

theorem checks_of_hasTy {Γ : List KExpr} {a T A : KExpr} (h : HasTy M φ Γ a T)
    (hc : DenEq M φ Γ T A) : ChecksAt M φ Γ a A := fun ρ hρ X Y hX hY => by
  obtain ⟨Y', hY', hm⟩ := h ρ hρ X hX
  rwa [hc ρ hρ Y' Y hY' hY] at hm

/-- **A λ against a `∀`**: domains alike, data alike, the body against the codomain. -/
theorem checks_lam {Γ : List KExpr} {A1 b A A2 B2 : KExpr} {m1 m2 : BinderMeta}
    (hr : Reduces M φ Γ A (.forallE A2 B2 m2)) (hd : DenEq M φ Γ A1 A2)
    (hm : regime φ m1.pw = regime φ m2.pw) (hb : ChecksAt M φ (A1 :: Γ) b B2) :
    ChecksAt M φ Γ (.lam A1 b m1) A := by
  intro ρ hρ X Y hX hY
  obtain ⟨Ad, F, hAd, hF, _, rfl⟩ := den_lam.mp hX
  obtain ⟨Ad2, Bf, hAd2, hBf, _, hYe⟩ := den_pi.mp (hr ρ hρ Y hY)
  obtain rfl := hd ρ hρ Ad Ad2 hAd hAd2
  rw [hYe, hm]
  exact lamR_mem fun x hx =>
    hb (push x ρ) (ctxSat_push hρ hAd hx) (F x) (Bf x) (hF x hx) (hBf x hx)

theorem denEq_refl_syn {Γ : List KExpr} {T : KExpr} : DenEq M φ Γ T T :=
  fun _ _ _ _ h h' => Denotes_functional h h'

theorem denEq_of_reduces {Γ : List KExpr} {T A T' A' : KExpr} (hT : Reduces M φ Γ T T')
    (hA : Reduces M φ Γ A A') (h : DenEq M φ Γ T' A') : DenEq M φ Γ T A :=
  fun ρ hρ Y Y' hY hY' => h ρ hρ Y Y' (hT ρ hρ Y hY) (hA ρ hρ Y' hY')

theorem denEq_pi {Γ : List KExpr} {d b d' b' : KExpr} {m m' : BinderMeta}
    (hm : regime φ m.pw = regime φ m'.pw) (hd : DenEq M φ Γ d d') (hb : DenEq M φ (d :: Γ) b b') :
    DenEq M φ Γ (.forallE d b m) (.forallE d' b' m') := by
  intro ρ hρ Y Y' hY hY'
  obtain ⟨Ad, Bf, hAd, hBf, _, rfl⟩ := den_pi.mp hY
  obtain ⟨Ad', Bf', hAd', hBf', _, rfl⟩ := den_pi.mp hY'
  obtain rfl := hd ρ hρ Ad Ad' hAd hAd'
  rw [hm]
  exact piR_congr fun x hx =>
    hb (push x ρ) (ctxSat_push hρ hAd hx) (Bf x) (Bf' x) (hBf x hx) (hBf' x hx)

theorem denEq_lam {Γ : List KExpr} {d b d' b' : KExpr} {m m' : BinderMeta}
    (hm : regime φ m.pw = regime φ m'.pw) (hd : DenEq M φ Γ d d') (hb : DenEq M φ (d :: Γ) b b') :
    DenEq M φ Γ (.lam d b m) (.lam d' b' m') := by
  intro ρ hρ Y Y' hY hY'
  obtain ⟨Ad, F, hAd, hF, _, rfl⟩ := den_lam.mp hY
  obtain ⟨Ad', F', hAd', hF', _, rfl⟩ := den_lam.mp hY'
  obtain rfl := hd ρ hρ Ad Ad' hAd hAd'
  rw [hm]
  exact lamR_congr fun x hx =>
    hb (push x ρ) (ctxSat_push hρ hAd hx) (F x) (F' x) (hF x hx) (hF' x hx)

theorem denEq_natLit_left {Γ : List KExpr} {k : Nat} {e : KExpr}
    (h : DenEq M φ Γ (natLitToConstructor k) e) : DenEq M φ Γ (.lit (.natVal k)) e :=
  fun ρ hρ Y Y' hY hY' => h ρ hρ Y Y' (den_natLit.mp hY) hY'

theorem denEq_natLit_right {Γ : List KExpr} {k : Nat} {e : KExpr}
    (h : DenEq M φ Γ e (natLitToConstructor k)) : DenEq M φ Γ e (.lit (.natVal k)) :=
  fun ρ hρ Y Y' hY hY' => h ρ hρ Y Y' hY (den_natLit.mp hY')

/-- Two spines with heads alike and arguments pairwise alike. -/
theorem denEq_spine {Γ : List KExpr} {T A : KExpr} (hh : DenEq M φ Γ T.getAppFn A.getAppFn)
    (ha : ∀ ρ, CtxSat M φ Γ ρ → ∀ Ys Ys', DenotesList M.cval env φ ρ T.getAppArgs Ys →
      DenotesList M.cval env φ ρ A.getAppArgs Ys' → Ys = Ys') : DenEq M φ Γ T A := by
  intro ρ hρ Y Y' hY hY'
  rw [← mkAppN_getApp T] at hY
  rw [← mkAppN_getApp A] at hY'
  obtain ⟨F, Ys, hF, hYs, rfl⟩ := (den_mkAppN _).mp hY
  obtain ⟨F', Ys', hF', hYs', rfl⟩ := (den_mkAppN _).mp hY'
  rw [hh ρ hρ F F' hF hF', ha ρ hρ Ys Ys' hYs hYs']

/-! ## Fitting a telescope -/

theorem fitsAt_nil {Γ : List KExpr} {T : KExpr} : FitsAt M φ Γ T [] :=
  fun ρ _ _ Xs _ hXs => by cases hXs; exact ⟨ρ, T, .nil⟩

theorem fitsAt_cons {Γ : List KExpr} {A B a : KExpr} {m : BinderMeta} {as : List KExpr}
    (hk : as.length ≤ kPis B) (ha : ChecksAt M φ Γ a A)
    (hrest : FitsAt M φ Γ (B.instantiate1Lift a 0) as) :
    FitsAt M φ Γ (.forallE A B m) (a :: as) := by
  intro ρ hρ TT Xs hT hXs
  cases hXs with
  | @cons _ _ X Xs' hX hXs' =>
    obtain ⟨Ad, Bf, hAd, hBf, _, _⟩ := den_pi.mp hT
    have hx := ha ρ hρ X Ad hX hAd
    have hB := (den_inst1Lift0 hX B (Bf X)).mpr (hBf X hx)
    obtain ⟨σ, R, hf⟩ := hrest ρ hρ _ Xs' hB hXs'
    have hf' : Fits M.cval env φ (pushAll [] ρ) (B.instantiate1Lift a ([] : List V).length) Xs' σ R := by
      simpa [pushAll_nil] using hf
    obtain ⟨σ', R', hf''⟩ := fits_inst1Lift hX Xs' B [] σ R
      (by rw [denotesList_length hXs']; exact hk) hf'
    rw [pushAll_nil] at hf''
    exact ⟨σ', R', .cons hAd hx hf''⟩


theorem ctorApp?_spec {env' : KEnv} {e : KExpr} {ck : KKey} {cus : List Level} {np nf : Nat}
    {cargs : List KExpr} (h : ctorApp? env' e = some (ck, cus, np, nf, cargs)) :
    e.getAppFn = .const ck cus ∧ (∃ cv, env'.find? ck = some (.ctorInfo cv np nf)) ∧
      e.getAppArgs = cargs := by
  unfold ctorApp? at h
  split at h
  · rename_i k us hfn
    split at h
    · rename_i cv np' nf' hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨hfn, ⟨cv, hf⟩, rfl⟩
    · cases h
  · cases h

/-- **The projection of a constructor**, forward: at a structure that is never a proposition
(`proj_ctor`; in a proof-irrelevant set model its constructor is read in the graph regime and its
image is the field tuple, read at position `i + off`). -/
theorem reduces_proj (hL : Laws M) {Γ : List KExpr} {s : KKey} {i : Nat} {p p' fi : KExpr}
    (args : List KExpr) {ck : KKey} {cus : List Level} {np nf : Nat} {cargs : List KExpr}
    {entry : ProjEntry .anon} {cvC : ConstantVal .anon}
    (hp : Reduces M φ Γ p p') (hfn : p'.getAppFn = .const ck cus) (hargs : p'.getAppArgs = cargs)
    (hck : env.find? ck = some (.ctorInfo cvC np nf))
    (hent : env.findProj? s i = some entry) (hctor : entry.ctor = ck)
    (hns : NeverProp env s) (hlen : cargs.length = np + nf)
    (hdef : cvC.type.allLevelParamsDefined cvC.levelParams = true)
    (hfits : FitsAt M φ Γ (cvC.type.instantiateLevelParams cvC.levelParams cus) cargs)
    (hfi : cargs[np + i]? = some fi) :
    Reduces M φ Γ (Expr.mkAppN (.proj s i p) args) (Expr.mkAppN fi args) := by
  intro ρ hρ Y hY
  obtain ⟨Pr, As, hPr, hAs, rfl⟩ := (den_mkAppN args).mp hY
  have hP : ∃ P, Denotes M.cval env φ ρ p P ∧ Pr = field (i + entry.off) P := by
    cases hPr with
    | proj_table ht he => rw [hent] at ht; cases ht; exact ⟨_, he, rfl⟩
    | proj_fst ht _ => rw [hent] at ht; cases ht
    | proj_snd ht _ => rw [hent] at ht; cases ht
  obtain ⟨P, hPd, rfl⟩ := hP
  have hP' := hp ρ hρ P hPd
  rw [← mkAppN_getApp p', hfn, hargs] at hP'
  obtain ⟨K, Cs, hK, hCs, rfl⟩ := (den_mkAppN cargs).mp hP'
  cases hK with
  | const hf' _ =>
    rw [hck] at hf'
    cases hf'
    simp only [ConstantInfo.toConstantVal]
    obtain ⟨TT, hTT, _⟩ := mem_key M hck (Level.substFn φ cvC.levelParams cus) ρ
    simp only [ConstantInfo.toConstantVal] at hTT
    have hTi := den_inst M hL (fun _ _ => rfl) hTT hdef
    obtain ⟨σ, R, hfit⟩ := hfits ρ hρ _ Cs hTi hCs
    obtain ⟨σ', R', hfit'⟩ := fits_uninst M hL (fun _ _ => rfl) Cs cvC.type ρ σ R TT hdef hTT hfit
    have hCl : Cs.length = np + nf := by rw [denotesList_length hCs, hlen]
    obtain ⟨Z, hZ, hfiZ⟩ := denotesList_get hCs hfi
    have hFi : (Cs.drop np)[i]? = some Z := by rw [List.getElem?_drop]; exact hZ
    obtain ⟨cvT, caps, sT, hfT, hsT, hnv⟩ := hns
    have hpc := hL.proj_ctor s i entry cvC np nf cvT caps sT
      (Level.substFn φ cvC.levelParams cus) ρ σ' R' (Cs.take np) (Cs.drop np) Z hent
      (by rw [hctor]; exact hck) hfT hsT (eval_ne_zero_of_never hnv _) (by simp [hCl])
      (by simp [hCl]) (by rw [List.take_append_drop]; exact hfit') hFi
    rw [List.take_append_drop, hctor] at hpc
    rw [hpc]
    exact (den_mkAppN args).mpr ⟨Z, As, hfiZ, hAs, rfl⟩

end Sem

end IxCC.Grounding
