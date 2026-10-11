import Ix.CompileCert.Conv.Total

/-!
# M7 X1: the termination proof

`develop_total`: on simply typed input, `hinstP` and `happP` succeed from some fuel on, with a
result of the input's type (`Total.lean` explains the statement). Induction on the size of the
substituted value's type; inside, on the size of the term.
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created projCtor?)

/-! ## Typing facts -/

theorem pairName_ctorKind {s c : Name} (h : pairName s c = true) : ∃ k, ctorKind c = some k := by
  unfold pairName at h
  unfold ctorKind
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  by_cases h1 : (c == Ix.Compile.Image.nPProdMk) = true
  · exact ⟨true, by simp [h1]⟩
  · rcases h with h | h
    · exact absurd h.2 h1
    · exact ⟨false, by simp [h1, h.2]⟩

theorem pairName_pairKind {s c : Name} (h : pairName s c = true) : ∃ k, pairKind s = some k := by
  unfold pairName at h
  unfold pairKind
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  by_cases h1 : (s == Ix.Compile.Image.nPProd) = true
  · exact ⟨true, by simp [h1]⟩
  · rcases h with h | h
    · exact absurd h.1 h1
    · exact ⟨false, by simp [h1, h.1]⟩

theorem typ_const_pair {Γ : List Ty} {c : Name} {us : Array Level} {T : Ty}
    (hp : ∃ k, ctorKind c = some k) (ht : Typ Γ (.const c us) T) :
    ∃ α β a b k, T = .arr α (.arr β (.arr a (.arr b (Ty.pair k a b)))) := by
  cases ht with
  | const _ _ hk => obtain ⟨k, hk'⟩ := hp; rw [hk] at hk'; cases hk'
  | pairMk _ α β a b hk => exact ⟨α, β, a, b, _, rfl⟩

theorem Ty.arr_inj {a b a' b' : Ty} (h : Ty.arr a b = Ty.arr a' b') : a = a' ∧ b = b' := by
  cases h; exact ⟨rfl, rfl⟩

/-- A pair constructor applied to four arguments, typed as a pair: the fields have the
component types. -/
theorem typ_pair4 {Γ : List Ty} {s c : Name} {us : Array Level} {α β a b : Tm} {k : Bool}
    {A B : Ty} (hp : pairName s c = true) (ht : Typ Γ (pair4 c us α β a b) (Ty.pair k A B)) :
    Typ Γ a A ∧ Typ Γ b B := by
  obtain ⟨σs, hc, hargs⟩ := Typ.appN_iff.1 ht
  obtain ⟨α', β', a', b', k', he⟩ := typ_const_pair (pairName_ctorKind hp) hc
  cases hargs with
  | cons h1 h2 => cases h2 with
    | cons h3 h4 => cases h4 with
      | cons h5 h6 => cases h6 with
        | cons h7 h8 => cases h8 with
          | nil =>
            simp only [Ty.arrows, Ty.arr.injEq] at he
            obtain ⟨-, -, rfl, rfl, hpair⟩ := he
            obtain ⟨-, rfl, rfl⟩ := Ty.pair_inj hpair
            exact ⟨h5, h7⟩

/-- Inverting the typing of a λ. -/
theorem typ_lam_inv {Γ : List Ty} {t b : Tm} {τ : Ty} (h : Typ Γ (.lam t b) τ) :
    ∃ ρ σx τb, τ = .arr σx τb ∧ Typ Γ t ρ ∧ Typ (σx :: Γ) b τb := by
  cases h with
  | lam ht hb => exact ⟨_, _, _, rfl, ht, hb⟩

/-! ## The arguments of a spine -/

/-- Arguments each developed from some fuel on, with their types. -/
theorem args_total {v : Expr} {k : Nat} {Γ₁ Γ₂ : List Ty} :
    ∀ (l : List Expr) (ρs : List Ty),
    (∀ a ∈ l, ∀ ρ, Typ Γ₁ (er a) ρ →
      ∃ N r c, (∀ m, N ≤ m → hinstP m v k a = .ok (r, c)) ∧ Typ Γ₂ (er r) ρ) →
    TypArgs Γ₁ (l.map er) ρs →
    ∃ N rs, (∀ m, N ≤ m → l.mapM (fun a => Prod.fst <$> hinstP m v k a) = .ok rs) ∧
      TypArgs Γ₂ (rs.map er) ρs
  | [], ρs, _, h => by
    cases h
    exact ⟨0, [], fun m _ => rfl, .nil⟩
  | a :: l, ρs, H, h => by
    cases h with
    | cons ha hl =>
      obtain ⟨N1, r, c, h1, t1⟩ := H a (List.mem_cons_self) _ ha
      obtain ⟨N2, rs, h2, t2⟩ := args_total l _ (fun x hx => H x (List.mem_cons_of_mem _ hx)) hl
      refine ⟨max N1 N2, r :: rs, fun m hm => ?_, .cons t1 t2⟩
      simp only [List.mapM_cons]
      rw [h1 m (by omega), h2 m (by omega)]
      rfl

/-! ## Hereditary steps at smaller types -/

/-- `hinstP` succeeds on every typed input with the substituted value at type `σ`. -/
def HinstTotalAt (σ : Ty) : Prop :=
  ∀ (e v : Expr) (Θ Δ : List Ty) (τ : Ty), Typ Δ (er v) σ → Typ (Θ ++ σ :: Δ) (er e) τ →
    HinstOk v σ Θ Δ e τ

theorem mkAppN_toList (f : Expr) (l : List Expr) : er (mkAppN f l.toArray) = Tm.appN (er f) (l.map er) := by
  rw [er_mkAppN, List.toList_toArray]

theorem happP_succ_nonlam (m : Nat) (f a : Expr) (rest : List Expr)
    (hl : ∀ n t b bi hh, f ≠ Expr.lam n t b bi hh) :
    happP (m + 1) f (a :: rest) = .ok (mkAppN f (a :: rest).toArray) := by
  rw [happP_succ]
  cases f with
  | lam n t b bi hh => exact absurd rfl (hl n t b bi hh)
  | _ => rfl

/-- `happP` on a spine whose arguments have the parameters' types. -/
theorem happP_total_of {Γ : List Ty} : ∀ (args : List Expr) (f : Expr) (ρs : List Ty) (τ : Ty),
    (∀ ρ ∈ ρs, HinstTotalAt ρ) → Typ Γ (er f) (Ty.arrows ρs τ) → TypArgs Γ (args.map er) ρs →
    ∃ N r, (∀ m, N ≤ m → happP m f args = .ok r) ∧ Typ Γ (er r) τ
  | [], f, ρs, τ, _, hf, ha => by
    cases ha
    refine ⟨1, mkAppN f ([] : List Expr).toArray, fun m hm => ?_, ?_⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [happP_succ]
      cases f <;> rfl
    · rw [mkAppN_toList, List.map_nil, Tm.appN_nil]; simpa [Ty.arrows] using hf
  | a :: rest, f, ρs, τ, H, hf, ha => by
    cases ha with
    | @cons _ ρ _ ρs' ha hrest =>
      by_cases hl : ∃ n t b bi hh, f = Expr.lam n t b bi hh
      · obtain ⟨n, t, b, bi, hh, rfl⟩ := hl
        simp only [er, Ty.arrows] at hf
        obtain ⟨_, σx, τb, he, -, hb⟩ := typ_lam_inv hf
        obtain ⟨rfl, rfl⟩ := Ty.arr_inj he
        obtain ⟨N1, b', cb, h1, t1, -, -⟩ :=
          H ρ List.mem_cons_self b a [] Γ _ ha (by simpa using hb)
        obtain ⟨N2, r, h2, t2⟩ :=
          happP_total_of rest b' ρs' τ (fun ρ' h => H ρ' (List.mem_cons_of_mem _ h)) (by simpa using t1) hrest
        refine ⟨max N1 N2 + 1, r, fun m hm => ?_, t2⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [happP_succ]
        show (do let (b', _) ← hinstP m' a 0 b; happP m' b' rest) = .ok r
        rw [show (0 : Nat) = ([] : List Ty).length from rfl, h1 m' (by omega)]
        exact h2 m' (by omega)
      · refine ⟨1, mkAppN f (a :: rest).toArray, fun m hm => ?_, ?_⟩
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          exact happP_succ_nonlam m' f a rest (fun n t b bi hh e => hl ⟨n, t, b, bi, hh, e⟩)
        · rw [mkAppN_toList]
          exact Typ.appN_iff.2 ⟨ρ :: ρs', hf, .cons ha hrest⟩

end Ix.CompileCert.Conv

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created projCtor?)

theorem TypArgs.split {Γ : List Ty} : ∀ {as bs : List Tm} {σs : List Ty}, TypArgs Γ (as ++ bs) σs →
    ∃ σs₁ σs₂, σs = σs₁ ++ σs₂ ∧ TypArgs Γ as σs₁ ∧ TypArgs Γ bs σs₂
  | [], bs, σs, h => ⟨[], σs, rfl, .nil, h⟩
  | a :: as, bs, σs, h => by
    cases h with
    | cons ha hrest =>
      obtain ⟨σs₁, σs₂, rfl, h1, h2⟩ := TypArgs.split hrest
      exact ⟨_ :: σs₁, σs₂, rfl, .cons ha h1, h2⟩

theorem TypArgs.lower {Θ Δ : List Ty} {σ : Ty} : ∀ {as : List Tm} {σs : List Ty},
    TypArgs (Θ ++ σ :: Δ) as σs → (∀ a ∈ as, Tm.occ a Θ.length = false) →
    TypArgs (Θ ++ Δ) (as.map (Tm.lower 1 Θ.length)) σs
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons ha hrest, hocc =>
    .cons (Typ.lower ha (hocc _ List.mem_cons_self))
      (TypArgs.lower hrest fun a h => hocc a (List.mem_cons_of_mem _ h))

/-- Hereditary steps at the smaller types: the induction on the term. -/
theorem hinstTotalAt_of (n : Nat) (IHt : ∀ ρ, ρ.size ≤ n → HinstTotalAt ρ) (σ : Ty)
    (hσ : σ.size ≤ n + 1) : HinstTotalAt σ := by
  suffices H : ∀ (s : Nat) (e : Expr), sizeOf e < s → ∀ (v : Expr) (Θ Δ : List Ty) (τ : Ty),
      Typ Δ (er v) σ → Typ (Θ ++ σ :: Δ) (er e) τ → HinstOk v σ Θ Δ e τ from
    fun e v Θ Δ τ hv he => H (sizeOf e + 1) e (by omega) v Θ Δ τ hv he
  intro s
  induction s with
  | zero => intro e h; omega
  | succ s ih =>
    intro e hs v Θ Δ τ hv he
    by_cases hr : looseRangeP e ≤ Θ.length
    · -- nothing to substitute
      refine ⟨1, e, .no, fun m hm => ?_, ?_, (fun h => by cases h), (fun h => by cases h)⟩
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        unfold hinstP; simp only [hr, ↓reduceIte]; rfl
      · have hr' : Tm.range (er e) ≤ Θ.length := by rw [← looseRangeP_eq]; exact hr
        have := Typ.lower he (Tm.occ_of_range_le _ _ hr')
        rwa [Tm.lower_of_range_le 1 Θ.length _ hr'] at this
    · match e, hs, he, hr with
      | .bvar i hh, hs, he, hr =>
        simp only [er] at he
        cases he with
        | bvar hi =>
          simp only [looseRangeP] at hr
          by_cases hik : i = Θ.length
          · subst hik
            rw [List.getElem?_append_right (by omega), Nat.sub_self, List.getElem?_cons_zero] at hi
            cases hi
            refine ⟨1, liftP v Θ.length 0, .direct, fun m hm => ?_, ?_, fun _ => ?_,
              (fun h => by cases h)⟩
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              unfold hinstP; simp only [looseRangeP, hr, ↓reduceIte, beq_self_eq_true]; rfl
            · rw [er_liftP]; exact Typ.lift_front Θ hv
            · exact ⟨[], [], by rw [er_liftP]; rfl, rfl, .nil⟩
          · have hgt : i > Θ.length := by omega
            refine ⟨1, Expr.mkBVar (i - 1), .no, fun m hm => ?_, ?_, (fun h => by cases h),
              (fun h => by cases h)⟩
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              have hb : (i == Θ.length) = false := by simp [hik]
              unfold hinstP; simp only [looseRangeP, hr, ↓reduceIte, hb, hgt]; rfl
            · rw [er_mkBVar]
              apply Typ.bvar
              rw [List.getElem?_append_right (by omega)]
              rw [List.getElem?_append_right (by omega)] at hi
              have : i - Θ.length = (i - 1 - Θ.length) + 1 := by omega
              rw [this, List.getElem?_cons_succ] at hi
              exact hi
      | .app f₀ a₀ hh, hs, he, hr =>
        have hsz := getAppFnArgs_sizeOf f₀ a₀ hh
        rw [er_getAppFnArgs] at he
        obtain ⟨ρs, tH0, tA0⟩ := Typ.appN_iff.1 he
        obtain ⟨Na, args0, hNa, tA⟩ := args_total (v := v) (k := Θ.length) (Γ₂ := Θ ++ Δ) _ ρs
          (fun a ha ρ hta => by
            obtain ⟨N, r, c, h1, t1, -, -⟩ := ih a (by have := hsz.2 a ha; omega) v Θ Δ ρ hv hta
            exact ⟨N, r, c, h1, t1⟩) tA0
        obtain ⟨Nh, h0, c0, hNh, tH, dH, rH⟩ := ih _ (by have := hsz.1; omega) v Θ Δ _ hv tH0
        -- the fuel goal, reduced to the tail of the application case
        have run : ∀ m', max Na Nh ≤ m' → ∀ R, (match (generalizing := false) c0, h0 with
            | .no, _ => pure (mkAppN h0 args0.toArray, Created.no)
            | _, .lam .. => do pure ((← happP m' h0 args0), Created.reduced)
            | c, _ => pure (mkAppN h0 args0.toArray, c)) = Except.ok R →
            hinstP (m' + 1) v Θ.length (.app f₀ a₀ hh) = .ok R := by
          intro m' hm' R hR
          unfold hinstP
          simp only [hr, ↓reduceIte]
          rw [hNa m' (by omega), hNh m' (by omega)]
          exact hR
        by_cases hc : c0 = .no
        · subst hc
          refine ⟨max Na Nh + 1, mkAppN h0 args0.toArray, .no, fun m hm => ?_, ?_,
            (fun h => by cases h), (fun h => by cases h)⟩
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            exact run m' (by omega) _ rfl
          · rw [mkAppN_toList]; exact Typ.appN_iff.2 ⟨ρs, tH, tA⟩
        · have hsize := HinstOk.size dH rH hc
          by_cases hl : ∃ nm t b bi hh', h0 = Expr.lam nm t b bi hh'
          · obtain ⟨nm, t, b, bi, hh', rfl⟩ := hl
            have Hρ : ∀ ρ ∈ ρs, HinstTotalAt ρ := fun ρ hρ =>
              IHt ρ (by have := size_arrows_dom (τ := τ) ρ hρ; omega)
            obtain ⟨Nap, r, hap, tr⟩ := happP_total_of args0 _ ρs τ Hρ tH tA
            refine ⟨max (max Na Nh) Nap + 1, r, .reduced, fun m hm => ?_, tr,
              (fun h => by cases h), fun _ => ?_⟩
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              refine run m' (by omega) _ ?_
              cases c0 with
              | no => exact absurd rfl hc
              | direct => show (do pure ((← happP m' _ args0), Created.reduced)) = _; rw [hap m' (by omega)]; rfl
              | reduced => show (do pure ((← happP m' _ args0), Created.reduced)) = _; rw [hap m' (by omega)]; rfl
            · have := size_arrows_le ρs τ; omega
          · refine ⟨max Na Nh + 1, mkAppN h0 args0.toArray, c0, fun m hm => ?_, ?_, fun hd => ?_,
              fun _ => ?_⟩
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              refine run m' (by omega) _ ?_
              cases c0 with
              | no => exact absurd rfl hc
              | direct =>
                cases h0 with
                | lam nm t b bi hh' => exact absurd ⟨nm, t, b, bi, hh', rfl⟩ hl
                | _ => rfl
              | reduced =>
                cases h0 with
                | lam nm t b bi hh' => exact absurd ⟨nm, t, b, bi, hh', rfl⟩ hl
                | _ => rfl
            · rw [mkAppN_toList]; exact Typ.appN_iff.2 ⟨ρs, tH, tA⟩
            · obtain ⟨as, σs, eh, hσs, tas⟩ := dH hd
              refine ⟨as ++ args0.map er, σs ++ ρs, ?_, ?_, tas.append tA⟩
              · rw [mkAppN_toList, eh, Tm.appN_append]
              · rw [Ty.arrows_append, ← hσs]
            · have := size_arrows_le ρs τ; omega
      | .proj s₀ i x hh, hs, he, hr =>
        simp only [er] at he
        have hsx : sizeOf x < s := by simp only [Expr.proj.sizeOf_spec] at hs; omega
        -- the projected term's type in the derivation, and what the projection's type is
        have key : ∃ ρx, Typ (Θ ++ σ :: Δ) (er x) ρx ∧
            (∀ x', Typ (Θ ++ Δ) (er x') ρx → Typ (Θ ++ Δ) (.proj s₀ i (er x')) τ) ∧
            (∀ c us (α β a b : Tm), pairName s₀ c = true → i < 2 →
              ∀ x', er x' = pair4 c us α β a b → Typ (Θ ++ Δ) (er x') ρx →
              ((i = 0 → Typ (Θ ++ Δ) a τ) ∧ (i = 1 → Typ (Θ ++ Δ) b τ)) ∧ τ.size < ρx.size) := by
          cases he with
          | @proj0 _ _ _ k A B hk hx =>
            refine ⟨_, hx, fun x' t => .proj0 hk t, fun c us α β a b hp _ x' ex tx => ?_⟩
            rw [ex] at tx
            obtain ⟨ta, -⟩ := typ_pair4 hp tx
            refine ⟨⟨fun _ => ta, fun h => by cases h⟩, ?_⟩
            rw [Ty.size_pair]; omega
          | @proj1 _ _ _ k A B hk hx =>
            refine ⟨_, hx, fun x' t => .proj1 hk t, fun c us α β a b hp _ x' ex tx => ?_⟩
            rw [ex] at tx
            obtain ⟨-, tb⟩ := typ_pair4 hp tx
            refine ⟨⟨(fun h => by cases h), fun _ => tb⟩, ?_⟩
            rw [Ty.size_pair]; omega
          | @projOpaque _ _ _ _ ρ _ hsi hx =>
            refine ⟨_, hx, fun x' t => .projOpaque _ hsi t, fun c us α β a b hp hi2 x' ex tx => ?_⟩
            obtain ⟨k, hk⟩ := pairName_pairKind hp
            exfalso
            rcases hsi with hsi | hsi
            · rw [hsi] at hk; cases hk
            · omega
        obtain ⟨ρx, tX0, rebuild, field⟩ := key
        obtain ⟨Nx, x0, cx, hNx, tX, dX, rX⟩ := ih x hsx v Θ Δ ρx hv tX0
        have run : ∀ m', Nx ≤ m' → ∀ R, (match (generalizing := false) cx with
            | .no => pure (Expr.mkProj s₀ i x0, Created.no)
            | _ =>
              match projCtor? s₀ i x0 with
              | some f => pure (f, Created.reduced)
              | none => pure (Expr.mkProj s₀ i x0, Created.no)) = (Except.ok R : Except String (Expr × Created)) →
            hinstP (m' + 1) v Θ.length (.proj s₀ i x hh) = .ok R := by
          intro m' hm' R hR
          unfold hinstP
          simp only [hr, ↓reduceIte]
          rw [hNx m' hm']
          exact hR
        by_cases hc : cx = .no
        · subst hc
          refine ⟨Nx + 1, Expr.mkProj s₀ i x0, .no, fun m hm => ?_, ?_, (fun h => by cases h),
            (fun h => by cases h)⟩
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            exact run m' (by omega) _ rfl
          · rw [er_mkProj]; exact rebuild x0 tX
        · cases hpc : projCtor? s₀ i x0 with
          | none =>
            refine ⟨Nx + 1, Expr.mkProj s₀ i x0, .no, fun m hm => ?_, ?_, (fun h => by cases h),
              (fun h => by cases h)⟩
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              refine run m' (by omega) _ ?_
              cases cx with
              | no => exact absurd rfl hc
              | direct => rw [hpc]; rfl
              | reduced => rw [hpc]; rfl
            · rw [er_mkProj]; exact rebuild x0 tX
          | some f =>
            obtain ⟨c, us, α, β, a, b, ex, hp, hfi⟩ := projCtor?_spec hpc
            have hi2 : i < 2 := by rcases hfi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
            have hsz := HinstOk.size dX rX hc
            obtain ⟨⟨h0, h1⟩, hlt⟩ := field c us _ _ _ _ hp hi2 x0 ex tX
            refine ⟨Nx + 1, f, .reduced, fun m hm => ?_, ?_, (fun h => by cases h),
              fun _ => by omega⟩
            · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              refine run m' (by omega) _ ?_
              cases cx with
              | no => exact absurd rfl hc
              | direct => rw [hpc]; rfl
              | reduced => rw [hpc]; rfl
            · rcases hfi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact h0 rfl
              · exact h1 rfl
      | .lam nm t b bi hh, hs, he, hr =>
        simp only [er] at he
        have hst : sizeOf t < s := by simp only [Expr.lam.sizeOf_spec] at hs; omega
        have hsb : sizeOf b < s := by simp only [Expr.lam.sizeOf_spec] at hs; omega
        obtain ⟨ρt, σx, τb, rfl, tT0, tB0⟩ := typ_lam_inv he
        obtain ⟨Nt, t0, ct, hNt, tT, -, -⟩ := ih t hst v Θ Δ ρt hv tT0
        obtain ⟨Nb, b0, cb, hNb, tB, dB, -⟩ := ih b hsb v (σx :: Θ) Δ τb hv (by simpa using tB0)
        simp only [List.length_cons, List.cons_append] at hNb tB dB
        have run : ∀ m', max Nt Nb ≤ m' → ∀ R, (match (generalizing := false) cb, b0 with
            | .direct, .app f (.bvar 0 _) _ =>
              if !(occursP f 0) then pure (lowerP f 1 0, Created.direct)
              else pure (Expr.mkLam nm t0 b0 bi, Created.no)
            | _, _ => pure (Expr.mkLam nm t0 b0 bi, Created.no)) = (Except.ok R : Except String (Expr × Created)) →
            hinstP (m' + 1) v Θ.length (.lam nm t b bi hh) = .ok R := by
          intro m' hm' R hR
          unfold hinstP
          simp only [hr, ↓reduceIte]
          rw [hNt m' (by omega), hNb m' (by omega)]
          exact hR
        by_cases hη : ∃ f h1 h2, cb = .direct ∧ b0 = .app f (.bvar 0 h1) h2 ∧ occursP f 0 = false
        · obtain ⟨f, h1, h2, rfl, rfl, hocc⟩ := hη
          obtain ⟨as, σs, eb, hσs, tas⟩ := dB rfl
          have hocc' : Tm.occ (er f) 0 = false := by rw [← occursP_eq]; exact hocc
          simp only [er] at eb
          rcases appN_eq_app eb.symm with ⟨-, ehd⟩ | ⟨as', rfl, ef⟩
          · exfalso
            have h1' := Tm.occ_lift_mid (Θ.length + 1) 0 0 (er v) (Nat.le_refl _) (by omega)
            rw [ehd] at h1'
            simp [Tm.occ] at h1'
          · obtain ⟨σs', σs'', rfl, tas', tz⟩ := TypArgs.split tas
            cases tz with
            | cons tz0 tznil =>
              cases tznil
              cases tz0 with
              | bvar hz =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
                subst hz
                have hocc'' : ∀ a ∈ as', Tm.occ a 0 = false := (Tm.occ_appN (ef ▸ hocc')).2
                have tas'' := @TypArgs.lower [] (Θ ++ Δ) σx as' σs' tas' (by simpa using hocc'')
                simp only [List.nil_append, List.length_nil] at tas''
                have hσ : σ = Ty.arrows σs' (.arr σx τb) := by
                  rw [hσs, Ty.arrows_append]; rfl
                have er_r : er (lowerP f 1 0) = Tm.appN (Tm.lift Θ.length 0 (er v))
                    (as'.map (Tm.lower 1 0)) := by
                  rw [er_lowerP, ef, Tm.lower_appN, lower_lift_succ]
                refine ⟨max Nt Nb + 1, lowerP f 1 0, .direct, fun m hm => ?_, ?_,
                  fun _ => ⟨_, σs', er_r, hσ, tas''⟩, (fun h => by cases h)⟩
                · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                  refine run m' (by omega) _ ?_
                  simp only [hocc, Bool.not_false, ↓reduceIte]; rfl
                · rw [er_r]
                  exact Typ.appN_iff.2 ⟨σs', hσ ▸ Typ.lift_front Θ hv, tas''⟩
        · refine ⟨max Nt Nb + 1, Expr.mkLam nm t0 b0 bi, .no, fun m hm => ?_, ?_,
            (fun h => by cases h), (fun h => by cases h)⟩
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            refine run m' (by omega) _ ?_
            split
            · rename_i f h1 h2
              split
              · rename_i hocc
                exfalso
                exact hη ⟨f, h1, h2, rfl, rfl, by simpa using hocc⟩
              · rfl
            · rfl
          · rw [er_mkLam]; exact .lam tT tB
      | .forallE nm t b bi hh, hs, he, hr =>
        simp only [er] at he
        have hst : sizeOf t < s := by simp only [Expr.forallE.sizeOf_spec] at hs; omega
        have hsb : sizeOf b < s := by simp only [Expr.forallE.sizeOf_spec] at hs; omega
        cases he with
        | @pi _ _ _ ρt σx ρb _ tT0 tB0 =>
          obtain ⟨Nt, t0, ct, hNt, tT, -, -⟩ := ih t hst v Θ Δ ρt hv tT0
          obtain ⟨Nb, b0, cb, hNb, tB, -, -⟩ := ih b hsb v (σx :: Θ) Δ ρb hv (by simpa using tB0)
          simp only [List.length_cons, List.cons_append] at hNb tB
          refine ⟨max Nt Nb + 1, Expr.mkForallE nm t0 b0 bi, .no, fun m hm => ?_, ?_,
            (fun h => by cases h), (fun h => by cases h)⟩
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            unfold hinstP
            simp only [hr, ↓reduceIte]
            rw [hNt m' (by omega), hNb m' (by omega)]
            rfl
          · rw [er_mkForallE]; exact .pi _ tT tB
      | .letE nm t x b nd hh, hs, he, hr =>
        simp only [er] at he
        have hst : sizeOf t < s := by simp only [Expr.letE.sizeOf_spec] at hs; omega
        have hsx : sizeOf x < s := by simp only [Expr.letE.sizeOf_spec] at hs; omega
        have hsb : sizeOf b < s := by simp only [Expr.letE.sizeOf_spec] at hs; omega
        cases he with
        | @letE _ _ _ _ ρt σx _ tT0 tX0 tB0 =>
          obtain ⟨Nt, t0, ct, hNt, tT, -, -⟩ := ih t hst v Θ Δ ρt hv tT0
          obtain ⟨Nx, x0, cx, hNx, tX, -, -⟩ := ih x hsx v Θ Δ σx hv tX0
          obtain ⟨Nb, b0, cb, hNb, tB, -, -⟩ := ih b hsb v (σx :: Θ) Δ _ hv (by simpa using tB0)
          simp only [List.length_cons, List.cons_append] at hNb tB
          refine ⟨max (max Nt Nx) Nb + 1, Expr.mkLetE nm t0 x0 b0 nd, .no, fun m hm => ?_, ?_,
            (fun h => by cases h), (fun h => by cases h)⟩
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            unfold hinstP
            simp only [hr, ↓reduceIte]
            rw [hNt m' (by omega), hNx m' (by omega), hNb m' (by omega)]
            rfl
          · rw [er_mkLetE]; exact .letE tT tX tB
      | .mdata md x hh, hs, he, hr =>
        simp only [er] at he
        have hsx : sizeOf x < s := by simp only [Expr.mdata.sizeOf_spec] at hs; omega
        obtain ⟨Nx, x0, cx, hNx, tX, dX, rX⟩ := ih x hsx v Θ Δ τ hv he
        refine ⟨Nx + 1, Expr.mkMData md x0, cx, fun m hm => ?_, by rwa [er_mkMData],
          fun hd => ?_, rX⟩
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          unfold hinstP
          simp only [hr, ↓reduceIte]
          rw [hNx m' (by omega)]
          rfl
        · obtain ⟨as, σs, ex, h1, h2⟩ := dX hd
          exact ⟨as, σs, by rw [er_mkMData]; exact ex, h1, h2⟩
      | .fvar .., _, _, hr => exact absurd (by simp [looseRangeP]) hr
      | .mvar .., _, _, hr => exact absurd (by simp [looseRangeP]) hr
      | .sort .., _, _, hr => exact absurd (by simp [looseRangeP]) hr
      | .const .., _, _, hr => exact absurd (by simp [looseRangeP]) hr
      | .lit .., _, _, hr => exact absurd (by simp [looseRangeP]) hr

end Ix.CompileCert.Conv

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created projCtor?)

/-- **The development terminates on simply typed input**: substituting a value of type `σ` into
a term typed with `σ` at the substituted position succeeds from some fuel on, with one result,
of the term's type. -/
theorem develop_total : ∀ (σ : Ty), HinstTotalAt σ := by
  suffices H : ∀ n σ, σ.size ≤ n → HinstTotalAt σ from fun σ => H σ.size σ (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro σ h; have := Ty.size_pos σ; omega
  | succ n ih => intro σ h; exact hinstTotalAt_of n ih σ h

/-- The head-β part: a spine whose arguments have the parameters' types. -/
theorem happP_total {Γ : List Ty} {f : Expr} {args : List Expr} {ρs : List Ty} {τ : Ty}
    (hf : Typ Γ (er f) (Ty.arrows ρs τ)) (ha : TypArgs Γ (args.map er) ρs) :
    ∃ N r, (∀ m, N ≤ m → happP m f args = .ok r) ∧ Typ Γ (er r) τ :=
  happP_total_of args f ρs τ (fun ρ _ => develop_total ρ) hf ha

/-- **The call-site development succeeds on a simply typable call site** from some fuel on,
with one result (convertible to the call site, `instantiateP_conv`, and of its type). -/
theorem instantiate_total {Γ : List Ty} {f : Expr} {args : Array Expr} {τ : Ty}
    (h : Typ Γ (er (mkAppN f args)) τ) :
    ∃ N r, (∀ m, N ≤ m → happP m f args.toList = .ok r) ∧ Typ Γ (er r) τ := by
  rw [er_mkAppN] at h
  obtain ⟨ρs, hf, ha⟩ := Typ.appN_iff.1 h
  exact happP_total hf ha

/-- `instantiateP` (the core at `defaultFuel`) on a simply typable call site: it succeeds
whenever the depth of the run is within `defaultFuel`; a larger fuel never changes a result
(`fuel_mono`). -/
theorem instantiateP_of_total {f : Expr} {args : Array Expr} {N : Nat} {r : Expr}
    (h : ∀ m, N ≤ m → happP m f args.toList = .ok r) (hN : N ≤ Ix.Compile.Image.defaultFuel) :
    instantiateP f args = .ok r := h _ hN

end Ix.CompileCert.Conv
