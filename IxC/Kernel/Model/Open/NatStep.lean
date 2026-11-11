module

public import IxC.Kernel.Model.Open.Lit
public import IxC.Kernel.Rules.NatOffset

@[expose] public section

/-!
# The rules' soundness over the public `Model`: the `Nat` steps

* `Red.natSucc`: `Nat.succ a`, with `a` reducing to a literal reading, is the next literal —
  `Denotes` reads a literal as its constructor form.
* `Red.natOp`: a stored binary operation on two literal readings is its result — the literal
  law (`Model.lit_ops`).
* `Red.natAddSucc`, `Red.natAddZero`, `DefEq.natOffset`: `Nat.add b k` at a non-literal `b`
  — `Nat.add`'s recurrences (`Model.nat_add`). The rules read `b`'s membership in `Nat` off
  the stored `Nat.add`'s outer binder, whose datum is `never` (`natAddTyOk`): a graph
  determines its domain, so the subject's grading puts `b`'s set in `Nat`'s.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Readings -/

/-- `x` after `k` applications of `s`. -/
noncomputable def succIter (s x : V) : Nat → V
  | 0 => x
  | k + 1 => app s (succIter s x k)

omit [SetTheory V] in
theorem succIter_add (s x : V) (j : Nat) :
    ∀ k, succIter s (succIter s x j) k = succIter s x (j + k)
  | 0 => rfl
  | k + 1 => congrArg (app s) (succIter_add s x j k)

/-- **A literal reading** (`rawNatLit?`: a literal, or `Nat.zero`) denotes what the literal
does. -/
theorem rawNatLit_den {w : Expr md} {n : Nat} (h : rawNatLit? w = some n) {σ : Nat → V}
    {ρ : BVarIdx → V} {X : V} (hX : DenotesO M.cval env φ σ ρ w X) :
    DenotesO M.cval env φ σ ρ (.lit (.natVal n)) X := by
  cases w with
  | lit l =>
    cases l with
    | natVal m =>
      simp only [rawNatLit?, Option.some.injEq] at h
      subst h
      exact hX
    | strVal _ => simp [rawNatLit?] at h
  | const c us =>
    cases us with
    | nil =>
      simp only [rawNatLit?] at h
      split at h
      · rename_i hc
        subst hc
        simp only [Option.some.injEq] at h
        subst h
        exact .natLit hX
      · exact nomatch h
    | cons _ _ => simp [rawNatLit?] at h
  | _ => simp [rawNatLit?] at h

/-- **A level-monomorphic constant's head**: every reading of it is `cval n φ`. -/
theorem mono_head {n : Key md} {ci : ConstantInfo md} (hf : env.find? n = some ci)
    (hl : ci.toConstantVal.levelParams = []) {us : List Level} {σ : Nat → V}
    {ρ : BVarIdx → V} {F : V} (h : DenotesO M.cval env φ σ ρ (.const n us) F) :
    F = M.cval n φ := by
  cases h with
  | const hf' hlen =>
    rw [hf] at hf'
    cases hf'
    rw [hl] at hlen ⊢
    rw [List.eq_nil_of_length_eq_zero hlen, substFn_nil_eq]

/-- **The literals as successor powers**: literal `n` denotes `succⁿ zero`, a member of
`Nat`'s set. -/
theorem natLit_val (hs : natLitSupported env = true) (σ : Nat → V) :
    ∀ n : Nat, (∀ ρ, DenotesO M.cval env φ σ ρ (.lit (.natVal n))
        (succIter (M.cval natSuccName φ) (M.cval natZeroName φ) n)) ∧
      succIter (M.cval natSuccName φ) (M.cval natZeroName φ) n ∈ˢ M.cval natName φ := by
  obtain ⟨r, B, -, hZ, hS, hZm, hSm, hBN, hP⟩ := nat_basis (M := M) (φ := φ) hs σ
  intro n
  induction n with
  | zero => exact ⟨fun ρ => .natLit (hZ ρ), hZm⟩
  | succ k ih =>
    refine ⟨fun ρ => .natLit (.app (hS ρ) (ih.1 ρ)), ?_⟩
    have h := app_mem_piR hSm ih.2 (by rw [← univ_zero]; exact hP)
    rwa [hBN _ ih.2] at h

/-! ## `Nat.succ` and the binary operations on literals -/

/-- **`Nat.succ` packing** (`Red.natSucc`). -/
theorem Red.natSucc_sound {d n : Nat} {a w : Expr md} (hr : RedS M φ d a w)
    (hw : rawNatLit? w = some n) :
    RedS M φ d (.app (.const natSuccName []) a) (.lit (.natVal (n + 1))) := by
  intro hfr
  obtain ⟨-, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨-, -, k⟩ := hr hfa
  refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun σ hC v hv hg => ?_⟩
  obtain ⟨-, hga, -⟩ := Gr.app_iff.1 hg
  cases hv with
  | app hS hX =>
    obtain ⟨hXw, -⟩ := k σ (hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]) _ hX hga
    exact ⟨.natLit (.app hS (rawNatLit_den hw hXw)), True.intro⟩

/-- **The result of a binary literal operation, as the literal law states it.** -/
theorem natOpResult_law {c : Key md} {a b : Nat} {r : Expr md} (hc : c ∈ natBinOpNames)
    (hr : natOpResult c a b = some r) :
    (∃ f : Nat → Nat → Nat, (c, f) ∈ natArithOps ∧ r = .lit (.natVal (f a b))) ∨
    (∃ f : Nat → Nat → Bool, (c, f) ∈ natCmpOps ∧
      r = .const (if f a b then boolTrueName else boolFalseName) []) := by
  unfold natOpResult at hr
  by_cases h1 : c = natPredName
  · subst h1
    exact absurd hc (by cases md <;> decide)
  rw [if_neg h1] at hr
  by_cases h2 : c = natAddName
  · subst h2
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.add, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h2] at hr
  by_cases h3 : c = natSubName
  · subst h3
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.sub, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h3] at hr
  by_cases h4 : c = natMulName
  · subst h4
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.mul, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h4] at hr
  by_cases h5 : c = natPowName
  · subst h5
    rw [if_pos rfl] at hr
    split at hr
    · exact nomatch hr
    · exact Or.inl ⟨Nat.pow, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h5] at hr
  by_cases h6 : c = natDivName
  · subst h6
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.div, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h6] at hr
  by_cases h7 : c = natModName
  · subst h7
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.mod, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h7] at hr
  by_cases h8 : c = natGcdName
  · subst h8
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.gcd, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h8] at hr
  by_cases h9 : c = natLandName
  · subst h9
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.land, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h9] at hr
  by_cases h10 : c = natLorName
  · subst h10
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.lor, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h10] at hr
  by_cases h11 : c = natXorName
  · subst h11
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.xor, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h11] at hr
  by_cases h12 : c = natShiftLeftName
  · subst h12
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.shiftLeft, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h12] at hr
  by_cases h13 : c = natShiftRightName
  · subst h13
    rw [if_pos rfl] at hr
    exact Or.inl ⟨Nat.shiftRight, by simp [natArithOps], (Option.some.inj hr).symm⟩
  rw [if_neg h13] at hr
  by_cases h14 : c = natBeqName
  · subst h14
    rw [if_pos rfl] at hr
    refine Or.inr ⟨Nat.beq, by simp [natCmpOps], ?_⟩
    rw [← Option.some.inj hr]
    cases hb : Nat.beq a b
    · rw [if_neg (Nat.ne_of_beq_eq_false hb), if_neg (by decide)]
    · rw [if_pos (Nat.eq_of_beq_eq_true hb), if_pos rfl]
  rw [if_neg h14] at hr
  by_cases h15 : c = natBleName
  · subst h15
    rw [if_pos rfl] at hr
    refine Or.inr ⟨Nat.ble, by simp [natCmpOps], ?_⟩
    rw [← Option.some.inj hr]
    cases hb : Nat.ble a b
    · rw [if_neg (Nat.not_le_of_not_ble_eq_true (by rw [hb]; decide)), if_neg (by decide)]
    · rw [if_pos (Nat.le_of_ble_eq_true hb), if_pos rfl]
  rw [if_neg h15] at hr
  exact nomatch hr

/-- **Binary `Nat` acceleration** (`Red.natOp`): the literal law (`Model.lit_ops`). -/
theorem Red.natOp_sound {d : Nat} {c : Key md} {a wa b wb r : Expr md} {n₁ n₂ : Nat}
    (hc : c ∈ natBinOpNames) (hst : natOpStored env c = true)
    (ha : RedS M φ d a wa) (hwa : rawNatLit? wa = some n₁)
    (hb : RedS M φ d b wb) (hwb : rawNatLit? wb = some n₂)
    (hr : natOpResult c n₁ n₂ = some r) :
    RedS M φ d (.app (.app (.const c []) a) b) r := by
  have hrc : r.hasFvar = false ∧ r.looseBVarsBounded 0 = true := by
    rcases natOpResult_shape hr with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> exact ⟨rfl, rfl⟩
  obtain ⟨cv, val, hint, hfc⟩ : ∃ cv val hint, env.find? c = some (.defnInfo cv val hint) := by
    cases hf : env.find? c with
    | none => simp [natOpStored, hf] at hst
    | some ci =>
      cases ci with
      | defnInfo cv val hint => exact ⟨cv, val, hint, rfl⟩
      | _ => simp [natOpStored, hf] at hst
  intro hfr
  obtain ⟨hfca, hfb⟩ := Frame.app_iff.1 hfr
  obtain ⟨-, hfa⟩ := Frame.app_iff.1 hfca
  obtain ⟨-, -, ka⟩ := ha hfa
  obtain ⟨-, -, kb⟩ := hb hfb
  refine ⟨Frame.of_closed hrc.1 hrc.2, LeavesSub.of_closed hrc.1, fun σ hC v hv hg => ?_⟩
  obtain ⟨hgca, hgb, -⟩ := Gr.app_iff.1 hg
  obtain ⟨-, hga, -⟩ := Gr.app_iff.1 hgca
  cases hv with
  | app hCA hB =>
    cases hCA with
    | app hc' hA =>
      obtain ⟨hA', -⟩ := ka σ (hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]) _ hA hga
      obtain ⟨hB', -⟩ := kb σ (hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]) _ hB hgb
      have hD := DenotesO.to_denotes (.app (.app hc' (rawNatLit_den hwa hA'))
        (rawNatLit_den hwb hB')) (by rfl)
      rcases natOpResult_law hc hr with ⟨f, hmem, rfl⟩ | ⟨f, hmem, rfl⟩
      · exact ⟨DenotesO.of_denotes (M.lit_ops.2.1 c f hmem cv val hint hfc φ ρ₀ n₁ n₂ _ hD),
          True.intro⟩
      · exact ⟨DenotesO.of_denotes (M.lit_ops.2.2 c f hmem cv val hint hfc φ ρ₀ n₁ n₂ _ hD),
          True.intro⟩

/-! ## `Nat.add` at a non-literal -/

/-- `natAddTyOk`, inverted. -/
theorem natAddTyOk_inv (h : natAddTyOk (env.find? natAddName) = true) :
    ∃ cv v hint mb1 mb2, env.find? natAddName = some (.defnInfo cv v hint) ∧
      cv.levelParams = [] ∧
      cv.type = .forallE (.const natName []) (.forallE (.const natName []) (.const natName []) mb2)
        mb1 ∧ mb1.pw.isNever = true := by
  unfold natAddTyOk at h
  split at h
  · next cv v hint heqA =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨hl, hty⟩ := h
    split at hty
    · next d₁ d₂ c mb2 mb1 heq =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hty
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hnev⟩ := hty
      exact ⟨cv, v, hint, mb1, mb2, heqA, hl, heq, hnev⟩
    · exact nomatch hty
  · exact nomatch h

/-- **A graph's argument is in its domain**: a function in a graph-regime product and in a
second product applied in the second's domain is applied in the first's. -/
theorem mem_dom_pos {r r' : Nat} {A A' F X : V} {B B' : V → V} (hr' : r' ≠ 0)
    (hF : F ∈ˢ piR r A B) (hF' : F ∈ˢ piR r' A' B') (hX : X ∈ˢ A) : X ∈ˢ A' := by
  have hr : r ≠ 0 := by
    intro h0
    subst h0
    have hpt := eq_pt_of_mem_piR_zero hF
    rw [hpt] at hF'
    exact not_pt_mem_piR_pos hr' hF'
  rw [← piR_dom_unique hr hr' hF hF']
  exact hX

/-- **The stored `Nat.add` in the sets**: a graph from `Nat`'s set to functions from `Nat`'s
set into it. -/
theorem natAdd_basis (hs : natLitSupported env = true)
    (ht : natAddTyOk (env.find? natAddName) = true) (σ : Nat → V) :
    ∃ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint) (r1 : Nat) (B1 : V → V),
      env.find? natAddName = some (.defnInfo cv v hint) ∧ cv.levelParams = [] ∧
      (∀ ρ, DenotesO M.cval env φ σ ρ (.const natAddName []) (M.cval natAddName φ)) ∧
      M.cval natAddName φ ∈ˢ piR r1 (M.cval natName φ) B1 ∧ r1 ≠ 0 ∧
      ∀ x, x ∈ˢ M.cval natName φ → ∃ (r2 : Nat) (B2 : V → V),
        B1 x = piR r2 (M.cval natName φ) B2 ∧
        (∀ y, y ∈ˢ M.cval natName φ → B2 y = M.cval natName φ) ∧
        (r2 = 0 → ∀ y, y ∈ˢ M.cval natName φ → B2 y ∈ˢ univ 0) := by
  obtain ⟨cv, v, hint, mb1, mb2, hfA, hl, hty, hnev⟩ := natAddTyOk_inv ht
  obtain ⟨hN, -⟩ := natLit_den (M := M) (φ := φ) hs σ
  obtain ⟨hA, T, hT, hm⟩ := mono_const (M := M) (φ := φ) hfA hl σ
  have hT' : Den M φ σ cv.type T := hT
  rw [hty] at hT'
  obtain ⟨A1, B1, rfl, hA1, hB1, -⟩ := pi_inv hT'
  obtain rfl := DenotesO.functional hA1 (hN ρ₀)
  refine ⟨cv, v, hint, _, B1, hfA, hl, hA, hm, regime_ne_zero_of_isNever hnev φ,
    fun x hx => ?_⟩
  obtain ⟨A2, B2, hY, hA2, hB2, hP2⟩ := pi_inv (hB1 x hx)
  obtain rfl := DenotesO.functional hA2 (hN _)
  exact ⟨_, B2, hY, fun y hy => DenotesO.functional (hB2 y hy) (hN _), hP2⟩

/-- **`Nat.add` on a literal**: `x + n` is `succⁿ x` at every `x` in `Nat`'s set
(`Model.nat_add`). -/
theorem natAdd_lit (hs : natLitSupported env = true) {cv : ConstantVal md} {v : Expr md}
    {hint : ReducibilityHint} (hfA : env.find? natAddName = some (.defnInfo cv v hint))
    (hl : cv.levelParams = []) (σ : Nat → V) {X : V} (hX : X ∈ˢ M.cval natName φ) :
    ∀ n : Nat, app (app (M.cval natAddName φ) X)
        (succIter (M.cval natSuccName φ) (M.cval natZeroName φ) n) =
      succIter (M.cval natSuccName φ) X n := by
  obtain ⟨r, B, hN, hZ, hS, -, -, -, -⟩ := nat_basis (M := M) (φ := φ) hs σ
  obtain ⟨hA, -⟩ := mono_const (M := M) (φ := φ) hfA hl σ
  have law := M.nat_add cv v hint hfA φ ρ₀ _ _ _ _ (DenotesO.to_denotes (hN ρ₀) rfl)
    (DenotesO.to_denotes (hZ ρ₀) rfl) (DenotesO.to_denotes (hS ρ₀) rfl)
    (DenotesO.to_denotes (hA ρ₀) rfl)
  intro n
  induction n with
  | zero => exact (law X _ hX (natLit_val (M := M) (φ := φ) hs σ 0).2).1
  | succ k ih =>
    show app (app (M.cval natAddName φ) X)
        (app (M.cval natSuccName φ) (succIter (M.cval natSuccName φ) (M.cval natZeroName φ) k)) =
      app (M.cval natSuccName φ) (succIter (M.cval natSuccName φ) X k)
    rw [(law X _ hX (natLit_val (M := M) (φ := φ) hs σ k).2).2, ih]

/-- **`Nat.add`'s first argument is in `Nat`'s set** wherever the application is graded: the
stored `Nat.add` is a graph (`never` datum), and a graph fixes its domain. -/
theorem natAdd_arg_mem {cv : ConstantVal md} {v : Expr md} {hint : ReducibilityHint}
    (hfA : env.find? natAddName = some (.defnInfo cv v hint)) (hl : cv.levelParams = [])
    {r1 : Nat} {B1 : V → V} (hm : M.cval natAddName φ ∈ˢ piR r1 (M.cval natName φ) B1)
    (hr1 : r1 ≠ 0) {σ : Nat → V} {us : List Level} {x : Expr md} {X : V}
    (hg : Gr M φ σ (.app (.const natAddName us) x)) (hX : Den M φ σ x X) :
    X ∈ˢ M.cval natName φ := by
  obtain ⟨-, -, r, A, F, X', B, hF, hX', hmF, hx, -⟩ := Gr.app_iff.1 hg
  obtain rfl := mono_head (ci := .defnInfo cv v hint) hfA hl hF
  obtain rfl := DenotesO.functional hX' hX
  exact mem_dom_pos hr1 hmF hm hx

/-- The frame and leaves of `b + k` as the offset moves write it. -/
theorem natAddLit_frame {d k : Nat} {b : Expr md} (hb : Frame d b) :
    Frame d (natAddLit b k) ∧ LeavesSub (natAddLit b k) b := by
  unfold natAddLit
  split
  · exact ⟨hb, fun _ h => h⟩
  · refine ⟨Frame.app_iff.2 ⟨Frame.app_iff.2 ⟨Frame.of_closed rfl rfl, hb⟩,
      Frame.of_closed rfl rfl⟩, fun l hl => ?_⟩
    simpa [Expr.fvarLeaves] using hl

/-- **An offset's successor step** (`Red.natAddSucc`): `b + (k + 1) = succ (b + k)`. -/
theorem Red.natAddSucc_sound {d : Nat} {us : List Level} {b : Expr md} {k : Nat}
    (hs : natLitSupported env = true) (ht : natAddTyOk (env.find? natAddName) = true) :
    RedS M φ d (.app (.app (.const natAddName us) b) (.lit (.natVal (k + 1))))
      (.app (.const natSuccName []) (natAddLit b k)) := by
  intro hfr
  obtain ⟨hfAb, -⟩ := Frame.app_iff.1 hfr
  obtain ⟨-, hfb⟩ := Frame.app_iff.1 hfAb
  obtain ⟨hfl, hsubl⟩ := natAddLit_frame (k := k) hfb
  refine ⟨Frame.app_iff.2 ⟨Frame.of_closed rfl rfl, hfl⟩, fun l hl => ?_,
    fun σ hC v hv hg => ?_⟩
  · simp only [Expr.fvarLeaves, List.nil_append] at hl
    have := hsubl l hl
    simp [Expr.fvarLeaves, this]
  obtain ⟨cv, val, hint, r1, B1, hfA, hl, hA, hAm, hr1, hB1⟩ :=
    natAdd_basis (M := M) (φ := φ) hs ht σ
  obtain ⟨r, B, hN, -, hS, -, hSm, hBN, hP⟩ := nat_basis (M := M) (φ := φ) hs σ
  obtain ⟨hgAb, -, -⟩ := Gr.app_iff.1 hg
  obtain ⟨-, hgb, -⟩ := Gr.app_iff.1 hgAb
  cases hv with
  | app hAb hL =>
    cases hAb with
    | @app _ _ _ F X hA' hX =>
      obtain rfl := mono_head (ci := .defnInfo cv val hint) hfA hl hA'
      have hXN := natAdd_arg_mem hfA hl hAm hr1 hgAb hX
      obtain rfl := DenotesO.functional hL ((natLit_val (M := M) (φ := φ) hs σ (k + 1)).1 ρ₀)
      have hLk := natLit_val (M := M) (φ := φ) hs σ k
      have hsum := natAdd_lit (M := M) (φ := φ) hs hfA hl σ hXN
      rw [hsum (k + 1)]
      -- the reduct
      obtain ⟨r2, B2, hY2, hB2N, hP2⟩ := hB1 _ hXN
      have hden : Den M φ σ (natAddLit b k) (succIter (M.cval natSuccName φ) X k) ∧
          Gr M φ σ (natAddLit b k) ∧
          succIter (M.cval natSuccName φ) X k ∈ˢ M.cval natName φ := by
        by_cases hk : k = 0
        · subst hk
          rw [natAddLit, if_pos rfl]
          exact ⟨hX, hgb, hXN⟩
        · rw [natAddLit, if_neg hk]
          have hm1 : app (M.cval natAddName φ) X ∈ˢ piR r2 (M.cval natName φ) B2 := by
            rw [← hY2]
            exact app_mem_piR_pos hr1 hAm hXN
          have hm2 := app_mem_piR hm1 hLk.2 (by rw [← univ_zero]; exact hP2)
          rw [hB2N _ hLk.2, hsum k] at hm2
          refine ⟨?_, Gr.app_iff.2 ⟨Gr.app_iff.2 ⟨True.intro, hgb, _, _, _, _, B1, hA ρ₀, hX, hAm,
            hXN, fun h0 => absurd h0 hr1⟩, True.intro, _, _, _, _, B2, .app (hA ρ₀) hX,
            hLk.1 ρ₀, hm1, hLk.2, hP2⟩, hm2⟩
          rw [← hsum k]
          exact .app (.app (hA ρ₀) hX) (hLk.1 ρ₀)
      refine ⟨.app (hS ρ₀) hden.1, Gr.app_iff.2 ⟨True.intro, hden.2.1, _, _, _, _, B, hS ρ₀,
        hden.1, hSm, hden.2.2, hP⟩⟩

/-- **Adding zero** (`Red.natAddZero`): `b + 0 = b`. -/
theorem Red.natAddZero_sound {d : Nat} {us : List Level} {b a w : Expr md}
    (hs : natLitSupported env = true) (ht : natAddTyOk (env.find? natAddName) = true)
    (hr : RedS M φ d a w) (hw : rawNatLit? w = some 0) :
    RedS M φ d (.app (.app (.const natAddName us) b) a) b := by
  intro hfr
  obtain ⟨hfAb, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨-, hfb⟩ := Frame.app_iff.1 hfAb
  obtain ⟨-, -, ka⟩ := hr hfa
  refine ⟨hfb, fun l hl => by simp [Expr.fvarLeaves, hl], fun σ hC v hv hg => ?_⟩
  obtain ⟨cv, val, hint, r1, -, hfA, hl, -, hAm, hr1, -⟩ :=
    natAdd_basis (M := M) (φ := φ) hs ht σ
  obtain ⟨hgAb, hga, -⟩ := Gr.app_iff.1 hg
  obtain ⟨-, hgb, -⟩ := Gr.app_iff.1 hgAb
  cases hv with
  | app hAb hZ =>
    cases hAb with
    | @app _ _ _ F X hA' hX =>
      obtain rfl := mono_head (ci := .defnInfo cv val hint) hfA hl hA'
      have hXN := natAdd_arg_mem hfA hl hAm hr1 hgAb hX
      obtain ⟨hZw, -⟩ := ka σ (hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]) _ hZ hga
      obtain rfl := DenotesO.functional (rawNatLit_den hw hZw)
        ((natLit_val (M := M) (φ := φ) hs σ 0).1 ρ₀)
      rw [natAdd_lit (M := M) (φ := φ) hs hfA hl σ hXN 0]
      exact ⟨hX, hgb⟩

/-! ## Offsets in conversion -/

/-- **An offset's meaning**: a framed, graded term with the offset `(base, k)` denotes
`succᵏ` of what its base denotes; the base is framed and graded, and its leaves are the
term's. -/
theorem natOffset_sem (hs : natLitSupported env = true) :
    ∀ (e : Expr md) {b : Expr md} {k : Nat}, natOffsetOf e = some (b, k) →
      (natOffsetAdd e = true → natAddTyOk (env.find? natAddName) = true) →
      ∀ {d : Nat}, Frame d e → Frame d b ∧ LeavesSub b e ∧
        ∀ (σ : Nat → V) (v : V), Den M φ σ e v → Gr M φ σ e →
          ∃ vb, Den M φ σ b vb ∧ Gr M φ σ b ∧
            v = succIter (M.cval natSuccName φ) vb k := by
  obtain ⟨_, _, _, _, _, _, _, _, -, -, hfS, -, -, hlS, -⟩ := natLitSupported_inv hs
  refine natOffsetOf_rec (fun e ih => ?_)
  intro b k h hguard d hf
  rcases natOffsetOf_some h with ⟨rfl, rfl⟩ | ⟨us, x, rfl, hx⟩ | ⟨us, x, n, rfl, hx⟩
  · -- a literal: `succᵏ 0`
    refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun σ v hv _ => ?_⟩
    obtain rfl := DenotesO.functional hv ((natLit_val (M := M) (φ := φ) hs σ k).1 ρ₀)
    refine ⟨_, (natLit_val (M := M) (φ := φ) hs σ 0).1 ρ₀, True.intro, ?_⟩
    rfl
  · -- `Nat.succ x`
    have hfx : Frame d x := (Frame.app_iff.1 hf).2
    have hsubx : LeavesSub x (.app (.const natSuccName us) x) :=
      fun l hl => by simp [Expr.fvarLeaves, hl]
    have haddx : natOffsetAdd x = true → natAddTyOk (env.find? natAddName) = true :=
      fun h' => hguard (by rw [natOffsetAdd_succ, if_pos rfl]; exact h')
    rcases natOffsetStep_eq hx with ⟨k', hx', rfl⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨hfb, hsubb, kx⟩ := ih x (Or.inl ⟨us, rfl⟩) hx' haddx hfx
      refine ⟨hfb, fun l hl => hsubx l (hsubb l hl), fun σ v hv hg => ?_⟩
      obtain ⟨-, hgx, -⟩ := Gr.app_iff.1 hg
      cases hv with
      | app hF hX =>
        obtain rfl := mono_head (ci := .ctorInfo _ _ _) hfS hlS hF
        obtain ⟨vb, hvb, hgb, rfl⟩ := kx σ _ hX hgx
        exact ⟨vb, hvb, hgb, rfl⟩
    · refine ⟨hfx, hsubx, fun σ v hv hg => ?_⟩
      obtain ⟨-, hgx, -⟩ := Gr.app_iff.1 hg
      cases hv with
      | app hF hX =>
        obtain rfl := mono_head (ci := .ctorInfo _ _ _) hfS hlS hF
        exact ⟨_, hX, hgx, rfl⟩
  · -- `Nat.add x (lit n)`: the split reads the stored `Nat.add`
    have ht : natAddTyOk (env.find? natAddName) = true :=
      hguard (by rw [natOffsetAdd_add, if_pos rfl])
    have hfAx : Frame d (.app (.const natAddName us) x) := (Frame.app_iff.1 hf).1
    have hfx : Frame d x := (Frame.app_iff.1 hfAx).2
    have hsubx : LeavesSub x (.app (.app (.const natAddName us) x) (.lit (.natVal n))) :=
      fun l hl => by simp [Expr.fvarLeaves, hl]
    have hsem : ∀ (σ : Nat → V) (v : V),
        Den M φ σ (.app (.app (.const natAddName us) x) (.lit (.natVal n))) v →
        Gr M φ σ (.app (.app (.const natAddName us) x) (.lit (.natVal n))) →
        ∃ X, Den M φ σ x X ∧ Gr M φ σ x ∧ v = succIter (M.cval natSuccName φ) X n := by
      intro σ v hv hg
      obtain ⟨cv, val, hint, r1, -, hfA, hl, -, hAm, hr1, -⟩ :=
        natAdd_basis (M := M) (φ := φ) hs ht σ
      obtain ⟨hgAx, -, -⟩ := Gr.app_iff.1 hg
      obtain ⟨-, hgx, -⟩ := Gr.app_iff.1 hgAx
      cases hv with
      | app hAx hL =>
        cases hAx with
        | app hA' hX =>
          obtain rfl := mono_head (ci := .defnInfo cv val hint) hfA hl hA'
          have hXN := natAdd_arg_mem hfA hl hAm hr1 hgAx hX
          obtain rfl := DenotesO.functional hL ((natLit_val (M := M) (φ := φ) hs σ n).1 ρ₀)
          exact ⟨_, hX, hgx, natAdd_lit (M := M) (φ := φ) hs hfA hl σ hXN n⟩
    rcases natOffsetStep_eq hx with ⟨k', hx', rfl⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨hfb, hsubb, kx⟩ := ih x (Or.inr ⟨us, n, rfl⟩) hx' (fun _ => ht) hfx
      refine ⟨hfb, fun l hl => hsubx l (hsubb l hl), fun σ v hv hg => ?_⟩
      obtain ⟨X, hX, hgx, rfl⟩ := hsem σ v hv hg
      obtain ⟨vb, hvb, hgb, rfl⟩ := kx σ X hX hgx
      exact ⟨vb, hvb, hgb, succIter_add _ _ k' n⟩
    · exact ⟨hfx, hsubx, hsem⟩

/-- **Equal offsets** (`DefEq.natOffset`): both sides are `succᵏ` of their bases, and the
bases denote alike. -/
theorem DefEq.natOffset_sound {d : Nat} {a b ba bb : Expr md} {k : Nat}
    (hs : natLitSupported env = true)
    (ht : natOffsetAdd a = true ∨ natOffsetAdd b = true →
      natAddTyOk (env.find? natAddName) = true)
    (ha : natOffsetOf a = some (ba, k)) (hb : natOffsetOf b = some (bb, k))
    (h : DefEqS M φ d ba bb) : DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb v w hv hw hga hgb
  obtain ⟨hfA, hsubA, kA⟩ :=
    natOffset_sem (M := M) (φ := φ) hs a ha (fun h' => ht (Or.inl h')) hfa
  obtain ⟨hfB, hsubB, kB⟩ :=
    natOffset_sem (M := M) (φ := φ) hs b hb (fun h' => ht (Or.inr h')) hfb
  obtain ⟨xa, hxa, hgxa, rfl⟩ := kA σ v hv hga
  obtain ⟨xb, hxb, hgxb, rfl⟩ := kB σ w hw hgb
  rw [h hfA hfB σ (hCa.of_subset hsubA) (hCb.of_subset hsubB) xa xb hxa hxb hgxa hgxb]

end Ix.Kernel.Open
