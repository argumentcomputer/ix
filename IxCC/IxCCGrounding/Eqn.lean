import IxCCGrounding.Apply

/-!
# The `eqn` lemma (`IxCCGrounding.Eqn`)

**In every model, at every level assignment, a function whose equation theorem is stored with the
checked shape (`EqnShape`) denotes its equation body** `λ Ds. rhs` (`eqn_den`). Any telescope of
arguments, any result type. No law and no typing hypothesis: only `mem` of the function, of the
theorem and of `Eq`, and `eq_equality`.

* The theorem's membership in its stored type makes `@Eq T (f xs) rhs` inhabited at every
  arguments `xs` in the binders' domains.
* `Eq`'s membership in its stored type makes its denotation a graph over `univ u`, then over `⟦T⟧`
  twice. A graph applied off its domain is empty, so inhabitation forces `⟦T⟧`, `⟦f xs⟧` and
  `⟦rhs⟧` into their domains, and then `eq_equality` makes the two sides equal (`eq_of_inhabited`).
* The function's membership in its stored type, a `∀`-telescope over the same domains, makes it a
  graph (or the proof point) at each binder, and extensionality of graphs gives the `λ`
  (`eqn_tele`, by induction on the telescope).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (CId)

universe w

variable {V : Type w}

/-! ## Environments with several bound sets -/

/-- `xs` bound in order, the last innermost: index `i < xs.length` reads `xs[n-1-i]` (the
reversed list), and the indices above read `ρ`. -/
def pushAll (xs : List V) (ρ : BVarIdx → V) : BVarIdx → V := fun i =>
  xs.reverse.getD i (ρ (i - xs.length))

theorem pushAll_nil (ρ : BVarIdx → V) : pushAll [] ρ = ρ := by
  funext i; simp [pushAll]

theorem pushAll_snoc (xs : List V) (x : V) (ρ : BVarIdx → V) :
    pushAll (xs ++ [x]) ρ = push x (pushAll xs ρ) := by
  funext i
  cases i with
  | zero => simp [pushAll, push]
  | succ i =>
    simp only [pushAll, push, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.getD_cons_succ, List.length_append,
      List.length_singleton]
    show xs.reverse.getD i (ρ (i + 1 - (xs.length + 1))) = xs.reverse.getD i (ρ (i - xs.length))
    rw [Nat.add_sub_add_right]

theorem pushAll_rev (xs : List V) (ρ : BVarIdx → V) (j : Nat) (hj : j < xs.length) :
    pushAll xs ρ (xs.length - 1 - j) = xs[j] := by
  simp only [pushAll]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some,
    List.getElem_reverse]
  congr 1
  omega

variable [Ix.Kernel.SetTheory V] {env : KEnv}

/-- `n` consecutive variables from `k`, applied to a head, denote the head applied to the sets
the environment holds there. -/
theorem den_mkAppN_bvars {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} (k : Nat) :
    ∀ (xs : List V) (g : KExpr) (G : V),
      (∀ j (h : j < xs.length), ρ (k + xs.length - 1 - j) = xs[j]) →
      Denotes cval env φ ρ g G →
      Denotes cval env φ ρ (Expr.mkAppN g (bvarsFrom k xs.length)) (xs.foldl app G)
  | [], g, G, _, hg => by simpa [bvarsFrom, Expr.mkAppN] using hg
  | x :: xs, g, G, hρ, hg => by
    have hb : bvarsFrom k (xs.length + 1) = .bvar (k + xs.length) :: bvarsFrom k xs.length := by
      simp [bvarsFrom, List.range_succ]
    simp only [List.length_cons, hb, Expr.mkAppN, List.foldl_cons]
    have h0 : ρ (k + xs.length) = x := by
      have := hρ 0 (by simp)
      simpa using this
    refine den_mkAppN_bvars k xs _ _ (fun j hj => ?_) (.app hg (h0 ▸ .bvar))
    have := hρ (j + 1) (by simp; omega)
    have e : k + (x :: xs).length - 1 - (j + 1) = k + xs.length - 1 - j := by simp; omega
    rw [e] at this
    simpa using this

/-! ## Inhabited `Eq` -/

/-- **An inhabited `@Eq.{u} T a b` makes `a` and `b` denote the same set, and its member is the
proof point** (`Model.mem` of `Eq`, read through `EqBasis`, and `Model.eq_equality`: the
proposition denotes `eqv x x`, a truth value). -/
theorem eq_of_inhabited_pt (M : Model V env) (hEq : EqBasis env) {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {u : Level} {T a b : KExpr} {X y : V}
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const eqName [u]) [T, a, b]) X) (hy : y ∈ˢ X) :
    (∃ x, Denotes M.cval env φ ρ a x ∧ Denotes M.cval env φ ρ b x) ∧ y = pt := by
  obtain ⟨ciE, hfE, hlE, htE⟩ := hEq
  simp only [Expr.mkAppN] at hX
  obtain ⟨E3, xb, hE3, hb, rfl⟩ := den_app.mp hX
  obtain ⟨E2, xa, hE2, ha, rfl⟩ := den_app.mp hE3
  obtain ⟨E, A, hE, hA, rfl⟩ := den_app.mp hE2
  have hE' := hE
  cases hE' with
  | const hf' _ =>
    rw [hfE] at hf'
    cases hf'
    rw [hlE] at hE
    obtain ⟨TE, hTE, hEm⟩ := mem_key M hfE (Level.substFn φ [0] [u]) ρ
    rw [htE] at hTE
    unfold eqType at hTE
    rw [hlE] at hy
    have hv : regime (Level.substFn φ [0] [u]) bmN.pw ≠ 0 := by simp [bmN, regime_never]
    obtain ⟨AU, BU, hAU, hBU, _, hTEe⟩ := den_pi.mp hTE
    obtain rfl := den_sort.mp hAU
    rw [hTEe] at hEm
    have hU : A ∈ˢ univ (Level.eval (Level.substFn φ [0] [u]) (.param 0)) := by
      refine Classical.byContradiction fun hn => ?_
      rw [app_off_dom_piR_pos hv hEm hn, app_empty, app_empty] at hy
      exact not_mem_empty _ hy
    have m1 := app_mem_piR_pos hv hEm hU
    obtain ⟨B1d, B1f, hB1d, hB1f, _, hB1e⟩ := den_pi.mp (hBU A hU)
    have eB1 : B1d = A := den_bvar.mp hB1d
    rw [hB1e, eB1] at m1
    have hv1 : regime (Level.substFn φ [0] [u]) bmN.pw ≠ 0 := hv
    have haA : xa ∈ˢ A := by
      refine Classical.byContradiction fun hn => ?_
      rw [app_off_dom_piR_pos hv1 m1 hn, app_empty] at hy
      exact not_mem_empty _ hy
    have m2 := app_mem_piR_pos hv1 m1 haA
    obtain ⟨B2d, B2f, hB2d, _, _, hB2e⟩ := den_pi.mp (hB1f xa (eB1 ▸ haA))
    have eB2 : B2d = A := den_bvar.mp hB2d
    rw [hB2e, eB2] at m2
    have hbA : xb ∈ˢ A := by
      refine Classical.byContradiction fun hn => ?_
      rw [app_off_dom_piR_pos hv1 m2 hn] at hy
      exact not_mem_empty _ hy
    have hAu : A ∈ˢ univ (Level.eval φ u) := by
      simpa [Level.substFn, Level.eval] using hU
    have heq := M.eq_equality u φ ρ _ A xa xb hE hAu haA hbA
    rw [heq] at hy
    obtain rfl := mem_eqv hy
    exact ⟨⟨xa, ha, hb⟩, mem_univ_zero (eqv_mem_univ xa xa) hy⟩

/-- **An inhabited `@Eq.{u} T a b` makes `a` and `b` denote the same set.** -/
theorem eq_of_inhabited (M : Model V env) (hEq : EqBasis env) {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {u : Level} {T a b : KExpr} {X y : V}
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const eqName [u]) [T, a, b]) X) (hy : y ∈ˢ X) :
    ∃ x, Denotes M.cval env φ ρ a x ∧ Denotes M.cval env φ ρ b x :=
  (eq_of_inhabited_pt M hEq hX hy).1

/-! ## The telescope -/

/-- A use of a constant at its own level parameters denotes its `cval` at the assignment. -/
theorem substFn_self (φ : LevelParam → Nat) :
    ∀ ps : List LevelParam, Level.substFn φ ps (ps.map Level.param) = φ
  | [] => funext fun _ => rfl
  | p :: ps => by
    funext n
    simp only [List.map_cons, Level.substFn]
    by_cases h : p = n
    · subst h; simp [Level.eval]
    · simp [h, substFn_self φ ps]

/-- Domain, the theorem's binder datum, the function's binder datum. -/
abbrev TeleB := KExpr × BinderMeta × BinderMeta

/-- The theorem's telescope. -/
def teleT : List TeleB → List (KExpr × BinderMeta)
  | [] => []
  | (D, mT, _) :: bs => (D, mT) :: teleT bs

/-- The function's telescope (the equation body's binders). -/
def teleF : List TeleB → List (KExpr × BinderMeta)
  | [] => []
  | (D, _, mF) :: bs => (D, mF) :: teleF bs

theorem tele_zip : ∀ (Ds : List (KExpr × BinderMeta)) (ms : List BinderMeta),
    Ds.length = ms.length →
    teleT ((Ds.zip ms).map fun p => (p.1.1, p.1.2, p.2)) = Ds ∧
    teleF ((Ds.zip ms).map fun p => (p.1.1, p.1.2, p.2)) = Ds.zipWith (fun b m => (b.1, m)) ms
  | [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | (D, m) :: Ds, m' :: ms, h => by
    obtain ⟨h1, h2⟩ := tele_zip Ds ms (by simpa using h)
    simp [List.zip_cons_cons, teleT, teleF, h1, h2]

/-- **The telescope induction**: at a stage where the sets `pre` have been bound, the theorem's
value applied to them inhabits the rest of its statement and the function's value applied to them
is a member of the rest of its type; then the rest of the equation body denotes the function's
value applied to them. -/
theorem eqn_tele (M : Model V env) (hEq : EqBasis env) {φ : LevelParam → Nat}
    (ρ0 : BVarIdx → V) {n : Nat} {u : Level} {T rhs R : KExpr} {fk : KKey} {us : List Level}
    {F P : V} (hfk : ∀ ρ, Denotes M.cval env φ ρ (.const fk us) F) :
    ∀ (bs : List TeleB) (pre : List V), pre.length + bs.length = n →
      ∀ {TT TF : V},
      Denotes M.cval env φ (pushAll pre ρ0)
        (piTele (teleT bs) (Expr.mkAppN (.const eqName [u])
          [T, Expr.mkAppN (.const fk us) (bvarsFrom 0 n), rhs])) TT →
      pre.foldl app P ∈ˢ TT →
      Denotes M.cval env φ (pushAll pre ρ0) (piTele (teleF bs) R) TF →
      pre.foldl app F ∈ˢ TF →
      Denotes M.cval env φ (pushAll pre ρ0) (lamTele (teleF bs) rhs) (pre.foldl app F)
  | [], pre, hlen, TT, TF, hTT, hP, _, _ => by
    simp only [teleT, teleF, piTele, lamTele] at hTT ⊢
    obtain ⟨x, hx, hr⟩ := eq_of_inhabited M hEq hTT hP
    have hl : pre.length = n := by simpa using hlen
    have hfx : Denotes M.cval env φ (pushAll pre ρ0)
        (Expr.mkAppN (.const fk us) (bvarsFrom 0 n)) (pre.foldl app F) := by
      subst hl
      refine den_mkAppN_bvars 0 pre _ _ (fun j hj => ?_) (hfk _)
      rw [Nat.zero_add]
      exact pushAll_rev pre ρ0 j hj
    obtain rfl := Denotes_functional hx hfx
    exact hr
  | (D, mT, mF) :: bs, pre, hlen, TT, TF, hTT, hP, hTF, hF => by
    simp only [teleT, teleF, piTele, lamTele] at hTT hTF ⊢
    have hTF0 := hTF
    obtain ⟨A, BF, hA, hBF, _, rfl⟩ := den_pi.mp hTF
    have step : ∀ x, x ∈ˢ A → Denotes M.cval env φ (push x (pushAll pre ρ0))
        (lamTele (teleF bs) rhs) (app (pre.foldl app F) x) := by
      intro x hx
      obtain ⟨BTx, hBTx, hPx⟩ := app_mem_den_pi hTT hA hP hx
      obtain ⟨BFx, hBFx, hFx⟩ := app_mem_den_pi hTF0 hA hF hx
      have e1 := pushAll_snoc pre x ρ0
      have e2 : (pre ++ [x]).foldl app F = app (pre.foldl app F) x := by simp
      have e3 : (pre ++ [x]).foldl app P = app (pre.foldl app P) x := by simp
      have ih := eqn_tele M hEq ρ0 (n := n) hfk bs (pre ++ [x]) (by simp at hlen ⊢; omega)
        (TT := BTx) (TF := BFx) (by rw [e1]; exact hBTx) (by rw [e3]; exact hPx)
        (by rw [e1]; exact hBFx) (by rw [e2]; exact hFx)
      rwa [e1, e2] at ih
    have hlam := Denotes.lam (m := mF) hA step (fun h0 x _ => by
      show app (pre.foldl app F) x = pt
      have hz : pre.foldl app F ∈ˢ piR 0 A BF := by rw [← h0]; exact hF
      rw [eq_pt_of_mem_piR_zero hz, app_pt])
    have heq : lamR (regime φ mF.pw) A (fun x => app (pre.foldl app F) x) = pre.foldl app F := by
      by_cases h0 : regime φ mF.pw = 0
      · have hz : pre.foldl app F ∈ˢ piR 0 A BF := by rw [← h0]; exact hF
        rw [h0, lamR_zero]
        exact (eq_pt_of_mem_piR_zero hz).symm
      · exact eq_of_mem_piR_app_eq (lamR_mem (B := BF) fun x hx => app_mem_piR_pos h0 hF hx) hF
          fun x hx => app_lamR_pos h0 hx
    rwa [heq] at hlam

/-- **The `eqn` lemma.** -/
theorem eqn_den (M : Model V env) {κ : CId → KKey} {c thm : CId} {d : EqnData}
    (hS : EqnShape env κ c thm d) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ d.body (M.cval (κ c) φ) := by
  obtain ⟨hEq, ciF, cvT, pf, hfF, hfT, hlen, hlps, htT, htF⟩ := hS
  obtain ⟨hT, hF⟩ := tele_zip d.Ds d.ms hlen
  have hfk : ∀ ρ', Denotes M.cval env φ ρ' (.const (κ c) (cvT.levelParams.map Level.param))
      (M.cval (κ c) φ) := by
    intro ρ'
    have h := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ')
      (us := cvT.levelParams.map Level.param) hfF (by rw [List.length_map, hlps])
    rwa [← hlps, substFn_self] at h
  obtain ⟨TT, hTT, hPm⟩ := mem_key M hfT φ ρ
  obtain ⟨TF, hTF, hFm⟩ := mem_key M hfF φ ρ
  simp only [ConstantInfo.toConstantVal] at hTT
  have hTT' : Denotes M.cval env φ (pushAll [] ρ)
      (piTele (teleT ((d.Ds.zip d.ms).map fun p => (p.1.1, p.1.2, p.2)))
        (Expr.mkAppN (.const eqName [d.u]) [d.T, Expr.mkAppN (.const (κ c)
          (cvT.levelParams.map Level.param)) (bvarsFrom 0 d.Ds.length), d.rhs])) TT := by
    rw [pushAll_nil, hT, ← htT]; exact hTT
  have hTF' : Denotes M.cval env φ (pushAll [] ρ)
      (piTele (teleF ((d.Ds.zip d.ms).map fun p => (p.1.1, p.1.2, p.2))) d.R) TF := by
    rw [pushAll_nil, hF, ← htF]; exact hTF
  have h := eqn_tele M hEq ρ hfk _ [] (by simp [List.length_zip, hlen]) hTT' hPm hTF' hFm
  rw [pushAll_nil, hF] at h
  simpa [EqnData.body] using h

end IxCC.Grounding
