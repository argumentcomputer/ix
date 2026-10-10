import Ix.CompileCert.Opt.O6
import Ix.CompileCert.Opt.Subst

/-!
# M7 L3-def: O3, `casesOn` over a permuted or split block (`Ix/Compile/Pass/Opt/O3.lean`)

The docstring's *Faithfulness (definitional)*: "Lean's `x.casesOn := λ ps motive is t mins.
x.rec ps M⃗ N⃗ is t` … Pass 2 builds `ρ.casesOn` by the same construction on `x`'s canonical
component: `ρ.casesOn := λ ps motive is t mins. ρ ps M⃗′ N⃗′ is t`. … The constant motives and
minors of the other members are Lean's and Pass 2's same terms …, so `M⃗″ = M⃗′` and
`N⃗″ ≡β N⃗′` … Hence `img(x.casesOn) a⃗ ≡ ρ ps M⃗′ N⃗′ is t ≡δβ ρ.casesOn a⃗`."

Restated over `Ix.Compile.Pass.Opt.O3.apply` (unfolded) as **`O3_faithful`**, given `CasesOnLaw`:

* Lean's `x.casesOn.{us}` δ-reduces to `mkCasesOn` over `x.rec.{us}` with slot terms `M⃗`, `N⃗`
  (`CasesOnBody`), `x.rec.{us}` to its image with minor terms `mins` (`ImageAt`), and Pass 2's
  `ρ.casesOn.{ℓs}` to `mkCasesOn` over `ρ.{ℓs}` with slot terms `M⃗′`, `N⃗′`;
* the slot correspondence (AuxLaws, OD5): `M⃗′` is the shape's selection of `M⃗`, and each
  `N′ₖ` converts to the image's minor `k` with Lean's casesOn slot terms substituted (for a
  minor variable: Lean's `N_{σ′k}`, by `refl`; for a minor the image wraps, Def 3.4 step 4: the
  β-steps that discard the hypotheses, the docstring's `N⃗″ ≡β N⃗′`).

`O3_some`, `O3.Side`, `O3_side`: the decomposition and the side condition.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal InductiveVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-! ## `mkCasesOn` -/

/-- Position `p` of `casesOn`'s telescope `ps motive is t mins` (`nc` minors). -/
def casesTv (np ni nc p : Nat) : Tm := .bvar (np + 1 + ni + 1 + nc - 1 - p)

/-- The arguments of the recursor in `casesOn`'s body: `ps M⃗ N⃗ is t`. -/
def casesBody (np ni nc : Nat) (M N : List Tm) : List Tm :=
  (List.range np).map (casesTv np ni nc) ++ M ++ N ++
    (List.range (ni + 1)).map (fun i => casesTv np ni nc (np + 1 + i))

/-- `v` is `mkCasesOn` over `c.{us}` with the motive and minor slot terms `M`, `N`. -/
def CasesOnBody (c : Name) (us : Array Level) (np ni nc : Nat) (M N : List Tm) (v : Tm) : Prop :=
  ∃ ts, ts.length = np + 1 + ni + 1 + nc ∧
    v = lamN ts (Tm.appN (.const c us) (casesBody np ni nc M N))

/-- **`CasesOnLaw`** (Def 3.5, Lean's `mkCasesOn`; AuxLaws: Pass 2's `ρ.casesOn`, slotwise). -/
def CasesOnLaw (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (h r x ixCases : Name) (b : OptBlock) (s : RecShape) (iv : InductiveVal) (us : Array Level),
    classify h = some (.kCasesOn, r) → casesOnMember h = some x → env.blockOf h = some b →
    b.shapes.get? r = some s → env.const? x = some (.inductInfo iv) →
    ixAuxOf s.ixRec .kCasesOn = some ixCases → env.resolves ixCases = true →
    ShapeWF s ∧
    ∃ (v₁ v₂ v₃ : Tm) (M N M' N' mins : List Tm),
      Γ.ax (.const h us) v₁ ∧ CasesOnBody r us s.np s.ni iv.ctors.size M N v₁ ∧
      M.length = s.nm ∧ N.length = s.nmin ∧
      Γ.ax (.const r us) v₂ ∧ ImageAt s (s.levelsAt us) mins v₂ ∧
      Γ.ax (.const ixCases (s.levelsAt us)) v₃ ∧
      CasesOnBody s.ixRec (s.levelsAt us) s.np s.ni iv.ctors.size M' N' v₃ ∧
      M' = s.motiveSrc.toList.map (fun m => M.getD m (.bvar 0)) ∧
      Forall2 (Conv Γ) (mins.map (betaN (casesBody s.np s.ni iv.ctors.size M N))) N'

/-! ## The decomposition -/

theorem kind_casesOn {k : AuxKind} (hk : ¬ (k != .kCasesOn) = true) : k = .kCasesOn := by
  cases k
  all_goals first | rfl | exact absurd rfl hk

theorem eq_of_not_bne {a b : Nat} (h : ¬ (a != b) = true) : a = b := by
  have hab : (a == b) = true := by
    cases hb : (a == b)
    · exact absurd (by simp [bne, hb]) h
    · rfl
  exact beq_iff_eq.mp hab

theorem bool_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- What a firing of O3 established. -/
theorem O3_some {env : OptEnv} {o : Occ} {e : Expr} (h : O3.apply env o = some e) :
    ∃ r x b s iv ls ixCases, classify o.head = some (.kCasesOn, r) ∧ casesOnMember o.head = some x ∧
      env.blockOf o.head = some b ∧ b.change.collapse = false ∧
      (∃ cls, b.classOf.get? x = some cls ∧ cls.size = 1) ∧
      b.shapes.get? r = some s ∧ env.const? x = some (.inductInfo iv) ∧
      standardTelescope env s .kCasesOn o.head iv.ctors.size =
        some (s.np + 1 + s.ni + 1 + iv.ctors.size) ∧
      s.np + 1 + s.ni + 1 + iv.ctors.size ≤ o.args.size ∧ O5.levels s o.us = some ls ∧
      ixAuxOf s.ixRec .kCasesOn = some ixCases ∧ env.resolves ixCases = true ∧
      e = mkAppN (Expr.mkConst ixCases ls) o.args := by
  unfold O3.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨x, hx, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hcol, h⟩ := oguard h
  obtain ⟨cls, hcls, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsize, h⟩ := oguard h
  obtain ⟨s, hs, h⟩ := obind.1 h
  try dsimp only at h
  split at h
  · rename_i iv hiv
    obtain ⟨n, hn, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨hsz, h⟩ := oguard h
    obtain ⟨ls, hls, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨ixCases, hix, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨hres, h⟩ := oguard h
    simp only [pure, Option.some.injEq] at h
    have he : e = mkAppN (Expr.mkConst ixCases ls) o.args := h.symm
    have hk' : k = .kCasesOn := kind_casesOn hk
    subst hk'
    have hn' : n = s.np + 1 + s.ni + 1 + iv.ctors.size := standardTelescope_eq hn
    subst hn'
    exact ⟨r, x, b, s, iv, ls, ixCases, hc, hx, hb, bool_false hcol, ⟨cls, hcls, eq_of_not_bne hsize⟩,
      hs, hiv, hn, by omega, hls, hix, bnot_false hres, he⟩
  · cases h

/-- **O3's side condition** (the docstring's list). -/
def O3.Side (env : OptEnv) (o : Occ) : Prop :=
  ∃ r x b s iv ls ixCases, classify o.head = some (.kCasesOn, r) ∧ casesOnMember o.head = some x ∧
    env.blockOf o.head = some b ∧ b.change.collapse = false ∧
    (∃ cls, b.classOf.get? x = some cls ∧ cls.size = 1) ∧
    b.shapes.get? r = some s ∧ env.const? x = some (.inductInfo iv) ∧
    standardTelescope env s .kCasesOn o.head iv.ctors.size = some (s.np + 1 + s.ni + 1 + iv.ctors.size) ∧
    s.np + 1 + s.ni + 1 + iv.ctors.size ≤ o.args.size ∧ O5.levels s o.us = some ls ∧
    ixAuxOf s.ixRec .kCasesOn = some ixCases ∧ env.resolves ixCases = true

theorem O3_side {env : OptEnv} {o : Occ} {e : Expr} (h : O3.apply env o = some e) : O3.Side env o := by
  obtain ⟨r, x, b, s, iv, ls, ixCases, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := O3_some h
  exact ⟨r, x, b, s, iv, ls, ixCases, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## The conversion -/

theorem getD_range_map {n p : Nat} {f : Nat → Tm} {d : Tm} (h : p < n) :
    ((List.range n).map f).getD p d = f p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some]

theorem casesBody_length {np ni nc : Nat} {M N : List Tm} :
    (casesBody np ni nc M N).length = np + M.length + N.length + (ni + 1) := by
  simp only [casesBody, List.length_append, List.length_map, List.length_range]

/-- The two `ρ`-spines of the `casesOn` square agree argument by argument: Pass 2's slot terms
with the arguments substituted, against the image's body with Lean's slot terms and the
arguments substituted. -/
theorem casesOn_middle {Γ : Env} (hΓ : Γ.InstClosed) {s : RecShape} {nc : Nat}
    {M N M' N' mins A : List Tm} (hwf : ShapeWF s) (hM : M.length = s.nm) (hN : N.length = s.nmin)
    (hmrng : ∀ t ∈ mins, t.range ≤ s.arity)
    (hM' : M' = s.motiveSrc.toList.map (fun m => M.getD m (.bvar 0)))
    (hN' : Forall2 (Conv Γ) (mins.map (betaN (casesBody s.np s.ni nc M N))) N') :
    Forall2 (Conv Γ) ((casesBody s.np s.ni nc M' N').map (betaN A))
      ((shapeArgs s mins).map (betaN ((casesBody s.np s.ni nc M N).map (betaN A)))) := by
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have hK : (casesBody s.np s.ni nc M N).length = s.arity := by
    rw [casesBody_length, hM, hN]; omega
  have hKA : ((casesBody s.np s.ni nc M N).map (betaN A)).length = s.arity := by
    rw [List.length_map, hK]
  -- a telescope position of the image, substituted
  have hpos : ∀ p, p < s.arity → betaN ((casesBody s.np s.ni nc M N).map (betaN A)) (shapeTv s p) =
      betaN A ((casesBody s.np s.ni nc M N).getD p (.bvar 0)) := by
    intro p hp
    have e1 := betaN_tv (A := (casesBody s.np s.ni nc M N).map (betaN A)) (p := p) (by rw [hKA]; exact hp)
    rw [hKA] at e1
    have e2 := getD_map_tm (l := casesBody s.np s.ni nc M N) (f := betaN A) (p := p) (d := .bvar 0)
      (d' := .bvar 0) (by rw [hK]; exact hp)
    show betaN _ (.bvar (s.arity - 1 - p)) = _
    rw [e1, e2]
  have lP : ((List.range s.np).map (casesTv s.np s.ni nc)).length = s.np := by simp
  -- the regions of Lean's slot terms
  have kP : ∀ p, p < s.np → (casesBody s.np s.ni nc M N).getD p (.bvar 0) = casesTv s.np s.ni nc p := by
    intro p hp
    have := gD4_1 (A := (List.range s.np).map (casesTv s.np s.ni nc)) (B := M) (C := N)
      (D := (List.range (s.ni + 1)).map (fun i => casesTv s.np s.ni nc (s.np + 1 + i))) (p := p) (d := .bvar 0)
      (by rw [lP]; exact hp)
    simp only [casesBody]
    rw [this, getD_range_map hp]
  have kM : ∀ m, m < s.nm → (casesBody s.np s.ni nc M N).getD (s.np + m) (.bvar 0) = M.getD m (.bvar 0) := by
    intro m hm
    have := gD4_2 (A := (List.range s.np).map (casesTv s.np s.ni nc)) (B := M) (C := N)
      (D := (List.range (s.ni + 1)).map (fun i => casesTv s.np s.ni nc (s.np + 1 + i))) (p := m) (d := .bvar 0)
      (by rw [hM]; exact hm)
    rw [lP] at this
    simp only [casesBody]
    exact this
  have kI : ∀ i, i < s.ni + 1 → (casesBody s.np s.ni nc M N).getD (s.np + s.nm + s.nmin + i) (.bvar 0) =
      casesTv s.np s.ni nc (s.np + 1 + i) := by
    intro i hi
    have := gD4_4 (A := (List.range s.np).map (casesTv s.np s.ni nc)) (B := M) (C := N)
      (D := (List.range (s.ni + 1)).map (fun i => casesTv s.np s.ni nc (s.np + 1 + i))) (p := i) (d := .bvar 0)
    rw [lP, hM, hN, getD_range_map hi] at this
    simp only [casesBody]
    exact this
  generalize hKAdef : (casesBody s.np s.ni nc M N).map (betaN A) = KA at hpos ⊢
  simp only [casesBody, shapeArgs, List.map_append]
  refine forall2_append (forall2_append (forall2_append ?_ ?_) ?_) ?_
  · -- the parameters
    apply forall2_of_eq
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hp' := List.mem_range.1 hp
    simp only [Function.comp_apply]
    rw [hpos p (by omega), kP p hp']
  · -- the motives
    apply forall2_of_eq
    rw [hM']
    simp only [List.map_map]
    apply List.map_congr_left
    intro m hm
    have hm' := hwf.motives m hm
    simp only [Function.comp_apply]
    rw [hpos (s.np + m) (by omega), kM m hm']
  · -- the minors
    have e : mins.map (betaN KA) =
        (mins.map (betaN (casesBody s.np s.ni nc M N))).map (betaN A) := by
      rw [← hKAdef, List.map_map]
      apply List.map_congr_left
      intro t ht
      have := betaN_betaN A (casesBody s.np s.ni nc M N) t (by rw [hK]; exact hmrng t ht)
      simp only [Function.comp_apply]
      exact this.symm
    rw [e]
    exact forall2_symm (forall2_mapRight (betaN A) (conv_betaN hΓ A) hN')
  · -- the indices and the major
    apply forall2_of_eq
    simp only [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [hpos (s.np + s.nm + s.nmin + i) (by omega), kI i hi']

/-- **O3 is definitional**: its output (Pass 2's `ρ.casesOn` with the occurrence's arguments)
converts to the occurrence. -/
theorem O3_faithful {Γ : Env} {env : OptEnv} (hΓ : Γ.InstClosed) (hL : CasesOnLaw Γ env)
    {o : Occ} {e : Expr} (h : O3.apply env o = some e) : ExprConv Γ e (occTerm o) := by
  obtain ⟨r, x, b, s, iv, ls, ixCases, hc, hx, hb, -, -, hs, hiv, -, hsz, hls, hix, hres, rfl⟩ :=
    O3_some h
  have hls' := O5_levels_eq hls
  subst hls'
  obtain ⟨hwf, v₁, v₂, v₃, M, N, M', N', mins, hδ₁, hv₁, hM, hN, hδ₂, hv₂, hδ₃, hv₃, hM', hN'⟩ :=
    hL o.head r x ixCases b s iv o.us hc hx hb hs hiv hix hres
  unfold ExprConv
  rw [er_occTerm, er_mkAppN, er_mkConst]
  have hL0 : s.np + 1 + s.ni + 1 + iv.ctors.size ≤ (o.args.toList.map er).length := by simpa using hsz
  generalize o.args.toList.map er = L at hL0 ⊢
  obtain ⟨ts₁, hts₁, rfl⟩ := hv₁
  obtain ⟨ts₃, hts₃, rfl⟩ := hv₃
  obtain ⟨ts₂, hts₂, -, -, hmrng, rfl⟩ := hv₂
  have c1 := delta_beta (L := L) hL0 hts₁ hδ₁
  have c3 := delta_beta (L := L) hL0 hts₃ hδ₃
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have hK : (casesBody s.np s.ni iv.ctors.size M N).length = s.arity := by
    rw [casesBody_length, hM, hN]; omega
  have hKA : ((casesBody s.np s.ni iv.ctors.size M N).map
      (betaN (L.take (s.np + 1 + s.ni + 1 + iv.ctors.size)))).length = s.arity := by
    rw [List.length_map, hK]
  have hL1 : s.arity ≤ ((casesBody s.np s.ni iv.ctors.size M N).map
      (betaN (L.take (s.np + 1 + s.ni + 1 + iv.ctors.size))) ++
      L.drop (s.np + 1 + s.ni + 1 + iv.ctors.size)).length := by
    rw [List.length_append, hKA]; omega
  have c2 := delta_beta (L := (casesBody s.np s.ni iv.ctors.size M N).map
      (betaN (L.take (s.np + 1 + s.ni + 1 + iv.ctors.size))) ++
      L.drop (s.np + 1 + s.ni + 1 + iv.ctors.size)) hL1 hts₂ hδ₂
  have htake : ((casesBody s.np s.ni iv.ctors.size M N).map
      (betaN (L.take (s.np + 1 + s.ni + 1 + iv.ctors.size))) ++ L.drop (s.np + 1 + s.ni + 1 + iv.ctors.size)).take s.arity = (casesBody s.np s.ni iv.ctors.size M N).map
      (betaN (L.take (s.np + 1 + s.ni + 1 + iv.ctors.size))) := by
    rw [← hKA]; simp
  have hdrop : ((casesBody s.np s.ni iv.ctors.size M N).map
      (betaN (L.take (s.np + 1 + s.ni + 1 + iv.ctors.size))) ++ L.drop (s.np + 1 + s.ni + 1 + iv.ctors.size)).drop s.arity = L.drop (s.np + 1 + s.ni + 1 + iv.ctors.size) := by
    rw [← hKA]; simp
  rw [htake, hdrop] at c2
  have cmid := Conv.appN_args (Γ := Γ) (.const s.ixRec (s.levelsAt o.us))
    (forall2_append (casesOn_middle (A := L.take (s.np + 1 + s.ni + 1 + iv.ctors.size)) hΓ hwf hM hN hmrng
      hM' hN') (Conv.forall₂_refl (L.drop (s.np + 1 + s.ni + 1 + iv.ctors.size))))
  exact .trans c3 (.trans cmid (.symm (.trans c1 c2)))

end Ix.CompileCert.Opt
