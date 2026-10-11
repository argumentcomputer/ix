import Ix.CompileCert.Opt.O3

/-!
# M7 L3-def: O4, `below`/`brecOn`/`.go`/`.eq` over a selection shape (`Ix/Compile/Pass/Opt/O4.lean`)

The docstring's *Faithfulness (definitional)*: "Lean builds `below`, `brecOn`, `.go`, `.eq` from
`r` by `mkBelow`/`mkBRecOn`: `r` applied to motives and minors that are functions of the user's
motives (and handlers), slot by slot … Pass 2 builds `ρ.S` by the same construction on the
canonical component. … Lean's slot term for a slot in the component is Pass 2's slot term for
the corresponding Ix slot with the motives and handlers renamed by `σ` … `img(a) a⃗ ≡ ρ.S ps
(ms∘σ) is t (Fs∘σ)`. For `.eq` (a theorem) the statement is the same equation with both sides
rewritten this way; the proof term is immaterial (proof irrelevance)."

The constructions, as Lean 4.34 builds them (checked on the box, `out/scratch/auxq.lean`):
`x.below := λ ps ms is t. x.rec.{Lv} ps Mot⃗ Min⃗ is t`, `x.brecOn.go := λ ps ms is t Fs. x.rec.{Lv}
ps Mot⃗ Min⃗ is t` (a *`rec` construction*), `x.brecOn := λ ps ms is t Fs. (x.brecOn.go ps ms is t
Fs).1` (a projection, `.proj PProd 0`), `x.brecOn.eq` a theorem.

* `RecConsSquare` (AuxLaws, slotwise): Lean's and Pass 2's `rec` constructions, with Pass 2's
  slot terms renamed into Lean's telescope (`qRen`: the motives and handlers by `σ`) convertible
  to Lean's selected slot terms; `recCons_conv`: the square converts, at any argument list;
* `BRecOnSquare`: both `brecOn`s are the projection of their `.go`, whose square holds;
  `brecOn_conv`;
* `EqPIrrel` (design D-2, a named rule of `Γ`): proof irrelevance for the `.eq` pair;
* **`O4_faithful`**, given `O4Law` (one of the three per kind).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal InductiveVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-! ## The telescopes of `below` and `brecOn` -/

/-- Position `p` of a telescope of `n` binders, as a variable of its body. -/
def tvT (n p : Nat) : Tm := .bvar (n - 1 - p)

/-- The recursor's arguments in a `rec` construction over a telescope of `n` binders: the
parameters, the motive and minor slot terms, the indices and the major. -/
def recBody (n np nm ni : Nat) (Mot Min : List Tm) : List Tm :=
  (List.range np).map (tvT n) ++ Mot ++ Min ++ (List.range (ni + 1)).map (fun i => tvT n (np + nm + i))

/-- Lean's telescope: `ps ms is t` (`below`) or `ps ms is t Fs` (the `brecOn` family). -/
def o4Len (s : RecShape) : Bool → Nat
  | false => s.np + s.nm + s.ni + 1
  | true => s.np + s.nm + s.ni + 1 + s.nm

/-- Pass 2's telescope, with `ρ`'s motives. -/
def o4LenI (s : RecShape) : Bool → Nat
  | false => s.np + s.motiveSrc.size + s.ni + 1
  | true => s.np + s.motiveSrc.size + s.ni + 1 + s.motiveSrc.size

/-- The positions of O4's output arguments `ps (ms∘σ) is t (Fs∘σ)` in Lean's telescope. -/
def o4Idx (s : RecShape) : Bool → List Nat
  | false => List.range s.np ++ s.motiveSrc.toList.map (s.np + ·) ++ (List.range (s.ni + 1)).map (s.np + s.nm + ·)
  | true => List.range s.np ++ s.motiveSrc.toList.map (s.np + ·) ++ (List.range (s.ni + 1)).map (s.np + s.nm + ·) ++
      s.motiveSrc.toList.map (s.np + s.nm + s.ni + 1 + ·)

/-- Pass 2's telescope renamed into Lean's: the variables at O4's output positions. -/
def qRen (s : RecShape) (hd : Bool) : List Tm := (o4Idx s hd).map (tvT (o4Len s hd))

theorem length_o4Idx (s : RecShape) : ∀ hd, (o4Idx s hd).length = o4LenI s hd
  | false => by simp only [o4Idx, o4LenI, List.length_append, List.length_map, List.length_range,
      Array.length_toList]; omega
  | true => by simp only [o4Idx, o4LenI, List.length_append, List.length_map, List.length_range,
      Array.length_toList]; omega

theorem o4Idx_lt {s : RecShape} (hm : ∀ m ∈ s.motiveSrc.toList, m < s.nm) :
    ∀ hd, ∀ p ∈ o4Idx s hd, p < o4Len s hd
  | false, p, hp => by
    simp only [o4Idx, List.mem_append, List.mem_map, List.mem_range] at hp
    simp only [o4Len]
    rcases hp with (hp | ⟨m, hm', rfl⟩) | ⟨i, hi, rfl⟩
    · omega
    · have := hm m hm'; omega
    · omega
  | true, p, hp => by
    simp only [o4Idx, List.mem_append, List.mem_map, List.mem_range] at hp
    simp only [o4Len]
    rcases hp with ((hp | ⟨m, hm', rfl⟩) | ⟨i, hi, rfl⟩) | ⟨m, hm', rfl⟩
    · omega
    · have := hm m hm'; omega
    · omega
    · have := hm m hm'; omega

theorem o4Idx_param {s : RecShape} {p : Nat} (hp : p < s.np) : ∀ hd, (o4Idx s hd).getD p 0 = p
  | false => by
    simp only [o4Idx]
    have h1 : p < (List.range s.np ++ s.motiveSrc.toList.map (s.np + ·)).length := by simp; omega
    have h2 : p < (List.range s.np).length := by simp; omega
    rw [getD_append_lt h1, getD_append_lt h2, getD_range hp]
  | true => by
    simp only [o4Idx]
    have h2 : p < (List.range s.np).length := by simp; omega
    rw [getD4_1 h2, getD_range hp]

theorem o4Idx_index {s : RecShape} {i : Nat} (hi : i < s.ni + 1) :
    ∀ hd, (o4Idx s hd).getD (s.np + s.motiveSrc.size + i) 0 = s.np + s.nm + i
  | false => by
    simp only [o4Idx]
    have e : (List.range s.np ++ s.motiveSrc.toList.map (s.np + ·)).length = s.np + s.motiveSrc.size := by
      simp
    have h1 : (List.range s.np ++ s.motiveSrc.toList.map (s.np + ·)).length ≤ s.np + s.motiveSrc.size + i := by
      rw [e]; omega
    rw [getD_append_ge h1, e, Nat.add_sub_cancel_left, getD_map_range hi]
  | true => by
    simp only [o4Idx]
    have := getD4_3 (A := List.range s.np) (B := s.motiveSrc.toList.map (s.np + ·))
      (C := (List.range (s.ni + 1)).map (s.np + s.nm + ·))
      (D := s.motiveSrc.toList.map (s.np + s.nm + s.ni + 1 + ·)) (p := i) (by simpa using hi)
    simp only [List.length_range, List.length_map, Array.length_toList] at this
    rw [this, getD_map_range hi]

theorem recBody_length {n np nm ni : Nat} {Mot Min : List Tm} :
    (recBody n np nm ni Mot Min).length = np + Mot.length + Min.length + (ni + 1) := by
  simp only [recBody, List.length_append, List.length_map, List.length_range]

/-- The variables of a telescope, substituted, are the arguments. -/
theorem betaN_telVars (A : List Tm) : ((List.range A.length).map (tvT A.length)).map (betaN A) = A := by
  rw [List.map_map]
  have hv := betaN_vars A (List.range A.length) (fun p hp => List.mem_range.1 hp)
  refine Eq.trans ?_ (Eq.trans hv (range_getD A (.bvar 0)))
  rfl

/-! ## The square of a `rec` construction -/

/-- **`RecConsSquare`** (AuxLaws, OD5, slotwise): Lean's `h.{us}` is a `rec` construction over
`r.{Lv}` (slot terms `Mot⃗`, `Min⃗` over Lean's telescope), `r.{Lv}` δ-reduces to its image, and
Pass 2's `ixA.{ls}` is a `rec` construction over `ρ.{ℓs[Lv]}` (slot terms `Mot⃗′`, `Min⃗′` over Pass
2's telescope, closed over it) whose slot terms, renamed into Lean's telescope, convert to Lean's
selected ones. -/
def RecConsSquare (Γ : Env) (s : RecShape) (hd : Bool) (h r ixA : Name) (us ls : Array Level) : Prop :=
  ∃ (Lv : Array Level) (v₁ v₂ v₃ : Tm) (tsL tsI Mot Min Mot' Min' : List Tm),
    Γ.ax (.const h us) v₁ ∧ tsL.length = o4Len s hd ∧ Mot.length = s.nm ∧ Min.length = s.nmin ∧
    v₁ = lamN tsL (Tm.appN (.const r Lv) (recBody (o4Len s hd) s.np s.nm s.ni Mot Min)) ∧
    Γ.ax (.const r Lv) v₂ ∧ ShapeAt s (s.levelsAt Lv) v₂ ∧
    Γ.ax (.const ixA ls) v₃ ∧ tsI.length = o4LenI s hd ∧
    v₃ = lamN tsI (Tm.appN (.const s.ixRec (s.levelsAt Lv))
      (recBody (o4LenI s hd) s.np s.motiveSrc.size s.ni Mot' Min')) ∧
    (∀ t ∈ Mot' ++ Min', t.range ≤ o4LenI s hd) ∧
    Forall2 (Conv Γ) (s.motiveSrc.toList.map (fun m => Mot.getD m (.bvar 0))) (Mot'.map (betaN (qRen s hd))) ∧
    Forall2 (Conv Γ) ((selMinors s).map (fun j => Min.getD j (.bvar 0))) (Min'.map (betaN (qRen s hd)))

/-- The two `ρ`-spines of a `rec`-construction square agree argument by argument. -/
theorem recCons_middle {Γ : Env} (hΓ : Γ.InstClosed) {s : RecShape} {hd : Bool}
    {Mot Min Mot' Min' A : List Tm} (hwf : ShapeWF s) (hMot : Mot.length = s.nm)
    (hMin : Min.length = s.nmin) (hA : A.length = o4Len s hd)
    (hrng : ∀ t ∈ Mot' ++ Min', t.range ≤ o4LenI s hd)
    (hcM : Forall2 (Conv Γ) (s.motiveSrc.toList.map (fun m => Mot.getD m (.bvar 0)))
      (Mot'.map (betaN (qRen s hd))))
    (hcN : Forall2 (Conv Γ) ((selMinors s).map (fun j => Min.getD j (.bvar 0)))
      (Min'.map (betaN (qRen s hd)))) :
    Forall2 (Conv Γ)
      ((recBody (o4LenI s hd) s.np s.motiveSrc.size s.ni Mot' Min').map (betaN ((qRen s hd).map (betaN A))))
      ((shapeIdx s).map (gL ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A)))) := by
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have hKL : (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).length = s.arity := by
    rw [recBody_length, hMot, hMin]; omega
  have hQ : (qRen s hd).length = o4LenI s hd := by rw [qRen, List.length_map, length_o4Idx]
  have hQA : ((qRen s hd).map (betaN A)).length = o4LenI s hd := by rw [List.length_map, hQ]
  -- Pass 2's telescope positions, substituted
  have hApos : ∀ q, q < o4LenI s hd → betaN ((qRen s hd).map (betaN A)) (tvT (o4LenI s hd) q) =
      betaN A (tvT (o4Len s hd) ((o4Idx s hd).getD q 0)) := by
    intro q hq
    have e1 := betaN_tv (A := (qRen s hd).map (betaN A)) (p := q) (by rw [hQA]; exact hq)
    rw [hQA] at e1
    have e2 := getD_map_tm (l := qRen s hd) (f := betaN A) (p := q) (d := .bvar 0) (d' := .bvar 0)
      (by rw [hQ]; exact hq)
    have e3 := getD_map_tm (l := o4Idx s hd) (f := tvT (o4Len s hd)) (p := q) (d := 0) (d' := .bvar 0)
      (by rw [length_o4Idx]; exact hq)
    show betaN _ (.bvar (o4LenI s hd - 1 - q)) = _
    rw [e1, e2]
    unfold qRen
    rw [e3]
  -- Lean's slot positions, substituted
  have hKpos : ∀ p, p < s.arity →
      gL ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A)) p =
        betaN A ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).getD p (.bvar 0)) := by
    intro p hp
    unfold gL
    exact getD_map_tm (by rw [hKL]; exact hp)
  have lP : ((List.range s.np).map (tvT (o4Len s hd))).length = s.np := by simp
  have kP : ∀ p, p < s.np → (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).getD p (.bvar 0) =
      tvT (o4Len s hd) p := by
    intro p hp
    have := gD4_1 (A := (List.range s.np).map (tvT (o4Len s hd))) (B := Mot) (C := Min)
      (D := (List.range (s.ni + 1)).map (fun i => tvT (o4Len s hd) (s.np + s.nm + i))) (p := p) (d := .bvar 0)
      (by rw [lP]; exact hp)
    simp only [recBody]
    rw [this, getD_range_map hp]
  have kM : ∀ m, m < s.nm → (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).getD (s.np + m) (.bvar 0) =
      Mot.getD m (.bvar 0) := by
    intro m hm
    have := gD4_2 (A := (List.range s.np).map (tvT (o4Len s hd))) (B := Mot) (C := Min)
      (D := (List.range (s.ni + 1)).map (fun i => tvT (o4Len s hd) (s.np + s.nm + i))) (p := m) (d := .bvar 0)
      (by rw [hMot]; exact hm)
    rw [lP] at this
    simp only [recBody]
    exact this
  have kN : ∀ j, j < s.nmin →
      (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).getD (s.np + s.nm + j) (.bvar 0) = Min.getD j (.bvar 0) := by
    intro j hj
    have := gD4_3 (A := (List.range s.np).map (tvT (o4Len s hd))) (B := Mot) (C := Min)
      (D := (List.range (s.ni + 1)).map (fun i => tvT (o4Len s hd) (s.np + s.nm + i))) (p := j) (d := .bvar 0)
      (by rw [hMin]; exact hj)
    rw [lP, hMot] at this
    simp only [recBody]
    exact this
  have kI : ∀ i, i < s.ni + 1 →
      (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).getD (s.np + s.nm + s.nmin + i) (.bvar 0) =
        tvT (o4Len s hd) (s.np + s.nm + i) := by
    intro i hi
    have := gD4_4 (A := (List.range s.np).map (tvT (o4Len s hd))) (B := Mot) (C := Min)
      (D := (List.range (s.ni + 1)).map (fun i => tvT (o4Len s hd) (s.np + s.nm + i))) (p := i) (d := .bvar 0)
    rw [lP, hMot, hMin, getD_range_map hi] at this
    simp only [recBody]
    exact this
  generalize hA'def : (qRen s hd).map (betaN A) = A' at hApos ⊢
  generalize hKAdef : (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A) = KA at hKpos ⊢
  simp only [recBody, shapeIdx, List.map_append]
  refine forall2_append (forall2_append (forall2_append ?_ ?_) ?_) ?_
  · -- the parameters
    apply forall2_of_eq
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hp' := List.mem_range.1 hp
    simp only [Function.comp_apply]
    rw [hApos p (by cases hd <;> simp only [o4LenI] <;> omega), o4Idx_param hp' hd,
      hKpos p (by omega), kP p hp']
  · -- the motives
    have e1 : Mot'.map (betaN A') = (Mot'.map (betaN (qRen s hd))).map (betaN A) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      rw [betaN_betaN A (qRen s hd) t (by rw [hQ]; exact hrng t (List.mem_append_left _ ht)), hA'def]
    have e2 : (s.motiveSrc.toList.map (s.np + ·)).map (gL KA) =
        (s.motiveSrc.toList.map (fun m => Mot.getD m (.bvar 0))).map (betaN A) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro m hm
      have hm' := hwf.motives m hm
      simp only [Function.comp_apply]
      rw [hKpos (s.np + m) (by omega), kM m hm']
    rw [e1, e2]
    exact forall2_symm (forall2_mapRight (betaN A) (conv_betaN hΓ A) hcM)
  · -- the minors
    have e1 : Min'.map (betaN A') = (Min'.map (betaN (qRen s hd))).map (betaN A) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      rw [betaN_betaN A (qRen s hd) t (by rw [hQ]; exact hrng t (List.mem_append_right _ ht)), hA'def]
    have e2 : ((selMinors s).map (s.np + s.nm + ·)).map (gL KA) =
        ((selMinors s).map (fun j => Min.getD j (.bvar 0))).map (betaN A) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro j hj
      have hj' := hwf.minors j hj
      simp only [Function.comp_apply]
      rw [hKpos (s.np + s.nm + j) (by omega), kN j hj']
    rw [e1, e2]
    exact forall2_symm (forall2_mapRight (betaN A) (conv_betaN hΓ A) hcN)
  · -- the indices and the major
    apply forall2_of_eq
    simp only [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [hApos (s.np + s.motiveSrc.size + i) (by cases hd <;> simp only [o4LenI] <;> omega),
      o4Idx_index hi' hd, hKpos (s.np + s.nm + s.nmin + i) (by omega), kI i hi']

/-- **The square of a `rec` construction converts**: at any argument list covering Lean's
telescope, Lean's `h.{us}` against Pass 2's `ixA.{ls}` at O4's selection of the arguments. -/
theorem recCons_conv {Γ : Env} (hΓ : Γ.InstClosed) {s : RecShape} {hd : Bool} {h r ixA : Name}
    {us ls : Array Level} (hwf : ShapeWF s) (hsel : s.minorSrc.all Option.isSome = true)
    (hsq : RecConsSquare Γ s hd h r ixA us ls) {L : List Tm} (hL : o4Len s hd ≤ L.length) :
    Conv Γ (Tm.appN (.const h us) L)
      (Tm.appN (.const ixA ls) ((o4Idx s hd).map (gL L) ++ L.drop (o4Len s hd))) := by
  obtain ⟨Lv, v₁, v₂, v₃, tsL, tsI, Mot, Min, Mot', Min', hδ₁, htsL, hMot, hMin, rfl, hδ₂, hv₂,
    hδ₃, htsI, rfl, hrng, hcM, hcN⟩ := hsq
  have hb : SelOk s := ⟨hwf.motives, hwf.minors⟩
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  -- Lean's side: δ (h), β; δ (the image of r), β
  have c1 := delta_beta (L := L) hL htsL hδ₁
  have hAlen : (L.take (o4Len s hd)).length = o4Len s hd := by rw [List.length_take]; omega
  generalize hA : L.take (o4Len s hd) = A at c1 hAlen
  have hKL : (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).length = s.arity := by
    rw [recBody_length, hMot, hMin]; omega
  have hKA : ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A)).length = s.arity := by
    rw [List.length_map, hKL]
  obtain ⟨ts₂, hts₂, rfl⟩ := hv₂.sel hsel
  have hL1 : s.arity ≤ ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A) ++
      L.drop (o4Len s hd)).length := by
    rw [List.length_append, hKA]; omega
  have c2 := delta_sel (L := (recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A) ++
    L.drop (o4Len s hd)) hL1 hts₂ (shapeIdx_lt hb) hδ₂
  have hdrop2 : ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A) ++
      L.drop (o4Len s hd)).drop s.arity = L.drop (o4Len s hd) := by
    rw [← hKA]; simp
  have hsel2 : (shapeIdx s).map (gL ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map (betaN A) ++
      L.drop (o4Len s hd))) = (shapeIdx s).map (gL ((recBody (o4Len s hd) s.np s.nm s.ni Mot Min).map
        (betaN A))) := by
    apply List.map_congr_left
    intro p hp
    exact gL_append_lt (by rw [hKA]; exact shapeIdx_lt hb p hp)
  rw [hdrop2, hsel2] at c2
  -- Pass 2's side: δ (ixA), β
  have hO : ((o4Idx s hd).map (gL L)).length = o4LenI s hd := by rw [List.length_map, length_o4Idx]
  have hLo : o4LenI s hd ≤ ((o4Idx s hd).map (gL L) ++ L.drop (o4Len s hd)).length := by
    rw [List.length_append, hO]; omega
  have c3 := delta_beta (L := (o4Idx s hd).map (gL L) ++ L.drop (o4Len s hd)) hLo htsI hδ₃
  have ht3 : ((o4Idx s hd).map (gL L) ++ L.drop (o4Len s hd)).take (o4LenI s hd) = (o4Idx s hd).map (gL L) := by
    rw [← hO]; simp
  have hd3 : ((o4Idx s hd).map (gL L) ++ L.drop (o4Len s hd)).drop (o4LenI s hd) = L.drop (o4Len s hd) := by
    rw [← hO]; simp
  rw [ht3, hd3] at c3
  -- the output's telescope is Pass 2's telescope renamed into Lean's, substituted
  have hA' : (o4Idx s hd).map (gL L) = (qRen s hd).map (betaN A) := by
    unfold qRen
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hp' := o4Idx_lt hwf.motives hd p hp
    have e1 := betaN_tv (A := A) (p := p) (by rw [hAlen]; exact hp')
    rw [hAlen] at e1
    simp only [Function.comp_apply]
    show gL L p = betaN A (.bvar (o4Len s hd - 1 - p))
    rw [e1, ← hA]
    unfold gL
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp']
  have cmid := Conv.appN_args (Γ := Γ) (.const s.ixRec (s.levelsAt Lv))
    (forall2_append (recCons_middle hΓ hwf hMot hMin hAlen hrng hcM hcN)
      (Conv.forall₂_refl (L.drop (o4Len s hd))))
  rw [← hA'] at cmid
  exact .symm (.trans c3 (.trans cmid (.symm (.trans c1 c2))))

/-! ## `brecOn` and `.eq` -/

/-- **`BRecOnSquare`**: Lean's `x.brecOn` and Pass 2's `ρ.brecOn` are the first projection of
their `.go` (Lean's `mkBRecOn`), and the `.go` square holds. -/
def BRecOnSquare (Γ : Env) (s : RecShape) (h r ixA : Name) (us ls : Array Level) : Prop :=
  ∃ (goL goI sn : Name) (v₁ v₃ : Tm) (tsL tsI : List Tm),
    Γ.ax (.const h us) v₁ ∧ tsL.length = o4Len s true ∧
    v₁ = lamN tsL (.proj sn 0 (Tm.appN (.const goL us) ((List.range (o4Len s true)).map (tvT (o4Len s true))))) ∧
    Γ.ax (.const ixA ls) v₃ ∧ tsI.length = o4LenI s true ∧
    v₃ = lamN tsI (.proj sn 0 (Tm.appN (.const goI ls) ((List.range (o4LenI s true)).map (tvT (o4LenI s true))))) ∧
    RecConsSquare Γ s true goL r goI us ls

theorem brecOn_conv {Γ : Env} (hΓ : Γ.InstClosed) {s : RecShape} {h r ixA : Name}
    {us ls : Array Level} (hwf : ShapeWF s) (hsel : s.minorSrc.all Option.isSome = true)
    (hsq : BRecOnSquare Γ s h r ixA us ls) {L : List Tm} (hL : o4Len s true ≤ L.length) :
    Conv Γ (Tm.appN (.const h us) L)
      (Tm.appN (.const ixA ls) ((o4Idx s true).map (gL L) ++ L.drop (o4Len s true))) := by
  obtain ⟨goL, goI, sn, v₁, v₃, tsL, tsI, hδ₁, htsL, rfl, hδ₃, htsI, rfl, hgo⟩ := hsq
  have hAlen : (L.take (o4Len s true)).length = o4Len s true := by rw [List.length_take]; omega
  -- Lean's side: δ (brecOn), β, then the `.go` square at the telescope's arguments
  have c1 := delta_betaG (L := L) hL htsL hδ₁
  have hvars : ((List.range (o4Len s true)).map (tvT (o4Len s true))).map (betaN (L.take (o4Len s true))) =
      L.take (o4Len s true) := by
    have := betaN_telVars (L.take (o4Len s true))
    rw [hAlen] at this
    exact this
  rw [betaN_proj, betaN_appN, betaN_const, hvars] at c1
  have cgo := recCons_conv hΓ hwf hsel hgo (L := L.take (o4Len s true)) (by omega)
  have hdA : (L.take (o4Len s true)).drop (o4Len s true) = [] := by simp
  have hsA : (o4Idx s true).map (gL (L.take (o4Len s true))) = (o4Idx s true).map (gL L) := by
    apply List.map_congr_left
    intro p hp
    have hp' := o4Idx_lt hwf.motives true p hp
    unfold gL
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp']
  rw [hdA, List.append_nil, hsA] at cgo
  -- Pass 2's side: δ (ρ.brecOn), β
  have hO : ((o4Idx s true).map (gL L)).length = o4LenI s true := by rw [List.length_map, length_o4Idx]
  have hLo : o4LenI s true ≤ ((o4Idx s true).map (gL L) ++ L.drop (o4Len s true)).length := by
    rw [List.length_append, hO]; omega
  have c3 := delta_betaG (L := (o4Idx s true).map (gL L) ++ L.drop (o4Len s true)) hLo htsI hδ₃
  have ht3 : ((o4Idx s true).map (gL L) ++ L.drop (o4Len s true)).take (o4LenI s true) =
      (o4Idx s true).map (gL L) := by
    rw [← hO]; simp
  have hd3 : ((o4Idx s true).map (gL L) ++ L.drop (o4Len s true)).drop (o4LenI s true) =
      L.drop (o4Len s true) := by
    rw [← hO]; simp
  rw [ht3, hd3] at c3
  have hvars3 : ((List.range (o4LenI s true)).map (tvT (o4LenI s true))).map
      (betaN ((o4Idx s true).map (gL L))) = (o4Idx s true).map (gL L) := by
    have := betaN_telVars ((o4Idx s true).map (gL L))
    rw [hO] at this
    exact this
  rw [betaN_proj, betaN_appN, betaN_const, hvars3] at c3
  exact .trans c1 (.trans (Conv.appN (.proj sn 0 cgo) (Conv.forall₂_refl _)) (.symm c3))

/-- **`EqPIrrel`** (design D-2, a named rule of `Γ`): proof irrelevance for the pair Lean's
`x.brecOn.eq`, Pass 2's `ρ.brecOn.eq` (two proofs of statements the `.go`/`brecOn` squares make
convertible): an occurrence of the first steps to the second at O4's selection of its
arguments. -/
def EqPIrrel (Γ : Env) (s : RecShape) (h ixA : Name) (us ls : Array Level) : Prop :=
  ∀ L : List Tm, o4Len s true ≤ L.length →
    Γ.ax (Tm.appN (.const h us) L) (Tm.appN (.const ixA ls) ((o4Idx s true).map (gL L) ++ L.drop (o4Len s true)))

/-- **`O4Law`**: per kind, the square O4's conversion uses. -/
def O4Law (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (h r ixA : Name) (k : AuxKind) (b : OptBlock) (s : RecShape) (us : Array Level),
    classify h = some (k, r) → env.blockOf h = some b → b.shapes.get? r = some s →
    ixAuxOf s.ixRec k = some ixA → env.resolves ixA = true →
    ShapeWF s ∧
    (k = .kBelow → RecConsSquare Γ s false h r ixA us (s.levelsAt us)) ∧
    (k = .kGo → RecConsSquare Γ s true h r ixA us (s.levelsAt us)) ∧
    (k = .kBRecOn → BRecOnSquare Γ s h r ixA us (s.levelsAt us)) ∧
    (k = .kEq → EqPIrrel Γ s h ixA us (s.levelsAt us))

/-! ## The decomposition -/

theorem kind_o4 {k : AuxKind} (hk : ¬ (!(k == .kBelow || k == .kBRecOn || k == .kGo || k == .kEq)) = true) :
    k = .kBelow ∨ k = .kBRecOn ∨ k = .kGo ∨ k = .kEq := by
  cases k
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl rfl)
    | exact .inr (.inr (.inl rfl))
    | exact .inr (.inr (.inr rfl))
    | exact absurd rfl hk

/-- The flag of O4's telescope: the `brecOn` family has handlers. -/
def o4Hd : AuxKind → Bool
  | .kBelow => false
  | _ => true

/-- What a firing of O4 established. -/
theorem O4_some {env : OptEnv} {o : Occ} {e : Expr} (h : O4.apply env o = some e) :
    ∃ k r b s ls ixA ms' hs', classify o.head = some (k, r) ∧
      (k = .kBelow ∨ k = .kBRecOn ∨ k = .kGo ∨ k = .kEq) ∧
      env.blockOf o.head = some b ∧ b.change.collapse = false ∧ b.shapes.get? r = some s ∧
      s.isSelection = true ∧ standardTelescope env s k o.head = some (o4Len s (o4Hd k)) ∧
      o4Len s (o4Hd k) ≤ o.args.size ∧ O5.levels s o.us = some ls ∧
      ixAuxOf s.ixRec k = some ixA ∧ env.resolves ixA = true ∧
      (k ≠ .kBelow → ∃ d, env.const? (belowNameOf r) = some (.defnInfo d)) ∧
      pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms' ∧
      (if o4Hd k then pick (o.args.extract (s.np + s.nm + s.ni + 1) (o4Len s true)) s.motiveSrc = some hs'
        else hs' = #[]) ∧
      e = mkAppN (Expr.mkConst ixA ls) (o.args.extract 0 s.np ++ ms' ++
        o.args.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1) ++ hs' ++
        o.args.extract (o4Len s (o4Hd k)) o.args.size) := by
  unfold O4.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hcol, h⟩ := oguard h
  obtain ⟨s, hs, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsel, h⟩ := oguard h
  obtain ⟨n, hn, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsz, h⟩ := oguard h
  obtain ⟨ls, hls, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨ixA, hix, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hres, h⟩ := oguard h
  have hkk := kind_o4 hk
  rcases hkk with rfl | rfl | rfl | rfl
  · have h := oite_false (show ¬ (AuxKind.kBelow != AuxKind.kBelow) = true by decide) h
    obtain ⟨ms', hms, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨hs', hhs, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h hhs
    have he := h.symm
    have hn' : n = o4Len s false := standardTelescope_eq hn
    subst hn'
    exact ⟨.kBelow, r, b, s, ls, ixA, ms', hs', hc, .inl rfl, hb, bool_false hcol, hs,
      bnot_false hsel, hn, (by show o4Len s false ≤ o.args.size; omega), hls, hix, bnot_false hres,
      fun hne => absurd rfl hne, hms,
      hhs.symm, he⟩
  all_goals
    cases hbel : env.const? (belowNameOf r) with
    | none => rw [hbel] at h; oabsurd h
    | some ci =>
      cases ci
      case defnInfo d =>
        rw [hbel] at h
        try dsimp only at h
        obtain ⟨ms', hms, h⟩ := obind.1 h
        try dsimp only at h
        try (replace h := oite_false (by decide) h)
        obtain ⟨hs', hhs, h⟩ := obind.1 h
        simp only [pure, Option.some.injEq] at h
        have he := h.symm
        have hn' : n = o4Len s true := standardTelescope_eq hn
        subst hn'
        exact ⟨_, r, b, s, ls, ixA, ms', hs', hc,
          by first | exact .inr (.inl rfl) | exact .inr (.inr (.inl rfl)) | exact .inr (.inr (.inr rfl)),
          hb, bool_false hcol, hs, bnot_false hsel, hn, (by show o4Len s true ≤ o.args.size; omega), hls, hix,
          bnot_false hres,
          fun _ => ⟨d, hbel⟩, hms, hhs, he⟩
      all_goals (rw [hbel] at h; oabsurd h)


/-! ## The conversion -/

/-- O4's output arguments erase to its selection of the occurrence's arguments. -/
theorem o4_out {o : Occ} {s : RecShape} {hd : Bool} {ms' hs' : Array Expr}
    (hn : o4Len s hd ≤ o.args.size)
    (hms : pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms')
    (hhs : if hd then pick (o.args.extract (s.np + s.nm + s.ni + 1) (o4Len s true)) s.motiveSrc = some hs'
      else hs' = #[]) :
    (o.args.extract 0 s.np ++ ms' ++ o.args.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1) ++ hs' ++
      o.args.extract (o4Len s hd) o.args.size).toList.map er =
      (o4Idx s hd).map (gL (o.args.toList.map er)) ++ (o.args.toList.map er).drop (o4Len s hd) := by
  have hg : gL (o.args.toList.map er) = argT o.args := funext (gL_args o.args)
  have hb : s.np + s.nm + s.ni + 1 ≤ o4Len s hd := by cases hd <;> simp only [o4Len] <;> omega
  have e1 := extract_map o.args (i := 0) (j := s.np) (by omega)
  have e3 := extract_map o.args (i := s.np + s.nm) (j := s.np + s.nm + s.ni + 1) (by omega)
  have e5 := extract_map o.args (i := o4Len s hd) (j := o.args.size) (Nat.le_refl _)
  obtain ⟨hms1, -⟩ := pick_extract (by omega) hms
  rw [hg, args_drop o.args hn]
  simp only [Array.toList_append, List.map_append]
  rw [e1, hms1, e3, e5]
  cases hd with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hhs
    subst hhs
    simp only [o4Idx, List.map_append, List.map_map, Nat.sub_zero, Nat.zero_add, List.map_nil, List.append_nil]
    rw [show s.np + s.nm + s.ni + 1 - (s.np + s.nm) = s.ni + 1 by omega]
    try rfl
  | true =>
    simp only [↓reduceIte] at hhs
    obtain ⟨hhs1, -⟩ := pick_extract hn hhs
    rw [hhs1]
    simp only [o4Idx, List.map_append, List.map_map, Nat.sub_zero, Nat.zero_add]
    rw [show s.np + s.nm + s.ni + 1 - (s.np + s.nm) = s.ni + 1 by omega]
    try rfl

/-- **O4 is definitional**: its output converts to the occurrence (`below`, `.go`: the square of
the `rec` construction; `brecOn`: through its `.go`; `.eq`: proof irrelevance, D-2). -/
theorem O4_faithful {Γ : Env} {env : OptEnv} (hΓ : Γ.InstClosed) (hL : O4Law Γ env)
    {o : Occ} {e : Expr} (h : O4.apply env o = some e) : ExprConv Γ e (occTerm o) := by
  obtain ⟨k, r, b, s, ls, ixA, ms', hs', hc, hkk, hb, -, hs, hsel, -, hn, hls, hix, hres, -, hms,
    hhs, rfl⟩ := O4_some h
  have hls' := O5_levels_eq hls
  subst hls'
  obtain ⟨hwf, hBelow, hGo, hBRecOn, hEq⟩ := hL o.head r ixA k b s o.us hc hb hs hix hres
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have hsel' : s.minorSrc.all Option.isSome = true := hsel
  unfold ExprConv
  rw [er_occTerm, er_mkAppN, er_mkConst, o4_out hn hms hhs]
  have hL0 : o4Len s (o4Hd k) ≤ (o.args.toList.map er).length := by simpa using hn
  generalize o.args.toList.map er = L at hL0 ⊢
  rcases hkk with rfl | rfl | rfl | rfl
  · exact .symm (recCons_conv hΓ hwf hsel' (hBelow rfl) hL0)
  · exact .symm (brecOn_conv hΓ hwf hsel' (hBRecOn rfl) hL0)
  · exact .symm (recCons_conv hΓ hwf hsel' (hGo rfl) hL0)
  · exact .symm (.step (.ax (hEq rfl L hL0)))


end Ix.CompileCert.Opt
