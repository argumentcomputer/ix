import Ix.CompileCert.Opt.Shape

/-!
# M7 L3-def: `rec` and `recOn` over a selection shape (the common part of O1 and O6)

O1 (a permuted block, `isPerm`) and O6 (any block whose image is a selection, `isSelection`) give
the same term: `ρ.{ℓs[us]}` (or Pass 2's `ρ.recOn`) applied to the selection of the occurrence's
arguments the shape records. This module proves, once, that this term converts to the
occurrence:

* `rec_sel_conv` (`rec`): δ (the image, `RecLaw`), `n` β-steps; the motives and minors the
  selection drops are discarded by β;
* `recOn_sel_conv` (`recOn`): δ (Lean's `x.recOn`, `mkRecOn` over `x.rec`), β, δ (the image), β;
  and on the other side δ (Pass 2's `ρ.recOn`, `mkRecOn` over `ρ`), β: both reach the same
  selection of the arguments (`recOn_index_lean`, `recOn_index_ix`: equations between index
  lists).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-! ## Index lists -/

theorem getD_map_nat {β : Type} {l : List Nat} {f : Nat → β} {p : Nat} {d : β} (h : p < l.length) :
    (l.map f).getD p d = f (l.getD p 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some, Option.getD_some]

theorem getD_map_range {β : Type} {n p : Nat} {f : Nat → β} {d : β} (h : p < n) :
    ((List.range n).map f).getD p d = f p := by
  have h1 : p < (List.range n).length := by simpa using h
  rw [getD_map_nat h1, getD_range h]

/-- `gL` through a selection. -/
theorem gL_sel' {L : List Tm} {idx : List Nat} {p : Nat} (h : p < idx.length) :
    gL (idx.map (gL L)) p = gL L (idx.getD p 0) := by
  unfold gL
  exact getD_map_nat h

/-- **Selections compose.** -/
theorem sel_sel' {L R : List Tm} {idx1 idx2 : List Nat} (h : ∀ p ∈ idx2, p < idx1.length) :
    idx2.map (gL (idx1.map (gL L) ++ R)) = (idx2.map (fun p => idx1.getD p 0)).map (gL L) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  have hp' : p < (idx1.map (gL L)).length := by rw [List.length_map]; exact h p hp
  rw [gL_append_lt hp', gL_sel' (h p hp)]
  rfl

/-- Four appended lists, part by part. -/
theorem app4 {α : Type} {a a' b b' c c' d d' : List α} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' := by
  subst ha hb hc hd; rfl

section four
variable {A B C D : List Nat} {p : Nat}

theorem getD4_1 (h : p < A.length) : (A ++ B ++ C ++ D).getD p 0 = A.getD p 0 := by
  have h1 : p < (A ++ B ++ C).length := by simp; omega
  have h2 : p < (A ++ B).length := by simp; omega
  rw [getD_append_lt h1, getD_append_lt h2, getD_append_lt h]

theorem getD4_2 (h : p < B.length) : (A ++ B ++ C ++ D).getD (A.length + p) 0 = B.getD p 0 := by
  have h1 : A.length + p < (A ++ B ++ C).length := by simp; omega
  have h2 : A.length + p < (A ++ B).length := by simp; omega
  have h3 : A.length ≤ A.length + p := Nat.le_add_right _ _
  rw [getD_append_lt h1, getD_append_lt h2, getD_append_ge h3, Nat.add_sub_cancel_left]

theorem getD4_3 (h : p < C.length) :
    (A ++ B ++ C ++ D).getD (A.length + B.length + p) 0 = C.getD p 0 := by
  have h1 : A.length + B.length + p < (A ++ B ++ C).length := by simp; omega
  have h2 : (A ++ B).length ≤ A.length + B.length + p := by simp
  rw [getD_append_lt h1, getD_append_ge h2]
  simp only [List.length_append]
  rw [Nat.add_sub_cancel_left]

theorem getD4_4 : (A ++ B ++ C ++ D).getD (A.length + B.length + C.length + p) 0 = D.getD p 0 := by
  have h1 : (A ++ B ++ C).length ≤ A.length + B.length + C.length + p := by simp; omega
  rw [getD_append_ge h1]
  simp only [List.length_append]
  rw [Nat.add_sub_cancel_left]

end four

theorem length_recOnIdx (np nm nmin ni : Nat) :
    (recOnIdx np nm nmin ni).length = np + nm + nmin + ni + 1 := by
  simp only [recOnIdx, List.length_append, List.length_map, List.length_range]; omega

/-- The selection of a list by `List.range` over its own length, mapped. -/
theorem map_range_getD (l : List Nat) (f : Nat → Nat) :
    (List.range l.length).map (fun k => f (l.getD k 0)) = l.map f := by
  have := congrArg (List.map f) (range_getD l 0)
  rw [List.map_map] at this
  exact this

/-- The positions of the O1/O6 `recOn` output's arguments `ps ms′ is t mins′` in the occurrence's
telescope `ps ms is t mins`. -/
def recOnOutIdx (s : RecShape) : List Nat :=
  List.range s.np ++ s.motiveSrc.toList.map (s.np + ·) ++ (List.range (s.ni + 1)).map (s.np + s.nm + ·) ++
    (selMinors s).map (s.np + s.nm + s.ni + 1 + ·)

/-- The selected arguments in `ρ`'s order, read through either side of the `recOn` square. -/
def recOnTarget (s : RecShape) : List Nat :=
  List.range s.np ++ s.motiveSrc.toList.map (s.np + ·) ++ (selMinors s).map (s.np + s.nm + s.ni + 1 + ·) ++
    (List.range (s.ni + 1)).map (s.np + s.nm + ·)

theorem length_recOnOutIdx {s : RecShape} : (recOnOutIdx s).length =
    s.np + s.motiveSrc.size + (s.ni + 1) + (selMinors s).length := by
  simp only [recOnOutIdx, List.length_append, List.length_map, List.length_range, Array.length_toList]

/-- Lean's side of the `recOn` square: the image's selection read through `mkRecOn`. -/
theorem recOn_index_lean {s : RecShape} (hm : ∀ p ∈ s.motiveSrc.toList, p < s.nm)
    (hj : ∀ j ∈ selMinors s, j < s.nmin) :
    (shapeIdx s).map (fun p => (recOnIdx s.np s.nm s.nmin s.ni).getD p 0) = recOnTarget s := by
  have lA : (List.range s.np).length = s.np := List.length_range ..
  have lB : ((List.range s.nm).map (s.np + ·)).length = s.nm := by simp
  have lC : ((List.range s.nmin).map (s.np + s.nm + s.ni + 1 + ·)).length = s.nmin := by simp
  simp only [shapeIdx, recOnTarget, List.map_append, List.map_map]
  refine app4 ?_ ?_ ?_ ?_
  · -- the parameters
    refine Eq.trans ?_ (List.map_id (List.range s.np))
    apply List.map_congr_left
    intro p hp
    have hp' : p < s.np := List.mem_range.1 hp
    have := getD4_1 (A := List.range s.np) (B := (List.range s.nm).map (s.np + ·))
      (C := (List.range s.nmin).map (s.np + s.nm + s.ni + 1 + ·))
      (D := (List.range (s.ni + 1)).map (s.np + s.nm + ·)) (p := p) (by rw [lA]; exact hp')
    simp only [id_eq, recOnIdx]
    rw [this, getD_range hp']
  · -- the motives
    apply List.map_congr_left
    intro m hm'
    have hmn := hm m hm'
    have := getD4_2 (A := List.range s.np) (B := (List.range s.nm).map (s.np + ·))
      (C := (List.range s.nmin).map (s.np + s.nm + s.ni + 1 + ·))
      (D := (List.range (s.ni + 1)).map (s.np + s.nm + ·)) (p := m) (by rw [lB]; exact hmn)
    rw [lA, getD_map_range hmn] at this
    simp only [Function.comp_apply, recOnIdx]
    exact this
  · -- the minors
    apply List.map_congr_left
    intro j hj'
    have hjn := hj j hj'
    have := getD4_3 (A := List.range s.np) (B := (List.range s.nm).map (s.np + ·))
      (C := (List.range s.nmin).map (s.np + s.nm + s.ni + 1 + ·))
      (D := (List.range (s.ni + 1)).map (s.np + s.nm + ·)) (p := j) (by rw [lC]; exact hjn)
    rw [lA, lB, getD_map_range hjn] at this
    simp only [Function.comp_apply, recOnIdx]
    exact this
  · -- the indices and the major
    apply List.map_congr_left
    intro i hi
    have hi' : i < s.ni + 1 := List.mem_range.1 hi
    have := getD4_4 (A := List.range s.np) (B := (List.range s.nm).map (s.np + ·))
      (C := (List.range s.nmin).map (s.np + s.nm + s.ni + 1 + ·))
      (D := (List.range (s.ni + 1)).map (s.np + s.nm + ·)) (p := i)
    rw [lA, lB, lC, getD_map_range hi'] at this
    simp only [Function.comp_apply, recOnIdx]
    exact this

/-- Pass 2's side of the `recOn` square: `mkRecOn` over `ρ` read through the output's order. -/
theorem recOn_index_ix {s : RecShape} (hsm : (selMinors s).length = s.minorSrc.size) :
    (recOnIdx s.np s.motiveSrc.size s.minorSrc.size s.ni).map (fun p => (recOnOutIdx s).getD p 0) =
      recOnTarget s := by
  have lA : (List.range s.np).length = s.np := List.length_range ..
  have lB : (s.motiveSrc.toList.map (s.np + ·)).length = s.motiveSrc.size := by simp
  have lC : ((List.range (s.ni + 1)).map (s.np + s.nm + ·)).length = s.ni + 1 := by simp
  simp only [recOnIdx, recOnTarget, List.map_append, List.map_map]
  refine app4 ?_ ?_ ?_ ?_
  · refine Eq.trans ?_ (List.map_id (List.range s.np))
    apply List.map_congr_left
    intro p hp
    have hp' : p < s.np := List.mem_range.1 hp
    have := getD4_1 (A := List.range s.np) (B := s.motiveSrc.toList.map (s.np + ·))
      (C := (List.range (s.ni + 1)).map (s.np + s.nm + ·))
      (D := (selMinors s).map (s.np + s.nm + s.ni + 1 + ·)) (p := p) (by rw [lA]; exact hp')
    simp only [id_eq, recOnOutIdx]
    rw [this, getD_range hp']
  · -- the motives: `np + k ↦ np + motiveSrc[k]`
    have e : (List.range s.motiveSrc.size).map (fun k => s.np + s.motiveSrc.toList.getD k 0) =
        s.motiveSrc.toList.map (s.np + ·) := by
      have := map_range_getD s.motiveSrc.toList (s.np + ·)
      rw [Array.length_toList] at this
      exact this
    rw [← e]
    apply List.map_congr_left
    intro k hk
    have hk' : k < s.motiveSrc.size := List.mem_range.1 hk
    have hk'' : k < s.motiveSrc.toList.length := by rw [Array.length_toList]; exact hk'
    have := getD4_2 (A := List.range s.np) (B := s.motiveSrc.toList.map (s.np + ·))
      (C := (List.range (s.ni + 1)).map (s.np + s.nm + ·))
      (D := (selMinors s).map (s.np + s.nm + s.ni + 1 + ·)) (p := k) (by rw [lB]; exact hk')
    rw [lA, getD_map_nat hk''] at this
    simp only [Function.comp_apply, recOnOutIdx]
    exact this
  · -- the minors: `np + nm′ + ni + 1 + k ↦ np + nm + ni + 1 + selMinors[k]`
    have e : (List.range s.minorSrc.size).map
        (fun k => s.np + s.nm + s.ni + 1 + (selMinors s).getD k 0) =
        (selMinors s).map (s.np + s.nm + s.ni + 1 + ·) := by
      have := map_range_getD (selMinors s) (s.np + s.nm + s.ni + 1 + ·)
      rw [hsm] at this
      exact this
    rw [← e]
    apply List.map_congr_left
    intro k hk
    have hk' : k < s.minorSrc.size := List.mem_range.1 hk
    have hk'' : k < (selMinors s).length := by rw [hsm]; exact hk'
    have := getD4_4 (A := List.range s.np) (B := s.motiveSrc.toList.map (s.np + ·))
      (C := (List.range (s.ni + 1)).map (s.np + s.nm + ·))
      (D := (selMinors s).map (s.np + s.nm + s.ni + 1 + ·)) (p := k)
    rw [lA, lB, lC, getD_map_nat hk''] at this
    simp only [Function.comp_apply, recOnOutIdx]
    rw [show s.np + s.motiveSrc.size + s.ni + 1 + k = s.np + s.motiveSrc.size + (s.ni + 1) + k by omega]
    exact this
  · -- the indices and the major: `np + nm′ + i ↦ np + nm + i`
    apply List.map_congr_left
    intro i hi
    have hi' : i < s.ni + 1 := List.mem_range.1 hi
    have := getD4_3 (A := List.range s.np) (B := s.motiveSrc.toList.map (s.np + ·))
      (C := (List.range (s.ni + 1)).map (s.np + s.nm + ·))
      (D := (selMinors s).map (s.np + s.nm + s.ni + 1 + ·)) (p := i) (by rw [lC]; exact hi')
    rw [lA, lB, getD_map_range hi'] at this
    simp only [Function.comp_apply, recOnOutIdx]
    exact this

/-! ## The two conversions -/

/-- The bounds a successful pair of `pick`s gives. -/
structure SelOk (s : RecShape) : Prop where
  motives : ∀ p ∈ s.motiveSrc.toList, p < s.nm
  minors : ∀ j ∈ selMinors s, j < s.nmin

theorem shapeIdx_lt {s : RecShape} (hb : SelOk s) : ∀ p ∈ shapeIdx s, p < s.arity := by
  intro p hp
  simp only [shapeIdx, List.mem_append, List.mem_map, List.mem_range] at hp
  unfold RecShape.arity
  rcases hp with ((hp | ⟨m, hm, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
  · omega
  · have := hb.motives m hm; omega
  · have := hb.minors j hj; omega
  · omega

theorem recOnIdx_lt (np nm nmin ni : Nat) :
    ∀ p ∈ recOnIdx np nm nmin ni, p < np + nm + nmin + ni + 1 := by
  intro p hp
  simp only [recOnIdx, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with ((hp | ⟨m, hm, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩ <;> omega

theorem selOk_of_picks {o : Occ} {s : RecShape} {ms' mins' : Array Expr} {i j : Nat}
    (hn : s.arity ≤ o.args.size) (hij : j - i = s.nmin) (hj : j ≤ o.args.size)
    (hms : pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms')
    (hmins : pick (o.args.extract i j) (s.minorSrc.filterMap id) = some mins') : SelOk s := by
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have h1 : s.np + s.nm ≤ o.args.size := by omega
  obtain ⟨-, hms2⟩ := pick_extract h1 hms
  obtain ⟨-, hmi2⟩ := pick_extract hj hmins
  refine ⟨fun p hp => ?_, fun q hq => ?_⟩
  · have := hms2 p hp; omega
  · have hq' : q ∈ (s.minorSrc.filterMap id).toList := by
      rw [Array.toList_filterMap]; exact hq
    have := hmi2 q hq'; omega

/-- **`rec` over a selection shape**: `ρ.{ls}` applied to the shape's selection of the arguments
(and the arguments past the telescope) converts to the occurrence, given its δ-rule. -/
theorem rec_sel_conv {Γ : Env} {o : Occ} {s : RecShape} {ls : Array Level} {v : Tm}
    {ms' mins' : Array Expr} (hδ : Γ.ax (.const o.head o.us) v) (hv : ShapeAt s ls v)
    (hsel : s.minorSrc.all Option.isSome = true) (hn : s.arity ≤ o.args.size)
    (hms : pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms')
    (hmins : pick (o.args.extract (s.np + s.nm) (s.np + s.nm + s.nmin)) (s.minorSrc.filterMap id) = some mins') :
    ExprConv Γ (mkAppN (Expr.mkConst s.ixRec ls) (o.args.extract 0 s.np ++ ms' ++ mins' ++
      o.args.extract (s.np + s.nm + s.nmin) s.arity ++ o.args.extract s.arity o.args.size)) (occTerm o) := by
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have h1 : s.np + s.nm ≤ o.args.size := by omega
  have h2 : s.np + s.nm + s.nmin ≤ o.args.size := by omega
  obtain ⟨hms1, -⟩ := pick_extract h1 hms
  obtain ⟨hmi1, -⟩ := pick_extract h2 hmins
  have hb : SelOk s := selOk_of_picks hn (by omega) h2 hms hmins
  obtain ⟨ts, hts, rfl⟩ := hv.sel hsel
  have hout : (o.args.extract 0 s.np ++ ms' ++ mins' ++ o.args.extract (s.np + s.nm + s.nmin) s.arity ++
      o.args.extract s.arity o.args.size).toList.map er =
      (shapeIdx s).map (argT o.args) ++
        (List.range (o.args.size - s.arity)).map (fun k => argT o.args (s.arity + k)) := by
    have e1 := extract_map o.args (i := 0) (j := s.np) (by omega)
    have e4 := extract_map o.args (i := s.np + s.nm + s.nmin) (j := s.arity) hn
    have e5 := extract_map o.args (i := s.arity) (j := o.args.size) (Nat.le_refl _)
    simp only [Array.toList_append, List.map_append]
    rw [e1, hms1, hmi1, e4, e5, Array.toList_filterMap]
    simp only [shapeIdx, selMinors, List.map_append, List.map_map, Nat.sub_zero, Nat.zero_add]
    rw [show s.arity - (s.np + s.nm + s.nmin) = s.ni + 1 by omega]
    try rfl
  have hL : s.arity ≤ (o.args.toList.map er).length := by simpa using hn
  have hconv := delta_sel (L := o.args.toList.map er) hL hts (shapeIdx_lt hb) hδ
  rw [args_drop o.args hn, show gL (o.args.toList.map er) = argT o.args from funext (gL_args o.args)]
    at hconv
  unfold ExprConv
  rw [er_occTerm, er_mkAppN, er_mkConst, hout]
  exact .symm hconv

/-- **`recOn` over a selection shape**: Pass 2's `ρ.recOn.{ls}` applied to the shape's selection
of the arguments, in `recOn`'s order, converts to the occurrence of Lean's `x.recOn`, given the
δ-rules of `x.recOn` (`mkRecOn` over `x.rec`), of `x.rec` (its image) and of `ρ.recOn`
(`mkRecOn` over `ρ`). -/
theorem recOn_sel_conv {Γ : Env} {o : Occ} {r ixRecOn : Name} {s : RecShape} {ls : Array Level}
    {v₁ v₂ v₃ : Tm} {ms' mins' : Array Expr}
    (hδ₁ : Γ.ax (.const o.head o.us) v₁) (hv₁ : RecOnBody r o.us s.np s.nm s.nmin s.ni v₁)
    (hδ₂ : Γ.ax (.const r o.us) v₂) (hv₂ : ShapeAt s ls v₂)
    (hδ₃ : Γ.ax (.const ixRecOn ls) v₃)
    (hv₃ : RecOnBody s.ixRec ls s.np s.motiveSrc.size s.minorSrc.size s.ni v₃)
    (hsel : s.minorSrc.all Option.isSome = true) (hn : s.arity ≤ o.args.size)
    (hms : pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms')
    (hmins : pick (o.args.extract (s.np + s.nm + s.ni + 1) s.arity) (s.minorSrc.filterMap id) = some mins') :
    ExprConv Γ (mkAppN (Expr.mkConst ixRecOn ls) (o.args.extract 0 s.np ++ ms' ++
      o.args.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1) ++ mins' ++
      o.args.extract s.arity o.args.size)) (occTerm o) := by
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  have h1 : s.np + s.nm ≤ o.args.size := by omega
  obtain ⟨hms1, -⟩ := pick_extract h1 hms
  obtain ⟨hmi1, -⟩ := pick_extract hn hmins
  have hb : SelOk s := selOk_of_picks hn (by omega) hn hms hmins
  have hsm : (selMinors s).length = s.minorSrc.size := selMinors_length hsel
  -- the output's arguments, as a selection
  have hout : (o.args.extract 0 s.np ++ ms' ++ o.args.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1) ++
      mins' ++ o.args.extract s.arity o.args.size).toList.map er =
      (recOnOutIdx s).map (argT o.args) ++
        (List.range (o.args.size - s.arity)).map (fun k => argT o.args (s.arity + k)) := by
    have e1 := extract_map o.args (i := 0) (j := s.np) (by omega)
    have e3 := extract_map o.args (i := s.np + s.nm) (j := s.np + s.nm + s.ni + 1) (by omega)
    have e5 := extract_map o.args (i := s.arity) (j := o.args.size) (Nat.le_refl _)
    simp only [Array.toList_append, List.map_append]
    rw [e1, hms1, e3, hmi1, e5, Array.toList_filterMap]
    simp only [recOnOutIdx, selMinors, List.map_append, List.map_map, Nat.sub_zero, Nat.zero_add]
    rw [show s.np + s.nm + s.ni + 1 - (s.np + s.nm) = s.ni + 1 by omega]
    try rfl
  unfold ExprConv
  rw [er_occTerm, er_mkAppN, er_mkConst, hout]
  have hg : argT o.args = gL (o.args.toList.map er) := (funext (gL_args o.args)).symm
  rw [← args_drop o.args hn, hg]
  have hL : s.arity ≤ (o.args.toList.map er).length := by simpa using hn
  generalize o.args.toList.map er = L at hL ⊢
  -- Lean's side: δ (x.recOn), β, δ (x.rec), β
  obtain ⟨ts₁, hts₁, rfl⟩ := hv₁
  have c1 := delta_sel (L := L) (n := s.arity) hL hts₁ (recOnIdx_lt s.np s.nm s.nmin s.ni) hδ₁
  have hL₁ : s.arity ≤ ((recOnIdx s.np s.nm s.nmin s.ni).map (gL L) ++ L.drop s.arity).length := by
    simp only [List.length_append, List.length_map, length_recOnIdx]; omega
  obtain ⟨ts₂, hts₂, rfl⟩ := hv₂.sel hsel
  have c2 := delta_sel (L := (recOnIdx s.np s.nm s.nmin s.ni).map (gL L) ++ L.drop s.arity) hL₁ hts₂
    (shapeIdx_lt hb) hδ₂
  have hlt2 : ∀ p ∈ shapeIdx s, p < (recOnIdx s.np s.nm s.nmin s.ni).length := by
    intro p hp; rw [length_recOnIdx]; exact shapeIdx_lt hb p hp
  have hd2 : ((recOnIdx s.np s.nm s.nmin s.ni).map (gL L) ++ L.drop s.arity).drop s.arity =
      L.drop s.arity := by
    have := drop_sel (L := L) (R := L.drop s.arity) (idx := recOnIdx s.np s.nm s.nmin s.ni)
    rw [length_recOnIdx] at this
    exact this
  rw [sel_sel' hlt2, recOn_index_lean hb.motives hb.minors, hd2] at c2
  -- Pass 2's side: δ (ρ.recOn), β
  obtain ⟨ts₃, hts₃, rfl⟩ := hv₃
  have hLo : s.np + s.motiveSrc.size + s.minorSrc.size + s.ni + 1 ≤
      ((recOnOutIdx s).map (gL L) ++ L.drop s.arity).length := by
    simp only [List.length_append, List.length_map, length_recOnOutIdx]; omega
  have c3 := delta_sel (L := (recOnOutIdx s).map (gL L) ++ L.drop s.arity) hLo hts₃
    (recOnIdx_lt _ _ _ _) hδ₃
  have hlt3 : ∀ p ∈ recOnIdx s.np s.motiveSrc.size s.minorSrc.size s.ni, p < (recOnOutIdx s).length := by
    intro p hp
    rw [length_recOnOutIdx, hsm]
    have := recOnIdx_lt s.np s.motiveSrc.size s.minorSrc.size s.ni p hp
    omega
  have hd3 : ((recOnOutIdx s).map (gL L) ++ L.drop s.arity).drop
      (s.np + s.motiveSrc.size + s.minorSrc.size + s.ni + 1) = L.drop s.arity := by
    have := drop_sel (L := L) (R := L.drop s.arity) (idx := recOnOutIdx s)
    rw [length_recOnOutIdx, hsm] at this
    rw [show s.np + s.motiveSrc.size + s.minorSrc.size + s.ni + 1 =
      s.np + s.motiveSrc.size + (s.ni + 1) + s.minorSrc.size by omega]
    exact this
  rw [sel_sel' hlt3, recOn_index_ix hsm, hd3] at c3
  exact .trans c3 (.symm (.trans c1 c2))

end Ix.CompileCert.Opt
