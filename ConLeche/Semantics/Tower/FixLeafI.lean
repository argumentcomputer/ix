module

import ConLeche.Semantics.Tower.SumLeaf
public import ConLeche.Semantics.Tower.SumMk
public import ConLeche.Semantics.NoBVar
import ConLeche.SetModel.Iter
public import ConLeche.SetModel.TowerMono
import ConLeche.Semantics.Univ

@[expose] public section

/-!
# The type-former leaf of a direct recursive FAMILY (task #188, indexed)

The carrier of a directly installed recursive inductive family
`T : Π p⃗ ı⃗, Sort w` is the least pre-fixed family (`lfpFam`,
`ConLeche/SetTheory/Derive/LfpFam.lean`) of its constructor-tower functor
on families over the **index-tuple set** `I = ⟦Σ' ı⃗⟧` (the tower over
the index telescope, `idxTyAV`; a tuple is `tupW u ı⃗` — the point at
index level `0`):

    λ p⃗ ı⃗. lfpFam.{u,w} I (λ (X : I → Sort w) (t : I). Σ_j tower_j(X, t)) ⟨ı⃗⟩

Constructor `j`'s tower at `(X, t)` is spelled over its **X-chain**
(`chainXI`): an ordinary field domain is lifted past the two binders
`X, t`; a recursive field `T p⃗ e⃗_i(f_prev)` reads `X ⟨e⃗_i⟩` — the family
applied to the tuple of its index expressions, the tuple built by the
**index tupler** `tuplerAV` (a λ over the index telescope returning the
tuple, applied to the expressions — no substitution is ever performed);
the terminator is the index equation of the sum route (`idxEqAV`) with
the constructor's index expressions equated to the PROJECTIONS of the
tuple `t`.  At `nIdx = 0` this is the non-indexed route with the unit
tuple; the non-recursive class is the constant functor.

This module: the spelled pieces, their readings and gradings, and the
former leaf's three laws (`nativeTyAVI_mem/_ok2/_fold`) under one
hereditary premise (`ParamsOkXI`).  The functor's semantic laws
(monotonicity, the ω-iterate as a closed family, the fixed point, the
identification with the real chains) are in `FixFamI.lean`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The index tuple -/

/-- The index tuple's value: the point at index level `0`, the tuple
tower above. -/
noncomputable def tupW (u : Nat) (is : List V) : V := if u = 0 then pt else mkTower is

theorem tupW_zero (is : List V) : tupW 0 is = (pt : V) := if_pos rfl
theorem tupW_pos {u : Nat} (hu : u ≠ 0) (is : List V) : tupW u is = mkTower is := if_neg hu

/-- The index-tuple set at a parameter frame. -/
noncomputable def idxSet (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) : V :=
  towerSet u (teleOfFields ρp Ids)

/-- The index tuple type, spelled at the parameter frame. -/
def idxTyAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm := towerBodyAV u Ids

/-- The index tupler: the λ-tower over the index telescope returning
the tuple (bit `u`: the tuple's type is `I : Sort u`). -/
def tuplerAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  mkLamsC u (Ids.map fun F => (u, u, F)) (mkTowerGo u Ids)

/-- The index telescope's grading, with the bound in both regimes (the
index domains' sorts are at most `u`, so the tuple type is a graph-regime
tower even at `u = 0` where `FieldsOkB` alone asks for no bound). -/
def IdxOk (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) : Prop :=
  FieldsOkB u ρp Ids ∧ FieldsBound u ρp Ids

theorem idxTyAV_facts {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (idxTyAV u Ids) = idxSet u ρp Ids ∧
      idxSet u ρp Ids ∈ˢ (univ u : V) ∧ WellDenoted V ρp (idxTyAV u Ids) :=
  ⟨towerBodyAV_interp (fun _ => h.2), towerSet_univ_of_okB (fun _ => h.2), towerBodyAV_wellDenoted h.1⟩

/-- A fitting index spine's tuple is in the tuple set. -/
theorem tupW_mem {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {is : List V}
    (hsp : SpineFit ρp Ids is) : tupW u is ∈ˢ idxSet u ρp Ids := by
  unfold tupW idxSet
  split
  · next hu => exact hu ▸ pt_mem_tower (fitsS_teleOfFields.mpr hsp)
  · next hu => exact mkTower_mem hu (fitsS_teleOfFields.mpr hsp)

/-- The tupler's binder data. -/
abbrev tuplerData (u : Nat) (Ids : List AnnotTerm) : List (Nat × Nat × AnnotTerm) :=
  Ids.map fun F => (u, u, F)

omit [SetTheory V] in
theorem tuplerData_doms (u : Nat) (Ids : List AnnotTerm) :
    (tuplerData u Ids).map (·.2.2) = Ids := by
  simp [tuplerData, Function.comp_def]

/-- The tupler's type: `Π ı⃗, I` (the tuple type lifted under the index
binders). -/
def tuplerTyAV (u : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  mkPisAV (tuplerData u Ids) ((idxTyAV u Ids).liftN Ids.length 0)

theorem tuplerAV_under {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    UnderTowerOk u ρp (mkTowerGo u Ids) ((idxTyAV u Ids).liftN Ids.length 0) (tuplerData u Ids) := by
  have := underTowerOk_fields (w := u) (bodyC := (idxTyAV u Ids).liftN Ids.length 0) (ρp := ρp)
    (Fs := Ids) h.1 (fun bs hsp => by
      have hsh : shiftE Ids.length 0 (consList bs ρp) = ρp := by
        rw [← hsp.length_eq]; exact shiftE_consList bs ρp
      rw [interp_liftN, hsh]
      exact (idxTyAV_facts h).1)
    (rest := tuplerData u Ids) (pre := []) (bs := []) (by simp [tuplerData, Function.comp_def])
    trivial
  simpa using this

theorem tuplerAV_mem {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (tuplerAV u Ids) ∈ˢ interp V ρp (tuplerTyAV u Ids) :=
  mkLamsC_mem (fun _ hd => by
    obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd
    exact Iff.rfl) (tuplerAV_under h)

theorem tuplerAV_wellDenoted {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    WellDenoted V ρp (tuplerAV u Ids) :=
  mkLamsC_wellDenoted (fun _ hd => by
    obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd
    exact Iff.rfl) (tuplerAV_under h)

theorem foldl_app_pt' : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' ts

/-- **The tupler's fold**: along a fitting index spine it computes the
tuple (both regimes). -/
theorem tuplerAV_fold {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) :
    is.foldl SetTheory.app (interp V ρp (tuplerAV u Ids)) = tupW u is := by
  by_cases hu : u = 0
  · subst hu
    rw [tupW_zero]
    cases Ids with
    | nil =>
      cases is with
      | nil => rfl
      | cons _ _ => exact hsp.elim
    | cons F Ids =>
      show is.foldl SetTheory.app (interp V ρp (mkLamsAV ((0, F) :: _) _)) = _
      rw [mkLamsAV_zero_head]
      exact foldl_app_pt' is
  · unfold tuplerAV mkLamsC
    rw [mkLamsAV_fold (fun d hd => by
        obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
        exact hu) (by rw [List.map_map]; simpa [tuplerData, Function.comp_def] using hsp)]
    rw [mkTowerGo_interp (fun _ => h.2) hsp, if_neg hu, tupW_pos hu]

/-! ## The family type and the functor -/

/-- `I → Sort w`, spelled. -/
def famTyAV (u w : Nat) (Ids : List AnnotTerm) : AnnotTerm :=
  .pi u (w + 1) (idxTyAV u Ids) (.sort w)

theorem famTyAV_facts {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (h : IdxOk u ρp Ids) :
    interp V ρp (famTyAV u w Ids) = lfpFamSpace V w (idxSet u ρp Ids) ∧
      lfpFamSpace V w (idxSet u ρp Ids) ∈ˢ (univ (Nat.max u (w + 1)) : V) ∧
      WellDenoted V ρp (famTyAV u w Ids) := by
  obtain ⟨hv, hu, hok⟩ := idxTyAV_facts h
  refine ⟨?_, ?_, ?_⟩
  · unfold famTyAV lfpFamSpace
    rw [interp_pi, hv]
    rfl
  · unfold lfpFamSpace
    have := piR_mem_univ (u := u) (v := w + 1) hu (fun _ _ => univ_mem_univ w)
    rwa [if_neg (Nat.succ_ne_zero w)] at this
  · unfold famTyAV
    rw [WellDenoted_pi]
    exact ⟨hok, fun _ _ => trivial⟩

/-- A recursive field's own telescope (`a⃗ : A⃗` at a reflexive field,
task #202; empty at a finitary one) lifted past the two binders `X, t`
at position `i`: binder `k` sits under `k` earlier telescope binders. -/
def liftTele2 (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  (List.range tl.length).map fun k =>
    let d := tl.getD k default
    (d.1, d.2.1, d.2.2.liftN 2 (i + k))

omit [SetTheory V] in
@[simp] theorem liftTele2_nil (i : Nat) : liftTele2 i [] = [] := rfl

omit [SetTheory V] in
theorem liftTele2_length (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    (liftTele2 i tl).length = tl.length := by simp [liftTele2]

/-- The variables of an `m`-binder telescope, innermost last. -/
def teleVarsAV (m : Nat) : List AnnotTerm := (List.range m).map fun k => .bvar (m - 1 - k)

/-- **The recursive slot** at position `i` of an X-chain: the family
`X` (at `bvar (i + 1 + m)` under the field's `m` telescope binders)
applied to the tuple of the field's index expressions, under the
field's telescope — `Π a⃗ : A⃗, X ⟨e⃗_i(a⃗)⟩`; at a finitary field
(`tl = []`) just `X ⟨e⃗_i⟩`. -/
def slotXI (u : Nat) (Ids : List AnnotTerm) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm)
    (i : Nat) : AnnotTerm :=
  mkPisAV (liftTele2 i tl)
    (.app (.bvar (i + 1 + tl.length))
      (AnnotTerm.mkAppN ((tuplerAV u Ids).liftN (i + 2 + tl.length) 0)
        (Eis.map (·.liftN 2 (i + tl.length)))))

omit [SetTheory V] in

/-- The X-chain of one constructor from position `i` on, at the frame
`(ρp, X, t, f₀ … f_{i-1})`: a recursive slot reads `X ⟨e⃗_i⟩` under the
field's telescope (`slotXI`), an ordinary domain is lifted past `X`
and `t`. -/
def chainXIGo (u : Nat) (Ids : List AnnotTerm) (rs : List Bool) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) : List AnnotTerm → Nat → List AnnotTerm
  | [], _ => []
  | F :: Fs, i =>
    (if rs.getD i false then slotXI u Ids (tls.getD i []) (Eis.getD i []) i
     else F.liftN 2 i) :: chainXIGo u Ids rs tls Eis Fs (i + 1)

/-- The index equations at the chain's end: the constructor's index
expressions against the projections of the tuple `t` (at `bvar nF`). -/
def eqsXI (nIdx nF : Nat) (Es : List AnnotTerm) : List (AnnotTerm × AnnotTerm) :=
  (List.range nIdx).map fun l => ((Es.getD l default).liftN 2 nF, projAV l (.bvar nF))

/-- One constructor's X-chain, equation-terminated. -/
def chainXI (u : Nat) (Ids : List AnnotTerm) (nIdx : Nat) (rs : List Bool) (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm))
    (Fs Es : List AnnotTerm) : List AnnotTerm :=
  chainXIGo u Ids rs tls Eis Fs 0 ++ [idxEqAV (eqsXI nIdx Fs.length Es)]

/-- The X-chains of all constructors. -/
def chainsXI (u : Nat) (Ids : List AnnotTerm) (nIdx : Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : List (List AnnotTerm) :=
  (List.range Fss.length).map fun j =>
    chainXI u Ids nIdx (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j [])

theorem chainsXI_getElem? (u : Nat) (Ids : List AnnotTerm) (nIdx : Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) (j : Nat) :
    (chainsXI u Ids nIdx rss tlss Eiss Fss Ess)[j]?
      = if j < Fss.length then
          some (chainXI u Ids nIdx (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j []))
        else none := by
  unfold chainsXI
  rw [List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simpa using h)]; rfl

omit [SetTheory V] in

/-- The functor's λ: `λ (X : I → Sort w) (t : I). Σ_j tower_j(X, t)`. -/
def fixFunAVI (u w : Nat) (Ids : List AnnotTerm) (nIdx : Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : AnnotTerm :=
  .lam (Nat.max u (w + 1)) (famTyAV u w Ids)
    (.lam (w + 1) ((idxTyAV u Ids).liftN 1 0) (sumBodyAV w (chainsXI u Ids nIdx rss tlss Eiss Fss Ess)))

/-- The family: `lfpFam.{u,w} I F` at the parameter frame. -/
def fixBodyAVI (u w : Nat) (Ids : List AnnotTerm) (nIdx : Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .lfpFam [u, w]) [idxTyAV u Ids, fixFunAVI u w Ids nIdx rss tlss Eiss Fss Ess]

/-- The type-former leaf: the λ-tower over the parameter and index
domains, the family at the tuple of the index variables. -/
def nativeTyAVI (u w : Nat) (pps : List (Nat × Nat × AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) :
    AnnotTerm :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2))
    (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0) (mkTowerGo u Ids))

/-! ## The semantic functor -/

/-- The functor's fibre at `(X, t)`. -/
noncomputable def fixStepI (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm))
    (X t : V) : V :=
  sumSet w (sumFibre w (cons t (cons X ρp)) (chainsXI u Ids nIdx rss tlss Eiss Fss Ess))

/-- The functor on families (as a set-level function of `X`). -/
noncomputable def famFI (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm))
    (X : V) : V :=
  lamR (w + 1) (idxSet u ρp Ids) fun t => fixStepI u w ρp Ids nIdx rss tlss Eiss Fss Ess X t

/-- The functor as a set. -/
noncomputable def fixFunVI (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : V :=
  lamR (Nat.max u (w + 1)) (lfpFamSpace V w (idxSet u ρp Ids))
    fun X => famFI u w ρp Ids nIdx rss tlss Eiss Fss Ess X

/-- The least pre-fixed family. -/
noncomputable def fixFamI (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : V :=
  lfpFamSet w (idxSet u ρp Ids) (fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss Ess)

/-- The grading premise: at every family `X` and tuple `t` the X-chains
are graded. -/
def FixChainsOkI (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) :
    Prop :=
  ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
    SumFieldsOkB w (cons t (cons X ρp)) (chainsXI u Ids nIdx rss tlss Eiss Fss Ess)

section Facts

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {nIdx : Nat} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}

theorem fixStepI_univ (hok : FixChainsOkI u w ρp Ids nIdx rss tlss Eiss Fss Ess) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V} (ht : t ∈ˢ idxSet u ρp Ids) :
    fixStepI u w ρp Ids nIdx rss tlss Eiss Fss Ess X t ∈ˢ (univ w : V) :=
  sumSet_univ_of_okB (hok X hX t ht)

theorem famFI_mem (hok : FixChainsOkI u w ρp Ids nIdx rss tlss Eiss Fss Ess) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) :
    famFI u w ρp Ids nIdx rss tlss Eiss Fss Ess X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) :=
  lamR_mem fun _ ht => fixStepI_univ hok hX ht

theorem famFI_app {X t : V} (ht : t ∈ˢ idxSet u ρp Ids) :
    SetTheory.app (famFI u w ρp Ids nIdx rss tlss Eiss Fss Ess X) t
      = fixStepI u w ρp Ids nIdx rss tlss Eiss Fss Ess X t :=
  app_lamR_pos (a := t) (Nat.succ_ne_zero w) ht

theorem fixFunVI_mem (hok : FixChainsOkI u w ρp Ids nIdx rss tlss Eiss Fss Ess) :
    fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss Ess ∈ˢ lfpFamFunSpace V u w (idxSet u ρp Ids) :=
  lamR_mem fun _ hX => famFI_mem hok hX

theorem fixFunVI_app {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) :
    SetTheory.app (fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss Ess) X
      = famFI u w ρp Ids nIdx rss tlss Eiss Fss Ess X :=
  app_lamR_pos (max_succ_ne_zero u w) hX

/-- The frame under the functor's two binders. -/
theorem idxTyAV_lift1 (h : IdxOk u ρp Ids) (X : V) :
    interp V (cons X ρp) ((idxTyAV u Ids).liftN 1 0) = idxSet u ρp Ids ∧
      WellDenoted V (cons X ρp) ((idxTyAV u Ids).liftN 1 0) := by
  rw [interp_liftN, WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]
  exact ⟨(idxTyAV_facts h).1, (idxTyAV_facts h).2.2⟩

/-- **The functor's λ**: its value, its membership, its grading. -/
theorem fixFunAVI_facts (hI : IdxOk u ρp Ids) (hok : FixChainsOkI u w ρp Ids nIdx rss tlss Eiss Fss Ess) :
    interp V ρp (fixFunAVI u w Ids nIdx rss tlss Eiss Fss Ess) = fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss Ess ∧
      WellDenoted V ρp (fixFunAVI u w Ids nIdx rss tlss Eiss Fss Ess) := by
  obtain ⟨hfv, hfu, hfok⟩ := famTyAV_facts (w := w) hI
  refine ⟨?_, ?_⟩
  · unfold fixFunAVI fixFunVI
    rw [interp_lam, hfv]
    refine lamR_congr fun X hX => ?_
    unfold famFI
    rw [interp_lam, (idxTyAV_lift1 hI X).1]
    refine lamR_congr fun t ht => ?_
    exact sumBodyAV_interp (hok X hX t ht)
  · unfold fixFunAVI
    rw [WellDenoted_lam]
    refine ⟨hfok, fun X hX => ?_, fun _ => lfpFamSpace V w (idxSet u ρp Ids), fun X hX => ?_,
      fun h => absurd h (max_succ_ne_zero u w)⟩
    · rw [hfv] at hX
      rw [WellDenoted_lam]
      refine ⟨(idxTyAV_lift1 hI X).2, fun t ht => ?_, fun _ => (univ w : V), fun t ht => ?_,
        fun h => absurd h (Nat.succ_ne_zero w)⟩
      · rw [(idxTyAV_lift1 hI X).1] at ht
        exact sumBodyAV_wellDenoted (hok X hX t ht)
      · rw [(idxTyAV_lift1 hI X).1] at ht
        rw [sumBodyAV_interp (hok X hX t ht)]
        exact fixStepI_univ hok hX ht
    · rw [hfv] at hX
      rw [interp_lam, (idxTyAV_lift1 hI X).1]
      refine lamR_mem fun t ht => ?_
      rw [sumBodyAV_interp (hok X hX t ht)]
      exact fixStepI_univ hok hX ht

/-- **The family**: its value, its membership, its grading. -/
theorem fixBodyAVI_facts (hI : IdxOk u ρp Ids) (hok : FixChainsOkI u w ρp Ids nIdx rss tlss Eiss Fss Ess) :
    interp V ρp (fixBodyAVI u w Ids nIdx rss tlss Eiss Fss Ess) = fixFamI u w ρp Ids nIdx rss tlss Eiss Fss Ess ∧
      fixFamI u w ρp Ids nIdx rss tlss Eiss Fss Ess ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) ∧
      WellDenoted V ρp (fixBodyAVI u w Ids nIdx rss tlss Eiss Fss Ess) := by
  obtain ⟨hiv, hiu, hiok⟩ := idxTyAV_facts hI
  obtain ⟨hfv, hfok⟩ := fixFunAVI_facts hI hok
  have hc : interp V ρp (.const .lfpFam [u, w]) = lfpFamV V u w := rfl
  refine ⟨?_, lfpFamSet_mem_space V w _ _, ?_⟩
  · show SetTheory.app (SetTheory.app (interp V ρp (.const .lfpFam [u, w]))
      (interp V ρp (idxTyAV u Ids))) (interp V ρp (fixFunAVI u w Ids nIdx rss tlss Eiss Fss Ess)) = _
    rw [hc, hiv, hfv]
    exact lfpFamV_app V hiu (fixFunVI_mem hok)
  · show WellDenoted V ρp (.app (.app (.const .lfpFam [u, w]) _) _)
    rw [WellDenoted_app]
    refine ⟨?_, hfok, Nat.max u (w + 1), lfpFamFunSpace V u w (idxSet u ρp Ids),
      fun _ => lfpFamSpace V w (idxSet u ρp Ids), ?_, ?_, fun h => absurd h (max_succ_ne_zero u w)⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, hiok, Nat.max u (w + 1), univ u,
        fun I => piR (Nat.max u (w + 1)) (lfpFamFunSpace V u w I) fun _ => lfpFamSpace V w I,
        lfpFamV_mem V u w, by rw [hiv]; exact hiu, fun h => absurd h (max_succ_ne_zero u w)⟩
    · show SetTheory.app (interp V ρp (.const .lfpFam [u, w])) (interp V ρp (idxTyAV u Ids)) ∈ˢ _
      rw [hc, hiv]
      exact app_mem_piR_pos (max_succ_ne_zero u w) (lfpFamV_mem V u w) hiu
    · rw [hfv]; exact fixFunVI_mem hok

end Facts

/-! ## The leaf -/

/-- The base of the leaf's premise, at the frame below the parameters
AND the index binders: the index telescope graded at the parameter
frame, the X-chains graded there, the frame's index tuple fitting. -/
def FixBaseI (u w : Nat) (ρ : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : Prop :=
  IdxOk u (shiftE Ids.length 0 ρ) Ids ∧
  FixChainsOkI u w (shiftE Ids.length 0 ρ) Ids Ids.length rss tlss Eiss Fss Ess ∧
  SpineFit (shiftE Ids.length 0 ρ) Ids (frameIdx Ids.length ρ)

/-- `ParamsOkXI`: the leaf's one hereditary premise — the parameter
and index telescope graded, `FixBaseI` at the base. -/
def ParamsOkXI (u w : Nat) (ρ : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => FixBaseI u w ρ Ids rss tlss Eiss Fss Ess
  | d :: pps => d.2.1 ≠ 0 ∧ WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → ParamsOkXI u w (cons a ρ) Ids rss tlss Eiss Fss Ess pps

omit [SetTheory V] in
theorem frameIdx_succ (n : Nat) (ρ : Nat → V) : frameIdx (n + 1) ρ = ρ n :: frameIdx n ρ := by
  unfold frameIdx
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  show ρ (n + 1 - 1 - 0) :: _ = _
  rw [show n + 1 - 1 - 0 = n from rfl]
  congr 1
  apply List.map_congr_left
  intro l _
  show ρ (n + 1 - 1 - (l + 1)) = ρ (n - 1 - l)
  rw [show n + 1 - 1 - (l + 1) = n - 1 - l from by omega]

omit [SetTheory V] in
/-- The index tuple of a consed spine. -/
theorem frameIdx_consList' : ∀ (is : List V) (ρ : Nat → V),
    frameIdx is.length (consList is ρ) = is
  | [], _ => rfl
  | a :: as, ρ => by
    rw [consList_cons, List.length_cons, frameIdx_succ, frameIdx_consList' as (cons a ρ)]
    congr 1
    have := consList_apply_add as (cons a ρ) 0
    rw [Nat.zero_add] at this
    exact this

omit [SetTheory V] in
/-- A frame is its index tuple over its shift. -/
theorem consList_frameIdx : ∀ (n : Nat) (ρ : Nat → V),
    consList (frameIdx n ρ) (shiftE n 0 ρ) = ρ
  | 0, ρ => by
    show consList [] (shiftE 0 0 ρ) = ρ
    rw [consList_nil, shiftE_zero_zero]
  | n + 1, ρ => by
    have hfr : frameIdx (n + 1) ρ = ρ n :: frameIdx n ρ := frameIdx_succ n ρ
    have hsh : cons (ρ n) (shiftE (n + 1) 0 ρ) = shiftE n 0 ρ := by
      funext i
      cases i with
      | zero => show ρ n = ρ (0 + n); rw [Nat.zero_add]
      | succ i =>
        show ρ (i + (n + 1)) = ρ (i + 1 + n)
        rw [show i + (n + 1) = i + 1 + n from by omega]
    rw [hfr, consList_cons, hsh]
    exact consList_frameIdx n ρ

/-- The body's reading at the base frame: the family at the frame's
tuple. -/
theorem fixLeafBody_facts {u w : Nat} {ρ : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (h : FixBaseI u w ρ Ids rss tlss Eiss Fss Ess) :
    interp V ρ (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids))
      = SetTheory.app (fixFamI u w (shiftE Ids.length 0 ρ) Ids Ids.length rss tlss Eiss Fss Ess)
          (tupW u (frameIdx Ids.length ρ)) ∧
    interp V ρ (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids)) ∈ˢ (univ w : V) ∧
    WellDenoted V ρ (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids)) := by
  obtain ⟨hI, hok, hsp⟩ := h
  obtain ⟨hbv, hbm, hbok⟩ := fixBodyAVI_facts hI hok
  have hρ : consList (frameIdx Ids.length ρ) (shiftE Ids.length 0 ρ) = ρ :=
    consList_frameIdx Ids.length ρ
  have hlift : interp V ρ ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
      = fixFamI u w (shiftE Ids.length 0 ρ) Ids Ids.length rss tlss Eiss Fss Ess := by
    rw [interp_liftN, hbv]
  have hliftok : WellDenoted V ρ ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0) := by
    rw [WellDenoted_liftN]; exact hbok
  have htv : interp V ρ (mkTowerGo u Ids) = tupW u (frameIdx Ids.length ρ) := by
    have h1 := mkTowerGo_interp (ρp := shiftE Ids.length 0 ρ) (bs := frameIdx Ids.length ρ)
      (fun _ => hI.2) hsp
    rw [hρ] at h1
    rw [h1]
    rfl
  have htok : WellDenoted V ρ (mkTowerGo u Ids) := by
    have h1 := mkTowerGo_wellDenoted (ρp := shiftE Ids.length 0 ρ) (bs := frameIdx Ids.length ρ) hI.1 hsp
    rwa [hρ] at h1
  have htmem : tupW u (frameIdx Ids.length ρ) ∈ˢ idxSet u (shiftE Ids.length 0 ρ) Ids := tupW_mem hsp
  refine ⟨?_, ?_, ?_⟩
  · rw [interp_app, hlift, htv]
  · rw [interp_app, hlift, htv]
    exact famSpace_app (by unfold lfpFamSpace at hbm; rwa [piR_pos (Nat.succ_ne_zero w)] at hbm) htmem
  · rw [WellDenoted_app]
    refine ⟨hliftok, htok, w + 1, idxSet u (shiftE Ids.length 0 ρ) Ids, fun _ => (univ w : V),
      ?_, ?_, fun h => absurd h (Nat.succ_ne_zero w)⟩
    · rw [hlift]; exact hbm
    · rw [htv]; exact htmem

/-- **The leaf inhabits its type's reading.** -/
theorem nativeTyAVI_mem {u w : Nat} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkXI u w ρ Ids rss tlss Eiss Fss Ess pps →
      interp V ρ (nativeTyAVI u w pps Ids rss tlss Eiss Fss Ess) ∈ˢ interp V ρ (mkPisAV pps (.sort w))
  | [], ρ, h => (fixLeafBody_facts h).2.1
  | d :: pps, ρ, h => by
    show (lamR (w + 1) (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamR_mem_zero_agree (iff_of_false (Nat.succ_ne_zero w) h.1)
      (fun a ha => nativeTyAVI_mem (h.2.2 a ha))

/-- **The leaf is graded.** -/
theorem nativeTyAVI_wellDenoted {u w : Nat} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkXI u w ρ Ids rss tlss Eiss Fss Ess pps →
      WellDenoted V ρ (nativeTyAVI u w pps Ids rss tlss Eiss Fss Ess)
  | [], _, h => (fixLeafBody_facts h).2.2
  | d :: pps, ρ, h => by
    show WellDenoted V ρ (.lam (w + 1) d.2.2 (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
    rw [WellDenoted_lam]
    exact ⟨h.2.1, fun a ha => nativeTyAVI_wellDenoted (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => nativeTyAVI_mem (h.2.2 a ha),
       fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩⟩

/-- **The leaf's application fold**: along a fitting parameter-and-
index spine the leaf computes the family at the spine's tuple. -/
theorem nativeTyAVI_fold {u w : Nat} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hbase : FixBaseI u w (consList as ρ) Ids rss tlss Eiss Fss Ess) :
    as.foldl SetTheory.app (interp V ρ (nativeTyAVI u w pps Ids rss tlss Eiss Fss Ess))
      = SetTheory.app
          (fixFamI u w (shiftE Ids.length 0 (consList as ρ)) Ids Ids.length rss tlss Eiss Fss Ess)
          (tupW u (frameIdx Ids.length (consList as ρ))) := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [nativeTyAVI,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp']
  exact (fixLeafBody_facts hbase).1

end ConLeche.Semantics
