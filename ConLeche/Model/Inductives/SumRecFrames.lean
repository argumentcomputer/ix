module

public import ConLeche.Model.Inductives.SumRecData
public import ConLeche.Model.Inductives.SumStageCtor
import ConLeche.Model.Inductives.StructRecFrames
public section

/-!
# The sum recursor's frames (task #175 sum-types, indexed)

`sumRecFrames`: at a parameter frame, the generated sum recursor's
entries read to the recursor leaf's premise `RecBaseS` — the motive
entry to the nested product over the former's index telescope into
the family at each index tuple, minor entry `j` (at the frame under
the motive and the earlier minors) to constructor `j`'s minor space
`minorSpI` (its conclusion at the constructor's own index values),
the index entries to the former's index telescope, the major entry
to the family at the frame's index tuple — and the K-frame's two
hypothesis records (`RecHypS`, `SqHypS`).  The walk: down the minor
chain (`sumMinorsTail`), then down the index chain (`sumIdxTail`),
the frame kept as an explicit `consList`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
@[expose] def fssOf (nP : Nat) (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The index readings of the constructor data. -/
@[expose] def essOf (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => cd.2.2.2

theorem fssOf_length (nP : Nat) (cds : List CtorDatum) : (fssOf nP cds).length = cds.length := by
  simp [fssOf]

theorem fssOf_getElem? (nP : Nat) (cds : List CtorDatum) (j : Nat) :
    (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOf]

theorem essOf_getElem? (cds : List CtorDatum) (j : Nat) :
    (essOf cds)[j]? = cds[j]?.map fun cd => cd.2.2.2 := by
  simp [essOf]

/-! ## The recursor data's entries -/

section Entries

variable {pds dms dis : List (Nat × Nat × AnnotTerm)} {dM dt : Nat × Nat × AnnotTerm}

end Entries

/-! ## The nested product over a telescope, read -/

/-- **A Π-tower over nonzero-bit domains is the nested product** over
the domains' telescope, the body at the accumulated tuple. -/
theorem interp_mkPisAV_piTele {v : Nat} {B : List V → V} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V} {acc : List V},
      (∀ d ∈ gds, (d.2.1 = 0 ↔ v = 0)) →
      (∀ as : List V, SpineFit σ (gds.map (·.2.2)) as → interp V (consList as σ) R = B (acc ++ as)) →
      interp V σ (mkPisAV gds R) = piTele v (teleOfFields σ (gds.map (·.2.2))) B acc
  | [], σ, acc, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simp only [mkPisAV]
    exact this
  | d :: gds, σ, acc, hbits, hbase => by
    simp only [mkPisAV, interp_pi]
    rw [piR_congr_bit (v := d.2.1) (v' := v) (hbits d List.mem_cons_self)]
    apply piR_congr
    intro a ha
    refine interp_mkPisAV_piTele (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_
    intro as hsp
    have := hbase (a :: as) ⟨ha, hsp⟩
    rw [consList_cons] at this
    rw [this, List.append_assoc, List.singleton_append]

/-! ## The minor space, read -/

/-- **The minor space with an explicit conclusion is the interpreted
Π-tower** over field domains agreeing with the chain's. -/
theorem interp_minorSpI_of_tele {ℓ : Nat} {c : List V → V} :
    ∀ {Fs : List AnnotTerm} {gds : List (Nat × Nat × AnnotTerm)} {Rm : AnnotTerm}
      {σ ρf : Nat → V} {acc : List V},
      gds.length = Fs.length →
      (∀ d ∈ gds, (ℓ = 0 ↔ d.2.1 = 0)) →
      (∀ (j : Nat) (as : List V), j < Fs.length → SpineFit ρf (Fs.take j) as →
        interp V (consList as σ) ((gds.getD j default).2.2)
          = interp V (consList as ρf) (Fs.getD j default)) →
      (∀ as : List V, SpineFit ρf Fs as →
        interp V (consList as σ) Rm = c (acc ++ as)) →
      interp V σ (mkPisAV gds Rm) = minorSpI ℓ c Fs ρf acc
  | [], [], Rm, σ, ρf, acc, _, _, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simpa [mkPisAV, minorSpI] using this
  | [], _ :: _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _, _, _ => by simp at hlen
  | F :: Fs, d :: gds, Rm, σ, ρf, acc, hlen, hbits, hdom, hbase => by
    simp only [mkPisAV, interp_pi, minorSpI]
    have hd0 : interp V σ d.2.2 = interp V ρf F := by
      have := hdom 0 [] (by simp) trivial
      simpa [consList] using this
    rw [hd0, piR_congr_bit (v := d.2.1) (v' := ℓ) (hbits d List.mem_cons_self).symm]
    apply piR_congr
    intro a ha
    refine interp_minorSpI_of_tele (by simpa using hlen)
      (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_ ?_
    · intro j as hj hsp
      have := hdom (j + 1) (a :: as) (by simpa using hj)
        (by simp only [List.take_succ_cons, SpineFit]; exact ⟨ha, hsp⟩)
      simpa [consList_cons] using this
    · intro as hsp
      have := hbase (a :: as) ⟨ha, hsp⟩
      rw [consList_cons] at this
      rw [this, List.append_cons]

/-! ## The K-frame -/

section KFrame

variable {ρp : Nat → V} {M : V} {ms is : List V} {n nIdx : Nat}

omit [SetTheory V] in
theorem kframe_apply_add (his : is.length = nIdx) (hms : ms.length = n) (i : Nat) :
    consList is (consList ms (cons M ρp)) (i + (nIdx + n + 1)) = ρp i := by
  rw [show i + (nIdx + n + 1) = (i + 1 + n) + is.length from by omega, consList_apply_add,
    show i + 1 + n = (i + 1) + ms.length from by omega, consList_apply_add]
  rfl

omit [SetTheory V] in
theorem kframe_frP (his : is.length = nIdx) (hms : ms.length = n) :
    frP n nIdx (consList is (consList ms (cons M ρp))) = ρp := by
  unfold frP
  rw [shiftE_zero]
  funext i
  exact kframe_apply_add his hms i

omit [SetTheory V] in
theorem kframe_frM (his : is.length = nIdx) (hms : ms.length = n) :
    frM n nIdx (consList is (consList ms (cons M ρp))) = M := by
  unfold frM
  rw [show nIdx + n = n + is.length from by omega, consList_apply_add,
    show n = 0 + ms.length from by omega, consList_apply_add]
  rfl

theorem kframe_frMs (his : is.length = nIdx) (hms : ms.length = n) {j : Nat} (hj : j < n) :
    frMs n nIdx (consList is (consList ms (cons M ρp))) j = ms.getD j pt := by
  unfold frMs
  rw [show nIdx + n - 1 - j = (n - 1 - j) + is.length from by omega, consList_apply_add,
    consList_apply_lt _ _ _ (by omega), hms, show n - 1 - (n - 1 - j) = j from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    Option.getD_some]

omit [SetTheory V] in
theorem kframe_frameIdx (his : is.length = nIdx) :
    frameIdx nIdx (consList is (consList ms (cons M ρp))) = is :=
  frameIdx_consList his _

end KFrame

/-! ## The restricted chains at two frames -/

/-- The restricted tower depends on the frame only through the
shifted frame and the index tuple. -/
theorem towerSet_rChain_congr {w d d' nIdx : Nat} {Fs Es : List AnnotTerm} {σ σ' : Nat → V}
    (hEs : Es.length = nIdx) (hsh : shiftE d 0 σ = shiftE d' 0 σ')
    (hidx : frameIdx nIdx σ = frameIdx nIdx σ') :
    towerSet w (teleOfFields σ (rChain d nIdx Fs Es))
      = towerSet w (teleOfFields σ' (rChain d' nIdx Fs Es)) := by
  unfold rChain
  apply SetTheory.ext
  intro y
  by_cases hw : w = 0
  · subst hw
    constructor
    · intro hy
      obtain ⟨rfl, bs, hsp, hall⟩ := restricted_member_zero hy
      have hsp' : SpineFit (shiftE d 0 σ) Fs bs := (spineFit_liftFields d).mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, hsh, hidx] at hall
      have := restricted_member_intro (w := 0) (Fs := liftFields d' 0 Fs)
        ((spineFit_liftFields d').mpr (hsh ▸ hsp'))
        ((EqAll_idxEqsAt (d := d') hEs hsp'.length_eq).mpr hall)
      rw [if_pos rfl] at this
      exact this
    · intro hy
      obtain ⟨rfl, bs, hsp, hall⟩ := restricted_member_zero hy
      have hsp' : SpineFit (shiftE d' 0 σ') Fs bs := (spineFit_liftFields d').mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, ← hsh, ← hidx] at hall
      have := restricted_member_intro (w := 0) (Fs := liftFields d 0 Fs)
        ((spineFit_liftFields d).mpr (hsh.symm ▸ hsp'))
        ((EqAll_idxEqsAt (d := d) hEs hsp'.length_eq).mpr hall)
      rw [if_pos rfl] at this
      exact this
  · constructor
    · intro hy
      obtain ⟨hsp, -, hall, heta⟩ := restricted_member_elim hw hy
      rw [liftFields_length] at hsp hall heta
      have hsp' : SpineFit (shiftE d 0 σ) Fs (projList Fs.length y) := (spineFit_liftFields d).mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, hsh, hidx] at hall
      have := restricted_member_intro (w := w) (Fs := liftFields d' 0 Fs)
        ((spineFit_liftFields d').mpr (hsh ▸ hsp'))
        ((EqAll_idxEqsAt (d := d') hEs hsp'.length_eq).mpr hall)
      rw [if_neg hw] at this
      rw [heta]
      exact this
    · intro hy
      obtain ⟨hsp, -, hall, heta⟩ := restricted_member_elim hw hy
      rw [liftFields_length] at hsp hall heta
      have hsp' : SpineFit (shiftE d' 0 σ') Fs (projList Fs.length y) :=
        (spineFit_liftFields d').mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, ← hsh, ← hidx] at hall
      have := restricted_member_intro (w := w) (Fs := liftFields d 0 Fs)
        ((spineFit_liftFields d).mpr (hsh.symm ▸ hsp'))
        ((EqAll_idxEqsAt (d := d) hEs hsp'.length_eq).mpr hall)
      rw [if_neg hw] at this
      rw [heta]
      exact this

/-- The sum fibre over the restricted chains depends on the frame
only through the shifted frame and the index tuple. -/
theorem sumFibre_rChains_congr {w d d' nIdx : Nat} {Fss Ess : List (List AnnotTerm)} {σ σ' : Nat → V}
    (hEs : ∀ j, j < Fss.length → (Ess.getD j []).length = nIdx) (hlenE : Ess.length = Fss.length)
    (hsh : shiftE d 0 σ = shiftE d' 0 σ') (hidx : frameIdx nIdx σ = frameIdx nIdx σ') :
    sumFibre w σ (rChains d nIdx Fss Ess) = sumFibre w σ' (rChains d' nIdx Fss Ess) := by
  funext i
  rcases Nat.lt_or_ge i Fss.length with hi | hi
  · obtain ⟨Fs, hFs⟩ : ∃ Fs, Fss[i]? = some Fs := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨Es, hEs'⟩ : ∃ Es, Ess[i]? = some Es := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h1 : (rChains d nIdx Fss Ess)[i]? = some (rChain d nIdx Fs Es) := by
      rw [rChains_getElem?, hFs, hEs']
    have h2 : (rChains d' nIdx Fss Ess)[i]? = some (rChain d' nIdx Fs Es) := by
      rw [rChains_getElem?, hFs, hEs']
    rw [sumFibre_of_getElem? h1, sumFibre_of_getElem? h2]
    have hEsD : Ess.getD i [] = Es := by rw [List.getD_eq_getElem?_getD, hEs']; rfl
    exact towerSet_rChain_congr (by rw [← hEsD]; exact hEs i hi) hsh hidx
  · rw [sumFibre_of_ge (by rw [rChains_length, hlenE]; exact Nat.le_trans (Nat.min_le_left _ _) hi),
      sumFibre_of_ge (by rw [rChains_length, hlenE]; exact Nat.le_trans (Nat.min_le_left _ _) hi)]

/-! ## The family spine at an index tuple -/

/-! ## The sources at a fitting spine -/

/-! ## The index chain -/

/-! ## The minor chain -/

end ConLeche.Model
