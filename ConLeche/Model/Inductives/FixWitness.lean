module

public import ConLeche.Model.Inductives.FixChains
public import ConLeche.SetModel.Container
public import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The closure witness of the fixpoint route's family functor (task #202, Stage B)

The family functor `fixFunVI` of a recursive block is a container in
the sense of `ConLeche/SetModel/Container.lean`: an element of its fibre
at a tuple is a tagged tuple `inj j (mkTower (fs ++ [pt]))` whose
recursive slots hold nested functions over the fields' telescopes into
the family's fibres; its SHAPE is the shadow tuple — the recursive
slots replaced by the shadow value (the chain facts read every domain,
telescope and index expression at frames whose recursive slots hold an
arbitrary value: `ChainFacts.nb`/`nbT`/`nbE`/`nbEs`, the kernel's
`structUsedLater` guard) — its POSITIONS are the recursive fields'
telescope spines (tagged by the field's position), its TARGETS the
calls' index tuples, and the builder curries a function on spines back
into the slots (`lamTower`).  `container_closed_exists` then yields the
closed member family `fixFunVI_closed_exists` needs, for every block —
finitary or not, any sort — replacing the ω-iterate and the top-family
witnesses.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Shadow spines -/

/-- The shadow spine of a field spine from position `i` on: the
recursive slots hold the shadow value. -/
noncomputable def shadowOfGo (nP : Nat) (ks : List RecFieldKind) : Nat → List V → List V
  | _, [] => []
  | i, a :: as => (if recAt nP ks (nP + i) then shadowVal else a) :: shadowOfGo nP ks (i + 1) as

/-- The shadow spine of a field spine. -/
noncomputable def shadowOf (nP : Nat) (ks : List RecFieldKind) (fs : List V) : List V := shadowOfGo nP ks 0 fs

theorem shadowOfGo_length (nP : Nat) (ks : List RecFieldKind) :
    ∀ (i : Nat) (fs : List V), (shadowOfGo nP ks i fs).length = fs.length
  | _, [] => rfl
  | i, _ :: fs => by simp [shadowOfGo, shadowOfGo_length nP ks (i + 1) fs]

theorem shadowOf_length (nP : Nat) (ks : List RecFieldKind) (fs : List V) :
    (shadowOf nP ks fs).length = fs.length := shadowOfGo_length nP ks 0 fs

theorem shadowOfGo_getD (nP : Nat) (ks : List RecFieldKind) :
    ∀ (i : Nat) (fs : List V) (l : Nat), l < fs.length →
      (shadowOfGo nP ks i fs).getD l pt = if recAt nP ks (nP + (i + l)) then shadowVal else fs.getD l pt
  | _, [], _, hl => absurd hl (Nat.not_lt_zero _)
  | i, a :: fs, 0, _ => by simp [shadowOfGo]
  | i, a :: fs, l + 1, hl => by
    simp only [shadowOfGo, List.getD_cons_succ]
    rw [shadowOfGo_getD nP ks (i + 1) fs l (by simpa using hl),
      show i + 1 + l = i + (l + 1) from by omega]

theorem shadowOf_getD {nP : Nat} {ks : List RecFieldKind} {fs : List V} {l : Nat} (hl : l < fs.length) :
    (shadowOf nP ks fs).getD l pt = if recAt nP ks (nP + l) then shadowVal else fs.getD l pt := by
  unfold shadowOf
  rw [shadowOfGo_getD nP ks 0 fs l hl, Nat.zero_add]

theorem shadowRel_shadowOf (nP : Nat) (ks : List RecFieldKind) (fs : List V) :
    ShadowRel nP ks fs (shadowOf nP ks fs) :=
  ⟨shadowOf_length nP ks fs, fun l hl hr => by rw [shadowOf_getD hl, if_neg hr]⟩

theorem shadowOfGo_append (nP : Nat) (ks : List RecFieldKind) :
    ∀ (i : Nat) (fs gs : List V),
      shadowOfGo nP ks i (fs ++ gs) = shadowOfGo nP ks i fs ++ shadowOfGo nP ks (i + fs.length) gs
  | _, [], _ => by simp [shadowOfGo]
  | i, a :: fs, gs => by
    simp only [List.cons_append, shadowOfGo, List.length_cons, shadowOfGo_append nP ks (i + 1) fs gs]
    rw [show i + 1 + fs.length = i + (fs.length + 1) from by omega]

theorem shadowOfGo_take (nP : Nat) (ks : List RecFieldKind) :
    ∀ (o : Nat) (fs : List V) (i : Nat),
      (shadowOfGo nP ks o fs).take i = shadowOfGo nP ks o (fs.take i)
  | _, [], _ => by simp [shadowOfGo]
  | o, a :: fs, 0 => rfl
  | o, a :: fs, i + 1 => by
    simp only [shadowOfGo, List.take_succ_cons]
    rw [shadowOfGo_take nP ks (o + 1) fs i]

theorem shadowOf_take (nP : Nat) (ks : List RecFieldKind) (fs : List V) (i : Nat) :
    (shadowOf nP ks fs).take i = shadowOf nP ks (fs.take i) :=
  shadowOfGo_take nP ks 0 fs i

/-! ## Graded field chains from pointwise facts -/

/-- **The shadow fields are graded** (at a positive sort): the ordinary
domains by the chain facts at shadow spines, the recursive slots
`Sort 0` — a member of every positive universe. -/
theorem shadowFs_okB {u w nP nF : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm}
    {ks : List RecFieldKind} {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm}
    {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}
    (hC : ChainFacts u w nP nF ρp Ids ks tls Fs Eis Es) :
    FieldsOkB w ρp (shadowFs nP ks nF Fs) := by
  refine fieldsOkB_of_pointwise fun i hi as hsp => ?_
  rw [shadowFs_length] at hi
  have hget : (shadowFs nP ks nF Fs).getD i default
      = if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default := by
    rw [List.getD_eq_getElem?_getD, shadowFs_getElem? hi]; rfl
  rw [hget]
  by_cases hr : recAt nP ks (nP + i)
  · rw [if_pos hr]
    refine ⟨trivial, fun _ => ?_⟩
    rw [interp_sort]
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    exact univ_mono (Nat.succ_le_succ (Nat.zero_le w')) _ (univ_mem_univ 0)
  · rw [if_neg hr]
    obtain ⟨hok, hmem, -⟩ := hC.gr i hi as hsp
    exact ⟨hok, fun hw' => hmem hr hw'⟩

/-! ## The shapes: the shadow tuples -/

/-- The shadow field lists of all constructors. -/
def shadowFss (nP : Nat) (ksF : Nat → List RecFieldKind) (Fss : List (List AnnotTerm)) :
    List (List AnnotTerm) :=
  (List.range Fss.length).map fun j => shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])

theorem shadowFss_length (nP : Nat) (ksF : Nat → List RecFieldKind) (Fss : List (List AnnotTerm)) :
    (shadowFss nP ksF Fss).length = Fss.length := by simp [shadowFss]

theorem shadowFss_getElem? (nP : Nat) (ksF : Nat → List RecFieldKind) (Fss : List (List AnnotTerm))
    {j : Nat} (hj : j < Fss.length) :
    (shadowFss nP ksF Fss)[j]? = some (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) := by
  simp [shadowFss, List.getElem?_range hj]

/-- **The shape set at a tuple**: the shadow tuples of the constructors
whose index values are the tuple's. -/
noncomputable def shapeSet (u w nP : Nat) (ρp : Nat → V) (Ids : List AnnotTerm)
    (ksF : Nat → List RecFieldKind) (Fss Ess : List (List AnnotTerm)) (t : V) : V :=
  sep (sumSet w (sumFibre w ρp (uChains (shadowFss nP ksF Fss)))) fun a =>
    ∃ j as', j < Fss.length ∧ a = inj j (mkTower (as' ++ [pt])) ∧
      as'.length = (Fss.getD j []).length ∧
      idxValsAt ρp (Ess.getD j []) as' = isOfW u Ids.length t

/-- The tag of a tagged tuple. -/
noncomputable def shapeTag (a : V) : Nat := natIdx (sfst a)

/-- The fields of a tagged tuple. -/
noncomputable def shapeFields (nF : Nat) (a : V) : List V := projList nF (ssnd a)

theorem shapeTag_inj (j : Nat) (x : V) : shapeTag (inj j x) = j := by
  unfold shapeTag inj
  rw [sfst_spair, natIdx_vnat]

theorem shapeFields_inj (j : Nat) (as bs : List V) :
    shapeFields as.length (inj j (mkTower (as ++ bs))) = as := by
  unfold shapeFields inj
  rw [ssnd_spair, projList_mkTower_append]

/-- **Membership in the shape set** (positive sort): a shadow tuple of
some constructor, its spine fitting the shadow fields, its index values
the tuple's. -/
theorem mem_shapeSet {u w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm}
    {ksF : Nat → List RecFieldKind} {Fss Ess : List (List AnnotTerm)} {t a : V} :
    a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t ↔
      ∃ j as', j < Fss.length ∧ a = inj j (mkTower (as' ++ [pt])) ∧
        SpineFit ρp (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) as' ∧
        idxValsAt ρp (Ess.getD j []) as' = isOfW u Ids.length t := by
  unfold shapeSet
  rw [mem_sep]
  constructor
  · rintro ⟨hsum, j, as', hj, rfl, hlen, hidx⟩
    obtain ⟨j', a', ha', heq⟩ := sumSet_elim hw hsum
    obtain ⟨rfl, rfl⟩ := inj_inj heq
    rw [sumFibre_of_getElem? (by rw [uChains_getElem?, shadowFss_getElem? nP ksF Fss hj]; rfl)] at ha'
    obtain ⟨hfit, -, -, -⟩ := restricted_member_elim hw ha'
    have hl : (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])).length = as'.length := by
      rw [shadowFs_length, hlen]
    rw [hl, projList_mkTower_append] at hfit
    exact ⟨j, as', hj, rfl, hfit, hidx⟩
  · rintro ⟨j, as', hj, rfl, hfit, hidx⟩
    have hlen : as'.length = (Fss.getD j []).length := by
      rw [hfit.length_eq, shadowFs_length]
    refine ⟨?_, j, as', hj, rfl, hlen, hidx⟩
    refine inj_mem hw ?_
    rw [sumFibre_of_getElem? (by rw [uChains_getElem?, shadowFss_getElem? nP ksF Fss hj]; rfl)]
    refine mkTower_mem hw (fitsS_teleOfFields.mpr (SpineFit.append hfit ?_))
    show (pt : V) ∈ˢ interp V (consList as' ρp) (idxEqAV []) ∧ True
    rw [idxEqAV_interp, truthVal_eq_unitSet (EqAll_nil _)]
    exact ⟨pt_mem_unitSet, trivial⟩

/-- **The shape set is a member**: the shadow chains are graded. -/
theorem shapeSet_mem {u w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm}
    {ksF : Nat → List RecFieldKind} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (hC : ∀ j, j < Fss.length → ChainFacts u w nP (Fss.getD j []).length ρp Ids (ksF j)
      (tlss.getD j []) (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
    (t : V) : shapeSet u w nP ρp Ids ksF Fss Ess t ∈ˢ (univ w : V) := by
  unfold shapeSet
  refine univ_sep_mem (sumSet_univ_of_okB (SumFieldsOkB_uChains ?_))
  intro Fs hFs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
  have hjn : j < Fss.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; rwa [shadowFss_length] at this
  rw [shadowFss_getElem? nP ksF Fss hjn] at hj
  obtain rfl := Option.some.inj hj
  exact shadowFs_okB hw (hC j hjn)

/-! ## Members: application, tuples, λ-towers -/

theorem app_mem_univ {w : Nat} (hw : w ≠ 0) {f a : V} (hf : f ∈ˢ (univ w : V)) :
    app f a ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold app
  split
  · exact hU.pt_mem (empty_mem_univ w)
  · exact hU.sUnion_mem (hU.sep_mem (hU.sUnion_mem (hU.sUnion_mem hf)))

theorem kpair_comp_mem {w : Nat} (hw : w ≠ 0) {a b : V} (h : kpair a b ∈ˢ (univ w : V)) :
    a ∈ˢ (univ w : V) ∧ b ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold kpair at h
  exact ⟨hU.transitive (hU.transitive h (mem_upair_left _ _)) (mem_sing.mpr rfl),
    hU.transitive (hU.transitive h (mem_upair_right _ _)) (mem_upair_right a b)⟩

theorem spair_comp_mem {w : Nat} (hw : w ≠ 0) {a b : V} (h : spair a b ∈ˢ (univ w : V)) :
    a ∈ˢ (univ w : V) ∧ b ∈ˢ (univ w : V) := by
  rw [spair_eq_kpair] at h
  exact kpair_comp_mem hw h

theorem spair_mem_univ {w : Nat} (hw : w ≠ 0) {a b : V} (ha : a ∈ˢ (univ w : V))
    (hb : b ∈ˢ (univ w : V)) : spair a b ∈ˢ (univ w : V) := by
  rw [spair_eq_kpair]
  exact (univ_isTGUniverse hw).kpair_mem ha ha hb

theorem mkTower_comp_mem {w : Nat} (hw : w ≠ 0) :
    ∀ {L : List V}, mkTower L ∈ˢ (univ w : V) → ∀ x, x ∈ L → x ∈ˢ (univ w : V)
  | [], _, _, hx => nomatch hx
  | a :: L, h, x, hx => by
    obtain ⟨ha, hL⟩ := spair_comp_mem hw (show spair a (mkTower L) ∈ˢ (univ w : V) from h)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact mkTower_comp_mem hw hL x hx

theorem mkTower_mem_univ {w : Nat} (hw : w ≠ 0) :
    ∀ {L : List V}, (∀ x, x ∈ L → x ∈ˢ (univ w : V)) → mkTower L ∈ˢ (univ w : V)
  | [], _ => (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)
  | a :: L, h => by
    show spair a (mkTower L) ∈ˢ _
    exact spair_mem_univ hw (h a List.mem_cons_self)
      (mkTower_mem_univ hw fun x hx => h x (List.mem_cons_of_mem a hx))

theorem vnat_mem_univ {w : Nat} (hw : w ≠ 0) (j : Nat) : (vnat j : V) ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact (univ_isTGUniverse hw).transitive (omega_mem_univ_succ w') (vnat_mem_omega j)

theorem inj_mem_univ {w : Nat} (hw : w ≠ 0) {j : Nat} {x : V} (hx : x ∈ˢ (univ w : V)) :
    inj j x ∈ˢ (univ w : V) :=
  spair_mem_univ hw (vnat_mem_univ hw j) hx

theorem inj_comp_mem {w : Nat} (hw : w ≠ 0) {j : Nat} {x : V} (h : inj j x ∈ˢ (univ w : V)) :
    x ∈ˢ (univ w : V) :=
  (spair_comp_mem hw h).2

/-- A λ-tower over graded binder data with member values is a member. -/
theorem lamTower_mem_univ {w : Nat} (hw : w ≠ 0) {g : (Nat → V) → V} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsOkB w ρ (tl.map (·.2.2)) →
      (∀ bs, SpineFit ρ (tl.map (·.2.2)) bs → g (consList bs ρ) ∈ˢ (univ w : V)) →
      lamTower w ρ tl g ∈ˢ (univ w : V)
  | [], ρ, _, hg => by simpa [lamTower] using hg [] trivial
  | d :: tl, ρ, hF, hg => by
    have hU := univ_isTGUniverse (V := V) hw
    show lamR w (interp V ρ d.2.2) (fun a => lamTower w (cons a ρ) tl g) ∈ˢ _
    rw [List.map_cons] at hF
    rw [lamR_pos hw]
    unfold graph
    refine hU.image_mem (hF.2.1 hw) fun a ha => ?_
    refine hU.kpair_mem (hF.2.1 hw) (hU.transitive (hF.2.1 hw) ha) ?_
    refine lamTower_mem_univ hw (hF.2.2 a ha) fun bs hbs => ?_
    have := hg (a :: bs) ⟨ha, hbs⟩
    rwa [consList_cons] at this

/-- λ-towers over frames agreeing off excluded slots, whose domains
mention none, agree when the bodies agree at corresponding leaves. -/
theorem lamTower_congr_exclP {Q : Nat → Prop} {m : Nat} {g : (Nat → V) → V} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      (∀ k dd, tl[k]? = some dd → NoBVar (exclP Q (d + k)) dd.2.2) →
      (∀ bs, SpineFit σ (tl.map (·.2.2)) bs → g (consList bs σ) = g (consList bs σ')) →
      lamTower m σ tl g = lamTower m σ' tl g
  | [], _, _, σ, σ', _, _, hg => by simpa [lamTower] using hg [] trivial
  | dd :: tl, d, hQ, σ, σ', hag, hnb, hg => by
    show lamR m (interp V σ dd.2.2) (fun a => lamTower m (cons a σ) tl g)
      = lamR m (interp V σ' dd.2.2) (fun a => lamTower m (cons a σ') tl g)
    have hnb0 : NoBVar (exclP Q d) dd.2.2 := by simpa using hnb 0 dd rfl
    rw [← interp_congr_noBVar dd.2.2 hnb0 hag]
    refine lamR_congr fun a ha => ?_
    refine lamTower_congr_exclP tl (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
      (agreeOff_exclP_cons hQ hag a) ?_ ?_
    · intro k d' hk
      have := hnb (k + 1) d' (by simpa using hk)
      rwa [show d + (k + 1) = d + 1 + k from by omega] at this
    · intro bs hbs
      have := hg (a :: bs) ⟨ha, hbs⟩
      simpa [consList_cons] using this

omit [SetTheory V] in
theorem frameIdx_cons_consList (a : V) (bs : List V) (ρ : Nat → V) :
    frameIdx (bs.length + 1) (consList bs (cons a ρ)) = a :: bs := by
  have := frameIdx_consList' (a :: bs) ρ
  rwa [List.length_cons, consList_cons] at this

/-- **Eta for a slot's value**: a member of the nested product is the
λ-tower of its spine folds. -/
theorem piTele_eta {w : Nat} (hw : w ≠ 0) {B : List V → V} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V} {f : V},
      f ∈ˢ piTele w (teleOfFields ρ (tl.map (·.2.2))) B acc →
      lamTower w ρ tl (fun σ => (frameIdx tl.length σ).foldl SetTheory.app f) = f
  | [], _, _, _, _ => by simp [lamTower, frameIdx]
  | d :: tl, ρ, acc, f, hf => by
    rw [List.map_cons] at hf
    simp only [teleOfFields, piTele] at hf
    show lamR w (interp V ρ d.2.2) (fun a => lamTower w (cons a ρ) tl
      (fun σ => (frameIdx (tl.length + 1) σ).foldl SetTheory.app f)) = f
    refine Eq.trans ?_ (lamR_eta hf)
    refine lamR_congr fun a ha => ?_
    have hfa := app_mem_piR_pos hw hf ha
    rw [← piTele_eta hw hfa]
    refine lamTower_congr_leaves fun bs hbs => ?_
    have hlen : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
    rw [← hlen, frameIdx_cons_consList, frameIdx_consList', List.foldl_cons]

theorem spineFit_take_prefix {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) := by
  have h' : SpineFit ρ (Fs.take i ++ Fs.drop i) as := by rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_inv h'
  have hl : as₁.length = i := by
    rw [h1.length_eq, List.length_take]; exact Nat.min_eq_left hi
  have : as.take i = as₁ := by
    rw [heq, List.take_append, List.take_of_length_le (Nat.le_of_eq hl), hl, Nat.sub_self,
      List.take_zero, List.append_nil]
  rw [this]
  exact h1

theorem recAt_iff_rsOf {nP i : Nat} {ks : List RecFieldKind} (hi : i < ks.length) :
    recAt nP ks (nP + i) ↔ (rsOf ks).getD i false = true := by
  rw [rsOf_getD_iff hi]
  unfold recAt
  rw [Nat.add_sub_cancel_left]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_add_right _ _, h⟩⟩

/-! ## The positions, the targets, the builder -/

/-- The tags of the recursive positions. -/
noncomputable def recTags (rs : List Bool) (nF : Nat) : V :=
  sep omega fun k => ∃ i, i ∈ recIdx rs nF ∧ k = vnat i

theorem mem_recTags {rs : List Bool} {nF : Nat} {k : V} :
    k ∈ˢ recTags rs nF ↔ ∃ i, i ∈ recIdx rs nF ∧ k = vnat i := by
  unfold recTags
  rw [mem_sep]
  exact ⟨fun h => h.2, fun ⟨i, hi, hk⟩ => ⟨by rw [hk]; exact vnat_mem_omega i, i, hi, hk⟩⟩

theorem recTags_mem {w : Nat} (hw : w ≠ 0) (rs : List Bool) (nF : Nat) :
    recTags rs nF ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact univ_sep_mem (omega_mem_univ_succ w')

/-- The spine set of a telescope at a prefix. -/
noncomputable def spineSet (w : Nat) (ρp : Nat → V) (tl : List (Nat × Nat × AnnotTerm)) (as : List V) :
    V :=
  towerSet w (teleOfFields (consList as ρp) (tl.map (·.2.2)))

/-- The positions of a shape: the recursive fields' spines, tagged. -/
noncomputable def posSet (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Fss : List (List AnnotTerm)) (a : V) : V :=
  sigmaPairs (recTags (rss.getD (shapeTag a) []) (Fss.getD (shapeTag a) []).length) fun k =>
    spineSet w ρp ((tlss.getD (shapeTag a) []).getD (natIdx k) [])
      ((shapeFields (Fss.getD (shapeTag a) []).length a).take (natIdx k))

/-- The target of a position: the call's index tuple. -/
noncomputable def posTgt (u : Nat) (ρp : Nat → V) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (Fss : List (List AnnotTerm)) (a p : V) : V :=
  tupW u (((Eiss.getD (shapeTag a) []).getD (natIdx (sfst p)) []).map
    (interp V (consList (projList ((tlss.getD (shapeTag a) []).getD (natIdx (sfst p)) []).length (ssnd p))
      (consList ((shapeFields (Fss.getD (shapeTag a) []).length a).take (natIdx (sfst p))) ρp))))

/-- The builder: the tuple with the recursive slots holding the curried
function on spines. -/
noncomputable def mkShape (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Fss : List (List AnnotTerm)) (a g : V) : V :=
  inj (shapeTag a) (mkTower (((List.range (Fss.getD (shapeTag a) []).length).map fun i =>
    if (rss.getD (shapeTag a) []).getD i false then
      lamTower w (consList ((shapeFields (Fss.getD (shapeTag a) []).length a).take i) ρp)
        ((tlss.getD (shapeTag a) []).getD i []) fun σ =>
          app g (kpair (vnat i) (mkTower (frameIdx ((tlss.getD (shapeTag a) []).getD i []).length σ)))
    else (shapeFields (Fss.getD (shapeTag a) []).length a).getD i pt) ++ [pt]))

section Block

variable {u w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
  {ksF : Nat → List RecFieldKind} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
  {Fss Ess : List (List AnnotTerm)}
  (hrss : ∀ j, j < Fss.length → rss.getD j [] = rsOf (ksF j))
  (hC : ∀ j, j < Fss.length → ChainFacts u w nP (Fss.getD j []).length ρp Ids (ksF j)
    (tlss.getD j []) (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
include hw hrss hC

omit hw in
/-- The recursive slot at a shadow prefix fits (the chain facts at the
shadow-fitting prefix). -/
theorem slotFit_shadow {j : Nat} (hj : j < Fss.length) {as' : List V}
    (hfit : SpineFit ρp (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) as')
    {i : Nat} (hi : i ∈ recIdx (rss.getD j []) (Fss.getD j []).length) :
    SlotFit u w ρp Ids ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i []) (as'.take i) := by
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  rw [hrss j hj] at hri
  have hr : recAt nP (ksF j) (nP + i) := (recAt_iff_rsOf (by rw [(hC j hj).hks]; exact hik)).mpr hri
  have hsp := spineFit_take_prefix hfit (i := i) (by rw [shadowFs_length]; exact Nat.le_of_lt hik)
  exact ((hC j hj).gr i hik (as'.take i) hsp).2.2 hr

omit hrss hC in
theorem shapeSet_data {t a : V} (ha : a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t) :
    ∃ j as', j < Fss.length ∧ a = inj j (mkTower (as' ++ [pt])) ∧
      as'.length = (Fss.getD j []).length ∧
      SpineFit ρp (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])) as' ∧
      idxValsAt ρp (Ess.getD j []) as' = isOfW u Ids.length t ∧
      shapeTag a = j ∧ shapeFields (Fss.getD j []).length a = as' := by
  obtain ⟨j, as', hj, rfl, hfit, hidx⟩ := (mem_shapeSet hw).mp ha
  have hlen : as'.length = (Fss.getD j []).length := by rw [hfit.length_eq, shadowFs_length]
  refine ⟨j, as', hj, rfl, hlen, hfit, hidx, shapeTag_inj j _, ?_⟩
  rw [← hlen]
  exact shapeFields_inj j as' [pt]

/-- **The positions of a shape are a member.** -/
theorem posSet_mem {t a : V} (ha : a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t) :
    posSet w ρp rss tlss Fss a ∈ˢ (univ w : V) := by
  obtain ⟨j, as', hj, -, -, hfit, -, htag, hfields⟩ := shapeSet_data hw ha
  unfold posSet
  rw [htag, hfields]
  refine (univ_isTGUniverse hw).sigmaPairs_mem (recTags_mem hw _ _) fun k hk => ?_
  obtain ⟨i, hi, rfl⟩ := mem_recTags.mp hk
  rw [natIdx_vnat]
  unfold spineSet
  exact towerSet_univ_of_okB fun _ =>
    FieldsOkB.toBound hw (slotFit_shadow hrss hC hj hfit hi).1

/-- **A position's target is an index tuple.** -/
theorem posTgt_mem {t a p : V} (ha : a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t)
    (hp : p ∈ˢ posSet w ρp rss tlss Fss a) :
    posTgt u ρp tlss Eiss Fss a p ∈ˢ idxSet u ρp Ids := by
  obtain ⟨j, as', hj, -, -, hfit, -, htag, hfields⟩ := shapeSet_data hw ha
  unfold posSet at hp
  rw [htag, hfields] at hp
  obtain ⟨k, hk, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
  obtain ⟨i, hi, rfl⟩ := mem_recTags.mp hk
  rw [natIdx_vnat] at hq
  unfold posTgt
  rw [htag, hfields, sfst_kpair, ssnd_kpair, natIdx_vnat]
  unfold spineSet at hq
  have hbs := (towerSet_elim_teleOfFields hw hq).1
  rw [List.length_map] at hbs
  have hslot := slotFit_shadow hrss hC hj hfit hi
  obtain ⟨-, hv⟩ := hslot.2.2 _ hbs
  rw [consList_append] at hv
  exact tupW_mem hv

/-- **The builder keeps members.** -/
theorem mkShape_mem {t a g : V} (ha : a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t)
    (hg : g ∈ˢ (univ w : V)) : mkShape w ρp rss tlss Fss a g ∈ˢ (univ w : V) := by
  obtain ⟨j, as', hj, rfl, -, hfit, -, htag, hfields⟩ := shapeSet_data hw ha
  have hamem : inj j (mkTower (as' ++ [pt])) ∈ˢ (univ w : V) :=
    (univ_isTGUniverse hw).transitive (shapeSet_mem hw hC t) ha
  have hcomp : ∀ x, x ∈ as' → x ∈ˢ (univ w : V) := fun x hx =>
    mkTower_comp_mem hw (inj_comp_mem hw hamem) x (List.mem_append_left _ hx)
  unfold mkShape
  rw [htag, hfields]
  refine inj_mem_univ hw (mkTower_mem_univ hw fun x hx => ?_)
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hi
    by_cases hri : (rss.getD j []).getD i false = true
    · rw [if_pos hri]
      have hmem : i ∈ recIdx (rss.getD j []) (Fss.getD j []).length := mem_recIdx.mpr ⟨hi, hri⟩
      refine lamTower_mem_univ hw (slotFit_shadow hrss hC hj hfit hmem).1 fun bs _ => ?_
      exact app_mem_univ hw hg
    · rw [if_neg hri]
      by_cases hil : i < as'.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
        exact hcomp _ (List.getElem_mem hil)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
        exact (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)
  · rw [List.mem_singleton] at hx
    subst hx
    exact (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)

/-! ## The element decomposition -/

omit [SetTheory V] hw hrss hC in
theorem agreeOff_symm {P : Nat → Prop} {σ σ' : Nat → V} (h : AgreeOff P σ σ') : AgreeOff P σ' σ :=
  fun i hi => (h i hi).symm

omit hw hrss in
/-- The moved telescope's `NoBVar` facts in the domain-list form. -/
theorem nbT_map {j : Nat} (hj : j < Fss.length) {i : Nat} (hik : i < (Fss.getD j []).length)
    (hr : recAt nP (ksF j) (nP + i)) :
    ∀ k F, (((tlss.getD j []).getD i []).map (·.2.2))[k]? = some F →
      NoBVar (exclP (fun q => recAt nP (ksF j) q ∧ q < nP + i) (nP + i + k)) F := by
  intro k F hk
  rw [List.getElem?_map] at hk
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hk
  exact (hC j hj).nbT i hik hr k d hd

omit hw in
/-- **A spine fitting the X-chain has its shadow fitting the shadow
fields**: the ordinary domains do not mention the recursive slots, the
recursive slots read `Sort 0` at the shadow value. -/
theorem shadowOf_fits {j : Nat} (hj : j < Fss.length) {X t : V} :
    ∀ (Fs' : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      Fs' = (Fss.getD j []).drop i →
      SpineFit (consList as (cons t (cons X ρp)))
        (chainXIGo u Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) Fs' i) bs →
      SpineFit (consList (shadowOf nP (ksF j) as) ρp)
        ((shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])).drop i)
        (shadowOfGo nP (ksF j) i bs)
  | [], i, as, bs, _, hF, h => by
    cases bs with
    | nil =>
      have hlen : (Fss.getD j []).length ≤ i := by
        have := congrArg List.length hF
        rw [List.length_nil, List.length_drop] at this
        omega
      rw [List.drop_eq_nil_of_le (by rw [shadowFs_length]; exact hlen)]
      trivial
    | cons b bs => exact h.elim
  | F :: Fs', i, as, bs, hi, hF, h => by
    subst hi
    cases bs with
    | nil => exact h.elim
    | cons b bs =>
    rw [chainXIGo_cons] at h
    obtain ⟨hb, hrest⟩ := h
    have hlt : as.length < (Fss.getD j []).length := by
      have := congrArg List.length hF
      rw [List.length_cons, List.length_drop] at this
      omega
    have hdropF := List.drop_eq_getElem_cons hlt
    rw [← hF] at hdropF
    obtain ⟨hFget, hFs'⟩ := List.cons.inj hdropF
    have hFgetD : F = (Fss.getD j []).getD as.length default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact hFget
    have hltS : as.length < (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j [])).length := by
      rw [shadowFs_length]; exact hlt
    rw [List.drop_eq_getElem_cons hltS]
    have hget : (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j []))[as.length]
        = if recAt nP (ksF j) (nP + as.length) then AnnotTerm.sort 0
          else (Fss.getD j []).getD as.length default := by
      have := shadowFs_getElem? (nP := nP) (ks := ksF j) (Fs := Fss.getD j []) hlt
      rw [List.getElem?_eq_getElem hltS] at this
      exact Option.some.inj this
    rw [hget]
    show (if recAt nP (ksF j) (nP + as.length) then shadowVal else b) ∈ˢ _ ∧ SpineFit _ _ _
    refine ⟨?_, ?_⟩
    · by_cases hr : recAt nP (ksF j) (nP + as.length)
      · rw [if_pos hr, if_pos hr, interp_sort]
        exact shadowVal_mem
      · rw [if_neg hr, if_neg hr]
        have hri : (rss.getD j []).getD as.length false = false := by
          rw [hrss j hj]
          exact Bool.eq_false_iff.mpr fun h =>
            hr ((recAt_iff_rsOf (nP := nP) (by rw [(hC j hj).hks]; exact hlt)).mpr h)
        rw [xEntry_ord F as t hri] at hb
        have hnb := (hC j hj).nb as.length hlt
        rw [← hFgetD] at hnb
        rw [← hFgetD, ← interp_congr_noBVar F hnb (agreeOff_shadow (shadowRel_shadowOf nP (ksF j) as) ρp)]
        exact hb
    · have ih := shadowOf_fits hj (X := X) (t := t) Fs' (as.length + 1) (as ++ [b]) bs
        (length_snoc' b as) hFs' (by rw [← consList_snoc']; exact hrest)
      have hsh : shadowOf nP (ksF j) (as ++ [b])
          = shadowOf nP (ksF j) as ++ [if recAt nP (ksF j) (nP + as.length) then shadowVal else b] := by
        unfold shadowOf
        rw [shadowOfGo_append, Nat.zero_add]
        rfl
      rw [hsh, ← consList_snoc'] at ih
      exact ih

omit hw hrss in
/-- The index values are read at the shadow spine. -/
theorem idxValsAt_shadow {j : Nat} (hj : j < Fss.length) {fs : List V}
    (hlen : fs.length = (Fss.getD j []).length) :
    idxValsAt ρp (Ess.getD j []) (shadowOf nP (ksF j) fs) = idxValsAt ρp (Ess.getD j []) fs := by
  unfold idxValsAt
  apply List.map_congr_left
  intro E hE
  have hnb := (hC j hj).nbEs E hE
  rw [← hlen] at hnb
  exact (interp_congr_noBVar E hnb (agreeOff_shadow (shadowRel_shadowOf nP (ksF j) fs) ρp)).symm

include hI in
set_option maxHeartbeats 3200000 in
/-- **Every element of the functor's fibre is a container element**: its
shadow tuple is a shape, its recursive slots' spine folds a function on
the positions into the family at the targets, and it is the builder's
value at both. -/
theorem fixStep_elim_container {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V}
    (ht : t ∈ˢ idxSet u ρp Ids)
    (hfitX : ∀ j, j < Fss.length →
      SlotsFitX u w ρp Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) X t 0 [] (Fss.getD j []))
    {x : V} (hx : x ∈ˢ fixStepI u w ρp Ids Ids.length rss tlss Eiss Fss Ess X t) :
    ∃ a, a ∈ˢ shapeSet u w nP ρp Ids ksF Fss Ess t ∧
      ∃ g, g ∈ˢ piSet (posSet w ρp rss tlss Fss a) (fun p => app X (posTgt u ρp tlss Eiss Fss a p)) ∧
        x = mkShape w ρp rss tlss Fss a g := by
  obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim ht
  obtain ⟨j, fs, rfl, hj, hlen, hfs, hall⟩ := fixStepI_elim hw hx
  have hEs : (Ess.getD j []).length = Ids.length := (hC j hj).hEs
  have hfam : ∀ t', app X t' ∈ˢ (univ w : V) := fun t' => famApp_mem_univ hX t'
  -- the shape: the shadow tuple
  have hsh : SpineFit ρp (shadowFs nP (ksF j) (Fss.getD j []).length (Fss.getD j []))
      (shadowOf nP (ksF j) fs) := by
    have := shadowOf_fits hrss hC hj (X := X) (t := tupW u is) (Fss.getD j []) 0 [] fs rfl
      List.drop_zero.symm hfs
    rw [List.drop_zero] at this
    exact this
  have hidx : idxValsAt ρp (Ess.getD j []) (shadowOf nP (ksF j) fs) = isOfW u Ids.length (tupW u is) := by
    rw [isOfW_tupW hI hsp, idxValsAt_shadow hC hj hlen]
    rw [← hlen] at hall
    exact idxValsAt_of_eqsXI hI hsp hEs hall
  refine ⟨inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt])),
    (mem_shapeSet hw).mpr ⟨j, _, hj, rfl, hsh, hidx⟩, ?_⟩
  have htag := shapeTag_inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt]))
  have hfields : shapeFields (Fss.getD j []).length (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt])))
      = shadowOf nP (ksF j) fs := by
    rw [← hlen, ← shadowOf_length nP (ksF j) fs]
    exact shapeFields_inj j _ [pt]
  -- the recursive slots at the real prefix
  have hslot : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      SlotFit u w ρp Ids ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i []) (fs.take i) ∧
      fs.getD i pt ∈ˢ slotSet w u (consList (fs.take i) ρp) ((tlss.getD j []).getD i [])
        ((Eiss.getD j []).getD i []) X := by
    intro i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have := fitsXI_slot_mem hI (Fss.getD j []) 0 [] fs rfl (hfitX j hj) hfs i (by rw [hlen]; exact hik)
      (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at this
    exact this
  -- the shadow prefix against the real prefix
  have hrecAt : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, recAt nP (ksF j) (nP + i) := by
    intro i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    rw [hrss j hj] at hri
    exact (recAt_iff_rsOf (by rw [(hC j hj).hks]; exact hik)).mpr hri
  have hQ : ∀ i, ∀ q, (recAt nP (ksF j) q ∧ q < nP + i) → q < nP + i := fun _ _ h => h.2
  have hlenT : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, (fs.take i).length = i := by
    intro i hi
    rw [List.length_take, hlen]; exact Nat.min_eq_left (Nat.le_of_lt (mem_recIdx.mp hi).1)
  have hag : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      AgreeOff (exclP (fun q => recAt nP (ksF j) q ∧ q < nP + i) (nP + i))
        (consList (fs.take i) ρp) (consList ((shadowOf nP (ksF j) fs).take i) ρp) := by
    intro i hi
    have := agreeOff_shadow (shadowRel_shadowOf nP (ksF j) (fs.take i)) ρp
    rw [hlenT i hi, ← shadowOf_take] at this
    exact this
  have hspine : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∀ bs : List V,
      SpineFit (consList ((shadowOf nP (ksF j) fs).take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) bs ↔
      SpineFit (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) bs := fun i hi bs =>
    (spineFit_congr_exclP _ bs (hQ i) (hag i hi)
      (nbT_map hC hj (mem_recIdx.mp hi).1 (hrecAt i hi))).symm
  have hEmap : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∀ bs : List V,
      bs.length = ((tlss.getD j []).getD i []).length →
      ((Eiss.getD j []).getD i []).map (interp V (consList bs (consList ((shadowOf nP (ksF j) fs).take i) ρp)))
        = ((Eiss.getD j []).getD i []).map (interp V (consList bs (consList (fs.take i) ρp))) := by
    intro i hi bs hbs
    apply List.map_congr_left
    intro E hE
    have hnb := (hC j hj).nbE i (mem_recIdx.mp hi).1 (hrecAt i hi) E hE
    rw [← hbs] at hnb
    exact (interp_congr_noBVar E hnb (agreeOff_exclP_consList bs (hQ i) (hag i hi))).symm
  -- the function on the positions: the recursive slots' spine folds
  let G : V → V := fun p =>
    (projList ((tlss.getD j []).getD (natIdx (sfst p)) []).length (ssnd p)).foldl SetTheory.app
      (fs.getD (natIdx (sfst p)) pt)
  have hpos : ∀ p, p ∈ˢ posSet w ρp rss tlss Fss (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt]))) ↔
      ∃ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∃ q,
        q ∈ˢ spineSet w ρp ((tlss.getD j []).getD i []) ((shadowOf nP (ksF j) fs).take i) ∧
        p = kpair (vnat i) q := by
    intro p
    unfold posSet
    rw [htag, hfields, mem_sigmaPairs]
    constructor
    · rintro ⟨k, hk, q, hq, rfl⟩
      obtain ⟨i, hi, rfl⟩ := mem_recTags.mp hk
      rw [natIdx_vnat] at hq
      exact ⟨i, hi, q, hq, rfl⟩
    · rintro ⟨i, hi, q, hq, rfl⟩
      refine ⟨vnat i, mem_recTags.mpr ⟨i, hi, rfl⟩, q, ?_, rfl⟩
      rw [natIdx_vnat]; exact hq
  refine ⟨graph G (posSet w ρp rss tlss Fss (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt])))), ?_, ?_⟩
  · -- the values land in the family at the targets
    refine graph_mem_piSet fun p hp => ?_
    obtain ⟨i, hi, q, hq, rfl⟩ := (hpos p).mp hp
    unfold spineSet at hq
    have hbs := (towerSet_elim_teleOfFields hw hq).1
    rw [List.length_map] at hbs
    have hbsR := (hspine i hi _).mp hbs
    have hlenbs : (projList ((tlss.getD j []).getD i []).length q).length = ((tlss.getD j []).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    have hmem := slotSet_fold_mem hfam (hslot i hi).2 hbsR
    show G (kpair (vnat i) q) ∈ˢ app X (posTgt u ρp tlss Eiss Fss _ (kpair (vnat i) q))
    unfold posTgt
    simp only [G, sfst_kpair, ssnd_kpair, natIdx_vnat, htag, hfields]
    rw [hEmap i hi _ hlenbs]
    exact hmem
  · -- the element is the builder's value
    unfold mkShape
    rw [htag, hfields]
    have hL : fs = (List.range (Fss.getD j []).length).map fun i =>
        if (rss.getD j []).getD i false then
          lamTower w (consList ((shadowOf nP (ksF j) fs).take i) ρp) ((tlss.getD j []).getD i []) fun σ =>
            app (graph G (posSet w ρp rss tlss Fss (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt])))))
              (kpair (vnat i) (mkTower (frameIdx ((tlss.getD j []).getD i []).length σ)))
        else (shadowOf nP (ksF j) fs).getD i pt := by
      apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      have hfsi : fs[i] = fs.getD i pt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
      rw [hfsi]
      by_cases hri : (rss.getD j []).getD i false = true
      · rw [if_pos hri]
        have hi : i ∈ recIdx (rss.getD j []) (Fss.getD j []).length := mem_recIdx.mpr ⟨by omega, hri⟩
        -- the tower at the shadow prefix is the tower at the real prefix
        have h1 : lamTower w (consList ((shadowOf nP (ksF j) fs).take i) ρp) ((tlss.getD j []).getD i [])
              (fun σ => app (graph G (posSet w ρp rss tlss Fss (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt]))))) (kpair (vnat i) (mkTower (frameIdx ((tlss.getD j []).getD i []).length σ))))
            = lamTower w (consList (fs.take i) ρp) ((tlss.getD j []).getD i [])
              (fun σ => app (graph G (posSet w ρp rss tlss Fss (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt]))))) (kpair (vnat i) (mkTower (frameIdx ((tlss.getD j []).getD i []).length σ)))) := by
          refine lamTower_congr_exclP _ (hQ i) (agreeOff_symm (hag i hi)) ?_ fun bs hbs => ?_
          · intro k d hk
            exact (hC j hj).nbT i (by omega) (hrecAt i hi) k d hk
          · have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by
              rw [hbs.length_eq, List.length_map]
            rw [← hlenbs, frameIdx_consList', frameIdx_consList']
        -- the tower at the real prefix is the slot's eta expansion
        have h2 : lamTower w (consList (fs.take i) ρp) ((tlss.getD j []).getD i [])
              (fun σ => app (graph G (posSet w ρp rss tlss Fss (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt]))))) (kpair (vnat i) (mkTower (frameIdx ((tlss.getD j []).getD i []).length σ))))
            = lamTower w (consList (fs.take i) ρp) ((tlss.getD j []).getD i [])
              (fun σ => (frameIdx ((tlss.getD j []).getD i []).length σ).foldl SetTheory.app (fs.getD i pt)) := by
          refine lamTower_congr_leaves fun bs hbs => ?_
          have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by
            rw [hbs.length_eq, List.length_map]
          rw [← hlenbs, frameIdx_consList']
          have hpmem : kpair (vnat i) (mkTower bs) ∈ˢ posSet w ρp rss tlss Fss
              (inj j (mkTower (shadowOf nP (ksF j) fs ++ [pt]))) := by
            refine (hpos _).mpr ⟨i, hi, mkTower bs, ?_, rfl⟩
            unfold spineSet
            exact mkTower_mem hw (fitsS_teleOfFields.mpr ((hspine i hi bs).mpr hbs))
          rw [app_graph hpmem]
          simp only [G, sfst_kpair, ssnd_kpair, natIdx_vnat]
          rw [projList_mkTower _ bs hlenbs]
        rw [h1, h2]
        have := (hslot i hi).2
        unfold slotSet at this
        exact (piTele_eta hw this).symm
      · rw [if_neg hri, shadowOf_getD h1]
        rw [if_neg]
        intro hr
        exact hri (by rw [hrss j hj]; exact (recAt_iff_rsOf (by rw [(hC j hj).hks]; omega)).mp hr)
    exact congrArg (fun L => inj j (mkTower (L ++ [pt]))) hL

/-! ## The witness -/

include hI in
/-- **A closed member family exists for every recursive block** (positive
sort): the family functor is a container — shapes the shadow tuples,
positions the recursive fields' spines, targets the calls' tuples, the
builder the curried slots — so `container_closed_exists` applies. -/
theorem fixClosed_of :
    ∃ L, IsClosedFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) L := by
  have hfitX : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
      ∀ j, j < Fss.length →
        SlotsFitX u w ρp Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) X t 0 [] (Fss.getD j []) := by
    intro X hX t ht j hj
    rw [hrss j hj]
    exact (fixChain_of hI hX ht (hC j hj)).2
  obtain ⟨L, hL, hclosed⟩ := container_closed_exists hw (I := idxSet u ρp Ids)
    (famFI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) (shapeSet u w nP ρp Ids ksF Fss Ess)
    (posSet w ρp rss tlss Fss) (posTgt u ρp tlss Eiss Fss) (mkShape w ρp rss tlss Fss)
    (fun t _ => shapeSet_mem hw hC t) (fun _ a _ ha => posSet_mem hw hrss hC ha)
    (fun _ a p _ ha hp => posTgt_mem hw hrss hC ha hp) (fun _ a g _ ha hg => mkShape_mem hw hrss hC ha hg)
    (fun X hX t ht x hx => by
      rw [← lfpFamSpace_eq] at hX
      rw [famFI_app ht] at hx
      exact fixStep_elim_container hw hI hrss hC hX ht (hfitX X hX t ht) hx)
  refine ⟨L, hL, ?_⟩
  rw [fixFunVI_app (by rw [lfpFamSpace_eq]; exact hL)]
  exact hclosed

end Block

end ConLeche.Model
