module

public import ConLeche.Model.Inductives.FixRecPre
public import ConLeche.Model.Inductives.FixIntro
public section

/-!
# The recursive recursor's rule law, at the readings (task #188)

The sum route's `sumRecLawCore` (`SumRecLawP.lean`) for the recursive
route: at a frame where the recursor's arguments fit its binder data
and the constructor's arguments fit the constructor's, the recursor at
the constructor value is the rule's right-hand side — the minor at the
fields and at the inductive hypotheses — at the block's arguments and
the fields.  The inductive hypotheses in the rule (`ihAppAV`) read to
the recursor at the block, the field's index values and the field,
exactly the recursor's iota (`nativeRecAVI_iota`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames -/

omit [SetTheory V] in
/-- A block of length `nP + 1 + n` splits into parameters, a motive and
minors. -/
theorem block_split {as₀ : List V} {nP n : Nat} (hlen : as₀.length = nP + 1 + n) :
    ∃ (as₁ : List V) (M : V) (ms : List V),
      as₀ = (as₁ ++ [M]) ++ ms ∧ as₁.length = nP ∧ ms.length = n := by
  have hsplit := (List.take_append_drop nP as₀).symm
  have hlenD : (as₀.drop nP).length = 1 + n := by rw [List.length_drop]; omega
  cases hd : as₀.drop nP with
  | nil => rw [hd, List.length_nil] at hlenD; omega
  | cons M ms =>
    refine ⟨as₀.take nP, M, ms, ?_, by rw [List.length_take]; omega, ?_⟩
    · rw [List.append_assoc, List.singleton_append, ← hd, ← hsplit]
    · rw [hd] at hlenD; simp at hlenD; omega

/-- The recursor's leading spine under `bs` telescope binders reads to
the block (task #202). -/
theorem map_recPrefixBvarsM_interp {nP n nF : Nat} {as₁ ms as₂ : List V} {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenF : as₂.length = nF) (bs : List V) :
    (recPrefixBvarsM nP n nF bs.length).map
        (interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))))
      = (as₁ ++ [M]) ++ ms := by
  unfold recPrefixBvarsM
  rw [List.map_append, List.map_append]
  congr 1
  congr 1
  · rw [show nP + nF + n + 1 + bs.length = nP + (nF + n + 1 + bs.length) from by omega,
      map_paramBvarsAt_interp (ρp := consList as₁ ρ) (fun k => by
        rw [show k + (nF + n + 1 + bs.length) = (k + (nF + n + 1)) + bs.length from by omega,
          consList_apply_add,
          show k + (nF + n + 1) = (k + (n + 1)) + as₂.length from by omega, consList_apply_add,
          show k + (n + 1) = (k + 1) + ms.length from by omega, consList_apply_add]
        rfl), ← hlenP, range_reverse_map_consList]
  · simp only [List.map_cons, List.map_nil, interp_bvar]
    rw [consList_apply_add, show nF + n = n + as₂.length from by omega, consList_apply_add,
      show n = 0 + ms.length from by omega, consList_apply_add]
    rfl
  · apply List.ext_getElem
    · simp [hlenM]
    · intro l h1 h2
      have hl : l < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp_bvar]
      rw [consList_apply_add, show nF + n - 1 - l = (n - 1 - l) + as₂.length from by omega,
        consList_apply_add, consList_apply_lt' ms _ (by omega),
        show ms.length - 1 - (n - 1 - l) = l from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem recPrefixBvarsM_wellDenoted {nP n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ recPrefixBvarsM nP n nF m) : WellDenoted V σ a := by
  unfold recPrefixBvarsM at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
    · rw [List.mem_singleton] at ha; subst ha; trivial
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial

theorem recPrefixBvarsM_validV {nP n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ recPrefixBvarsM nP n nF m) : AnnotValid V σ a := by
  unfold recPrefixBvarsM at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
    · rw [List.mem_singleton] at ha; subst ha; trivial
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial

/-! ## The rule's ih applications at the re-bit telescopes (task #202 A2) -/

omit [SetTheory V] in
theorem ihTeleAtGo_rebit (nF o i l b : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      ihTeleAtGo nF o i l k (rebit b tl) = rebit b (ihTeleAtGo nF o i l k tl)
  | _, [] => rfl
  | k, d :: tl => by
    simp only [rebit_cons, ihTeleAtGo, ihTeleAtGo_rebit nF o i l b (k + 1) tl]

omit [SetTheory V] in
/-- The rule's ih application at a re-bit telescope is the semantic
spelling `ihAppAVb` at the elimination bit with no extras. -/
theorem ihAppAV_rebit (b : Nat) (R : AnnotTerm) (nP n nF i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) :
    ihAppAV R nP n nF i (rebit b tl) Eis = ihAppAVb b (fun _ => R) nP n nF 0 i tl Eis := by
  unfold ihAppAV ihAppAVb ihTeleAtR mkLamsC
  rw [ihTeleAtGo_rebit, rebit_map_lam, rebit_length]
  rfl

/-- **The rule's core reads to the minor's fold** at the fields and the
inductive-hypothesis values — the λ-towers over the recursive fields'
telescopes of the leaf at the block, the calls' index values and the
field along the telescope (`sqIhValsK`; a finitary field: the leaf at
the block, the index values and the field). -/
theorem interp_fixRuleCoreAV {ℓ b nP n nF j : Nat} (hbz : ℓ = 0 ↔ b = 0) {as₁ ms as₂ : List V}
    {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenF : as₂.length = nF) (hjn : j < n)
    {R : AnnotTerm} (hRcl : Term.bvarsBelow 0 R.erase) {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    interp V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        (fixRuleCoreAV b R nP nF n j (recIdx rs nF) tls Eis)
      = (as₂ ++ sqIhValsK ℓ (consList as₁ ρ) as₁ ms M (interp V ρ R) rs tls Eis nF as₂).foldl
          SetTheory.app (ms.getD j pt) := by
  unfold fixRuleCoreAV
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
    (g := SetTheory.app), List.map_append, List.map_map, interp_bvar,
    show fieldBvars nF = (List.range nF).map (fun k => AnnotTerm.bvar (nF - 1 - k)) from rfl,
    map_fieldBvars_interp hlenF,
    show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega, consList_apply_add,
    consList_apply_lt' ms _ (by omega), show ms.length - 1 - (n - 1 - j) = j from by omega]
  congr 2
  unfold sqIhValsK
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  simp only [Function.comp]
  rw [ihAppAV_rebit]
  have h := interp_ihAppAVb (b := b) (M := M) (ρ := ρ) (ex := []) (Rm := fun _ => R)
    (rV := interp V ρ R) hlenP hlenM rfl hlenF hik (fun bs => interp_closed (V := V) hRcl _ ρ)
    (tls.getD i []) (Eis.getD i [])
  simp only [consList_nil, List.length_nil] at h
  rw [h, lamTower_bit_agree hbz.symm]

/-- An application spine over a function whose reading is the point is
graded whenever the head and the arguments are: the `.app` clause is
witnessed at bit `0` by the singleton of the argument's reading. -/
theorem mkAppN_wellDenotedV_of_pt :
    ∀ {f : AnnotTerm} {args : List AnnotTerm} {ρ : Nat → V},
      WellDenotedV V ρ f → interp V ρ f = (pt : V) →
      (∀ a ∈ args, WellDenotedV V ρ a) →
      WellDenotedV V ρ (AnnotTerm.mkAppN f args)
  | _, [], _, hf, _, _ => hf
  | f, a :: args, ρ, hf, hpt, hargs => by
    rw [AnnotTerm.mkAppN_cons]
    have ha := hargs a List.mem_cons_self
    refine mkAppN_wellDenotedV_of_pt (f := .app f a) ?_ ?_
      (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
    · refine ⟨⟨hf.1, ha.1, 0, image (fun _ => interp V ρ a) unitSet, fun _ => unitSet, ?_, ?_, ?_⟩,
        hf.2, ha.2⟩
      · rw [hpt]; exact pt_mem_piR_zero_of fun _ _ => pt_mem_unitSet
      · exact mem_image.mpr ⟨pt, pt_mem_unitSet, rfl⟩
      · intro _ _ _; rw [← univ_zero]; exact unitSet_mem_univ 0
    · rw [interp_app, hpt, app_pt]

/-! ## The law -/

set_option maxHeartbeats 12800000 in
/-- **The recursive recursor rule's law at the readings.**  The
constructor's parameter arguments and the recursor's are never
compared: neither spine is identified with the other, and the law holds
at any pair of fitting parameter spines.  In the graph regime the
constructor's value does not mention its own parameters
(`sumMkAV_fold`), and the recursor's telescope fit already places that
value in the family's fibre at the RECURSOR's parameters, which inverts
(`sumSet_elim`, `towerSet_elim_teleOfFields`) into a fit of the fields
there — all the rule's λ-tower fold asks for.  In the squash regime the
fibre is inhabited by some fitting spine, and the subsingleton
criterion at the recursor's frame and at the constructor's identifies
both that spine and the constructor's fields with the source spine. -/
theorem fixRecLawCore {ℓ b w u s nP nF nIdx n j : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {rds ds : List (Nat × Nat × AnnotTerm)}
    {Fss₀ Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Es : List AnnotTerm}
    (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hlenDs : ds.length = nP + nF) (hjn : j < n)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2))) (hEsj : Ess[j]? = some Es)
    (hEs : Es.length = nIdx)
    {R : AnnotTerm} (hR : R = nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
    (hRcl : Term.bvarsBelow 0 R.erase)
    (hokFss : ∀ ρp : Nat → V, Sat V (((rds.take nP).map (·.2.2)).reverse) ρp →
      SumFieldsOkB w ρp Fss)
    -- the constructor's parameter frame and the recursor's are the
    -- same `Sat` (the install pins the constructor's parameter domains
    -- against the former's by defeq)
    (hsatIff : ∀ ρp : Nat → V,
      Sat V (((rds.take nP).map (·.2.2)).reverse) ρp ↔
        Sat V (((ds.take nP).map (·.2.2)).reverse) ρp)
    -- the subsingleton criterion at ANY frame satisfying the parameter
    -- domains (`CtorDataI.srcProp` is parameter-generic by statement)
    (hsrc : w = 0 → ℓ ≠ 0 → ∀ ρp : Nat → V,
      Sat V (((rds.take nP).map (·.2.2)).reverse) ρp →
      ∀ i, i < (Fss.getD 0 []).length → srcOfEs (Ess.getD 0 []) (Fss.getD 0 []).length i = none →
      ∀ fs : List V, SpineFit ρp ((Fss.getD 0 []).take i) fs →
        interp V (consList fs ρp) ((Fss.getD 0 []).getD i default) ∈ˢ (univZero : V))
    {lds : List (Nat × AnnotTerm)}
    (hldsDom : lds.map (·.2) = (rds.take (nP + 1 + n)).map (·.2.2) ++
      (liftDoms (n + 1) 0 (ds.drop nP)).map (·.2.2))
    -- every rule binder carries the elimination bit
    (hldsBits : ∀ d ∈ lds, d.1 = b)
    {Ra : AnnotTerm}
    (hRa : Ra = mkLamsAV lds (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j [])
      (Eiss.getD j [])))
    (hokRa : ∀ ρ : Nat → V, WellDenotedV V ρ Ra)
    {ρ : Nat → V} {xs ys : List AnnotTerm} (hxl : xs.length = nP + 1 + n + nIdx) (hyl : ys.length = nP + nF)
    (hspR : SpineFit ρ (rds.map (·.2.2))
      ((xs ++ [AnnotTerm.mkAppN (sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]).map
        (interp V ρ)))
    (hspC : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ)))
    (hpin : ∀ i, i < nIdx →
      interp V (consList (ys.map (interp V ρ)) ρ) (Es.getD i default)
        = interp V ρ (xs.getD (nP + 1 + n + i) default)) :
    interp V ρ (AnnotTerm.mkAppN R
        (xs ++ [AnnotTerm.mkAppN (sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]))
      = interp V ρ (AnnotTerm.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP)) ∧
    ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
      WellDenotedV V ρ (AnnotTerm.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hFsjD : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  have hEsjD : Ess.getD j [] = Es := by
    rw [List.getD_eq_getElem?_getD, hEsj]; rfl
  have hjF : j < Fss.length := by rw [hFss]; exact hjn
  -- the constructor's fit, split at the parameters
  have hdsSplit : ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨as₁, as₂, hys, hsp₁, hsp₂⟩ := spineFit_append_inv hspC
  have hlen₁ : as₁.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlen₂ : as₂.length = nF := by rw [hsp₂.length_eq, hlenFs]
  -- the recursor's fit: the block, the indices, the major
  have hspR' := hspR
  rw [List.map_append, List.map_cons, List.map_nil] at hspR'
  generalize hvs : xs.map (interp V ρ) = vs at hspR'
  generalize htv : interp V ρ
    (AnnotTerm.mkAppN (sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys) = t at hspR'
  have hlenvs : vs.length = nP + 1 + n + nIdx := by rw [← hvs, List.length_map, hxl]
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ := kframe_split h hspR'
  rw [hFss] at hl₀
  rw [hIds] at hli
  obtain ⟨bs₁, M, ms, rfl, hlenb₁, hlenm⟩ := block_split hl₀
  -- the K-frame
  obtain ⟨hK, htK⟩ := h.hK ρ _ t hspR'
  have hKfr : consList (((bs₁ ++ [M]) ++ ms) ++ is) ρ = consList is (consList ms (cons M (consList bs₁ ρ))) :=
    consList_kframe bs₁ M ms is ρ
  have hlenIs' : is.length = Ids.length := by rw [hIds]; exact hli
  have hlenMs' : ms.length = Fss.length := by rw [hFss]; exact hlenm
  have hfrP : frP Fss.length Ids.length (consList is (consList ms (cons M (consList bs₁ ρ))))
      = consList bs₁ ρ := kframe_frP hlenIs' hlenMs'
  have hfrIdx : frameIdx Ids.length (consList is (consList ms (cons M (consList bs₁ ρ)))) = is :=
    kframe_frameIdx hlenIs'
  have hfrMs : frMs Fss.length Ids.length (consList is (consList ms (cons M (consList bs₁ ρ)))) j
      = ms.getD j pt := kframe_frMs hlenIs' hlenMs' hjF
  have hfrK : frKSpine nP Fss.length Ids.length (consList is (consList ms (cons M (consList bs₁ ρ))))
      = (bs₁ ++ [M]) ++ ms := by
    rw [← hKfr]
    exact frKSpine_of nP Fss.length Ids.length (by simp [hlenb₁, hlenMs']; omega) hlenIs' ρ
  have hxsv : xs.map (interp V ρ) = ((bs₁ ++ [M]) ++ ms) ++ is := hvs
  have hsh : shiftE (Ids.length + Fss.length + 1) 0 (consList is (consList ms (cons M (consList bs₁ ρ))))
      = consList bs₁ ρ := hfrP
  -- the constructor's parameters `as₁` are NOT identified with the
  -- recursor's `bs₁`
  -- the index values at the CONSTRUCTOR's parameters (from the pin)
  have hidxEq : idxValsAt (consList as₁ ρ) Es as₂ = is := by
    apply List.ext_getElem
    · simp [idxValsAt, hEs, hli]
    · intro i h1 h2
      have hi : i < nIdx := by simpa [idxValsAt, hEs] using h1
      simp only [idxValsAt, List.getElem_map]
      have h := hpin i hi
      rw [hys, consList_append, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some] at h
      rw [h]
      have hx : (xs.map (interp V ρ))[nP + 1 + n + i]? = is[i]? := by
        rw [hxsv]
        simp only [List.append_assoc]
        rw [List.getElem?_append_right (by simp [hlenb₁]; omega),
          List.getElem?_append_right (by simp [hlenb₁]; omega),
          List.getElem?_append_right (by simp [hlenb₁, hlenm]; omega)]
        congr 1
        simp [hlenb₁, hlenm]
        omega
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some,
        List.getElem?_eq_getElem (by omega)] at hx
      exact Option.some.inj hx
  -- the CONSTRUCTOR's parameter frame satisfies the parameters (via the iff)
  have hsatC : Sat V (((rds.take nP).map (·.2.2)).reverse) (consList as₁ ρ) := by
    refine (hsatIff _).mpr ?_
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  -- the constructor leaf's value, at its own parameters
  have hleafC' : sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)
      = sumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) (uChains Fss) := by
    rw [List.take_append_drop]
  have hokU : SumFieldsOkB w (consList as₁ ρ) (uChains Fss) := SumFieldsOkB_uChains (hokFss _ hsatC)
  have hjU : (uChains Fss)[j]? = some ((ds.drop nP).map (·.2.2) ++ [idxEqAV []]) := by
    rw [uChains_getElem?, hFsj]; rfl
  have hmkv : t = if w = 0 then (pt : V) else inj j (mkTower (as₂ ++ [pt])) := by
    rw [← htv, interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hys,
      hleafC']
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [hw0, sumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
    · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
      rw [sumMkAV_fold hw hsp₁ hsp₂ hokU hjU, if_neg hw]
  -- the major in the fibre, in sum form (recursor side)
  have ht' : t ∈ˢ sumSet w (sumFibre w (consList (((bs₁ ++ [M]) ++ ms) ++ is) ρ)
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) := by
    rw [← hK.hyp.hfam]
    exact htK
  have hRj : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[j]?
      = some (rChain (Ids.length + Fss.length + 1) Ids.length ((ds.drop nP).map (·.2.2)) Es) := by
    rw [rChains_getElem?, hFsj, hEsj]
  -- graph regime: the fibre membership inverts into a fit of the
  -- fields at the RECURSOR's parameters `bs₁`
  have hfitB : w ≠ 0 → SpineFit (consList bs₁ ρ) ((ds.drop nP).map (·.2.2)) as₂ := by
    intro hw
    have hmaj : t = inj j (mkTower (as₂ ++ [pt])) := by rw [hmkv, if_neg hw]
    obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht'
    rw [hmaj] at hta
    obtain ⟨rfl, rfl⟩ := inj_inj hta
    rw [sumFibre_of_getElem? hRj] at ha
    obtain ⟨hfitR, heta⟩ := towerSet_elim_teleOfFields hw ha
    have hlenR : (rChain (Ids.length + Fss.length + 1) Ids.length ((ds.drop nP).map (·.2.2)) Es).length
        = nF + 1 := by
      rw [rChain, List.length_append, liftFields_length, hlenFs, List.length_singleton]
    have hpl : projList (rChain (Ids.length + Fss.length + 1) Ids.length ((ds.drop nP).map (·.2.2)) Es).length
        (mkTower (as₂ ++ [pt])) = as₂ ++ [pt] := by
      refine (mkTower_inj ?_ heta.symm)
      rw [projList_length, hlenR, List.length_append, hlen₂, List.length_singleton]
    rw [hpl] at hfitR
    unfold rChain at hfitR
    have hpre := spineFit_prefix (as := as₂) (bs := [pt]) hfitR
    rw [List.take_left' (by rw [liftFields_length, hlenFs, hlen₂])] at hpre
    rw [spineFit_liftFields, hKfr, hsh] at hpre
    exact hpre
  -- squash regime (large eliminator): the fibre is
  -- inhabited by SOME fitting spine at `bs₁`; the subsingleton criterion
  -- at `bs₁` (recursor side, `hK.hsq`) and at `as₁` (constructor side,
  -- `hsrc`) identify both that spine and `as₂` with the source spine
  have has₂sq : w = 0 → ℓ ≠ 0 → as₂ = srcVals is (srcList Es nF) := by
    intro hw hℓ0
    subst hw
    obtain ⟨hle, -, hprop⟩ := hK.hsq rfl hℓ0
    have hj0 : j = 0 := by omega
    subst hj0
    rw [hFsjD, hEsjD] at hprop
    have hpropC := hsrc rfl hℓ0 (consList as₁ ρ) hsatC
    rw [hFsjD, hEsjD] at hpropC
    have := srcVals_of_fit hpropC hsp₂ hidxEq
    rwa [hlenFs] at this
  have hfitBsq : w = 0 → ℓ ≠ 0 → SpineFit (consList bs₁ ρ) ((ds.drop nP).map (·.2.2)) as₂ := by
    intro hw hℓ0
    subst hw
    obtain ⟨hle, -, hprop⟩ := hK.hsq rfl hℓ0
    have hj0 : j = 0 := by omega
    subst hj0
    rw [hFsjD, hEsjD] at hprop
    have htpt : t = pt := by rw [hmkv, if_pos rfl]
    obtain ⟨-, i, a, ha⟩ := sumSet_zero_elim ht'
    -- the inhabited fibre is constructor `0`'s
    have hi0 : i = 0 := by
      cases hRi : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[i]? with
      | none =>
        unfold sumFibre at ha
        rw [hRi] at ha
        exact absurd ha (not_mem_empty _)
      | some _ =>
        have := (List.getElem?_eq_some_iff.mp hRi).1
        rw [rChains_length] at this
        have h1 : i < Fss.length := Nat.lt_of_lt_of_le this (Nat.min_le_left _ _)
        omega
    subst hi0
    rw [sumFibre_of_getElem? hRj] at ha
    obtain ⟨-, fs', hfs'⟩ := towerSet_zero_elim _ ha
    rw [fitsS_teleOfFields] at hfs'
    unfold rChain at hfs'
    obtain ⟨fs₁, fs₂, rfl, h1, h2⟩ := spineFit_append_split hfs'
    have hlenfs₁ : fs₁.length = nF := by rw [h1.length_eq, liftFields_length, hlenFs]
    rw [spineFit_liftFields, hKfr, hsh] at h1
    -- the index equation of the fibre's spine
    have hidx' : idxValsAt (consList bs₁ ρ) Es fs₁ = is := by
      match fs₂, h2 with
      | [e], ⟨he, _⟩ =>
        obtain ⟨-, hall⟩ := mem_idxEqAV he
        rw [hlenFs] at hall
        have hEs' : Es.length = Ids.length := by rw [hEs, hIds]
        have := (EqAll_idxEqsAt hEs' hlenfs₁).mp hall
        rw [hKfr, hsh, kframe_frameIdx hlenIs'] at this
        exact this
    -- both spines are the source spine
    have hfs₁ : fs₁ = srcVals is (srcList Es nF) := by
      rw [hKfr, hfrP] at hprop
      have := srcVals_of_fit hprop h1 hidx'
      rwa [hlenFs] at this
    rw [← has₂sq rfl hℓ0] at hfs₁
    rw [← hfs₁]
    exact h1
  -- the right-hand side's fit at the recursor's parameters (graph regime,
  -- and squash regime with a large eliminator)
  have hys₂ : (ys.map (interp V ρ)).drop nP = as₂ := by rw [hys, List.drop_left' hlen₁]
  have hxs₁ : (xs.take (nP + 1 + n)).map (interp V ρ) = (bs₁ ++ [M]) ++ ms := by
    rw [List.map_take, hxsv, List.take_append_of_le_length (by simp [hlenb₁, hlenm]; omega),
      List.take_of_length_le (by simp [hlenb₁, hlenm]; omega)]
  have hfitOf : SpineFit (consList bs₁ ρ) ((ds.drop nP).map (·.2.2)) as₂ →
      SpineFit ρ (lds.map (·.2)) ((xs.take (nP + 1 + n) ++ ys.drop nP).map (interp V ρ)) := by
    intro hfitB'
    rw [hldsDom, List.map_append (f := interp V ρ) (l₁ := xs.take (nP + 1 + n)) (l₂ := ys.drop nP),
      List.map_drop, hys₂, hxs₁]
    refine SpineFit.append ?_ ?_
    · have hpre := spineFit_prefix (as := (bs₁ ++ [M]) ++ ms) (bs := is ++ [t]) (by
        rw [← List.append_assoc]; exact hspR')
      rw [show ((bs₁ ++ [M]) ++ ms).length = nP + 1 + n from by simp [hlenb₁, hlenm]; omega,
        ← List.map_take] at hpre
      exact hpre
    · rw [spineFit_liftDoms, consList_append, consList_append, consList_cons, consList_nil,
        show n + 1 = ms.length + 1 from by omega, shiftE_consList_add ms 1, shiftE_succ_cons,
        shiftE_zero_zero]
      exact hfitB'
  -- the right-hand side's frame
  have hframeR : consList ((xs.take (nP + 1 + n) ++ ys.drop nP).map (interp V ρ)) ρ
      = consList as₂ (consList ms (cons M (consList bs₁ ρ))) := by
    rw [List.map_append (f := interp V ρ) (l₁ := xs.take (nP + 1 + n)) (l₂ := ys.drop nP),
      List.map_drop, hys₂, hxs₁, consList_append, consList_append, consList_append, consList_cons,
      consList_nil]
  -- the right-hand side: the rule's fold to the core (given the fit)
  have hRHSOf : SpineFit (consList bs₁ ρ) ((ds.drop nP).map (·.2.2)) as₂ →
      interp V ρ (AnnotTerm.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))
      = interp V (consList as₂ (consList ms (cons M (consList bs₁ ρ))))
          (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss.getD j [])) := by
    intro hfitB'
    rw [interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hRa,
      mkLamsAV_fold_graded (by rw [← hRa]; exact (hokRa ρ).1) (hfitOf hfitB'), hframeR]
  -- the left-hand side: the recursor's fold
  have hLHS : interp V ρ (AnnotTerm.mkAppN R
        (xs ++ [AnnotTerm.mkAppN (sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]))
      = ((((bs₁ ++ [M]) ++ ms) ++ is) ++ [t]).foldl SetTheory.app (interp V ρ R) := by
    rw [interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app),
      List.map_append, List.map_cons, List.map_nil, hxsv, htv]
  -- at `ℓ = 0` the rule reads as the point (every binder bit is `0`)
  have hRaPt : ℓ = 0 → interp V ρ Ra = pt := by
    intro hℓ0
    have hb0 : b = 0 := hbz.mp hℓ0
    have hlen : lds.length = nP + 1 + n + nF := by
      have := congrArg List.length hldsDom
      simp only [List.length_map, List.length_append, List.length_take, liftDoms_length,
        List.length_drop, hlenDs, h.hlen] at this
      omega
    cases hlds : lds with
    | nil => rw [hlds] at hlen; simp at hlen; omega
    | cons d rest =>
      have hd : d.1 = 0 := by rw [← hb0]; exact hldsBits d (by rw [hlds]; exact List.mem_cons_self)
      rw [hRa, hlds, mkLamsAV, interp_lam, hd, lamR_zero]
  refine ⟨?_, ?_⟩
  · rw [hLHS]
    by_cases hℓ0 : ℓ = 0
    · -- both sides are the point
      have hRpt : interp V ρ R = pt := by
        rw [hR]
        have hmem := nativeRecAVI_mem h ρ
        refine eq_pt_of_mem_univZero ?_ hmem
        cases hrds : rds with
        | nil => have := h.hlen; rw [hrds] at this; simp at this
        | cons d rest =>
          rw [hrds] at h
          show piR d.2.1 _ _ ∈ˢ _
          rw [(h.hz d List.mem_cons_self).mp hℓ0]
          exact piR_zero_mem_univZero
      rw [hRpt, foldl_app_pt_sum, interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app),
        hRaPt hℓ0, foldl_app_pt_sum]
    · by_cases hw : w = 0
      · -- the squash regime: the recursor's iota at the proof point,
        -- the fields the source spine
        rw [hRHSOf (hfitBsq hw hℓ0)]
        subst hw
        have htpt : t = pt := by rw [hmkv, if_pos rfl]
        subst htpt
        have hiota := nativeRecAVI_iota_sq h rfl hℓ0 ρ hlenb₁ hlenMs' hlenIs' hspR'
        rw [← hR] at hiota
        obtain ⟨hle, -, -⟩ := hK.hsq rfl hℓ0
        have hj0 : j = 0 := by omega
        subst hj0
        rw [hiota, interp_fixRuleCoreAV hbz hlenb₁ hlenm hlen₂ hjn hRcl, hEsjD, hFsjD, hlenFs,
          ← has₂sq rfl hℓ0]
      · rw [hRHSOf (hfitB hw)]
        have hmaj : t = inj j (mkTower (as₂ ++ [pt])) := by rw [hmkv, if_neg hw]
        have hiota := nativeRecAVI_iota h hw hℓ0 ρ hspR' hjF
          (fs := as₂) (by rw [hFsjD, hlen₂, hlenFs]) hmaj
        rw [← hR] at hiota
        rw [hiota, hKfr, hfrMs, hfrK, hfrP, hFsjD, hlenFs,
          interp_fixRuleCoreAV hbz hlenb₁ hlenm hlen₂ hjn hRcl]
        rfl
  · intro hxs_ok hys_ok
    have hargs : ∀ a ∈ xs.take (nP + 1 + n) ++ ys.drop nP, WellDenotedV V ρ a := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hxs_ok a (List.mem_of_mem_take h)
      · exact hys_ok a (List.mem_of_mem_drop h)
    by_cases hℓ0 : ℓ = 0
    · exact mkAppN_wellDenotedV_of_pt (hokRa ρ) (hRaPt hℓ0) hargs
    · have hfitB' : SpineFit (consList bs₁ ρ) ((ds.drop nP).map (·.2.2)) as₂ := by
        by_cases hw : w = 0
        · exact hfitBsq hw hℓ0
        · exact hfitB hw
      exact mkAppN_wellDenotedV_of_lam (hokRa ρ) hargs (by rw [← hRa]; exact (hokRa ρ).1)
        (Or.inr (by rw [hRa])) (hfitOf hfitB')

end ConLeche.Model
