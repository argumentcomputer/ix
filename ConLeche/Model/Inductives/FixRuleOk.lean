module

import ConLeche.Model.Inductives.FixRuleKit
public import ConLeche.Model.Inductives.FixRecLaw
public section

/-!
# The rule right-hand side's gradedness (task #188)

A recursive rule's right-hand side `λ p⃗ M m⃗ f⃗. m_j f⃗ ih⃗` mentions the
recursor (in the inductive hypotheses `ih_i = rec p⃗ M m⃗ e⃗_i f_i`), so
the kernel's inference run at the pre-recursor environment cannot
certify it as the sum route's; its `WellDenotedV` is proved from the
model: the minor lies in its ih-extended space (the K-frame package),
the fields fit, each inductive hypothesis is the recursor leaf — in
the recursor type's reading — applied along a spine fitting the
binder data (`FixPre.hspine`), landing in the ih domain
(`recConcAV_at`), and the ih tower folds (`ihSpL_spine`).  The
λ-tower's gradedness is the domain walk (`mkLamsC_wellDenoted`) and its
validity the validity walk (`mkLamsC_validV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The block split of a rule spine -/

/-- **The block split** of a spine fitting the recursor's binder data
below the indices: the parameters, the motive (in its reading), the
minors (in their ih-extended readings). -/
theorem fixBlock_split {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {elimL : Level}
    {nP nIdx n ℓ w b : Nat}
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {cds : List CtorDatumR} (hn : cds.length = n)
    {Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hminor : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ j cd, cds[j]? = some cd → ∀ (M : V) (ms : List V), ms.length = j →
        interp V (consList ms (cons M ρp))
            (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
              cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp M (Ess.getD j []) j fs)
              (ihDomsI ℓ ρp M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
            (Fss.getD j []) ρp [])
    (ρb : Nat → V) (as : List V)
    (hsp : SpineFit ρb ((pps.map (·.2.2) ++ [motiveAVI m T ψ nP nIdx elimL ips]) ++
        (fixMinorsData m ψ nP b cds 1).map (·.2.2)) as) :
    ∃ (ps : List V) (M : V) (ms : List V),
      as = (ps ++ [M]) ++ ms ∧ ps.length = nP ∧ ms.length = n ∧
      Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) ∧
      M ∈ˢ interp V (consList ps ρb) (motiveAVI m T ψ nP nIdx elimL ips) ∧
      (∀ j, j < n → ms.getD j pt ∈ˢ minorSpI ℓ
        (fun fs => ihSpL ℓ (concI w (consList ps ρb) M (Ess.getD j []) j fs)
          (ihDomsI ℓ (consList ps ρb) M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
        (Fss.getD j []) (consList ps ρb) []) := by
  have hlenMD : (fixMinorsData m ψ nP b cds 1).length = n := by rw [fixMinorsData_length, hn]
  obtain ⟨c₁, ms, rfl, hsp₂, hspM⟩ := spineFit_append_inv hsp
  obtain ⟨ps, m₁, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₂
  obtain ⟨M, rfl, hM⟩ := spineFit_singleton hspMot
  have hlenPs : ps.length = nP := by rw [hspP.length_eq, List.length_map, hlenP]
  have hlenMs : ms.length = n := by rw [hspM.length_eq, List.length_map, hlenMD]
  have hρp : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
    rwa [List.append_nil] at this
  have hframe : consList (ps ++ [M]) ρb = cons M (consList ps ρb) := by
    rw [consList_append, consList_cons, consList_nil]
  rw [hframe] at hspM
  refine ⟨ps, M, ms, rfl, hlenPs, hlenMs, hρp, hM, ?_⟩
  intro j hj
  obtain ⟨cd, hcd⟩ : ∃ cd, cds[j]? = some cd := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hmem := FixKI.spineFit_getD_mem' hspM (l := j) (by rw [List.length_map, hlenMD]; exact hj)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, fixMinorsData_getElem?, hcd,
    Option.map_some, Option.getD_some] at hmem
  have hread := hminor (consList ps ρb) hρp j cd hcd M (ms.take j)
    (by rw [List.length_take, hlenMs]; omega)
  rw [hread] at hmem
  exact hmem

/-! ## One inductive hypothesis -/

/-- **An inductive hypothesis' facts** at the rule's leaf frame (task
#202: under the field's telescope): the recursor at the block, the
field's index values and the field applied to the telescope's values
is graded, valid, and the λ-tower over the telescope lies in the ih
domain — the nested product of the motive at the index values and the
applied field. -/
theorem ihAppAV_facts {ℓ w u s nP nF nIdx n j i : Nat} {rds : List (Nat × Nat × AnnotTerm)}
    {Fss₀ Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx) (hjn : j < n)
    {Fs : List AnnotTerm} (hFsj : Fss[j]? = some Fs) (hlenFs : Fs.length = nF)
    {R : AnnotTerm} (hR : R = nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
    (hRcl : Term.bvarsBelow 0 R.erase)
    {ρ : Nat → V} {as₁ ms as₂ : List V} {M : V}
    (hlen₁ : as₁.length = nP) (hlenm : ms.length = n) (hlen₂ : as₂.length = nF)
    (hRok : ∀ σ : Nat → V, WellDenotedV V σ R)
    (hspB : SpineFit ρ ((rds.take (nP + 1 + n)).map (·.2.2)) ((as₁ ++ [M]) ++ ms))
    (hreal : ChainsRealI (fixFamI u w (consList as₁ ρ) Ids nIdx rss tlss Eiss Fss₀ Ess) u w
      (consList as₁ ρ) Ids rss tlss Eiss Fss₀ Fss Ess)
    {b : Nat} (hbz : ℓ = 0 ↔ b = 0)
    (hTV : FieldsValid (consList (as₂.take i) (consList as₁ ρ))
      (((tlss.getD j []).getD i []).map (·.2.2)))
    (hEisV : ∀ bs : List V,
      SpineFit (consList (as₂.take i) (consList as₁ ρ)) (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValid V (consList bs (consList (as₂.take i) (consList as₁ ρ))) E)
    (hsp₂ : SpineFit (consList as₁ ρ) Fs as₂)
    (hi : i ∈ recIdx (rss.getD j []) nF) :
    WellDenoted V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        (ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i [])) ∧
      AnnotValid V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        (ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i [])) ∧
      interp V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
          (ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i []))
        ∈ˢ piTele ℓ (teleOfFields (consList (as₂.take i) (consList as₁ ρ))
            (((tlss.getD j []).getD i []).map (·.2.2)))
          (fun as => SetTheory.app
            ((((Eiss.getD j []).getD i []).map
              (interp V (consList as (consList (as₂.take i) (consList as₁ ρ))))).foldl
                SetTheory.app M)
            (as.foldl SetTheory.app (as₂.getD i pt))) [] := by
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  have hjF : j < Fss.length := by rw [hFss]; exact hjn
  have hFsD : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  -- the real chain at the field: the slot's fit and the field's value
  have hc := chainRealI_at (Fss₀.getD j []) Fs 0 [] as₂ rfl (by rw [← hFsD]; exact hreal.2.2.2.2 j hjF)
    (by simpa using hsp₂) i (by rw [hlenFs]; exact hik) (by rw [Nat.zero_add]; exact hri)
  rw [Nat.zero_add, List.nil_append] at hc
  obtain ⟨hfitS, heq⟩ := hc
  -- the family's applications are bounded
  have hfamU : ∀ t, SetTheory.app (fixFamI u w (consList as₁ ρ) Ids nIdx rss tlss Eiss Fss₀ Ess) t
      ∈ˢ (univ w : V) := by
    intro t
    rw [← hIds]
    exact famApp_mem_univ (fixFamI_mem _ _ _ _ _ _ _ _ _) t
  -- the field lies in the slot's value
  have hfield : as₂.getD i pt ∈ˢ slotSet w u (consList (as₂.take i) (consList as₁ ρ))
      ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])
      (fixFamI u w (consList as₁ ρ) Ids nIdx rss tlss Eiss Fss₀ Ess) := by
    have := FixKI.spineFit_getD_mem' hsp₂ (by rw [hlenFs]; exact hik)
    rw [heq] at this
    exact this
  have hshB : shiftE (Fss.length + 1) 0 (consList ((as₁ ++ [M]) ++ ms) ρ) = consList as₁ ρ := by
    rw [hFss, consList_append, consList_append, consList_cons, consList_nil, shiftE_minors hlenm]
  -- the recursor leaf's membership
  have hRmem : interp V ρ R ∈ˢ interp V ρ (mkPisAV rds (recConcAV Fss.length Ids.length)) := by
    rw [hR]; exact nativeRecAVI_mem h ρ
  have hM : consList ((as₁ ++ [M]) ++ ms) ρ n = M := by
    rw [consList_append, consList_append, consList_cons, consList_nil,
      show n = 0 + ms.length from by omega, consList_apply_add]
    rfl
  -- **per telescope spine**: the body's grading, value and validity
  have hbody : ∀ bs : List V,
      SpineFit (consList (as₂.take i) (consList as₁ ρ)) (((tlss.getD j []).getD i []).map (·.2.2)) bs →
      WellDenoted V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
          (AnnotTerm.mkAppN R (recPrefixBvarsM nP n nF bs.length ++
            ((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 bs.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)])) ∧
        interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
            (AnnotTerm.mkAppN R (recPrefixBvarsM nP n nF bs.length ++
              ((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 bs.length) ++
              [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)]))
          ∈ˢ SetTheory.app
            ((((Eiss.getD j []).getD i []).map
              (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))).foldl
                SetTheory.app M)
            (bs.foldl SetTheory.app (as₂.getD i pt)) ∧
        (ℓ = 0 → SetTheory.app
            ((((Eiss.getD j []).getD i []).map
              (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))).foldl
                SetTheory.app M)
            (bs.foldl SetTheory.app (as₂.getD i pt)) ∈ˢ (univZero : V)) ∧
        AnnotValid V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
          (AnnotTerm.mkAppN R (recPrefixBvarsM nP n nF bs.length ++
            ((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 bs.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)])) := by
    intro bs hsp
    obtain ⟨hEok, hvsp⟩ := hfitS.2.2 bs hsp
    rw [consList_append] at hEok hvsp
    have hmem := slotSet_fold_mem hfamU hfield hsp
    generalize hvals : ((Eiss.getD j []).getD i []).map
      (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))) = vals at hvsp hmem ⊢
    have hfit : SpineFit ρ (rds.map (·.2.2))
        (((as₁ ++ [M]) ++ ms) ++ vals ++ [bs.foldl SetTheory.app (as₂.getD i pt)]) := by
      refine h.hspine ρ ((as₁ ++ [M]) ++ ms) (by rw [hFss]; exact hspB) vals _ ?_ ?_
      · rw [hshB]; exact hvsp
      · rw [hshB, hIds]; exact hmem
    have hchain := appChainOk_of_mkPisAV' h.hz (fun hm as' hsp' => h.hconc0 hm ρ as' hsp') hRmem hfit
    have hval := mkPisAV_fold_mem h.hz (fun hm as' hsp' => h.hconc0 hm ρ as' hsp') hRmem hfit
    have hlenVals : vals.length = nIdx := by rw [hvsp.length_eq, hIds]
    have hRi : interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))) R
        = interp V ρ R := interp_closed (V := V) hRcl _ ρ
    -- the argument readings
    have hpre := map_recPrefixBvarsM_interp hlen₁ hlenm hlen₂ (M := M) (ρ := ρ) bs
    have hvars : (teleVarsAV bs.length).map
        (interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ)))))) = bs :=
      map_fieldBvars_interp rfl _
    have hfld : interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
        (AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length))
        = bs.foldl SetTheory.app (as₂.getD i pt) := by
      rw [interp_mkAppN, interp_bvar, consList_apply_add, consList_apply_lt' as₂ _ (by omega),
        show as₂.length - 1 - (nF - 1 - i) = i from by omega,
        ← List.foldl_map (f := interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))))
          (g := SetTheory.app) (l := teleVarsAV bs.length), hvars]
    have hidx : ∀ E ∈ (Eiss.getD j []).getD i [],
        interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
            (ihIdxAtM nF (n + 1) i 0 bs.length E)
          = interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))) E := by
      intro E _
      have := interp_ihIdxAtM (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms) (by omega)
        (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) bs E
      rw [consList_nil] at this
      exact this
    have hargs : (recPrefixBvarsM nP n nF bs.length ++
        ((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)]).map
          (interp V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))))
        = ((as₁ ++ [M]) ++ ms) ++ vals ++ [bs.foldl SetTheory.app (as₂.getD i pt)] := by
      rw [List.map_append, List.map_append, hpre, List.map_map]
      simp only [List.map_cons, List.map_nil]
      rw [hfld]
      congr 2
      rw [← hvals]
      apply List.map_congr_left
      intro E hE
      simp only [Function.comp]
      exact hidx E hE
    have hargsOk : ∀ a ∈ recPrefixBvarsM nP n nF bs.length ++
        ((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)],
        WellDenoted V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))) a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact recPrefixBvarsM_wellDenoted ha
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          have := (WellDenoted_ihIdxAtM (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms)
            (by omega) (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) bs E)
          rw [consList_nil] at this
          exact this.mpr (hEok E hE)
      · rw [List.mem_singleton] at ha; subst ha
        refine (mkAppN_wellDenoted_of_chain (f := .bvar (nF - 1 - i + bs.length))
          (args := teleVarsAV bs.length)
          (σ := consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))) trivial
          (fun a ha => ?_) ?_).1
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
        · rw [interp_bvar, consList_apply_add, consList_apply_lt' as₂ _ (by omega),
            show as₂.length - 1 - (nF - 1 - i) = i from by omega, hvars]
          exact slotSet_chainOk hfamU hfield hsp
    obtain ⟨hok, hv⟩ := mkAppN_wellDenoted_of_chain (hRok _).1 hargsOk (by rw [hargs, hRi]; exact hchain)
    rw [consList_append, consList_append, consList_cons, consList_nil, hFss, hIds,
      recConcAV_at vals hlenVals, hM] at hval
    refine ⟨hok, by rw [hv, hargs, hRi]; exact hval, fun h0 => ?_, ?_⟩
    · have := h.hconc0 h0 ρ _ hfit
      rw [consList_append, consList_append, consList_cons, consList_nil, hFss, hIds,
        recConcAV_at vals hlenVals, hM] at this
      exact this
    · refine mkAppN_validV (hRok _).2 fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact recPrefixBvarsM_validV ha
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          have := (AnnotValid_ihIdxAtM (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms)
            (by omega) (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) bs E)
          rw [consList_nil] at this
          exact this.mpr (hEisV bs hsp E hE)
      · rw [List.mem_singleton] at ha; subst ha
        refine mkAppN_validV trivial fun a ha => ?_
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
  -- **the tower**: the moved telescope's walk and the leaf facts (the
  -- telescope re-bit to the elimination bit, task #202 A2)
  have hdom_eq : (ihTeleAtR nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i []))).map (·.2.2)
      = (ihTeleAtR nF (n + 1) i 0 ((tlss.getD j []).getD i [])).map (·.2.2) := by
    rw [ihTeleAtR, ihTeleAtR, ihTeleAtGo_rebit, rebit_map_dom]
  have hspIff : ∀ bs : List V,
      SpineFit (consList as₂ (consList ms (cons M (consList as₁ ρ))))
          ((ihTeleAtR nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i []))).map (·.2.2)) bs ↔
        SpineFit (consList (as₂.take i) (consList as₁ ρ)) (((tlss.getD j []).getD i []).map (·.2.2)) bs := by
    intro bs
    have := spineFit_ihTeleAtGo (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms) (by omega)
      (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) ((tlss.getD j []).getD i []) [] bs
    simp only [List.length_nil, consList] at this
    rw [hdom_eq]
    exact this
  have hwalk : DomsWalk (consList as₂ (consList ms (cons M (consList as₁ ρ))))
      (ihTeleAtR nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i []))) := by
    refine domsWalk_of_fieldsOkB (w := w) ?_
    have := fieldsOkB_ihTeleAtGo (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms) (by omega)
      (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) ((tlss.getD j []).getD i []) [] hfitS.1
    simp only [List.length_nil, consList] at this
    rw [hdom_eq]
    exact this
  have hz : ∀ d ∈ ihTeleAtR nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i [])), (ℓ = 0 ↔ d.2.1 = 0) := by
    intro d hd
    rw [ihTeleAtR, ihTeleAtGo_rebit] at hd
    rw [mem_rebit hd]; exact hbz
  have hunder : UnderTowerOk ℓ (consList as₂ (consList ms (cons M (consList as₁ ρ))))
      (AnnotTerm.mkAppN R (recPrefixBvarsM nP n nF (rebit b ((tlss.getD j []).getD i [])).length ++
        ((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i [])).length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + (rebit b ((tlss.getD j []).getD i [])).length))
          (teleVarsAV (rebit b ((tlss.getD j []).getD i [])).length)]))
      (AnnotTerm.mkAppN (.bvar (nF + (n + 1) - 1 + 0 + (rebit b ((tlss.getD j []).getD i [])).length))
        (((Eiss.getD j []).getD i []).map (ihIdxAtM nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i [])).length) ++
          [AnnotTerm.mkAppN (.bvar (nF - 1 - i + 0 + (rebit b ((tlss.getD j []).getD i [])).length))
            (teleVarsAV (rebit b ((tlss.getD j []).getD i [])).length)]))
      (ihTeleAtR nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i []))) := by
    refine underTowerOk_of_walk hwalk fun bs hsp => ?_
    have hsp' := (hspIff bs).mp hsp
    have hlen : bs.length = (rebit b ((tlss.getD j []).getD i [])).length := by
      rw [hsp'.length_eq, List.length_map, rebit_length]
    obtain ⟨hok, hmem, h0, -⟩ := hbody bs hsp'
    have hT := interp_ihDomBody (o := n + 1) (l := 0) (ρp := consList as₁ ρ) (M := M) (ms := ms)
      (by omega) (fs := as₂) (ihs := []) hlen₂ rfl hik bs ((Eiss.getD j []).getD i [])
    rw [consList_nil] at hT
    rw [← hlen, hT]
    exact ⟨hok, hmem, h0⟩
  refine ⟨mkLamsAV_bits_wellDenoted hz hunder, ?_, ?_⟩
  · -- validity: the moved telescope and the body at every leaf
    refine mkLamsAV_bits_validV (underTowerValid_of ?_ fun bs hsp => ?_)
    · intro k d hk bs hsp
      have hv := fieldsValid_ihTeleAtGo (o := n + 1) (ρp := consList as₁ ρ) (M := M) (ms := ms)
        (by omega) (fs := as₂) (ihs := []) hlen₂ rfl (Nat.le_of_lt hik) ((tlss.getD j []).getD i []) []
        hTV
      simp only [List.length_nil, consList] at hv
      have hv' : FieldsValid (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        ((ihTeleAtR nF (n + 1) i 0 (rebit b ((tlss.getD j []).getD i []))).map (·.2.2)) := by
        rw [hdom_eq]; exact hv
      have := fieldsValid_getD hv' (j := k)
        (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hk).1)
        (bs := bs) (by rw [← List.map_take]; exact hsp)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hk] at this
      exact this
    · have hsp' := (hspIff bs).mp hsp
      have hlen : bs.length = (rebit b ((tlss.getD j []).getD i [])).length := by
        rw [hsp'.length_eq, List.length_map, rebit_length]
      rw [← hlen]
      exact (hbody bs hsp').2.2.2
  · -- the value lies in the ih domain
    have hdom := interp_ihDomAV (ℓ := ℓ) (o := n + 1) (l := 0) (ρp := consList as₁ ρ) (M := M)
      (ms := ms) (by omega) (fs := as₂) (ihs := []) hlen₂ rfl hik
      (tl := rebit b ((tlss.getD j []).getD i [])) (fun d hd => by rw [mem_rebit hd]; exact hbz.symm)
      ((Eiss.getD j []).getD i [])
    rw [consList_nil, rebit_map_dom] at hdom
    rw [← hdom]
    unfold ihDomAV ihAppAV
    exact mkLamsAV_bits_mem hz hunder

/-! ## The rule's right-hand side -/

set_option maxHeartbeats 6400000 in
/-- **The rule's right-hand side is `WellDenotedV`** at every frame. -/
theorem fixRuleOk {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {elimL : Level}
    {nP nIdx n ℓ w u s b : Nat} (hℓ : elimL.eval ψ = ℓ)
    (hb : pwBit ψ (Level.zeronessOf elimL) = b) (hbz : ℓ = 0 ↔ b = 0)
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {cds : List CtorDatumR} (hn : cds.length = n)
    {Fss₀ Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hlenFs : Fss.length = n) (hlenEs : Ess.length = n)
    (hEs : ∀ j, j < n → (Ess.getD j []).length = nIdx)
    (hEisLen : ∀ j i, i ∈ recIdx (rss.getD j []) (Fss.getD j []).length →
      ((Eiss.getD j []).getD i []).length = nIdx)
    (h : FixPre V ℓ w u nP Fss Ess Fss₀ (ips.map (·.2.2)) rss tlss Eiss
      (fixRecDataAV m T ψ nP nIdx elimL pps ips cds) s)
    (okΓ : ∀ i, i < nP + n + nIdx + 2 → ∀ ρ : Nat → V,
      Sat V (((((fixRecDataAV m T ψ nP nIdx elimL pps ips cds).map (·.2.2)).reverse)).drop
        (nP + n + nIdx + 2 - i)) ρ →
      WellDenotedV V ρ (((((fixRecDataAV m T ψ nP nIdx elimL pps ips cds).map (·.2.2)).reverse)).getD
        (nP + n + nIdx + 2 - 1 - i) default))
    {R : AnnotTerm}
    (hR : R = nativeRecAVI ℓ w nP Fss Ess (ips.map (·.2.2)) rss tlss Eiss
      (fixRecDataAV m T ψ nP nIdx elimL pps ips cds) s)
    (hRcl : Term.bvarsBelow 0 R.erase) (hRok : ∀ ρ : Nat → V, WellDenotedV V ρ R)
    (hframes : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      XChainsOk u w ρp (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess ∧
      ChainsRealI (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) u w ρp
        (ips.map (·.2.2)) rss tlss Eiss Fss₀ Fss Ess ∧
      (∀ j, j < n → FieldsOkB w ρp (Fss.getD j []) ∧
        ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
          (∀ E ∈ Ess.getD j [], WellDenoted V (consList bs ρp) E) ∧
          SpineFit ρp (ips.map (·.2.2)) (idxValsAt ρp (Ess.getD j []) bs)) ∧
      (∀ σ : Nat → V, interp V σ (m.acval T ψ)
        = interp V (fun k => ρp (k + nP))
            (nativeTyAVI u w (pps ++ ips) (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess)) ∧
      (∀ j cd, cds[j]? = some cd → ∀ (M : V) (ms : List V), ms.length = j →
        interp V (consList ms (cons M ρp))
            (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
              cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp M (Ess.getD j []) j fs)
              (ihDomsI ℓ ρp M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
            (Fss.getD j []) ρp []))
    (hvalid : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp Fss ∧
      (∀ j, j < n → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
        ∀ fs : List V, SpineFit ρp (Fss.getD j []) fs →
        FieldsValid (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) bs →
        ∀ E ∈ (Eiss.getD j []).getD i [], AnnotValid V (consList bs (consList (fs.take i) ρp)) E))
    (hsingle : w = 0 → ℓ ≠ 0 → n ≤ 1)
    (hprop : w = 0 → ℓ ≠ 0 → ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ j, j < n → ∀ i, i < (Fss.getD j []).length →
      srcOfEs (Ess.getD j []) (Fss.getD j []).length i = none →
      ∀ fs : List V, SpineFit ρp ((Fss.getD j []).take i) fs →
        interp V (consList fs ρp) ((Fss.getD j []).getD i default) ∈ˢ (univZero : V))
    {j : Nat} {C : Name} {nF : Nat} {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {recIdxJ : List Nat} {EissJ : List (List AnnotTerm)} {tlsJ : List (List (Nat × Nat × AnnotTerm))}
    (hcd : cds[j]? = some (C, nF, ds, Es, recIdxJ, EissJ, tlsJ))
    (hlenDs : ds.length = nP + nF) (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hEsj : Ess[j]? = some Es) (hrecIdx : recIdxJ = recIdx (rss.getD j []) nF)
    (hEissJ : Eiss.getD j [] = EissJ) (htlsJ : tlss.getD j [] = tlsJ)
    (hleafC : m.acval C ψ = sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss))
    (hclC : Term.bvarsBelow 0 (m.acval C ψ).erase)
    (hiff : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp ↔
      Sat V (((ds.take nP).map (·.2.2)).reverse) ρp) :
    ∀ ρ : Nat → V, WellDenotedV V ρ (mkLamsAV (fixRuleDataAV m T ψ nP nIdx elimL pps ips cds ds)
      (fixRuleCoreAV b R nP nF n j recIdxJ tlsJ EissJ)) := by
  intro ρ
  subst hrecIdx
  subst hEissJ
  subst htlsJ
  have hjn : j < n := by rw [← hn]; exact (List.getElem?_eq_some_iff.mp hcd).1
  have hjF : j < Fss.length := by rw [hlenFs]; exact hjn
  have hlenIds : ((ips.map (·.2.2))).length = nIdx := by rw [List.length_map, hlenI]
  have hlenFs' : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hFsD : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  have hEsD : Ess.getD j [] = Es := by rw [List.getD_eq_getElem?_getD, hEsj]; rfl
  have hlenMD : (fixMinorsData m ψ nP b cds 1).length = n := by rw [fixMinorsData_length, hn]
  -- the binder data
  generalize hrds : fixRecDataAV m T ψ nP nIdx elimL pps ips cds = rds at h okΓ hR
  have hrdsE : rds = (rebit b pps ++ [(0, b, motiveAVI m T ψ nP nIdx elimL ips)] ++
      fixMinorsData m ψ nP b cds 1) ++ rebit b (liftDoms (n + 1) 0 ips) ++
      [(0, b, majorAVAt m T ψ nP nIdx n)] := by
    rw [← hrds, fixRecDataAV, hb, hn]
  have hlenR : rds.length = nP + n + nIdx + 2 := by
    rw [← hrds, fixRecDataAV_length hlenP hlenI, hn]
  generalize hX : rebit b pps ++ [(0, b, motiveAVI m T ψ nP nIdx elimL ips)] ++
      fixMinorsData m ψ nP b cds 1 = X at hrdsE
  have hlenX : X.length = nP + 1 + n := by
    rw [← hX]
    simp only [List.length_append, rebit_length, hlenP, List.length_singleton, hlenMD]
  have hprefix : rds.take (nP + 1 + n) = X := by
    have hlenXD : (X ++ rebit b (liftDoms (n + 1) 0 ips)).length = nP + 1 + n + nIdx := by
      rw [List.length_append, hlenX, rebit_length, liftDoms_length, hlenI]
    rw [hrdsE,
      List.take_append_of_le_length (by omega :
        nP + 1 + n ≤ (X ++ rebit b (liftDoms (n + 1) 0 ips)).length),
      List.take_append_of_le_length (by omega : nP + 1 + n ≤ X.length),
      List.take_of_length_le (by omega : X.length ≤ nP + 1 + n)]
  have hXdoms : X.map (·.2.2) = (pps.map (·.2.2) ++ [motiveAVI m T ψ nP nIdx elimL ips]) ++
      (fixMinorsData m ψ nP b cds 1).map (·.2.2) := by
    rw [← hX]
    simp only [List.map_append, List.map_cons, List.map_nil, rebit_map_dom]
  generalize hD : rebit b (liftDoms (n + 1) 0 (ds.drop nP)) = D
  have hDdoms : D.map (·.2.2) = (liftDoms (n + 1) 0 (ds.drop nP)).map (·.2.2) := by
    rw [← hD, rebit_map_dom]
  have hlenD : D.length = nF := by rw [← hD, rebit_length, liftDoms_length]; simp [hlenDs]
  -- the rule's binder data are the block's and the lifted fields, at bit `b`
  have hlds : fixRuleDataAV m T ψ nP nIdx elimL pps ips cds ds = (X ++ D).map fun d => (b, d.2.2) := by
    unfold fixRuleDataAV
    rw [hb, hn, hX, hD]
    apply List.map_congr_left
    intro d hd
    have hbit : d.2.1 = b := by
      rw [← hX, ← hD] at hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with ((hd | rfl) | hd) | hd
      · exact mem_rebit hd
      · rfl
      · exact mem_fixMinorsData hd
      · exact mem_rebit hd
    rw [hbit]
  have hzXD : ∀ d ∈ X ++ D, (b = 0 ↔ d.2.1 = 0) := by
    intro d hd
    have hbit : d.2.1 = b := by
      rw [← hX, ← hD] at hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with ((hd | rfl) | hd) | hd
      · exact mem_rebit hd
      · rfl
      · exact mem_fixMinorsData hd
      · exact mem_rebit hd
    rw [hbit]
  rw [hlds]
  show WellDenotedV V ρ (mkLamsC b (X ++ D) (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss.getD j [])))
  -- the conclusion, spelled at the rule's leaf frame
  generalize hT : AnnotTerm.mkAppN (.bvar (nF + (n + 1) - 1))
      ((Es.map fun E => E.liftN (n + 1) nF) ++
        [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + (n + 1) + nF) ++ fieldBvars nF)]) = TC
  -- **the leaf facts** at every fitting spine of the rule's binder data
  have hleaf : ∀ as : List V, SpineFit ρ ((X ++ D).map (·.2.2)) as →
      WellDenoted V (consList as ρ) (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss.getD j [])) ∧
      interp V (consList as ρ) (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss.getD j []))
        ∈ˢ interp V (consList as ρ) TC ∧
      (b = 0 → interp V (consList as ρ) TC ∈ˢ (univZero : V)) ∧
      AnnotValid V (consList as ρ) (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss.getD j [])) := by
    intro as hsp
    rw [List.map_append] at hsp
    obtain ⟨block, as₂, rfl, hspB, hspD⟩ := spineFit_append_inv hsp
    rw [hXdoms] at hspB
    obtain ⟨as₁, M, ms, rfl, hlen₁, hlenm, hρp, hM, hms⟩ :=
      fixBlock_split (T := T) (elimL := elimL) (ips := ips) hlenP hn
        (fun ρp hρp => (hframes ρp hρp).2.2.2.2) ρ _ hspB
    have hframe : consList ((as₁ ++ [M]) ++ ms) ρ = consList ms (cons M (consList as₁ ρ)) := by
      rw [consList_append, consList_append, consList_cons, consList_nil]
    rw [hframe] at hspD
    rw [hDdoms, spineFit_liftDoms, shiftE_minors hlenm] at hspD
    have hlen₂ : as₂.length = nF := by rw [hspD.length_eq, hlenFs']
    rw [consList_append, hframe]
    obtain ⟨hXc, hreal, hfields, hleafT, -⟩ := hframes _ hρp
    obtain ⟨hvFss, hEisV⟩ := hvalid _ hρp
    have hsatC : Sat V (((ds.take nP).map (·.2.2)).reverse) (consList as₁ ρ) := (hiff _).mp hρp
    have hokB : SumFieldsOkB w (consList as₁ ρ) Fss := by
      intro Fs hFs
      obtain ⟨j', hj'⟩ := List.getElem?_of_mem hFs
      have hjn' : j' < n := by rw [← hlenFs]; exact (List.getElem?_eq_some_iff.mp hj').1
      have := (hfields j' hjn').1
      rwa [List.getD_eq_getElem?_getD, hj'] at this
    -- the K-frame at the constructor's index values
    have hfit : SpineFit (consList as₁ ρ) (ips.map (·.2.2)) (idxValsAt (consList as₁ ρ) Es as₂) := by
      have := ((hfields j hjn).2 as₂ (by rw [hFsD]; exact hspD)).2
      rwa [hEsD] at this
    obtain ⟨hK, -⟩ := fixKFrame_of hℓ hlenP hlenI hlenFs hlenEs hEs hEisLen hρp hXc hreal hfields
      hleafT hM hlenm hms hsingle (fun hw0 hℓ0 => hprop hw0 hℓ0 (consList as₁ ρ) hρp) hfit
    have hlenIs' : (idxValsAt (consList as₁ ρ) Es as₂).length = (ips.map (·.2.2)).length := by
      rw [hfit.length_eq]
    have hlenm' : ms.length = Fss.length := by rw [hlenFs]; exact hlenm
    have hfrP := kframe_frP (ρp := consList as₁ ρ) (M := M) hlenIs' hlenm'
    have hfrM := kframe_frM (ρp := consList as₁ ρ) (M := M) hlenIs' hlenm'
    -- the conclusion's value
    have hTv : interp V (consList as₂ (consList ms (cons M (consList as₁ ρ)))) TC
        = concI w (consList as₁ ρ) M Es j as₂ := by
      rw [← hT]
      exact interp_minorConcAV (o := n + 1) (by omega) hlenDs hleafC hclC hFsj hokB hsatC hspD
    have hconc0 : ℓ = 0 → concI w (consList as₁ ρ) M Es j as₂ ∈ˢ (univZero : V) := by
      intro h0
      have := hK.hyp.toRecHypCore.conc_univZero h0 hjF as₂
      rwa [hfrP, hfrM, hEsD] at this
    have hc0 : ℓ = 0 → ∀ acc, ihSpL ℓ (concI w (consList as₁ ρ) M (Ess.getD j []) j acc)
        (ihDomsI ℓ (consList as₁ ρ) M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j acc)
        ∈ˢ (univZero : V) := by
      intro h0 acc
      refine ihSpL_zero_univZero h0 ?_ _
      have := hK.hyp.toRecHypCore.conc_univZero h0 hjF acc
      rwa [hfrP, hfrM] at this
    -- the minor at the fields
    have hmj := hms j hjn
    have hchainM := minorSpI_appChainOk hc0 hmj (by rw [hFsD]; exact hspD)
    have hfoldM := minorSpI_fold hc0 hmj (by rw [hFsD]; exact hspD)
    rw [List.nil_append] at hfoldM
    have hbv : interp V (consList as₂ (consList ms (cons M (consList as₁ ρ)))) (.bvar (nF + n - 1 - j))
        = ms.getD j pt := by
      rw [interp_bvar, show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega,
        consList_apply_add, consList_apply_lt' ms _ (by omega),
        show ms.length - 1 - (n - 1 - j) = j from by omega]
    have hfb : (fieldBvars nF).map (interp V (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
        = as₂ := by
      show ((List.range nF).map fun k => AnnotTerm.bvar (nF - 1 - k)).map
        (interp V (consList as₂ (consList ms (cons M (consList as₁ ρ))))) = as₂
      exact map_fieldBvars_interp hlen₂ _
    obtain ⟨hokF, hvF⟩ := mkAppN_wellDenoted_of_chain (f := .bvar (nF + n - 1 - j)) (args := fieldBvars nF)
      (σ := consList as₂ (consList ms (cons M (consList as₁ ρ)))) trivial
      (fun a ha => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        trivial)
      (by rw [hbv, hfb]; exact hchainM)
    rw [hbv, hfb] at hvF
    -- the inductive hypotheses
    have har : (Fss.getD j []).length = nF := by rw [hFsD, hlenFs']
    have hih : ∀ i ∈ recIdx (rss.getD j []) nF,
        WellDenoted V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
          (ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i [])) ∧
        AnnotValid V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
          (ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i [])) ∧
        interp V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
            (ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i []))
          ∈ˢ piTele ℓ (teleOfFields (consList (as₂.take i) (consList as₁ ρ))
              (((tlss.getD j []).getD i []).map (·.2.2)))
            (fun as => SetTheory.app
              ((((Eiss.getD j []).getD i []).map
                (interp V (consList as (consList (as₂.take i) (consList as₁ ρ))))).foldl
                  SetTheory.app M)
              (as.foldl SetTheory.app (as₂.getD i pt))) [] := by
      intro i hi
      have hV := hEisV j hjn i (by rw [har]; exact hi) as₂ (by rw [hFsD]; exact hspD)
      exact ihAppAV_facts h hlenFs hlenIds hjn hFsj hlenFs' hR hRcl hlen₁ hlenm hlen₂ hRok
        (by rw [hprefix, hXdoms]; exact hspB) hreal hbz hV.1 hV.2 hspD hi
    -- the ih tower's fold
    have hAs : ihDomsI ℓ (consList as₁ ρ) M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j as₂
        = (recIdx (rss.getD j []) nF).map fun i =>
            piTele ℓ (teleOfFields (consList (as₂.take i) (consList as₁ ρ))
                (((tlss.getD j []).getD i []).map (·.2.2)))
              (fun as => SetTheory.app
                ((((Eiss.getD j []).getD i []).map
                  (interp V (consList as (consList (as₂.take i) (consList as₁ ρ))))).foldl
                    SetTheory.app M)
                (as.foldl SetTheory.app (as₂.getD i pt))) [] := by
      unfold ihDomsI
      simp only [har]
    have hsp_ih := ihSpL_spine (V := V) (ℓ := ℓ)
      (C := concI w (consList as₁ ρ) M (Ess.getD j []) j as₂)
      (As := ihDomsI ℓ (consList as₁ ρ) M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j as₂)
      (args := (recIdx (rss.getD j []) nF).map fun i =>
        ihAppAV R nP n nF i (rebit b ((tlss.getD j []).getD i [])) ((Eiss.getD j []).getD i []))
      (f := AnnotTerm.mkAppN (.bvar (nF + n - 1 - j)) (fieldBvars nF))
      (σ := consList as₂ (consList ms (cons M (consList as₁ ρ))))
      (fun h0 => by
        have := hK.hyp.toRecHypCore.conc_univZero h0 hjF as₂
        rwa [hfrP, hfrM] at this)
      hokF (by rw [hvF]; exact hfoldM)
      (by rw [hAs, List.length_map, List.length_map])
      (by
        intro l hl
        rw [hAs, List.length_map] at hl
        obtain ⟨i, hi⟩ : ∃ i, (recIdx (rss.getD j []) nF)[l]? = some i :=
          ⟨_, List.getElem?_eq_getElem hl⟩
        have hmem : i ∈ recIdx (rss.getD j []) nF := List.mem_of_getElem? hi
        have hgd1 : ∀ (f : Nat → AnnotTerm) (xs : List Nat) (d : AnnotTerm),
            xs[l]? = some i → (xs.map f).getD l d = f i := by
          intro f xs d hx
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]; rfl
        have hgd2 : ∀ (f : Nat → V) (xs : List Nat) (d : V),
            xs[l]? = some i → (xs.map f).getD l d = f i := by
          intro f xs d hx
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]; rfl
        rw [hAs, hgd1 _ _ _ hi, hgd2 _ _ _ hi]
        exact ⟨(hih i hmem).1, (hih i hmem).2.2⟩)
      (fun h0 A hA => by
        have := hK.hyp.hdoms0 h0 j as₂ A
        rw [hfrP, hfrM] at this
        exact this hA)
    rw [← AnnotTerm.mkAppN_append] at hsp_ih
    refine ⟨hsp_ih.1, ?_, ?_, ?_⟩
    · rw [hTv, ← hEsD]; exact hsp_ih.2
    · intro hb0
      rw [hTv]
      exact hconc0 (hbz.mpr hb0)
    · unfold fixRuleCoreAV
      refine mkAppN_validV trivial fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        trivial
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        exact (hih i hi).2.1
  -- **the tower**: the domain walk
  have hwalk : DomsWalk ρ (X ++ D) := by
    refine domsWalk_append ?_ ?_
    · have := domsWalk_take (nP + 1 + n) (h.hdoms ρ)
      rwa [hprefix] at this
    · intro as hsp
      rw [hXdoms] at hsp
      obtain ⟨as₁, M, ms, rfl, hlen₁, hlenm, hρp, -, -⟩ :=
        fixBlock_split (T := T) (elimL := elimL) (ips := ips) hlenP hn
          (fun ρp hρp => (hframes ρp hρp).2.2.2.2) ρ _ hsp
      rw [← hD]
      refine domsWalk_rebit b (domsWalk_liftDoms (w := w) _ 0 _ ?_)
      rw [consList_append, consList_append, consList_cons, consList_nil, shiftE_minors hlenm,
        ← hFsD]
      exact ((hframes _ hρp).2.2.1 j hjn).1
  refine ⟨mkLamsC_wellDenoted (T := TC) hzXD (underTowerOk_of_walk (C := TC) hwalk fun as hsp => ?_),
    mkLamsC_validV ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hleaf as hsp
    exact ⟨h1, h2, h3⟩
  · -- the validity walk
    refine underTowerValid_of ?_ fun as hsp => (hleaf as hsp).2.2.2
    intro k d hk as hsp
    rcases Nat.lt_or_ge k X.length with hkX | hkX
    · -- a block entry: the recursor's binder datum
      have hkR : rds[k]? = some d := by
        rw [List.getElem?_append_left hkX] at hk
        rw [← hprefix, List.getElem?_take_of_lt (by omega)] at hk
        exact hk
      have htake : (X ++ D).take k = rds.take k := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hkX), ← hprefix, List.take_take,
          show min k (nP + 1 + n) = k from by omega]
      rw [htake] at hsp
      have hsat := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp
      exact (prefixOk_of_okΓ hlenR okΓ k d hkR _ hsat).2
    · -- a field entry, lifted under the block
      rw [List.getElem?_append_right hkX] at hk
      have hkD : k - X.length < D.length := (List.getElem?_eq_some_iff.mp hk).1
      rw [← hD, show rebit b (liftDoms (n + 1) 0 (ds.drop nP))
          = (liftDoms (n + 1) 0 (ds.drop nP)).map (fun d => (d.1, b, d.2.2)) from rfl,
        List.getElem?_map, liftDoms_getElem?] at hk
      obtain ⟨q, hq⟩ : ∃ q, (ds.drop nP)[k - X.length]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hD, rebit_length, liftDoms_length] at hkD; exact hkD)⟩
      rw [hq] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      show AnnotValid V (consList as ρ) (q.2.2.liftN (n + 1) (0 + (k - X.length)))
      rw [List.take_append, List.take_of_length_le (by omega : X.length ≤ k)] at hsp
      rw [List.map_append] at hsp
      obtain ⟨block, as₂, rfl, hspB, hspD⟩ := spineFit_append_inv hsp
      rw [hXdoms] at hspB
      obtain ⟨as₁, M, ms, rfl, hlen₁, hlenm, hρp, -, -⟩ :=
        fixBlock_split (T := T) (elimL := elimL) (ips := ips) hlenP hn
          (fun ρp hρp => (hframes ρp hρp).2.2.2.2) ρ _ hspB
      have hframe : consList ((as₁ ++ [M]) ++ ms) ρ = consList ms (cons M (consList as₁ ρ)) := by
        rw [consList_append, consList_append, consList_cons, consList_nil]
      rw [hframe] at hspD
      rw [← hD, show rebit b (liftDoms (n + 1) 0 (ds.drop nP))
          = (liftDoms (n + 1) 0 (ds.drop nP)).map (fun d => (d.1, b, d.2.2)) from rfl,
        ← List.map_take, liftDoms_take, List.map_map] at hspD
      have hDmap : ((liftDoms (n + 1) 0 ((ds.drop nP).take (k - X.length))).map
          ((fun d : Nat × Nat × AnnotTerm => d.2.2) ∘ fun d => (d.1, b, d.2.2)))
          = (liftDoms (n + 1) 0 ((ds.drop nP).take (k - X.length))).map (·.2.2) := rfl
      rw [hDmap, spineFit_liftDoms, shiftE_minors hlenm] at hspD
      have hlenDrop : (ds.drop nP).length = nF := by simp [hlenDs]
      have hkD' : k - X.length < nF := by rw [hlenD] at hkD; exact hkD
      have hlen₂ : as₂.length = k - X.length := by
        rw [hspD.length_eq, List.length_map, List.length_take]
        omega
      rw [consList_append, hframe, AnnotValid_liftN, Nat.zero_add, ← hlen₂, shiftE_consList_len,
        shiftE_minors hlenm]
      have hvFs : FieldsValid (consList as₁ ρ) ((ds.drop nP).map (·.2.2)) := by
        have := (hvalid _ hρp).1 _ (List.mem_of_getElem? hFsj)
        exact this
      have := fieldsValid_getD hvFs (j := k - X.length) (by rw [hlenFs']; exact hkD')
        (bs := as₂) (by rw [← List.map_take]; exact hspD)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hq] at this
      simpa using this

end ConLeche.Model
