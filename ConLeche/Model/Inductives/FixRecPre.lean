module

public import ConLeche.Model.Inductives.FixRecKFrame
public section

/-!
# The recursive recursor's premise (task #188)

`FixPre` (`ConLeche/Semantics/Tower/FixRecI.lean`) — the frame-generic
premise of the recursor leaf's facts — from the recursor type's
readings: the binder data's gradings along every walk (`okΓ` of the
opened type), the per-parameter-frame facts of the block (the chains'
grading, the real chains' identification, the leaf's reading, the
minors' readings) and the sort of the type.  A fitting spine of the
recursor's binder data splits into the parameters, the motive, the
minors, the indices and the major; the K-frame package
(`fixKFrame_of`) answers at the split.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Walks -/

/-- The domains graded along every fitting walk, from the gradings at
the prefixes. -/
theorem domsWalk_of_prefixOk :
    ∀ (rds : List (Nat × Nat × AnnotTerm)) (Δ₀ : List AnnotTerm) (ρ : Nat → V), Sat V Δ₀ ρ →
      (∀ k d, rds[k]? = some d → ∀ σ : Nat → V,
        Sat V (((rds.take k).map (·.2.2)).reverse ++ Δ₀) σ → WellDenoted V σ d.2.2) →
      DomsWalk ρ rds
  | [], _, _, _, _ => trivial
  | d :: ds, Δ₀, ρ, hρ, hok => by
    refine ⟨hok 0 d rfl ρ (by simpa using hρ), fun a ha => ?_⟩
    refine domsWalk_of_prefixOk ds (d.2.2 :: Δ₀) (cons a ρ) (Sat_cons V hρ ha) ?_
    intro k d' hk σ hσ
    refine hok (k + 1) d' (by simpa using hk) σ ?_
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hσ

omit [SetTheory V] in
/-- The reversed context's tail is the reversed prefix. -/
theorem drop_reverse_map {rds : List (Nat × Nat × AnnotTerm)} {n k : Nat} (hlen : rds.length = n)
    (hk : k ≤ n) :
    ((rds.map (·.2.2)).reverse).drop (n - k) = ((rds.take k).map (·.2.2)).reverse := by
  rw [List.drop_reverse, List.length_map, hlen, show n - (n - k) = k from by omega, List.map_take]

/-- The per-entry gradings at the prefixes, from the opened type's
gradings. -/
theorem prefixOk_of_okΓ {rds : List (Nat × Nat × AnnotTerm)} {n : Nat} (hlen : rds.length = n)
    (okΓ : ∀ i, i < n → ∀ ρ : Nat → V,
      Sat V ((((rds.map (·.2.2)).reverse)).drop (n - i)) ρ →
      WellDenotedV V ρ ((((rds.map (·.2.2)).reverse)).getD (n - 1 - i) default)) :
    ∀ k d, rds[k]? = some d → ∀ σ : Nat → V,
      Sat V (((rds.take k).map (·.2.2)).reverse ++ []) σ → WellDenotedV V σ d.2.2 := by
  intro k d hk σ hσ
  have hkn : k < n := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hk).1
  rw [List.append_nil] at hσ
  have := okΓ k hkn σ (by rw [drop_reverse_map hlen (Nat.le_of_lt hkn)]; exact hσ)
  rwa [getD_reverse_of_peel hlen hkn hk] at this

omit [SetTheory V] in
/-- An entry of bounded binder data is bounded at its depth. -/
theorem domsBelow_getElem? :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k j : Nat} {d : Nat × Nat × AnnotTerm},
      DomsBelow k ds → ds[j]? = some d → Term.bvarsBelow (k + j) d.2.2.erase
  | [], _, _, _, _, h => nomatch h
  | d' :: ds, k, 0, d, hb, h => by
    obtain rfl := Option.some.inj h
    exact hb.1
  | d' :: ds, k, j + 1, d, hb, h => by
    have := domsBelow_getElem? (ds := ds) (k := k + 1) (j := j) hb.2 (by simpa using h)
    rwa [show k + 1 + j = k + (j + 1) from by omega] at this

/-! ## Lifted index domains -/

omit [SetTheory V] in
theorem shiftE_succ_cons' (n k : Nat) (a : V) (σ : Nat → V) :
    shiftE n (k + 1) (cons a σ) = cons a (shiftE n k σ) := by
  funext i
  cases i with
  | zero => simp [shiftE, cons]
  | succ i =>
    simp only [shiftE, cons_succ, Nat.succ_lt_succ_iff]
    split
    · rfl
    · rw [show i + 1 + n = i + n + 1 from by omega]; rfl

/-- A spine fits lifted domains exactly when it fits the domains at
the shifted frame. -/
theorem spineFit_liftDoms_iff (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) (σ : Nat → V) (as : List V),
      SpineFit σ ((liftDoms n k ds).map (·.2.2)) as ↔ SpineFit (shiftE n k σ) (ds.map (·.2.2)) as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ds, k, σ, a :: as => by
    simp only [liftDoms, List.map_cons, SpineFit]
    rw [interp_liftN, spineFit_liftDoms_iff n ds (k + 1) (cons a σ) as, shiftE_succ_cons']

/-! ## Spines of the recursor's binder data -/

/-- A spine fitting a single domain. -/
theorem spineFit_singleton {σ : Nat → V} {D : AnnotTerm} :
    ∀ {xs : List V}, SpineFit σ [D] xs → ∃ x, xs = [x] ∧ x ∈ˢ interp V σ D
  | [], h => h.elim
  | [x], h => ⟨x, rfl, h.1⟩
  | _ :: _ :: _, h => h.2.elim

omit [SetTheory V] in
/-- The frame `n + 1` below the K-frame's indices is the parameter
frame. -/
theorem shiftE_minors {n : Nat} {ρp : Nat → V} {M : V} {ms : List V} (hlenM : ms.length = n) :
    shiftE (n + 1) 0 (consList ms (cons M ρp)) = ρp := by
  rw [← hlenM, shiftE_consList_add ms 1 (cons M ρp), shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
/-- The K-frame as a cons list over the bottom. -/
theorem consList_kframe (ps : List V) (M : V) (ms is : List V) (ρb : Nat → V) :
    consList (((ps ++ [M]) ++ ms) ++ is) ρb = consList is (consList ms (cons M (consList ps ρb))) := by
  rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]

/-- **The K-frame split** of a spine fitting the recursor's binder
data below the major: the parameters, the motive (in its reading),
the minors (in their ih-extended readings) and a fitting index tuple. -/
theorem fixSpine_split {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {elimL : Level}
    {nP nIdx n ℓ w b : Nat}
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {cds : List CtorDatumR} (hn : cds.length = n)
    {Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hminor : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ j cd, cds[j]? = some cd → ∀ (M : V) (ms : List V), ms.length = j →
        interp V (consList ms (cons M ρp))
            (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2.2
              cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp M (Ess.getD j []) j fs)
              (ihDomsI ℓ ρp M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
            (Fss.getD j []) ρp [])
    (ρb : Nat → V) (as : List V)
    (hsp : SpineFit ρb (((pps.map (·.2.2) ++ [motiveAVI m T ψ nP nIdx elimL ips]) ++
        (fixMinorsData m ψ nP b cds 1).map (·.2.2)) ++ (liftDoms (n + 1) 0 ips).map (·.2.2)) as) :
    ∃ (ps : List V) (M : V) (ms is : List V),
      as = ((ps ++ [M]) ++ ms) ++ is ∧ ps.length = nP ∧ ms.length = n ∧ is.length = nIdx ∧
      Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) ∧
      M ∈ˢ interp V (consList ps ρb) (motiveAVI m T ψ nP nIdx elimL ips) ∧
      (∀ j, j < n → ms.getD j pt ∈ˢ minorSpI ℓ
        (fun fs => ihSpL ℓ (concI w (consList ps ρb) M (Ess.getD j []) j fs)
          (ihDomsI ℓ (consList ps ρb) M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
        (Fss.getD j []) (consList ps ρb) []) ∧
      SpineFit (consList ps ρb) (ips.map (·.2.2)) is := by
  have hlenMD : (fixMinorsData m ψ nP b cds 1).length = n := by rw [fixMinorsData_length, hn]
  obtain ⟨b₁, is, rfl, hsp₁, hspI⟩ := spineFit_append_inv hsp
  obtain ⟨c₁, ms, rfl, hsp₂, hspM⟩ := spineFit_append_inv hsp₁
  obtain ⟨ps, m₁, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₂
  obtain ⟨M, rfl, hM⟩ := spineFit_singleton hspMot
  have hlenPs : ps.length = nP := by rw [hspP.length_eq, List.length_map, hlenP]
  have hlenMs : ms.length = n := by rw [hspM.length_eq, List.length_map, hlenMD]
  have hlenIs : is.length = nIdx := by
    rw [hspI.length_eq, List.length_map, liftDoms_length, hlenI]
  have hρp : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
    rwa [List.append_nil] at this
  have hframe : consList (ps ++ [M]) ρb = cons M (consList ps ρb) := by
    rw [consList_append, consList_cons, consList_nil]
  rw [hframe] at hspM
  have hframe' : consList ((ps ++ [M]) ++ ms) ρb = consList ms (cons M (consList ps ρb)) := by
    rw [consList_append, hframe]
  rw [hframe'] at hspI
  refine ⟨ps, M, ms, is, rfl, hlenPs, hlenMs, hlenIs, hρp, hM, ?_, ?_⟩
  · -- the minors
    intro j hj
    obtain ⟨cd, hcd⟩ : ∃ cd, cds[j]? = some cd := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hmem := FixKI.spineFit_getD_mem' hspM (l := j) (by rw [List.length_map, hlenMD]; exact hj)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, fixMinorsData_getElem?, hcd,
      Option.map_some, Option.getD_some] at hmem
    have hread := hminor (consList ps ρb) hρp j cd hcd M (ms.take j)
      (by rw [List.length_take, hlenMs]; omega)
    rw [hread] at hmem
    exact hmem
  · -- the indices
    rw [spineFit_liftDoms_iff, shiftE_minors hlenMs] at hspI
    exact hspI

/-! ## The premise -/

set_option maxHeartbeats 3200000 in
/-- **The recursor's premise from the readings.** -/
theorem fixPre_of {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {elimL : Level}
    {nP nIdx n ℓ w u s b : Nat} (hℓ : elimL.eval ψ = ℓ)
    (hb : pwBit ψ (Level.zeronessOf elimL) = b) (hbz : ℓ = 0 ↔ b = 0)
    (hs0 : s = 0 ↔ ℓ = 0)
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {cds : List CtorDatumR} (hn : cds.length = n)
    {Fss₀ Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hlenFs : Fss.length = n) (hlenEs : Ess.length = n)
    (hEs : ∀ j, j < n → (Ess.getD j []).length = nIdx)
    (hEisLen : ∀ j i, i ∈ recIdx (rss.getD j []) (Fss.getD j []).length →
      ((Eiss.getD j []).getD i []).length = nIdx)
    (hEbelow : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase)
    (hsingle : w = 0 → ℓ ≠ 0 → n ≤ 1)
    (hprop : w = 0 → ℓ ≠ 0 → ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ j, j < n → ∀ i, i < (Fss.getD j []).length →
      srcOfEs (Ess.getD j []) (Fss.getD j []).length i = none →
      ∀ fs : List V, SpineFit ρp ((Fss.getD j []).take i) fs →
        interp V (consList fs ρp) ((Fss.getD j []).getD i default) ∈ˢ (univZero : V))
    (hTbelow : ∀ j i, DomsBelow (nP + i) ((tlss.getD j []).getD i []))
    (hbelow : DomsBelow 0 (fixRecDataAV m T ψ nP nIdx elimL pps ips cds))
    (okΓ : ∀ i, i < nP + n + nIdx + 2 → ∀ ρ : Nat → V,
      Sat V (((((fixRecDataAV m T ψ nP nIdx elimL pps ips cds).map (·.2.2)).reverse)).drop
        (nP + n + nIdx + 2 - i)) ρ →
      WellDenotedV V ρ (((((fixRecDataAV m T ψ nP nIdx elimL pps ips cds).map (·.2.2)).reverse)).getD
        (nP + n + nIdx + 2 - 1 - i) default))
    (hokTy : ∀ ρ : Nat → V,
      WellDenoted V ρ (mkPisAV (fixRecDataAV m T ψ nP nIdx elimL pps ips cds) (recConcAV n nIdx)))
    (hunivTy : ∀ ρ : Nat → V,
      interp V ρ (mkPisAV (fixRecDataAV m T ψ nP nIdx elimL pps ips cds) (recConcAV n nIdx))
        ∈ˢ (univ s : V))
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
            (minorAVAtR m cd.1 ψ nP cd.2.1 b (1 + j) cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2.2
              cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp M (Ess.getD j []) j fs)
              (ihDomsI ℓ ρp M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
            (Fss.getD j []) ρp [])) :
    FixPre V ℓ w u nP Fss Ess Fss₀ (ips.map (·.2.2)) rss tlss Eiss
      (fixRecDataAV m T ψ nP nIdx elimL pps ips cds) s := by
  have hlenIds : ((ips.map (·.2.2))).length = nIdx := by rw [List.length_map, hlenI]
  generalize hrds : fixRecDataAV m T ψ nP nIdx elimL pps ips cds = rds
    at hbelow okΓ hokTy hunivTy
  have hrdsE : rds = rebit b pps ++ [(0, b, motiveAVI m T ψ nP nIdx elimL ips)] ++
      fixMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (n + 1) 0 ips) ++
      [(0, b, majorAVAt m T ψ nP nIdx n)] := by
    rw [← hrds, fixRecDataAV, hb, hn]
  have hlenR : rds.length = nP + n + nIdx + 2 := by
    rw [← hrds, fixRecDataAV_length hlenP hlenI, hn]
  have hlenMD : (fixMinorsData m ψ nP b cds 1).length = n := by rw [fixMinorsData_length, hn]
  -- the binder data's domains, split
  have hdoms : rds.map (·.2.2)
      = (((pps.map (·.2.2) ++ [motiveAVI m T ψ nP nIdx elimL ips]) ++
          (fixMinorsData m ψ nP b cds 1).map (·.2.2)) ++
          (liftDoms (n + 1) 0 ips).map (·.2.2)) ++ [majorAVAt m T ψ nP nIdx n] := by
    rw [hrdsE]
    simp only [List.map_append, List.map_cons, List.map_nil, rebit_map_dom]
  have hprefix : (rds.take (nP + 1 + n)).map (·.2.2)
      = (pps.map (·.2.2) ++ [motiveAVI m T ψ nP nIdx elimL ips]) ++
          (fixMinorsData m ψ nP b cds 1).map (·.2.2) := by
    have hlenX : (rebit b pps ++ [(0, b, motiveAVI m T ψ nP nIdx elimL ips)] ++
        fixMinorsData m ψ nP b cds 1).length = nP + 1 + n := by
      simp only [List.length_append, rebit_length, hlenP, List.length_singleton, hlenMD]
    generalize hX : rebit b pps ++ [(0, b, motiveAVI m T ψ nP nIdx elimL ips)] ++
        fixMinorsData m ψ nP b cds 1 = X at hrdsE hlenX
    have hlenXD : (X ++ rebit b (liftDoms (n + 1) 0 ips)).length = nP + 1 + n + nIdx := by
      rw [List.length_append, hlenX, rebit_length, liftDoms_length, hlenI]
    rw [hrdsE,
      List.take_append_of_le_length (by omega :
        nP + 1 + n ≤ (X ++ rebit b (liftDoms (n + 1) 0 ips)).length),
      List.take_append_of_le_length (by omega : nP + 1 + n ≤ X.length),
      List.take_of_length_le (by omega : X.length ≤ nP + 1 + n), ← hX]
    simp only [List.map_append, List.map_cons, List.map_nil, rebit_map_dom]
  -- **the K-frame package** at a split
  have hpack : ∀ (ρb : Nat → V) (ps : List V) (M : V) (ms is : List V),
      ps.length = nP → ms.length = n → is.length = nIdx →
      Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) →
      M ∈ˢ interp V (consList ps ρb) (motiveAVI m T ψ nP nIdx elimL ips) →
      (∀ j, j < n → ms.getD j pt ∈ˢ minorSpI ℓ
        (fun fs => ihSpL ℓ (concI w (consList ps ρb) M (Ess.getD j []) j fs)
          (ihDomsI ℓ (consList ps ρb) M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
        (Fss.getD j []) (consList ps ρb) []) →
      SpineFit (consList ps ρb) (ips.map (·.2.2)) is →
      FixKI₀ ℓ w u (consList is (consList ms (cons M (consList ps ρb)))) Fss Ess Fss₀
        (ips.map (·.2.2)) rss tlss Eiss ∧
      interp V (consList is (consList ms (cons M (consList ps ρb)))) (majorAVAt m T ψ nP nIdx n)
        = SetTheory.app (fixFamI u w (consList ps ρb) (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess)
            (tupW u is) := by
    intro ρb ps M ms is _ hlenMs _ hρp hM hms hfit
    obtain ⟨hX, hreal, hfields, hleafT, -⟩ := hframes (consList ps ρb) hρp
    exact fixKFrame_of hℓ hlenP hlenI hlenFs hlenEs hEs hEisLen hρp hX hreal hfields hleafT hM
      hlenMs hms hsingle (fun hw0 hℓ0 => hprop hw0 hℓ0 (consList ps ρb) hρp) hfit
  refine ⟨?_, ?_, ?_, hs0, ?_, ?_, ?_, ?_, ?_, hEbelow, hTbelow⟩
  · -- `hz`
    intro d hd
    rw [← hrds] at hd
    rw [mem_fixRecDataAV hd, hb]
    exact hbz
  · -- `hlen`
    rw [hlenR, hlenFs, hlenIds]; omega
  · -- `hclosed`
    intro k d hk
    have := domsBelow_getElem? hbelow hk
    rwa [Nat.zero_add] at this
  · -- `hdoms`
    intro ρb
    exact domsWalk_of_prefixOk rds [] ρb (Sat_nil V ρb)
      (fun k d hk σ hσ => (prefixOk_of_okΓ hlenR okΓ k d hk σ hσ).1)
  · -- `hK`
    intro ρb as t hsp
    rw [hdoms] at hsp
    obtain ⟨as', ts, heq, hsp', hspT⟩ := spineFit_append_inv hsp
    obtain ⟨t', rfl, ht⟩ := spineFit_singleton hspT
    obtain ⟨rfl, ht'⟩ := List.append_inj' heq rfl
    obtain rfl := List.singleton_inj.mp ht'
    obtain ⟨ps, M, ms, is, rfl, hlenPs, hlenMs, hlenIs, hρp, hM, hms, hfit⟩ := fixSpine_split (T := T) (elimL := elimL) hlenP hlenI hn
      (fun ρp hρp => (hframes ρp hρp).2.2.2.2) ρb as hsp'
    obtain ⟨hK, hmaj⟩ := hpack ρb ps M ms is hlenPs hlenMs hlenIs hρp hM hms hfit
    rw [consList_kframe] at ht ⊢
    refine ⟨hK, ?_⟩
    rw [hmaj] at ht
    have hlenIs' : is.length = (ips.map (·.2.2)).length := by rw [hlenIds]; exact hlenIs
    have hlenMs' : ms.length = Fss.length := by rw [hlenFs]; exact hlenMs
    unfold famK
    rw [kframe_frP hlenIs' hlenMs', kframe_frameIdx hlenIs', hlenIds]
    exact ht
  · -- `hspine`
    intro ρb as hsp vals f hv hf
    rw [hlenFs, hprefix] at hsp
    obtain ⟨c₁, ms, rfl, hsp₂, hspM⟩ := spineFit_append_inv hsp
    obtain ⟨ps, m₁, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₂
    obtain ⟨M, rfl, hM⟩ := spineFit_singleton hspMot
    have hlenPs : ps.length = nP := by rw [hspP.length_eq, List.length_map, hlenP]
    have hlenMs : ms.length = n := by rw [hspM.length_eq, List.length_map, hlenMD]
    have hρp : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
      rwa [List.append_nil] at this
    have hframe' : consList ((ps ++ [M]) ++ ms) ρb = consList ms (cons M (consList ps ρb)) := by
      rw [consList_append, consList_append, consList_cons, consList_nil]
    rw [hlenFs, hframe', shiftE_minors hlenMs] at hv hf
    rw [hdoms]
    refine SpineFit.append (SpineFit.append hsp ?_) ?_
    · rw [hframe', spineFit_liftDoms_iff, shiftE_minors hlenMs]
      exact hv
    · refine ⟨?_, trivial⟩
      rw [consList_append, hframe']
      obtain ⟨hX, -, -, hleafT, -⟩ := hframes (consList ps ρb) hρp
      rw [interp_majorAVAt hlenP hlenI hρp hX hleafT hlenMs hv]
      rw [hlenIds] at hf
      exact hf
  · -- `hconc0`
    intro h0 ρb as' hsp
    rw [hdoms] at hsp
    obtain ⟨as, ts, rfl, hsp', hspT⟩ := spineFit_append_inv hsp
    obtain ⟨t, rfl, ht⟩ := spineFit_singleton hspT
    obtain ⟨ps, M, ms, is, rfl, hlenPs, hlenMs, hlenIs, hρp, hM, hms, hfit⟩ := fixSpine_split (T := T) (elimL := elimL) hlenP hlenI hn
      (fun ρp hρp => (hframes ρp hρp).2.2.2.2) ρb as hsp'
    obtain ⟨hK, -⟩ := hpack ρb ps M ms is hlenPs hlenMs hlenIs hρp hM hms hfit
    have hlenIs' : is.length = (ips.map (·.2.2)).length := by rw [hlenIds]; exact hlenIs
    have hlenMs' : ms.length = Fss.length := by rw [hlenFs]; exact hlenMs
    have h := hK.hyp.toRecHypCore.hM0 h0 t
    unfold frMi at h
    rw [kframe_frameIdx hlenIs', kframe_frM hlenIs' hlenMs'] at h
    rw [consList_append, consList_kframe, consList_cons, consList_nil, hlenFs, hlenIds,
      recConcAV_at is hlenIs t]
    have hMn : consList ms (cons M (consList ps ρb)) n = M := by
      rw [← hlenMs, show ms.length = 0 + ms.length from (Nat.zero_add _).symm, consList_apply_add]
      rfl
    rw [hMn]
    exact h
  · -- `hRecTy`
    intro ρb
    rw [hlenFs, hlenIds]
    exact ⟨hunivTy ρb, hokTy ρb⟩

end ConLeche.Model
