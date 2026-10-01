module

public import ConLeche.Model.Inductives.FixRecFrames
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The recursive recursor's K-frames, part 2: the package (task #188)

At a K-frame `(p⃗, M, m⃗, ı⃗)` over a parameter frame — the motive in
its reading, the minors in the readings of their (ih-extended) minor
premises, the indices fitting — the recursive route's K-frame
package `FixKI₀` (`ConLeche/Semantics/Tower/FixRecI.lean`) holds and the
major's domain reads to the carrier at the frame's index tuple.  The
minor premise's reading is the ih-extended minor space
(`interp_minorAVAtR`), the sum route's core computation under the ih
tower read (`interp_ihPisAV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The minor premise, read -/

/-- The minor's conclusion — the motive at the constructor's index
readings and the constructor at the block's variables — reads to
`concI` at a fitting field spine over the block (`o` binders: the
motive and the minors before it). -/
theorem interp_minorConcAV {m : EnvModel V env} {ψ : Name → Nat} {C : Name}
    {nP nF w j o : Nat} {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    {ds : List (Nat × Nat × AnnotTerm)} (hlenDs : ds.length = nP + nF) {Es : List AnnotTerm}
    {Fss : List (List AnnotTerm)}
    (hleafC : m.acval C ψ = sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss))
    (hclC : Term.bvarsBelow 0 (m.acval C ψ).erase)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hokB : SumFieldsOkB w ρp Fss)
    (hsatC : Sat V (((ds.take nP).map (·.2.2)).reverse) ρp)
    {as : List V} (hsp : SpineFit ρp ((ds.drop nP).map (·.2.2)) as) :
    interp V (consList as (consList ms (cons M ρp)))
        (AnnotTerm.mkAppN (.bvar (nF + o - 1))
          ((Es.map fun E => E.liftN o nF) ++
            [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)]))
      = concI w ρp M Es j as := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenAs : as.length = nF := by rw [hsp.length_eq, hlenFs]
  have hsh : shiftE o 0 (consList ms (cons M ρp)) = ρp := by
    rw [← hms, shiftE_consList_add ms 1 (cons M ρp), shiftE_succ_cons, shiftE_zero_zero]
  have hMval : consList as (consList ms (cons M ρp)) (nF + o - 1) = M := by
    rw [show nF + o - 1 = (o - 1) + as.length from by omega, consList_apply_add,
      show o - 1 = 0 + ms.length from by omega, consList_apply_add]
    rfl
  have hσ : ∀ k, consList as (consList ms (cons M ρp)) (k + (o + nF)) = ρp k := by
    intro k
    rw [show k + (o + nF) = (k + o) + as.length from by omega, consList_apply_add,
      show k + o = (k + 1) + ms.length from by omega, consList_apply_add]
    rfl
  have hshF : shiftE o nF (consList as (consList ms (cons M ρp))) = consList as ρp := by
    rw [← hlenAs, shiftE_consList_len, hsh]
  have hleafC' : m.acval C ψ
      = sumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) (uChains Fss) := by
    rw [hleafC, List.take_append_drop]
  rw [AnnotTerm.mkAppN_append_one, interp_app, interp_mkAppN, interp_bvar, hMval,
    ← List.foldl_map (f := interp V (consList as (consList ms (cons M ρp)))) (g := SetTheory.app),
    List.map_map]
  have hidxv : Es.map ((interp V (consList as (consList ms (cons M ρp)))) ∘
      fun E => E.liftN o nF) = idxValsAt ρp Es as := by
    unfold idxValsAt
    apply List.map_congr_left
    intro E _
    simp only [Function.comp]
    rw [interp_liftN, hshF]
  rw [hidxv]
  unfold concI
  congr 1
  rw [interp_mkAppN,
    ← List.foldl_map (f := interp V (consList as (consList ms (cons M ρp)))) (g := SetTheory.app),
    List.map_append, show nP + o + nF = nP + (o + nF) from by omega,
    map_paramBvarsAt_interp hσ,
    show fieldBvars nF = (List.range nF).map (fun k => AnnotTerm.bvar (nF - 1 - k)) from rfl,
    map_fieldBvars_interp hlenAs, interp_closed (V := V) hclC _ (fun k => ρp (k + nP)), hleafC']
  have hlenP' : ((((ds.take nP).map (·.2.2)))).length = nP := by simp [hlenDs]
  have hsp₁ := spineFit_of_sat (Δ₀ := []) (Ds := (ds.take nP).map (·.2.2))
    (by rw [List.append_nil]; exact hsatC)
  rw [hlenP'] at hsp₁
  unfold ctorValI
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · rw [hw0, sumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
    rw [sumMkAV_fold hw' hsp₁ (by rw [consList_range_reverse]; exact hsp)
      (by rw [consList_range_reverse]; exact SumFieldsOkB_uChains hokB)
      (by rw [uChains_getElem?, hFsj]; rfl), if_neg hw']

/-- **A recursive minor premise reads to the ih-extended minor space**:
at the frame of the `j` earlier minors over the motive over the
parameter frame. -/
theorem interp_minorAVAtR {m : EnvModel V env} {ψ : Name → Nat} {C : Name}
    {nP nF ℓ w b j : Nat} (hbz : ℓ = 0 ↔ b = 0) {ρp : Nat → V} {M : V} {ms : List V}
    (hlenM : ms.length = j) {ds : List (Nat × Nat × AnnotTerm)} (hlenDs : ds.length = nP + nF)
    {Es : List AnnotTerm} {Fss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hleafC : m.acval C ψ = sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss))
    (hclC : Term.bvarsBelow 0 (m.acval C ψ).erase)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hokB : SumFieldsOkB w ρp Fss)
    (hsatC : Sat V (((ds.take nP).map (·.2.2)).reverse) ρp) :
    interp V (consList ms (cons M ρp))
        (minorAVAtR m C ψ nP nF b (1 + j) ds Es (recIdx (rss.getD j []) nF) (tlss.getD j [])
          (Eiss.getD j []))
      = minorSpI ℓ (fun fs => ihSpL ℓ (concI w ρp M Es j fs)
          (ihDomsI ℓ ρp M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
        ((ds.drop nP).map (·.2.2)) ρp [] := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenFds : ((ds.drop nP)).length = nF := by simp [hlenDs]
  have hsh : shiftE (1 + j) 0 (consList ms (cons M ρp)) = ρp := by
    rw [← hlenM, Nat.add_comm, shiftE_consList_add ms 1 (cons M ρp), shiftE_succ_cons,
      shiftE_zero_zero]
  have har : (Fss.getD j []).length = nF := by
    rw [List.getD_eq_getElem?_getD, hFsj, Option.getD_some, hlenFs]
  unfold minorAVAtR
  refine interp_minorSpI_of_tele
    (by simp only [rebit_length, liftDoms_length, List.length_map]) ?_ ?_ ?_
  · intro d hd
    rw [mem_rebit hd]; exact hbz
  · -- the field domains agree along a fitting chain
    intro j' as hj' hsp
    rw [hlenFs] at hj'
    have hlenAs : as.length = j' := by
      rw [hsp.length_eq, List.length_take, hlenFs]; omega
    rw [rebit_getD _ _ _ (by rw [liftDoms_length]; omega)]
    show interp V (consList as (consList ms (cons M ρp)))
      ((liftDoms (1 + j) 0 (ds.drop nP)).getD j' default).2.2 = _
    obtain ⟨q, hq⟩ : ∃ q, (ds.drop nP)[j']? = some q :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenFds]; exact hj')⟩
    have hsh' : shiftE (1 + j) j' (consList as (consList ms (cons M ρp))) = consList as ρp := by
      rw [← hlenAs, shiftE_consList_len, hsh]
    rw [List.getD_eq_getElem?_getD, liftDoms_getElem?, hq, Option.map_some, Option.getD_some]
    show interp V (consList as (consList ms (cons M ρp))) (q.2.2.liftN (1 + j) (0 + j')) = _
    rw [interp_liftN, Nat.zero_add, hsh', fields_getD (by rw [hlenFds]; exact hj'),
      List.getD_eq_getElem?_getD, hq, Option.getD_some]
  · -- the core: the ih tower over the motive at the index values and
    -- the constructor leaf's fold
    intro as hsp
    have hlenAs : as.length = nF := by rw [hsp.length_eq, hlenFs]
    rw [List.nil_append]
    unfold ihDomsI
    simp only [har]
    refine interp_ihPisAV hbz (by omega) hlenAs (recIdx (rss.getD j []) nF) 0 [] _ rfl
      (fun i hi => (mem_recIdx.mp hi).1) ?_
    intro ihs' hl
    rw [Nat.zero_add] at hl
    rw [interp_liftN, ← hl, shiftE_consList]
    exact interp_minorConcAV (o := 1 + j) (by omega) hlenDs hleafC hclC hFsj hokB hsatC hsp

/-! ## The family at an index spine -/

/-- **The family at an index spine, from the leaf**: at any frame over
the parameter frame, the carrier applied to the parameter variables
and an index spine is the family's fibre at the spine's tuple. -/
theorem fixFamAt_of {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {nP nIdx w u : Nat}
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {Fss₀ Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hX : XChainsOk u w ρp (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess)
    (hleafT : ∀ σ : Nat → V, interp V σ (m.acval T ψ)
      = interp V (fun k => ρp (k + nP))
          (nativeTyAVI u w (pps ++ ips) (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess))
    {as : List V} (hlenAs : as.length = nIdx) (as₀ : List V)
    (hspAs : SpineFit ρp (ips.map (·.2.2)) as) :
    interp V (consList as (consList as₀ ρp))
        (AnnotTerm.mkAppN (m.acval T ψ)
          (paramBvarsAt nP (nP + (as₀.length + nIdx)) ++ fieldBvars nIdx))
      = SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) (tupW u as) := by
  have hlenIds : ((ips.map (·.2.2))).length = nIdx := by rw [List.length_map, hlenI]
  have hlenAll : (pps ++ ips).length = nP + ((ips.map (·.2.2))).length := by
    simp [hlenP, hlenI, hlenIds]
  have hdropAll : ((pps ++ ips).drop nP).map (·.2.2) = ips.map (·.2.2) := by
    rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append]
  have htakeAll : Sat V ((((pps ++ ips).take nP).map (·.2.2)).reverse) ρp := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    exact hsatP
  have hX' : XChainsOk u w ρp (((pps ++ ips).drop nP).map (·.2.2)) rss tlss Eiss Fss₀ Ess := by
    rw [hdropAll]; exact hX
  have hleafT' : ∀ σ : Nat → V, interp V σ (m.acval T ψ)
      = interp V (fun k => ρp (k + nP))
          (nativeTyAVI u w (pps ++ ips) (((pps ++ ips).drop nP).map (·.2.2)) rss tlss Eiss Fss₀ Ess) := by
    rw [hdropAll]; exact hleafT
  have hlenAll' : (pps ++ ips).length = nP + (((pps ++ ips).drop nP).map (·.2.2)).length := by
    rw [hdropAll]; exact hlenAll
  have hfb : (fieldBvars nIdx).map (interp V (consList as (consList as₀ ρp))) = as := by
    show ((List.range nIdx).map fun k => AnnotTerm.bvar (nIdx - 1 - k)).map
      (interp V (consList as (consList as₀ ρp))) = as
    exact map_fieldBvars_interp hlenAs _
  have h := fixLeafApp (Eis := fieldBvars nIdx) (as := as₀ ++ as) hlenAll' hX' htakeAll hleafT'
    (by rw [consList_append, hfb, hdropAll]; exact hspAs)
  rw [consList_append, hfb, hdropAll, hlenIds] at h
  rw [show as₀.length + nIdx = (as₀ ++ as).length from by simp [hlenAs]]
  exact h

/-- **The major's domain at a K-frame** reads to the carrier's fibre at
the frame's index tuple. -/
theorem interp_majorAVAt {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {nP nIdx n w u : Nat}
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {Fss₀ Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hX : XChainsOk u w ρp (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess)
    (hleafT : ∀ σ : Nat → V, interp V σ (m.acval T ψ)
      = interp V (fun k => ρp (k + nP))
          (nativeTyAVI u w (pps ++ ips) (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess))
    {M : V} {ms : List V} (hlenM : ms.length = n) {is : List V}
    (hfit : SpineFit ρp (ips.map (·.2.2)) is) :
    interp V (consList is (consList ms (cons M ρp))) (majorAVAt m T ψ nP nIdx n)
      = SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) (tupW u is) := by
  have hlenIs : is.length = nIdx := by rw [hfit.length_eq, List.length_map, hlenI]
  unfold majorAVAt
  have h := fixFamAt_of hlenP hlenI hsatP hX hleafT hlenIs (M :: ms) hfit
  rw [consList_cons, show (M :: ms).length + nIdx = 1 + n + nIdx from by
    rw [List.length_cons, hlenM]; omega] at h
  rw [show nP + 1 + n + nIdx = nP + (1 + n + nIdx) from by omega]
  exact h

/-- A nested product at a zero elimination level is a truth value. -/
theorem piTele_zero_mem_univZero {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) ∈ˢ (univZero : V)) →
      piTele 0 T B acc ∈ˢ (univZero : V)
  | _, .nil, acc, h => by simpa [piTele] using h [] trivial
  | _, .cons A T, acc, _ => by
    show piR 0 A _ ∈ˢ (univZero : V)
    exact piR_zero_mem_univZero

/-! ## The K-frame package -/

/-- **The K-frame package**: at a K-frame over a parameter frame with
the motive in its reading, the minors in their ih-extended readings and
a fitting index tuple, `FixKI₀` holds and the major's domain reads to
the carrier's fibre at the tuple. -/
theorem fixKFrame_of {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {elimL : Level}
    {nP nIdx n ℓ w u : Nat} (hℓ : elimL.eval ψ = ℓ)
    {pps ips : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {Fss₀ Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hlenFs : Fss.length = n) (hlenEs : Ess.length = n)
    (hEs : ∀ j, j < n → (Ess.getD j []).length = nIdx)
    (hEisLen : ∀ j i, i ∈ recIdx (rss.getD j []) (Fss.getD j []).length →
      ((Eiss.getD j []).getD i []).length = nIdx)
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hX : XChainsOk u w ρp (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess)
    (hreal : ChainsRealI (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) u w ρp
      (ips.map (·.2.2)) rss tlss Eiss Fss₀ Fss Ess)
    (hfields : ∀ j, j < n → FieldsOkB w ρp (Fss.getD j []) ∧
      ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
        (∀ E ∈ Ess.getD j [], WellDenoted V (consList bs ρp) E) ∧
        SpineFit ρp (ips.map (·.2.2)) (idxValsAt ρp (Ess.getD j []) bs))
    (hleafT : ∀ σ : Nat → V, interp V σ (m.acval T ψ)
      = interp V (fun k => ρp (k + nP))
          (nativeTyAVI u w (pps ++ ips) (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess))
    {M : V} (hM : M ∈ˢ interp V ρp (motiveAVI m T ψ nP nIdx elimL ips))
    {ms : List V} (hlenM : ms.length = n)
    (hms : ∀ j, j < n → ms.getD j pt ∈ˢ minorSpI ℓ
      (fun fs => ihSpL ℓ (concI w ρp M (Ess.getD j []) j fs)
        (ihDomsI ℓ ρp M rss tlss Eiss (fun j' => (Fss.getD j' []).length) j fs))
      (Fss.getD j []) ρp [])
    (hsingle : w = 0 → ℓ ≠ 0 → n ≤ 1)
    (hprop : w = 0 → ℓ ≠ 0 → ∀ j, j < n → ∀ i, i < (Fss.getD j []).length →
      srcOfEs (Ess.getD j []) (Fss.getD j []).length i = none →
      ∀ fs : List V, SpineFit ρp ((Fss.getD j []).take i) fs →
        interp V (consList fs ρp) ((Fss.getD j []).getD i default) ∈ˢ (univZero : V))
    {is : List V} (hfit : SpineFit ρp (ips.map (·.2.2)) is) :
    FixKI₀ ℓ w u (consList is (consList ms (cons M ρp))) Fss Ess Fss₀ (ips.map (·.2.2)) rss tlss Eiss ∧
    interp V (consList is (consList ms (cons M ρp))) (majorAVAt m T ψ nP nIdx n)
      = SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) (tupW u is) := by
  have hlenIds : ((ips.map (·.2.2))).length = nIdx := by rw [List.length_map, hlenI]
  have hlenIs : is.length = nIdx := by rw [hfit.length_eq, hlenIds]
  have hlenIs' : is.length = (ips.map (·.2.2)).length := by rw [hlenIds]; exact hlenIs
  have hlenM' : ms.length = Fss.length := by rw [hlenFs]; exact hlenM
  have hfamL : fixFamI u w ρp (ips.map (·.2.2)) (ips.map (·.2.2)).length rss tlss Eiss Fss₀ Ess
      = fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess := by rw [hlenIds]
  -- the K-frame's accessors
  have hfrP := kframe_frP (ρp := ρp) (M := M) (n := n) (nIdx := nIdx) hlenIs hlenM
  have hfrIdx := kframe_frameIdx (ρp := ρp) (M := M) (ms := ms) hlenIs
  have hshK : shiftE (nIdx + n + 1) 0 (consList is (consList ms (cons M ρp))) = ρp := by
    unfold frP at hfrP; exact hfrP
  have hshK' : shiftE ((ips.map (·.2.2)).length + Fss.length + 1) 0
      (consList is (consList ms (cons M ρp))) = ρp := by
    rw [hlenIds, hlenFs]; exact hshK
  -- the motive's value: the nested product over the index telescope
  have hMtele : M ∈ˢ piTele (ℓ + 1) (teleOfFields ρp (ips.map (·.2.2)))
      (fun is' => piR (ℓ + 1)
        (SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) (ips.map (·.2.2)).length rss tlss Eiss Fss₀ Ess)
          (tupW u is'))
        fun _ => (univ ℓ : V)) [] := by
    have hMv := hM
    unfold motiveAVI at hMv
    rw [interp_mkPisAV_piTele (v := ℓ + 1) (gds := rebit (pwBit ψ PropWhen.never) ips)
      (fun d hd => by
        rw [mem_rebit hd]
        exact ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ),
          fun h => absurd h (Nat.succ_ne_zero _)⟩)
      (B := fun is' => piR (ℓ + 1)
        (SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) (ips.map (·.2.2)).length rss tlss Eiss Fss₀ Ess)
          (tupW u is'))
        fun _ => (univ ℓ : V)) ?_, rebit_map_dom] at hMv
    · exact hMv
    intro as hsp
    rw [rebit_map_dom] at hsp
    have hlenAs : as.length = nIdx := by rw [hsp.length_eq, hlenIds]
    rw [interp_pi, hℓ, List.nil_append]
    have h := fixFamAt_of hlenP hlenI hsatP hX hleafT hlenAs [] hsp
    rw [consList_nil, List.length_nil, Nat.zero_add] at h
    rw [h, ← hfamL, piR_congr_bit (v' := ℓ + 1)
      ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ), fun h => absurd h (Nat.succ_ne_zero _)⟩]
    rfl
  -- the carrier's fibre at the tuple is the sum of the real fibres
  have hfibre : SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) (tupW u is)
      = sumSet w (sumFibre w (consList is (consList ms (cons M ρp)))
          (rChains (nIdx + n + 1) nIdx Fss Ess)) := by
    have hreal' : ChainsRealI (fixFamI u w ρp (ips.map (·.2.2)) (ips.map (·.2.2)).length rss tlss Eiss
        Fss₀ Ess) u w ρp (ips.map (·.2.2)) rss tlss Eiss Fss₀ Fss Ess := by
      rw [hfamL]; exact hreal
    have h := fixFamI_app_eq_sum hX hreal' hfit
    rw [hfamL, hlenIds] at h
    rw [h]
    congr 1
    refine sumFibre_rChains_congr (fun j hj => hEs j (by rw [← hlenFs]; exact hj))
      (by rw [hlenEs, hlenFs]) ?_ ?_
    · rw [hshK, ← hlenIs, shiftE_consList]
    · rw [hfrIdx, frameIdx_consList hlenIs]
  -- the core hypotheses
  have hcore : RecHypCore ℓ w (consList is (consList ms (cons M ρp))) Fss Ess (ips.map (·.2.2))
      (fun is' => SetTheory.app
        (fixFamI u w (frP Fss.length (ips.map (·.2.2)).length (consList is (consList ms (cons M ρp))))
          (ips.map (·.2.2)) (ips.map (·.2.2)).length rss tlss Eiss Fss₀ Ess) (tupW u is')) := by
    refine ⟨?_, ?_, by rw [hlenEs, hlenFs], ?_, ?_, ?_⟩
    · -- the restricted chains are graded at the K-frame
      intro Fs' hFs'
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs'
      rw [rChains_getElem?] at hj
      cases hF : Fss[j]? with
      | none => rw [hF] at hj; exact nomatch hj
      | some Fs =>
        cases hE : Ess[j]? with
        | none => rw [hF, hE] at hj; exact nomatch hj
        | some Es =>
          rw [hF, hE] at hj
          obtain rfl := Option.some.inj hj
          have hjn : j < n := by
            have := (List.getElem?_eq_some_iff.mp hF).1; rwa [hlenFs] at this
          have hFD : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hF]; rfl
          have hED : Ess.getD j [] = Es := by rw [List.getD_eq_getElem?_getD, hE]; rfl
          refine FieldsOkB_rChain (by rw [← hED, hlenIds]; exact hEs j hjn) ?_ ?_
          · rw [hshK', ← hFD]; exact (hfields j hjn).1
          · rw [hshK', ← hFD, ← hED]
            intro bs hsp E hE'
            exact ((hfields j hjn).2 bs hsp).1 E hE'
    · intro j hj
      rw [hlenIds]
      exact hEs j (by rw [← hlenFs]; exact hj)
    · rw [kframe_frM hlenIs' hlenM', kframe_frP hlenIs' hlenM']
      exact hMtele
    · rw [kframe_frP hlenIs' hlenM', kframe_frameIdx hlenIs']
      exact hfit
    · rw [kframe_frameIdx hlenIs', kframe_frP hlenIs' hlenM', hlenIds, hlenFs]
      exact hfibre
  refine ⟨⟨⟨hcore, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- the minors in their ih-extended spaces
    intro j hj
    rw [kframe_frMs hlenIs' hlenM' hj, kframe_frP hlenIs' hlenM', kframe_frM hlenIs' hlenM']
    exact hms j (by rw [← hlenFs]; exact hj)
  · -- the ih domains are truth values at a zero elimination level
    intro h0 j fs A hA
    unfold ihDomsI at hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    rw [h0]
    refine piTele_zero_mem_univZero fun as _ => ?_
    rw [List.nil_append]
    have := hcore.hMapp0 h0
      (is' := ((Eiss.getD j []).getD i []).map (interp V (consList as (consList (fs.take i) ρp))))
      (by rw [List.length_map, hlenIds]; exact hEisLen j i hi) (as.foldl SetTheory.app (fs.getD i pt))
    rw [kframe_frM hlenIs' hlenM'] at this
    rw [kframe_frP hlenIs' hlenM', kframe_frM hlenIs' hlenM']
    exact this
  · rw [kframe_frP hlenIs' hlenM']; exact hX
  · rw [kframe_frP hlenIs' hlenM', hfamL]; exact hreal
  · -- the squash regime (task #202 A2): one constructor, its fields a
    -- `Prop` chain, the unsourced fields propositions
    intro hw0 hℓ0
    have hn1 : n ≤ 1 := hsingle hw0 hℓ0
    refine ⟨by rw [hlenFs]; exact hn1, ?_, ?_⟩
    · rw [kframe_frP hlenIs' hlenM']
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · -- no constructor (task #210 Part B): the empty field list
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenFs]; omega)]
        exact trivial
      · have := (hfields 0 hpos).1
        rwa [hw0] at this
    · rw [kframe_frP hlenIs' hlenM']
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · intro j hj
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenFs]; omega)] at hj
        exact absurd hj (Nat.not_lt_zero _)
      · exact hprop hw0 hℓ0 0 hpos
  · exact interp_majorAVAt hlenP hlenI hsatP hX hleafT hlenM hfit

end ConLeche.Model
