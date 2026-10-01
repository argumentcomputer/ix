module

public import ConLeche.Model.Inductives.FixShadow
public import ConLeche.Semantics.Tower.FixFamI
public section

/-!
# The X-chains, graded at every family (task #188)

The functor's premise (`XChainsOk`): at every family `X` over the index
tuples and every tuple `t`, a constructor's X-chain — its ordinary
domains lifted past `X` and `t`, its recursive slots reading `X ⟨e⃗⟩`,
the index-equation terminator — is graded (`FieldsOkB`) and its
recursive slots fit (`SlotsFitX`).  The walk along the chain keeps a
**shadow spine** beside the X-chain's values: the same values at the
ordinary slots and a truth value at the recursive ones, which fits the
shadow fields (`shadowFs`: the ordinary domains, `Sort 0` at the
recursive positions) and hence satisfies the shadow context of
`FixShadowP.lean`, where every entry is graded; the entries, the index
expressions and the terminator mention no recursive slot, so their
grading and value carry from the shadow frame to the X-frame
(`interp_congr_noBVar`, `WellDenoted_congr_noBVar`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Kit -/

/-- The recursive positions as the functor's Bool list. -/
@[expose] def rsOf (ks : List RecFieldKind) : List Bool := ks.map fun k => decide (k = .recursive ∨ k = .reflexive)

omit [SetTheory V] in
theorem rsOf_getD {ks : List RecFieldKind} {i : Nat} (hi : i < ks.length) :
    (rsOf ks).getD i false = decide (ks.getD i .ordinary = .recursive ∨ ks.getD i .ordinary = .reflexive) := by
  simp only [rsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

omit [SetTheory V] in
theorem rsOf_getD_iff {ks : List RecFieldKind} {i : Nat} (hi : i < ks.length) :
    (rsOf ks).getD i false = true ↔
      (ks.getD i .ordinary = .recursive ∨ ks.getD i .ordinary = .reflexive) := by
  rw [rsOf_getD hi, decide_eq_true_eq]

/-- The shadow fields: the ordinary domains, `Sort 0` at the recursive
positions. -/
def shadowFs (nP : Nat) (ks : List RecFieldKind) (nF : Nat) (Fs : List AnnotTerm) : List AnnotTerm :=
  (List.range nF).map fun i => if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default

omit [SetTheory V] in
theorem shadowFs_length {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AnnotTerm} :
    (shadowFs nP ks nF Fs).length = nF := by simp [shadowFs]

omit [SetTheory V] in
theorem shadowFs_getElem? {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AnnotTerm} {i : Nat}
    (hi : i < nF) :
    (shadowFs nP ks nF Fs)[i]?
      = some (if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default) := by
  simp [shadowFs, List.getElem?_map, List.getElem?_range hi]

omit [SetTheory V] in
theorem shadowFs_take_succ {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AnnotTerm} {i : Nat}
    (hi : i < nF) :
    (shadowFs nP ks nF Fs).take (i + 1)
      = (shadowFs nP ks nF Fs).take i ++
          [if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default] := by
  rw [List.take_add_one, shadowFs_getElem? hi]
  rfl

omit [SetTheory V] in
/-- The shadow context below field `i` is the shadow fields below `i`
over the parameters. -/
theorem shadowCtx_drop_fields {nP nF : Nat} {ks : List RecFieldKind}
    {ds : List (Nat × Nat × AnnotTerm)} (hlen : ds.length = nP + nF) {i : Nat} (hi : i ≤ nF) :
    (shadowCtx nP ks (nP + nF) ((ds.map (·.2.2)).reverse)).drop (nP + nF - (nP + i))
      = ((shadowFs nP ks nF ((ds.drop nP).map (·.2.2))).take i).reverse ++
          ((ds.take nP).map (·.2.2)).reverse := by
  have hlenS : ((shadowFs nP ks nF ((ds.drop nP).map (·.2.2))).take i).length = i := by
    rw [List.length_take, shadowFs_length]; omega
  have hlenP : (((ds.take nP).map (·.2.2)).reverse).length = nP := by
    simp [List.length_take, hlen]
  apply List.ext_getElem?
  intro q
  rw [List.getElem?_drop]
  by_cases hq : q < i + nP
  · rw [shadowCtx_getElem? (by omega)]
    by_cases hqi : q < i
    · -- a shadow field entry
      rw [List.getElem?_append_left (by rw [List.length_reverse, hlenS]; exact hqi),
        List.getElem?_reverse (by rw [hlenS]; exact hqi), hlenS,
        List.getElem?_take_of_lt (by omega), shadowFs_getElem? (by omega)]
      congr 1
      have e1 : nP + nF - 1 - (nP + nF - (nP + i) + q) = nP + (i - 1 - q) := by omega
      rw [e1]
      split
      · rfl
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse
          (by simp [hlen]; omega), List.getElem?_map, List.getElem?_map, List.getElem?_drop]
        simp only [List.length_map, hlen]
        rw [show nP + nF - 1 - (nP + nF - (nP + i) + q) = nP + (i - 1 - q) from by omega]
    · -- a parameter entry
      have hq' : q - i < nP := by omega
      have hidx : nP - 1 - (q - i) < ds.length := by omega
      have hlenP' : (((ds.take nP).map (·.2.2))).length = nP := by
        simp [List.length_take, hlen]
      have hR : (((ds.take nP).map (·.2.2)).reverse)[q - i]?
          = some (ds.getD (nP - 1 - (q - i)) default).2.2 := by
        rw [List.getElem?_reverse (by rw [hlenP']; exact hq'), hlenP', List.getElem?_map,
          List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hidx,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        rfl
      have hL : (if recAt nP ks (nP + nF - 1 - (nP + nF - (nP + i) + q)) then AnnotTerm.sort 0
            else ((ds.map (·.2.2)).reverse).getD (nP + nF - (nP + i) + q) default)
          = (ds.getD (nP - 1 - (q - i)) default).2.2 := by
        rw [if_neg, List.getD_eq_getElem?_getD, List.getElem?_reverse (by simp [hlen]; omega)]
        · simp only [List.length_map, hlen, List.getElem?_map]
          rw [show nP + nF - 1 - (nP + nF - (nP + i) + q) = nP - 1 - (q - i) from by omega,
            List.getElem?_eq_getElem hidx, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hidx]
          rfl
        · intro h
          have := h.1
          omega
      rw [hL, List.getElem?_append_right (by rw [List.length_reverse, hlenS]; omega),
        List.length_reverse, hlenS, hR]
  · rw [List.getElem?_eq_none (by rw [shadowCtx_length]; omega),
      List.getElem?_eq_none (by rw [List.length_append, List.length_reverse, hlenS, hlenP]; omega)]

/-- A truth value: the shadow value at the recursive slots. -/
noncomputable def shadowVal : V := truthVal False

theorem shadowVal_mem : (shadowVal : V) ∈ˢ (univ 0 : V) := truthVal_mem_univ False 0

/-- The shadow spine tracks the X-chain's spine off the recursive
slots. -/
@[expose] def ShadowRel (nP : Nat) (ks : List RecFieldKind) (as as' : List V) : Prop :=
  as'.length = as.length ∧
  ∀ l, l < as.length → ¬ recAt nP ks (nP + l) → as'.getD l pt = as.getD l pt

theorem consList_apply_lt' (as : List V) (σ : Nat → V) {k : Nat} (hk : k < as.length) :
    consList as σ k = as.getD (as.length - 1 - k) pt := by
  rw [consList_apply_lt as σ k hk, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-- The two frames agree off the recursive slots. -/
theorem agreeOff_shadow {nP : Nat} {ks : List RecFieldKind} {as as' : List V}
    (h : ShadowRel nP ks as as') (ρp : Nat → V) :
    AgreeOff (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length))
      (consList as ρp) (consList as' ρp) := by
  intro j hj
  by_cases hji : j < as.length
  · rw [consList_apply_lt' as ρp hji, consList_apply_lt' as' ρp (by rw [h.1]; exact hji), h.1]
    have hnr : ¬ recAt nP ks (nP + (as.length - 1 - j)) := by
      intro hr
      apply hj
      exact ⟨nP + (as.length - 1 - j), ⟨hr, by omega⟩, by omega, by omega⟩
    exact (h.2 (as.length - 1 - j) (by omega) hnr).symm
  · have h1 := consList_apply_add as ρp (j - as.length)
    have h2 := consList_apply_add as' ρp (j - as.length)
    rw [show j - as.length + as.length = j from by omega] at h1
    rw [h.1, show j - as.length + as.length = j from by omega] at h2
    rw [h1, h2]

theorem ShadowRel.nil (nP : Nat) (ks : List RecFieldKind) : ShadowRel (V := V) nP ks [] [] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem ShadowRel.snoc {nP : Nat} {ks : List RecFieldKind} {as as' : List V}
    (h : ShadowRel nP ks as as') {a a' : V}
    (ha : ¬ recAt nP ks (nP + as.length) → a' = a) :
    ShadowRel nP ks (as ++ [a]) (as' ++ [a']) := by
  refine ⟨by simp [h.1], fun l hl hr => ?_⟩
  simp only [List.length_append, List.length_singleton] at hl
  by_cases hla : l < as.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hla,
      List.getElem?_append_left (by rw [h.1]; exact hla), ← List.getD_eq_getElem?_getD,
      ← List.getD_eq_getElem?_getD]
    exact h.2 l hla hr
  · have hl' : l = as.length := by omega
    subst hl'
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_refl _),
      List.getElem?_append_right (by rw [h.1]; exact Nat.le_refl _),
      h.1, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    exact ha hr

omit [SetTheory V] in
theorem mem_fvarLeaves_of_getAppArgs : ∀ (e a : Expr), a ∈ e.getAppArgs →
    ∀ l ∈ a.fvarLeaves, l ∈ e.fvarLeaves
  | .app f a', a, ha, l, hl => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.fvarLeaves, List.mem_append]
    rcases ha with ha | rfl
    · exact Or.inl (mem_fvarLeaves_of_getAppArgs f a ha l hl)
    · exact Or.inr hl
  | .bvar _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .fvar _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .sort _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .const _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .lam _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .forallE _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .letE _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .proj _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .lit _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])

/-! ## Carrying a slot's fit off the shadow frame -/

omit [SetTheory V] in
theorem agreeOff_congr {P P' : Nat → Prop} (h : ∀ i, P i ↔ P' i) {σ σ' : Nat → V}
    (ha : AgreeOff P σ σ') : AgreeOff P' σ σ' :=
  fun i hi => ha i (fun hp => hi ((h i).mp hp))

omit [SetTheory V] in
/-- Frames agreeing off the slots of `Q` at depth `d` still agree, one
binder in, off the slots of `Q` at depth `d + 1`. -/
theorem agreeOff_exclP_cons {Q : Nat → Prop} {d : Nat} (hQ : ∀ q, Q q → q < d) {σ σ' : Nat → V}
    (h : AgreeOff (exclP Q d) σ σ') (x : V) :
    AgreeOff (exclP Q (d + 1)) (cons x σ) (cons x σ') :=
  agreeOff_congr (shiftP_exclP Q d hQ) (agreeOff_cons h x)

omit [SetTheory V] in
theorem agreeOff_exclP_consList {Q : Nat → Prop} :
    ∀ (bs : List V) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      AgreeOff (exclP Q (d + bs.length)) (consList bs σ) (consList bs σ')
  | [], _, _, _, _, h => by simpa using h
  | b :: bs, d, hQ, σ, σ', h => by
    rw [consList_cons, consList_cons, List.length_cons,
      show d + (bs.length + 1) = d + 1 + bs.length from by omega]
    exact agreeOff_exclP_consList bs (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
      (agreeOff_exclP_cons hQ h b)

/-- **A graded telescope carried between frames** agreeing off the
slots its domains do not mention. -/
theorem fieldsOkB_congr_exclP {Q : Nat → Prop} {w : Nat} :
    ∀ (Fs : List AnnotTerm) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      (∀ k F, Fs[k]? = some F → NoBVar (exclP Q (d + k)) F) →
      FieldsOkB w σ' Fs → FieldsOkB w σ Fs
  | [], _, _, _, _, _, _, _ => trivial
  | F :: Fs, d, hQ, σ, σ', hag, hnb, hF => by
    obtain ⟨hok, hbnd, hrest⟩ := hF
    have hnb0 : NoBVar (exclP Q d) F := by simpa using hnb 0 F rfl
    have hv : interp V σ F = interp V σ' F := interp_congr_noBVar F hnb0 hag
    refine ⟨(WellDenoted_congr_noBVar F hnb0 hag).mpr hok, fun hw => by rw [hv]; exact hbnd hw,
      fun a ha => ?_⟩
    rw [hv] at ha
    refine fieldsOkB_congr_exclP Fs (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
      (agreeOff_exclP_cons hQ hag a) ?_ (hrest a ha)
    intro k F' hk
    have := hnb (k + 1) F' (by simpa using hk)
    rwa [show d + 1 + k = d + (k + 1) from by omega]

/-- **A spine's fit carried between frames** agreeing off the slots
the telescope does not mention. -/
theorem spineFit_congr_exclP {Q : Nat → Prop} :
    ∀ (Fs : List AnnotTerm) (bs : List V) {d : Nat}, (∀ q, Q q → q < d) → ∀ {σ σ' : Nat → V},
      AgreeOff (exclP Q d) σ σ' →
      (∀ k F, Fs[k]? = some F → NoBVar (exclP Q (d + k)) F) →
      (SpineFit σ Fs bs ↔ SpineFit σ' Fs bs)
  | [], [], _, _, _, _, _, _ => Iff.rfl
  | [], _ :: _, _, _, _, _, _, _ => Iff.rfl
  | _ :: _, [], _, _, _, _, _, _ => Iff.rfl
  | F :: Fs, b :: bs, d, hQ, σ, σ', hag, hnb => by
    have hnb0 : NoBVar (exclP Q d) F := by simpa using hnb 0 F rfl
    show b ∈ˢ interp V σ F ∧ SpineFit (cons b σ) Fs bs ↔
      b ∈ˢ interp V σ' F ∧ SpineFit (cons b σ') Fs bs
    rw [interp_congr_noBVar F hnb0 hag,
      spineFit_congr_exclP Fs bs (fun q hq => Nat.lt_succ_of_lt (hQ q hq))
        (agreeOff_exclP_cons hQ hag b) ?_]
    intro k F' hk
    have := hnb (k + 1) F' (by simpa using hk)
    rwa [show d + 1 + k = d + (k + 1) from by omega]

/-- **A slot's fit carried off the shadow frame** (task #202): the
field's telescope domains and index expressions mention no recursive
slot below the field, so the shadow values there are invisible. -/
theorem slotFit_congr_shadow {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {nP : Nat}
    {ks : List RecFieldKind} {as as' : List V} (hrel : ShadowRel nP ks as as')
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hT : ∀ k d, tl[k]? = some d →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length + k)) d.2.2)
    (hE : ∀ E ∈ Eis,
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length + tl.length)) E)
    (h : SlotFit u w ρp Ids tl Eis as') : SlotFit u w ρp Ids tl Eis as := by
  have hQ : ∀ q, (recAt nP ks q ∧ q < nP + as.length) → q < nP + as.length := fun _ h => h.2
  have hag := agreeOff_shadow hrel ρp
  have hT' : ∀ k F, (tl.map (·.2.2))[k]? = some F →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length + k)) F := by
    intro k F hk
    rw [List.getElem?_map] at hk
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact hT k d hd
  refine ⟨fieldsOkB_congr_exclP _ hQ hag hT' h.1, h.2.1, fun bs hsp => ?_⟩
  have hsp' : SpineFit (consList as' ρp) (tl.map (·.2.2)) bs :=
    (spineFit_congr_exclP _ bs hQ hag hT').mp hsp
  obtain ⟨hok, hfit⟩ := h.2.2 bs hsp'
  have hlen : bs.length = tl.length := by rw [hsp.length_eq, List.length_map]
  have hag' : AgreeOff (exclP (fun q => recAt nP ks q ∧ q < nP + as.length)
      (nP + as.length + tl.length)) (consList (as ++ bs) ρp) (consList (as' ++ bs) ρp) := by
    rw [consList_append, consList_append, ← hlen]
    exact agreeOff_exclP_consList bs hQ hag
  refine ⟨fun E hE' => (WellDenoted_congr_noBVar E (hE E hE') hag').mpr (hok E hE'), ?_⟩
  have hmap : Eis.map (interp V (consList (as ++ bs) ρp))
      = Eis.map (interp V (consList (as' ++ bs) ρp)) :=
    List.map_congr_left fun E hE' => interp_congr_noBVar E (hE E hE') hag'
  rw [hmap]; exact hfit

/-! ## The walk -/

section Walk

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {nP nF : Nat} {ks : List RecFieldKind}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)}
  {Es : List AnnotTerm}

/-- The per-position facts the walk consumes: the entries, index
expressions and residual index readings mention no recursive slot
below them; at every shadow-fitting spine the entry is graded (in the
family's universe when ordinary and the family is not `Prop`), a
recursive entry's index expressions are graded and fit the index
telescope; the residual's index readings are graded at every
shadow-fitting field spine. -/
structure ChainFacts (u w nP nF : Nat) (ρp : Nat → V) (Ids : List AnnotTerm)
    (ks : List RecFieldKind) (tls : List (List (Nat × Nat × AnnotTerm))) (Fs : List AnnotTerm)
    (Eis : List (List AnnotTerm)) (Es : List AnnotTerm) : Prop where
  hks : ks.length = nF
  hFs : Fs.length = nF
  hEs : Es.length = Ids.length
  nb : ∀ i, i < nF →
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) (Fs.getD i default)
  nbT : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ k d, (tls.getD i [])[k]? = some d →
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + k)) d.2.2
  nbE : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ E ∈ Eis.getD i [],
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + (tls.getD i []).length)) E
  nbEs : ∀ E ∈ Es, NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + nF) (nP + nF)) E
  gr : ∀ i, i < nF → ∀ as' : List V, SpineFit ρp ((shadowFs nP ks nF Fs).take i) as' →
    WellDenoted V (consList as' ρp) (Fs.getD i default) ∧
    (¬ recAt nP ks (nP + i) → w ≠ 0 →
      interp V (consList as' ρp) (Fs.getD i default) ∈ˢ (univ w : V)) ∧
    (recAt nP ks (nP + i) → SlotFit u w ρp Ids (tls.getD i []) (Eis.getD i []) as')
  grE : ∀ as' : List V, SpineFit ρp (shadowFs nP ks nF Fs) as' →
    ∀ E ∈ Es, WellDenoted V (consList as' ρp) E

/-- **The walk**: along the X-chain, beside a shadow spine. -/
theorem fixChainWalk (hI : IdxOk u ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hC : ChainFacts u w nP nF ρp Ids ks tls Fs Eis Es) :
    ∀ (m : Nat) (as as' : List V), nF - as.length = m → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs).take as.length) as' →
      FieldsOkB w (consList as (cons t (cons X ρp)))
        (chainXIGo u Ids (rsOf ks) tls Eis (Fs.drop as.length) as.length ++
          [idxEqAV (eqsXI Ids.length nF Es)]) ∧
      SlotsFitX u w ρp Ids (rsOf ks) tls Eis X t as.length as (Fs.drop as.length) := by
  intro m
  induction m with
  | zero =>
    intro as as' hm hle hrel hsp
    have hlen : as.length = nF := by omega
    have hdrop : Fs.drop as.length = [] := by
      rw [List.drop_eq_nil_iff, hC.hFs]; omega
    rw [hdrop]
    simp only [chainXIGo, List.nil_append, SlotsFitX, and_true]
    -- the terminator: the residual's index readings, carried from the
    -- shadow frame
    have hspF : SpineFit ρp (shadowFs nP ks nF Fs) as' := by
      rwa [hlen, List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hsp
    have hag := agreeOff_shadow hrel ρp
    rw [hlen] at hag
    have hEok : ∀ E ∈ Es, WellDenoted V (consList as ρp) E := fun E hE =>
      (WellDenoted_congr_noBVar E (hC.nbEs E hE) hag).mpr (hC.grE as' hspF E hE)
    refine ⟨idxEqAV_wellDenoted (eqsXI_wellDenoted hI ht hlen hEok hC.hEs), fun _ => idxEqAV_mem_univ _ _ _,
      fun _ _ => trivial⟩
  | succ m ih =>
    intro as as' hm hle hrel hsp
    have hi : as.length < nF := by omega
    have hdrop : Fs.drop as.length = Fs.getD as.length default :: Fs.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hC.hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hC.hFs]; exact hi)]
      rfl
    rw [hdrop, chainXIGo_cons, List.cons_append]
    have hag := agreeOff_shadow hrel ρp
    obtain ⟨hok', hbnd', hrec'⟩ := hC.gr as.length hi as' hsp
    have hFnb := hC.nb as.length hi
    -- the entry's grading and value, carried from the shadow frame
    have hokF : WellDenoted V (consList as ρp) (Fs.getD as.length default) :=
      (WellDenoted_congr_noBVar _ hFnb hag).mpr hok'
    have hvF : interp V (consList as ρp) (Fs.getD as.length default)
        = interp V (consList as' ρp) (Fs.getD as.length default) :=
      interp_congr_noBVar _ hFnb hag
    -- the recursion at an extended spine
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AnnotTerm.sort 0 else Fs.getD as.length default) →
        FieldsOkB w (consList (as ++ [a]) (cons t (cons X ρp)))
          (chainXIGo u Ids (rsOf ks) tls Eis (Fs.drop (as.length + 1)) (as.length + 1) ++
            [idxEqAV (eqsXI Ids.length nF Es)]) ∧
        SlotsFitX u w ρp Ids (rsOf ks) tls Eis X t (as.length + 1) (as ++ [a])
          (Fs.drop (as.length + 1)) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    by_cases hr : recAt nP ks (nP + as.length)
    · -- a recursive slot
      have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      have hfit : SlotFit u w ρp Ids (tls.getD as.length []) (Eis.getD as.length []) as :=
        slotFit_congr_shadow hrel (hC.nbT as.length hi hr) (hC.nbE as.length hi hr) (hrec' hr)
      have hx : xEntry u Ids (rsOf ks) tls Eis (Fs.getD as.length default) as.length
          = slotXI u Ids (tls.getD as.length []) (Eis.getD as.length []) as.length := by
        unfold xEntry; rw [if_pos hrs]
      rw [hx]
      obtain ⟨hokX, huniv⟩ := slotXI_wellDenoted hI hX as t hfit
      have hval := slotXI_interp (X := X) hI as t hfit
      refine ⟨⟨hokX, fun hw => by rw [hval]; exact huniv hw, fun a ha => ?_⟩,
        fun _ => hfit, fun a ha => ?_⟩
      · rw [consList_snoc']
        exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)).1
      · rw [hx] at ha
        exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)).2
    · -- an ordinary entry
      have hrs : (rsOf ks).getD as.length false = false := by
        have := rsOf_getD_iff (ks := ks) (i := as.length) (by rw [hC.hks]; exact hi)
        cases h : (rsOf ks).getD as.length false with
        | false => rfl
        | true =>
          exfalso
          apply hr
          refine ⟨Nat.le_add_right _ _, ?_⟩
          rw [Nat.add_sub_cancel_left]
          exact this.mp h
      have hx : xEntry u Ids (rsOf ks) tls Eis (Fs.getD as.length default) as.length
          = (Fs.getD as.length default).liftN 2 as.length := by
        unfold xEntry; rw [if_neg (by rw [hrs]; exact Bool.false_ne_true)]
      rw [hx]
      have hokL : WellDenoted V (consList as (cons t (cons X ρp)))
          ((Fs.getD as.length default).liftN 2 as.length) :=
        (WellDenoted_chainXI_ord _ as t X).mpr hokF
      have hvL : interp V (consList as (cons t (cons X ρp)))
          ((Fs.getD as.length default).liftN 2 as.length)
          = interp V (consList as' ρp) (Fs.getD as.length default) := by
        rw [interp_chainXI_ord, hvF]
      refine ⟨⟨hokL, fun hw => by rw [hvL]; exact hbnd' hr hw, fun a ha => ?_⟩,
        fun h => absurd h (by rw [hrs]; exact Bool.false_ne_true), fun a ha => ?_⟩
      · rw [consList_snoc']
        rw [hvL] at ha
        exact (hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)).1
      · rw [hx, hvL] at ha
        exact (hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)).2

/-- **The X-chain, graded and fitting**, from the walk at the empty
spine. -/
theorem fixChain_of (hI : IdxOk u ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hC : ChainFacts u w nP nF ρp Ids ks tls Fs Eis Es) :
    FieldsOkB w (cons t (cons X ρp)) (chainXI u Ids Ids.length (rsOf ks) tls Eis Fs Es) ∧
    SlotsFitX u w ρp Ids (rsOf ks) tls Eis X t 0 [] Fs := by
  have h := fixChainWalk hI hX ht hC nF [] [] (by simp) (by simp) (ShadowRel.nil nP ks) trivial
  simp only [List.length_nil, List.drop_zero, consList_nil] at h
  rw [chainXI, hC.hFs]
  exact h

end Walk

/-! ## Kit (the field entries of the reversed context) -/

omit [SetTheory V] in
/-- The reversed context's entry at field `i`. -/
theorem reverse_getD_field {ds : List (Nat × Nat × AnnotTerm)} {nP nF i : Nat}
    (hlen : ds.length = nP + nF) (hi : i < nF) :
    (((ds.map (·.2.2)).reverse).getD (nP + nF - 1 - (nP + i)) default)
      = (((ds.drop nP).map (·.2.2)).getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_reverse (by simp [hlen]; omega)]
  simp only [List.length_map, hlen, List.getElem?_map, List.getElem?_drop]
  rw [show nP + nF - 1 - (nP + nF - 1 - (nP + i)) = nP + i from by omega]

omit [SetTheory V] in
theorem drop_map_getD {ds : List (Nat × Nat × AnnotTerm)} {nP nF i : Nat}
    (hlen : ds.length = nP + nF) (hi : i < nF) :
    (((ds.drop nP).map (·.2.2)).getD i default) = (ds.getD (nP + i) default).2.2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
    List.getElem?_eq_getElem (by omega)]
  rfl

end ConLeche.Model
