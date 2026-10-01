module

public import ConLeche.Semantics.Tower.FixLeafI
public import ConLeche.Semantics.Tower.SumRecCase

@[expose] public section

/-!
# The recursive family's functor: readings and laws (task #188, indexed)

The X-chain's entries at the **X-frame** `(ρp, X, t, f₀ … f_{i-1})`
(`FixLeafI.lean`): an ordinary entry reads the domain at the parameter
frame below the fields (`interp_chainXI_ord`), a recursive entry
reads `X ⟨e⃗_i⟩` — the family at the tuple of the index expressions'
values (`recSlot_facts`, through the tupler's fold; graded through the
tupler's Π-tower chain, `appChainOk_of_mkPisAV`), and the terminator
reads the index equation against the tuple's projections
(`EqAll_eqsXI`).  On top of these the functor's laws: monotonicity in
the family (`chainXIGo_tele_sub`, `fixStepI_mono`), the closed member
family (the premise's witness, task #202 Stage B: the container
instance at `Type`, the top family at `Prop`), the fixed point
(`fixFamI_app_eq`), and the identification
of the fibre at `⟨ı⃗⟩` with the indexed sum route's restricted tagged
union (`fixFamI_app_eq_sum`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The X-frame kit -/

omit [SetTheory V] in
theorem shiftE_Xframe (ρp : Nat → V) (as : List V) (t X : V) :
    shiftE (as.length + 2) 0 (consList as (cons t (cons X ρp))) = ρp := by
  rw [shiftE_consList_add, show (2 : Nat) = 1 + 1 from rfl, shiftE_succ_cons, shiftE_succ_cons,
    shiftE_zero_zero]

omit [SetTheory V] in
theorem Xframe_X (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) (as.length + 1) = X := by
  have := consList_apply_add as (cons t (cons X ρp)) 1
  rw [Nat.add_comm] at this
  exact this

omit [SetTheory V] in
theorem Xframe_t (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) as.length = t := by
  have := consList_apply_add as (cons t (cons X ρp)) 0
  rw [Nat.zero_add] at this
  exact this

/-- An ordinary entry of the X-chain reads the domain at the parameter
frame under the fields. -/
theorem interp_chainXI_ord {ρp : Nat → V} (F : AnnotTerm) (as : List V) (t X : V) :
    interp V (consList as (cons t (cons X ρp))) (F.liftN 2 as.length)
      = interp V (consList as ρp) F := by
  rw [interp_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl, shiftE_succ_cons,
    shiftE_succ_cons, shiftE_zero_zero]

theorem WellDenoted_chainXI_ord {ρp : Nat → V} (F : AnnotTerm) (as : List V) (t X : V) :
    WellDenoted V (consList as (cons t (cons X ρp))) (F.liftN 2 as.length)
      ↔ WellDenoted V (consList as ρp) F := by
  rw [WellDenoted_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl, shiftE_succ_cons,
    shiftE_succ_cons, shiftE_zero_zero]

/-! ## The recursive slot -/

/-- The application chain along a Π-tower's binder data is graded. -/
theorem appChainOk_of_mkPisAV {m : Nat} {b C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {f : V} {as : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b C ds →
      f ∈ˢ interp V ρ (mkPisAV ds C) → SpineFit ρ (ds.map (·.2.2)) as → AppChainOk f as
  | [], _, _, [], _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, hsp => hsp.elim
  | d :: ds, ρ, f, a :: as, hz, hu, hf, hsp => by
    have hf' : f ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        (fun x => interp V (cons x ρ) (mkPisAV ds C)) := hf
    have hB0 : d.2.1 = 0 → ∀ x, x ∈ˢ interp V ρ d.2.2 →
        interp V (cons x ρ) (mkPisAV ds C) ∈ˢ (univZero : V) := by
      intro h0 x hx
      exact underTowerOk_res_univZero ((hz d (.head _)).mpr h0)
        (fun d' hd' => hz d' (.tail _ hd')) (hu.2 x hx)
    intro l hl
    cases l with
    | zero =>
      refine ⟨d.2.1, interp V ρ d.2.2, fun x => interp V (cons x ρ) (mkPisAV ds C), ?_, ?_, hB0⟩
      · simpa using hf'
      · simpa using hsp.1
    | succ l =>
      have ih := appChainOk_of_mkPisAV (ds := ds) (ρ := cons a ρ) (f := SetTheory.app f a)
        (as := as) (fun d' hd' => hz d' (.tail _ hd')) (hu.2 a hsp.1)
        (app_mem_piR hf' hsp.1 hB0) hsp.2 l (by simpa using hl)
      obtain ⟨v, A, B, h1, h2, h3⟩ := ih
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2

section Slot

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}

/-- The tupler applied to index expressions at the X-frame: its value
(the tuple of the expressions' values) and its grading. -/
theorem tuplerApp_facts (hI : IdxOk u ρp Ids) (as : List V) (t X : V) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V (consList as ρp) E)
    (hsp : SpineFit ρp Ids (Es.map (interp V (consList as ρp)))) :
    interp V (consList as (cons t (cons X ρp)))
        (AnnotTerm.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length)))
      = tupW u (Es.map (interp V (consList as ρp))) ∧
    WellDenoted V (consList as (cons t (cons X ρp)))
      (AnnotTerm.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length))) := by
  have hfv : interp V (consList as (cons t (cons X ρp))) ((tuplerAV u Ids).liftN (as.length + 2) 0)
      = interp V ρp (tuplerAV u Ids) := by
    rw [interp_liftN, shiftE_Xframe]
  have hfok : WellDenoted V (consList as (cons t (cons X ρp))) ((tuplerAV u Ids).liftN (as.length + 2) 0) := by
    rw [WellDenoted_liftN, shiftE_Xframe]; exact tuplerAV_wellDenoted hI
  have hargs : (Es.map (·.liftN 2 as.length)).map (interp V (consList as (cons t (cons X ρp))))
      = Es.map (interp V (consList as ρp)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro E _
    exact interp_chainXI_ord E as t X
  have hargsok : ∀ a ∈ Es.map (·.liftN 2 as.length), WellDenoted V (consList as (cons t (cons X ρp))) a := by
    intro a ha
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
    exact (WellDenoted_chainXI_ord E as t X).mpr (hEok E hE)
  have hchain : AppChainOk (interp V (consList as (cons t (cons X ρp)))
      ((tuplerAV u Ids).liftN (as.length + 2) 0))
      ((Es.map (·.liftN 2 as.length)).map (interp V (consList as (cons t (cons X ρp))))) := by
    rw [hfv, hargs]
    exact appChainOk_of_mkPisAV (ds := tuplerData u Ids) (b := mkTowerGo u Ids)
      (C := (idxTyAV u Ids).liftN Ids.length 0)
      (fun _ hd => by obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd; exact Iff.rfl)
      (tuplerAV_under hI) (tuplerAV_mem hI) (by rw [tuplerData_doms]; exact hsp)
  have h := mkAppN_wellDenoted_of_chain hfok hargsok hchain
  refine ⟨?_, h.1⟩
  rw [h.2, hargs, hfv]
  exact tuplerAV_fold hI hsp

/-- **The recursive slot** `X ⟨e⃗⟩` at the X-frame: its value, its
grading, its bound. -/
theorem recSlot_facts (hI : IdxOk u ρp Ids) {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids))
    (as : List V) (t : V) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V (consList as ρp) E)
    (hsp : SpineFit ρp Ids (Es.map (interp V (consList as ρp)))) :
    interp V (consList as (cons t (cons X ρp)))
        (.app (.bvar (as.length + 1))
          (AnnotTerm.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length))))
      = SetTheory.app X (tupW u (Es.map (interp V (consList as ρp)))) ∧
    WellDenoted V (consList as (cons t (cons X ρp)))
      (.app (.bvar (as.length + 1))
        (AnnotTerm.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length)))) ∧
    SetTheory.app X (tupW u (Es.map (interp V (consList as ρp)))) ∈ˢ (univ w : V) := by
  obtain ⟨htv, htok⟩ := tuplerApp_facts (X := X) (t := t) hI as hEok hsp
  have hXm : X ∈ˢ piR (w + 1) (idxSet u ρp Ids) fun _ => (univ w : V) := hX
  refine ⟨?_, ?_, ?_⟩
  · rw [interp_app, interp_bvar, Xframe_X, htv]
  · rw [WellDenoted_app]
    refine ⟨trivial, htok, w + 1, idxSet u ρp Ids, fun _ => (univ w : V), ?_, ?_,
      fun h => absurd h (Nat.succ_ne_zero w)⟩
    · rw [interp_bvar, Xframe_X]; exact hXm
    · rw [htv]; exact tupW_mem hsp
  · exact app_mem_piR_pos (Nat.succ_ne_zero w) hXm (tupW_mem hsp)

/-! ## The terminator -/

/-- At index level `0` every index value is the point. -/
theorem spineFit_pt_of_bound0 {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs as →
      ∀ l, l < as.length → as.getD l pt = pt
  | [], [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, hsp, _, _ => hsp.elim
  | _ :: _, [], _, hsp, _, _ => hsp.elim
  | F :: Fs, a :: as, hb, hsp, l, hl => by
    cases l with
    | zero =>
      have h0 : interp V ρ F ∈ˢ (univZero : V) := by
        have := hb.1; rwa [univ_zero] at this
      exact eq_pt_of_mem_univZero h0 hsp.1
    | succ l =>
      exact spineFit_pt_of_bound0 (hb.2 a hsp.1) hsp.2 l (by simpa using hl)

/-- The terminator's sides are graded at the X-frame. -/
theorem eqsXI_wellDenoted (hI : IdxOk u ρp Ids) {X t : V} (ht : t ∈ˢ idxSet u ρp Ids) {bs : List V}
    {nF : Nat} (hlen : bs.length = nF) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V (consList bs ρp) E) (hEs : Es.length = Ids.length) :
    EqsOk (consList bs (cons t (cons X ρp))) (eqsXI Ids.length nF Es) := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < Ids.length := List.mem_range.mp hl
  refine ⟨?_, ?_⟩
  · show WellDenoted V _ ((Es.getD l default).liftN 2 nF)
    subst hlen
    exact (WellDenoted_chainXI_ord _ bs t X).mpr (hEok _ (getD_mem_of_lt (by omega)))
  · show WellDenoted V _ (projAV l (.bvar nF))
    subst hlen
    refine projAV_wellDenoted_tower (w := u) (Fs := Ids) (ρ := ρp) (by simp) ?_ hI.2 hl'
    rw [interp_bvar, Xframe_t]
    exact ht

/-- **The terminator's reading**, pointwise: the index expressions'
values equal the tuple's projections (no premise: the sides read off
the frame directly). -/
theorem EqAll_eqsXI_gen {X t : V} {bs : List V} {nF : Nat} (hlen : bs.length = nF)
    {n : Nat} {Es : List AnnotTerm} :
    EqAll (consList bs (cons t (cons X ρp))) (eqsXI n nF Es) ↔
      ∀ l, l < n → interp V (consList bs ρp) (Es.getD l default) = projS l t := by
  have hproj : ∀ l, interp V (consList bs (cons t (cons X ρp))) (projAV l (.bvar nF)) = projS l t := by
    intro l
    subst hlen
    rw [projAV_interp, interp_bvar, Xframe_t]
  unfold EqAll eqsXI
  constructor
  · intro h l hl
    have := h ((Es.getD l default).liftN 2 nF, projAV l (.bvar nF))
      (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
    simp only at this
    subst hlen
    rwa [interp_chainXI_ord, hproj l] at this
  · intro h e he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    simp only
    subst hlen
    rw [interp_chainXI_ord, hproj l]
    exact h l (List.mem_range.mp hl)

/-- The terminator's value does not depend on the family slot. -/
theorem interp_termXI {X Y t : V} {bs : List V} {nF : Nat} (hlen : bs.length = nF)
    {n : Nat} {Es : List AnnotTerm} :
    interp V (consList bs (cons t (cons X ρp))) (idxEqAV (eqsXI n nF Es))
      = interp V (consList bs (cons t (cons Y ρp))) (idxEqAV (eqsXI n nF Es)) := by
  rw [idxEqAV_interp, idxEqAV_interp]
  congr 1
  exact propext ((EqAll_eqsXI_gen hlen).trans (EqAll_eqsXI_gen hlen).symm)

/-- **The terminator's reading** at a tuple: the index expressions'
values are the tuple's components. -/
theorem EqAll_eqsXI (hI : IdxOk u ρp Ids) {X : V} {is : List V} (hsp : SpineFit ρp Ids is)
    {bs : List V} {nF : Nat} (hlen : bs.length = nF) {Es : List AnnotTerm} :
    EqAll (consList bs (cons (tupW u is) (cons X ρp))) (eqsXI Ids.length nF Es) ↔
      ∀ l, l < Ids.length → interp V (consList bs ρp) (Es.getD l default) = is.getD l pt := by
  rw [EqAll_eqsXI_gen hlen]
  have hislen : is.length = Ids.length := hsp.length_eq
  have hproj : ∀ l, l < Ids.length → projS l (tupW u is) = is.getD l pt := by
    intro l hl
    by_cases hu : u = 0
    · subst hu
      rw [tupW_zero, projS_pt, spineFit_pt_of_bound0 hI.2 hsp l (by omega)]
    · rw [tupW_pos hu, projS_mkTower l is (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
  constructor
  · intro h l hl; rw [← hproj l hl]; exact h l hl
  · intro h l hl; rw [hproj l hl]; exact h l hl

/-- The sum route's terminator at the index frame, in the same
pointwise form. -/
theorem EqAll_idxEqsAt' {is : List V} (hislen : is.length = Ids.length) {bs : List V} {nF : Nat}
    (hlen : bs.length = nF) {Es : List AnnotTerm} (hEs : Es.length = Ids.length) :
    EqAll (consList bs (consList is ρp)) (idxEqsAt Ids.length Ids.length nF Es) ↔
      ∀ l, l < Ids.length → interp V (consList bs ρp) (Es.getD l default) = is.getD l pt := by
  rw [EqAll_idxEqsAt hEs hlen]
  have hsh : shiftE Ids.length 0 (consList is ρp) = ρp := by
    rw [← hislen]; exact shiftE_consList is ρp
  have hfr : frameIdx Ids.length (consList is ρp) = is := by
    rw [← hislen]; exact frameIdx_consList' is ρp
  rw [hsh, hfr]
  unfold idxValsAt
  constructor
  · intro h l hl
    have hl' : l < Es.length := by omega
    have := congrArg (fun L => L.getD l pt) h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl',
      Option.map_some, Option.getD_some] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some,
      List.getD_eq_getElem?_getD]
    exact this
  · intro h
    apply List.ext_getElem
    · rw [List.length_map]; omega
    · intro l h1 h2
      rw [List.getElem_map]
      have := h l (by rw [List.length_map] at h1; omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_map] at h1; omega),
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
        Option.getD_some] at this
      exact this

end Slot

/-! ## The functor's laws -/

section Fam

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}

/-- The X-chain entry at position `i` (the head of `chainXIGo` there). -/
def xEntry (u : Nat) (Ids : List AnnotTerm) (rs : List Bool) (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (F : AnnotTerm)
    (i : Nat) : AnnotTerm :=
  if rs.getD i false then slotXI u Ids (tls.getD i []) (Eis.getD i []) i
  else F.liftN 2 i

omit [SetTheory V] in
theorem chainXIGo_cons (rs : List Bool) (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (F : AnnotTerm) (Fs : List AnnotTerm)
    (i : Nat) :
    chainXIGo u Ids rs tls Eis (F :: Fs) i = xEntry u Ids rs tls Eis F i :: chainXIGo u Ids rs tls Eis Fs (i + 1) :=
  rfl

omit [SetTheory V] in
theorem chainXIGo_length (rs : List Bool) (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) :
    ∀ (Fs : List AnnotTerm) (i : Nat), (chainXIGo u Ids rs tls Eis Fs i).length = Fs.length
  | [], _ => rfl
  | _ :: Fs, i => by simp [chainXIGo, chainXIGo_length rs tls Eis Fs (i + 1)]

omit [SetTheory V] in
theorem consList_snoc' (a : V) (as : List V) (ρ : Nat → V) :
    cons a (consList as ρ) = consList (as ++ [a]) ρ := by
  rw [consList_append]; rfl

omit [SetTheory V] in
theorem length_snoc' (a : V) (as : List V) : (as ++ [a]).length = as.length + 1 := by simp

-- `u` (the slot's tuple level) is unused by the fit itself; kept for uniformity
set_option linter.unusedVariables false in
/-- **A recursive slot's fit** at the frame `(ρp, as)`: the field's
telescope graded there with its codomain bits at the family's regime,
and under every fitting telescope spine the index expressions graded
and their values fitting the index telescope.  At a finitary field
(`tl = []`) the spine is empty and this is the old clause. -/
def SlotFit (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) (as : List V) : Prop :=
  FieldsOkB w (consList as ρp) (tl.map (·.2.2)) ∧ (∀ d ∈ tl, (d.2.1 = 0 ↔ w = 0)) ∧
  ∀ bs : List V, SpineFit (consList as ρp) (tl.map (·.2.2)) bs →
    (∀ E ∈ Eis, WellDenoted V (consList (as ++ bs) ρp) E) ∧
    SpineFit ρp Ids (Eis.map (interp V (consList (as ++ bs) ρp)))

/-- **The recursive slot's value** at a family `X`: the nested product
over the field's telescope of the family at the tuple of the index
expressions (task #202); at a finitary field the family at the tuple. -/
noncomputable def slotSet (w u : Nat) (ρ : Nat → V) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) (X : V) : V :=
  piTele w (teleOfFields ρ (tl.map (·.2.2)))
    (fun bs => SetTheory.app X (tupW u (Eis.map (interp V (consList bs ρ))))) []

theorem slotSet_nil (w u : Nat) (ρ : Nat → V) (Eis : List AnnotTerm) (X : V) :
    slotSet w u ρ [] Eis X = SetTheory.app X (tupW u (Eis.map (interp V ρ))) := rfl

omit [SetTheory V] in
theorem liftTele2_cons (i : Nat) (d : Nat × Nat × AnnotTerm) (tl : List (Nat × Nat × AnnotTerm)) :
    liftTele2 i (d :: tl) = (d.1, d.2.1, d.2.2.liftN 2 i) :: liftTele2 (i + 1) tl := by
  unfold liftTele2
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [List.getD_cons_zero, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_def, List.getD_cons_succ]
  rw [show i + (k + 1) = i + 1 + k from by omega]

/-- The lifted telescope reads at the X-frame as the telescope reads
at the parameter frame under the fields. -/
theorem spineFit_liftTele2 {ρp : Nat → V} (t X : V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as bs : List V),
      SpineFit (consList as (cons t (cons X ρp))) ((liftTele2 as.length tl).map (·.2.2)) bs ↔
        SpineFit (consList as ρp) (tl.map (·.2.2)) bs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => by simp [liftTele2_cons, SpineFit]
  | d :: tl, as, b :: bs => by
    rw [liftTele2_cons, List.map_cons, List.map_cons]
    show b ∈ˢ interp V (consList as (cons t (cons X ρp))) (d.2.2.liftN 2 as.length) ∧ _ ↔
      b ∈ˢ interp V (consList as ρp) d.2.2 ∧ _
    rw [interp_chainXI_ord, consList_snoc', consList_snoc']
    have := spineFit_liftTele2 (ρp := ρp) t X tl (as ++ [b]) bs
    rw [length_snoc'] at this
    rw [this]

/-- The nested product over the lifted telescope at the X-frame is the
nested product over the telescope at the parameter frame under the
fields (the body reads the accumulated spine at the latter). -/
theorem piTele_liftTele2 {w : Nat} {ρp : Nat → V} (t X : V) {B : List V → V} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as acc : List V),
      piTele w (teleOfFields (consList as (cons t (cons X ρp))) ((liftTele2 as.length tl).map (·.2.2))) B acc
        = piTele w (teleOfFields (consList as ρp) (tl.map (·.2.2))) B acc
  | [], _, _ => rfl
  | d :: tl, as, acc => by
    rw [liftTele2_cons, List.map_cons, List.map_cons]
    simp only [teleOfFields, piTele]
    rw [interp_chainXI_ord]
    refine piR_congr fun a _ => ?_
    rw [consList_snoc', consList_snoc']
    have := piTele_liftTele2 (w := w) (ρp := ρp) t X (B := B) tl (as ++ [a]) (acc ++ [a])
    rw [length_snoc'] at this
    exact this

/-- `piR` is monotone in its fibres. -/
theorem piR_mono {v : Nat} {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x) :
    piR v A B ⊆ˢ piR v A B' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [piR_zero, piR_zero]
    intro z hz
    obtain ⟨hp, rfl⟩ := mem_truthVal.mp hz
    exact mem_truthVal.mpr ⟨fun x hx => (hp x hx).elim fun y hy => ⟨y, h x hx y hy⟩, rfl⟩
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    intro f hf
    obtain ⟨hg, hB, -, -⟩ := mem_piR_pos hv' hf
    rw [piR_pos hv', ← hg]
    exact graph_mem_piSet fun x hx => h x hx _ (hB x hx)

/-- The nested product is monotone in its body over the fitting
spines. -/
theorem piTele_mono {v : Nat} {B B' : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) ⊆ˢ B' (acc ++ as)) →
      piTele v T B acc ⊆ˢ piTele v T B' acc
  | _, .nil, acc, h => by
    simp only [piTele]
    have := h [] trivial
    simpa using this
  | _, .cons A T, acc, h => by
    simp only [piTele]
    refine piR_mono fun a ha => ?_
    refine piTele_mono fun as has => ?_
    have := h (a :: as) ⟨ha, has⟩
    simpa [List.append_assoc] using this

/-- **The slot's value is monotone** in the family. -/
theorem slotSet_mono {w u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {X Y : V}
    (hXY : FamLe (idxSet u ρp Ids) X Y) {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    {as : List V} (hfit : SlotFit u w ρp Ids tl Eis as) :
    slotSet w u (consList as ρp) tl Eis X ⊆ˢ slotSet w u (consList as ρp) tl Eis Y := by
  unfold slotSet
  refine piTele_mono fun bs hbs => ?_
  simp only [List.nil_append]
  rw [← consList_append]
  exact hXY _ (tupW_mem (hfit.2.2 bs (fitsS_teleOfFields.mp hbs)).2)

/-- **A Π-tower over domains at the family's regime is the nested
product** over the domains' telescope, the body at the accumulated
spine (the P tier's `interp_mkPisAV_piTele`, here for the leaf). -/
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
    show piR d.2.1 (interp V σ d.2.2) (fun x => interp V (cons x σ) (mkPisAV gds R))
      = piR v (interp V σ d.2.2)
          (fun a => piTele v (teleOfFields (cons a σ) (gds.map (·.2.2))) B (acc ++ [a]))
    refine piR_zero_agree (hbits d List.mem_cons_self) fun a ha => ?_
    refine interp_mkPisAV_piTele (R := R) (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_
    intro as hsp
    have := hbase (a :: as) ⟨ha, hsp⟩
    rw [consList_cons] at this
    rw [this, List.append_assoc, List.singleton_append]

/-- A finitary slot's fit is the index expressions' grading and fit at
the frame. -/
theorem SlotFit.fin {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {Eis : List AnnotTerm} {as : List V}
    (h : SlotFit u w ρp Ids [] Eis as) :
    (∀ E ∈ Eis, WellDenoted V (consList as ρp) E) ∧
      SpineFit ρp Ids (Eis.map (interp V (consList as ρp))) := by
  have := h.2.2 [] trivial
  simpa using this

/-- **The recursive slot at the X-frame** reads to its value. -/
theorem slotXI_interp {w u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids) {X : V}
    (as : List V) (t : V)
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} (hfit : SlotFit u w ρp Ids tl Eis as) :
    interp V (consList as (cons t (cons X ρp))) (slotXI u Ids tl Eis as.length)
      = slotSet w u (consList as ρp) tl Eis X := by
  unfold slotXI slotSet
  rw [← piTele_liftTele2 t X tl as []]
  refine interp_mkPisAV_piTele (v := w) ?_ ?_
  · intro d hd
    unfold liftTele2 at hd
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
    have hk' : k < tl.length := List.mem_range.mp hk
    have hmem : tl.getD k default ∈ tl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      exact List.getElem_mem hk'
    show (tl.getD k default).2.1 = 0 ↔ w = 0
    exact hfit.2.1 _ hmem
  · intro bs hbs
    rw [(spineFit_liftTele2 t X tl as bs)] at hbs
    have hlen : bs.length = tl.length := by
      have := hbs.length_eq; simpa using this
    obtain ⟨hEok, hsp⟩ := hfit.2.2 bs hbs
    have hval := (tuplerApp_facts (X := X) (t := t) hI (as ++ bs) hEok hsp).1
    simp only [List.nil_append]
    rw [← consList_append, interp_app, interp_bvar,
      show as.length + 1 + tl.length = (as ++ bs).length + 1 from by simp [hlen]; omega,
      show as.length + 2 + tl.length = (as ++ bs).length + 2 from by simp [hlen]; omega,
      show as.length + tl.length = (as ++ bs).length from by simp [hlen],
      Xframe_X, hval, consList_append]

/-- **The product over a graded, bounded telescope lives in the
universe** its body's values do. -/
theorem piTele_mem_univ {w : Nat} (hw : w ≠ 0) {B : List V → V} :
    ∀ (Fs : List AnnotTerm) {σ : Nat → V} {acc : List V},
      FieldsOkB w σ Fs →
      (∀ as, SpineFit σ Fs as → B (acc ++ as) ∈ˢ (univ w : V)) →
      piTele w (teleOfFields σ Fs) B acc ∈ˢ (univ w : V)
  | [], _, _, _, hB => by simpa [piTele] using hB [] trivial
  | F :: Fs, σ, acc, hF, hB => by
    obtain ⟨-, hbnd, hrest⟩ := hF
    simp only [teleOfFields_cons, piTele]
    have := piR_mem_univ (hbnd hw) fun a ha =>
      piTele_mem_univ hw Fs (acc := acc ++ [a]) (hrest a ha) fun as hsp => by
        have := hB (a :: as) ⟨ha, hsp⟩
        rwa [List.append_assoc, List.singleton_append]
    rwa [if_neg hw, show Nat.max w w = w from Nat.max_self w] at this

/-- **A Π-tower is graded** when its domains are along the telescope
and its body is at every fitting spine. -/
theorem WellDenoted_mkPisAV_of {w : Nat} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      FieldsOkB w σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → WellDenoted V (consList as σ) R) →
      WellDenoted V σ (mkPisAV gds R)
  | [], _, _, hR => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hF, hR => by
    rw [List.map_cons] at hF
    obtain ⟨hok, -, hrest⟩ := hF
    simp only [mkPisAV, WellDenoted_pi]
    refine ⟨hok, fun x hx => ?_⟩
    refine WellDenoted_mkPisAV_of (hrest x hx) fun as hsp => ?_
    have := hR (x :: as) ⟨hx, hsp⟩
    rwa [consList_cons] at this

/-- A telescope graded at the parameter frame under the fields is
graded, lifted, at the X-frame. -/
theorem fieldsOkB_liftTele2 {w : Nat} {ρp : Nat → V} (t X : V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      FieldsOkB w (consList as ρp) (tl.map (·.2.2)) →
      FieldsOkB w (consList as (cons t (cons X ρp))) ((liftTele2 as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    rw [liftTele2_cons, List.map_cons]
    rw [List.map_cons] at hF
    obtain ⟨hok, hbnd, hrest⟩ := hF
    refine ⟨(WellDenoted_chainXI_ord _ as t X).mpr hok,
      fun hw => by rw [interp_chainXI_ord]; exact hbnd hw, fun a ha => ?_⟩
    rw [interp_chainXI_ord] at ha
    rw [consList_snoc']
    have := fieldsOkB_liftTele2 t X tl (as ++ [a]) (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

/-- **The recursive slot is graded at the X-frame**, and its value
lives in the family's universe (task #202: through the field's
telescope). -/
theorem slotXI_wellDenoted {w u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (as : List V) (t : V)
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} (hfit : SlotFit u w ρp Ids tl Eis as) :
    WellDenoted V (consList as (cons t (cons X ρp))) (slotXI u Ids tl Eis as.length) ∧
    (w ≠ 0 → slotSet w u (consList as ρp) tl Eis X ∈ˢ (univ w : V)) := by
  constructor
  · unfold slotXI
    refine WellDenoted_mkPisAV_of (w := w) (fieldsOkB_liftTele2 t X tl as hfit.1) fun bs hsp => ?_
    have hsp' := (spineFit_liftTele2 t X tl as bs).mp hsp
    have hlen : bs.length = tl.length := by rw [hsp'.length_eq, List.length_map]
    obtain ⟨hEok, hspE⟩ := hfit.2.2 bs hsp'
    have h := (recSlot_facts hI hX (as ++ bs) t hEok hspE).2.1
    rw [List.length_append, hlen, consList_append] at h
    rw [show as.length + 1 + tl.length = as.length + tl.length + 1 from by omega,
      show as.length + 2 + tl.length = as.length + tl.length + 2 from by omega]
    exact h
  · intro hw
    unfold slotSet
    refine piTele_mem_univ hw _ hfit.1 fun bs hsp => ?_
    simp only [List.nil_append]
    rw [← consList_append]
    exact (recSlot_facts hI hX (as ++ bs) t (hfit.2.2 bs hsp).1 (hfit.2.2 bs hsp).2).2.2

/-- A finitary slot fits from the index expressions' grading and fit
at the frame (the converse of `SlotFit.fin`). -/
theorem SlotFit.of_fin {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {Eis : List AnnotTerm}
    {as : List V} (hok : ∀ E ∈ Eis, WellDenoted V (consList as ρp) E)
    (hsp : SpineFit ρp Ids (Eis.map (interp V (consList as ρp)))) :
    SlotFit u w ρp Ids [] Eis as := by
  refine ⟨trivial, fun _ h => (List.not_mem_nil h).elim, fun bs hbs => ?_⟩
  cases bs with
  | nil => simpa using And.intro hok hsp
  | cons b bs => exact hbs.elim

/-- **A graded Π-tower's pieces**: at a `Prop`-regime family the
domains are graded along the telescope, and the body is graded at
every fitting spine. -/
theorem WellDenoted_mkPisAV_inv {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV gds R) →
      FieldsOkB 0 σ (gds.map (·.2.2)) ∧
      ∀ as, SpineFit σ (gds.map (·.2.2)) as → WellDenoted V (consList as σ) R
  | [], σ, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [mkPisAV, consList] using h
      | cons a as => exact hsp.elim⟩
  | d :: gds, σ, h => by
    simp only [mkPisAV, WellDenoted_pi] at h
    obtain ⟨hok, hB⟩ := h
    refine ⟨⟨hok, fun h0 => absurd rfl h0, fun x hx => (WellDenoted_mkPisAV_inv (hB x hx)).1⟩,
      fun as hsp => ?_⟩
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons]
      exact (WellDenoted_mkPisAV_inv (hB a ha)).2 as hsp'

omit [SetTheory V] in
/-- A lifted telescope entry carries an original entry's bits. -/
theorem mem_liftTele2 {i : Nat} {tl : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm}
    (hd : d ∈ liftTele2 i tl) : ∃ d' ∈ tl, d.2.1 = d'.2.1 := by
  unfold liftTele2 at hd
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
  have hk' : k < tl.length := List.mem_range.mp hk
  refine ⟨tl.getD k default, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  exact List.getElem_mem hk'

/-- The recursive slots' fit, hereditarily along the X-chain at
`(X, t)`: at each recursive position the slot fits (`SlotFit`). -/
def SlotsFitX (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (X t : V) :
    Nat → List V → List AnnotTerm → Prop
  | _, _, [] => True
  | i, as, F :: Fs =>
    (rs.getD i false = true → SlotFit u w ρp Ids (tls.getD i []) (Eis.getD i []) as) ∧
    ∀ a, a ∈ˢ interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F i) →
      SlotsFitX u w ρp Ids rs tls Eis X t (i + 1) (as ++ [a]) Fs

/-- **The functor's full premise**: the index telescope graded, the
X-chains graded at every family and tuple, the recursive slots
fitting there. -/
structure XChainsOk (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) : Prop where
  hI : IdxOk u ρp Ids
  hok : FixChainsOkI u w ρp Ids Ids.length rss tlss Eiss Fss Ess
  hfit : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
    ∀ j, j < Fss.length →
      SlotsFitX u w ρp Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) X t 0 [] (Fss.getD j [])
  /-- the closure witness: a closed member family (task #202 Stage B:
  supplied by the tower's container instance at `w ≠ 0`,
  `fixFunVI_closed_zero` at a `Prop`-valued block) -/
  hclosed : ∃ L, IsClosedFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) L

theorem lfpFamSpace_eq (w : Nat) (I : V) : lfpFamSpace V w I = famSpace w I :=
  piR_pos (Nat.succ_ne_zero w)

/-- A recursive entry reads the family at the tuple (no membership of
the family needed for the value). -/
theorem xEntry_rec (hI : IdxOk u ρp Ids) {X : V}
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    (F : AnnotTerm) (as : List V) (t : V)
    (hri : rs.getD as.length false = true)
    (hfit : SlotFit u w ρp Ids (tls.getD as.length []) (Eis.getD as.length []) as) :
    interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F as.length)
      = slotSet w u (consList as ρp) (tls.getD as.length []) (Eis.getD as.length []) X := by
  unfold xEntry
  rw [if_pos hri]
  exact slotXI_interp hI as t hfit

/-- An ordinary entry reads the domain. -/
theorem xEntry_ord {X : V} {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} (F : AnnotTerm) (as : List V)
    (t : V) (hri : rs.getD as.length false = false) :
    interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F as.length)
      = interp V (consList as ρp) F := by
  unfold xEntry
  rw [if_neg (by rw [hri]; exact Bool.false_ne_true)]
  exact interp_chainXI_ord F as t X

/-- **Monotonicity of the X-chain telescope** in the family. -/
theorem chainXIGo_tele_sub (hI : IdxOk u ρp Ids) {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (hXY : FamLe (idxSet u ρp Ids) X Y)
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {t : V} {n nF : Nat} {Es : List AnnotTerm} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i →
      SlotsFitX u w ρp Ids rs tls Eis X t i as Fs → as.length + Fs.length = nF →
      TeleS.Sub
        (teleOfFields (consList as (cons t (cons X ρp)))
          (chainXIGo u Ids rs tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
        (teleOfFields (consList as (cons t (cons Y ρp)))
          (chainXIGo u Ids rs tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
  | [], i, as, hi, _, hnF => by
    simp only [chainXIGo, List.nil_append, teleOfFields]
    rw [interp_termXI (X := X) (Y := Y) (by simpa using hnF)]
    exact .cons (Subset.refl _) fun _ _ => .nil
  | F :: Fs, i, as, hi, hfit, hnF => by
    subst hi
    rw [chainXIGo_cons, List.cons_append]
    simp only [teleOfFields]
    refine .cons ?_ fun a ha => ?_
    · by_cases hri : rs.getD as.length false = true
      · rw [xEntry_rec hI (X := X) F as t hri (hfit.1 hri),
          xEntry_rec hI (X := Y) F as t hri (hfit.1 hri)]
        exact slotSet_mono hXY (hfit.1 hri)
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntry_ord F as t hri', xEntry_ord F as t hri']
        exact Subset.refl _
    · rw [consList_snoc', consList_snoc']
      exact chainXIGo_tele_sub hI hX hXY Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
        (hfit.2 a ha) (by simp at hnF ⊢; omega)

/-- The fit predicate restricts along a smaller family. -/
theorem slotsFitX_mono (hI : IdxOk u ρp Ids) {X X' : V} (hX'X : FamLe (idxSet u ρp Ids) X' X)
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {t : V} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i →
      SlotsFitX u w ρp Ids rs tls Eis X t i as Fs → SlotsFitX u w ρp Ids rs tls Eis X' t i as Fs
  | [], _, _, _, _ => trivial
  | F :: Fs, i, as, hi, hfit => by
    subst hi
    refine ⟨hfit.1, fun a ha => ?_⟩
    have ha' : a ∈ˢ interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F as.length) := by
      by_cases hri : rs.getD as.length false = true
      · rw [xEntry_rec hI (X := X') F as t hri (hfit.1 hri)] at ha
        rw [xEntry_rec hI (X := X) F as t hri (hfit.1 hri)]
        exact slotSet_mono hX'X (hfit.1 hri) a ha
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntry_ord F as t hri'] at ha
        rw [xEntry_ord F as t hri']
        exact ha
    exact slotsFitX_mono hI hX'X Fs (as.length + 1) (as ++ [a]) (length_snoc' a as) (hfit.2 a ha')

/-- **The functor is monotone** in the family. -/
theorem fixStepI_mono (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (hXY : FamLe (idxSet u ρp Ids) X Y) {t : V}
    (ht : t ∈ˢ idxSet u ρp Ids) :
    fixStepI u w ρp Ids Ids.length rss tlss Eiss Fss Ess X t
      ⊆ˢ fixStepI u w ρp Ids Ids.length rss tlss Eiss Fss Ess Y t := by
  unfold fixStepI
  refine sumSet_mono fun j => ?_
  unfold sumFibre
  by_cases hj : j < Fss.length
  · rw [chainsXI_getElem?, if_pos hj]
    show towerSet w (teleOfFields (cons t (cons X ρp)) (chainXI u Ids Ids.length (rss.getD j [])
      (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j []))) ⊆ˢ towerSet w (teleOfFields (cons t (cons Y ρp))
      (chainXI u Ids Ids.length (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j [])))
    refine towerSet_mono ?_
    unfold chainXI
    exact chainXIGo_tele_sub h.hI hX hXY (Fss.getD j []) 0 [] rfl (h.hfit X hX t ht j hj) (by simp)
  · rw [chainsXI_getElem?, if_neg hj]
    exact Subset.refl _

theorem famFI_le (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (hXY : FamLe (idxSet u ρp Ids) X Y) :
    FamLe (idxSet u ρp Ids) (famFI u w ρp Ids Ids.length rss tlss Eiss Fss Ess X)
      (famFI u w ρp Ids Ids.length rss tlss Eiss Fss Ess Y) := by
  intro t ht
  rw [famFI_app ht, famFI_app ht]
  exact fixStepI_mono h hX hXY ht

theorem fixFunVI_mono (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) :
    MonoFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) := by
  intro X Y hX hY hXY
  rw [← lfpFamSpace_eq] at hX hY
  rw [fixFunVI_app hX, fixFunVI_app hY]
  exact famFI_le h hX hXY

theorem fixFunVI_maps (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) :
    MapsFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) := by
  intro X hX
  rw [← lfpFamSpace_eq] at hX ⊢
  rw [fixFunVI_app hX]
  exact famFI_mem h.hok hX

/-- **A closed family exists** (the premise's witness). -/
theorem fixFunVI_closed_exists (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) :
    ∃ L, IsClosedFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) L :=
  h.hclosed

/-- **The top family `i ↦ {pt}` is closed at a `Prop`-valued block**
(every fibre at `w = 0` is a subset of `{pt}`). -/
theorem fixFunVI_closed_zero (hok : FixChainsOkI u 0 ρp Ids Ids.length rss tlss Eiss Fss Ess) :
    ∃ L, IsClosedFam 0 (idxSet u ρp Ids) (fixFunVI u 0 ρp Ids Ids.length rss tlss Eiss Fss Ess) L := by
  have htop : graph (fun _ => unitSet) (idxSet u ρp Ids) ∈ˢ lfpFamSpace V 0 (idxSet u ρp Ids) := by
    rw [lfpFamSpace_eq]
    exact graph_mem_famSpace fun _ _ => by rw [univ_zero]; exact mem_univZero.mpr (Subset.refl _)
  refine ⟨graph (fun _ => unitSet) (idxSet u ρp Ids), by rw [← lfpFamSpace_eq]; exact htop, ?_⟩
  rw [fixFunVI_app htop]
  intro t ht x hx
  rw [famFI_app ht] at hx
  rw [app_graph ht]
  have := fixStepI_univ hok htop ht
  rw [univ_zero] at this
  exact mem_univZero.mp this x hx

/-! ## The carrier's laws -/

theorem fixFamI_mem (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) :
    fixFamI u w ρp Ids Ids.length rss tlss Eiss Fss Ess ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) :=
  lfpFamSet_mem_space V w _ _

/-- **The fixed-point equation**, fibrewise: the fibre at `t` is the
functor's fibre at the carrier. -/
theorem fixFamI_app_eq (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) {t : V} (ht : t ∈ˢ idxSet u ρp Ids) :
    fixStepI u w ρp Ids Ids.length rss tlss Eiss Fss Ess (fixFamI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) t
      = SetTheory.app (fixFamI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) t := by
  have := app_lfpFamSet_eq (fixFunVI_closed_exists h) (fixFunVI_mono h) (fixFunVI_maps h) ht
  unfold fixFamI at this ⊢
  rwa [fixFunVI_app (lfpFamSet_mem_space V w _ _), famFI_app ht] at this

/-! ## `FieldsOkB`, pointwise -/

/-- `FieldsOkB` from the per-position facts at every fitting prefix. -/
theorem fieldsOkB_of_pointwise {w : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V},
      (∀ i, i < Fs.length → ∀ as : List V, SpineFit ρ (Fs.take i) as →
        WellDenoted V (consList as ρ) (Fs.getD i default) ∧
        (w ≠ 0 → interp V (consList as ρ) (Fs.getD i default) ∈ˢ (univ w : V))) →
      FieldsOkB w ρ Fs
  | [], _, _ => trivial
  | F :: Fs, ρ, h => by
    have h0 := h 0 (by simp) [] trivial
    simp only [consList_nil, List.getD_cons_zero] at h0
    refine ⟨h0.1, h0.2, fun a ha => fieldsOkB_of_pointwise fun i hi as hsp => ?_⟩
    have := h (i + 1) (by simpa using hi) (a :: as) ⟨ha, hsp⟩
    simpa only [consList_cons, List.getD_cons_succ] using this

/-- The per-position grading of `FieldsOkB`. -/
theorem FieldsOkB.wellDenoted_at {w : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      ∀ i, i < Fs.length → ∀ as : List V, SpineFit ρ (Fs.take i) as →
        WellDenoted V (consList as ρ) (Fs.getD i default)
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | F :: Fs, ρ, h, 0, _, [], _ => h.1
  | _ :: _, _, _, 0, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, _ + 1, _, [], hsp => hsp.elim
  | F :: Fs, ρ, h, i + 1, hi, a :: as, hsp => by
    simp only [consList_cons, List.getD_cons_succ]
    exact FieldsOkB.wellDenoted_at (h.2.2 a hsp.1) i (by simpa using hi) as hsp.2

omit [SetTheory V] in
theorem getD_map_snd {tl : List (Nat × Nat × AnnotTerm)} {k : Nat} (hk : k < tl.length) :
    (tl.map (·.2.2)).getD k default = (tl.getD k default).2.2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk]
  rfl

/-! ## The identification with the real chains -/

/-- `ChainRealI μ … i as Fs₀ Fs`: constructor's real chain `Fs` against
the chain `Fs₀` the functor was spelled from, hereditarily along the
real chain at the frame `(ρp, as)`: at a recursive position the index
expressions are graded and fit, and the real domain reads to the
carrier at their tuple; at an ordinary position the two are the same
term. -/
def ChainRealI (μ : V) (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) :
    Nat → List V → List AnnotTerm → List AnnotTerm → Prop
  | _, _, [], [] => True
  | i, as, F₀ :: Fs₀, F :: Fs =>
    (if rs.getD i false then
      SlotFit u w ρp Ids (tls.getD i []) (Eis.getD i []) as ∧
      interp V (consList as ρp) F = slotSet w u (consList as ρp) (tls.getD i []) (Eis.getD i []) μ
     else F = F₀) ∧
    ∀ a, a ∈ˢ interp V (consList as ρp) F →
      ChainRealI μ u w ρp Ids rs tls Eis (i + 1) (as ++ [a]) Fs₀ Fs
  | _, _, _, _ => False

/-- The lifted real entry reads the domain at the parameter frame. -/
theorem interp_liftIdx (F : AnnotTerm) (as is : List V) (hislen : is.length = Ids.length) :
    interp V (consList as (consList is ρp)) (F.liftN Ids.length as.length)
      = interp V (consList as ρp) F := by
  rw [interp_liftN, shiftE_consList_len, ← hislen, shiftE_consList]

/-- The sigma set depends on its fibres only over the base. -/
theorem sigmaSet_congr' {w : Nat} {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    sigmaSet w A B = sigmaSet w A B' := by
  unfold sigmaSet
  split
  · congr 1
    exact propext ⟨fun ⟨x, hx, y, hy⟩ => ⟨x, hx, y, (h x hx) ▸ hy⟩,
      fun ⟨x, hx, y, hy⟩ => ⟨x, hx, y, (h x hx).symm ▸ hy⟩⟩
  · exact sigmaPairs_congr h

/-- The X-chain tower at the carrier and a tuple is the real
restricted tower at the index spine. -/
theorem towerSet_chainXI_eq (hI : IdxOk u ρp Ids) {μ : V} {is : List V} (hsp : SpineFit ρp Ids is)
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {nF : Nat} {Es : List AnnotTerm}
    (hEs : Es.length = Ids.length) :
    ∀ (Fs₀ Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i →
      ChainRealI μ u w ρp Ids rs tls Eis i as Fs₀ Fs → as.length + Fs.length = nF →
      towerSet w (teleOfFields (consList as (cons (tupW u is) (cons μ ρp)))
          (chainXIGo u Ids rs tls Eis Fs₀ i ++ [idxEqAV (eqsXI Ids.length nF Es)]))
        = towerSet w (teleOfFields (consList as (consList is ρp))
          (liftFields Ids.length i Fs ++ [idxEqAV (idxEqsAt Ids.length Ids.length nF Es)]))
  | [], [], i, as, hi, _, hnF => by
    simp only [chainXIGo, liftFields_nil, List.nil_append, teleOfFields, towerSet]
    have hislen : is.length = Ids.length := hsp.length_eq
    have hlen : as.length = nF := by simpa using hnF
    have h1 : interp V (consList as (cons (tupW u is) (cons μ ρp))) (idxEqAV (eqsXI Ids.length nF Es))
        = interp V (consList as (consList is ρp)) (idxEqAV (idxEqsAt Ids.length Ids.length nF Es)) := by
      rw [idxEqAV_interp, idxEqAV_interp]
      congr 1
      exact propext ((EqAll_eqsXI hI hsp hlen).trans (EqAll_idxEqsAt' hislen hlen hEs).symm)
    rw [h1]
  | [], _ :: _, _, _, _, hc, _ => hc.elim
  | _ :: _, [], _, _, _, hc, _ => hc.elim
  | F₀ :: Fs₀, F :: Fs, i, as, hi, hc, hnF => by
    subst hi
    have hislen : is.length = Ids.length := hsp.length_eq
    rw [chainXIGo_cons, liftFields_cons, List.cons_append, List.cons_append]
    simp only [teleOfFields, towerSet]
    obtain ⟨hhead, htail⟩ := hc
    have hA : interp V (consList as (cons (tupW u is) (cons μ ρp))) (xEntry u Ids rs tls Eis F₀ as.length)
        = interp V (consList as (consList is ρp)) (F.liftN Ids.length as.length) := by
      rw [interp_liftIdx F as is hislen]
      by_cases hri : rs.getD as.length false = true
      · rw [if_pos hri] at hhead
        obtain ⟨hf, heq⟩ := hhead
        rw [xEntry_rec hI F₀ as (tupW u is) hri hf, heq]
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [if_neg (by rw [hri']; exact Bool.false_ne_true)] at hhead
        rw [xEntry_ord F₀ as (tupW u is) hri', hhead]
    rw [hA]
    refine sigmaSet_congr' fun a ha => ?_
    rw [consList_snoc', consList_snoc']
    refine towerSet_chainXI_eq hI hsp hEs Fs₀ Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
      (htail a ?_) (by simp at hnF ⊢; omega)
    rwa [interp_liftIdx F as is hislen] at ha

/-- `ChainsRealI`: `ChainRealI` for every constructor, at the carrier. -/
def ChainsRealI (μ : V) (u w : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (Fss₀ Fss Ess : List (List AnnotTerm)) : Prop :=
  Fss₀.length = Fss.length ∧ Ess.length = Fss.length ∧
  (∀ j, j < Fss.length → (Ess.getD j []).length = Ids.length) ∧
  (∀ j, j < Fss.length → (Fss₀.getD j []).length = (Fss.getD j []).length) ∧
  ∀ j, j < Fss.length →
    ChainRealI μ u w ρp Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) 0 [] (Fss₀.getD j []) (Fss.getD j [])

/-- **The carrier's fibre at an index spine is the indexed sum route's
restricted tagged union** there. -/
theorem fixFamI_app_eq_sum (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess) {Fss' : List (List AnnotTerm)}
    (hreal : ChainsRealI (fixFamI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) u w ρp Ids rss tlss Eiss Fss Fss' Ess)
    {is : List V} (hsp : SpineFit ρp Ids is) :
    SetTheory.app (fixFamI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) (tupW u is)
      = sumSet w (sumFibre w (consList is ρp) (rChains Ids.length Ids.length Fss' Ess)) := by
  rw [← fixFamI_app_eq h (tupW_mem hsp)]
  unfold fixStepI
  refine sumSet_congr fun j => ?_
  obtain ⟨hl₀, hlE, hEs, hlen, hc⟩ := hreal
  unfold sumFibre
  by_cases hj : j < Fss'.length
  · have hjF : j < Fss.length := by omega
    rw [chainsXI_getElem?, if_pos hjF, rChains_getElem?, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (by omega)]
    show towerSet w (teleOfFields (cons (tupW u is) (cons _ ρp)) (chainXI u Ids Ids.length _ _ _ _ _))
      = towerSet w (teleOfFields (consList is ρp) (rChain Ids.length Ids.length Fss'[j] Ess[j]))
    unfold chainXI rChain
    have hg1 : Fss'[j] = Fss'.getD j [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hg2 : Ess[j] = Ess.getD j [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hg1, hg2]
    have := towerSet_chainXI_eq (w := w) (nF := (Fss.getD j []).length) h.hI hsp (hEs j hj)
      (Fss.getD j []) (Fss'.getD j []) 0 [] rfl (hc j hj)
      (by simp only [List.length_nil, Nat.zero_add]; exact (hlen j hj).symm)
    rw [← hlen j hj]
    simpa only [consList_nil] using this
  · have hjF : ¬ j < Fss.length := by omega
    rw [chainsXI_getElem?, if_neg hjF, rChains_getElem?, List.getElem?_eq_none (by omega)]

/-! ## Elimination at a stage -/

/-- The recursive components of a tuple fitting the X-chain at `X` lie
in the slot's value at `X` — the family at their index tuple under the
field's telescope. -/
theorem fitsXI_slot_mem (hI : IdxOk u ρp Ids) {X t : V} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      SlotsFitX u w ρp Ids rs tls Eis X t i as Fs →
      SpineFit (consList as (cons t (cons X ρp))) (chainXIGo u Ids rs tls Eis Fs i) bs →
      ∀ l, l < bs.length → rs.getD (i + l) false = true →
        SlotFit u w ρp Ids (tls.getD (i + l) []) (Eis.getD (i + l) []) (as ++ bs.take l) ∧
        bs.getD l pt ∈ˢ slotSet w u (consList (as ++ bs.take l) ρp) (tls.getD (i + l) [])
          (Eis.getD (i + l) []) X
  | [], _, _, [], _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, h, _, _, _ => h.elim
  | _ :: _, _, _, [], _, _, h, _, _, _ => h.elim
  | F :: Fs, i, as, b :: bs, hi, hfit, h, l, hl, hr => by
    subst hi
    rw [chainXIGo_cons] at h
    obtain ⟨hb, hrest⟩ := h
    cases l with
    | zero =>
      rw [Nat.add_zero] at hr ⊢
      rw [xEntry_rec hI F as t hr (hfit.1 hr)] at hb
      simpa using ⟨hfit.1 hr, hb⟩
    | succ l =>
      rw [consList_snoc'] at hrest
      have := fitsXI_slot_mem hI Fs (as.length + 1) (as ++ [b]) bs (length_snoc' b as) (hfit.2 b hb) hrest l
        (by simpa using hl) (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
      rw [show as.length + 1 + l = as.length + (l + 1) from by omega] at this
      simpa [List.append_assoc] using this

/-- The recursive components of a tuple fitting the X-chain at `X` lie
in `X` at their own index tuples (finitary fields). -/
theorem fitsXI_rec_mem (hI : IdxOk u ρp Ids) {X t : V} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} (hfin : ∀ i, tls.getD i [] = [])
    {Eis : List (List AnnotTerm)} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      SlotsFitX u w ρp Ids rs tls Eis X t i as Fs →
      SpineFit (consList as (cons t (cons X ρp))) (chainXIGo u Ids rs tls Eis Fs i) bs →
      ∀ l, l < bs.length → rs.getD (i + l) false = true →
        bs.getD l pt ∈ˢ SetTheory.app X
          (tupW u ((Eis.getD (i + l) []).map (interp V (consList (as ++ bs.take l) ρp))))
  | [], _, _, [], _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, h, _, _, _ => h.elim
  | _ :: _, _, _, [], _, _, h, _, _, _ => h.elim
  | F :: Fs, i, as, b :: bs, hi, hfit, h, l, hl, hr => by
    subst hi
    rw [chainXIGo_cons] at h
    obtain ⟨hb, hrest⟩ := h
    cases l with
    | zero =>
      rw [Nat.add_zero] at hr
      rw [xEntry_rec hI F as t hr (hfit.1 hr), hfin, slotSet_nil] at hb
      simpa using hb
    | succ l =>
      rw [consList_snoc'] at hrest
      have := fitsXI_rec_mem hI hfin Fs (as.length + 1) (as ++ [b]) bs (length_snoc' b as) (hfit.2 b hb) hrest l
        (by simpa using hl) (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
      rw [show as.length + 1 + l = as.length + (l + 1) from by omega] at this
      simpa [List.append_assoc] using this

/-- A tuple fitting the X-chain at a family below the carrier fits the
real chain. -/
theorem spineFit_real_of_XI (hI : IdxOk u ρp Ids) {μ X t : V} (hXμ : FamLe (idxSet u ρp Ids) X μ)
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (Fs₀ Fs : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      ChainRealI μ u w ρp Ids rs tls Eis i as Fs₀ Fs →
      SlotsFitX u w ρp Ids rs tls Eis X t i as Fs₀ →
      SpineFit (consList as (cons t (cons X ρp))) (chainXIGo u Ids rs tls Eis Fs₀ i) bs →
      SpineFit (consList as ρp) Fs bs
  | [], [], _, _, [], _, _, _, _ => trivial
  | [], [], _, _, _ :: _, _, _, _, h => h.elim
  | [], _ :: _, _, _, _, _, hc, _, _ => hc.elim
  | _ :: _, [], _, _, _, _, hc, _, _ => hc.elim
  | _ :: _, _ :: _, _, _, [], _, _, _, h => h.elim
  | F₀ :: Fs₀, F :: Fs, i, as, b :: bs, hi, hc, hfit, h => by
    subst hi
    rw [chainXIGo_cons] at h
    obtain ⟨hb, hrest⟩ := h
    obtain ⟨hhead, htail⟩ := hc
    have hb' : b ∈ˢ interp V (consList as ρp) F := by
      by_cases hri : rs.getD as.length false = true
      · rw [if_pos hri] at hhead
        obtain ⟨hf, heq⟩ := hhead
        rw [xEntry_rec hI F₀ as t hri hf] at hb
        rw [heq]
        exact slotSet_mono hXμ hf b hb
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [if_neg (by rw [hri']; exact Bool.false_ne_true)] at hhead
        rw [xEntry_ord F₀ as t hri'] at hb
        rw [hhead]
        exact hb
    refine ⟨hb', ?_⟩
    rw [consList_snoc'] at hrest ⊢
    exact spineFit_real_of_XI hI hXμ Fs₀ Fs (as.length + 1) (as ++ [b]) bs (length_snoc' b as)
      (htail b hb') (hfit.2 b hb) hrest

/-- **Stage elimination** (graph regime): a member of the functor's
fibre at `(X, t)` is the injection of a point-terminated tuple fitting
constructor `j`'s X-chain, with the index equation holding. -/
theorem fixStepI_elim {w : Nat} (hw : w ≠ 0) {X t x : V}
    (hx : x ∈ˢ fixStepI u w ρp Ids Ids.length rss tlss Eiss Fss Ess X t) :
    ∃ j fs, x = inj j (mkTower (fs ++ [pt])) ∧ j < Fss.length ∧
      fs.length = (Fss.getD j []).length ∧
      SpineFit (cons t (cons X ρp)) (chainXIGo u Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) 0) fs ∧
      EqAll (consList fs (cons t (cons X ρp))) (eqsXI Ids.length (Fss.getD j []).length (Ess.getD j [])) := by
  unfold fixStepI at hx
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
  unfold sumFibre at ha
  by_cases hj : j < Fss.length
  · rw [chainsXI_getElem?, if_pos hj] at ha
    obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
    unfold chainXI at hfit heta
    obtain ⟨fs, hfs, hsp, hall⟩ := spineFit_append_idxEq.mp hfit
    have hlen : fs.length = (Fss.getD j []).length := by
      have := hsp.length_eq
      rwa [chainXIGo_length] at this
    refine ⟨j, fs, ?_, hj, hlen, hsp, hall⟩
    rw [heta, hfs]
  · rw [chainsXI_getElem?, if_neg hj] at ha
    exact absurd ha (not_mem_empty _)

/-- **Stage elimination** (squash regime). -/
theorem fixStepI_zero_elim {X t x : V}
    (hx : x ∈ˢ fixStepI u 0 ρp Ids Ids.length rss tlss Eiss Fss Ess X t) :
    x = pt ∧ ∃ j fs, j < Fss.length ∧ fs.length = (Fss.getD j []).length ∧
      SpineFit (cons t (cons X ρp)) (chainXIGo u Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) 0) fs ∧
      EqAll (consList fs (cons t (cons X ρp))) (eqsXI Ids.length (Fss.getD j []).length (Ess.getD j [])) := by
  unfold fixStepI at hx
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
  refine ⟨rfl, ?_⟩
  unfold sumFibre at ha
  by_cases hj : j < Fss.length
  · rw [chainsXI_getElem?, if_pos hj] at ha
    obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
    have hfit' := fitsS_teleOfFields.mp hfit
    unfold chainXI at hfit'
    obtain ⟨fs, -, hsp, hall⟩ := spineFit_append_idxEq.mp hfit'
    have hlen : fs.length = (Fss.getD j []).length := by
      have := hsp.length_eq
      rwa [chainXIGo_length] at this
    exact ⟨j, fs, hj, hlen, hsp, hall⟩
  · rw [chainsXI_getElem?, if_neg hj] at ha
    exact absurd ha (not_mem_empty _)

/-- The index values of a fitting tuple's terminator are the tuple's
components. -/
theorem idxValsAt_of_eqsXI (hI : IdxOk u ρp Ids) {X : V} {is : List V} (hsp : SpineFit ρp Ids is)
    {fs : List V} {Es : List AnnotTerm} (hEs : Es.length = Ids.length)
    (hall : EqAll (consList fs (cons (tupW u is) (cons X ρp))) (eqsXI Ids.length fs.length Es)) :
    idxValsAt ρp Es fs = is := by
  have h := (EqAll_eqsXI hI hsp rfl).mp hall
  have hislen : is.length = Ids.length := hsp.length_eq
  unfold idxValsAt
  apply List.ext_getElem
  · rw [List.length_map]; omega
  · intro l h1 h2
    rw [List.getElem_map]
    have := h l (by rw [List.length_map] at h1; omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_map] at h1; omega),
      Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this
    exact this

end Fam

end ConLeche.Semantics
