import IxC.Resource.Proof.Heap
import IxC.Resource.Proof.EvalS

/-!
# Operational Soundness & Framing Specs (`IxC.Resource.Proof.Ops`)

Soundness and framing theorems for the pure-`M` compound operations of
`IxC.Resource.Eval` and `IxC.Resource.Proof.EvalS`:

1. `bindAt_spec` (`Eval.bindAt`)
2. `ret_spec` (`Eval.ret`)
3. `prim_spec` (`Eval.prim`)
4. `construct_spec` (`Eval.construct`)
5. `makePap_spec` (`Eval.makePap`)
6. `formClosure_spec` (`Eval.formClosure`)
7. `bindParamsM_spec` (`EvalS.bindParamsM`)
8. `select_spec` (`Eval.select`)

Each theorem proves that under the appropriate heap/value invariants (`CapsOk`,
`DeepLive`, `AcyclicFrom`, `OwnTreeFull`, `OpenUnder`), the operation never
returns `.error (.violation _)`, preserves all locations outside the owned
closures of transferred unique values, and establishes the output invariants.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. Shape, Allocation, Taint, and `conform` Helpers -/

/-- `h₂` extends `h₁` while keeping `CellSameShape` on every location present in `h₁`. -/
def OldSameShape (h₁ h₂ : Heap) : Prop :=
  h₁.objs.size ≤ h₂.objs.size ∧
  ∀ (l : Nat) (o₁ : Obj), h₁.objs[l]? = some o₁ →
    ∃ o₂ : Obj, h₂.objs[l]? = some o₂ ∧ CellSameShape o₁.cell o₂.cell

theorem OldSameShape.refl (h : Heap) : OldSameShape h h :=
  ⟨Nat.le_refl _, fun _ o ho => ⟨o, ho, CellSameShape.refl _⟩⟩

theorem OldSameShape.trans {h₁ h₂ h₃ : Heap}
    (h12 : OldSameShape h₁ h₂) (h23 : OldSameShape h₂ h₃) :
    OldSameShape h₁ h₃ := by
  refine ⟨Nat.le_trans h12.1 h23.1, fun l o₁ ho1 => ?_⟩
  obtain ⟨o₂, ho2, hs12⟩ := h12.2 l o₁ ho1
  obtain ⟨o₃, ho3, hs23⟩ := h23.2 l o₂ ho2
  exact ⟨o₃, ho3, hs12.trans hs23⟩

theorem OldSameShape.of_heapSameShape {h₁ h₂ : Heap} (h : HeapSameShape h₁ h₂) :
    OldSameShape h₁ h₂ :=
  ⟨Nat.le_of_eq h.1, fun _ _ ho => h.getElem?_some ho⟩

theorem OldSameShape.of_preserves_old {h₁ h₂ : Heap}
    (hsz : h₁.objs.size ≤ h₂.objs.size)
    (hp : PreservesLocs (fun l => l < h₁.objs.size) h₁ h₂) :
    OldSameShape h₁ h₂ := by
  refine ⟨hsz, fun l o₁ ho1 => ?_⟩
  have hlt : l < h₁.objs.size := (Array.getElem?_eq_some_iff.mp ho1).1
  exact ⟨o₁, (hp l hlt).trans ho1, CellSameShape.refl _⟩

theorem DeepOpenUnder_of_sameShape {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) {rs A : List Nat}
    (hd : DeepOpenUnder h₁ rs A v₁) :
    DeepOpenUnder h₂ rs A v₂ := by
  intro w₂ hw₂
  rcases hw₂ with rfl | ⟨l, o₂, hrl2, ho2, hm2⟩
  · intro r hr hopen
    rw [← hv.taint_eq] at hr
    exact hd.self r hr hopen
  · have hrl1 := (Reach_iff_sameShape hh hv l).mpr hrl2
    obtain ⟨o₁, ho1, hsh⟩ := hh.symm.getElem?_some ho2
    obtain ⟨w₁, hm1, hwsh⟩ := hsh.vals_fwd hm2
    intro r hr hopen
    rw [hwsh.taint_eq] at hr
    exact hd w₁ (Or.inr ⟨l, o₁, hrl1, ho1, hm1⟩) r hr hopen

theorem ClsOk_of_sameShape {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) (hlive : LiveRef h₂ v₂) {c : Cls}
    (hc : ClsOk h₁ c v₁) :
    ClsOk h₂ c v₂ := by
  cases c with
  | irr =>
    subst hc
    cases v₂ with
    | imm i => exact congrArg Val.imm hv.symm
    | ref _ _ _ => exact False.elim hv
  | imm =>
    obtain ⟨i, rfl⟩ := hc
    cases v₂ with
    | imm i₂ => exact ⟨i₂, rfl⟩
    | ref _ _ _ => exact False.elim hv
  | val => trivial
  | leaf =>
    obtain ⟨loc, cap₁, o₁, n, rfl, ho1, hcell1, _⟩ := hc
    cases v₂ with
    | imm _ => exact False.elim hv
    | ref loc₂ cap₂ t₂ =>
      rcases hv with ⟨rfl, ht⟩
      have ht2 : t₂ = [] := ht.symm
      subst ht2
      obtain ⟨o₂, ho2, hcap2⟩ := hlive
      have hsh := hh.2 loc o₁ o₂ ho1 ho2
      rw [hcell1] at hsh
      cases hc2 : o₂.cell with
      | num n₂ =>
        rw [hc2] at hsh
        exact ⟨loc, cap₂, o₂, n₂, rfl, ho2, hc2, hcap2⟩
      | ctor _ _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
        rw [hc2] at hsh; exact False.elim hsh

theorem DeepLive_imm (h : Heap) (i : Imm) : DeepLive h (.imm i) := by
  intro w hw
  rcases hw with rfl | ⟨_, _, hr, _, _⟩
  · exact ⟨trivial, trivial⟩
  · cases hr

theorem AcyclicFrom_imm (h : Heap) (i : Imm) : AcyclicFrom h (.imm i) := by
  intro _ _ _ hr; cases hr

theorem DeepOpenUnder_imm (h : Heap) (rs A : List Nat) (i : Imm) :
    DeepOpenUnder h rs A (.imm i) := by
  intro w hw
  rcases hw with rfl | ⟨_, _, hr, _, _⟩
  · exact OpenUnder.of_nil rfl
  · cases hr

theorem OwnReach_imm_false (P : Prog) (h : Heap) (i : Imm) (l : Nat) :
    ¬ OwnReach P h (.imm i) l := by
  intro hr; cases hr

theorem OwnTreeFull_imm (P : Prog) (h : Heap) (i : Imm) : OwnTreeFull P h (.imm i) := by
  constructor
  · intro _ _ _ _ _ _ _ _ _ _ _ hp; cases hp
  · intro _ _ _ _ _ _ _ hp; cases hp

theorem OwnReach_num_false {P : Prog} {h : Heap} {loc cap : Nat} {t : List Nat}
    {o : Obj} {n : Nat} (ho : h.objs[loc]? = some o) (hc : o.cell = .num n) (l : Nat) :
    ¬ OwnReach P h (.ref loc cap t) l := by
  intro hr
  cases hr with
  | here ho' hnn =>
    rw [ho] at ho'; cases ho'
    rcases hnn with hnn | hnat
    · simp [hc, Cell.isNum] at hnn
    · exact hnat rfl
  | step ho' hi _ _ =>
    rw [ho] at ho'; cases ho'
    simp [hc, ownedSlots] at hi

theorem OwnTreeFull_num {P : Prog} {h : Heap} {loc cap : Nat} {t : List Nat}
    {o : Obj} {n : Nat} (ho : h.objs[loc]? = some o) (hc : o.cell = .num n) :
    OwnTreeFull P h (.ref loc cap t) := by
  constructor
  · intro p₁ _ _ _ _ _ _ _ _ _ _ hp₁
    exact False.elim (OwnReach_num_false ho hc p₁ hp₁)
  · intro p _ _ _ _ _ _ hp
    exact False.elim (OwnReach_num_false ho hc p hp)

theorem Reach_num_iff {h : Heap} {loc cap : Nat} {t : List Nat} {o : Obj} {n : Nat}
    (ho : h.objs[loc]? = some o) (hc : o.cell = .num n) (l : Nat) :
    Reach h (.ref loc cap t) l ↔ l = loc := by
  constructor
  · intro hr
    cases hr with
    | here => rfl
    | step ho' hm _ =>
      rw [ho] at ho'; cases ho'
      rw [hc] at hm; simp [Cell.vals] at hm
  · rintro rfl; exact .here

theorem DeepLive_ref_taint {h : Heap} {loc cap : Nat} {t₁ t₂ : List Nat}
    (hd : DeepLive h (.ref loc cap t₁))
    (hlu : LeafUntainted h (.ref loc cap t₂)) :
    DeepLive h (.ref loc cap t₂) := by
  intro w hw
  rcases HeldBy_ref_taint (t2 := t₁) hw with rfl | hw₁
  · exact ⟨hd.self.1, hlu⟩
  · exact hd w hw₁

theorem AcyclicFrom_ref_taint {h : Heap} {loc cap : Nat} {t₁ t₂ : List Nat}
    (ha : AcyclicFrom h (.ref loc cap t₁)) :
    AcyclicFrom h (.ref loc cap t₂) := by
  intro l o w hrl ho hm
  exact ha l o w (Reach_ref_taint.mp hrl) ho hm

theorem OwnTreeFull_ref_taint {P : Prog} {h : Heap} {loc cap : Nat} {t₁ t₂ : List Nat}
    (ht : OwnTreeFull P h (.ref loc cap t₁)) :
    OwnTreeFull P h (.ref loc cap t₂) := by
  constructor
  · intro p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁' t₂' hp₁ hp₂
    exact ht.1 p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁' t₂'
      (OwnReach_ref_taint.mp hp₁) (OwnReach_ref_taint.mp hp₂)
  · intro p l i o r fs w hp ho hcell hi hs hl
    exact ht.2 p l i o r fs w (OwnReach_ref_taint.mp hp) ho hcell hi hs
      (OwnReach_ref_taint.mp hl)

/-! ### Allocation invariants (`alloc`) -/

theorem HeldBy_alloc_new {h : Heap} {c : Cell} {t : List Nat} {w : Val}
    (hsub : ∀ u ∈ c.vals, DeepLive h u) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    HeldBy h' (.ref h.objs.size h.nextCap t) w →
      w = .ref h.objs.size h.nextCap t ∨ ∃ u ∈ c.vals, HeldBy h u w := by
  intro h' hw
  have hpOld : PreservesLocs (fun x => x < h.objs.size) h h' := by
    intro x hx; simp [h', Array.getElem?_push_lt hx]
  have hoNew : h'.objs[h.objs.size]? = some ⟨c, h.nextCap⟩ := by simp [h']
  rcases hw with rfl | ⟨l, o, hrl, ho, hmem⟩
  · exact Or.inl rfl
  · rcases (Reach_alloc_new (t := t) hsub).mp hrl with rfl | ⟨u, hu, hrul⟩
    · rw [hoNew] at ho; cases ho
      exact Or.inr ⟨w, hmem, HeldBy.refl h w⟩
    · have hlt : l < h.objs.size := Reach_lt_size (hsub u hu) hrul
      have hoOld : h.objs[l]? = some o := (hpOld l hlt).symm.trans ho
      exact Or.inr ⟨u, hu, Or.inr ⟨l, o, hrul, hoOld, hmem⟩⟩

theorem alloc_deepLive {h : Heap} {c : Cell} {t : List Nat}
    (hsub : ∀ u ∈ c.vals, DeepLive h u)
    (hlu : c.isNum = false ∨ t = []) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    DeepLive h' (.ref h.objs.size h.nextCap t) := by
  intro h' w hw
  have hpOld : PreservesLocs (fun x => x < h.objs.size) h h' := by
    intro x hx; simp [h', Array.getElem?_push_lt hx]
  have hoNew : h'.objs[h.objs.size]? = some ⟨c, h.nextCap⟩ := by simp [h']
  rcases HeldBy_alloc_new (t := t) hsub hw with rfl | ⟨u, hu, huw⟩
  · refine ⟨⟨⟨c, h.nextCap⟩, hoNew, rfl⟩, ?_⟩
    intro o n ho hcell
    rw [hoNew] at ho; cases ho
    dsimp only at hcell
    rcases hlu with hnn | rfl
    · rw [hcell] at hnn; simp [Cell.isNum] at hnn
    · rfl
  · have hdw : DeepLive h w := (hsub u hu).sub huw
    have hpw : PreservesLocs (Reach h w) h h' :=
      hpOld.mono (fun x hx => Reach_lt_size hdw hx)
    exact ⟨(LiveRef_congr hpw).mpr hdw.self.1, (LeafUntainted_congr hpw).mpr hdw.self.2⟩

theorem alloc_acyclicFrom {h : Heap} {c : Cell} {t : List Nat}
    (hsub : ∀ u ∈ c.vals, DeepLive h u ∧ AcyclicFrom h u) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    AcyclicFrom h' (.ref h.objs.size h.nextCap t) := by
  intro h' l o w hrl ho hmem hwl
  have hsubDL : ∀ u ∈ c.vals, DeepLive h u := fun u hu => (hsub u hu).1
  have hpOld : PreservesLocs (fun x => x < h.objs.size) h h' := by
    intro x hx; simp [h', Array.getElem?_push_lt hx]
  have hoNew : h'.objs[h.objs.size]? = some ⟨c, h.nextCap⟩ := by simp [h']
  rcases (Reach_alloc_new (t := t) hsubDL).mp hrl with rfl | ⟨u, hu, hrul⟩
  · rw [hoNew] at ho; cases ho
    have hpw : PreservesLocs (Reach h w) h h' :=
      hpOld.mono (fun x hx => Reach_lt_size (hsubDL w hmem) hx)
    have hwlOld : Reach h w h.objs.size := (Reach_congr hpw h.objs.size).mp hwl
    exact Nat.lt_irrefl _ (Reach_lt_size (hsubDL w hmem) hwlOld)
  · have hlt : l < h.objs.size := Reach_lt_size (hsubDL u hu) hrul
    have hoOld : h.objs[l]? = some o := (hpOld l hlt).symm.trans ho
    have hdw : DeepLive h w := (hsubDL u hu).sub (Or.inr ⟨l, o, hrul, hoOld, hmem⟩)
    have hpw : PreservesLocs (Reach h w) h h' :=
      hpOld.mono (fun x hx => Reach_lt_size hdw hx)
    exact (hsub u hu).2 l o w hrul hoOld hmem ((Reach_congr hpw l).mp hwl)

theorem alloc_deepOpenUnder {h : Heap} {c : Cell} {t rs A : List Nat}
    (hsub : ∀ u ∈ c.vals, DeepLive h u ∧ DeepOpenUnder h rs A u)
    (ht : ∀ r ∈ t, r ∈ rs → r ∈ A) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    DeepOpenUnder h' rs A (.ref h.objs.size h.nextCap t) := by
  intro h' w hw
  have hsubDL : ∀ u ∈ c.vals, DeepLive h u := fun u hu => (hsub u hu).1
  rcases HeldBy_alloc_new (t := t) hsubDL hw with rfl | ⟨u, hu, huw⟩
  · exact ht
  · exact (hsub u hu).2 w huw

theorem alloc_ownReach_new {P : Prog} {h : Heap} {c : Cell} {t : List Nat} {l : Nat}
    (hsub : ∀ u ∈ c.vals, DeepLive h u)
    (hnn : c.isNum = false ∨ natClass ≠ .leaf) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    OwnReach P h' (.ref h.objs.size h.nextCap t) l ↔
      l = h.objs.size ∨ ∃ i ∈ ownedSlots P c, ∃ w, c.slot? i = some w ∧ OwnReach P h w l := by
  intro h'
  have hpOld : PreservesLocs (fun x => x < h.objs.size) h h' := by
    intro x hx; simp [h', Array.getElem?_push_lt hx]
  have hoNew : h'.objs[h.objs.size]? = some ⟨c, h.nextCap⟩ := by simp [h']
  constructor
  · intro hr
    cases hr with
    | here => exact Or.inl rfl
    | step ho hi hs hr' =>
      rw [hoNew] at ho; cases ho
      have hm : _ ∈ c.vals := mem_vals_of_ownedSlot hi hs
      have hpw : PreservesLocs (Reach h _) h h' :=
        hpOld.mono (fun x hx => Reach_lt_size (hsub _ hm) hx)
      exact Or.inr ⟨_, hi, _, hs, (OwnReach_congr hpw l).mp hr'⟩
  · rintro (rfl | ⟨i, hi, w, hs, hrw⟩)
    · exact .here hoNew hnn
    · have hm : w ∈ c.vals := mem_vals_of_ownedSlot hi hs
      have hpw : PreservesLocs (Reach h w) h h' :=
        hpOld.mono (fun x hx => Reach_lt_size (hsub w hm) hx)
      exact .step hoNew hi hs ((OwnReach_congr hpw l).mpr hrw)

/-- Generic `OwnTreeFull` for a freshly allocated non-num cell whose owned slots hold
pairwise `OwnReach`/`Reach`-disjoint acyclic `OwnTreeFull` values and (when `.ctor`)
whose non-owned (`@shared`) fields are disjoint from all owned slots' `OwnReach`. -/
theorem alloc_ownTreeFull {P : Prog} {h : Heap} {c : Cell} {t : List Nat}
    (hsub : ∀ u ∈ c.vals, DeepLive h u ∧ AcyclicFrom h u)
    (hnn : c.isNum = false ∨ natClass ≠ .leaf)
    (hown : ∀ i ∈ ownedSlots P c, ∀ w, c.slot? i = some w → OwnTreeFull P h w)
    (hpair : ∀ i j wi wj, i ∈ ownedSlots P c → j ∈ ownedSlots P c → i ≠ j →
      c.slot? i = some wi → c.slot? j = some wj →
      ∀ l, OwnReach P h wi l → ¬ Reach h wj l)
    (hsh : ∀ r fs i wi, c = .ctor r fs → i ∉ ownedSlots P c → fs[i]? = some wi →
      ∀ j ∈ ownedSlots P c, ∀ wj, c.slot? j = some wj →
      ∀ l, OwnReach P h wj l → ¬ Reach h wi l) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    OwnTreeFull P h' (.ref h.objs.size h.nextCap t) := by
  intro h'
  have hsubDL : ∀ u ∈ c.vals, DeepLive h u := fun u hu => (hsub u hu).1
  have hpOld : PreservesLocs (fun x => x < h.objs.size) h h' := by
    intro x hx; simp [h', Array.getElem?_push_lt hx]
  have hoNew : h'.objs[h.objs.size]? = some ⟨c, h.nextCap⟩ := by simp [h']
  have hlt_of_own : ∀ {i w x}, i ∈ ownedSlots P c → c.slot? i = some w →
      OwnReach P h w x → x < h.objs.size := by
    intro i w x hi hs hr
    exact Reach_lt_size (hsubDL w (mem_vals_of_ownedSlot hi hs)) (OwnReach_toReach hr)
  constructor
  · intro p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
    rcases (alloc_ownReach_new (P := P) (t := t) hsubDL hnn).mp hp₁ with
      rfl | ⟨j₁, hj₁, w₁, hsw₁, hr₁⟩
    · rw [hoNew] at ho₁; cases ho₁
      rcases (alloc_ownReach_new (P := P) (t := t) hsubDL hnn).mp hp₂ with
        rfl | ⟨j₂, hj₂, w₂, hsw₂, hr₂⟩
      · rw [hoNew] at ho₂; cases ho₂
        refine ⟨rfl, ?_⟩
        by_cases hij : i₁ = i₂
        · exact hij
        · have hm1 : Val.ref l c₁ t₁ ∈ c.vals := mem_vals_of_ownedSlot hi₁ hs₁
          obtain ⟨oL, hoL, _⟩ := (hsubDL _ hm1).self.1
          have hltL : l < h.objs.size := (Array.getElem?_eq_some_iff.mp hoL).1
          have hnlL : oL.cell.isNum = false ∨ natClass ≠ .leaf := hnl oL ((hpOld l hltL).trans hoL)
          exact False.elim (hpair i₁ i₂ _ _ hi₁ hi₂ hij hs₁ hs₂ l (.here hoL hnlL) .here)
      · have hlt2 : p₂ < h.objs.size := hlt_of_own hj₂ hsw₂ hr₂
        have ho₂Old : h.objs[p₂]? = some o₂ := (hpOld p₂ hlt2).symm.trans ho₂
        have hmw₂ : w₂ ∈ c.vals := mem_vals_of_ownedSlot hj₂ hsw₂
        have hstep₂ : Reach h w₂ l :=
          Reach.step_trans (OwnReach_toReach hr₂) ho₂Old (mem_vals_of_ownedSlot hi₂ hs₂) .here
        have hltL : l < h.objs.size := Reach_lt_size (hsubDL w₂ hmw₂) hstep₂
        have hoL : h.objs[l]? = some h.objs[l] := Array.getElem?_eq_getElem hltL
        have hnlL : h.objs[l].cell.isNum = false ∨ natClass ≠ .leaf :=
          hnl h.objs[l] ((hpOld l hltL).trans hoL)
        by_cases heq : i₁ = j₂
        · subst heq
          rw [hsw₂] at hs₁; cases hs₁
          exact False.elim ((hsub _ hmw₂).2 p₂ o₂ (.ref l c₂ t₂)
            (OwnReach_toReach hr₂) ho₂Old (mem_vals_of_ownedSlot hi₂ hs₂)
            (Reach_ref_taint.mpr (OwnReach_toReach hr₂)))
        · exact False.elim (hpair i₁ j₂ _ w₂ hi₁ hj₂ heq hs₁ hsw₂ l (.here hoL hnlL) hstep₂)
    · have hlt1 : p₁ < h.objs.size := hlt_of_own hj₁ hsw₁ hr₁
      have ho₁Old : h.objs[p₁]? = some o₁ := (hpOld p₁ hlt1).symm.trans ho₁
      have hmw₁ : w₁ ∈ c.vals := mem_vals_of_ownedSlot hj₁ hsw₁
      have hstep₁ : Reach h w₁ l :=
        Reach.step_trans (OwnReach_toReach hr₁) ho₁Old (mem_vals_of_ownedSlot hi₁ hs₁) .here
      have hltL : l < h.objs.size := Reach_lt_size (hsubDL w₁ hmw₁) hstep₁
      have hoL : h.objs[l]? = some h.objs[l] := Array.getElem?_eq_getElem hltL
      have hnlL : h.objs[l].cell.isNum = false ∨ natClass ≠ .leaf :=
        hnl h.objs[l] ((hpOld l hltL).trans hoL)
      rcases (alloc_ownReach_new (P := P) (t := t) hsubDL hnn).mp hp₂ with
        rfl | ⟨j₂, hj₂, w₂, hsw₂, hr₂⟩
      · rw [hoNew] at ho₂; cases ho₂
        by_cases heq : j₁ = i₂
        · subst heq
          rw [hsw₁] at hs₂; cases hs₂
          exact False.elim ((hsub _ hmw₁).2 p₁ o₁ (.ref l c₁ t₁)
            (OwnReach_toReach hr₁) ho₁Old (mem_vals_of_ownedSlot hi₁ hs₁)
            (Reach_ref_taint.mpr (OwnReach_toReach hr₁)))
        · exact False.elim (hpair i₂ j₁ _ w₁ hi₂ hj₁ (Ne.symm heq) hs₂ hsw₁ l
            (.here hoL hnlL) hstep₁)
      · have hlt2 : p₂ < h.objs.size := hlt_of_own hj₂ hsw₂ hr₂
        have ho₂Old : h.objs[p₂]? = some o₂ := (hpOld p₂ hlt2).symm.trans ho₂
        have hstep₂ : Reach h w₂ l :=
          Reach.step_trans (OwnReach_toReach hr₂) ho₂Old (mem_vals_of_ownedSlot hi₂ hs₂) .here
        by_cases heq : j₁ = j₂
        · subst heq
          rw [hsw₁] at hsw₂; cases hsw₂
          have hnlOld : ∀ o, h.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf :=
            fun o ho => hnl o ((hpOld l hltL).trans ho)
          exact (hown j₁ hj₁ w₁ hsw₁).1 p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂
            hr₁ hr₂ ho₁Old ho₂Old hi₁ hi₂ hs₁ hs₂ hnlOld
        · have hown₁ : OwnReach P h w₁ l :=
            OwnReach_step_trans hr₁ ho₁Old hi₁ hs₁ (.here hoL hnlL)
          exact False.elim (hpair j₁ j₂ w₁ w₂ hj₁ hj₂ heq hsw₁ hsw₂ l hown₁ hstep₂)
  · intro p l i o r fs w hrp ho hcell hi hs hrl hwl
    rcases (alloc_ownReach_new (P := P) (t := t) hsubDL hnn).mp hrp with
      rfl | ⟨jp, hjp, wp, hswp, hrpp⟩
    · rw [hoNew] at ho; cases ho
      dsimp only at hcell hi
      have hm : w ∈ c.vals := by
        rw [hcell]; exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs)
      have hpw : PreservesLocs (Reach h w) h h' :=
        hpOld.mono (fun x hx => Reach_lt_size (hsubDL w hm) hx)
      have hwlOld : Reach h w l := (Reach_congr hpw l).mp hwl
      rcases (alloc_ownReach_new (P := P) (t := t) hsubDL hnn).mp hrl with
        rfl | ⟨jl, hjl, wl, hswl, hrll⟩
      · exact Nat.lt_irrefl _ (Reach_lt_size (hsubDL w hm) hwlOld)
      · exact hsh r fs i w hcell hi hs jl hjl wl hswl l hrll hwlOld
    · have hltp : p < h.objs.size := hlt_of_own hjp hswp hrpp
      have hoOld : h.objs[p]? = some o := (hpOld p hltp).symm.trans ho
      have hmw : w ∈ o.cell.vals := by
        rw [hcell]; exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs)
      have hdw : DeepLive h w :=
        (hsubDL wp (mem_vals_of_ownedSlot hjp hswp)).sub
          (Or.inr ⟨p, o, OwnReach_toReach hrpp, hoOld, hmw⟩)
      have hpw : PreservesLocs (Reach h w) h h' :=
        hpOld.mono (fun x hx => Reach_lt_size hdw hx)
      have hwlOld : Reach h w l := (Reach_congr hpw l).mp hwl
      rcases (alloc_ownReach_new (P := P) (t := t) hsubDL hnn).mp hrl with
        rfl | ⟨jl, hjl, wl, hswl, hrll⟩
      · exact Nat.lt_irrefl _ (Reach_lt_size hdw hwlOld)
      · by_cases heq : jp = jl
        · subst heq
          rw [hswp] at hswl; cases hswl
          exact (hown jp hjp wp hswp).2 p l i o r fs w hrpp hoOld hcell hi hs hrll hwlOld
        · have hstepP : Reach h wp l :=
            Reach.step_trans (OwnReach_toReach hrpp) hoOld hmw hwlOld
          exact hpair jl jp wl wp hjl hjp (Ne.symm heq) hswl hswp l hrll hstepP

theorem alloc_ownTreeFull_once {P : Prog} {h : Heap} {v : Val} {t : List Nat}
    (hdl : DeepLive h v) (hacyc : AcyclicFrom h v) (htree : OwnTreeFull P h v) :
    let h' : Heap := { objs := h.objs.push ⟨.once v false, h.nextCap⟩, nextCap := h.nextCap + 1 }
    OwnTreeFull P h' (.ref h.objs.size h.nextCap t) := by
  refine alloc_ownTreeFull (P := P) (c := .once v false) (t := t)
    (fun u hu => by simp [Cell.vals] at hu; subst hu; exact ⟨hdl, hacyc⟩)
    (Or.inl rfl)
    (fun i hi w hs => by
      simp [ownedSlots] at hi; subst hi
      simp [Cell.slot?] at hs; subst hs; exact htree)
    (fun i j _ _ hi hj hne => by
      simp [ownedSlots] at hi hj; subst hi; subst hj; exact absurd rfl hne)
    (fun _ _ _ _ hc => by cases hc)

/-! ### `addTaint` and `renameTaint` preservation -/

theorem DeepLive_addTaint {h : Heap} {s : Nat} {v : Val}
    (hdl : DeepLive h v)
    (hnonLeaf : ∀ loc cap t o n, v = .ref loc cap t → h.objs[loc]? = some o → o.cell = .num n → False) :
    DeepLive h (addTaint s v) := by
  cases v with
  | imm _ => exact hdl
  | ref loc cap t =>
    apply DeepLive_ref_taint hdl
    intro o n ho hc
    exact False.elim (hnonLeaf loc cap t o n rfl ho hc)

theorem AcyclicFrom_addTaint {h : Heap} {s : Nat} {v : Val}
    (ha : AcyclicFrom h v) : AcyclicFrom h (addTaint s v) := by
  cases v with
  | imm _ => exact ha
  | ref loc cap t => exact AcyclicFrom_ref_taint ha

theorem OwnTreeFull_addTaint {P : Prog} {h : Heap} {s : Nat} {v : Val}
    (ht : OwnTreeFull P h v) : OwnTreeFull P h (addTaint s v) := by
  cases v with
  | imm _ => exact ht
  | ref loc cap t => exact OwnTreeFull_ref_taint ht

theorem Reach_addTaint_iff {h : Heap} {s : Nat} {v : Val} (l : Nat) :
    Reach h (addTaint s v) l ↔ Reach h v l := by
  cases v with
  | imm _ => exact Iff.rfl
  | ref _ _ _ => exact Reach_ref_taint

theorem OwnReach_addTaint_iff {P : Prog} {h : Heap} {s : Nat} {v : Val} (l : Nat) :
    OwnReach P h (addTaint s v) l ↔ OwnReach P h v l := by
  cases v with
  | imm _ => exact Iff.rfl
  | ref _ _ _ => exact OwnReach_ref_taint

theorem DeepOpenUnder_addTaint {h : Heap} {rs A : List Nat} {s : Nat} {v : Val}
    (hd : DeepOpenUnder h rs A v) :
    DeepOpenUnder h rs (s :: A) (addTaint s v) := by
  cases v with
  | imm _ => exact hd.mono (fun x hx => List.mem_cons_of_mem s hx)
  | ref loc cap t =>
    intro w hw
    rcases HeldBy_ref_taint (t2 := t) hw with rfl | hwOld
    · intro r hr hopen
      rcases mem_taint_addTaint (s := s) (v := .ref loc cap t) hr with rfl | hrt
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem s (hd.self r hrt hopen)
    · exact (hd w hwOld).mono (fun x hx => List.mem_cons_of_mem s hx)

theorem ClsOk_addTaint {h : Heap} {s : Nat} {c : Cls} {v : Val}
    (hc : ClsOk h c v)
    (hnonLeaf : ∀ loc cap t o n, v = .ref loc cap t → h.objs[loc]? = some o → o.cell = .num n → False) :
    ClsOk h c (addTaint s v) := by
  cases c with
  | irr => subst hc; rfl
  | imm => obtain ⟨i, rfl⟩ := hc; exact ⟨i, rfl⟩
  | val => trivial
  | leaf =>
    obtain ⟨loc, cap, o, n, rfl, ho, hcell, _⟩ := hc
    exact False.elim (hnonLeaf loc cap [] o n rfl ho hcell)

theorem renameTaint_of_taint_nil (s cur : Nat) {v : Val} (ht : v.taint = []) :
    renameTaint s cur v = v := by
  cases v with
  | imm _ => rfl
  | ref loc cap t =>
    simp [Val.taint] at ht
    subst ht
    rfl

theorem DeepLive_renameTaint {h : Heap} {s cur : Nat} {v : Val}
    (hdl : DeepLive h v) : DeepLive h (renameTaint s cur v) := by
  cases v with
  | imm _ => exact hdl
  | ref loc cap t =>
    by_cases ht : t = []
    · subst ht; simpa [renameTaint] using hdl
    · by_cases hcs : t.contains s = true
      · simp only [renameTaint, hcs, ↓reduceIte]
        apply DeepLive_ref_taint hdl
        intro o n ho hc
        exact absurd (hdl.self.2 o n ho hc) ht
      · simp only [renameTaint, hcs]
        exact hdl

theorem AcyclicFrom_renameTaint {h : Heap} {s cur : Nat} {v : Val}
    (ha : AcyclicFrom h v) : AcyclicFrom h (renameTaint s cur v) := by
  cases v with
  | imm _ => exact ha
  | ref loc cap t =>
    dsimp only [renameTaint]
    split
    · exact AcyclicFrom_ref_taint ha
    · exact ha

theorem OwnTreeFull_renameTaint {P : Prog} {h : Heap} {s cur : Nat} {v : Val}
    (ht : OwnTreeFull P h v) : OwnTreeFull P h (renameTaint s cur v) := by
  cases v with
  | imm _ => exact ht
  | ref loc cap t =>
    dsimp only [renameTaint]
    split
    · exact OwnTreeFull_ref_taint ht
    · exact ht

theorem Reach_renameTaint_iff {h : Heap} {s cur : Nat} {v : Val} (l : Nat) :
    Reach h (renameTaint s cur v) l ↔ Reach h v l := by
  cases v with
  | imm _ => exact Iff.rfl
  | ref loc cap t =>
    dsimp only [renameTaint]
    split
    · exact Reach_ref_taint
    · exact Iff.rfl

theorem OwnReach_renameTaint_iff {P : Prog} {h : Heap} {s cur : Nat} {v : Val} (l : Nat) :
    OwnReach P h (renameTaint s cur v) l ↔ OwnReach P h v l := by
  cases v with
  | imm _ => exact Iff.rfl
  | ref loc cap t =>
    dsimp only [renameTaint]
    split
    · exact OwnReach_ref_taint
    · exact Iff.rfl

theorem ClsOk_renameTaint {h : Heap} {s cur : Nat} {c : Cls} {v : Val}
    (hc : ClsOk h c v) : ClsOk h c (renameTaint s cur v) := by
  cases c with
  | irr => subst hc; rfl
  | imm => obtain ⟨i, rfl⟩ := hc; exact ⟨i, rfl⟩
  | val => trivial
  | leaf =>
    obtain ⟨loc, cap, o, n, rfl, ho, hcell, hcap⟩ := hc
    exact ⟨loc, cap, o, n, rfl, ho, hcell, hcap⟩

theorem OpenUnder_renameTaint {rs A : List Nat} {s cur : Nat} {v : Val}
    (ho : OpenUnder rs (s :: A) v) (hcur : cur = 0 ∨ cur ∈ A) :
    OpenUnder rs A (renameTaint s cur v) := by
  intro r hr hopen
  rcases mem_taint_renameTaint (s := s) (cur := cur) (v := v) hr with
    ⟨hne, hrt⟩ | ⟨rfl, hne0, _⟩
  · rcases List.mem_cons.mp (ho r hrt hopen) with rfl | hA
    · exact absurd rfl hne
    · exact hA
  · rcases hcur with h0 | hA
    · exact absurd h0 hne0
    · exact hA

theorem DeepOpenUnder_renameTaint_closed {h : Heap} {rs A : List Nat} {s cur : Nat} {v : Val}
    (hd : DeepOpenUnder h rs (s :: A) v) (hcur : cur = 0 ∨ cur ∈ A) :
    DeepOpenUnder h (rs.filter (· != s)) A (renameTaint s cur v) := by
  have hdrop : ∀ w, OpenUnder rs (s :: A) w → OpenUnder (rs.filter (· != s)) A w := by
    intro w hw r hr hopen
    rw [List.mem_filter] at hopen
    rcases List.mem_cons.mp (hw r hr hopen.1) with rfl | hA
    · simp at hopen
    · exact hA
  cases v with
  | imm _ =>
    exact fun w hw => hdrop w (hd w hw)
  | ref loc cap t =>
    dsimp only [renameTaint]
    split
    · intro w hw
      rcases HeldBy_ref_taint (t2 := t) hw with rfl | hwOld
      · have htop : OpenUnder rs A (renameTaint s cur (.ref loc cap t)) :=
          OpenUnder_renameTaint hd.self hcur
        dsimp only [renameTaint] at htop
        split at htop
        · exact htop.weaken_open (fun x hx => (List.mem_filter.mp hx).1)
        · contradiction
      · exact hdrop w (hd w hwOld)
    · exact fun w hw => hdrop w (hd w hw)

/-! ### Strengthened `conform_spec` (`OwnReach`, `OwnTreeFull`, `DeepOpenUnder`) -/

theorem conform_spec_full {P : Prog} {st : St} {c : Cls} {v : Val}
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v) :
    (conform c v).run st = .error .stuck ∨
    ∃ v' st', (conform c v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      DeepLive st'.heap v' ∧ ClsOk st'.heap c v' ∧ AcyclicFrom st'.heap v' ∧
      (∀ r ∈ v'.taint, r ∈ v.taint) ∧
      (∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
      (∀ l, OwnReach P st'.heap v' l → OwnReach P st.heap v l) ∧
      (OwnTreeFull P st.heap v → OwnTreeFull P st'.heap v') ∧
      (∀ rs A, DeepOpenUnder st.heap rs A v → DeepOpenUnder st'.heap rs A v') := by
  rcases conform_spec hc hdl hacyc with hst |
    ⟨v', st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl', hcls', hacyc', ht', hreach', hheld'⟩
  · exact Or.inl hst
  · right
    refine ⟨v', st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl', hcls', hacyc',
      ht', hreach', ?_, ?_, ?_⟩
    · intro l hor
      cases c with
      | irr =>
        rw [hcls'] at hor; exact False.elim (OwnReach_imm_false P _ _ l hor)
      | imm =>
        obtain ⟨i, rfl⟩ := hcls'; exact False.elim (OwnReach_imm_false P _ _ l hor)
      | leaf =>
        obtain ⟨loc, cap, o, n, rfl, ho, hcell, _⟩ := hcls'
        exact False.elim (OwnReach_num_false ho hcell l hor)
      | val =>
        have hEq : v' = v ∧ st' = st := by
          unfold conform at hrun; cases hrun; exact ⟨rfl, rfl⟩
        rw [hEq.1, hEq.2] at hor; exact hor
    · intro htree
      cases c with
      | irr => rw [hcls']; exact OwnTreeFull_imm P _ _
      | imm => obtain ⟨i, rfl⟩ := hcls'; exact OwnTreeFull_imm P _ _
      | leaf =>
        obtain ⟨loc, cap, o, n, rfl, ho, hcell, _⟩ := hcls'
        exact OwnTreeFull_num ho hcell
      | val =>
        have hEq : v' = v ∧ st' = st := by
          unfold conform at hrun; cases hrun; exact ⟨rfl, rfl⟩
        rw [hEq.1, hEq.2]; exact htree
    · intro rs A hdou w hw
      rcases hheld' w hw with rfl | hwOld
      · exact fun r hr hopen => hdou.self r (ht' r hr) hopen
      · exact hdou w hwOld

/-! ## 2. `bindAt_spec` (`Eval.bindAt`) -/

private theorem bindAt_flat (P : Prog) (fuel s : Nat) (m : BinderMode) (c : Cls) (v : Val)
    (hm : m ≠ .erased) (st : St) :
    (bindAt P fuel s m c v).run st =
      ((conform c v) >>= fun v₁ =>
       (if m.isUnique = true then transfer P fuel m.isBorrowed v₁ else pure v₁) >>= fun v₂ =>
       (isLeaf v₂ >>= fun b =>
         if (m.isBorrowed && !b) = true then pure (addTaint s v₂) else pure v₂) >>= fun v₃ =>
       (if (m.usage == .once) = true then alloc (.once v₃ false) v₃.taint else pure v₃) >>= fun v₄ =>
       pure ⟨v₄, m⟩).run st := by
  have hmne : (m == .erased) = false := beq_false_of_ne hm
  have htail : ∀ (v₂ : Val) (st₂ : St),
      (do
        let __do_lift ← isLeaf v₂
        if (m.isBorrowed && !__do_lift) = true then do
          let v ← pure (addTaint s v₂)
          if (m.usage == .once) = true then do
            let v ← alloc (.once v false) v.taint
            pure ⟨v, m⟩
          else do
            let v ← pure v
            pure ⟨v, m⟩
        else do
          let v ← pure v₂
          if (m.usage == .once) = true then do
            let v ← alloc (.once v false) v.taint
            pure ⟨v, m⟩
          else do
            let v ← pure v
            pure ⟨v, m⟩ : M Bnd).run st₂ =
      ((isLeaf v₂ >>= fun b =>
          if (m.isBorrowed && !b) = true then pure (addTaint s v₂) else pure v₂) >>= fun v₃ =>
       (if (m.usage == .once) = true then alloc (.once v₃ false) v₃.taint else pure v₃) >>= fun v₄ =>
       pure ⟨v₄, m⟩).run st₂ := by
    intro v₂ st₂
    rw [M_bind_run, M_bind_run, M_bind_run]
    cases (isLeaf v₂).run st₂ with
    | error e => rfl
    | ok pb =>
      dsimp only
      cases (m.isBorrowed && !pb.1) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      · rw [M_bind_run, M_pure_run]
        dsimp only
        cases (m.usage == .once) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
  unfold bindAt
  simp only [hmne, Bool.false_eq_true, ↓reduceIte]
  rw [M_bind_run, M_bind_run]
  cases (conform c v).run st with
  | error e => rfl
  | ok p₁ =>
    dsimp only
    cases hu : m.isUnique <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [M_bind_run, M_bind_run, M_pure_run]
      dsimp only
      exact htail p₁.1 p₁.2
    · rw [M_bind_run, M_bind_run]
      cases (transfer P fuel m.isBorrowed p₁.1).run p₁.2 with
      | error e => rfl
      | ok p₂ =>
        dsimp only
        exact htail p₂.1 p₂.2

/-- Soundness and framing for `Eval.bindAt`. -/
theorem bindAt_spec {P : Prog} {fuel s : Nat} {m : BinderMode} {c : Cls} {v : Val} {st : St}
    (hc : CapsOk st.heap)
    (hdl : m ≠ .erased → DeepLive st.heap v)
    (hacyc : m ≠ .erased → AcyclicFrom st.heap v)
    (htree : m.isUnique = true → OwnTreeFull P st.heap v)
    (hconf : m.isUnique = true → m.isBorrowed = false → OpenUnder st.regions [] v) :
    (bindAt P fuel s m c v).run st = .error .stuck ∨
    (bindAt P fuel s m c v).run st = .error .outOfFuel ∨
    ∃ bnd st', (bindAt P fuel s m c v).run st = .ok (bnd, st') ∧
      bnd.mode = m ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧ (m.isUnique = true → ¬ OwnReach P st.heap v l))
        st.heap st'.heap ∧
      DeepLive st'.heap bnd.val ∧
      AcyclicFrom st'.heap bnd.val ∧
      (m.isUnique = true → OwnTreeFull P st'.heap bnd.val) ∧
      (m = .erased → bnd = ⟨.imm .irr, .erased⟩ ∧ st' = st) ∧
      (m ≠ .erased → m.usage ≠ .once → ClsOk st'.heap c bnd.val) ∧
      (m.usage = .once →
        ∃ base loc cap,
          bnd.val = .ref loc cap base.taint ∧
          loc = st'.heap.objs.size - 1 ∧
          st.heap.objs.size ≤ loc ∧
          st'.heap.objs[loc]? = some ⟨.once base false, cap⟩ ∧
          DeepLive st'.heap base ∧
          ClsOk st'.heap c base ∧
          AcyclicFrom st'.heap base ∧
          (∀ r ∈ base.taint, r ∈ v.taint ∨ (m.isBorrowed = true ∧ r = s))) ∧
      (∀ r ∈ bnd.val.taint, r ∈ v.taint ∨ (m.isBorrowed = true ∧ r = s)) ∧
      (c = .leaf → bnd.val.taint = []) ∧
      (∀ rs A, (m ≠ .erased → DeepOpenUnder st.heap rs A v) →
        DeepOpenUnder st'.heap rs (if m.isBorrowed then s :: A else A) bnd.val) ∧
      (∀ l, Reach st'.heap bnd.val l → st.heap.objs.size ≤ l ∨ (m ≠ .erased ∧ Reach st.heap v l)) ∧
      (∀ l, OwnReach P st'.heap bnd.val l →
        st.heap.objs.size ≤ l ∨ (m ≠ .erased ∧ OwnReach P st.heap v l)) := by
  by_cases her : m = .erased
  · subst her
    right; right
    refine ⟨⟨.imm .irr, .erased⟩, st, rfl, rfl, rfl, rfl, rfl, rfl,
      Nat.le_refl _, Nat.le_refl _, hc, OldSameShape.refl _, PreservesLocs.refl _ _,
      DeepLive_imm _ _, AcyclicFrom_imm _ _,
      (fun hu => by cases hu), (fun _ => ⟨rfl, rfl⟩),
      (fun h => absurd rfl h), (fun ho => by cases ho),
      (by simp [Val.taint]), (fun _ => rfl),
      (fun rs A _ => DeepOpenUnder_imm _ _ _ _),
      (fun _ hr => by cases hr), (fun _ hr => by cases hr)⟩
  · -- Step 1: `conform c v`
    rcases conform_spec_full (P := P) hc (hdl her) (hacyc her) with hst |
      ⟨v₁, st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hdl₁, hcls₁, hacyc₁,
        ht₁, hreach₁, hown₁, htree₁, hdou₁⟩
    · left
      rw [bindAt_flat P fuel s m c v her, M_bind_run, hst]
    -- Step 2: optional `transfer P fuel m.isBorrowed v₁`
    have hstep2 :
        (if m.isUnique = true then transfer P fuel m.isBorrowed v₁ else pure v₁).run st₁ = .error .outOfFuel ∨
        ∃ v₂ st₂,
          (if m.isUnique = true then transfer P fuel m.isBorrowed v₁ else pure v₁).run st₁ = .ok (v₂, st₂) ∧
          st₂.regions = st₁.regions ∧ st₂.nextRegion = st₁.nextRegion ∧
          st₂.statics = st₁.statics ∧ st₂.strs = st₁.strs ∧
          st₂.heap.objs.size = st₁.heap.objs.size ∧ st₁.heap.nextCap ≤ st₂.heap.nextCap ∧
          CapsOk st₂.heap ∧ HeapSameShape st₁.heap st₂.heap ∧ ValSameShape v₁ v₂ ∧
          DeepLive st₂.heap v₂ ∧ ClsOk st₂.heap c v₂ ∧ AcyclicFrom st₂.heap v₂ ∧
          (m.isUnique = true → OwnTreeFull P st₂.heap v₂) ∧
          PreservesLocs (fun l => m.isUnique = true → ¬ OwnReach P st₁.heap v₁ l) st₁.heap st₂.heap := by
      cases hu : m.isUnique with
      | false =>
        right
        refine ⟨v₁, st₁, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc₁,
          HeapSameShape.refl _, ValSameShape.refl _, hdl₁, hcls₁, hacyc₁,
          (fun h => by cases h), PreservesLocs.refl _ _⟩
      | true =>
        have hconf₁ : m.isBorrowed = false → OpenUnder st₁.regions [] v₁ := by
          intro hnb r hr hopen
          rw [hr₁] at hopen
          exact hconf hu hnb r (ht₁ r hr) hopen
        rcases transfer_spec (fuel := fuel) hc₁ hdl₁ hacyc₁ (htree₁ (htree hu)) hconf₁ with hOOF |
          ⟨v₂, st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc₂, hh₂, hv₂, hdl₂, hpres₂⟩
        · exact Or.inl hOOF
        · right
          exact ⟨v₂, st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc₂, hh₂, hv₂, hdl₂,
            ClsOk_of_sameShape hh₂ hv₂ hdl₂.self.1 hcls₁,
            AcyclicFrom_of_sameShape hh₂ hv₂ hacyc₁,
            fun _ => OwnTreeFull_of_sameShape hh₂ hv₂ (htree₁ (htree hu)),
            fun l hl => hpres₂ l (hl rfl)⟩
    rcases hstep2 with hOOF |
      ⟨v₂, st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc₂, hh₂, hv₂, hdl₂, hcls₂, hacyc₂,
        htree₂, hpres₂⟩
    · right; left
      rw [bindAt_flat P fuel s m c v her, M_bind_run, hrun₁]; dsimp only
      rw [M_bind_run, hOOF]
    -- Step 3: optional `addTaint s` when `m.isBorrowed && !(← isLeaf v₂)`
    have hstep3 :
        ∃ v₃,
          ((do
            let b ← isLeaf v₂
            if (m.isBorrowed && !b) = true then pure (addTaint s v₂) else pure v₂) : M Val).run st₂
            = .ok (v₃, st₂) ∧
          DeepLive st₂.heap v₃ ∧ ClsOk st₂.heap c v₃ ∧ AcyclicFrom st₂.heap v₃ ∧
          (m.isUnique = true → OwnTreeFull P st₂.heap v₃) ∧
          (∀ r ∈ v₃.taint, r ∈ v.taint ∨ (m.isBorrowed = true ∧ r = s)) ∧
          (c = .leaf → v₃.taint = []) ∧
          (∀ rs A, DeepOpenUnder st.heap rs A v →
            DeepOpenUnder st₂.heap rs (if m.isBorrowed then s :: A else A) v₃) ∧
          (∀ l, Reach st₂.heap v₃ l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
          (∀ l, OwnReach P st₂.heap v₃ l → OwnReach P st.heap v l) := by
      have hdou₂ : ∀ rs A, DeepOpenUnder st.heap rs A v → DeepOpenUnder st₂.heap rs A v₂ :=
        fun rs A hd => DeepOpenUnder_of_sameShape hh₂ hv₂ (hdou₁ rs A hd)
      have hreach₂ : ∀ l, Reach st₂.heap v₂ l → st.heap.objs.size ≤ l ∨ Reach st.heap v l :=
        fun l hl => hreach₁ l ((Reach_iff_sameShape hh₂ hv₂ l).mpr hl)
      have hown₂ : ∀ l, OwnReach P st₂.heap v₂ l → OwnReach P st.heap v l :=
        fun l hl => hown₁ l ((OwnReach_iff_sameShape hh₂ hv₂ l).mpr hl)
      have ht₂ : ∀ r ∈ v₂.taint, r ∈ v.taint := fun r hr => ht₁ r (hv₂.taint_eq ▸ hr)
      have hleafT₂ : c = .leaf → v₂.taint = [] := by
        intro hcl; subst hcl
        obtain ⟨_, _, _, _, rfl, _, _, _⟩ := hcls₂
        rfl
      cases hb : m.isBorrowed with
      | false =>
        refine ⟨v₂, ?_, hdl₂, hcls₂, hacyc₂, htree₂, fun r hr => Or.inl (ht₂ r hr),
          hleafT₂, hdou₂, hreach₂, hown₂⟩
        rw [M_bind_run, isLeaf_ok hdl₂.self.1]
        simp
        rfl
      | true =>
        cases hv2 : v₂ with
        | imm i =>
          refine ⟨.imm i, ?_, by simpa [hv2] using hdl₂, by simpa [hv2] using hcls₂,
            by simpa [hv2] using hacyc₂, by simpa [hv2] using htree₂,
            by simp [Val.taint], by intro _; rfl,
            (fun rs A _ => DeepOpenUnder_imm _ _ _ _),
            (fun _ hr => by cases hr), (fun _ hr => by cases hr)⟩
          rw [M_bind_run, isLeaf_ok (hv2 ▸ hdl₂.self.1)]
          rfl
        | ref loc cap t =>
          have hdl₂' : DeepLive st₂.heap (.ref loc cap t) := hv2 ▸ hdl₂
          obtain ⟨o, ho, _⟩ := hdl₂'.self.1
          cases hnum : o.cell.isNum with
          | true =>
            refine ⟨.ref loc cap t, ?_, hdl₂', hv2 ▸ hcls₂, hv2 ▸ hacyc₂, hv2 ▸ htree₂,
              fun r hr => Or.inl (ht₂ r (by rw [hv2]; exact hr)),
              fun hcl => by rw [← hv2]; exact hleafT₂ hcl,
              fun rs A hd => (hv2 ▸ hdou₂ rs A hd).mono (fun x hx => List.mem_cons_of_mem s hx),
              fun l hl => hreach₂ l (hv2.symm ▸ hl),
              fun l hl => hown₂ l (hv2.symm ▸ hl)⟩
            rw [M_bind_run, isLeaf_ok hdl₂'.self.1]
            simp only [ho, hnum, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            rfl
          | false =>
            have hnonLeaf : ∀ loc' cap' t' o' n',
                Val.ref loc cap t = .ref loc' cap' t' →
                st₂.heap.objs[loc']? = some o' → o'.cell = .num n' → False := by
              intro loc' cap' t' o' n' heq ho' hc'
              cases heq; rw [ho] at ho'; cases ho'
              simp [hc', Cell.isNum] at hnum
            refine ⟨addTaint s (.ref loc cap t), ?_,
              DeepLive_addTaint hdl₂' hnonLeaf,
              ClsOk_addTaint (hv2 ▸ hcls₂) hnonLeaf,
              AcyclicFrom_addTaint (hv2 ▸ hacyc₂),
              fun hu => OwnTreeFull_addTaint (hv2 ▸ htree₂ hu),
              fun r hr => by
                rcases mem_taint_addTaint (s := s) (v := .ref loc cap t) hr with rfl | hrt
                · exact Or.inr ⟨rfl, rfl⟩
                · exact Or.inl (ht₂ r (by rw [hv2]; exact hrt)),
              fun hcl => by
                subst hcl
                obtain ⟨loc', cap', o', n', heq, ho', hc', _⟩ := hv2 ▸ hcls₂
                exact False.elim (hnonLeaf loc' cap' [] o' n' heq ho' hc'),
              fun rs A hd => DeepOpenUnder_addTaint (hv2 ▸ hdou₂ rs A hd),
              fun l hl => hreach₂ l (hv2.symm ▸ (Reach_addTaint_iff l).mp hl),
              fun l hl => hown₂ l (hv2.symm ▸ (OwnReach_addTaint_iff l).mp hl)⟩
            rw [M_bind_run, isLeaf_ok hdl₂'.self.1]
            simp only [ho, hnum, Bool.not_false, Bool.and_true, ↓reduceIte]
            rfl
    obtain ⟨v₃, hrun₃, hdl₃, hcls₃, hacyc₃, htree₃, ht₃, hleafT₃, hdou₃, hreach₃, hown₃⟩ := hstep3
    have hpres12 : PreservesLocs
        (fun l => l < st.heap.objs.size ∧ (m.isUnique = true → ¬ OwnReach P st.heap v l))
        st.heap st₂.heap := by
      intro l ⟨hlt, hno⟩
      have h12 := hpres₂ l (fun hu hor1 => hno hu (hown₁ l hor1))
      exact h12.trans (hpres₁ l hlt)
    have hoss12 : OldSameShape st.heap st₂.heap :=
      (OldSameShape.of_preserves_old hsz₁ hpres₁).trans (OldSameShape.of_heapSameShape hh₂)
    -- Step 4: optional `alloc (.once v₃ false) v₃.taint`
    have hsz12 : st.heap.objs.size ≤ st₂.heap.objs.size := by omega
    cases honce : m.usage with
    | many | erased =>
      have hneOnce : m.usage ≠ .once := by rw [honce]; decide
      have hbeqOnce : (m.usage == .once) = false := beq_false_of_ne hneOnce
      right; right
      refine ⟨⟨v₃, m⟩, st₂, ?_, rfl,
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        hsz12, Nat.le_trans hcap₁ hcap₂, hc₂, hoss12, hpres12,
        hdl₃, hacyc₃, htree₃,
        (fun h => absurd h her), (fun _ _ => hcls₃), (fun h => by cases h),
        ht₃, hleafT₃,
        (fun rs A hd => hdou₃ rs A (hd her)),
        (fun l hl => (hreach₃ l hl).imp id (fun hr => ⟨her, hr⟩)),
        (fun l hl => Or.inr ⟨her, hown₃ l hl⟩)⟩
      rw [bindAt_flat P fuel s m c v her, M_bind_run, hrun₁]; dsimp only
      rw [M_bind_run, hrun₂]; dsimp only
      rw [M_bind_run, hrun₃]; dsimp only
      rw [M_bind_run]
      simp only [hbeqOnce, Bool.false_eq_true, ↓reduceIte]
      rfl
    | once =>
      have hbeqOnce : (m.usage == .once) = true := by rw [honce]; rfl
      let locNew := st₂.heap.objs.size
      let capNew := st₂.heap.nextCap
      let st₃ : St := { st₂ with heap := { objs := st₂.heap.objs.push ⟨.once v₃ false, capNew⟩,
                                           nextCap := capNew + 1 } }
      have hpres23 : PreservesLocs (fun l => l < st₂.heap.objs.size) st₂.heap st₃.heap :=
        alloc_preserves_old (.once v₃ false) v₃.taint st₂
      have hsz23 : st₂.heap.objs.size ≤ st₃.heap.objs.size := by simp [st₃]
      have hsub3 : ∀ u ∈ (Cell.once v₃ false).vals, DeepLive st₂.heap u ∧ AcyclicFrom st₂.heap u := by
        intro u hu; simp [Cell.vals] at hu; subst hu; exact ⟨hdl₃, hacyc₃⟩
      have hpw3 : PreservesLocs (Reach st₂.heap v₃) st₂.heap st₃.heap :=
        hpres23.mono (fun x hx => Reach_lt_size hdl₃ hx)
      right; right
      refine ⟨⟨.ref locNew capNew v₃.taint, m⟩, st₃, ?_, rfl,
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        Nat.le_trans hsz12 hsz23,
        Nat.le_trans (Nat.le_trans hcap₁ hcap₂) (Nat.le_succ _),
        alloc_capsOk hc₂,
        hoss12.trans (OldSameShape.of_preserves_old hsz23 hpres23),
        (fun l ⟨hlt, hno⟩ => (hpres23 l (Nat.lt_of_lt_of_le hlt hsz12)).trans
          (hpres12 l ⟨hlt, hno⟩)),
        alloc_deepLive (c := .once v₃ false) (t := v₃.taint) (fun u hu => (hsub3 u hu).1) (Or.inl rfl),
        alloc_acyclicFrom (c := .once v₃ false) (t := v₃.taint) hsub3,
        (fun hu => alloc_ownTreeFull_once hdl₃ hacyc₃ (htree₃ hu)),
        (fun h => absurd h her),
        (fun _ hne => absurd rfl hne),
        (fun _ => ⟨v₃, locNew, capNew, rfl, by simp [st₃, locNew], hsz12,
          by simp [st₃, locNew],
          (DeepLive_congr hpw3).mpr hdl₃,
          (ClsOk_congr hpw3).mpr hcls₃,
          (AcyclicFrom_congr hpw3).mpr hacyc₃,
          ht₃⟩),
        ht₃, hleafT₃,
        (fun rs A hd => alloc_deepOpenUnder (c := .once v₃ false) (t := v₃.taint)
          (fun u hu => by
            simp [Cell.vals] at hu; subst hu
            exact ⟨hdl₃, hdou₃ rs A (hd her)⟩)
          (hdou₃ rs A (hd her)).self),
        (fun l hl => by
          rcases (Reach_alloc_new (c := .once v₃ false) (t := v₃.taint)
            (fun u hu => (hsub3 u hu).1)).mp hl with rfl | ⟨u, hu, hru⟩
          · exact Or.inl hsz12
          · simp [Cell.vals] at hu; subst hu
            exact (hreach₃ l hru).imp id (fun hr => ⟨her, hr⟩)),
        (fun l hl => by
          rcases (alloc_ownReach_new (P := P) (c := .once v₃ false) (t := v₃.taint)
            (fun u hu => (hsub3 u hu).1) (Or.inl rfl)).mp hl with rfl | ⟨i, hi, w, hs, hrw⟩
          · exact Or.inl hsz12
          · simp [ownedSlots] at hi; subst hi
            simp [Cell.slot?] at hs; subst hs
            exact Or.inr ⟨her, hown₃ l hrw⟩)⟩
      rw [bindAt_flat P fuel s m c v her, M_bind_run, hrun₁]; dsimp only
      rw [M_bind_run, hrun₂]; dsimp only
      rw [M_bind_run, hrun₃]; dsimp only
      rw [M_bind_run]
      simp only [hbeqOnce, ↓reduceIte]
      rw [alloc_run]
      rfl

/-! ## 3. `ret_spec` (`Eval.ret`) -/

/-- Soundness and framing for `Eval.ret`. -/
theorem ret_spec {P : Prog} {fuel s cur : Nat} {r : ResultMode} {c : Cls} {v : Val} {st : St}
    (hc : CapsOk st.heap)
    (hdl : DeepLive st.heap v)
    (hacyc : AcyclicFrom st.heap v)
    (htree : r.isUnique = true → OwnTreeFull P st.heap v)
    (hnoS : (r = .shared ∨ r = .unique) → OpenUnder [s] [] v)
    (hnoOpen : r = .unique → OpenUnder st.regions [] v) :
    (ret P fuel s cur r c v).run st = .error .stuck ∨
    (ret P fuel s cur r c v).run st = .error .outOfFuel ∨
    ∃ v' st', (ret P fuel s cur r c v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧ (r.isUnique = true → ¬ OwnReach P st.heap v l))
        st.heap st'.heap ∧
      ClsOk st'.heap c v' ∧
      DeepLive st'.heap v' ∧
      AcyclicFrom st'.heap v' ∧
      (r.isUnique = true → OwnTreeFull P st'.heap v') ∧
      ((r = .shared ∨ r = .unique) → ∀ x ∈ v'.taint, x ∈ v.taint) ∧
      (r.isBorrowed = true →
        ∀ x ∈ v'.taint, (x ∈ v.taint ∧ x ≠ s) ∨ (x = cur ∧ cur ≠ 0 ∧ s ∈ v.taint)) ∧
      (∀ rs A, (r = .shared ∨ r = .unique) → DeepOpenUnder st.heap rs A v →
        DeepOpenUnder st'.heap rs A v') ∧
      (∀ rs A, r.isBorrowed = true → (cur = 0 ∨ cur ∈ A) →
        OpenUnder rs (s :: A) v → OpenUnder rs A v') ∧
      (∀ rs A, (cur = 0 ∨ cur ∈ A) → DeepOpenUnder st.heap rs (s :: A) v →
        DeepOpenUnder st'.heap (rs.filter (· != s)) A v') ∧
      (∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
      (∀ l, OwnReach P st'.heap v' l → OwnReach P st.heap v l) := by
  rcases conform_spec_full (P := P) hc hdl hacyc with hst |
    ⟨v₁, st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hdl₁, hcls₁, hacyc₁,
      ht₁, hreach₁, hown₁, htree₁, hdou₁⟩
  · left
    unfold ret; rw [M_bind_run, hst]
  have hdropS : ∀ {h' : Heap} {rs A : List Nat} {w : Val},
      DeepOpenUnder h' rs (s :: A) w → DeepOpenUnder h' (rs.filter (· != s)) A w := by
    intro h' rs A w hd u hu x hx hopen
    rw [List.mem_filter] at hopen
    rcases List.mem_cons.mp (hd u hu x hx hopen.1) with rfl | hA
    · simp at hopen
    · exact hA
  cases r with
  | shared =>
    have hconfF : confinedTo s v₁ = false := by
      have ho1 : OpenUnder [s] [] v₁ := fun x hx hopen => hnoS (Or.inl rfl) x (ht₁ x hx) hopen
      exact ho1.confinedTo_false List.mem_cons_self (List.not_mem_nil)
    right; right
    refine ⟨v₁, st₁, ?_, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁,
      OldSameShape.of_preserves_old hsz₁ hpres₁,
      (fun l ⟨hlt, _⟩ => hpres₁ l hlt),
      hcls₁, hdl₁, hacyc₁, (fun h => by cases h),
      (fun _ => ht₁), (fun h => by cases h),
      (fun rs A _ hd => hdou₁ rs A hd), (fun _ _ h => by cases h),
      (fun rs A _ hd => hdropS (hdou₁ rs (s :: A) hd)),
      hreach₁, hown₁⟩
    unfold ret; rw [M_bind_run, hrun₁]; dsimp only
    simp only [hconfF, Bool.false_eq_true, ↓reduceIte]; rfl
  | unique =>
    have hconfF : confinedTo s v₁ = false := by
      have ho1 : OpenUnder [s] [] v₁ := fun x hx hopen => hnoS (Or.inr rfl) x (ht₁ x hx) hopen
      exact ho1.confinedTo_false List.mem_cons_self (List.not_mem_nil)
    have hnoOpen₁ : false = false → OpenUnder st₁.regions [] v₁ := by
      intro _ x hx hopen
      rw [hr₁] at hopen
      exact hnoOpen rfl x (ht₁ x hx) hopen
    rcases transfer_spec hc₁ hdl₁ hacyc₁ (htree₁ (htree rfl)) hnoOpen₁ with hOOF |
      ⟨v₂, st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc₂, hh₂, hv₂, hdl₂, hpres₂⟩
    · right; left
      unfold ret; rw [M_bind_run, hrun₁]; dsimp only
      simp only [hconfF, Bool.false_eq_true, ↓reduceIte]
      exact hOOF
    · right; right
      refine ⟨v₂, st₂, ?_,
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        hsz₂.symm ▸ hsz₁, Nat.le_trans hcap₁ hcap₂, hc₂,
        (OldSameShape.of_preserves_old hsz₁ hpres₁).trans (OldSameShape.of_heapSameShape hh₂),
        (fun l ⟨hlt, hno⟩ => (hpres₂ l (fun hor1 => hno rfl (hown₁ l hor1))).trans (hpres₁ l hlt)),
        ClsOk_of_sameShape hh₂ hv₂ hdl₂.self.1 hcls₁,
        hdl₂, AcyclicFrom_of_sameShape hh₂ hv₂ hacyc₁,
        (fun _ => OwnTreeFull_of_sameShape hh₂ hv₂ (htree₁ (htree rfl))),
        (fun _ x hx => ht₁ x (hv₂.taint_eq ▸ hx)),
        (fun h => by cases h),
        (fun rs A _ hd => DeepOpenUnder_of_sameShape hh₂ hv₂ (hdou₁ rs A hd)),
        (fun _ _ h => by cases h),
        (fun rs A _ hd => hdropS (DeepOpenUnder_of_sameShape hh₂ hv₂ (hdou₁ rs (s :: A) hd))),
        (fun l hl => hreach₁ l ((Reach_iff_sameShape hh₂ hv₂ l).mpr hl)),
        (fun l hl => hown₁ l ((OwnReach_iff_sameShape hh₂ hv₂ l).mpr hl))⟩
      unfold ret; rw [M_bind_run, hrun₁]; dsimp only
      simp only [hconfF, Bool.false_eq_true, ↓reduceIte]
      exact hrun₂
  | borrowed =>
    right; right
    refine ⟨renameTaint s cur v₁, st₁, ?_, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁,
      OldSameShape.of_preserves_old hsz₁ hpres₁,
      (fun l ⟨hlt, _⟩ => hpres₁ l hlt),
      ClsOk_renameTaint hcls₁,
      DeepLive_renameTaint hdl₁,
      AcyclicFrom_renameTaint hacyc₁,
      (fun h => by cases h),
      (fun h => by rcases h with h | h <;> cases h),
      (fun _ x hx => by
        rcases mem_taint_renameTaint (s := s) (cur := cur) (v := v₁) hx with
          ⟨hne, h1⟩ | ⟨rfl, hne0, hs1⟩
        · exact Or.inl ⟨ht₁ x h1, hne⟩
        · exact Or.inr ⟨rfl, hne0, ht₁ s hs1⟩),
      (fun _ _ h => by rcases h with h | h <;> cases h),
      (fun rs A _ hcur ho => OpenUnder_renameTaint (fun x hx hopen => ho x (ht₁ x hx) hopen) hcur),
      (fun rs A hcur hd => DeepOpenUnder_renameTaint_closed (hdou₁ rs (s :: A) hd) hcur),
      (fun l hl => hreach₁ l ((Reach_renameTaint_iff l).mp hl)),
      (fun l hl => hown₁ l ((OwnReach_renameTaint_iff l).mp hl))⟩
    unfold ret; rw [M_bind_run, hrun₁]; rfl
  | uniqueBorrowed =>
    rcases transfer_spec (fuel := fuel) (toBorrowed := true) hc₁ hdl₁ hacyc₁
        (htree₁ (htree rfl)) (fun h => by cases h) with hOOF |
      ⟨v₂, st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc₂, hh₂, hv₂, hdl₂, hpres₂⟩
    · right; left
      unfold ret; rw [M_bind_run, hrun₁]; dsimp only
      rw [M_bind_run, hOOF]
    · right; right
      refine ⟨renameTaint s cur v₂, st₂, ?_,
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        hsz₂.symm ▸ hsz₁, Nat.le_trans hcap₁ hcap₂, hc₂,
        (OldSameShape.of_preserves_old hsz₁ hpres₁).trans (OldSameShape.of_heapSameShape hh₂),
        (fun l ⟨hlt, hno⟩ => (hpres₂ l (fun hor1 => hno rfl (hown₁ l hor1))).trans (hpres₁ l hlt)),
        ClsOk_renameTaint (ClsOk_of_sameShape hh₂ hv₂ hdl₂.self.1 hcls₁),
        DeepLive_renameTaint hdl₂,
        AcyclicFrom_renameTaint (AcyclicFrom_of_sameShape hh₂ hv₂ hacyc₁),
        (fun _ => OwnTreeFull_renameTaint (OwnTreeFull_of_sameShape hh₂ hv₂ (htree₁ (htree rfl)))),
        (fun h => by rcases h with h | h <;> cases h),
        (fun _ x hx => by
          rcases mem_taint_renameTaint (s := s) (cur := cur) (v := v₂) hx with
            ⟨hne, h2⟩ | ⟨rfl, hne0, hs2⟩
          · exact Or.inl ⟨ht₁ x (hv₂.taint_eq ▸ h2), hne⟩
          · exact Or.inr ⟨rfl, hne0, ht₁ s (hv₂.taint_eq ▸ hs2)⟩),
        (fun _ _ h => by rcases h with h | h <;> cases h),
        (fun rs A _ hcur ho =>
          OpenUnder_renameTaint (fun x hx hopen => ho x (ht₁ x (hv₂.taint_eq ▸ hx)) hopen) hcur),
        (fun rs A hcur hd =>
          DeepOpenUnder_renameTaint_closed (DeepOpenUnder_of_sameShape hh₂ hv₂ (hdou₁ rs (s :: A) hd)) hcur),
        (fun l hl => hreach₁ l ((Reach_iff_sameShape hh₂ hv₂ l).mpr ((Reach_renameTaint_iff l).mp hl))),
        (fun l hl => hown₁ l ((OwnReach_iff_sameShape hh₂ hv₂ l).mpr ((OwnReach_renameTaint_iff l).mp hl)))⟩
      unfold ret; rw [M_bind_run, hrun₁]; dsimp only
      rw [M_bind_run, hrun₂]; rfl

/-! ## 4. `prim_spec` (`Eval.prim`) -/

/-- Explicit list recursion matching `Eval.prim`'s `for v in vs` loop. -/
def primNumsLoop : List Val → List Nat → M (List Nat)
  | [], ns => pure ns
  | v :: rest, ns => do
    match ← numOf? v with
    | some k => primNumsLoop rest (ns ++ [k])
    | none => stuckM

theorem forIn_list_primNumsLoop (vs : List Val) (ns : List Nat) (st : St) :
    (forIn (m := M) vs ns (fun v r => do
        match ← numOf? v with
        | some k => pure (ForInStep.yield (r ++ [k]))
        | none => stuckM)).run st =
      (primNumsLoop vs ns).run st := by
  induction vs generalizing ns st with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.forIn_cons]
    unfold primNumsLoop
    rw [M_bind_run, M_bind_run, M_bind_run]
    cases (numOf? v).run st with
    | error e => rfl
    | ok p =>
      dsimp only
      cases p.1 with
      | none => rfl
      | some k =>
        rw [M_pure_run]
        exact ih (ns ++ [k]) p.2

theorem primNumsLoop_spec {vs : List Val} {ns : List Nat} {st : St}
    (hl : ∀ v ∈ vs, LiveRef st.heap v) :
    (primNumsLoop vs ns).run st = .error .stuck ∨
    ∃ ns', (primNumsLoop vs ns).run st = .ok (ns', st) := by
  induction vs generalizing ns with
  | nil => exact Or.inr ⟨ns, rfl⟩
  | cons v rest ih =>
    unfold primNumsLoop
    rw [M_bind_run, numOf?_ok (hl v List.mem_cons_self)]
    dsimp only
    split
    · exact ih (fun u hu => hl u (List.mem_cons_of_mem v hu))
    · exact Or.inl rfl

/-- Soundness and framing for `Eval.prim`. -/
theorem prim_spec {P : Prog} {p : Prim} {vs : List Val} {st : St}
    (hc : CapsOk st.heap)
    (hl : ∀ v ∈ vs, LiveRef st.heap v) :
    (prim p vs).run st = .error .stuck ∨
    ∃ v st', (prim p vs).run st = .ok (v, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      DeepLive st'.heap v ∧
      LeafUntainted st'.heap v ∧
      v.taint = [] ∧
      AcyclicFrom st'.heap v ∧
      OwnTreeFull P st'.heap v ∧
      ((∃ i, v = .imm i ∧ st' = st) ∨
       (∃ loc cap o n, v = .ref loc cap [] ∧ st.heap.objs.size ≤ loc ∧
         st'.heap.objs[loc]? = some o ∧ o.cell = .num n ∧ o.cap = cap)) := by
  have hnat : ∀ n,
      ∃ v st', (natValue n).run st = .ok (v, st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
        CapsOk st'.heap ∧
        OldSameShape st.heap st'.heap ∧
        DeepLive st'.heap v ∧
        LeafUntainted st'.heap v ∧
        v.taint = [] ∧
        AcyclicFrom st'.heap v ∧
        OwnTreeFull P st'.heap v ∧
        ((∃ i, v = .imm i ∧ st' = st) ∨
         (∃ loc cap o m, v = .ref loc cap [] ∧ st.heap.objs.size ≤ loc ∧
           st'.heap.objs[loc]? = some o ∧ o.cell = .num m ∧ o.cap = cap)) := by
    intro n
    obtain ⟨v, st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl, ht, hacyc, _, hnum⟩ :=
      mkNum_ok natClass n st hc
    obtain ⟨loc, cap, o, rfl, ho, hcell, hocap, hge⟩ := hnum (by decide)
    exact ⟨.ref loc cap [], st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc',
      OldSameShape.of_preserves_old hsz hpres,
      hdl, hdl.self.2, ht, hacyc, OwnTreeFull_num ho hcell,
      Or.inr ⟨loc, cap, o, n, rfl, hge, ho, hcell, hocap⟩⟩
  have hbool : ∀ (r : Ref),
      ∃ v st', (pure (Val.imm (.con r)) : M Val).run st = .ok (v, st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
        CapsOk st'.heap ∧
        OldSameShape st.heap st'.heap ∧
        DeepLive st'.heap v ∧
        LeafUntainted st'.heap v ∧
        v.taint = [] ∧
        AcyclicFrom st'.heap v ∧
        OwnTreeFull P st'.heap v ∧
        ((∃ i, v = .imm i ∧ st' = st) ∨
         (∃ loc cap o m, v = .ref loc cap [] ∧ st.heap.objs.size ≤ loc ∧
           st'.heap.objs[loc]? = some o ∧ o.cell = .num m ∧ o.cap = cap)) := by
    intro r
    exact ⟨.imm (.con r), st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, OldSameShape.refl _,
      DeepLive_imm _ _, trivial, rfl, AcyclicFrom_imm _ _, OwnTreeFull_imm P _ _,
      Or.inl ⟨.con r, rfl, rfl⟩⟩
  unfold prim
  rw [M_bind_run]
  erw [forIn_list_primNumsLoop]
  rcases primNumsLoop_spec hl with hst | ⟨ns, hns⟩
  · left; rw [hst]
  · rw [hns]; dsimp only
    cases p with
    | zero =>
      rcases ns with _ | ⟨_, _⟩
      · exact Or.inr (hnat 0)
      · exact Or.inl rfl
    | succ =>
      rcases ns with _ | ⟨a, _ | ⟨_, _⟩⟩
      · exact Or.inl rfl
      · exact Or.inr (hnat (a + 1))
      · exact Or.inl rfl
    | pred =>
      rcases ns with _ | ⟨a, _ | ⟨_, _⟩⟩
      · exact Or.inl rfl
      · exact Or.inr (hnat (a - 1))
      · exact Or.inl rfl
    | add =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a + b))
      · exact Or.inl rfl
    | sub =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a - b))
      · exact Or.inl rfl
    | mul =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a * b))
      · exact Or.inl rfl
    | div =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a / b))
      · exact Or.inl rfl
    | mod =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a % b))
      · exact Or.inl rfl
    | pow =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a ^ b))
      · exact Or.inl rfl
    | gcd =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (Nat.gcd a b))
      · exact Or.inl rfl
    | land =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a &&& b))
      · exact Or.inl rfl
    | lor =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a ||| b))
      · exact Or.inl rfl
    | xor =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a ^^^ b))
      · exact Or.inl rfl
    | shiftLeft =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a <<< b))
      · exact Or.inl rfl
    | shiftRight =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hnat (a >>> b))
      · exact Or.inl rfl
    | beq t f =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hbool (if a == b then t else f))
      · exact Or.inl rfl
    | ble t f =>
      rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (hbool (if a ≤ b then t else f))
      · exact Or.inl rfl

/-! ## 5. `construct_spec` (`Eval.construct`) -/

/-- Explicit list recursion matching `Eval.construct`'s `for (f, v) in fields.toList.zip vs` loop. -/
def constructLoop : List (Field × Val) → Array Val → M (Array Val)
  | [], out => pure out
  | (f, v) :: rest, out =>
    (if f.kept = true then conform f.cls v else pure (.imm .irr)) >>= fun v' =>
      constructLoop rest (out.push v')

theorem forIn_list_constructLoop (xs : List (Field × Val)) (out : Array Val) (st : St) :
    (forIn (m := M) xs out (fun fv acc => do
        let v' ← if fv.1.kept then conform fv.1.cls fv.2 else pure (.imm .irr)
        pure (ForInStep.yield (acc.push v')))).run st =
      (constructLoop xs out).run st := by
  induction xs generalizing out st with
  | nil => rfl
  | cons fv rest ih =>
    simp only [List.forIn_cons]
    unfold constructLoop
    rw [M_bind_run, M_bind_run]
    cases hk : fv.1.kept <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [M_bind_run, M_pure_run]
      dsimp only
      rw [M_pure_run]
      dsimp only
      exact ih (out.push (.imm .irr)) st
    · rw [M_bind_run]
      cases (conform fv.1.cls fv.2).run st with
      | error e => rfl
      | ok p =>
        dsimp only
        rw [M_pure_run]
        exact ih (out.push p.1) p.2

theorem constructLoop_spec {P : Prog} {xs : List (Field × Val)} {out : Array Val} {st : St}
    (hc : CapsOk st.heap)
    (hout : ∀ w ∈ out.toList, DeepLive st.heap w ∧ AcyclicFrom st.heap w)
    (hxs : ∀ fv ∈ xs, fv.1.kept = true → DeepLive st.heap fv.2 ∧ AcyclicFrom st.heap fv.2) :
    (constructLoop xs out).run st = .error .stuck ∨
    ∃ out' st', (constructLoop xs out).run st = .ok (out', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      out'.size = out.size + xs.length ∧
      (∀ i, i < out.size → out'[i]? = out[i]?) ∧
      (∀ w ∈ out'.toList, DeepLive st'.heap w ∧ AcyclicFrom st'.heap w) ∧
      (∀ k f v, xs[k]? = some (f, v) →
        ∃ w, out'[out.size + k]? = some w ∧
          DeepLive st'.heap w ∧ AcyclicFrom st'.heap w ∧
          (∀ x ∈ w.taint, f.kept = true ∧ x ∈ v.taint) ∧
          (∀ l, Reach st'.heap w l → st.heap.objs.size ≤ l ∨ (f.kept = true ∧ Reach st.heap v l)) ∧
          (∀ l, OwnReach P st'.heap w l → f.kept = true ∧ OwnReach P st.heap v l) ∧
          (f.kept = true → OwnTreeFull P st.heap v → OwnTreeFull P st'.heap w) ∧
          (∀ rs A, (f.kept = true → DeepOpenUnder st.heap rs A v) → DeepOpenUnder st'.heap rs A w) ∧
          (f.kept = false → w = .imm .irr)) := by
  induction xs generalizing out st with
  | nil =>
    right
    refine ⟨out, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, by simp, fun _ _ => rfl, hout, ?_⟩
    intro k _ _ hk; simp at hk
  | cons fv rest ih =>
    rcases fv with ⟨f, v⟩
    -- Step 1: process `(f, v)`
    have hstep1 :
        (if f.kept = true then conform f.cls v else pure (.imm .irr)).run st = .error .stuck ∨
        ∃ v' st₁,
          (if f.kept = true then conform f.cls v else pure (.imm .irr)).run st = .ok (v', st₁) ∧
          st₁.regions = st.regions ∧ st₁.nextRegion = st.nextRegion ∧
          st₁.statics = st.statics ∧ st₁.strs = st.strs ∧
          st.heap.objs.size ≤ st₁.heap.objs.size ∧ st.heap.nextCap ≤ st₁.heap.nextCap ∧
          PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₁.heap ∧
          CapsOk st₁.heap ∧
          DeepLive st₁.heap v' ∧ AcyclicFrom st₁.heap v' ∧
          (∀ x ∈ v'.taint, f.kept = true ∧ x ∈ v.taint) ∧
          (∀ l, Reach st₁.heap v' l → st.heap.objs.size ≤ l ∨ (f.kept = true ∧ Reach st.heap v l)) ∧
          (∀ l, OwnReach P st₁.heap v' l → f.kept = true ∧ OwnReach P st.heap v l) ∧
          (f.kept = true → OwnTreeFull P st.heap v → OwnTreeFull P st₁.heap v') ∧
          (∀ rs A, (f.kept = true → DeepOpenUnder st.heap rs A v) → DeepOpenUnder st₁.heap rs A v') ∧
          (f.kept = false → v' = .imm .irr) := by
      cases hk : f.kept with
      | false =>
        right
        refine ⟨.imm .irr, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
          PreservesLocs.refl _ _, hc, DeepLive_imm _ _, AcyclicFrom_imm _ _,
          by simp [Val.taint], (fun _ hr => by cases hr), (fun _ hr => by cases hr),
          (fun h => by cases h), (fun _ _ _ => DeepOpenUnder_imm _ _ _ _), fun _ => rfl⟩
      | true =>
        have hfv := hxs (f, v) List.mem_cons_self hk
        rcases conform_spec_full (P := P) hc hfv.1 hfv.2 with hst |
          ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hdl₁, _, hacyc₁,
            ht₁, hreach₁, hown₁, htree₁, hdou₁⟩
        · exact Or.inl hst
        · right
          exact ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hdl₁, hacyc₁,
            fun x hx => ⟨rfl, ht₁ x hx⟩,
            fun l hl => (hreach₁ l hl).imp id (fun hr => ⟨rfl, hr⟩),
            fun l hl => ⟨rfl, hown₁ l hl⟩,
            fun _ htr => htree₁ htr,
            fun rs A hd => hdou₁ rs A (hd rfl),
            fun h => by cases h⟩
    rcases hstep1 with hst |
      ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hdl₁, hacyc₁,
        ht₁, hreach₁, hown₁, htree₁, hdou₁, hnk₁⟩
    · left
      unfold constructLoop; rw [M_bind_run, hst]
    have hout₁ : ∀ w ∈ (out.push v').toList, DeepLive st₁.heap w ∧ AcyclicFrom st₁.heap w := by
      intro w hw
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have hw0 := hout w hw
        have hpw : PreservesLocs (Reach st.heap w) st.heap st₁.heap :=
          hpres₁.mono (fun x hx => Reach_lt_size hw0.1 hx)
        exact ⟨(DeepLive_congr hpw).mpr hw0.1, (AcyclicFrom_congr hpw).mpr hw0.2⟩
      · exact ⟨hdl₁, hacyc₁⟩
    have hxs₁ : ∀ fv' ∈ rest, fv'.1.kept = true → DeepLive st₁.heap fv'.2 ∧ AcyclicFrom st₁.heap fv'.2 := by
      intro fv' hmem hfk
      have h0 := hxs fv' (List.mem_cons_of_mem (f, v) hmem) hfk
      have hpw : PreservesLocs (Reach st.heap fv'.2) st.heap st₁.heap :=
        hpres₁.mono (fun x hx => Reach_lt_size h0.1 hx)
      exact ⟨(DeepLive_congr hpw).mpr h0.1, (AcyclicFrom_congr hpw).mpr h0.2⟩
    rcases ih hc₁ hout₁ hxs₁ with hst |
      ⟨out', st', hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hpres₂, hc', hszOut,
        hold, hall, hrest⟩
    · left
      unfold constructLoop; rw [M_bind_run, hrun₁]; exact hst
    · right
      have hpres12 : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
        fun l hlt => (hpres₂ l (Nat.lt_of_lt_of_le hlt hsz₁)).trans (hpres₁ l hlt)
      refine ⟨out', st', ?_,
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hpres12, hc',
        (by rw [hszOut]; simp only [Array.size_push, List.length_cons]; omega),
        (fun i hi => by
          have hi' : i < (out.push v').size := by simp; omega
          rw [hold i hi', Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]),
        hall, ?_⟩
      · unfold constructLoop; rw [M_bind_run, hrun₁]; exact hrun₂
      · intro k fk vk hk
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
          rcases hk with ⟨rfl, rfl⟩
          have hget : out'[out.size + 0]? = some v' := by
            have hlt : out.size < (out.push v').size := by simp
            simpa using (hold out.size hlt).trans (by simp)
          have hpw : PreservesLocs (Reach st₁.heap v') st₁.heap st'.heap :=
            hpres₂.mono (fun x hx => Reach_lt_size hdl₁ hx)
          exact ⟨v', hget,
            (DeepLive_congr hpw).mpr hdl₁,
            (AcyclicFrom_congr hpw).mpr hacyc₁,
            ht₁,
            (fun l hl => hreach₁ l ((Reach_congr hpw l).mp hl)),
            (fun l hl => hown₁ l ((OwnReach_congr hpw l).mp hl)),
            (fun hfk htr => (OwnTreeFull_congr hpw).mpr (htree₁ hfk htr)),
            (fun rs A hd => (DeepOpenUnder_congr hpw).mpr (hdou₁ rs A hd)),
            hnk₁⟩
        | succ k' =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨w, hwget, hwdl, hwacyc, hwt, hwreach, hwown, hwtree, hwdou, hwnk⟩ :=
            hrest k' fk vk hk
          have hidx : (out.push v').size + k' = out.size + (k' + 1) := by simp; omega
          rw [hidx] at hwget
          have hmem : (fk, vk) ∈ rest := List.mem_of_getElem? hk
          refine ⟨w, hwget, hwdl, hwacyc, hwt, ?_, ?_, ?_, ?_, hwnk⟩
          · intro l hl
            rcases hwreach l hl with hge | ⟨hfk, hrv1⟩
            · exact Or.inl (Nat.le_trans hsz₁ hge)
            · have h0 := hxs (fk, vk) (List.mem_cons_of_mem (f, v) hmem) hfk
              have hpw : PreservesLocs (Reach st.heap vk) st.heap st₁.heap :=
                hpres₁.mono (fun x hx => Reach_lt_size h0.1 hx)
              exact Or.inr ⟨hfk, (Reach_congr hpw l).mp hrv1⟩
          · intro l hl
            obtain ⟨hfk, hor1⟩ := hwown l hl
            have h0 := hxs (fk, vk) (List.mem_cons_of_mem (f, v) hmem) hfk
            have hpw : PreservesLocs (Reach st.heap vk) st.heap st₁.heap :=
              hpres₁.mono (fun x hx => Reach_lt_size h0.1 hx)
            exact ⟨hfk, (OwnReach_congr hpw l).mp hor1⟩
          · intro hfk htr
            have h0 := hxs (fk, vk) (List.mem_cons_of_mem (f, v) hmem) hfk
            have hpw : PreservesLocs (Reach st.heap vk) st.heap st₁.heap :=
              hpres₁.mono (fun x hx => Reach_lt_size h0.1 hx)
            exact hwtree hfk ((OwnTreeFull_congr hpw).mpr htr)
          · intro rs A hd
            refine hwdou rs A (fun hfk => ?_)
            have h0 := hxs (fk, vk) (List.mem_cons_of_mem (f, v) hmem) hfk
            have hpw : PreservesLocs (Reach st.heap vk) st.heap st₁.heap :=
              hpres₁.mono (fun x hx => Reach_lt_size h0.1 hx)
            exact (DeepOpenUnder_congr hpw).mpr (hd hfk)

/-- Soundness, framing, and `OwnTreeFull` construction for `Eval.construct`. -/
theorem construct_spec {P : Prog} {r : Ref} {fields : Array Field} {vs : List Val}
    {c : Cls} {st : St}
    (hc : CapsOk st.heap)
    (hvs : ∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
      DeepLive st.heap v ∧ AcyclicFrom st.heap v) :
    (construct r fields vs c).run st = .error .stuck ∨
    ∃ rv st', (construct r fields vs c).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      DeepLive st'.heap rv ∧
      AcyclicFrom st'.heap rv ∧
      (∀ rs A,
        (∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
          DeepOpenUnder st.heap rs A v) →
        DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l →
        st.heap.objs.size ≤ l ∨
        ∃ (i : Nat) (f : Field) (v : Val), fields[i]? = some f ∧ vs[i]? = some v ∧ f.kept = true ∧ Reach st.heap v l) ∧
      (c = .val → ClsOk st'.heap c rv) ∧
      (rv = .imm (.con r) ∨
       ((c = .imm ∨ c = .leaf) ∧ ClsOk st'.heap c rv) ∨
       (∃ loc cap out,
         rv = .ref loc cap (taints out.toList) ∧
         loc = st'.heap.objs.size - 1 ∧
         st.heap.objs.size ≤ loc ∧
         st'.heap.objs[loc]? = some ⟨.ctor r out, cap⟩ ∧
         out.size = min fields.size vs.length)) ∧
      ((∃ ind tag nP, P.ctorOf? r = some (ind, tag, nP, fields)) →
       (∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
         f.fmode = .inherited → OwnTreeFull P st.heap v) →
       (∀ (i j : Nat) (fi : Field) (vi : Val) (fj : Field) (vj : Val), i ≠ j →
         fields[i]? = some fi → vs[i]? = some vi →
         fields[j]? = some fj → vs[j]? = some vj →
         fi.kept = true → fj.kept = true → fi.fmode = .inherited →
         ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) →
       OwnTreeFull P st'.heap rv) := by
  have hxs : ∀ fv ∈ fields.toList.zip vs, fv.1.kept = true →
      DeepLive st.heap fv.2 ∧ AcyclicFrom st.heap fv.2 := by
    intro fv hmem hfk
    obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hmem
    rw [List.getElem_zip] at heq
    have hk' : k < min fields.size vs.length := by
      simpa [List.length_zip, Array.length_toList] using hk
    have hlt1 : k < fields.size := Nat.lt_of_lt_of_le hk' (Nat.min_le_left _ _)
    have hlt2 : k < vs.length := Nat.lt_of_lt_of_le hk' (Nat.min_le_right _ _)
    have hf : fields[k]? = some fv.1 := by
      rw [Array.getElem?_eq_getElem hlt1]; exact congrArg some (congrArg Prod.fst heq)
    have hv : vs[k]? = some fv.2 := by
      rw [List.getElem?_eq_getElem hlt2]; exact congrArg some (congrArg Prod.snd heq)
    exact hvs k fv.1 fv.2 hf hv hfk
  unfold construct
  rw [M_bind_run]
  erw [forIn_list_constructLoop]
  rcases constructLoop_spec (P := P) (out := #[]) hc (by simp) hxs with hst |
    ⟨out, st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hszOut, _, hall, hrest⟩
  · left; rw [hst]
  · rw [hrun₁]; dsimp only
    have hszZip : out.size = (fields.toList.zip vs).length := by simpa using hszOut
    have hzipAt : ∀ (k : Nat), k < out.size →
        ∃ (f : Field) (v : Val), fields[k]? = some f ∧ vs[k]? = some v ∧ (fields.toList.zip vs)[k]? = some (f, v) := by
      intro k hk
      have hk' : k < (fields.toList.zip vs).length := hszZip ▸ hk
      have hltF : k < fields.size := by rw [List.length_zip] at hk'; simp at hk'; omega
      have hltV : k < vs.length := by rw [List.length_zip] at hk'; simp at hk'; omega
      refine ⟨fields[k], vs[k], Array.getElem?_eq_getElem hltF, List.getElem?_eq_getElem hltV, ?_⟩
      rw [List.getElem?_eq_getElem hk', List.getElem_zip]
      rfl
    have hszMin : out.size = min fields.size vs.length := by
      simpa [List.length_zip, Array.length_toList] using hszZip
    let kept := (fields.zipIdx.filter fun x => x.1.kept).map (·.2)
    by_cases hke : kept.isEmpty = true
    · right
      refine ⟨.imm (.con r), st₁, ?_, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁,
        OldSameShape.of_preserves_old hsz₁ hpres₁,
        DeepLive_imm _ _, AcyclicFrom_imm _ _,
        (fun rs A _ => DeepOpenUnder_imm _ _ _ _),
        (fun _ hr => by cases hr),
        (fun h => by subst h; trivial),
        Or.inl rfl,
        (fun _ _ _ => OwnTreeFull_imm P _ _)⟩
      show StateT.run (if kept.isEmpty = true then _ else _) st₁ = _
      simp only [hke, ↓reduceIte]; rfl
    · by_cases hwrap : ((c == .imm || c == .leaf) && kept.size == 1) = true
      · cases hi0 : kept[0]? with
        | none =>
          left
          show StateT.run (if kept.isEmpty = true then _ else _) st₁ = _
          simp only [hke, Bool.false_eq_true, ↓reduceIte]
          change StateT.run (if ((c == .imm || c == .leaf) && kept.size == 1) = true then _ else _) st₁ = _
          simp only [hwrap, ↓reduceIte]
          rfl
        | some idx =>
          cases hvi : out[idx]? with
          | none =>
            left
            show StateT.run (if kept.isEmpty = true then _ else _) st₁ = _
            simp only [hke, Bool.false_eq_true, ↓reduceIte]
            change StateT.run (if ((c == .imm || c == .leaf) && kept.size == 1) = true then _ else _) st₁ = _
            simp only [hwrap, ↓reduceIte]
            rw [hvi]; rfl
          | some w =>
            have hltw : idx < out.size := (Array.getElem?_eq_some_iff.mp hvi).1
            obtain ⟨f, v, hf, hv, hfv⟩ := hzipAt idx hltw
            obtain ⟨w', hw', hwdl, hwacyc, _, hwreach, _, _, hwdou, _⟩ := hrest idx f v hfv
            simp only [Array.size_empty, Nat.zero_add] at hw'
            rw [hvi] at hw'; cases hw'
            rcases conform_spec_full (P := P) (c := c) hc₁ hwdl hwacyc with hst |
              ⟨rv, st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hpres₂, hc₂, hdl₂, hcls₂,
                hacyc₂, _, hreach₂, _, _, hdou₂⟩
            · left
              show StateT.run (if kept.isEmpty = true then _ else _) st₁ = _
              simp only [hke, Bool.false_eq_true, ↓reduceIte]
              change StateT.run (if ((c == .imm || c == .leaf) && kept.size == 1) = true then _ else _) st₁ = _
              simp only [hwrap, ↓reduceIte]
              rw [hvi]
              exact hst
            · have hcIL : c = .imm ∨ c = .leaf := by
                cases c
                · simp [Bool.and_eq_true] at hwrap
                  exact absurd hwrap.1 (by decide)
                · exact Or.inl rfl
                · exact Or.inr rfl
                · simp [Bool.and_eq_true] at hwrap
                  exact absurd hwrap.1 (by decide)
              have htree₂ : OwnTreeFull P st₂.heap rv := by
                rcases hcIL with rfl | rfl
                · obtain ⟨i, rfl⟩ := hcls₂; exact OwnTreeFull_imm P _ _
                · obtain ⟨loc, cap, o, n, rfl, ho, hcell, _⟩ := hcls₂
                  exact OwnTreeFull_num ho hcell
              have hpres12 : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₂.heap :=
                fun l hlt => (hpres₂ l (Nat.lt_of_lt_of_le hlt hsz₁)).trans (hpres₁ l hlt)
              right
              refine ⟨rv, st₂, ?_,
                hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
                Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hpres12, hc₂,
                OldSameShape.of_preserves_old (Nat.le_trans hsz₁ hsz₂) hpres12,
                hdl₂, hacyc₂,
                (fun rs A hdu => hdou₂ rs A (hwdou rs A (fun hfk => hdu idx f v hf hv hfk))),
                (fun l hl => by
                  rcases hreach₂ l hl with hge | hrw
                  · exact Or.inl (Nat.le_trans hsz₁ hge)
                  · rcases hwreach l hrw with hge | ⟨hfk, hrv⟩
                    · exact Or.inl hge
                    · exact Or.inr ⟨idx, f, v, hf, hv, hfk, hrv⟩),
                (fun h => by subst h; trivial),
                Or.inr (Or.inl ⟨hcIL, hcls₂⟩),
                (fun _ _ _ => htree₂)⟩
              show StateT.run (if kept.isEmpty = true then _ else _) st₁ = _
              simp only [hke, Bool.false_eq_true, ↓reduceIte]
              change StateT.run (if ((c == .imm || c == .leaf) && kept.size == 1) = true then _ else _) st₁ = _
              simp only [hwrap, ↓reduceIte]
              rw [hvi]
              exact hrun₂
      · -- Allocate `.ctor r out`
        let locNew := st₁.heap.objs.size
        let capNew := st₁.heap.nextCap
        let st₂ : St := { st₁ with heap := { objs := st₁.heap.objs.push ⟨.ctor r out, capNew⟩,
                                             nextCap := capNew + 1 } }
        have hpres12 : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
          alloc_preserves_old (.ctor r out) (taints out.toList) st₁
        have hsz12 : st₁.heap.objs.size ≤ st₂.heap.objs.size := by simp [st₂]
        have hpres02 : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₂.heap :=
          fun l hlt => (hpres12 l (Nat.lt_of_lt_of_le hlt hsz₁)).trans (hpres₁ l hlt)
        have hsub : ∀ u ∈ (Cell.ctor r out).vals, DeepLive st₁.heap u ∧ AcyclicFrom st₁.heap u :=
          fun u hu => hall u hu
        right
        refine ⟨.ref locNew capNew (taints out.toList), st₂, ?_,
          hr₁, hnr₁, hst₁, hstr₁,
          Nat.le_trans hsz₁ hsz12, Nat.le_trans hcap₁ (Nat.le_succ _),
          hpres02, alloc_capsOk hc₁,
          OldSameShape.of_preserves_old (Nat.le_trans hsz₁ hsz12) hpres02,
          alloc_deepLive (c := .ctor r out) (t := taints out.toList) (fun u hu => (hsub u hu).1) (Or.inl rfl),
          alloc_acyclicFrom (c := .ctor r out) (t := taints out.toList) hsub,
          ?_, ?_, (fun h => by subst h; trivial),
          Or.inr (Or.inr ⟨locNew, capNew, out, rfl, by simp [st₂, locNew], hsz₁,
            by simp [st₂, locNew], hszMin⟩),
          ?_⟩
        · show StateT.run (if kept.isEmpty = true then _ else _) st₁ = _
          simp only [hke, Bool.false_eq_true, ↓reduceIte]
          change StateT.run (if ((c == .imm || c == .leaf) && kept.size == 1) = true then _ else _) st₁ = _
          simp only [hwrap, Bool.false_eq_true, ↓reduceIte]
          rw [alloc_run]
        · intro rs A hdu
          have hsubDOU : ∀ u ∈ (Cell.ctor r out).vals, DeepLive st₁.heap u ∧ DeepOpenUnder st₁.heap rs A u := by
            intro u hu
            simp only [Cell.vals] at hu
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
            have hlt : k < out.size := by simpa [Array.length_toList] using hk
            obtain ⟨f, v, hf, hv, hfv⟩ := hzipAt k hlt
            obtain ⟨w, hw, hwdl, _, _, _, _, _, hwdou, _⟩ := hrest k f v hfv
            simp only [Array.size_empty, Nat.zero_add, Array.getElem?_eq_getElem hlt, Option.some.injEq] at hw
            subst hw
            exact ⟨hwdl, hwdou rs A (fun hfk => hdu k f v hf hv hfk)⟩
          have htOpen : ∀ x ∈ taints out.toList, x ∈ rs → x ∈ A := by
            intro x hx hopen
            obtain ⟨u, hu, hxu⟩ := (mem_taints (vs := out.toList)).mp hx
            exact (hsubDOU u hu).2.self x hxu hopen
          exact alloc_deepOpenUnder (c := .ctor r out) (t := taints out.toList) hsubDOU htOpen
        · intro l hl
          rcases (Reach_alloc_new (c := .ctor r out) (t := taints out.toList)
            (fun u hu => (hsub u hu).1)).mp hl with rfl | ⟨u, hu, hru⟩
          · exact Or.inl hsz₁
          · simp only [Cell.vals] at hu
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
            have hlt : k < out.size := by simpa [Array.length_toList] using hk
            obtain ⟨f, v, hf, hv, hfv⟩ := hzipAt k hlt
            obtain ⟨w, hw, _, _, _, hwreach, _, _, _, _⟩ := hrest k f v hfv
            simp only [Array.size_empty, Nat.zero_add, Array.getElem?_eq_getElem hlt, Option.some.injEq] at hw
            subst hw
            rcases hwreach l hru with hge | ⟨hfk, hrv⟩
            · exact Or.inl hge
            · exact Or.inr ⟨k, f, v, hf, hv, hfk, hrv⟩
        · intro ⟨ind, tag, nP, hctor⟩ hown hdisj
          have hownedIff : ∀ i, i ∈ ownedSlots P (.ctor r out) →
              ∃ f v, fields[i]? = some f ∧ vs[i]? = some v ∧ (fields.toList.zip vs)[i]? = some (f, v) ∧
                f.fmode = .inherited := by
            intro i hi
            simp only [ownedSlots, hctor, List.mem_filter, List.mem_range] at hi
            obtain ⟨f, v, hf, hv, hfv⟩ := hzipAt i hi.1
            have hinh : f.fmode = .inherited := by
              rw [hf] at hi
              simpa using hi.2
            exact ⟨f, v, hf, hv, hfv, hinh⟩
          have hdisjSlot : ∀ {i j wi wj l},
              i ∈ ownedSlots P (.ctor r out) → i ≠ j →
              out[i]? = some wi → out[j]? = some wj →
              OwnReach P st₁.heap wi l → ¬ Reach st₁.heap wj l := by
            intro i j wi wj l hi hne hsi hsj hori hrj
            obtain ⟨fi, vi, hfi, hvi, hfvi, hinh⟩ := hownedIff i hi
            obtain ⟨wi', hwi', _, _, _, _, howni, _, _, _⟩ := hrest i fi vi hfvi
            simp only [Array.size_empty, Nat.zero_add] at hwi'
            rw [hsi] at hwi'; cases hwi'
            obtain ⟨hfki, hor0⟩ := howni l hori
            have hltL : l < st.heap.objs.size :=
              Reach_lt_size (hvs i fi vi hfi hvi hfki).1 (OwnReach_toReach hor0)
            have hltj : j < out.size := (Array.getElem?_eq_some_iff.mp hsj).1
            obtain ⟨fj, vj, hfj, hvj, hfvj⟩ := hzipAt j hltj
            obtain ⟨wj', hwj', _, _, _, hreachj, _, _, _, _⟩ := hrest j fj vj hfvj
            simp only [Array.size_empty, Nat.zero_add] at hwj'
            rw [hsj] at hwj'; cases hwj'
            rcases hreachj l hrj with hge | ⟨hfkj, hr0⟩
            · omega
            · exact hdisj i j fi vi fj vj hne hfi hvi hfj hvj hfki hfkj hinh l hor0 hr0
          refine alloc_ownTreeFull (P := P) (c := .ctor r out) (t := taints out.toList)
            hsub (Or.inl rfl) ?_ ?_ ?_
          · intro i hi w hs
            obtain ⟨f, v, hf, hv, hfv, hinh⟩ := hownedIff i hi
            obtain ⟨w', hw', _, _, _, _, _, hwtree, _, hwnk⟩ := hrest i f v hfv
            simp only [Array.size_empty, Nat.zero_add] at hw'
            simp only [Cell.slot?] at hs
            rw [hs] at hw'; cases hw'
            cases hfk : f.kept with
            | false => rw [hwnk hfk]; exact OwnTreeFull_imm P _ _
            | true => exact hwtree hfk (hown i f v hf hv hfk hinh)
          · intro i j wi wj hi _ hne hsi hsj l hori
            exact hdisjSlot hi hne hsi hsj hori
          · intro r' fs i wi hcEq hi hsi j hj wj hsj l horj
            cases hcEq
            have hne : j ≠ i := fun h => hi (h ▸ hj)
            exact hdisjSlot hj hne hsj hsi horj

/-! ## 6. `makePap_spec` (`Eval.makePap`) -/

/-- Explicit list recursion matching `Eval.makePap`'s `for (v, i) in vs.zipIdx` loop. -/
def makePapLoop (P : Prog) (fuel : Nat) (params : Array Param) :
    List (Val × Nat) → Array Val → M (Array Val)
  | [], out => pure out
  | (v, i) :: rest, out =>
    let m : BinderMode := (params[i]?.map Param.mode).getD BinderMode.many
    (if captureTransfers m = true then transfer P fuel m.isBorrowed v else pure v) >>= fun v' =>
      makePapLoop P fuel params rest (out.push v')

theorem forIn_list_makePapLoop (P : Prog) (fuel : Nat) (params : Array Param)
    (xs : List (Val × Nat)) (out : Array Val) (st : St) :
    (forIn (m := M) xs out (fun vi acc => do
        let m : BinderMode := (params[vi.2]?.map Param.mode).getD BinderMode.many
        let v' ← if captureTransfers m then transfer P fuel m.isBorrowed vi.1 else pure vi.1
        pure (ForInStep.yield (acc.push v')))).run st =
      (makePapLoop P fuel params xs out).run st := by
  induction xs generalizing out st with
  | nil => rfl
  | cons vi rest ih =>
    rcases vi with ⟨v, i⟩
    simp only [List.forIn_cons]
    unfold makePapLoop
    dsimp only
    rw [M_bind_run, M_bind_run]
    cases hc : captureTransfers ((params[i]?.map Param.mode).getD BinderMode.many) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [M_bind_run, M_pure_run]
      dsimp only
      rw [M_pure_run]
      dsimp only
      exact ih (out.push v) st
    · rw [M_bind_run]
      cases (transfer P fuel (((params[i]?.map Param.mode).getD BinderMode.many).isBorrowed) v).run st with
      | error e => rfl
      | ok p =>
        dsimp only
        rw [M_pure_run]
        exact ih (out.push p.1) p.2

theorem makePapLoop_spec {P : Prog} {fuel : Nat} {params : Array Param}
    {xs : List (Val × Nat)} {out : Array Val} {st : St}
    (hc : CapsOk st.heap)
    (hout : ∀ w ∈ out.toList, DeepLive st.heap w ∧ AcyclicFrom st.heap w)
    (hxs : ∀ vi ∈ xs, DeepLive st.heap vi.1 ∧ AcyclicFrom st.heap vi.1)
    (huniq : ∀ vi ∈ xs,
      ((params[vi.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
      OwnTreeFull P st.heap vi.1 ∧
      (((params[vi.2]?.map Param.mode).getD BinderMode.many).isBorrowed = false → OpenUnder st.regions [] vi.1))
    (hdisjOut : ∀ vi ∈ xs,
      ((params[vi.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ w ∈ out.toList, ∀ l, OwnReach P st.heap vi.1 l → ¬ Reach st.heap w l)
    (hdisjXs : ∀ (a b : Nat) (va vb : Val) (ia ib : Nat), a ≠ b →
      xs[a]? = some (va, ia) → xs[b]? = some (vb, ib) →
      ((params[ia]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ l, OwnReach P st.heap va l → ¬ Reach st.heap vb l) :
    (makePapLoop P fuel params xs out).run st = .error .outOfFuel ∨
    ∃ out' st', (makePapLoop P fuel params xs out).run st = .ok (out', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      HeapSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => ∀ vi ∈ xs, ((params[vi.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
          ¬ OwnReach P st.heap vi.1 l)
        st.heap st'.heap ∧
      out'.size = out.size + xs.length ∧
      (∀ i, i < out.size → out'[i]? = out[i]?) ∧
      (∀ w ∈ out'.toList, DeepLive st'.heap w ∧ AcyclicFrom st'.heap w) ∧
      (∀ (k : Nat) (v : Val) (idx : Nat), xs[k]? = some (v, idx) →
        ∃ w, out'[out.size + k]? = some w ∧ ValSameShape v w ∧
          DeepLive st'.heap w ∧ AcyclicFrom st'.heap w) := by
  induction xs generalizing out st with
  | nil =>
    right
    refine ⟨out, st, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
      HeapSameShape.refl _, PreservesLocs.refl _ _, by simp, fun _ _ => rfl, hout, ?_⟩
    intro k _ _ hk; simp at hk
  | cons vi rest ih =>
    rcases vi with ⟨v, idx⟩
    let m : BinderMode := (params[idx]?.map Param.mode).getD BinderMode.many
    have hstep1 :
        (if captureTransfers m = true then transfer P fuel m.isBorrowed v else pure v).run st = .error .outOfFuel ∨
        ∃ v' st₁,
          (if captureTransfers m = true then transfer P fuel m.isBorrowed v else pure v).run st = .ok (v', st₁) ∧
          st₁.regions = st.regions ∧ st₁.nextRegion = st.nextRegion ∧
          st₁.statics = st.statics ∧ st₁.strs = st.strs ∧
          st₁.heap.objs.size = st.heap.objs.size ∧ st.heap.nextCap ≤ st₁.heap.nextCap ∧
          CapsOk st₁.heap ∧ HeapSameShape st.heap st₁.heap ∧ ValSameShape v v' ∧
          DeepLive st₁.heap v' ∧ AcyclicFrom st₁.heap v' ∧
          PreservesLocs (fun l => m.isUnique = true → ¬ OwnReach P st.heap v l) st.heap st₁.heap := by
      have hv0 := hxs (v, idx) List.mem_cons_self
      cases hu : m.isUnique with
      | false =>
        have hct : captureTransfers m = false := hu
        right
        refine ⟨v, st, by simp [hct]; rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
          HeapSameShape.refl _, ValSameShape.refl _, hv0.1, hv0.2, PreservesLocs.refl _ _⟩
      | true =>
        have hct : captureTransfers m = true := hu
        have hu0 := huniq (v, idx) List.mem_cons_self hu
        rcases transfer_spec (fuel := fuel) hc hv0.1 hv0.2 hu0.1 hu0.2 with hOOF |
          ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hh₁, hv₁, hdl₁, hpres₁⟩
        · exact Or.inl (by simp only [hct, ↓reduceIte]; exact hOOF)
        · right
          exact ⟨v', st₁, (by simp only [hct, ↓reduceIte]; exact hrun₁), hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁,
            hh₁, hv₁, hdl₁, AcyclicFrom_of_sameShape hh₁ hv₁ hv0.2,
            fun l hl => hpres₁ l (hl rfl)⟩
    rcases hstep1 with hOOF |
      ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hh₁, hv₁, hdl₁, hacyc₁, hpres₁⟩
    · left
      unfold makePapLoop; dsimp only; rw [M_bind_run, hOOF]
    -- Helper: every `w ∈ out.toList` is preserved across `st → st₁`
    have hpresOut : ∀ w ∈ out.toList, PreservesLocs (Reach st.heap w) st.heap st₁.heap := by
      intro w hw l hrl
      exact hpres₁ l (fun hu hor => hdisjOut (v, idx) List.mem_cons_self hu w hw l hor hrl)
    have hpresRest : ∀ vi' ∈ rest, PreservesLocs (Reach st.heap vi'.1) st.heap st₁.heap := by
      intro vi' hmem l hrl
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
      refine hpres₁ l (fun hu hor => ?_)
      have h0 : ((v, idx) :: rest)[0]? = some (v, idx) := rfl
      have hk' : ((v, idx) :: rest)[k + 1]? = some rest[k] := by
        simp [List.getElem?_eq_getElem hk]
      exact hdisjXs 0 (k + 1) v rest[k].1 idx rest[k].2 (Nat.zero_ne_add_one k) h0 hk' hu l hor hrl
    have hout₁ : ∀ w ∈ (out.push v').toList, DeepLive st₁.heap w ∧ AcyclicFrom st₁.heap w := by
      intro w hw
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have hw0 := hout w hw
        exact ⟨(DeepLive_congr (hpresOut w hw)).mpr hw0.1,
               (AcyclicFrom_congr (hpresOut w hw)).mpr hw0.2⟩
      · exact ⟨hdl₁, hacyc₁⟩
    have hxs₁ : ∀ vi' ∈ rest, DeepLive st₁.heap vi'.1 ∧ AcyclicFrom st₁.heap vi'.1 := by
      intro vi' hmem
      have h0 := hxs vi' (List.mem_cons_of_mem (v, idx) hmem)
      exact ⟨(DeepLive_congr (hpresRest vi' hmem)).mpr h0.1,
             (AcyclicFrom_congr (hpresRest vi' hmem)).mpr h0.2⟩
    have huniq₁ : ∀ vi' ∈ rest,
        ((params[vi'.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
        OwnTreeFull P st₁.heap vi'.1 ∧
        (((params[vi'.2]?.map Param.mode).getD BinderMode.many).isBorrowed = false → OpenUnder st₁.regions [] vi'.1) := by
      intro vi' hmem hu
      have h0 := huniq vi' (List.mem_cons_of_mem (v, idx) hmem) hu
      exact ⟨(OwnTreeFull_congr (hpresRest vi' hmem)).mpr h0.1, by rw [hr₁]; exact h0.2⟩
    have hdisjOut₁ : ∀ vi' ∈ rest,
        ((params[vi'.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
        ∀ w ∈ (out.push v').toList, ∀ l, OwnReach P st₁.heap vi'.1 l → ¬ Reach st₁.heap w l := by
      intro vi' hmem hu w hw l hor hrw
      have hor0 := (OwnReach_congr (hpresRest vi' hmem) l).mp hor
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hdisjOut vi' (List.mem_cons_of_mem (v, idx) hmem) hu w hw l hor0
          ((Reach_congr (hpresOut w hw) l).mp hrw)
      · have hrv0 : Reach st.heap v l := (Reach_iff_sameShape hh₁ hv₁ l).mpr hrw
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
        have h0 : ((v, idx) :: rest)[0]? = some (v, idx) := rfl
        have hk' : ((v, idx) :: rest)[k + 1]? = some rest[k] := by
          simp [List.getElem?_eq_getElem hk]
        exact hdisjXs (k + 1) 0 rest[k].1 v rest[k].2 idx (Nat.succ_ne_zero k) hk' h0 hu l hor0 hrv0
    have hdisjXs₁ : ∀ (a b : Nat) (va vb : Val) (ia ib : Nat), a ≠ b →
        rest[a]? = some (va, ia) → rest[b]? = some (vb, ib) →
        ((params[ia]?.map Param.mode).getD BinderMode.many).isUnique = true →
        ∀ l, OwnReach P st₁.heap va l → ¬ Reach st₁.heap vb l := by
      intro a b va vb ia ib hne ha hb hu l hor hrb
      have hma : (va, ia) ∈ rest := List.mem_of_getElem? ha
      have hmb : (vb, ib) ∈ rest := List.mem_of_getElem? hb
      have hor0 := (OwnReach_congr (hpresRest (va, ia) hma) l).mp hor
      have hrb0 := (Reach_congr (hpresRest (vb, ib) hmb) l).mp hrb
      have hne' : a + 1 ≠ b + 1 := fun h => hne (Nat.succ.inj h)
      exact hdisjXs (a + 1) (b + 1) va vb ia ib hne' (by simpa using ha) (by simpa using hb) hu l hor0 hrb0
    rcases ih hc₁ hout₁ hxs₁ huniq₁ hdisjOut₁ hdisjXs₁ with hOOF |
      ⟨out', st', hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc', hh₂, hpres₂,
        hszOut, hold, hall, hrest⟩
    · left
      unfold makePapLoop; dsimp only; rw [M_bind_run, hrun₁]; exact hOOF
    · right
      have hpresAll : PreservesLocs
          (fun l => ∀ vi' ∈ (v, idx) :: rest, ((params[vi'.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
            ¬ OwnReach P st.heap vi'.1 l)
          st.heap st'.heap := by
        intro l hl
        have hl1 : ∀ vi' ∈ rest, ((params[vi'.2]?.map Param.mode).getD BinderMode.many).isUnique = true →
            ¬ OwnReach P st₁.heap vi'.1 l := by
          intro vi' hmem hu hor1
          exact hl vi' (List.mem_cons_of_mem (v, idx) hmem) hu
            ((OwnReach_congr (hpresRest vi' hmem) l).mp hor1)
        exact (hpres₂ l hl1).trans (hpres₁ l (fun hu => hl (v, idx) List.mem_cons_self hu))
      refine ⟨out', st', ?_,
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        hsz₂.trans hsz₁, Nat.le_trans hcap₁ hcap₂, hc', hh₁.trans hh₂, hpresAll,
        (by rw [hszOut]; simp only [Array.size_push, List.length_cons]; omega),
        (fun i hi => by
          have hi' : i < (out.push v').size := by simp; omega
          rw [hold i hi', Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]),
        hall, ?_⟩
      · unfold makePapLoop; dsimp only; rw [M_bind_run, hrun₁]; exact hrun₂
      · intro k vk ik hk
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
          rcases hk with ⟨rfl, rfl⟩
          have hget : out'[out.size + 0]? = some v' := by
            have hlt : out.size < (out.push v').size := by simp
            simpa using (hold out.size hlt).trans (by simp)
          have hpw : PreservesLocs (Reach st₁.heap v') st₁.heap st'.heap := by
            intro l hrl
            refine hpres₂ l (fun vi' hmem hu hor1 => ?_)
            exact hdisjOut₁ vi' hmem hu v' (by simp) l hor1 hrl
          exact ⟨v', hget, hv₁,
            (DeepLive_congr hpw).mpr hdl₁,
            (AcyclicFrom_congr hpw).mpr hacyc₁⟩
        | succ k' =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨w, hwget, hwsh, hwdl, hwacyc⟩ := hrest k' vk ik hk
          have hidx : (out.push v').size + k' = out.size + (k' + 1) := by simp; omega
          rw [hidx] at hwget
          exact ⟨w, hwget, hwsh, hwdl, hwacyc⟩

/-- Soundness and framing for `Eval.makePap`. -/
theorem makePap_spec {P : Prog} {fuel : Nat} {r : Ref} {params : Array Param}
    {vs : List Val} {st : St}
    (hc : CapsOk st.heap)
    (hvs : ∀ v ∈ vs, DeepLive st.heap v ∧ AcyclicFrom st.heap v)
    (huniq : ∀ (i : Nat) (v : Val), vs[i]? = some v →
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      OwnTreeFull P st.heap v ∧
      (((params[i]?.map Param.mode).getD BinderMode.many).isBorrowed = false → OpenUnder st.regions [] v))
    (hdisj : ∀ (i j : Nat) (vi vj : Val), i ≠ j →
      vs[i]? = some vi → vs[j]? = some vj →
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) :
    (makePap P fuel r params vs).run st = .error .outOfFuel ∨
    ∃ rv out st', (makePap P fuel r params vs).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size + 1 ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧
          ∀ (i : Nat) (v : Val), vs[i]? = some v →
            ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true → ¬ OwnReach P st.heap v l)
        st.heap st'.heap ∧
      (∃ cap, rv = .ref st.heap.objs.size cap (taints out.toList) ∧
        st'.heap.objs[st.heap.objs.size]? = some ⟨.pap r out, cap⟩) ∧
      out.size = vs.length ∧
      (∀ (i : Nat) (v : Val), vs[i]? = some v →
        ∃ w, out[i]? = some w ∧ ValSameShape v w) ∧
      (∀ x, x ∈ rv.taint ↔ ∃ v ∈ vs, x ∈ v.taint) ∧
      DeepLive st'.heap rv ∧
      AcyclicFrom st'.heap rv ∧
      ((∀ v ∈ vs, OwnTreeFull P st.heap v) →
        (∀ (i j : Nat) (vi vj : Val), i ≠ j → vs[i]? = some vi → vs[j]? = some vj →
          ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) →
        OwnTreeFull P st'.heap rv) ∧
      (∀ rs A, (∀ v ∈ vs, DeepOpenUnder st.heap rs A v) → DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l → l = st.heap.objs.size ∨ ∃ v ∈ vs, Reach st.heap v l) := by
  have hzipMem : ∀ vi ∈ vs.zipIdx, vs[vi.2]? = some vi.1 := by
    intro vi hmem
    obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hmem
    have hlt : k < vs.length := by simpa [List.length_zipIdx] using hk
    rw [List.getElem_zipIdx] at heq
    have h2 : vi.2 = k := by simpa using (congrArg Prod.snd heq).symm
    have h1 : vi.1 = vs[k] := by simpa using (congrArg Prod.fst heq).symm
    rw [h2, h1, List.getElem?_eq_getElem hlt]
  have hzipGet : ∀ (k : Nat) (v : Val) (i : Nat),
      vs.zipIdx[k]? = some (v, i) → i = k ∧ vs[k]? = some v := by
    intro k v i hk
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hk
    have hlt' : k < vs.length := by simpa [List.length_zipIdx] using hlt
    rw [List.getElem_zipIdx] at heq
    simp only [Nat.zero_add, Prod.mk.injEq] at heq
    exact ⟨heq.2.symm, by rw [List.getElem?_eq_getElem hlt', heq.1]⟩
  unfold makePap
  rw [M_bind_run]
  erw [forIn_list_makePapLoop]
  rcases makePapLoop_spec (P := P) (fuel := fuel) (params := params) (out := #[]) hc
    (by simp)
    (fun vi hmem => hvs vi.1 (List.mem_of_getElem? (hzipMem vi hmem)))
    (fun vi hmem hu => huniq vi.2 vi.1 (hzipMem vi hmem) hu)
    (by simp)
    (fun a b va vb ia ib hne ha hb hu => by
      obtain ⟨rfl, hva⟩ := hzipGet a va ia ha
      obtain ⟨rfl, hvb⟩ := hzipGet b vb ib hb
      exact hdisj ia ib va vb hne hva hvb hu) with hOOF |
    ⟨out, st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hh₁, hpres₁,
      hszOut, _, hall, hrest⟩
  · left; rw [hOOF]
  · right
    have houtSz : out.size = vs.length := by simpa [List.length_zipIdx] using hszOut
    have houtEach : ∀ (i : Nat) (v : Val), vs[i]? = some v →
        ∃ w, out[i]? = some w ∧ ValSameShape v w ∧ DeepLive st₁.heap w ∧ AcyclicFrom st₁.heap w := by
      intro i v hi
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hi
      have hzi : vs.zipIdx[i]? = some (v, i) := by
        have hltz : i < vs.zipIdx.length := by simpa [List.length_zipIdx] using hlt
        rw [List.getElem?_eq_getElem hltz, List.getElem_zipIdx]
        simp [heq]
      obtain ⟨w, hw, hwsh, hwdl, hwacyc⟩ := hrest i v i hzi
      exact ⟨w, by simpa using hw, hwsh, hwdl, hwacyc⟩
    let capNew := st₁.heap.nextCap
    let st₂ : St := { st₁ with heap := { objs := st₁.heap.objs.push ⟨.pap r out, capNew⟩,
                                         nextCap := capNew + 1 } }
    have hpres12 : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
      alloc_preserves_old (.pap r out) (taints out.toList) st₁
    have hsz12 : st₁.heap.objs.size ≤ st₂.heap.objs.size := by simp [st₂]
    have hsub : ∀ u ∈ (Cell.pap r out).vals, DeepLive st₁.heap u ∧ AcyclicFrom st₁.heap u :=
      fun u hu => hall u hu
    have htIff : ∀ x, x ∈ taints out.toList ↔ ∃ v ∈ vs, x ∈ v.taint := by
      intro x
      rw [mem_taints]
      constructor
      · rintro ⟨w, hw, hxw⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
        have hlt : i < vs.length := by simpa [Array.length_toList, houtSz] using hi
        obtain ⟨w', hw', hwsh, _, _⟩ := houtEach i vs[i] (List.getElem?_eq_getElem hlt)
        have hltOut : i < out.size := houtSz ▸ hlt
        rw [Array.getElem?_eq_getElem hltOut, Option.some.injEq] at hw'
        subst hw'
        exact ⟨vs[i], List.getElem_mem hlt, hwsh.taint_eq.symm ▸ hxw⟩
      · rintro ⟨v, hv, hxv⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
        obtain ⟨w, hw, hwsh, _, _⟩ := houtEach i vs[i] (List.getElem?_eq_getElem hi)
        exact ⟨w, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw), hwsh.taint_eq ▸ hxv⟩
    refine ⟨.ref st.heap.objs.size capNew (taints out.toList), out, st₂, ?_,
      hr₁, hnr₁, hst₁, hstr₁,
      by simp [st₂, hsz₁], Nat.le_trans hcap₁ (Nat.le_succ _),
      alloc_capsOk hc₁,
      (OldSameShape.of_heapSameShape hh₁).trans (OldSameShape.of_preserves_old hsz12 hpres12),
      ?_, ⟨capNew, rfl, by rw [← hsz₁]; simp [st₂]⟩, houtSz,
      (fun i v hi => let ⟨w, hw, hwsh, _, _⟩ := houtEach i v hi; ⟨w, hw, hwsh⟩),
      htIff,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrun₁]; dsimp only; rw [alloc_run, hsz₁]
    · intro l ⟨hlt, hno⟩
      have h1 : st₁.heap.objs[l]? = st.heap.objs[l]? :=
        hpres₁ l (fun vi hmem hu => hno vi.2 vi.1 (hzipMem vi hmem) hu)
      exact (hpres12 l (hsz₁.symm ▸ hlt)).trans h1
    · simpa [hsz₁] using alloc_deepLive (c := .pap r out) (t := taints out.toList)
        (fun u hu => (hsub u hu).1) (Or.inl rfl)
    · simpa [hsz₁] using alloc_acyclicFrom (c := .pap r out) (t := taints out.toList) hsub
    · intro hownAll hpairAll
      have hownSlot : ∀ i ∈ ownedSlots P (.pap r out), ∀ w,
          (Cell.pap r out).slot? i = some w → OwnTreeFull P st₁.heap w := by
        intro i _ w hs
        simp only [Cell.slot?] at hs
        have hltOut : i < out.size := (Array.getElem?_eq_some_iff.mp hs).1
        have hlt : i < vs.length := houtSz ▸ hltOut
        obtain ⟨w', hw', hwsh, _, _⟩ := houtEach i vs[i] (List.getElem?_eq_getElem hlt)
        rw [hs] at hw'; cases hw'
        exact OwnTreeFull_of_sameShape hh₁ hwsh (hownAll vs[i] (List.getElem_mem hlt))
      have hpairSlot : ∀ i j wi wj, i ∈ ownedSlots P (.pap r out) →
          j ∈ ownedSlots P (.pap r out) → i ≠ j →
          (Cell.pap r out).slot? i = some wi → (Cell.pap r out).slot? j = some wj →
          ∀ l, OwnReach P st₁.heap wi l → ¬ Reach st₁.heap wj l := by
        intro i j wi wj _ _ hne hsi hsj l hor hrl
        simp only [Cell.slot?] at hsi hsj
        have hlti : i < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hsi).1
        have hltj : j < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hsj).1
        obtain ⟨wi', hwi', hwshi, _, _⟩ := houtEach i vs[i] (List.getElem?_eq_getElem hlti)
        obtain ⟨wj', hwj', hwshj, _, _⟩ := houtEach j vs[j] (List.getElem?_eq_getElem hltj)
        rw [hsi] at hwi'; cases hwi'
        rw [hsj] at hwj'; cases hwj'
        exact hpairAll i j vs[i] vs[j] hne (List.getElem?_eq_getElem hlti)
          (List.getElem?_eq_getElem hltj) l
          ((OwnReach_iff_sameShape hh₁ hwshi l).mpr hor)
          ((Reach_iff_sameShape hh₁ hwshj l).mpr hrl)
      simpa [hsz₁] using alloc_ownTreeFull (P := P) (c := .pap r out) (t := taints out.toList)
        hsub (Or.inl rfl) hownSlot hpairSlot (fun _ _ _ _ h => by cases h)
    · intro rs A hdu
      have hsubDOU : ∀ u ∈ (Cell.pap r out).vals, DeepLive st₁.heap u ∧ DeepOpenUnder st₁.heap rs A u := by
        intro u hu
        simp only [Cell.vals] at hu
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
        have hlt : i < vs.length := by simpa [Array.length_toList, houtSz] using hi
        obtain ⟨w, hw, hwsh, hwdl, _⟩ := houtEach i vs[i] (List.getElem?_eq_getElem hlt)
        have hltOut : i < out.size := houtSz ▸ hlt
        rw [Array.getElem?_eq_getElem hltOut, Option.some.injEq] at hw
        subst hw
        exact ⟨hwdl, DeepOpenUnder_of_sameShape hh₁ hwsh (hdu vs[i] (List.getElem_mem hlt))⟩
      have htOpen : ∀ x ∈ taints out.toList, x ∈ rs → x ∈ A := by
        intro x hx hopen
        obtain ⟨v, hv, hxv⟩ := (htIff x).mp hx
        exact (hdu v hv).self x hxv hopen
      simpa [hsz₁] using alloc_deepOpenUnder (c := .pap r out) (t := taints out.toList) hsubDOU htOpen
    · intro l hl
      have hl' : Reach st₂.heap (.ref st₁.heap.objs.size capNew (taints out.toList)) l :=
        hsz₁.symm ▸ hl
      rcases (Reach_alloc_new (c := .pap r out) (t := taints out.toList)
        (fun u hu => (hsub u hu).1)).mp hl' with rfl | ⟨u, hu, hru⟩
      · exact Or.inl hsz₁
      · simp only [Cell.vals] at hu
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
        have hlt : i < vs.length := by simpa [Array.length_toList, houtSz] using hi
        obtain ⟨w, hw, hwsh, _, _⟩ := houtEach i vs[i] (List.getElem?_eq_getElem hlt)
        have hltOut : i < out.size := houtSz ▸ hlt
        rw [Array.getElem?_eq_getElem hltOut, Option.some.injEq] at hw
        subst hw
        exact Or.inr ⟨vs[i], List.getElem_mem hlt, (Reach_iff_sameShape hh₁ hwsh l).mpr hru⟩

/-! ## 7. `formClosure_spec` (`Eval.formClosure`) -/

/-- Explicit list recursion matching `Eval.formClosure`'s `for i in fvs.toList` loop. -/
def formClosureLoop (P : Prog) (fuel : Nat) (env : List Bnd) :
    List Nat → List Bnd × List Nat → M (List Bnd × List Nat)
  | [], acc => pure acc
  | i :: rest, (env', taint) =>
    match env[i]? with
    | none => stuckM
    | some b =>
      if (b.mode == .erased) = true then violate .erasedRead
      else
        live b.val >>= fun _ =>
        (if captureTransfers b.mode = true then transfer P fuel b.mode.isBorrowed b.val else pure b.val) >>= fun v =>
        formClosureLoop P fuel env rest (setBnd env' i v, natUnion taint v.taint)

theorem forIn_list_formClosureLoop (P : Prog) (fuel : Nat) (env : List Bnd)
    (xs : List Nat) (acc : List Bnd × List Nat) (st : St) :
    (forIn (m := M) xs acc (fun i r => do
        let some b := env[i]? | stuckM
        if b.mode == .erased then violate .erasedRead
        live b.val
        let v ← if captureTransfers b.mode then transfer P fuel b.mode.isBorrowed b.val else pure b.val
        pure (ForInStep.yield (setBnd r.1 i v, natUnion r.2 v.taint)))).run st =
      (formClosureLoop P fuel env xs acc).run st := by
  induction xs generalizing acc st with
  | nil => rfl
  | cons i rest ih =>
    rcases acc with ⟨env', taint⟩
    simp only [List.forIn_cons]
    unfold formClosureLoop
    rw [M_bind_run]
    cases hbi : env[i]? with
    | none => rfl
    | some b =>
      dsimp only
      cases her : (b.mode == .erased) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, M_bind_run]
        cases (live b.val).run st with
        | error e => rfl
        | ok pl =>
          dsimp only
          cases hct : captureTransfers b.mode <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · rw [M_bind_run, M_bind_run, M_pure_run]
            dsimp only
            rw [M_pure_run]
            dsimp only
            exact ih (setBnd env' i b.val, natUnion taint b.val.taint) pl.2
          · rw [M_bind_run, M_bind_run]
            cases (transfer P fuel b.mode.isBorrowed b.val).run pl.2 with
            | error e => rfl
            | ok pt =>
              dsimp only
              rw [M_pure_run]
              exact ih (setBnd env' i pt.1, natUnion taint pt.1.taint) pt.2

theorem formClosureLoop_spec {P : Prog} {fuel : Nat} {env : List Bnd}
    {xs prev : List Nat} {env' : List Bnd} {taint : List Nat} {st : St}
    (hc : CapsOk st.heap)
    (hprev : ∀ j ∈ prev, ∃ b v', env[j]? = some b ∧ env'[j]? = some { b with val := v' } ∧
      ValSameShape b.val v' ∧ DeepLive st.heap v' ∧ AcyclicFrom st.heap v')
    (hother : ∀ j, j ∉ prev → env'[j]? = env[j]?)
    (hxs : ∀ i ∈ xs, ∀ b, env[i]? = some b →
      b.mode ≠ .erased ∧ DeepLive st.heap b.val ∧ AcyclicFrom st.heap b.val ∧
      (b.mode.isUnique = true →
        OwnTreeFull P st.heap b.val ∧ (b.mode.isBorrowed = false → OpenUnder st.regions [] b.val)))
    (hdisjPrev : ∀ i ∈ xs, ∀ bi, env[i]? = some bi → bi.mode.isUnique = true →
      ∀ j ∈ prev, ∀ bj v', env[j]? = some bj → env'[j]? = some { bj with val := v' } →
        ∀ l, OwnReach P st.heap bi.val l → ¬ Reach st.heap v' l)
    (hdisjXs : ∀ (a b : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ b →
      xs[a]? = some ia → xs[b]? = some ib →
      env[ia]? = some ba → env[ib]? = some bb →
      ba.mode.isUnique = true →
      ∀ l, OwnReach P st.heap ba.val l → ¬ Reach st.heap bb.val l) :
    (formClosureLoop P fuel env xs (env', taint)).run st = .error .stuck ∨
    (formClosureLoop P fuel env xs (env', taint)).run st = .error .outOfFuel ∨
    ∃ env'' taint' st', (formClosureLoop P fuel env xs (env', taint)).run st = .ok ((env'', taint'), st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      HeapSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => ∀ i ∈ xs, ∀ b, env[i]? = some b → b.mode.isUnique = true →
          ¬ OwnReach P st.heap b.val l)
        st.heap st'.heap ∧
      (∀ j ∈ prev ++ xs, ∃ b v', env[j]? = some b ∧ env''[j]? = some { b with val := v' } ∧
        ValSameShape b.val v' ∧ DeepLive st'.heap v' ∧ AcyclicFrom st'.heap v') ∧
      (∀ j, j ∉ xs → env''[j]? = env'[j]?) ∧
      (∀ x, x ∈ taint' ↔ x ∈ taint ∨ ∃ i ∈ xs, ∃ b, env[i]? = some b ∧ x ∈ b.val.taint) := by
  induction xs generalizing prev env' taint st with
  | nil =>
    right; right
    refine ⟨env', taint, st, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
      HeapSameShape.refl _, PreservesLocs.refl _ _,
      (by simpa using hprev), (fun _ _ => rfl), (by simp)⟩
  | cons idx rest ih =>
    cases hbi : env[idx]? with
    | none =>
      left
      unfold formClosureLoop; rw [hbi]; rfl
    | some b =>
      obtain ⟨hner, hdlb, hacycb, huniqb⟩ := hxs idx List.mem_cons_self b hbi
      have hbeqEr : (b.mode == .erased) = false := beq_false_of_ne hner
      have hstep1 :
          (if captureTransfers b.mode = true then transfer P fuel b.mode.isBorrowed b.val else pure b.val).run st = .error .outOfFuel ∨
          ∃ v' st₁,
            (if captureTransfers b.mode = true then transfer P fuel b.mode.isBorrowed b.val else pure b.val).run st = .ok (v', st₁) ∧
            st₁.regions = st.regions ∧ st₁.nextRegion = st.nextRegion ∧
            st₁.statics = st.statics ∧ st₁.strs = st.strs ∧
            st₁.heap.objs.size = st.heap.objs.size ∧ st.heap.nextCap ≤ st₁.heap.nextCap ∧
            CapsOk st₁.heap ∧ HeapSameShape st.heap st₁.heap ∧ ValSameShape b.val v' ∧
            DeepLive st₁.heap v' ∧ AcyclicFrom st₁.heap v' ∧
            PreservesLocs (fun l => b.mode.isUnique = true → ¬ OwnReach P st.heap b.val l) st.heap st₁.heap := by
        cases hu : b.mode.isUnique with
        | false =>
          have hct : captureTransfers b.mode = false := hu
          right
          refine ⟨b.val, st, by simp [hct]; rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
            HeapSameShape.refl _, ValSameShape.refl _, hdlb, hacycb, PreservesLocs.refl _ _⟩
        | true =>
          have hct : captureTransfers b.mode = true := hu
          have hu0 := huniqb hu
          rcases transfer_spec (fuel := fuel) hc hdlb hacycb hu0.1 hu0.2 with hOOF |
            ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hh₁, hv₁, hdl₁, hpres₁⟩
          · exact Or.inl (by simp [hct, hOOF])
          · right
            exact ⟨v', st₁, by simp [hct, hrun₁], hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁,
              hh₁, hv₁, hdl₁, AcyclicFrom_of_sameShape hh₁ hv₁ hacycb,
              fun l hl => hpres₁ l (hl rfl)⟩
      rcases hstep1 with hOOF |
        ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hh₁, hv₁, hdl₁, hacyc₁, hpres₁⟩
      · right; left
        unfold formClosureLoop
        rw [hbi]; dsimp only
        simp only [hbeqEr, Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, live_ok hdlb.self.1]; dsimp only
        rw [M_bind_run, hOOF]
      have hsetIdx : (setBnd env' idx v')[idx]? = some { b with val := v' } := by
        by_cases hmem : idx ∈ prev
        · obtain ⟨b0, w0, hb0, he0, _, _, _⟩ := hprev idx hmem
          rw [hbi] at hb0; cases hb0
          simpa using setBnd_getElem?_same (v := v') he0
        · have he0 : env'[idx]? = some b := (hother idx hmem).trans hbi
          exact setBnd_getElem?_same (v := v') he0
      have hpresRest : ∀ i ∈ rest, ∀ bi, env[i]? = some bi →
          PreservesLocs (Reach st.heap bi.val) st.heap st₁.heap := by
        intro i hmem bi hbi' l hrl
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
        refine hpres₁ l (fun hu hor => ?_)
        have h0 : (idx :: rest)[0]? = some idx := rfl
        have hk' : (idx :: rest)[k + 1]? = some rest[k] := by
          simp [List.getElem?_eq_getElem hk]
        exact hdisjXs 0 (k + 1) idx rest[k] b bi (Nat.zero_ne_add_one k) h0 hk' hbi hbi' hu l hor hrl
      have hprev₁ : ∀ j ∈ idx :: prev, ∃ bj w, env[j]? = some bj ∧
          (setBnd env' idx v')[j]? = some { bj with val := w } ∧
          ValSameShape bj.val w ∧ DeepLive st₁.heap w ∧ AcyclicFrom st₁.heap w := by
        intro j hj
        by_cases hji : j = idx
        · subst hji
          exact ⟨b, v', hbi, hsetIdx, hv₁, hdl₁, hacyc₁⟩
        · have hjPrev : j ∈ prev := (List.mem_cons.mp hj).resolve_left hji
          obtain ⟨bj, w, hbj, hej, hwsh, hwdl, hwacyc⟩ := hprev j hjPrev
          have hpw : PreservesLocs (Reach st.heap w) st.heap st₁.heap := by
            intro l hrl
            exact hpres₁ l (fun hu hor =>
              hdisjPrev idx List.mem_cons_self b hbi hu j hjPrev bj w hbj hej l hor hrl)
          exact ⟨bj, w, hbj, by rw [setBnd_getElem?_other hji, hej], hwsh,
            (DeepLive_congr hpw).mpr hwdl, (AcyclicFrom_congr hpw).mpr hwacyc⟩
      have hother₁ : ∀ j, j ∉ idx :: prev → (setBnd env' idx v')[j]? = env[j]? := by
        intro j hj
        have hne : j ≠ idx := fun h => hj (h ▸ List.mem_cons_self)
        have hnp : j ∉ prev := fun h => hj (List.mem_cons_of_mem _ h)
        rw [setBnd_getElem?_other hne]
        exact hother j hnp
      have hxs₁ : ∀ i ∈ rest, ∀ bi, env[i]? = some bi →
          bi.mode ≠ .erased ∧ DeepLive st₁.heap bi.val ∧ AcyclicFrom st₁.heap bi.val ∧
          (bi.mode.isUnique = true →
            OwnTreeFull P st₁.heap bi.val ∧
            (bi.mode.isBorrowed = false → OpenUnder st₁.regions [] bi.val)) := by
        intro i hi bi hbi'
        obtain ⟨hner', hdl', hacyc', hu'⟩ := hxs i (List.mem_cons_of_mem _ hi) bi hbi'
        have hp := hpresRest i hi bi hbi'
        refine ⟨hner', (DeepLive_congr hp).mpr hdl', (AcyclicFrom_congr hp).mpr hacyc', fun hui => ?_⟩
        obtain ⟨hot, hop⟩ := hu' hui
        exact ⟨(OwnTreeFull_congr hp).mpr hot, fun hnb => hr₁.symm ▸ hop hnb⟩
      have hdisjPrev₁ : ∀ i ∈ rest, ∀ bi, env[i]? = some bi → bi.mode.isUnique = true →
          ∀ j ∈ idx :: prev, ∀ bj w, env[j]? = some bj →
            (setBnd env' idx v')[j]? = some { bj with val := w } →
            ∀ l, OwnReach P st₁.heap bi.val l → ¬ Reach st₁.heap w l := by
        intro i hi bi hbi' hui j hj bj w hbj he' l hor hrl
        have horOld : OwnReach P st.heap bi.val l :=
          (OwnReach_iff_sameShape hh₁ (ValSameShape.refl _) l).mpr hor
        by_cases hji : j = idx
        · subst hji
          rw [hbi] at hbj; cases hbj
          rw [hsetIdx] at he'
          have hwv : v' = w := congrArg Bnd.val (Option.some.inj he')
          subst hwv
          have hrlOld : Reach st.heap b.val l := (Reach_iff_sameShape hh₁ hv₁ l).mpr hrl
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
          have hk' : (j :: rest)[k + 1]? = some rest[k] := by
            simp [List.getElem?_eq_getElem hk]
          exact hdisjXs (k + 1) 0 rest[k] j bi b (Nat.succ_ne_zero k) hk' rfl hbi' hbi hui l horOld hrlOld
        · have hjPrev : j ∈ prev := (List.mem_cons.mp hj).resolve_left hji
          rw [setBnd_getElem?_other hji] at he'
          have hrlOld : Reach st.heap w l := (Reach_iff_sameShape hh₁ (ValSameShape.refl _) l).mpr hrl
          exact hdisjPrev i (List.mem_cons_of_mem _ hi) bi hbi' hui j hjPrev bj w hbj he' l horOld hrlOld
      have hdisjXs₁ : ∀ (a b : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ b →
          rest[a]? = some ia → rest[b]? = some ib →
          env[ia]? = some ba → env[ib]? = some bb →
          ba.mode.isUnique = true →
          ∀ l, OwnReach P st₁.heap ba.val l → ¬ Reach st₁.heap bb.val l := by
        intro a b' ia ib ba bb hne ha hb hba hbb hua l hor hrl
        exact hdisjXs (a + 1) (b' + 1) ia ib ba bb (fun h => hne (Nat.succ.inj h))
          (by simpa using ha) (by simpa using hb) hba hbb hua l
          ((OwnReach_iff_sameShape hh₁ (ValSameShape.refl _) l).mpr hor)
          ((Reach_iff_sameShape hh₁ (ValSameShape.refl _) l).mpr hrl)
      have hrunStep :
          (formClosureLoop P fuel env (idx :: rest) (env', taint)).run st =
          (formClosureLoop P fuel env rest (setBnd env' idx v', natUnion taint v'.taint)).run st₁ := by
        conv => lhs; unfold formClosureLoop
        rw [hbi]; dsimp only
        simp only [hbeqEr, Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, live_ok hdlb.self.1]; dsimp only
        rw [M_bind_run, hrun₁]
      rcases ih hc₁ hprev₁ hother₁ hxs₁ hdisjPrev₁ hdisjXs₁ with hStuck | hOOF2 |
        ⟨env'', taint', st', hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc₂, hh₂,
          hpres₂, hprev₂, hnotRest, htaint₂⟩
      · left; rw [hrunStep, hStuck]
      · right; left; rw [hrunStep, hOOF2]
      · right; right
        refine ⟨env'', taint', st', by rw [hrunStep, hrun₂],
          hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
          hsz₂.trans hsz₁, Nat.le_trans hcap₁ hcap₂, hc₂,
          hh₁.trans hh₂, ?_, ?_, ?_, ?_⟩
        · intro l hl
          have h1 : st₁.heap.objs[l]? = st.heap.objs[l]? :=
            hpres₁ l (fun hu => hl idx List.mem_cons_self b hbi hu)
          have h2 : st'.heap.objs[l]? = st₁.heap.objs[l]? := by
            refine hpres₂ l (fun i hi bi hbi' hui hor => ?_)
            exact hl i (List.mem_cons_of_mem _ hi) bi hbi' hui
              ((OwnReach_iff_sameShape hh₁ (ValSameShape.refl _) l).mpr hor)
          exact h2.trans h1
        · intro j hj
          have hj' : j ∈ (idx :: prev) ++ rest := by
            simp only [List.mem_append, List.mem_cons] at hj ⊢
            rcases hj with hp | rfl | hr
            · exact Or.inl (Or.inr hp)
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr hr
          exact hprev₂ j hj'
        · intro j hj
          have hne : j ≠ idx := fun h => hj (h ▸ List.mem_cons_self)
          have hnr : j ∉ rest := fun h => hj (List.mem_cons_of_mem _ h)
          rw [hnotRest j hnr, setBnd_getElem?_other hne]
        · intro x
          rw [htaint₂, mem_natUnion, ← hv₁.taint_eq]
          constructor
          · rintro ((hx | hxb) | ⟨i, hi, bi, hbi', hxbi⟩)
            · exact Or.inl hx
            · exact Or.inr ⟨idx, List.mem_cons_self, b, hbi, hxb⟩
            · exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, bi, hbi', hxbi⟩
          · rintro (hx | ⟨i, hi, bi, hbi', hxbi⟩)
            · exact Or.inl (Or.inl hx)
            · rcases List.mem_cons.mp hi with rfl | hi'
              · rw [hbi] at hbi'; cases hbi'
                exact Or.inl (Or.inr hxbi)
              · exact Or.inr ⟨i, hi', bi, hbi', hxbi⟩

/-- Soundness & framing of `Eval.formClosure`. -/
theorem formClosure_spec {P : Prog} {fuel : Nat} {env : List Bnd}
    {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term} {st : St}
    (hc : CapsOk st.heap)
    (hfvs : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b →
      b.mode ≠ .erased ∧ DeepLive st.heap b.val ∧ AcyclicFrom st.heap b.val ∧
      (b.mode.isUnique = true →
        OwnTreeFull P st.heap b.val ∧ (b.mode.isBorrowed = false → OpenUnder st.regions [] b.val)))
    (hdisj : ∀ (a b : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ b →
      fvs.toList[a]? = some ia → fvs.toList[b]? = some ib →
      env[ia]? = some ba → env[ib]? = some bb →
      ba.mode.isUnique = true →
      ∀ l, OwnReach P st.heap ba.val l → ¬ Reach st.heap bb.val l) :
    (formClosure P fuel env p res rc fvs body).run st = .error .stuck ∨
    (formClosure P fuel env p res rc fvs body).run st = .error .outOfFuel ∨
    ∃ rv env' taint st',
      (formClosure P fuel env p res rc fvs body).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size + 1 ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧
          ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → b.mode.isUnique = true →
            ¬ OwnReach P st.heap b.val l)
        st.heap st'.heap ∧
      (∃ cap, rv = .ref st.heap.objs.size cap taint ∧
        st'.heap.objs[st.heap.objs.size]? = some ⟨.clo env' p res rc fvs body, cap⟩) ∧
      (∀ i ∈ fvs.toList, ∃ b v', env[i]? = some b ∧ env'[i]? = some { b with val := v' } ∧
        ValSameShape b.val v' ∧ DeepLive st'.heap v' ∧ AcyclicFrom st'.heap v') ∧
      (∀ j, j ∉ fvs.toList → env'[j]? = env[j]?) ∧
      (∀ x, x ∈ rv.taint ↔ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧ x ∈ b.val.taint) ∧
      DeepLive st'.heap rv ∧
      AcyclicFrom st'.heap rv ∧
      ((∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → OwnTreeFull P st.heap b.val) →
        (∀ i ∈ fvs.toList, ∀ j ∈ fvs.toList, i ≠ j →
          ∀ bi bj, env[i]? = some bi → env[j]? = some bj →
          ∀ l, OwnReach P st.heap bi.val l → ¬ Reach st.heap bj.val l) →
        OwnTreeFull P st'.heap rv) ∧
      (∀ rs A, (∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → DeepOpenUnder st.heap rs A b.val) →
        DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l →
        l = st.heap.objs.size ∨ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧ Reach st.heap b.val l) := by
  unfold formClosure
  rw [M_bind_run]
  erw [forIn_list_formClosureLoop]
  rcases formClosureLoop_spec (P := P) (fuel := fuel) (env := env) (xs := fvs.toList)
    (prev := []) (env' := env) (taint := []) hc
    (by simp) (fun _ _ => rfl) hfvs (by simp) hdisj with hStuck | hOOF |
    ⟨env', taint, st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hh₁,
      hpres₁, hcapEach, hnotFvs, htaint⟩
  · left; rw [hStuck]
  · right; left; rw [hOOF]
  · right; right
    have hcapEach' : ∀ i ∈ fvs.toList, ∃ b v', env[i]? = some b ∧
        env'[i]? = some { b with val := v' } ∧
        ValSameShape b.val v' ∧ DeepLive st₁.heap v' ∧ AcyclicFrom st₁.heap v' := by
      simpa using hcapEach
    have htIff : ∀ x, x ∈ taint ↔ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧ x ∈ b.val.taint := by
      intro x; simpa using htaint x
    let capNew := st₁.heap.nextCap
    let st₂ : St := { st₁ with heap := { objs := st₁.heap.objs.push ⟨.clo env' p res rc fvs body, capNew⟩,
                                         nextCap := capNew + 1 } }
    have hpres12 : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap :=
      alloc_preserves_old (.clo env' p res rc fvs body) taint st₁
    have hsz12 : st₁.heap.objs.size ≤ st₂.heap.objs.size := by simp [st₂]
    have hsub : ∀ u ∈ (Cell.clo env' p res rc fvs body).vals,
        DeepLive st₁.heap u ∧ AcyclicFrom st₁.heap u := by
      intro u hu
      simp only [Cell.vals, List.mem_filterMap] at hu
      obtain ⟨i, hi, hmap⟩ := hu
      obtain ⟨b, v', _, he', _, hdl, hacyc⟩ := hcapEach' i hi
      rw [he'] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      subst hmap
      exact ⟨hdl, hacyc⟩
    refine ⟨.ref st.heap.objs.size capNew taint, env', taint, st₂, ?_,
      hr₁, hnr₁, hst₁, hstr₁,
      by simp [st₂, hsz₁], Nat.le_trans hcap₁ (Nat.le_succ _),
      alloc_capsOk hc₁,
      (OldSameShape.of_heapSameShape hh₁).trans (OldSameShape.of_preserves_old hsz12 hpres12),
      ?_, ⟨capNew, rfl, by rw [← hsz₁]; simp [st₂]⟩, ?_, hnotFvs, htIff, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrun₁]; dsimp only; rw [alloc_run, hsz₁]
    · intro l ⟨hlt, hno⟩
      have h1 : st₁.heap.objs[l]? = st.heap.objs[l]? := hpres₁ l hno
      exact (hpres12 l (hsz₁.symm ▸ hlt)).trans h1
    · intro i hi
      obtain ⟨b, v', hb, he', hvsh, hdl, hacyc⟩ := hcapEach' i hi
      have hpv : PreservesLocs (Reach st₁.heap v') st₁.heap st₂.heap :=
        hpres12.mono (fun x hx => Reach_lt_size hdl hx)
      exact ⟨b, v', hb, he', hvsh, (DeepLive_congr hpv).mpr hdl, (AcyclicFrom_congr hpv).mpr hacyc⟩
    · simpa [hsz₁] using alloc_deepLive (c := .clo env' p res rc fvs body) (t := taint)
        (fun u hu => (hsub u hu).1) (Or.inl rfl)
    · simpa [hsz₁] using alloc_acyclicFrom (c := .clo env' p res rc fvs body) (t := taint) hsub
    · intro hownAll hpairAll
      have hownSlot : ∀ i ∈ ownedSlots P (.clo env' p res rc fvs body), ∀ w,
          (Cell.clo env' p res rc fvs body).slot? i = some w → OwnTreeFull P st₁.heap w := by
        intro i hi w hs
        simp only [ownedSlots] at hi
        obtain ⟨b, v', hb, he', hvsh, _, _⟩ := hcapEach' i hi
        simp only [Cell.slot?, he', Option.map_some, Option.some.injEq] at hs
        subst hs
        exact OwnTreeFull_of_sameShape hh₁ hvsh (hownAll i hi b hb)
      have hpairSlot : ∀ i j wi wj,
          i ∈ ownedSlots P (.clo env' p res rc fvs body) →
          j ∈ ownedSlots P (.clo env' p res rc fvs body) → i ≠ j →
          (Cell.clo env' p res rc fvs body).slot? i = some wi →
          (Cell.clo env' p res rc fvs body).slot? j = some wj →
          ∀ l, OwnReach P st₁.heap wi l → ¬ Reach st₁.heap wj l := by
        intro i j wi wj hi hj hne hsi hsj l hor hrl
        simp only [ownedSlots] at hi hj
        obtain ⟨bi, vi, hbi, hei, hvshi, _, _⟩ := hcapEach' i hi
        obtain ⟨bj, vj, hbj, hej, hvshj, _, _⟩ := hcapEach' j hj
        simp only [Cell.slot?, hei, Option.map_some, Option.some.injEq] at hsi
        simp only [Cell.slot?, hej, Option.map_some, Option.some.injEq] at hsj
        subst hsi; subst hsj
        exact hpairAll i hi j hj hne bi bj hbi hbj l
          ((OwnReach_iff_sameShape hh₁ hvshi l).mpr hor)
          ((Reach_iff_sameShape hh₁ hvshj l).mpr hrl)
      simpa [hsz₁] using alloc_ownTreeFull (P := P) (c := .clo env' p res rc fvs body) (t := taint)
        hsub (Or.inl rfl) hownSlot hpairSlot (fun _ _ _ _ h => by cases h)
    · intro rs A hdu
      have hsubDOU : ∀ u ∈ (Cell.clo env' p res rc fvs body).vals,
          DeepLive st₁.heap u ∧ DeepOpenUnder st₁.heap rs A u := by
        intro u hu
        simp only [Cell.vals, List.mem_filterMap] at hu
        obtain ⟨i, hi, hmap⟩ := hu
        obtain ⟨b, v', hb, he', hvsh, hdl, _⟩ := hcapEach' i hi
        rw [he'] at hmap
        simp only [Option.map_some, Option.some.injEq] at hmap
        subst hmap
        exact ⟨hdl, DeepOpenUnder_of_sameShape hh₁ hvsh (hdu i hi b hb)⟩
      have htOpen : ∀ x ∈ taint, x ∈ rs → x ∈ A := by
        intro x hx hopen
        obtain ⟨i, hi, b, hb, hxb⟩ := (htIff x).mp hx
        exact (hdu i hi b hb).self x hxb hopen
      simpa [hsz₁] using alloc_deepOpenUnder (c := .clo env' p res rc fvs body) (t := taint)
        hsubDOU htOpen
    · intro l hl
      have hl' : Reach st₂.heap (.ref st₁.heap.objs.size capNew taint) l :=
        hsz₁.symm ▸ hl
      rcases (Reach_alloc_new (c := .clo env' p res rc fvs body) (t := taint)
        (fun u hu => (hsub u hu).1)).mp hl' with rfl | ⟨u, hu, hru⟩
      · exact Or.inl hsz₁
      · simp only [Cell.vals, List.mem_filterMap] at hu
        obtain ⟨i, hi, hmap⟩ := hu
        obtain ⟨b, v', hb, he', hvsh, _, _⟩ := hcapEach' i hi
        rw [he'] at hmap
        simp only [Option.map_some, Option.some.injEq] at hmap
        subst hmap
        exact Or.inr ⟨i, hi, b, hb, (Reach_iff_sameShape hh₁ hvsh l).mpr hru⟩

/-! ## 8. `bindParamsM_spec` (`EvalS.bindParamsM`) -/

private theorem ne_erased_of_isUnique {m : BinderMode} (hu : m.isUnique = true) :
    m ≠ .erased := by
  intro h; subst h; simp [BinderMode.isUnique] at hu

/-- Soundness and framing for `EvalS.bindParamsM` (sequential `bindAt` over a list of
parameter-argument pairs, preserving per-binding invariants and pairwise `OwnReach`/`Reach`
disjointness across all resulting bindings). -/
theorem bindParamsM_spec {P : Prog} {fuel s : Nat}
    {xs : List (Param × Val)} {env : List Bnd} {st : St}
    (hc : CapsOk st.heap)
    (hxs : ∀ (i : Nat) (p : Param) (v : Val), xs[i]? = some (p, v) →
      (p.mode ≠ .erased → DeepLive st.heap v ∧ AcyclicFrom st.heap v) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap v ∧ (p.mode.isBorrowed = false → OpenUnder st.regions [] v)))
    (hdisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      xs[i]? = some (pi, vi) → xs[j]? = some (pj, vj) →
      pi.mode.isUnique = true → pj.mode ≠ .erased →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) :
    (bindParamsM P fuel s xs env).run st = .error .stuck ∨
    (bindParamsM P fuel s xs env).run st = .error .outOfFuel ∨
    ∃ (bs : List Bnd) (st' : St), (bindParamsM P fuel s xs env).run st = .ok (bs.reverse ++ env, st') ∧
      bs.length = xs.length ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧
          ∀ (i : Nat) (p : Param) (v : Val), xs[i]? = some (p, v) →
            p.mode.isUnique = true → ¬ OwnReach P st.heap v l)
        st.heap st'.heap ∧
      (∀ (i : Nat) (p : Param) (v : Val) (bnd : Bnd),
        xs[i]? = some (p, v) → bs[i]? = some bnd →
        bnd.mode = p.mode ∧
        DeepLive st'.heap bnd.val ∧
        AcyclicFrom st'.heap bnd.val ∧
        (p.mode.isUnique = true → OwnTreeFull P st'.heap bnd.val) ∧
        (p.mode = .erased → bnd = ⟨.imm .irr, .erased⟩) ∧
        (p.mode ≠ .erased → p.mode.usage ≠ .once → ClsOk st'.heap p.cls bnd.val) ∧
        (p.mode.usage = .once →
          ∃ base loc cap,
            bnd.val = .ref loc cap base.taint ∧
            st.heap.objs.size ≤ loc ∧
            st'.heap.objs[loc]? = some ⟨.once base false, cap⟩ ∧
            DeepLive st'.heap base ∧
            ClsOk st'.heap p.cls base ∧
            AcyclicFrom st'.heap base ∧
            (∀ r ∈ base.taint, r ∈ v.taint ∨ (p.mode.isBorrowed = true ∧ r = s))) ∧
        (∀ r ∈ bnd.val.taint, r ∈ v.taint ∨ (p.mode.isBorrowed = true ∧ r = s)) ∧
        (p.cls = .leaf → bnd.val.taint = []) ∧
        (∀ rs A, (p.mode ≠ .erased → DeepOpenUnder st.heap rs A v) →
          DeepOpenUnder st'.heap rs (if p.mode.isBorrowed then s :: A else A) bnd.val) ∧
        (∀ l, Reach st'.heap bnd.val l → st.heap.objs.size ≤ l ∨ (p.mode ≠ .erased ∧ Reach st.heap v l)) ∧
        (∀ l, OwnReach P st'.heap bnd.val l →
          st.heap.objs.size ≤ l ∨ (p.mode ≠ .erased ∧ OwnReach P st.heap v l))) ∧
      (∀ (i j : Nat) (pi pj : Param) (vi vj : Val) (bi bj : Bnd), i ≠ j →
        xs[i]? = some (pi, vi) → xs[j]? = some (pj, vj) →
        bs[i]? = some bi → bs[j]? = some bj →
        pi.mode.isUnique = true → pj.mode ≠ .erased →
        ∀ l, OwnReach P st'.heap bi.val l → ¬ Reach st'.heap bj.val l) := by
  induction xs generalizing env st with
  | nil =>
    right; right
    refine ⟨[], st, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, hc,
      OldSameShape.refl _, PreservesLocs.refl _ _, ?_, ?_⟩
    · intro i _ _ _ hi; simp at hi
    · intro i _ _ _ _ _ _ _ _ hi; simp at hi
  | cons pv rest ih =>
    rcases pv with ⟨p, v⟩
    have h0 := hxs 0 p v rfl
    rcases bindAt_spec (P := P) (fuel := fuel) (s := s) (m := p.mode) (c := p.cls) (v := v) hc
      (fun h => (h0.1 h).1) (fun h => (h0.1 h).2)
      (fun h => (h0.2 h).1) (fun h => (h0.2 h).2) with hStuck | hOOF |
      ⟨b, st₁, hrun₁, hbMode, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, hoss₁, hpres₁,
        hdl₁, hacyc₁, htree₁, her₁, hcls₁, honce₁, ht₁, hleaf₁, hdou₁, hreach₁, hown₁⟩
    · left
      unfold bindParamsM; rw [M_bind_run, hStuck]
    · right; left
      unfold bindParamsM; rw [M_bind_run, hOOF]
    -- Every non-erased argument in `rest` is preserved across `st → st₁`.
    have hpresRest : ∀ (k : Nat) (pk : Param) (vk : Val), rest[k]? = some (pk, vk) →
        pk.mode ≠ .erased → PreservesLocs (Reach st.heap vk) st.heap st₁.heap := by
      intro k pk vk hk hner l hrl
      have hk0 := hxs (k + 1) pk vk (by simpa using hk)
      have hlt : l < st.heap.objs.size := Reach_lt_size (hk0.1 hner).1 hrl
      refine hpres₁ l ⟨hlt, fun hup hor => ?_⟩
      exact hdisj 0 (k + 1) p pk v vk (Nat.zero_ne_add_one k) rfl (by simpa using hk) hup hner l hor hrl
    have hxs₁ : ∀ (i : Nat) (pi : Param) (vi : Val), rest[i]? = some (pi, vi) →
        (pi.mode ≠ .erased → DeepLive st₁.heap vi ∧ AcyclicFrom st₁.heap vi) ∧
        (pi.mode.isUnique = true →
          OwnTreeFull P st₁.heap vi ∧ (pi.mode.isBorrowed = false → OpenUnder st₁.regions [] vi)) := by
      intro i pi vi hi
      have hi0 := hxs (i + 1) pi vi (by simpa using hi)
      constructor
      · intro hner
        have hp := hpresRest i pi vi hi hner
        exact ⟨(DeepLive_congr hp).mpr (hi0.1 hner).1, (AcyclicFrom_congr hp).mpr (hi0.1 hner).2⟩
      · intro hui
        have hp := hpresRest i pi vi hi (ne_erased_of_isUnique hui)
        exact ⟨(OwnTreeFull_congr hp).mpr (hi0.2 hui).1, fun hnb => hr₁.symm ▸ (hi0.2 hui).2 hnb⟩
    have hdisj₁ : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
        rest[i]? = some (pi, vi) → rest[j]? = some (pj, vj) →
        pi.mode.isUnique = true → pj.mode ≠ .erased →
        ∀ l, OwnReach P st₁.heap vi l → ¬ Reach st₁.heap vj l := by
      intro i j pi pj vi vj hne hi hj hui hnerj l hor hrl
      have hpi := hpresRest i pi vi hi (ne_erased_of_isUnique hui)
      have hpj := hpresRest j pj vj hj hnerj
      exact hdisj (i + 1) (j + 1) pi pj vi vj (fun h => hne (Nat.succ.inj h))
        (by simpa using hi) (by simpa using hj) hui hnerj l
        ((OwnReach_congr hpi l).mp hor) ((Reach_congr hpj l).mp hrl)
    have hrunStep :
        (bindParamsM P fuel s ((p, v) :: rest) env).run st =
        (bindParamsM P fuel s rest (b :: env)).run st₁ := by
      conv => lhs; unfold bindParamsM
      rw [M_bind_run, hrun₁]
    rcases ih (env := b :: env) hc₁ hxs₁ hdisj₁ with hStuck2 | hOOF2 |
      ⟨bsRest, st', hrun₂, hlen₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hc', hoss₂, hpres₂,
        hspec₂, hdisj₂⟩
    · left; rw [hrunStep, hStuck2]
    · right; left; rw [hrunStep, hOOF2]
    · right; right
      -- Every location reachable from `b.val` in `st₁` is preserved across `st₁ → st'`.
      have hpresB : PreservesLocs (Reach st₁.heap b.val) st₁.heap st'.heap := by
        intro l hrl
        have hlt1 : l < st₁.heap.objs.size := Reach_lt_size hdl₁ hrl
        refine hpres₂ l ⟨hlt1, fun k pk vk hk huk hor1 => ?_⟩
        have hnerk : pk.mode ≠ .erased := ne_erased_of_isUnique huk
        have hor0 : OwnReach P st.heap vk l := (OwnReach_congr (hpresRest k pk vk hk hnerk) l).mp hor1
        have hlt0 : l < st.heap.objs.size :=
          Reach_lt_size ((hxs (k + 1) pk vk (by simpa using hk)).1 hnerk).1 (OwnReach_toReach hor0)
        rcases hreach₁ l hrl with hge | ⟨hnerp, hrv⟩
        · omega
        · exact hdisj (k + 1) 0 pk p vk v (Nat.succ_ne_zero k) (by simpa using hk) rfl huk hnerp l hor0 hrv
      have hrevEq : (b :: bsRest).reverse ++ env = bsRest.reverse ++ (b :: env) := by
        simp [List.reverse_cons, List.append_assoc]
      refine ⟨b :: bsRest, st', by rw [hrunStep, hrevEq, hrun₂],
        by simp [hlen₂],
        hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
        Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hc',
        hoss₁.trans hoss₂, ?_, ?_, ?_⟩
      · -- `PreservesLocs` for `st → st'`
        intro l ⟨hlt, hno⟩
        have h1 : st₁.heap.objs[l]? = st.heap.objs[l]? :=
          hpres₁ l ⟨hlt, fun hu => hno 0 p v rfl hu⟩
        have h2 : st'.heap.objs[l]? = st₁.heap.objs[l]? := by
          refine hpres₂ l ⟨Nat.lt_of_lt_of_le hlt hsz₁, fun k pk vk hk huk hor1 => ?_⟩
          have hor0 := (OwnReach_congr (hpresRest k pk vk hk (ne_erased_of_isUnique huk)) l).mp hor1
          exact hno (k + 1) pk vk (by simpa using hk) huk hor0
        exact h2.trans h1
      · -- Per-binding specs in `st'`
        intro i pi vi bnd hi hbs
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi hbs
          rcases hi with ⟨rfl, rfl⟩
          subst hbs
          refine ⟨hbMode,
            (DeepLive_congr hpresB).mpr hdl₁,
            (AcyclicFrom_congr hpresB).mpr hacyc₁,
            fun hu => (OwnTreeFull_congr hpresB).mpr (htree₁ hu),
            fun h => (her₁ h).1,
            fun hner hno => (ClsOk_congr hpresB).mpr (hcls₁ hner hno),
            ?_, ht₁, hleaf₁,
            fun rs A hd => (DeepOpenUnder_congr hpresB).mpr (hdou₁ rs A hd),
            fun l hl => hreach₁ l ((Reach_congr hpresB l).mp hl),
            fun l hl => hown₁ l ((OwnReach_congr hpresB l).mp hl)⟩
          intro honce
          obtain ⟨base, loc, cap, hbv, _, hgeLoc, hoLoc, hdlBase, hclsBase, hacycBase, htBase⟩ :=
            honce₁ honce
          have hrlLoc : Reach st₁.heap b.val loc := by rw [hbv]; exact .here
          have hpresBase : PreservesLocs (Reach st₁.heap base) st₁.heap st'.heap := by
            intro l hrl
            apply hpresB l
            rw [hbv]
            exact .step hoLoc (by simp [Cell.vals]) hrl
          exact ⟨base, loc, cap, hbv, hgeLoc,
            (hpresB loc hrlLoc).trans hoLoc,
            (DeepLive_congr hpresBase).mpr hdlBase,
            (ClsOk_congr hpresBase).mpr hclsBase,
            (AcyclicFrom_congr hpresBase).mpr hacycBase,
            htBase⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hi hbs
          obtain ⟨hm, hdl', hacyc', htree', her', hcls', honce', ht', hleaf', hdou', hreach', hown'⟩ :=
            hspec₂ k pi vi bnd hi hbs
          refine ⟨hm, hdl', hacyc', htree', her', hcls', ?_, ht', hleaf', ?_, ?_, ?_⟩
          · intro honce
            obtain ⟨base, loc, cap, hbv, hgeLoc, hoLoc, hdlBase, hclsBase, hacycBase, htBase⟩ :=
              honce' honce
            exact ⟨base, loc, cap, hbv, Nat.le_trans hsz₁ hgeLoc, hoLoc, hdlBase, hclsBase, hacycBase, htBase⟩
          · intro rs A hd
            exact hdou' rs A (fun hner => (DeepOpenUnder_congr (hpresRest k pi vi hi hner)).mpr (hd hner))
          · intro l hl
            rcases hreach' l hl with hge | ⟨hner, hr1⟩
            · exact Or.inl (Nat.le_trans hsz₁ hge)
            · exact Or.inr ⟨hner, (Reach_congr (hpresRest k pi vi hi hner) l).mp hr1⟩
          · intro l hl
            rcases hown' l hl with hge | ⟨hner, hor1⟩
            · exact Or.inl (Nat.le_trans hsz₁ hge)
            · exact Or.inr ⟨hner, (OwnReach_congr (hpresRest k pi vi hi hner) l).mp hor1⟩
      · -- Pairwise `OwnReach`/`Reach` disjointness across `b :: bsRest` in `st'`
        intro i j pi pj vi vj bi bj hne hi hj hbi hbj hui hnerj l hor hrl
        cases i with
        | zero =>
          cases j with
          | zero => exact absurd rfl hne
          | succ k =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi hbi
            simp only [List.getElem?_cons_succ] at hj hbj
            rcases hi with ⟨rfl, rfl⟩
            subst hbi
            have hor1 : OwnReach P st₁.heap b.val l := (OwnReach_congr hpresB l).mp hor
            have hlt1 : l < st₁.heap.objs.size := Reach_lt_size hdl₁ (OwnReach_toReach hor1)
            have hreachJ := (hspec₂ k pj vj bj hj hbj).2.2.2.2.2.2.2.2.2.2.1 l hrl
            rcases hreachJ with hge1 | ⟨_, hr1⟩
            · omega
            · have hr0 : Reach st.heap vj l := (Reach_congr (hpresRest k pj vj hj hnerj) l).mp hr1
              have hlt0 : l < st.heap.objs.size :=
                Reach_lt_size ((hxs (k + 1) pj vj (by simpa using hj)).1 hnerj).1 hr0
              rcases hown₁ l hor1 with hge0 | ⟨_, hor0⟩
              · omega
              · exact hdisj 0 (k + 1) p pj v vj (Nat.zero_ne_add_one k) rfl (by simpa using hj) hui hnerj l hor0 hr0
        | succ a =>
          cases j with
          | zero =>
            simp only [List.getElem?_cons_succ] at hi hbi
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj hbj
            rcases hj with ⟨rfl, rfl⟩
            subst hbj
            have hrb1 : Reach st₁.heap b.val l := (Reach_congr hpresB l).mp hrl
            have hlt1 : l < st₁.heap.objs.size := Reach_lt_size hdl₁ hrb1
            have hownI := (hspec₂ a pi vi bi hi hbi).2.2.2.2.2.2.2.2.2.2.2 l hor
            rcases hownI with hge1 | ⟨hneri, hor1⟩
            · omega
            · have hor0 : OwnReach P st.heap vi l :=
                (OwnReach_congr (hpresRest a pi vi hi hneri) l).mp hor1
              have hlt0 : l < st.heap.objs.size :=
                Reach_lt_size ((hxs (a + 1) pi vi (by simpa using hi)).1 hneri).1 (OwnReach_toReach hor0)
              rcases hreach₁ l hrb1 with hge0 | ⟨_, hrb0⟩
              · omega
              · exact hdisj (a + 1) 0 pi p vi v (Nat.succ_ne_zero a) (by simpa using hi) rfl hui hnerj l hor0 hrb0
          | succ b' =>
            simp only [List.getElem?_cons_succ] at hi hj hbi hbj
            exact hdisj₂ a b' pi pj vi vj bi bj (fun h => hne (congrArg Nat.succ h))
              hi hj hbi hbj hui hnerj l hor hrl

/-- Equivalence between `Eval.callExtern`'s parameter-binding `forIn` loop and `bindParamsM`
(so `callExtern` can directly reuse `bindParamsM_spec`). -/
theorem forIn_list_bindAtVals_eq_bindParamsM (P : Prog) (fuel s : Nat)
    (xs : List (Param × Val)) (acc : List Val) (env : List Bnd) (st : St)
    (hacc : acc = env.reverse.map (·.val)) :
    (forIn (m := M) xs acc (fun pv bs => do
        pure (ForInStep.yield (bs ++ [(← bindAt P fuel s pv.1.mode pv.1.cls pv.2).val])))).run st =
      ((bindParamsM P fuel s xs env) >>= fun env' => pure (env'.reverse.map (·.val))).run st := by
  induction xs generalizing acc env st with
  | nil =>
    subst hacc
    rfl
  | cons pv rest ih =>
    rcases pv with ⟨p, v⟩
    simp only [List.forIn_cons]
    unfold bindParamsM
    rw [M_bind_run, M_bind_run, M_bind_run, M_bind_run]
    cases (bindAt P fuel s p.mode p.cls v).run st with
    | error e => rfl
    | ok pb =>
      dsimp only
      rw [M_pure_run]
      dsimp only
      conv => rhs; rw [← M_bind_run]
      exact ih (acc ++ [pb.1.val]) (pb.1 :: env) pb.2 (by simp [hacc, List.reverse_cons])

/-! ## 9. `select_spec` (`Eval.select`) -/

/-- Strengthened `readOut` spec preserving exact `imm`/`ref` identity (`SameLoc`), `DeepLive`,
`AcyclicFrom`, `Reach`/`OwnReach`, `OwnTreeFull`, `HeldBy`, and taint bounds. -/
theorem readOut_spec_full {P : Prog} {st : St} {inherit : Bool} {t : List Nat} {v : Val}
    (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v) :
    ∃ v', (readOut inherit t v).run st = .ok (v', st) ∧
      ((∃ i, v = .imm i ∧ v' = .imm i) ∨
       (∃ loc cap t₁ t₂, v = .ref loc cap t₁ ∧ v' = .ref loc cap t₂)) ∧
      DeepLive st.heap v' ∧ AcyclicFrom st.heap v' ∧
      (∀ r ∈ v'.taint, r ∈ v.taint ∨ (inherit = true ∧ r ∈ t)) ∧
      (∀ l, Reach st.heap v' l ↔ Reach st.heap v l) ∧
      (∀ l, OwnReach P st.heap v' l ↔ OwnReach P st.heap v l) ∧
      (OwnTreeFull P st.heap v → OwnTreeFull P st.heap v') ∧
      (∀ w, HeldBy st.heap v' w → w = v' ∨ HeldBy st.heap v w) := by
  have hNonNum : ∀ {loc cap : Nat} {tv : List Nat} {o : Obj},
      st.heap.objs[loc]? = some o → o.cap = cap → o.cell.isNum = false →
      DeepLive st.heap (.ref loc cap tv) → AcyclicFrom st.heap (.ref loc cap tv) →
      ∃ v', (readOut inherit t (.ref loc cap tv)).run st = .ok (v', st) ∧
        ((∃ i, Val.ref loc cap tv = .imm i ∧ v' = .imm i) ∨
         (∃ loc' cap' t₁ t₂, Val.ref loc cap tv = .ref loc' cap' t₁ ∧ v' = .ref loc' cap' t₂)) ∧
        DeepLive st.heap v' ∧ AcyclicFrom st.heap v' ∧
        (∀ r ∈ v'.taint, r ∈ (Val.ref loc cap tv).taint ∨ (inherit = true ∧ r ∈ t)) ∧
        (∀ l, Reach st.heap v' l ↔ Reach st.heap (.ref loc cap tv) l) ∧
        (∀ l, OwnReach P st.heap v' l ↔ OwnReach P st.heap (.ref loc cap tv) l) ∧
        (OwnTreeFull P st.heap (.ref loc cap tv) → OwnTreeFull P st.heap v') ∧
        (∀ w, HeldBy st.heap v' w → w = v' ∨ HeldBy st.heap (.ref loc cap tv) w) := by
    intro loc cap tv o ho hcap hnn hdl' hacyc'
    have hlive : LiveRef st.heap (.ref loc cap tv) := ⟨o, ho, hcap⟩
    cases inherit with
    | false =>
      refine ⟨.ref loc cap tv, ?_, Or.inr ⟨loc, cap, tv, tv, rfl, rfl⟩,
        hdl', hacyc', fun r hr => Or.inl hr, fun _ => Iff.rfl, fun _ => Iff.rfl,
        id, fun _ hw => Or.inr hw⟩
      unfold readOut
      rw [M_bind_run, isLeaf_ok hlive]
      simp only [ho, hnn, Bool.false_eq_true, ↓reduceIte]
      rfl
    | true =>
      obtain ⟨tv1, htv1⟩ := foldl_addTaint_ref t loc cap tv
      have hlu1 : LeafUntainted st.heap (.ref loc cap tv1) := by
        intro o' n ho' hc'
        rw [ho] at ho'; cases ho'
        simp [hc', Cell.isNum] at hnn
      refine ⟨.ref loc cap tv1, ?_, Or.inr ⟨loc, cap, tv, tv1, rfl, rfl⟩,
        DeepLive_ref_taint hdl' hlu1, AcyclicFrom_ref_taint hacyc', ?_,
        fun _ => Reach_ref_taint, fun _ => OwnReach_ref_taint,
        OwnTreeFull_ref_taint, fun _ hw => HeldBy_ref_taint hw⟩
      · unfold readOut
        rw [M_bind_run, isLeaf_ok hlive]
        simp only [ho, hnn, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        rw [M_pure_run, htv1]
      · intro r hr
        have hr' : r ∈ (t.foldl (fun v s => addTaint s v) (.ref loc cap tv)).taint := by
          rw [htv1]; exact hr
        rcases mem_taint_foldl_addTaint hr' with ht | htv
        · exact Or.inr ⟨rfl, ht⟩
        · exact Or.inl htv
  cases v with
  | imm i =>
    refine ⟨.imm i, ?_, Or.inl ⟨i, rfl, rfl⟩, hdl, hacyc, by simp [Val.taint],
      fun _ => Iff.rfl, fun _ => Iff.rfl, id, fun _ hw => Or.inr hw⟩
    unfold readOut
    rw [M_bind_run, isLeaf_ok hdl.self.1]
    cases inherit
    · rfl
    · dsimp only; rw [foldl_addTaint_imm]; rfl
  | ref loc cap tv =>
    obtain ⟨o, ho, hcap⟩ := hdl.self.1
    cases hc : o.cell with
    | num n =>
      have htv : tv = [] := hdl.self.2 o n ho hc
      subst htv
      refine ⟨.ref loc cap [], ?_, Or.inr ⟨loc, cap, [], [], rfl, rfl⟩,
        hdl, hacyc, by simp [Val.taint], fun _ => Iff.rfl, fun _ => Iff.rfl,
        id, fun _ hw => Or.inr hw⟩
      unfold readOut
      rw [M_bind_run, isLeaf_ok hdl.self.1]
      simp only [ho, hc, Cell.isNum, ↓reduceIte]
      rfl
    | ctor _ _ => exact hNonNum ho hcap (by simp [hc, Cell.isNum]) hdl hacyc
    | str _ => exact hNonNum ho hcap (by simp [hc, Cell.isNum]) hdl hacyc
    | clo _ _ _ _ _ _ => exact hNonNum ho hcap (by simp [hc, Cell.isNum]) hdl hacyc
    | pap _ _ => exact hNonNum ho hcap (by simp [hc, Cell.isNum]) hdl hacyc
    | once _ _ => exact hNonNum ho hcap (by simp [hc, Cell.isNum]) hdl hacyc

theorem conform_val_eq {st st' : St} {v v' : Val}
    (h : (conform .val v).run st = .ok (v', st')) : v' = v ∧ st' = st := by
  unfold conform at h; cases h; exact ⟨rfl, rfl⟩

theorem conform_nonval_taint {st' : St} {c : Cls} {v' : Val}
    (hne : c ≠ .val) (hcls : ClsOk st'.heap c v') : v'.taint = [] := by
  cases c with
  | irr => rw [hcls]; rfl
  | imm => obtain ⟨_, rfl⟩ := hcls; rfl
  | leaf => obtain ⟨_, _, _, _, rfl, _⟩ := hcls; rfl
  | val => exact absurd rfl hne

theorem conform_fresh_is_num {st st' : St} {c : Cls} {v v' : Val}
    (hdl : DeepLive st.heap v) (h : (conform c v).run st = .ok (v', st')) :
    ∀ l o, st.heap.objs.size ≤ l → st'.heap.objs[l]? = some o → ∃ n, o.cell = .num n := by
  cases c with
  | irr =>
    unfold conform at h; cases h
    intro l o hge ho
    have hlt := (Array.getElem?_eq_some_iff.mp ho).1
    omega
  | val =>
    unfold conform at h; cases h
    intro l o hge ho
    have hlt := (Array.getElem?_eq_some_iff.mp ho).1
    omega
  | imm =>
    unfold conform at h
    cases v with
    | imm i =>
      cases h
      intro l o hge ho
      have hlt := (Array.getElem?_eq_some_iff.mp ho).1
      omega
    | ref loc cap t =>
      rw [M_bind_run, numOf?_ok hdl.self.1] at h
      dsimp only at h
      split at h <;> cases h
      intro l o hge ho
      have hlt := (Array.getElem?_eq_some_iff.mp ho).1
      omega
  | leaf =>
    unfold conform at h
    cases v with
    | imm i =>
      cases i with
      | irr | con _ => cases h
      | bits n =>
        rw [alloc_run] at h; cases h
        intro l o hge ho
        by_cases heq : l = st.heap.objs.size
        · subst heq
          simp only [Array.getElem?_push_size, Option.some.injEq] at ho
          subst ho; exact ⟨n, rfl⟩
        · have hlt := (Array.getElem?_eq_some_iff.mp ho).1
          simp only [Array.size_push] at hlt
          omega
    | ref loc cap t =>
      rw [M_bind_run, numOf?_ok hdl.self.1] at h
      dsimp only at h
      split at h <;> cases h
      intro l o hge ho
      have hlt := (Array.getElem?_eq_some_iff.mp ho).1
      omega

/-- Fields array looked up by `Eval.select` for constructor index `ci` of inductive `k.ind`. -/
def selectFieldsOf (P : Prog) (k : CaseInfo) (ci : Nat) : Array Field :=
  match (P.ctorsOf k.ind)[ci]? with
  | some c => match P.ctorOf? c with
    | some (_, _, _, fs) => fs
    | none => #[]
  | none => #[]

/-- Explicit list recursion matching `Eval.select`'s `.ctor` field-reading loop. -/
def selectFieldsLoop (t : List Nat) (fs : Array Val) :
    List (Field × Nat) → Array (Val × Bool) → M (Array (Val × Bool))
  | [], out => pure out
  | (f, i) :: rest, out =>
    readOut (f.fmode == .inherited) t (fs[i]?.getD (.imm .irr)) >>= fun v₁ =>
    (if f.kept = true then conform f.cls v₁ else pure (.imm .irr)) >>= fun v₂ =>
    selectFieldsLoop t fs rest (out.push (v₂, f.mode == .erased))

theorem forIn_list_selectFieldsLoop (t : List Nat) (fs : Array Val)
    (xs : List (Field × Nat)) (out : Array (Val × Bool)) (st : St) :
    (forIn (m := M) xs out (fun fi acc => do
        let v ← readOut (fi.1.fmode == .inherited) t (fs[fi.2]?.getD (.imm .irr))
        let v ← if fi.1.kept then conform fi.1.cls v else pure (.imm .irr)
        pure (ForInStep.yield (acc.push (v, fi.1.mode == .erased))))).run st =
      (selectFieldsLoop t fs xs out).run st := by
  induction xs generalizing out st with
  | nil => rfl
  | cons fi rest ih =>
    rcases fi with ⟨f, i⟩
    simp only [List.forIn_cons]
    unfold selectFieldsLoop
    rw [M_bind_run, M_bind_run, M_bind_run]
    cases (readOut (f.fmode == .inherited) t (fs[i]?.getD (.imm .irr))).run st with
    | error e => rfl
    | ok p₁ =>
      dsimp only
      cases hk : f.kept <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [M_bind_run, M_bind_run, M_pure_run]
        dsimp only
        rw [M_pure_run]
        dsimp only
        exact ih (out.push (.imm .irr, f.mode == .erased)) p₁.2
      · rw [M_bind_run, M_bind_run]
        cases (conform f.cls p₁.1).run p₁.2 with
        | error e => rfl
        | ok p₂ =>
          dsimp only
          rw [M_pure_run]
          exact ih (out.push (p₂.1, f.mode == .erased)) p₂.2

theorem selectFieldsLoop_spec {P : Prog} {t : List Nat} {fs : Array Val}
    {xs : List (Field × Nat)} {out : Array (Val × Bool)} {st : St}
    (hc : CapsOk st.heap)
    (hfs : ∀ w ∈ fs.toList, DeepLive st.heap w ∧ AcyclicFrom st.heap w) :
    (selectFieldsLoop t fs xs out).run st = .error .stuck ∨
    ∃ out' st', (selectFieldsLoop t fs xs out).run st = .ok (out', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      (∀ l o, st.heap.objs.size ≤ l → st'.heap.objs[l]? = some o → ∃ n, o.cell = .num n) ∧
      out'.size = out.size + xs.length ∧
      (∀ i, i < out.size → out'[i]? = out[i]?) ∧
      (∀ (k : Nat) (f : Field) (idx : Nat), xs[k]? = some (f, idx) →
        let raw := fs[idx]?.getD (.imm .irr)
        ∃ v, out'[out.size + k]? = some (v, f.mode == .erased) ∧
          (f.kept = false → v = .imm .irr) ∧
          (f.kept = true →
            (f.cls = .val →
              (∃ imm, raw = .imm imm ∧ v = .imm imm) ∨
              (∃ loc' cap' t₁ t₂, raw = .ref loc' cap' t₁ ∧ v = .ref loc' cap' t₂)) ∧
            ClsOk st'.heap f.cls v ∧
            DeepLive st'.heap v ∧
            AcyclicFrom st'.heap v ∧
            (∀ r' ∈ v.taint, r' ∈ raw.taint ∨ (f.fmode = .inherited ∧ r' ∈ t)) ∧
            (f.cls ≠ .val → v.taint = []) ∧
            (∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l ∨ Reach st.heap raw l) ∧
            (∀ w, HeldBy st'.heap v w → w = v ∨ HeldBy st.heap raw w) ∧
            (∀ l, OwnReach P st'.heap v l → OwnReach P st.heap raw l) ∧
            (OwnTreeFull P st.heap raw → OwnTreeFull P st'.heap v) ∧
            (∀ rs A, DeepOpenUnder st.heap rs A raw →
              (f.fmode = .inherited → ∀ r' ∈ t, r' ∈ rs → r' ∈ A) →
              DeepOpenUnder st'.heap rs A v))) := by
  induction xs generalizing out st with
  | nil =>
    right
    refine ⟨out, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, OldSameShape.refl _, ?_, by simp, fun _ _ => rfl, ?_⟩
    · intro l o hge ho; have := (Array.getElem?_eq_some_iff.mp ho).1; omega
    · intro k _ _ hk; simp at hk
  | cons fi rest ih =>
    rcases fi with ⟨f, idx⟩
    let raw := fs[idx]?.getD (.imm .irr)
    have hrawDA : DeepLive st.heap raw ∧ AcyclicFrom st.heap raw := by
      dsimp only [raw]
      cases hget : fs[idx]? with
      | none => exact ⟨DeepLive_imm st.heap .irr, AcyclicFrom_imm st.heap .irr⟩
      | some w => exact hfs w (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget))
    obtain ⟨v₁, hro, hsame₁, hdl₁, hacyc₁, ht₁, hreach₁, hown₁, htree₁, hheld₁⟩ :=
      readOut_spec_full (P := P) (inherit := (f.fmode == .inherited)) (t := t) hrawDA.1 hrawDA.2
    have hstep2 :
        (if f.kept = true then conform f.cls v₁ else pure (.imm .irr)).run st = .error .stuck ∨
        ∃ v₂ st₁,
          (if f.kept = true then conform f.cls v₁ else pure (.imm .irr)).run st = .ok (v₂, st₁) ∧
          st₁.regions = st.regions ∧ st₁.nextRegion = st.nextRegion ∧
          st₁.statics = st.statics ∧ st₁.strs = st.strs ∧
          st.heap.objs.size ≤ st₁.heap.objs.size ∧ st.heap.nextCap ≤ st₁.heap.nextCap ∧
          PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₁.heap ∧
          CapsOk st₁.heap ∧
          (∀ l o, st.heap.objs.size ≤ l → st₁.heap.objs[l]? = some o → ∃ n, o.cell = .num n) ∧
          (f.kept = false → v₂ = .imm .irr) ∧
          (f.kept = true →
            (f.cls = .val →
              (∃ imm, raw = .imm imm ∧ v₂ = .imm imm) ∨
              (∃ loc' cap' t₁ t₂, raw = .ref loc' cap' t₁ ∧ v₂ = .ref loc' cap' t₂)) ∧
            ClsOk st₁.heap f.cls v₂ ∧
            DeepLive st₁.heap v₂ ∧
            AcyclicFrom st₁.heap v₂ ∧
            (∀ r' ∈ v₂.taint, r' ∈ raw.taint ∨ (f.fmode = .inherited ∧ r' ∈ t)) ∧
            (f.cls ≠ .val → v₂.taint = []) ∧
            (∀ l, Reach st₁.heap v₂ l → st.heap.objs.size ≤ l ∨ Reach st.heap raw l) ∧
            (∀ w, HeldBy st₁.heap v₂ w → w = v₂ ∨ HeldBy st.heap raw w) ∧
            (∀ l, OwnReach P st₁.heap v₂ l → OwnReach P st.heap raw l) ∧
            (OwnTreeFull P st.heap raw → OwnTreeFull P st₁.heap v₂) ∧
            (∀ rs A, DeepOpenUnder st.heap rs A raw →
              (f.fmode = .inherited → ∀ r' ∈ t, r' ∈ rs → r' ∈ A) →
              DeepOpenUnder st₁.heap rs A v₂)) := by
      cases hkept : f.kept with
      | false =>
        right
        refine ⟨.imm .irr, st, (by simp; rfl), rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
          PreservesLocs.refl _ _, hc,
          (fun l o hge ho => by have := (Array.getElem?_eq_some_iff.mp ho).1; omega),
          (fun _ => rfl), (fun h => by cases h)⟩
      | true =>
        rcases conform_spec_full (P := P) (c := f.cls) hc hdl₁ hacyc₁ with hStuck |
          ⟨v₂, st₁, hconf, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁,
            hdl₂, hcls₂, hacyc₂, ht₂, hreach₂, hown₂, htree₂, hdou₂⟩
        · exact Or.inl (by simp [hStuck])
        · have hheld₂ : ∀ w, HeldBy st₁.heap v₂ w → w = v₂ ∨ HeldBy st.heap v₁ w := by
            rcases conform_spec (c := f.cls) hc hdl₁ hacyc₁ with hStuck' |
              ⟨v₂', st₁', hconf', _, _, _, _, _, _, _, _, _, _, _, _, _, hheld'⟩
            · rw [hconf] at hStuck'; cases hStuck'
            · rw [hconf] at hconf'; cases hconf'; exact hheld'
          right
          refine ⟨v₂, st₁, by simp [hconf], hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁,
            conform_fresh_is_num hdl₁ hconf, (fun h => by cases h), fun _ => ?_⟩
          refine ⟨?_, hcls₂, hdl₂, hacyc₂, ?_, fun hne => conform_nonval_taint hne hcls₂,
            ?_, ?_, ?_, fun htr => htree₂ (htree₁ htr), ?_⟩
          · intro hval
            rw [hval] at hconf
            obtain ⟨rfl, _⟩ := conform_val_eq hconf
            exact hsame₁
          · intro r' hr'
            rcases ht₁ r' (ht₂ r' hr') with hraw | ⟨hinh, hrt⟩
            · exact Or.inl hraw
            · exact Or.inr ⟨beq_iff_eq.mp hinh, hrt⟩
          · intro l hl
            rcases hreach₂ l hl with hge | hr1
            · exact Or.inl hge
            · exact Or.inr ((hreach₁ l).mp hr1)
          · intro w hw
            rcases hheld₂ w hw with rfl | hw1
            · exact Or.inl rfl
            · rcases hheld₁ w hw1 with rfl | hwRaw
              · by_cases heq : w = v₂
                · exact Or.inl heq
                · exact False.elim (by
                    cases hc' : f.cls with
                    | val =>
                      rw [hc'] at hconf; obtain ⟨rfl, _⟩ := conform_val_eq hconf
                      exact heq rfl
                    | irr =>
                      rw [hc'] at hcls₂; rw [hcls₂] at hw
                      rcases hw with rfl | ⟨_, _, hr, _, _⟩
                      · exact heq hcls₂.symm
                      · cases hr
                    | imm =>
                      rw [hc'] at hcls₂; obtain ⟨_, hveq⟩ := hcls₂; rw [hveq] at hw
                      rcases hw with rfl | ⟨_, _, hr, _, _⟩
                      · exact heq hveq.symm
                      · cases hr
                    | leaf =>
                      rw [hc'] at hcls₂
                      obtain ⟨loc', cap', o', n', hveq, ho', hnum', _⟩ := hcls₂
                      rw [hveq] at hw
                      rcases hw with rfl | ⟨l', ol', hr', hol', hm'⟩
                      · exact heq hveq.symm
                      · cases hr' with
                        | here => rw [ho'] at hol'; cases hol'; rw [hnum'] at hm'; cases hm'
                        | step ho1 hm1 _ => rw [ho'] at ho1; cases ho1; rw [hnum'] at hm1; cases hm1)
              · exact Or.inr hwRaw
          · intro l hl
            exact (hown₁ l).mp (hown₂ l hl)
          · intro rs A hdouRaw htopT
            have hdouV₁ : DeepOpenUnder st.heap rs A v₁ := by
              intro w hw
              rcases hheld₁ w hw with rfl | hwRaw
              · intro r' hr' hopen
                rcases ht₁ r' hr' with hraw | ⟨hinh, hrt⟩
                · exact hdouRaw.self r' hraw hopen
                · exact htopT (beq_iff_eq.mp hinh) r' hrt hopen
              · exact hdouRaw w hwRaw
            exact hdou₂ rs A hdouV₁
    rcases hstep2 with hStuck |
      ⟨v₂, st₁, hrun₂, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, hfresh₁, hnk₂, hk₂⟩
    · left
      conv => lhs; unfold selectFieldsLoop
      rw [M_bind_run, hro]; dsimp only
      rw [M_bind_run, hStuck]
    · have hrunStep :
          (selectFieldsLoop t fs ((f, idx) :: rest) out).run st =
          (selectFieldsLoop t fs rest (out.push (v₂, f.mode == .erased))).run st₁ := by
        conv => lhs; unfold selectFieldsLoop
        rw [M_bind_run, hro]; dsimp only
        rw [M_bind_run, hrun₂]
      have hfs₁ : ∀ w ∈ fs.toList, DeepLive st₁.heap w ∧ AcyclicFrom st₁.heap w := by
        intro w hw
        have h0 := hfs w hw
        have hpw : PreservesLocs (Reach st.heap w) st.heap st₁.heap :=
          hpres₁.mono (fun x hx => Reach_lt_size h0.1 hx)
        exact ⟨(DeepLive_congr hpw).mpr h0.1, (AcyclicFrom_congr hpw).mpr h0.2⟩
      rcases ih hc₁ hfs₁ with hStuck2 |
        ⟨out', st', hrunRest, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hpres₂, hc', hoss₂,
          hfresh₂, houtSz, hold, hrest⟩
      · left; rw [hrunStep, hStuck2]
      · right
        have hpres12 : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
          fun l hl => (hpres₂ l (Nat.lt_of_lt_of_le hl hsz₁)).trans (hpres₁ l hl)
        refine ⟨out', st', by rw [hrunStep, hrunRest],
          hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁, hstr₂.trans hstr₁,
          Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hpres12, hc',
          (OldSameShape.of_preserves_old hsz₁ hpres₁).trans hoss₂, ?_,
          (by rw [houtSz]; simp only [Array.size_push, List.length_cons]; omega),
          (fun i hi => by
            have hi' : i < (out.push (v₂, f.mode == .erased)).size := by simp; omega
            rw [hold i hi', Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]),
          ?_⟩
        · intro l o hge ho
          by_cases hlt1 : l < st₁.heap.objs.size
          · exact hfresh₁ l o hge ((hpres₂ l hlt1).symm.trans ho)
          · exact hfresh₂ l o (Nat.le_of_not_lt hlt1) ho
        · intro k fk idxk hk
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
            rcases hk with ⟨rfl, rfl⟩
            have hget : out'[out.size + 0]? = some (v₂, f.mode == .erased) := by
              have hlt : out.size < (out.push (v₂, f.mode == .erased)).size := by simp
              simpa using (hold out.size hlt).trans (by simp)
            refine ⟨v₂, hget, hnk₂, fun hfk => ?_⟩
            obtain ⟨hsame, hcls, hdl, hacyc, ht, hnv, hreach, hheld, hown, htree, hdou⟩ := hk₂ hfk
            have hpv : PreservesLocs (Reach st₁.heap v₂) st₁.heap st'.heap :=
              hpres₂.mono (fun x hx => Reach_lt_size hdl hx)
            refine ⟨hsame, (ClsOk_congr hpv).mpr hcls, (DeepLive_congr hpv).mpr hdl,
              (AcyclicFrom_congr hpv).mpr hacyc, ht, hnv,
              fun l hl => hreach l ((Reach_congr hpv l).mp hl),
              fun w hw => hheld w ((HeldBy_congr hpv w).mp hw),
              fun l hl => hown l ((OwnReach_congr hpv l).mp hl),
              fun htr => (OwnTreeFull_congr hpv).mpr (htree htr),
              fun rs A hrawD htopT => (DeepOpenUnder_congr hpv).mpr (hdou rs A hrawD htopT)⟩
          | succ k' =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨vk, hvkGet, hnk', hk'⟩ := hrest k' fk idxk hk
            have hidx : (out.push (v₂, f.mode == .erased)).size + k' = out.size + (k' + 1) := by
              simp; omega
            rw [hidx] at hvkGet
            let rawK := fs[idxk]?.getD (.imm .irr)
            have hrawKDA : DeepLive st.heap rawK ∧ AcyclicFrom st.heap rawK := by
              dsimp only [rawK]
              cases hget : fs[idxk]? with
              | none => exact ⟨DeepLive_imm st.heap .irr, AcyclicFrom_imm st.heap .irr⟩
              | some w => exact hfs w (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget))
            have hpRawK : PreservesLocs (Reach st.heap rawK) st.heap st₁.heap :=
              hpres₁.mono (fun x hx => Reach_lt_size hrawKDA.1 hx)
            refine ⟨vk, hvkGet, hnk', fun hfk => ?_⟩
            obtain ⟨hsame, hcls, hdl, hacyc, ht, hnv, hreach, hheld, hown, htree, hdou⟩ := hk' hfk
            refine ⟨hsame, hcls, hdl, hacyc, ht, hnv, ?_, ?_, ?_, ?_, ?_⟩
            · intro l hl
              rcases hreach l hl with hge | hr1
              · exact Or.inl (Nat.le_trans hsz₁ hge)
              · exact Or.inr ((Reach_congr hpRawK l).mp hr1)
            · intro w hw
              rcases hheld w hw with rfl | hw1
              · exact Or.inl rfl
              · exact Or.inr ((HeldBy_congr hpRawK w).mp hw1)
            · intro l hl
              exact (OwnReach_congr hpRawK l).mp (hown l hl)
            · intro htr
              exact htree ((OwnTreeFull_congr hpRawK).mpr htr)
            · intro rs A hrawD htopT
              exact hdou rs A ((DeepOpenUnder_congr hpRawK).mpr hrawD) htopT

/-- Soundness and framing for `Eval.select` (covering all 4 branches: `Nat`, all-`irr`,
trivial wrapper, and `.ctor` cell with Fix 6b `f.kept` conformance + pairwise `OwnReach`/`Reach`
disjointness across distinct fields). -/
theorem select_spec {P : Prog} {k : CaseInfo} {mv : Val} {st : St}
    (hidx : ∀ r ind cidx nP fs, P.ctorOf? r = some (ind, cidx, nP, fs) →
      (P.ctorsOf ind)[cidx]? = some r)
    (hc : CapsOk st.heap)
    (hdl : DeepLive st.heap mv)
    (hacyc : AcyclicFrom st.heap mv) :
    (select P k mv).run st = .error .stuck ∨
    ∃ cidx out st', (select P k mv).run st = .ok ((cidx, out), st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      (∀ l o, st.heap.objs.size ≤ l → st'.heap.objs[l]? = some o → ∃ n, o.cell = .num n) ∧
      ((P.nat = some k.ind ∧
        ((cidx = 0 ∧ out = #[] ∧ st' = st) ∨
         (cidx = 1 ∧ ∃ (m : Nat) (v : Val), out = #[(v, false)] ∧
           (natValue m).run st = .ok (v, st') ∧
           DeepLive st'.heap v ∧ ClsOk st'.heap natClass v ∧
           v.taint = [] ∧ AcyclicFrom st'.heap v ∧ OwnTreeFull P st'.heap v ∧
           (∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l)))) ∨
       (P.nat ≠ some k.ind ∧
        ((st' = st ∧ out = (selectFieldsOf P k cidx).map (fun f => (.imm .irr, f.mode == .erased))) ∨
         (st' = st ∧ cidx = 0 ∧
          ∃ wi, P.wrapperField? k.ind = some wi ∧
            out = ((selectFieldsOf P k 0).map (fun f => (.imm .irr, f.mode == .erased))).set! wi (mv, false) ∧
            ((∃ imm, mv = .imm imm) ∨
             (∃ loc cap o n, mv = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n))) ∨
         (∃ loc cap t o r fs nP fdefs,
            mv = .ref loc cap t ∧
            st.heap.objs[loc]? = some o ∧
            o.cap = cap ∧
            o.cell = .ctor r fs ∧
            P.ctorOf? r = some (k.ind, cidx, nP, fdefs) ∧
            selectFieldsOf P k cidx = fdefs ∧
            out.size = fdefs.size ∧
            (∀ (i : Nat) (f : Field), fdefs[i]? = some f →
              let raw := fs[i]?.getD (.imm .irr)
              ∃ v, out[i]? = some (v, f.mode == .erased) ∧
                (f.kept = false → v = .imm .irr) ∧
                (f.kept = true →
                  (raw = .imm .irr ∨ raw ∈ fs.toList) ∧
                  (f.cls = .val →
                    (∃ imm, raw = .imm imm ∧ v = .imm imm) ∨
                    (∃ loc' cap' t₁ t₂, raw = .ref loc' cap' t₁ ∧ v = .ref loc' cap' t₂)) ∧
                  ClsOk st'.heap f.cls v ∧
                  DeepLive st'.heap v ∧
                  AcyclicFrom st'.heap v ∧
                  (∀ r' ∈ v.taint, r' ∈ raw.taint ∨ (f.fmode = .inherited ∧ r' ∈ t)) ∧
                  (f.cls ≠ .val → v.taint = []) ∧
                  (∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l ∨ Reach st.heap raw l) ∧
                  (∀ w, HeldBy st'.heap v w → w = v ∨ HeldBy st.heap raw w) ∧
                  (∀ l, OwnReach P st'.heap v l →
                    OwnReach P st.heap raw l ∧ (f.fmode = .inherited → OwnReach P st.heap mv l)) ∧
                  (OwnTreeFull P st.heap mv → f.fmode = .inherited → OwnTreeFull P st'.heap v) ∧
                  (∀ rs A, DeepOpenUnder st.heap rs A raw →
                    (f.fmode = .inherited → OpenUnder rs A mv) →
                    DeepOpenUnder st'.heap rs A v))) ∧
            (OwnTreeFull P st.heap mv →
              ∀ (i j : Nat) (fi fj : Field) (vi vj : Val) (ei ej : Bool), i ≠ j →
                fdefs[i]? = some fi → fdefs[j]? = some fj →
                out[i]? = some (vi, ei) → out[j]? = some (vj, ej) →
                fi.fmode = .inherited →
                ∀ l, OwnReach P st'.heap vi l → ¬ Reach st'.heap vj l))))) := by
  have hIrrOk : ∀ {Q₁ Q₂ : Nat → Array (Val × Bool) → St → Prop} {mv₀ : Val} (cidx : Nat), P.nat ≠ some k.ind →
      (select P k mv₀).run st =
        .ok ((cidx, (selectFieldsOf P k cidx).map (fun f => (.imm .irr, f.mode == .erased))), st) →
      ∃ cidx' out' st', (select P k mv₀).run st = .ok ((cidx', out'), st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
        CapsOk st'.heap ∧ OldSameShape st.heap st'.heap ∧
        (∀ l o, st.heap.objs.size ≤ l → st'.heap.objs[l]? = some o → ∃ n, o.cell = .num n) ∧
        ((P.nat = some k.ind ∧ Q₁ cidx' out' st') ∨
         (P.nat ≠ some k.ind ∧
          ((st' = st ∧ out' = (selectFieldsOf P k cidx').map (fun f => (.imm .irr, f.mode == .erased))) ∨
           Q₂ cidx' out' st'))) := by
    intro Q₁ Q₂ mv₀ cidx hne hrun
    exact ⟨cidx, _, st, hrun, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, OldSameShape.refl _,
      (fun l o hge ho => by have := (Array.getElem?_eq_some_iff.mp ho).1; omega),
      Or.inr ⟨hne, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hWrapOk : ∀ {Q₁ Q₂ : Nat → Array (Val × Bool) → St → Prop} {mv₀ : Val} (hne : P.nat ≠ some k.ind),
      ((∃ imm, mv₀ = .imm imm) ∨
       (∃ loc cap o n, mv₀ = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n)) →
      ((match P.wrapperField? k.ind with
        | some wi => pure (0, ((selectFieldsOf P k 0).map (fun f => (.imm .irr, f.mode == .erased))).set! wi (mv₀, false))
        | none => stuckM : M (Nat × Array (Val × Bool))).run st = (select P k mv₀).run st) →
      (select P k mv₀).run st = .error .stuck ∨
      ∃ cidx out st', (select P k mv₀).run st = .ok ((cidx, out), st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
        CapsOk st'.heap ∧ OldSameShape st.heap st'.heap ∧
        (∀ l o, st.heap.objs.size ≤ l → st'.heap.objs[l]? = some o → ∃ n, o.cell = .num n) ∧
        ((P.nat = some k.ind ∧ Q₁ cidx out st') ∨
         (P.nat ≠ some k.ind ∧
          ((st' = st ∧ out = (selectFieldsOf P k cidx).map (fun f => (.imm .irr, f.mode == .erased))) ∨
           (st' = st ∧ cidx = 0 ∧
            ∃ wi, P.wrapperField? k.ind = some wi ∧
              out = ((selectFieldsOf P k 0).map (fun f => (.imm .irr, f.mode == .erased))).set! wi (mv₀, false) ∧
              ((∃ imm, mv₀ = .imm imm) ∨
               (∃ loc cap o n, mv₀ = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n))) ∨
           Q₂ cidx out st'))) := by
    intro Q₁ Q₂ mv₀ hne hmv heq
    cases hw : P.wrapperField? k.ind with
    | none =>
      left; rw [← heq, hw]; rfl
    | some wi =>
      right
      refine ⟨0, _, st, by rw [← heq, hw]; rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
        PreservesLocs.refl _ _, hc, OldSameShape.refl _,
        (fun l o hge ho => by have := (Array.getElem?_eq_some_iff.mp ho).1; omega),
        Or.inr ⟨hne, Or.inr (Or.inl ⟨rfl, rfl, wi, rfl, rfl, hmv⟩)⟩⟩
  by_cases hnat : P.nat = some k.ind
  · -- Branch 1: `Nat` inductive
    have hnatBeq : (P.nat == some k.ind) = true := by rw [hnat]; simp
    have hrunBase : (select P k mv).run st =
        (match (numOf? mv).run st with
         | .error e => .error e
         | .ok (opt, st0) =>
           match opt with
           | some 0 => .ok ((0, #[]), st0)
           | some (m + 1) => ((natValue m) >>= fun v => pure (1, #[(v, false)])).run st0
           | none => .error .stuck) := by
      unfold select
      simp only [hnatBeq, ↓reduceIte]
      rw [M_bind_run]
      cases (numOf? mv).run st with
      | error e => rfl
      | ok p =>
        rcases p with ⟨opt, st0⟩
        cases opt with
        | none => rfl
        | some n =>
          cases n with
          | zero => rfl
          | succ m => rfl
    rw [numOf?_ok hdl.self.1] at hrunBase
    dsimp only at hrunBase
    split at hrunBase
    · right
      refine ⟨0, #[], st, hrunBase, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
        PreservesLocs.refl _ _, hc, OldSameShape.refl _,
        (fun l o hge ho => by have := (Array.getElem?_eq_some_iff.mp ho).1; omega),
        Or.inl ⟨hnat, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩
    · rename_i m _
      obtain ⟨v, st', hnv, hr, hnr, hst, hstr, hsz, hcap, hpres, hc', hdlV, htV, hacycV, _, hnum⟩ :=
        mkNum_ok natClass m st hc
      obtain ⟨loc, cap, o, rfl, ho, hcell, hocap, hgeLoc⟩ := hnum (by decide)
      have hrunOk : (select P k mv).run st = .ok ((1, #[(.ref loc cap [], false)]), st') := by
        rw [hrunBase, M_bind_run]
        unfold natValue
        rw [hnv]; rfl
      have hfreshNum : ∀ l o', st.heap.objs.size ≤ l → st'.heap.objs[l]? = some o' → ∃ n', o'.cell = .num n' := by
        unfold mkNum at hnv
        simp only [show natClass = .leaf from rfl] at hnv
        rw [alloc_run] at hnv; cases hnv
        intro l o' hge ho'
        by_cases heq : l = st.heap.objs.size
        · subst heq
          simp only [Array.getElem?_push_size, Option.some.injEq] at ho'
          subst ho'; exact ⟨m, rfl⟩
        · have hlt := (Array.getElem?_eq_some_iff.mp ho').1
          simp only [Array.size_push] at hlt
          omega
      right
      refine ⟨1, #[(.ref loc cap [], false)], st', hrunOk,
        hr, hnr, hst, hstr, hsz, hcap, hpres, hc',
        OldSameShape.of_preserves_old hsz hpres, hfreshNum,
        Or.inl ⟨hnat, Or.inr ⟨rfl, m, .ref loc cap [], rfl, hnv, hdlV,
          ⟨loc, cap, o, m, rfl, ho, hcell, hocap⟩, htV, hacycV,
          OwnTreeFull_num ho hcell, ?_⟩⟩⟩
      intro l hl
      rw [Reach_num_iff ho hcell] at hl
      subst hl; exact hgeLoc
    · left; exact hrunBase
  · -- Non-Nat inductive
    have hnatBeq : (P.nat == some k.ind) = false := beq_false_of_ne hnat
    cases hmv : mv with
    | imm imm =>
      cases imm with
      | con r =>
        cases hctor : P.ctorOf? r with
        | none =>
          left; unfold select
          simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte, hctor]
          rfl
        | some info =>
          rcases info with ⟨ind, cidx, nP, fdefs⟩
          by_cases hind : ind = k.ind
          · subst hind
            right
            have hrun : (select P k (.imm (.con r))).run st =
                .ok ((cidx, (selectFieldsOf P k cidx).map (fun f => (.imm .irr, f.mode == .erased))), st) := by
              unfold select selectFieldsOf
              simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte, hctor, beq_self_eq_true, ↓reduceIte]
              rfl
            exact hIrrOk cidx hnat hrun
          · have hindBeq : (ind == k.ind) = false := beq_false_of_ne hind
            refine hWrapOk hnat (Or.inl ⟨.con r, rfl⟩) ?_
            unfold select selectFieldsOf
            simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte, hctor, hindBeq]
            rfl
      | irr =>
        by_cases hsz1 : (P.ctorsOf k.ind).size = 1
        · right
          have hrun : (select P k (.imm .irr)).run st =
              .ok ((0, (selectFieldsOf P k 0).map (fun f => (.imm .irr, f.mode == .erased))), st) := by
            unfold select selectFieldsOf
            simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte, hsz1, beq_self_eq_true]
            rfl
          exact hIrrOk 0 hnat hrun
        · left
          have hszBeq : ((P.ctorsOf k.ind).size == 1) = false := beq_false_of_ne hsz1
          unfold select
          simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte, hszBeq]
          rfl
      | bits n =>
        refine hWrapOk hnat (Or.inl ⟨.bits n, rfl⟩) ?_
        unfold select selectFieldsOf
        simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte]
        rfl
    | ref loc cap t =>
      have hdl' : DeepLive st.heap (.ref loc cap t) := hmv ▸ hdl
      have hacyc' : AcyclicFrom st.heap (.ref loc cap t) := hmv ▸ hacyc
      obtain ⟨o, ho, hcap⟩ := hdl'.self.1
      have hcapBeq : (o.cap == cap) = true := by rw [hcap]; simp
      cases hcell : o.cell with
      | num n =>
        have htNil : t = [] := hdl'.self.2 o n ho hcell
        subst htNil
        refine hWrapOk hnat (Or.inr ⟨loc, cap, o, n, rfl, ho, hcell⟩) ?_
        unfold select selectFieldsOf
        simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, obj_ok ho]
        simp only [hcapBeq, ↓reduceIte, hcell]
        rfl
      | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
        left
        unfold select
        simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, obj_ok ho]
        simp only [hcapBeq, ↓reduceIte, hcell]
        rfl
      | ctor r fs =>
        cases hctor : P.ctorOf? r with
        | none =>
          left
          unfold select
          simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte]
          rw [M_bind_run, obj_ok ho]
          simp only [hcapBeq, ↓reduceIte, hcell, hctor]
          rfl
        | some info =>
          rcases info with ⟨ind, cidx, nP, fdefs⟩
          by_cases hind : ind = k.ind
          · subst hind
            have hfsDA : ∀ w ∈ fs.toList, DeepLive st.heap w ∧ AcyclicFrom st.heap w := by
              intro w hw
              have hmem : w ∈ o.cell.vals := by rw [hcell]; exact hw
              exact ⟨hdl'.sub (HeldBy_of_mem_vals ho hmem), hacyc'.sub (HeldBy_of_mem_vals ho hmem)⟩
            have hselRun : (select P k (.ref loc cap t)).run st =
                ((selectFieldsLoop t fs fdefs.zipIdx.toList #[]) >>= fun out => pure (cidx, out)).run st := by
              unfold select
              simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte]
              rw [M_bind_run, obj_ok ho]
              simp only [hcapBeq, ↓reduceIte, hcell, hctor, beq_self_eq_true]
              rw [M_bind_run, M_bind_run]
              have hfor : (forIn (m := M) fdefs.zipIdx (#[] : Array (Val × Bool)) (fun fi acc => do
                  let v ← readOut (fi.1.fmode == .inherited) t (fs[fi.2]?.getD (.imm .irr))
                  let v ← if fi.1.kept then conform fi.1.cls v else pure (.imm .irr)
                  pure (ForInStep.yield (acc.push (v, fi.1.mode == .erased))))).run st =
                (selectFieldsLoop t fs fdefs.zipIdx.toList #[]).run st := by
                rw [← Array.forIn_toList]
                exact forIn_list_selectFieldsLoop t fs fdefs.zipIdx.toList #[] st
              erw [hfor]
            rcases selectFieldsLoop_spec (P := P) (t := t) (fs := fs)
                (xs := fdefs.zipIdx.toList) (out := #[]) hc hfsDA with hStuck |
              ⟨out, st', hloop, hr, hnr, hst, hstr, hsz, hcap', hpres, hc', hoss, hfresh,
                houtSz, _, hfields⟩
            · left; rw [hselRun, M_bind_run, hStuck]
            · right
              have hsfEq : selectFieldsOf P k cidx = fdefs := by
                unfold selectFieldsOf
                rw [hidx r k.ind cidx nP fdefs hctor]
                dsimp only
                rw [hctor]
              have houtSz' : out.size = fdefs.size := by
                simpa [Array.size_zipIdx] using houtSz
              have hzipGet : ∀ (i : Nat) (f : Field), fdefs[i]? = some f →
                  fdefs.zipIdx.toList[i]? = some (f, i) := by
                intro i f hi
                obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hi
                have hltz : i < fdefs.zipIdx.toList.length := by simp [hlt]
                rw [List.getElem?_eq_getElem hltz]
                simp [heq]
              have hfieldEach : ∀ (i : Nat) (f : Field), fdefs[i]? = some f →
                  let raw := fs[i]?.getD (.imm .irr)
                  ∃ v, out[i]? = some (v, f.mode == .erased) ∧
                    (f.kept = false → v = .imm .irr) ∧
                    (f.kept = true →
                      (raw = .imm .irr ∨ raw ∈ fs.toList) ∧
                      (f.cls = .val →
                        (∃ imm, raw = .imm imm ∧ v = .imm imm) ∨
                        (∃ loc' cap' t₁ t₂, raw = .ref loc' cap' t₁ ∧ v = .ref loc' cap' t₂)) ∧
                      ClsOk st'.heap f.cls v ∧
                      DeepLive st'.heap v ∧
                      AcyclicFrom st'.heap v ∧
                      (∀ r' ∈ v.taint, r' ∈ raw.taint ∨ (f.fmode = .inherited ∧ r' ∈ t)) ∧
                      (f.cls ≠ .val → v.taint = []) ∧
                      (∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l ∨ Reach st.heap raw l) ∧
                      (∀ w, HeldBy st'.heap v w → w = v ∨ HeldBy st.heap raw w) ∧
                      (∀ l, OwnReach P st'.heap v l →
                        OwnReach P st.heap raw l ∧ (f.fmode = .inherited → OwnReach P st.heap (.ref loc cap t) l)) ∧
                      (OwnTreeFull P st.heap (.ref loc cap t) → f.fmode = .inherited → OwnTreeFull P st'.heap v) ∧
                      (∀ rs A, DeepOpenUnder st.heap rs A raw →
                        (f.fmode = .inherited → OpenUnder rs A (.ref loc cap t)) →
                        DeepOpenUnder st'.heap rs A v)) := by
                intro i f hi
                obtain ⟨v, hvGet, hnk, hkv⟩ := hfields i f i (hzipGet i f hi)
                have hvGet' : out[i]? = some (v, f.mode == .erased) := by simpa using hvGet
                refine ⟨v, hvGet', hnk, fun hfk => ?_⟩
                obtain ⟨hsame, hcls, hdlv, hacycv, htv, hnvv, hreachv, hheldv, hownv, htreev, hdouv⟩ := hkv hfk
                have hrawMem : fs[i]?.getD (.imm .irr) = .imm .irr ∨ fs[i]?.getD (.imm .irr) ∈ fs.toList := by
                  cases hget : fs[i]? with
                  | none => exact Or.inl rfl
                  | some w => exact Or.inr (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget))
                have hownInh : ∀ l, OwnReach P st'.heap v l →
                    OwnReach P st.heap (fs[i]?.getD (.imm .irr)) l ∧
                    (f.fmode = .inherited → OwnReach P st.heap (.ref loc cap t) l) := by
                  intro l hl
                  have hor := hownv l hl
                  refine ⟨hor, fun hinh => ?_⟩
                  cases hget : fs[i]? with
                  | none =>
                    rw [hget] at hor; exact False.elim (OwnReach_imm_false P _ _ l hor)
                  | some w =>
                    rw [hget] at hor
                    have hlt : i < fs.size := (Array.getElem?_eq_some_iff.mp hget).1
                    have hiOwn : i ∈ ownedSlots P o.cell := by
                      rw [hcell]
                      simp only [ownedSlots, hctor, List.mem_filter, List.mem_range, hi, Option.map_some,
                        Option.getD_some, hinh, beq_self_eq_true]
                      exact ⟨hlt, trivial⟩
                    have hsi : o.cell.slot? i = some w := by rw [hcell]; exact hget
                    exact .step ho hiOwn hsi hor
                have htreeInh : OwnTreeFull P st.heap (.ref loc cap t) → f.fmode = .inherited →
                    OwnTreeFull P st'.heap v := by
                  intro htr hinh
                  apply htreev
                  cases hget : fs[i]? with
                  | none => exact OwnTreeFull_imm P _ _
                  | some w =>
                    have hlt : i < fs.size := (Array.getElem?_eq_some_iff.mp hget).1
                    have hiOwn : i ∈ ownedSlots P o.cell := by
                      rw [hcell]
                      simp only [ownedSlots, hctor, List.mem_filter, List.mem_range, hi, Option.map_some,
                        Option.getD_some, hinh, beq_self_eq_true]
                      exact ⟨hlt, trivial⟩
                    have hsi : o.cell.slot? i = some w := by rw [hcell]; exact hget
                    exact htr.sub rfl ho hiOwn hsi
                exact ⟨hrawMem, hsame, hcls, hdlv, hacycv, htv, hnvv, hreachv, hheldv, hownInh,
                  htreeInh, fun rs A hrawD hmvO => hdouv rs A hrawD (fun hinh => hmvO hinh)⟩
              refine ⟨cidx, out, st', by rw [hselRun, M_bind_run, hloop]; rfl,
                hr, hnr, hst, hstr, hsz, hcap', hpres, hc', hoss, hfresh,
                Or.inr ⟨hnat, Or.inr (Or.inr ⟨loc, cap, t, o, r, fs, nP, fdefs,
                  rfl, ho, hcap, hcell, hctor, hsfEq, houtSz', hfieldEach, ?_⟩)⟩⟩
              -- Pairwise `OwnReach`/`Reach` disjointness across distinct fields `i ≠ j`
              intro htr i j fi fj vi vj ei ej hne hfi hfj hvi hvj hinh l hori hrlj
              obtain ⟨vi', hvi', hnki, hki⟩ := hfieldEach i fi hfi
              rw [hvi] at hvi'; cases hvi'
              obtain ⟨vj', hvj', hnkj, hkj⟩ := hfieldEach j fj hfj
              rw [hvj] at hvj'; cases hvj'
              cases hfik : fi.kept with
              | false =>
                rw [hnki hfik] at hori; exact OwnReach_imm_false P _ _ l hori
              | true =>
                cases hfjk : fj.kept with
                | false =>
                  rw [hnkj hfjk] at hrlj; cases hrlj
                | true =>
                  have horRawI : OwnReach P st.heap (fs[i]?.getD (.imm .irr)) l :=
                    ((hki hfik).2.2.2.2.2.2.2.2.2.1 l hori).1
                  cases hfsi : fs[i]? with
                  | none =>
                    rw [hfsi] at horRawI; exact OwnReach_imm_false P _ _ l horRawI
                  | some wi =>
                    rw [hfsi] at horRawI
                    have hlti : i < fs.size := (Array.getElem?_eq_some_iff.mp hfsi).1
                    have hltL : l < st.heap.objs.size :=
                      Reach_lt_size (hfsDA wi (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfsi))).1
                        (OwnReach_toReach horRawI)
                    have hreachJ := (hkj hfjk).2.2.2.2.2.2.2.1 l hrlj
                    rcases hreachJ with hge | hrRawJ
                    · omega
                    · cases hfsj : fs[j]? with
                      | none => rw [hfsj] at hrRawJ; cases hrRawJ
                      | some wj =>
                        rw [hfsj] at hrRawJ
                        have hiOwn : i ∈ ownedSlots P o.cell := by
                          rw [hcell]
                          simp only [ownedSlots, hctor, List.mem_filter, List.mem_range, hfi,
                            Option.map_some, Option.getD_some, hinh, beq_self_eq_true]
                          exact ⟨hlti, trivial⟩
                        have hsi : o.cell.slot? i = some wi := by rw [hcell]; exact hfsi
                        have hsj : o.cell.slot? j = some wj := by rw [hcell]; exact hfsj
                        exact OwnTreeFull_other_slot_disjoint htr hacyc' ho hiOwn hsi hsj
                          (Ne.symm hne) (Or.inr ⟨r, fs, hcell, hfsj⟩) horRawI hrRawJ
          · left
            have hindBeq : (ind == k.ind) = false := beq_false_of_ne hind
            unfold select
            simp only [hnatBeq, Bool.false_eq_true, ↓reduceIte]
            rw [M_bind_run, obj_ok ho]
            simp only [hcapBeq, ↓reduceIte, hcell, hctor, hindBeq]
            rfl

end IxC.Resource.Proof
