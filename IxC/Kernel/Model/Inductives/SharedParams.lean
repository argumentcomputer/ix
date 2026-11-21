module

public import IxC.Kernel.Model.Inductives.StructFrames
import IxC.Kernel.Model.Annot.BitRename

public section

namespace Ix.Kernel.Model

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify SetTheory Ix.Kernel.SetTheory

universe u

private theorem erasedEq_looseBVarsBounded {md : Mode} :
    ∀ {e e' : Expr md}, Expr.ErasedEq e e' → ∀ n,
      e.looseBVarsBounded n = e'.looseBVarsBounded n
  | .bvar i, e', he, _ => by
    match e', he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar _ _, e', he, _ => by
    match e', he with
    | .fvar _ _, _ => simp only [Expr.looseBVarsBounded]
  | .sort _, e', he, _ => by
    match e', he with
    | .sort _, _ => simp only [Expr.looseBVarsBounded]
  | .const _ _, e', he, _ => by
    match e', he with
    | .const _ _, _ => simp only [Expr.looseBVarsBounded]
  | .lit _, e', he, _ => by
    match e', he with
    | .lit _, _ => simp only [Expr.looseBVarsBounded]
  | .app f a, e', he, n => by
    match e', he with
    | .app g b, he =>
      obtain ⟨hf, ha⟩ := he
      simp only [Expr.looseBVarsBounded, erasedEq_looseBVarsBounded hf n,
        erasedEq_looseBVarsBounded ha n]
  | .lam ty body _, e', he, n => by
    match e', he with
    | .lam ty' body' _, he =>
      obtain ⟨_, ht, hb⟩ := he
      simp only [Expr.looseBVarsBounded, erasedEq_looseBVarsBounded ht n,
        erasedEq_looseBVarsBounded hb (n + 1)]
  | .forallE ty body _, e', he, n => by
    match e', he with
    | .forallE ty' body' _, he =>
      obtain ⟨_, ht, hb⟩ := he
      simp only [Expr.looseBVarsBounded, erasedEq_looseBVarsBounded ht n,
        erasedEq_looseBVarsBounded hb (n + 1)]
  | .letE ty value body _, e', he, n => by
    match e', he with
    | .letE ty' value' body' _, he =>
      obtain ⟨ht, hv, hb⟩ := he
      simp only [Expr.looseBVarsBounded, erasedEq_looseBVarsBounded ht n,
        erasedEq_looseBVarsBounded hv n, erasedEq_looseBVarsBounded hb (n + 1)]
  | .proj _ _ e, e', he, n => by
    match e', he with
    | .proj _ _ e'', he =>
      obtain ⟨_, _, he⟩ := he
      simp only [Expr.looseBVarsBounded, erasedEq_looseBVarsBounded he n]

private theorem wScoped_of_leaves {md : Mode} :
    ∀ (e : Expr md) (d : Nat),
      (∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.WScoped l.1 l.2) → Expr.WScoped d e
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => by
    simp only [Expr.WScoped]
  | .fvar i ty, _, h => by
    simp only [Expr.WScoped]
    exact h (i, ty) (by simp [Expr.fvarLeaves])
  | .app f a, d, h => by
    simp only [Expr.fvarLeaves] at h
    simp only [Expr.WScoped]
    exact ⟨wScoped_of_leaves f d (fun l hl => h l (List.mem_append_left _ hl)),
      wScoped_of_leaves a d (fun l hl => h l (List.mem_append_right _ hl))⟩
  | .lam ty body _, d, h | .forallE ty body _, d, h => by
    simp only [Expr.fvarLeaves] at h
    simp only [Expr.WScoped]
    exact ⟨wScoped_of_leaves ty d (fun l hl => h l (List.mem_append_left _ hl)),
      wScoped_of_leaves body d (fun l hl => h l (List.mem_append_right _ hl))⟩
  | .letE ty value body _, d, h => by
    simp only [Expr.fvarLeaves] at h
    simp only [Expr.WScoped]
    exact ⟨wScoped_of_leaves ty d
        (fun l hl => h l (List.mem_append_left _ (List.mem_append_left _ hl))),
      wScoped_of_leaves value d
        (fun l hl => h l (List.mem_append_left _ (List.mem_append_right _ hl))),
      wScoped_of_leaves body d (fun l hl => h l (List.mem_append_right _ hl))⟩
  | .proj _ _ e, d, h => by
    simp only [Expr.fvarLeaves] at h
    simp only [Expr.WScoped]
    exact wScoped_of_leaves e d h

variable {md : Mode} {V : Type u} [SetTheory V] {env : Env md}
  {m : EnvModel V env} {φ : LevelParam → Nat}

private theorem earlier_var_leaves {nP : Nat} {tty : Expr md} {tfvs : List (Expr md)}
    {trest : Expr md} {Γt : List AnnotTerm} {Rt : AnnotTerm}
    (hT : Opened m φ nP tty tfvs trest Γt Rt)
    {i : Nat} {v : Expr md} (hv : v ∈ tfvs.take i) :
    ∀ l ∈ v.fvarLeaves,
      l.1 < i ∧ Expr.WScoped l.1 l.2 ∧ l.2.looseBVarsBounded 0 = true ∧
        Expr.fvar l.1 l.2 ∈ tfvs := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hjmin : j < min i tfvs.length := by simpa only [List.length_take] using hj
  have hjt : j < tfvs.length := by omega
  have hji : j < i := by omega
  have hget : tfvs[j]? = some tfvs[j] := List.getElem?_eq_getElem hjt
  have hvar := hT.var j tfvs[j] hget
  obtain ⟨ty, hfv⟩ := hvar.1
  rw [hfv] at hvar
  simp only [Expr.fvarTypeD] at hvar
  intro l hl
  simp only [List.getElem_take] at hl
  rw [hfv] at hl
  simp only [Expr.fvarLeaves] at hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨hji, hvar.2.1, hvar.2.2.1, by rw [← hfv]; exact List.getElem_mem hjt⟩
  · obtain ⟨hlt, hw⟩ := Expr.WScoped_leaves ty hvar.2.1 l hl
    exact ⟨by omega, hw, hvar.2.2.2.1 l hl, hvar.2.2.2.2 l hl⟩

/-- A checker comparison in the former's variable annotations proves equality of the
original domain readings. Context transport is the induction hypothesis already used by
the ordinary parameter-frame proof. No recursor or later declaration model is involved. -/
private theorem sharedParamRow {J : Judgements md} (hJ : JudgeSound J m)
    {nP nF : Nat} {tty cty : Expr md} {tfvs cfvs : List (Expr md)} {trest crest : Expr md}
    {Γt Γc : List AnnotTerm} {Rt Rc : AnnotTerm}
    (hT : Opened m φ nP tty tfvs trest Γt Rt)
    (hC : Opened m φ (nP + nF) cty cfvs crest Γc Rc)
    {i : Nat} (hi : i < nP) {a b a' : Expr md}
    (ha : cfvs[i]? = some a) (hb : tfvs[i]? = some b)
    (heq : Expr.ErasedEq a.fvarTypeD a')
    (hleaves : ∀ l ∈ a'.fvarLeaves, ∃ v ∈ tfvs.take i, l ∈ v.fvarLeaves)
    (hde : J.defeq env i a' b.fvarTypeD)
    (hsat : ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ → Sat V (Γt.drop (nP - i)) ρ)
    (htransfer : ∀ {e : Expr md}, CtxOk m φ i (Γt.drop (nP - i)) e →
      CtxOk m φ i (Γc.drop (nP + nF - i)) e) :
    ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ →
      interp V ρ (Γc.getD (nP + nF - 1 - i) default) =
        interp V ρ (Γt.getD (nP - 1 - i) default) := by
  obtain ⟨_, _, hba, _, _⟩ := hC.var i a ha
  obtain ⟨_, hwb, hbb, hLb, hleafb⟩ := hT.var i b hb
  have hinfo : ∀ l ∈ a'.fvarLeaves,
      l.1 < i ∧ Expr.WScoped l.1 l.2 ∧ l.2.looseBVarsBounded 0 = true ∧
        Expr.fvar l.1 l.2 ∈ tfvs := by
    intro l hl
    obtain ⟨v, hv, hlv⟩ := hleaves l hl
    exact earlier_var_leaves hT hv l hlv
  have hwa' : Expr.WScoped i a' :=
    wScoped_of_leaves a' i (fun l hl => ⟨(hinfo l hl).1, (hinfo l hl).2.1⟩)
  have hba' : a'.looseBVarsBounded 0 = true := by
    rw [← erasedEq_looseBVarsBounded heq 0]
    exact hba
  have hLa' : Expr.LeavesBounded a' := fun l hl => (hinfo l hl).2.2.1
  have hCa' : CtxOk m φ i (Γc.drop (nP + nF - i)) a' :=
    htransfer (hT.ctx (by omega) hwa' (fun l hl => (hinfo l hl).2.2.2))
  have hCb : CtxOk m φ i (Γc.drop (nP + nF - i)) b.fvarTypeD :=
    htransfer (hT.ctx (by omega) hwb hleafb)
  have hda' : denoteMeta m.acval env φ i a' = some (Γc.getD (nP + nF - 1 - i) default) := by
    rw [← denoteMeta_erasedEq heq i]
    exact hC.doms i a ha
  exact defEqRowJ hJ hde hwa' hba' hLa' hwb hbb hLb hCa' hCb hda' (hT.doms i b hb)
    (fun ρ hρ => hC.okΓ i (by omega) ρ hρ)
    (fun ρ hρ => hT.okΓ i hi ρ (hsat ρ hρ))

/-- Shared-annotation comparisons identify the complete parameter frames, without any
additional semantic assumption or change to the stored-environment invariant. -/
theorem paramFramesShared {J : Judgements md} (hJ : JudgeSound J m) {nP nF : Nat}
    {tty cty : Expr md} {tfvs cfvs : List (Expr md)} {trest crest : Expr md}
    {Γt Γc : List AnnotTerm} {Rt Rc : AnnotTerm}
    (hT : Opened m φ nP tty tfvs trest Γt Rt)
    (hC : Opened m φ (nP + nF) cty cfvs crest Γc Rc)
    (hpin : ∀ i, i < nP → ∃ a b a', cfvs[i]? = some a ∧ tfvs[i]? = some b ∧
      Expr.ErasedEq a.fvarTypeD a' ∧ J.defeq env i a' b.fvarTypeD ∧
      ∀ l ∈ a'.fvarLeaves, ∃ v ∈ tfvs.take i, l ∈ v.fvarLeaves) :
    ∀ i, i ≤ nP →
      (∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ ↔
        Sat V (Γt.drop (nP - i)) ρ) ∧
      (i < nP → ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - i)) ρ →
        interp V ρ (Γc.getD (nP + nF - 1 - i) default) =
          interp V ρ (Γt.getD (nP - 1 - i) default)) := by
  suffices ∀ i j, j ≤ i → j ≤ nP →
      (∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - j)) ρ ↔
        Sat V (Γt.drop (nP - j)) ρ) ∧
      (j < nP → ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - j)) ρ →
        interp V ρ (Γc.getD (nP + nF - 1 - j) default) =
          interp V ρ (Γt.getD (nP - 1 - j) default)) from
    fun i hi => this i i (Nat.le_refl _) hi
  intro i
  induction i with
  | zero =>
    intro j hj _
    obtain rfl : j = 0 := by omega
    have hnilC : Γc.drop (nP + nF - 0) = [] := by
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hC.len; omega)]
    have hnilT : Γt.drop (nP - 0) = [] := by
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by have := hT.len; omega)]
    have hsat : ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - 0)) ρ ↔
        Sat V (Γt.drop (nP - 0)) ρ := by
      intro ρ
      rw [hnilC, hnilT]
    refine ⟨hsat, fun hlt ρ hρ => ?_⟩
    obtain ⟨a, b, a', ha, hb, heq, hde, hleaves⟩ := hpin 0 hlt
    exact sharedParamRow hJ hT hC hlt ha hb heq hleaves hde
      (fun ρ h => (hsat ρ).mp h)
      (by intro e h; rw [hnilC]; rwa [hnilT] at h) ρ hρ
  | succ i ih =>
    intro j hj hjn
    rcases Nat.lt_or_ge j (i + 1) with hjl | hjg
    · exact ih j (by omega) hjn
    obtain rfl : j = i + 1 := by omega
    obtain ⟨ihsat, iheq⟩ := ih i (Nat.le_refl _) (by omega)
    have hlt : i < nP := by omega
    have hdc : Γc.drop (nP + nF - (i + 1)) =
        Γc.getD (nP + nF - 1 - i) default :: Γc.drop (nP + nF - i) := by
      rw [show nP + nF - (i + 1) = nP + nF - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γc) (i := nP + nF - i - 1)
          (by rw [hC.len]; omega)]
      have hG : Γc[nP + nF - i - 1]'(by have := hC.len; omega) =
          Γc.getD (nP + nF - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by rw [hC.len]; omega)]
        simp only [Option.getD_some]
        congr 1
        omega
      rw [hG, show nP + nF - i - 1 + 1 = nP + nF - i from by omega]
    have hdt : Γt.drop (nP - (i + 1)) =
        Γt.getD (nP - 1 - i) default :: Γt.drop (nP - i) := by
      rw [show nP - (i + 1) = nP - i - 1 from by omega,
        List.drop_eq_getElem_cons (l := Γt) (i := nP - i - 1) (by rw [hT.len]; omega)]
      have hG : Γt[nP - i - 1]'(by have := hT.len; omega) =
          Γt.getD (nP - 1 - i) default := by
        rw [List.getD, List.getElem?_eq_getElem (by rw [hT.len]; omega)]
        simp only [Option.getD_some]
        congr 1
        omega
      rw [hG, show nP - i - 1 + 1 = nP - i from by omega]
    have hsat : ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - (i + 1))) ρ ↔
        Sat V (Γt.drop (nP - (i + 1))) ρ := by
      intro ρ
      rw [hdc, hdt]
      constructor
      · intro h
        obtain ⟨h0, htl⟩ := Sat_cons_inv h
        have h' := Sat_cons V ((ihsat _).mp htl) (by
          rw [← iheq hlt _ htl]
          exact h0)
        rwa [cons_eta] at h'
      · intro h
        obtain ⟨h0, htl⟩ := Sat_cons_inv h
        have htl' := (ihsat _).mpr htl
        have h' := Sat_cons V htl' (by rw [iheq hlt _ htl']; exact h0)
        rwa [cons_eta] at h'
    refine ⟨hsat, fun hlt' ρ hρ => ?_⟩
    have hent : ∀ (p : Nat) (A₁ A₂ : AnnotTerm),
        (Γt.drop (nP - (i + 1)))[p]? = some A₁ →
        (Γc.drop (nP + nF - (i + 1)))[p]? = some A₂ →
        ∀ ρ : Nat → V, Sat V (Γc.drop (nP + nF - (i + 1))) ρ →
          interp V (fun j => ρ (j + p + 1)) A₁ =
            interp V (fun j => ρ (j + p + 1)) A₂ := by
      intro p A₁ A₂ hA₁ hA₂ ρ hρ
      have hpl : p < i + 1 := by
        have := (List.getElem?_eq_some_iff.mp hA₂).1
        rw [List.length_drop, hC.len] at this
        omega
      rw [List.getElem?_drop] at hA₁ hA₂
      have hj : nP - (i + 1) + p = nP - 1 - (i - p) := by omega
      have hj' : nP + nF - (i + 1) + p = nP + nF - 1 - (i - p) := by omega
      rw [hj] at hA₁
      rw [hj'] at hA₂
      have e1 : A₁ = Γt.getD (nP - 1 - (i - p)) default := by
        rw [List.getD, hA₁]
        rfl
      have e2 : A₂ = Γc.getD (nP + nF - 1 - (i - p)) default := by
        rw [List.getD, hA₂]
        rfl
      subst e1 e2
      have hd := Sat_drop hρ (p + 1)
      rw [List.drop_drop, show nP + nF - (i + 1) + (p + 1) = nP + nF - (i - p)
        from by omega] at hd
      have e : (fun j => ρ (j + p + 1)) = fun j => ρ (j + (p + 1)) := by
        funext j
        rw [Nat.add_assoc]
      rw [e]
      exact ((ih (i - p) (by omega) (by omega)).2 (by omega) _ hd).symm
    obtain ⟨a, b, a', ha, hb, heq, hde, hleaves⟩ := hpin (i + 1) hlt'
    exact sharedParamRow hJ hT hC hlt' ha hb heq hleaves hde
      (fun ρ h => (hsat ρ).mp h)
      (fun hctx => hctx.transfer (by rw [List.length_drop, hC.len]; omega)
        (fun ρ h => (hsat ρ).mp h) hent) ρ hρ


end Ix.Kernel.Model
