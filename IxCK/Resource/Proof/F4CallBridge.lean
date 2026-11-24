import IxCK.Resource.Proof.F4Check
import IxCK.Resource.Proof.F4Default

/-!
# Call, Application, and PAP Simulation Bridges (`F4CallBridge`)

Bridges `Check.applyValue`, `Check.callResult`, `Check.papVal`, `AApps`, and runtime `.pap`
values to `EvalS` (`applyOneConformS`, `applyAllS`, `callWithS`, `makePap`, `enterS`, `staticS`,
`callExtern`):

1. **`FullIH`**: unified outer budget induction hypothesis covering `PapsFunOk`, checked + default
   `enterS`, and checked + default `staticS` (and `FullIH.to_DefaultCallIH`), plus `makePap_sound_once`
   and `conform` post-apply helpers.
2. **Runtime `.pap` `FunOkAt` theorems**: `pap_iface_funOk`, `pap_ctor_funOk`, `pap_prim_funOk`,
   and `FullIH_to_PapsFunOk` (proving `PapsFunOk P ext (B + 1)` from `FullIH P ext B`).
3. **Application bridges**: `applyValue_bridge` (`Runs_applyValue` + `FunOkAt` → `applyOneConformS`)
   and `applyAllS_bridge` (`AApps` → `applyAllS`).
4. **Direct-call & PAP-creation bridges**: `papVal_bridge`, `ctor_pap_bridge`, `prim_pap_bridge`,
   and `callResult_direct_bridge` (`ACall.ifaceFullPos` / `ACall.ifaceFullZero`).
-/

namespace IxCK.Resource.Proof

open IxCK.Resource Ixon

/-! ## 1. `FullIH` and `ifaceSkel` / `applyResultRegs` / `makePap_sound_once` Helpers -/

/-- Unified outer budget induction hypothesis at budget `B : Nat`, covering:
1. `PapsFunOk P ext b` for all `b ≤ B`;
2. `enterS` soundness for every body `P.find? r = some (.body params res rc rs body)` at `b ≤ B`;
3. `staticS` soundness for every 0-ary body `P.find? r = some (.body #[] res rc rs body)` at `b ≤ B`. -/
def FullIH (P : Prog) (ext : ExternOracle) (B : Nat) : Prop :=
  (∀ b, b ≤ B → PapsFunOk P ext b) ∧
  (∀ (b fuel : Nat) (r : Ref) (params : Array Param) (res : ResultMode) (rc : Cls)
     (rs : Skel) (body : Term) (vs : List Val) (st : St)
     (Frame : Nat → Prop) (argRegs : List Nat)
     (argOnce : Nat → Bool) (argFoot : Nat → Nat → Prop),
     b ≤ B →
     P.find? r = some (.body params res rc rs body) →
     vs.length = params.size →
     StOk P ext b st →
     (∀ l, StaticStrLoc st l → Frame l) →
     (∀ l, Frame l → l < st.heap.objs.size) →
     (∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → vs[i]? = some v →
       (p.mode ≠ .erased →
         ValBaseOk st v ∧
         DeepOpenUnder st.heap st.regions argRegs v ∧
         CtorFieldsOk P ext b st v ∧
         (p.mode.usage = .once →
           FunOkAt P ext b st p.skel (argOnce i) (argFoot i) v ∧
           (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
         (p.mode.usage ≠ .once →
           NoOnceCell st.heap v ∧ argOnce i = false ∧ (∀ l, ¬ argFoot i l) ∧
           FunOkAt P ext b st p.skel false (fun _ => False) v) ∧
         (p.mode.isUnique = true →
           OwnTreeFull P st.heap v ∧
           (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
           (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v)))) →
     (∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
       params[i]? = some pi → vs[i]? = some vi →
       params[j]? = some pj → vs[j]? = some vj →
       pj.mode ≠ .erased →
       (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) ∧
       (pi.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap vj l) ∧
       (pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, argFoot i l → ¬ argFoot j l)) →
     (∀ k, (enterS P ext fuel params res rc body vs).run (st, b) ≠ .error (.violation k)) ∧
     ∀ rv st' B',
       (enterS P ext fuel params res rc body vs).run (st, b) = .ok (rv, (st', B')) →
         B' ≤ b ∧
         StOk P ext B' st' ∧
         st.heap.objs.size ≤ st'.heap.objs.size ∧
         st.heap.nextCap ≤ st'.heap.nextCap ∧
         st'.regions = st.regions ∧
         st.nextRegion ≤ st'.nextRegion ∧
         ArrayExtends st.statics st'.statics ∧
         ArrayExtends st.strs st'.strs ∧
         PreservesLocs Frame st.heap st'.heap ∧
         PreservesOnceShell st.heap st'.heap ∧
         StaticStrFresh st st' ∧
         ValBaseOk st' rv ∧
         ClsSafe st'.heap rc rv ∧
         NoOnceCell st'.heap rv ∧
         CtorFieldsOk P ext B' st' rv ∧
         FunOkAt P ext B' st' rs false (fun _ => False) rv ∧
         DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc [] argRegs) rv ∧
         (∀ l, Reach st'.heap rv l →
           st.heap.objs.size ≤ l ∨
           (∃ (i : Nat) (p : Param) (v : Val),
             params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧
             (res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧
             Reach st.heap v l) ∨
           StaticStrLoc st l ∨
           NumLoc st'.heap l) ∧
         (res.isUnique = true ∧ rc = .val →
           OwnTreeFull P st'.heap rv ∧
           ∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l)) ∧
  (∀ (b fuel : Nat) (r : Ref) (res : ResultMode) (rc : Cls) (rs : Skel) (body : Term) (st : St),
     b ≤ B →
     P.find? r = some (.body #[] res rc rs body) →
     StOk P ext b st →
     (∀ k, (staticS P ext fuel r body rc).run (st, b) ≠ .error (.violation k)) ∧
     ∀ rv st' B',
       (staticS P ext fuel r body rc).run (st, b) = .ok (rv, (st', B')) →
         DefStep P ext b B' st st' ∧
         ValBaseOk st' rv ∧
         ClsSafe st'.heap rc rv ∧
         DeepOpenUnder st'.heap st'.regions [] rv ∧
         NoOnceCell st'.heap rv ∧
         CtorFieldsOk P ext B' st' rv ∧
         FunOkAt P ext B' st' rs false (fun _ => False) rv ∧
         ∀ l, Reach st'.heap rv l →
           st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l)

theorem FullIH.mono {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    (hle : B₁ ≤ B₂) (h : FullIH P ext B₂) : FullIH P ext B₁ :=
  ⟨fun b hb => h.1 b (Nat.le_trans hb hle),
   fun b fuel r params res rc rs body vs st Frame argRegs argOnce argFoot hb =>
     h.2.1 b fuel r params res rc rs body vs st Frame argRegs argOnce argFoot (Nat.le_trans hb hle),
   fun b fuel r res rc rs body st hb =>
     h.2.2 b fuel r res rc rs body st (Nat.le_trans hb hle)⟩

/-- `FullIH P ext B` immediately supplies `F4Default.DefaultCallIH P ext B`. -/
theorem FullIH.to_DefaultCallIH {P : Prog} {ext : ExternOracle} {B : Nat}
    (h : FullIH P ext B) : DefaultCallIH P ext B := by
  refine ⟨h.1, ?_, ?_⟩
  · intro B_call fuel r params res rc rs body vs st A hB hfind hdef hlen hst hvs
    obtain ⟨hpmSk, hresEq, hrsDef⟩ := hdef
    subst hresEq
    have hargs : ∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → vs[i]? = some v →
        (p.mode ≠ .erased →
          ValBaseOk st v ∧ DeepOpenUnder st.heap st.regions A v ∧ CtorFieldsOk P ext B_call st v ∧
          (p.mode.usage = .once →
            FunOkAt P ext B_call st p.skel false (fun _ => False) v ∧
            (∀ l, False → Reach st.heap v l ∧ ¬ (l < st.heap.objs.size) ∧ ¬ NumLoc st.heap l)) ∧
          (p.mode.usage ≠ .once →
            NoOnceCell st.heap v ∧ false = false ∧ (∀ l : Nat, ¬ False) ∧
            FunOkAt P ext B_call st p.skel false (fun _ => False) v) ∧
          (p.mode.isUnique = true →
            OwnTreeFull P st.heap v ∧ (∀ l, OwnReach P st.heap v l → ¬ (l < st.heap.objs.size)) ∧
            (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v))) := by
      intro i p v hp hv _
      have ⟨hpm, hpsk⟩ := hpmSk p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp))
      have hdv := hvs v (List.mem_of_getElem? hv)
      refine ⟨hdv.1, hdv.2.1, hdv.2.2.2.1,
        (fun hu => by rw [hpm] at hu; cases hu),
        (fun _ => ⟨hdv.2.2.1, rfl, fun _ h => h, (FunOkAt_default_equiv rfl hpsk).mp hdv.2.2.2.2⟩),
        (fun hu => by rw [hpm] at hu; cases hu)⟩
    have hdisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
        params[i]? = some pi → vs[i]? = some vi →
        params[j]? = some pj → vs[j]? = some vj → pj.mode ≠ .erased →
        (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) ∧
        (pi.mode.usage = .once → ∀ l, False → ¬ Reach st.heap vj l) ∧
        (pi.mode.usage = .once → pj.mode.usage = .once → ∀ l : Nat, False → ¬ False) := by
      intro i j pi _ _ _ _ hpi _ _ _ _
      have hpm := (hpmSk pi (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hpi))).1
      exact ⟨(fun hu => by rw [hpm] at hu; cases hu), fun _ _ h => False.elim h, fun _ _ _ h => False.elim h⟩
    obtain ⟨hnoV, hok⟩ := h.2.1 B_call fuel r params .shared rc rs body vs st
      (fun l => l < st.heap.objs.size) A (fun _ => false) (fun _ _ => False)
      hB hfind hlen hst (fun _ hl => StOk_staticStrLoc_lt hst hl) (fun _ hl => hl) hargs hdisj
    refine ⟨hnoV, fun rv st' B' hrun => ?_⟩
    obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
      hbase, hcls, hno, hcf, hfun, hopen, hreach, _⟩ := hok rv st' B' hrun
    have hopenA : DeepOpenUnder st'.heap st'.regions A rv := by
      by_cases hrc : rc = .val
      · subst hrc
        have hne : (Cls.val != Cls.val) = false := rfl
        simpa [applyResultRegs, hne] using hopen
      · exact ClsSafe_deepOpenUnder_nil hrc hcls
    refine ⟨⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf⟩,
      hcls, ⟨hbase, hopenA, hno, hcf, (FunOkAt_default_equiv hrsDef rfl).mp hfun⟩, ?_⟩
    intro l hl
    rcases hreach l hl with hnew | ⟨i, p, v, _, hv, _, _, hrv⟩ | hss | hnum
    · exact Or.inl hnew
    · exact Or.inr (Or.inl ⟨v, List.mem_of_getElem? hv, hrv⟩)
    · exact Or.inr (Or.inr (Or.inl hss))
    · exact Or.inr (Or.inr (Or.inr hnum))
  · intro B_call fuel r res rc rs body st hB hfind hdef hst
    obtain ⟨_, hresEq, hrsDef⟩ := hdef
    subst hresEq
    obtain ⟨hnoV, hok⟩ := h.2.2 B_call fuel r .shared rc rs body st hB hfind hst
    refine ⟨hnoV, fun rv st' B' hrun => ?_⟩
    obtain ⟨hstep, hbase, hcls, hopen, hno, hcf, hfun, hreach⟩ := hok rv st' B' hrun
    exact ⟨hstep, hcls, ⟨hbase, hopen, hno, hcf, (FunOkAt_default_equiv hrsDef rfl).mp hfun⟩, hreach⟩

theorem list_drop_eq_cons {α : Type} {l : List α} {k : Nat} (hk : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k' => exact ih (by simpa using hk)

theorem OwnReach_of_sameShapeOn {P : Prog} {h₁ h₂ : Heap} {v₁ v₂ : Val} {l : Nat}
    (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hor : OwnReach P h₁ v₁ l) : OwnReach P h₂ v₂ l := by
  induction hor generalizing v₂ with
  | @here loc cap t o₁ ho₁ hnot =>
    cases v₂ with
    | imm _ => cases hloc
    | ref l₂ c₂ t₂ =>
      simp only [SameLoc] at hloc; subst hloc
      obtain ⟨o₂, ho₂, hcs⟩ := hs loc o₁ .here ho₁
      exact .here ho₂ (hcs.isNum_eq ▸ hnot)
  | @step loc cap t o₁ i w₁ l' ho₁ hi hsl _ ih =>
    cases v₂ with
    | imm _ => cases hloc
    | ref l₂ c₂ t₂ =>
      simp only [SameLoc] at hloc; subst hloc
      obtain ⟨o₂, ho₂, hcs⟩ := hs loc o₁ .here ho₁
      have hslot := hcs.slot? i
      rw [hsl] at hslot
      cases hs2 : o₂.cell.slot? i with
      | none => rw [hs2] at hslot; cases hslot
      | some w₂ =>
        rw [hs2] at hslot
        have hw₁Mem : w₁ ∈ o₁.cell.vals := mem_vals_of_ownedSlot hi hsl
        have hs' : SameShapeOn (Reach h₁ w₁) h₁ h₂ := hs.mono fun x hx => .step ho₁ hw₁Mem hx
        exact .step ho₂ (hcs.ownedSlots_eq ▸ hi) hs2 (ih hs' (SameLoc.of_valSameShape hslot))

theorem OwnReach_of_sameShapeOn_rev {P : Prog} {h₁ h₂ : Heap} {v₁ v₂ : Val} {l : Nat}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hor : OwnReach P h₂ v₂ l) : OwnReach P h₁ v₁ l := by
  induction hor generalizing v₁ with
  | @here loc cap t o₂ ho₂ hnot =>
    cases v₁ with
    | imm _ => cases hloc
    | ref l₁ c₁ t₁ =>
      simp only [SameLoc] at hloc; subst hloc
      obtain ⟨o₁, ho₁, _⟩ := hdl.self.1
      obtain ⟨o₂', ho₂', hcs⟩ := hs l₁ o₁ .here ho₁
      rw [ho₂] at ho₂'; cases ho₂'
      exact .here ho₁ (hcs.isNum_eq.symm ▸ hnot)
  | @step loc cap t o₂ i w₂ l' ho₂ hi hsl _ ih =>
    cases v₁ with
    | imm _ => cases hloc
    | ref l₁ c₁ t₁ =>
      simp only [SameLoc] at hloc; subst hloc
      obtain ⟨o₁, ho₁, _⟩ := hdl.self.1
      obtain ⟨o₂', ho₂', hcs⟩ := hs l₁ o₁ .here ho₁
      rw [ho₂] at ho₂'; cases ho₂'
      have hslot := hcs.slot? i
      rw [hsl] at hslot
      cases hs1 : o₁.cell.slot? i with
      | none => rw [hs1] at hslot; cases hslot
      | some w₁ =>
        rw [hs1] at hslot
        have hi₁ : i ∈ ownedSlots P o₁.cell := hcs.ownedSlots_eq.symm ▸ hi
        have hw₁Mem : w₁ ∈ o₁.cell.vals := mem_vals_of_ownedSlot hi₁ hs1
        have hdlW : DeepLive h₁ w₁ := hdl.sub (HeldBy_of_mem_vals ho₁ hw₁Mem)
        have hs' : SameShapeOn (Reach h₁ w₁) h₁ h₂ := hs.mono fun x hx => .step ho₁ hw₁Mem hx
        exact .step ho₁ hi₁ hs1 (ih hdlW hs' (SameLoc.of_valSameShape hslot))

theorem OwnTreeFull_of_sameShapeOn {P : Prog} {h₁ h₂ : Heap} {v₁ v₂ : Val}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (htree : OwnTreeFull P h₁ v₁) : OwnTreeFull P h₂ v₂ := by
  constructor
  · intro p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnot
    have hp₁' := OwnReach_of_sameShapeOn_rev hdl hs hloc hp₁
    have hp₂' := OwnReach_of_sameShapeOn_rev hdl hs hloc hp₂
    have hrp₁ := OwnReach_toReach hp₁'
    have hrp₂ := OwnReach_toReach hp₂'
    obtain ⟨o₁', ho₁'⟩ := hdl.exists_obj hrp₁
    obtain ⟨o₂', ho₂'⟩ := hdl.exists_obj hrp₂
    obtain ⟨o₁'', ho₁'', hcs₁⟩ := hs p₁ o₁' hrp₁ ho₁'
    obtain ⟨o₂'', ho₂'', hcs₂⟩ := hs p₂ o₂' hrp₂ ho₂'
    rw [ho₁] at ho₁''; cases ho₁''
    rw [ho₂] at ho₂''; cases ho₂''
    have hsl₁ := hcs₁.slot? i₁; rw [hs₁] at hsl₁
    cases h1 : o₁'.cell.slot? i₁ with
    | none => rw [h1] at hsl₁; cases hsl₁
    | some w₁ =>
      rw [h1] at hsl₁
      cases w₁ with
      | imm _ => cases hsl₁
      | ref l₁' c₁' t₁' =>
        have hl1Eq : l₁' = l := hsl₁.1
        rw [hl1Eq] at h1
        have hsl₂ := hcs₂.slot? i₂; rw [hs₂] at hsl₂
        cases h2 : o₂'.cell.slot? i₂ with
        | none => rw [h2] at hsl₂; cases hsl₂
        | some w₂ =>
          rw [h2] at hsl₂
          cases w₂ with
          | imm _ => cases hsl₂
          | ref l₂' c₂' t₂' =>
            have hl2Eq : l₂' = l := hsl₂.1
            rw [hl2Eq] at h2
            have hi₁' : i₁ ∈ ownedSlots P o₁'.cell := hcs₁.ownedSlots_eq.symm ▸ hi₁
            have hnot' : ∀ o, h₁.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf := by
              intro o ho
              have hrl1 : Reach h₁ v₁ l :=
                Reach_of_HeldBy (Or.inr ⟨p₁, o₁', hrp₁, ho₁', mem_vals_of_ownedSlot hi₁' h1⟩) .here
              obtain ⟨o', ho', hcsL⟩ := hs l o hrl1 ho
              exact hcsL.isNum_eq ▸ hnot o' ho'
            exact htree.1 p₁ p₂ i₁ i₂ l c₁' c₂' o₁' o₂' t₁' t₂' hp₁' hp₂' ho₁' ho₂'
              hi₁' (hcs₂.ownedSlots_eq.symm ▸ hi₂) h1 h2 hnot'
  · intro p l i o₂ r fs₂ w₂ hp ho₂ hc₂ hnotOwn hfs₂ hl hr₂
    have hp₁ := OwnReach_of_sameShapeOn_rev hdl hs hloc hp
    have hl₁ := OwnReach_of_sameShapeOn_rev hdl hs hloc hl
    have hrp₁ := OwnReach_toReach hp₁
    obtain ⟨o₁, ho₁⟩ := hdl.exists_obj hrp₁
    obtain ⟨o₂', ho₂', hcs⟩ := hs p o₁ hrp₁ ho₁
    rw [ho₂] at ho₂'; cases ho₂'
    have hcsRaw := hcs
    rw [hc₂] at hcs
    cases hc₁ : o₁.cell with
    | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ => rw [hc₁] at hcs; cases hcs
    | ctor r₁ fs₁ =>
      rw [hc₁] at hcs
      obtain ⟨rfl, hszEq, hvsAll⟩ := hcs
      have hi₂ : i < fs₂.size := (Array.getElem?_eq_some_iff.mp hfs₂).1
      have hi₁ : i < fs₁.size := hszEq ▸ hi₂
      have hvsW := hvsAll i hi₁ hi₂
      rw [Array.getElem?_eq_getElem hi₂] at hfs₂; cases hfs₂
      have hmem₁ : fs₁[i] ∈ o₁.cell.vals := by
        rw [hc₁]; exact Array.mem_toList_iff.mpr (Array.getElem_mem hi₁)
      have hdlW : DeepLive h₁ fs₁[i] :=
        hdl.sub (Or.inr ⟨p, o₁, hrp₁, ho₁, hmem₁⟩)
      have hsW : SameShapeOn (Reach h₁ fs₁[i]) h₁ h₂ :=
        hs.mono fun x hx => Reach_of_HeldBy (Or.inr ⟨p, o₁, hrp₁, ho₁, hmem₁⟩) hx
      have hr₁ : Reach h₁ fs₁[i] l :=
        Reach_of_sameShapeOn_rev hdlW hsW (SameLoc.of_valSameShape hvsW) hr₂
      have hnotOwn₁ : i ∉ ownedSlots P o₁.cell := fun h => hnotOwn (by
        have hEq : ownedSlots P o₁.cell = ownedSlots P o₂.cell := hcsRaw.ownedSlots_eq
        exact hEq ▸ h)
      exact htree.2 p l i o₁ r₁ fs₁ fs₁[i] hp₁ ho₁ hc₁ hnotOwn₁ (Array.getElem?_eq_getElem hi₁) hl₁ hr₁

theorem DeepOpenUnder_of_sameShapeOn {h₁ h₂ : Heap} {rs A : List Nat} {v₁ v₂ : Val}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hvs : ValSameShape v₁ v₂)
    (hd : DeepOpenUnder h₁ rs A v₁) : DeepOpenUnder h₂ rs A v₂ := by
  intro w₂ hw₂ r hr hopen
  rcases hw₂ with rfl | ⟨l, o₂, hrl₂, ho₂, hm₂⟩
  · rw [← hvs.taint_eq] at hr
    exact hd v₁ (HeldBy.refl _ _) r hr hopen
  · have hrl₁ : Reach h₁ v₁ l := Reach_of_sameShapeOn_rev hdl hs (SameLoc.of_valSameShape hvs) hrl₂
    obtain ⟨o₁, ho₁⟩ := hdl.exists_obj hrl₁
    obtain ⟨o₂', ho₂', hcs⟩ := hs l o₁ hrl₁ ho₁
    rw [ho₂] at ho₂'; cases ho₂'
    obtain ⟨w₁, hm₁, hvsW⟩ := hcs.symm.vals_fwd hm₂
    rw [hvsW.taint_eq] at hr
    exact hd w₁ (Or.inr ⟨l, o₁, hrl₁, ho₁, hm₁⟩) r hr hopen

theorem ClsSafe_ownTreeFull {P : Prog} {h : Heap} {rc : Cls} {v : Val}
    (hne : rc ≠ .val) (hc : ClsSafe h rc v) :
    OwnTreeFull P h v ∧ ∀ l, ¬ OwnReach P h v l := by
  have hnoOwn : ∀ l, ¬ OwnReach P h v l := by
    intro l hor
    rcases hc with rfl | hc
    · cases hor
    · cases rc with
      | irr => rw [hc] at hor; cases hor
      | imm => obtain ⟨_, rfl⟩ := hc; cases hor
      | leaf =>
        obtain ⟨loc, cap, o, n, rfl, ho, hnum, _⟩ := hc
        cases hor with
        | here ho' hnot =>
          rw [ho] at ho'; cases ho'
          rcases hnot with h1 | h2
          · rw [hnum] at h1; cases h1
          · exact h2 rfl
        | step ho' hm' _ _ =>
          rw [ho] at ho'; cases ho'; rw [hnum] at hm'; cases hm'
      | val => exact absurd rfl hne
  refine ⟨?_, hnoOwn⟩
  rcases hc with rfl | hc
  · exact OwnTreeFull_imm P h .irr
  · cases rc with
    | irr => rw [hc]; exact OwnTreeFull_imm P h .irr
    | imm => obtain ⟨_, rfl⟩ := hc; exact OwnTreeFull_imm P h _
    | leaf =>
      obtain ⟨loc, cap, o, n, rfl, ho, hnum, _⟩ := hc
      exact OwnTreeFull_num ho hnum
    | val => exact absurd rfl hne

theorem arrowParts_ifaceSkel_singleton (p : Param) (res : ResultMode) (cod : Skel) :
    arrowParts (ifaceSkel [p] res cod) = (p.mode, p.skel, res, cod) := rfl

theorem arrowParts_ifaceSkel_cons₂ (p₁ p₂ : Param) (ps : List Param) (res : ResultMode) (cod : Skel) :
    arrowParts (ifaceSkel (p₁ :: p₂ :: ps) res cod) =
      (p₁.mode, p₁.skel, .shared, ifaceSkel (p₂ :: ps) res cod) := rfl

theorem isArrowSkel_ifaceSkel_cons (p : Param) (ps : List Param) (res : ResultMode) (cod : Skel) :
    isArrowSkel (ifaceSkel (p :: ps) res cod) = true := by
  cases ps <;> rfl

theorem applyOneConformS_val_eq_applyOneS (P : Prog) (ext : ExternOracle) (fuel : Nat)
    (f a : Val) (st : St) (B : Nat) :
    (applyOneConformS P ext fuel f a .val).run (st, B) =
      (applyOneS P ext fuel f a .val).run (st, B) := by
  unfold applyOneConformS
  rw [MS_bind_run]
  cases (applyOneS P ext fuel f a .val).run (st, B) with
  | error e => rfl
  | ok p =>
    rcases p with ⟨g, ⟨st', B'⟩⟩
    dsimp only
    rw [MS_liftM_run]
    rfl

theorem applyResultRegs_mono {st : St} {res : ResultMode} {c : Cls}
    {fRegs₁ fRegs₂ aRegs₁ aRegs₂ : List Nat}
    (hf : ∀ x ∈ fRegs₁, x ∈ fRegs₂) (ha : ∀ x ∈ aRegs₁, x ∈ aRegs₂) :
    ∀ x ∈ applyResultRegs st res c fRegs₁ aRegs₁, x ∈ applyResultRegs st res c fRegs₂ aRegs₂ := by
  intro x hx
  unfold applyResultRegs at hx ⊢
  cases hc : (c != .val) with
  | true => simp only [hc, ↓reduceIte] at hx ⊢; exact hx
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    cases res with
    | unique => exact hf x hx
    | shared =>
      rcases List.mem_append.mp hx with h1 | h2
      · exact List.mem_append_left _ (ha x h1)
      · exact List.mem_append_right _ (hf x h2)
    | borrowed | uniqueBorrowed =>
      cases hreg : st.regions with
      | nil =>
        simp only [hreg] at hx ⊢
        rcases List.mem_append.mp hx with h1 | h2
        · exact List.mem_append_left _ (ha x h1)
        · exact List.mem_append_right _ (hf x h2)
      | cons cur rs =>
        simp only [hreg, List.mem_cons] at hx ⊢
        rcases hx with rfl | h2
        · exact Or.inl rfl
        · rcases List.mem_append.mp h2 with h2a | h2b
          · exact Or.inr (List.mem_append_left _ (ha x h2a))
          · exact Or.inr (List.mem_append_right _ (hf x h2b))

theorem applyResultRegs_sub_of_pap {st : St} {res : ResultMode} {rc : Cls}
    {fRegs aRegs : List Nat} :
    ∀ x ∈ applyResultRegs st res rc fRegs (aRegs ++ fRegs),
      x ∈ applyResultRegs st res .val fRegs aRegs := by
  intro x hx
  unfold applyResultRegs at hx ⊢
  have hvalF : (Cls.val != Cls.val) = false := rfl
  simp only [hvalF, Bool.false_eq_true, ↓reduceIte]
  cases hrc : (rc != .val) with
  | true => simp only [hrc, ↓reduceIte] at hx; cases hx
  | false =>
    simp only [hrc, Bool.false_eq_true, ↓reduceIte] at hx
    cases res with
    | unique => exact hx
    | shared =>
      rcases List.mem_append.mp hx with h1 | h2
      · exact h1
      · exact List.mem_append_right _ h2
    | borrowed | uniqueBorrowed =>
      cases hreg : st.regions with
      | nil =>
        simp only [hreg] at hx ⊢
        rcases List.mem_append.mp hx with h1 | h2
        · exact h1
        · exact List.mem_append_right _ h2
      | cons cur rs =>
        simp only [hreg, List.mem_cons] at hx ⊢
        rcases hx with rfl | h2
        · exact Or.inl rfl
        · rcases List.mem_append.mp h2 with h2a | h2b
          · exact Or.inr h2a
          · exact Or.inr (List.mem_append_right _ h2b)

/-- Helper: `conform c` after `enterS`/`callExtern`/`makePap` preserves `StOk` + `ValBaseOk` +
`DeepOpenUnder` (clamping to `[]` when `c ≠ .val`), `NoOnceCell`, `CtorFieldsOk`, `FunOkAt`,
and `Reach` bounds. -/
theorem conform_post_apply {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {c : Cls} {sk : Skel} {res : ResultMode} {onceOnly : Bool}
    {Foot : Nat → Prop} {v : Val} {fRegs aRegs : List Nat}
    (hst : StOk P ext B st)
    (hbase : ValBaseOk st v)
    (hcf : CtorFieldsOk P ext B st v)
    (hno : onceOnly = false → NoOnceCell st.heap v)
    (hfun : FunOkAt P ext B st sk onceOnly Foot v)
    (hopen : c = .val → DeepOpenUnder st.heap st.regions (applyResultRegs st res .val fRegs aRegs) v) :
    (conform c v).run st = .error .stuck ∨
    ∃ rv st', (conform c v).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' rv ∧
      ClsSafe st'.heap c rv ∧
      DeepOpenUnder st'.heap st'.regions (applyResultRegs st res c fRegs aRegs) rv ∧
      CtorFieldsOk P ext B st' rv ∧
      (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
      (onceOnly = false → NoOnceCell st'.heap rv) ∧
      FunOkAt P ext B st' sk onceOnly Foot rv ∧
      (c = .val → rv = v ∧ st' = st) := by
  rcases conform_sound hst hbase hcf hno hfun with hSt |
    ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf,
     hst', hbv', hcls', hcf', hdou', hreach', _, _, hno', hvalEq, _, hfun'⟩
  · exact Or.inl hSt
  · right
    have hdouRes : DeepOpenUnder st'.heap st'.regions (applyResultRegs st res c fRegs aRegs) rv := by
      by_cases hcv : c = .val
      · subst hcv
        rw [hr]; exact hdou' st.regions _ (hopen rfl)
      · have hne : (c != .val) = true := by
          cases hc : c with
          | val => exact absurd hc hcv
          | irr | imm | leaf => rfl
        simpa [applyResultRegs, hne] using ClsSafe_deepOpenUnder_nil hcv hcls'
    exact ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf,
      hst', hbv', hcls', hdouRes, hcf', hreach', hno', hfun', hvalEq⟩

/-- Calling `conform c` a second time on a value already `ClsSafe st.heap c v` either gets `.stuck`
(only for `.leaf` on `.imm .irr`) or returns `(v, st)` unchanged. -/
theorem conform_idem_of_clsSafe {st : St} {c : Cls} {v : Val}
    (hbase : ValBaseOk st v) (hcls : ClsSafe st.heap c v) :
    (conform c v).run st = .error .stuck ∨ (conform c v).run st = .ok (v, st) := by
  cases c with
  | val => exact Or.inr rfl
  | irr =>
    rcases hcls with rfl | rfl <;> exact Or.inr rfl
  | imm =>
    rcases hcls with rfl | ⟨i, rfl⟩ <;> exact Or.inr rfl
  | leaf =>
    rcases hcls with rfl | ⟨loc, cap, o, n, rfl, ho, hnum, _⟩
    · exact Or.inl rfl
    · right
      obtain ⟨o', ho', hcap'⟩ := hbase.1.self.1
      rw [ho] at ho'; cases ho'
      unfold conform
      rw [M_bind_run]
      have hnumRun : (numOf? (.ref loc cap [])).run st = .ok (some n, st) := by
        unfold numOf?; rw [M_bind_run, obj_ok ho]
        have hbeq : (o.cap == cap) = true := by rw [hcap']; simp
        simp only [hbeq, ↓reduceIte, hnum]; rfl
      rw [hnumRun]; rfl

/-- `Eval.makePap` lifted to `F4Inv` predicates, allowing `.once` arguments at non-unique
positions while preserving `NoOnceCell` whenever every argument satisfies `NoOnceCell`. -/
theorem makePap_sound_once {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {r : Ref} {params : Array Param} {vs : List Val} {st : St}
    (hst : StOk P ext B st)
    (hvs : ∀ v ∈ vs, ValBaseOk st v ∧ CtorFieldsOk P ext B st v)
    (huniq : ∀ (i : Nat) (v : Val), vs[i]? = some v →
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      NoOnceCell st.heap v ∧ OwnTreeFull P st.heap v ∧
      (((params[i]?.map Param.mode).getD BinderMode.many).isBorrowed = false → OpenUnder st.regions [] v) ∧
      ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l)
    (hdisj : ∀ (i j : Nat) (vi vj : Val), i ≠ j →
      vs[i]? = some vi → vs[j]? = some vj →
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) :
    (makePap P fuel r params vs).run st = .error .outOfFuel ∨
    ∃ rv out st', (makePap P fuel r params vs).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size + 1 ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧
          ∀ (i : Nat) (v : Val), vs[i]? = some v →
            ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true → ¬ OwnReach P st.heap v l)
        st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      (∃ cap, rv = .ref st.heap.objs.size cap (taints out.toList) ∧
        st'.heap.objs[st.heap.objs.size]? = some ⟨.pap r out, cap⟩) ∧
      out.size = vs.length ∧
      (∀ (i : Nat) (v : Val), vs[i]? = some v →
        ∃ w, out[i]? = some w ∧ ValSameShape v w ∧ ValBaseOk st' w ∧
          (NoOnceCell st.heap v → NoOnceCell st'.heap w) ∧
          CtorFieldsOk P ext B st' w ∧
          (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot v →
            FunOkAt P ext B st' sk onceOnly Foot w)) ∧
      ValBaseOk st' rv ∧
      ((∀ v ∈ vs, NoOnceCell st.heap v) → NoOnceCell st'.heap rv) ∧
      CtorFieldsOk P ext B st' rv ∧
      (∀ rs A, (∀ v ∈ vs, DeepOpenUnder st.heap rs A v) → DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l → l = st.heap.objs.size ∨ ∃ v ∈ vs, Reach st.heap v l) := by
  rcases makePap_spec (P := P) (fuel := fuel) (r := r) (params := params) (vs := vs) hst.1
    (fun v hv => ⟨(hvs v hv).1.1, (hvs v hv).1.2.1⟩)
    (fun i v hv hu => ⟨(huniq i v hv hu).2.1, (huniq i v hv hu).2.2.1⟩)
    hdisj with hOOF |
    ⟨rv, out, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hc', hoss, hpres, hrvObj, houtSz,
      houtShape, htRv, hdl', hacyc', _, hdou', hreach'⟩
  · exact Or.inl hOOF
  · right
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    let S : Nat → Prop := fun l => ∃ (i : Nat) (v : Val), vs[i]? = some v ∧
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true ∧ OwnReach P st.heap v l
    have hpresS : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ S l) st.heap st'.heap :=
      hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun i v hv hu hor => hnot ⟨i, v, hv, hu, hor⟩⟩
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_oldSameShape_noOnce hpresS
        (fun l o₁ t₁ sp₁ ⟨i, v, hv, hu, hor⟩ ho₁ hc₁ =>
          (huniq i v hv hu).1 l o₁ (OwnReach_toReach hor) ho₁ t₁ sp₁ hc₁)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside hst hstat hstr hpresS
        (fun l hss ⟨i, v, hv, hu, hor⟩ => (huniq i v hv hu).2.2.2 l hor hss)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_outside hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpresS
        (fun l hss ⟨i, v, hv, hu, hor⟩ => (huniq i v hv hu).2.2.2 l hor hss)
    obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
    have houtProps : ∀ (i : Nat) (v : Val), vs[i]? = some v →
        ∃ w, out[i]? = some w ∧ ValSameShape v w ∧ ValBaseOk st' w ∧
          (NoOnceCell st.heap v → NoOnceCell st'.heap w) ∧
          CtorFieldsOk P ext B st' w ∧
          (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot v →
            FunOkAt P ext B st' sk onceOnly Foot w) := by
      intro i v hv
      obtain ⟨w, hw, hvsh⟩ := houtShape i v hv
      have hvMem : v ∈ vs := List.mem_of_getElem? hv
      obtain ⟨hbv, hcfv⟩ := hvs v hvMem
      have hwMem : w ∈ out.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw)
      have hwHeld : HeldBy st'.heap rv w := by
        rw [hrvEq]; exact HeldBy_of_mem_vals hoNew (by simpa [Cell.vals] using hwMem)
      have hdlW : DeepLive st'.heap w := hdl'.sub hwHeld
      have hacycW : AcyclicFrom st'.heap w := hacyc'.sub hwHeld
      have hlocW : SameLoc v w := SameLoc.of_valSameShape hvsh
      have htbW : DeepTaintsBounded st'.heap st'.nextRegion w := by
        rw [hnr]
        exact DeepTaintsBounded_of_oldSameShape hbv.1 hoss hlocW
          (fun x hx => by
            have htEq : w.taint = v.taint := by
              cases v <;> cases w <;> simp [ValSameShape, Val.taint] at hvsh ⊢
              exact hvsh.2.symm
            rw [htEq] at hx; exact hbv.2.2.2 v (HeldBy.refl _ _) x hx)
          hbv.2.2.2
      exact ⟨w, hw, hvsh, ValBaseOk_of_deepLive hdlW hacycW htbW,
        fun hnov => NoOnceCell_of_sameShape hbv.1 (hoss.to_sameShapeOn _) hlocW hnov,
        CtorFieldsOk_of_sameShape hbv.1 (hoss.to_sameShapeOn _) hlocW hrf hcfv,
        fun sk oo ft hf => FunOkAt_preserve_sameShape hlocW (hoss.to_sameShapeOn _) hrf hf⟩
    have houtMem : ∀ w ∈ out.toList, ValBaseOk st' w ∧
        ((∀ v ∈ vs, NoOnceCell st.heap v) → NoOnceCell st'.heap w) ∧
        CtorFieldsOk P ext B st' w := by
      intro w hw
      obtain ⟨i, hi, hwi⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hw)
      have hiV : i < vs.length := houtSz ▸ hi
      obtain ⟨w', hw', _, hbw', hno', hcf', _⟩ := houtProps i vs[i] (List.getElem?_eq_getElem hiV)
      rw [Array.getElem?_eq_getElem hi] at hw'; cases hw'; subst hwi
      exact ⟨hbw', fun hall => hno' (hall vs[i] (List.getElem_mem hiV)), hcf'⟩
    have htbRv : DeepTaintsBounded st'.heap st'.nextRegion rv := by
      intro w hw x hx
      rcases hw with rfl | ⟨l, o', hr', ho', hm'⟩
      · obtain ⟨v, hv, hxv⟩ := (htRv x).mp hx
        rw [hnr]; exact (hvs v hv).1.2.2.2 v (HeldBy.refl _ _) x hxv
      · rw [hrvEq] at hr'
        cases hr' with
        | here =>
          rw [hoNew] at ho'; cases ho'
          exact (houtMem w (by simpa [Cell.vals] using hm')).1.2.2.2 w (HeldBy.refl _ _) x hx
        | step ho1 hm1 hr2 =>
          rw [hoNew] at ho1; cases ho1
          exact (houtMem _ (by simpa [Cell.vals] using hm1)).1.2.2.2 w (Or.inr ⟨l, o', hr2, ho', hm'⟩) x hx
    have hnoRv : (∀ v ∈ vs, NoOnceCell st.heap v) → NoOnceCell st'.heap rv := by
      intro hall l o hr' ho' t sp hcell
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        exact (houtMem _ (by simpa [Cell.vals] using hm1)).2.1 hall l o hr2 ho' t sp hcell
    have hcfRv : CtorFieldsOk P ext B st' rv := by
      intro l o rc fs w hr' ho' hcell hw
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        exact (houtMem _ (by simpa [Cell.vals] using hm1)).2.2 l o rc fs w hr2 ho' hcell hw
    exact ⟨rv, out, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hoss, hpres, honceSh, hssf, hst',
      ⟨cap, hrvEq, hoNew⟩, houtSz, houtProps, ValBaseOk_of_deepLive hdl' hacyc' htbRv,
      hnoRv, hcfRv, hdou', hreach'⟩

/-- Helper: `ValBaseOk` + `DeepOpenUnder` + `CtorFieldsOk` on `out[i]` inside a `.pap r out` cell
lifted across `SameShapeOn` + `RegsFuture`. -/
private theorem pap_arg_lift {P : Prog} {ext : ExternOracle} {B : Nat}
    {st₀ st : St} {loc cap cap' : Nat} {t₀ t' : List Nat}
    {r : Ref} {out₀ out : Array Val} {fRegs : List Nat}
    (ho₀ : st₀.heap.objs[loc]? = some ⟨.pap r out₀, cap⟩)
    (ho : st.heap.objs[loc]? = some ⟨.pap r out, cap'⟩)
    (hsh : SameShapeOn (Reach st₀.heap (.ref loc cap t₀)) st₀.heap st.heap)
    (hfBase : ValBaseOk st (.ref loc cap' t'))
    (hfOpen : DeepOpenUnder st.heap st.regions fRegs (.ref loc cap' t'))
    (hfCf : CtorFieldsOk P ext B st (.ref loc cap' t')) :
    out.size = out₀.size ∧
    ∀ (i : Nat) (w₀ w : Val), out₀[i]? = some w₀ → out[i]? = some w →
      ValSameShape w₀ w ∧
      SameLoc w₀ w ∧
      SameShapeOn (Reach st₀.heap w₀) st₀.heap st.heap ∧
      ValBaseOk st w ∧
      DeepOpenUnder st.heap st.regions fRegs w ∧
      CtorFieldsOk P ext B st w ∧
      (∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l) := by
  obtain ⟨o₂, ho₂, hcs⟩ := hsh loc ⟨.pap r out₀, cap⟩ .here ho₀
  rw [ho] at ho₂; cases ho₂
  dsimp only [CellSameShape] at hcs
  obtain ⟨_, hszEq, hvsAll⟩ := hcs
  refine ⟨hszEq.symm, fun i w₀ w hw₀ hw => ?_⟩
  have hi₀ : i < out₀.size := (Array.getElem?_eq_some_iff.mp hw₀).1
  have hi : i < out.size := (Array.getElem?_eq_some_iff.mp hw).1
  have hvs := hvsAll i hi₀ hi
  rw [Array.getElem?_eq_getElem hi₀] at hw₀; cases hw₀
  rw [Array.getElem?_eq_getElem hi] at hw; cases hw
  have hmem₀ : out₀[i] ∈ (⟨.pap r out₀, cap⟩ : Obj).cell.vals := by
    dsimp [Cell.vals]; exact Array.mem_toList_iff.mpr (Array.getElem_mem hi₀)
  have hmem : out[i] ∈ (⟨.pap r out, cap'⟩ : Obj).cell.vals := by
    dsimp [Cell.vals]; exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  have hheld : HeldBy st.heap (.ref loc cap' t') out[i] := HeldBy_of_mem_vals ho hmem
  exact ⟨hvs, SameLoc.of_valSameShape hvs,
    hsh.mono fun l hl => .step ho₀ hmem₀ hl,
    hfBase.sub hheld, hfOpen.sub hheld, CtorFieldsOk.sub hfCf hheld,
    fun l hl => .step ho hmem hl⟩

/-! ## 2. Runtime `.pap` `FunOkAt` Theorems & `PapsFunOk` -/

theorem applyResultRegs_eq_of_regions {st₁ st₂ : St} {res : ResultMode} {c : Cls}
    {fRegs aRegs : List Nat} (hr : st₁.regions = st₂.regions) :
    applyResultRegs st₁ res c fRegs aRegs = applyResultRegs st₂ res c fRegs aRegs := by
  unfold applyResultRegs; rw [hr]

/-- Helper finishing `(applyAllS P ext n' g [] c) >>= conform c` for a saturated `.pap` call. -/
private theorem pap_sat_finish {P : Prog} {ext : ExternOracle} {b'' n' : Nat}
    {st st₁ : St} {B₁ : Nat} {f a g : Val} {c rc' : Cls} {res : ResultMode} {resSkel : Skel}
    {onceOnly : Bool} {m_in : BinderMode} {Frame : Nat → Prop} {fRegs aRegs : List Nat}
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hB₁ : B₁ ≤ b'')
    (hst₁ : StOk P ext B₁ st₁)
    (hsz₁ : st.heap.objs.size ≤ st₁.heap.objs.size)
    (hcap₁ : st.heap.nextCap ≤ st₁.heap.nextCap)
    (hr₁ : st₁.regions = st.regions)
    (hnr₁ : st.nextRegion ≤ st₁.nextRegion)
    (hstat₁ : ArrayExtends st.statics st₁.statics)
    (hstr₁ : ArrayExtends st.strs st₁.strs)
    (hpres₁ : PreservesLocs Frame st.heap st₁.heap)
    (honce₁ : PreservesOnceShell st.heap st₁.heap)
    (hssf₁ : StaticStrFresh st st₁)
    (hbaseG : ValBaseOk st₁ g)
    (hclsG : ClsSafe st₁.heap rc' g)
    (hnoG : NoOnceCell st₁.heap g)
    (hcfG : CtorFieldsOk P ext B₁ st₁ g)
    (hfunG : FunOkAt P ext B₁ st₁ resSkel false (fun _ => False) g)
    (hopenG : c = .val → DeepOpenUnder st₁.heap st₁.regions (applyResultRegs st res .val fRegs aRegs) g)
    (hreachG : ∀ l, Reach st₁.heap g l →
      st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ Reach st.heap a l ∨
      StaticStrLoc st l ∨ NumLoc st₁.heap l)
    (huniqG : res.isUnique = true ∧ rc' = .val →
      OwnTreeFull P st₁.heap g ∧
      ∀ l, OwnReach P st₁.heap g l → ¬ Frame l ∧ ¬ StaticStrLoc st₁ l)
    (hnoArgG : res = .unique → (m_in.isBorrowed = true ∨ m_in = .erased) →
      ∀ l, Reach st₁.heap g l →
        st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨
        StaticStrLoc st l ∨ NumLoc st₁.heap l) :
    (∀ k', (match (applyAllS P ext n' g [] c).run (st₁, B₁) with
      | .error e => (Except.error e : Except Stop (Val × St × Nat))
      | .ok (g1, (st₂, B₂)) =>
        match (conform c g1).run st₂ with
        | .error e => .error e
        | .ok (rv, st₃) => .ok (rv, (st₃, B₂))) ≠ .error (.violation k')) ∧
    ∀ rv st' B',
      (match (applyAllS P ext n' g [] c).run (st₁, B₁) with
      | .error e => (Except.error e : Except Stop (Val × St × Nat))
      | .ok (g1, (st₂, B₂)) =>
        match (conform c g1).run st₂ with
        | .error e => .error e
        | .ok (rv, st₃) => .ok (rv, (st₃, B₂))) = .ok (rv, (st', B')) →
      ∃ (_ : B' ≤ b'' + 1),
        StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧
        st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧
        ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        ValBaseOk st' rv ∧
        ClsSafe st'.heap c rv ∧
        DeepOpenUnder st'.heap st'.regions (applyResultRegs st res c fRegs aRegs) rv ∧
        CtorFieldsOk P ext B' st' rv ∧
        (∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ Reach st.heap a l ∨
          StaticStrLoc st l ∨ NumLoc st'.heap l) ∧
        (let resOnce := isArrowSkel resSkel && (onceOnly || m_in.isUnique || m_in.usage == .once)
         (resOnce = false → NoOnceCell st'.heap rv ∧ FunOkAt P ext B' st' resSkel false (fun _ => False) rv) ∧
         (resOnce = true → ∃ resFoot,
           (∀ l, resFoot l → Reach st'.heap rv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l) ∧
           FunOkAt P ext B' st' resSkel true resFoot rv)) ∧
        (res.isUnique = true ∧ c = .val →
          OwnTreeFull P st'.heap rv ∧
          (∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l) ∧
          (res = .unique → (m_in.isBorrowed = true ∨ m_in = .erased) →
            ∀ l, Reach st'.heap rv l →
              st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨
              StaticStrLoc st l ∨ NumLoc st'.heap l)) := by
  cases n' with
  | zero =>
    have h0 : (applyAllS P ext 0 g [] c).run (st₁, B₁) = .error .outOfFuel := by
      cases B₁ with
      | zero => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
      | succ B₁' => unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; rfl
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n'' =>
    cases B₁ with
    | zero =>
      have h0 : (applyAllS P ext (n'' + 1) g [] c).run (st₁, 0) = .error .outOfFuel := by
        unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ B₁' =>
      have hApp0 : (applyAllS P ext (n'' + 1) g [] c).run (st₁, B₁' + 1) =
          (match (conform c g).run st₁ with
           | .error e => .error e
           | .ok (g1, st₂) => .ok (g1, (st₂, B₁'))) := by
        unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_liftM_run]
        cases (conform c g).run st₁ <;> rfl
      rw [hApp0]
      have hst₁' : StOk P ext B₁' st₁ := StOk_mono (Nat.le_succ _) hst₁
      rcases conform_post_apply (res := res) (fRegs := fRegs) (aRegs := aRegs)
          hst₁' hbaseG (CtorFieldsOk_mono (Nat.le_succ _) hcfG) (fun _ => hnoG)
          (FunOkAt_mono (Nat.le_succ _) hfunG) (fun hcv => by rw [applyResultRegs_eq_of_regions hr₁]; exact hopenG hcv) with hStC |
        ⟨rv, st₂, hcRun, hr₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂,
         hst₂, hbv₂, hcls₂, hdou₂, hcf₂, hreach₂, hno₂, hfun₂, hvalEq₂⟩
      · rw [hStC]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hcRun]; dsimp only
        rcases conform_idem_of_clsSafe hbv₂ hcls₂ with hSt2 | hOk2
        · rw [hSt2]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [hOk2]
          refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
          cases hok
          have hpresAll : PreservesLocs Frame st.heap st₂.heap :=
            hpres₁.trans (hpres₂.mono fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁)
          have hliftNum12 : ∀ l, NumLoc st₁.heap l → NumLoc st₂.heap l := by
            rintro l ⟨o1, n1, ho1, hc1⟩
            have hlt1 : l < st₁.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho1).1
            exact ⟨o1, n1, (hpres₂ l hlt1).trans ho1, hc1⟩
          have hssfAll : StaticStrFresh st st₂ :=
            StaticStrFresh.trans hsz₁ (hpres₂.mono fun _ hl => StOk_staticStrLoc_lt hst₁ hl) hssf₁ hssf₂
          have hreachAll : ∀ l, Reach st₂.heap rv l →
              st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ Reach st.heap a l ∨
              StaticStrLoc st l ∨ NumLoc st₂.heap l := by
            intro l hrl
            rcases hreach₂ l hrl with hge1 | hrg
            · exact Or.inl (Nat.le_trans hsz₁ hge1)
            · rcases hreachG l hrg with h1 | h2 | h3 | h4 | h5
              · exact Or.inl h1
              · exact Or.inr (Or.inl h2)
              · exact Or.inr (Or.inr (Or.inl h3))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (hliftNum12 l h5))))
          refine ⟨by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
            hr₂.trans hr₁, by rw [hnr₂]; exact hnr₁,
            by rw [hstat₂]; exact hstat₁, by rw [hstr₂]; exact hstr₁,
            hpresAll, honce₁.trans honce₂, hssfAll,
            hbv₂, hcls₂, by rw [applyResultRegs_eq_of_regions hr₁] at hdou₂; exact hdou₂, hcf₂, hreachAll,
            ⟨fun _ => ⟨hno₂ rfl, hfun₂⟩,
             fun _ => ⟨fun _ => False, fun _ h => False.elim h, FunOkAt_weaken_onceOnly hfun₂⟩⟩,
            ?_⟩
          rintro ⟨hru, hcv⟩
          obtain ⟨rfl, rfl⟩ := hvalEq₂ hcv
          refine ⟨?_, ?_, hnoArgG⟩
          · by_cases hrc : rc' = .val
            · exact (huniqG ⟨hru, hrc⟩).1
            · exact (ClsSafe_ownTreeFull hrc hclsG).1
          · intro l hor
            by_cases hrc : rc' = .val
            · exact (huniqG ⟨hru, hrc⟩).2 l hor
            · exact False.elim ((ClsSafe_ownTreeFull hrc hclsG).2 l hor)

/-- Helper constructing `FunOkAt` and `resFoot` for the extended PAP `g` allocated in
`pap_iface_under_step`. -/
private theorem pap_iface_under_funG {P : Prog} {ext : ExternOracle} {b b'' : Nat}
    {st₀ st st₁ : St} {loc cap' cap₁ : Nat} {t' : List Nat}
    {r : Ref} {ifc : Iface} {out₀ out out' : Array Val}
    {onceOnly : Bool} {pOnce : Nat → Bool} {pFoot : Nat → Nat → Prop}
    {a g : Val} {Frame : Nat → Prop} {fRegs : List Nat}
    {aOnce : Bool} {aFoot : Nat → Prop} {pk : Param}
    (hkLt : out₀.size < ifc.params.size)
    (hMore : out₀.size + 1 < ifc.params.size)
    (hpkGet : ifc.params[out₀.size]? = some pk)
    (houtSz : out.size = out₀.size)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (haBase : ValBaseOk st a)
    (hFf : ∀ l, Frame l → ¬ (∃ i, i < out₀.size ∧ pFoot i l))
    (hFa : ∀ l, Frame l → ¬ aFoot l)
    (h12 : ∀ l, (∃ i, i < out₀.size ∧ pFoot i l) → ¬ aFoot l)
    (hfa : ∀ l, Reach st.heap (.ref loc cap' t') l → ¬ aFoot l)
    (haf : ∀ l, Reach st.heap a l → ¬ (∃ i, i < out₀.size ∧ pFoot i l))
    (haNum : (∀ l, aFoot l → Reach st.heap a l ∧ ¬ NumLoc st.heap l) ∧
             (pk.mode = .erased → NoOnceCell st.heap a))
    (harg : pk.mode ≠ .erased →
      (pk.mode.usage = .once → FunOkAt P ext (b'' + 1 + 1) st pk.skel aOnce aFoot a) ∧
      (pk.mode.usage ≠ .once →
        NoOnceCell st.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
        FunOkAt P ext (b'' + 1 + 1) st pk.skel false (fun _ => False) a) ∧
      (pk.mode.isUnique = true →
        OwnTreeFull P st.heap a ∧
        (∀ l, OwnReach P st.heap a l → ¬ Frame l ∧ ¬ Reach st.heap (.ref loc cap' t') l) ∧
        (pk.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] a)))
    (hOutAll₀ : ∀ (i : Nat) (w₀ : Val), out₀[i]? = some w₀ →
      ValBaseOk st₀ w₀ ∧ (onceOnly = false → NoOnceCell st₀.heap w₀))
    (hargs₀ : ∀ (i : Nat) (p : Param) (w₀ : Val),
      ifc.params[i]? = some p → out₀[i]? = some w₀ → p.mode ≠ .erased →
      (p.mode.usage = .once →
        FunOkAt P ext (b + 1) st₀ p.skel (pOnce i) (pFoot i) w₀ ∧
        (∀ l, pFoot i l → Reach st₀.heap w₀ l ∧ ¬ StaticStrLoc st₀ l ∧ ¬ NumLoc st₀.heap l) ∧
        (onceOnly = false → ∀ l, ¬ pFoot i l)) ∧
      (p.mode.usage ≠ .once →
        NoOnceCell st₀.heap w₀ ∧ pOnce i = false ∧
        FunOkAt P ext (b + 1) st₀ p.skel false (fun _ => False) w₀ ∧
        (p.mode.isUnique = false → ∀ l, ¬ pFoot i l)) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st₀.heap w₀ ∧
        (p.mode.isBorrowed = false → DeepOpenUnder st₀.heap st₀.regions [] w₀) ∧
        (∀ l, OwnReach P st₀.heap w₀ l → pFoot i l) ∧
        (∀ l, pFoot i l → OwnReach P st₀.heap w₀ l) ∧
        (onceOnly = false → ∀ l, ¬ OwnReach P st₀.heap w₀ l)) ∧
      (∀ l, pFoot i l → Reach st₀.heap w₀ l ∧ ¬ StaticStrLoc st₀ l ∧ ¬ NumLoc st₀.heap l))
    (herFoot₀ : ∀ (i : Nat) (p : Param) (w₀ : Val),
      ifc.params[i]? = some p → out₀[i]? = some w₀ → p.mode = .erased → ∀ l, ¬ pFoot i l)
    (hlifts : ∀ (i : Nat) (w₀ w : Val), out₀[i]? = some w₀ → out[i]? = some w →
      ValSameShape w₀ w ∧ SameLoc w₀ w ∧ SameShapeOn (Reach st₀.heap w₀) st₀.heap st.heap ∧
      ValBaseOk st w ∧ DeepOpenUnder st.heap st.regions fRegs w ∧ CtorFieldsOk P ext (b'' + 1 + 1) st w ∧
      (∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l))
    (hOutAll : ∀ (i : Nat) (w : Val), out[i]? = some w →
      ValBaseOk st w ∧ DeepOpenUnder st.heap st.regions fRegs w ∧
      CtorFieldsOk P ext b'' st w ∧
      (onceOnly = false → NoOnceCell st.heap w) ∧
      (∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l))
    (hOutLift : ∀ (i : Nat) (p : Param) (w : Val),
      ifc.params[i]? = some p → out[i]? = some w → p.mode ≠ .erased →
      (p.mode.usage = .once →
        FunOkAt P ext b'' st p.skel (pOnce i) (pFoot i) w ∧
        (∀ l, pFoot i l → Reach st.heap w l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
      (p.mode.usage ≠ .once →
        NoOnceCell st.heap w ∧ pOnce i = false ∧ (∀ l, ¬ (p.mode.isUnique = false ∧ pFoot i l)) ∧
        FunOkAt P ext b'' st p.skel false (fun _ => False) w) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap w ∧
        (∀ l, OwnReach P st.heap w l → ¬ Frame l ∧ ¬ Reach st.heap a l) ∧
        (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] w) ∧
        (∀ l, OwnReach P st.heap w l → pFoot i l) ∧
        (∀ l, pFoot i l → OwnReach P st.heap w l)))
    (hOutDisj : ∀ (i j : Nat) (pi pj : Param) (wi wj : Val), i ≠ j →
      ifc.params[i]? = some pi → out[i]? = some wi →
      ifc.params[j]? = some pj → out[j]? = some wj →
      (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap wi l → ¬ Reach st.heap wj l) ∧
      (pj.mode ≠ .erased → pi.mode.usage = .once → ∀ l, pFoot i l → ¬ Reach st.heap wj l) ∧
      (pj.mode ≠ .erased → pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, pFoot i l → ¬ pFoot j l))
    (hih_step : ∀ {st₁ : St} {loc₁ cap₁ : Nat} {t₁ : List Nat}
      {out₁ : Array Val} {once₁ : Bool} {pOnce₁ : Nat → Bool} {pFoot₁ : Nat → Nat → Prop},
      out₁.size < ifc.params.size →
      st₁.heap.objs[loc₁]? = some ⟨.pap r out₁, cap₁⟩ →
      (∀ (i : Nat) (w₀ : Val), out₁[i]? = some w₀ →
        ValBaseOk st₁ w₀ ∧ (once₁ = false → NoOnceCell st₁.heap w₀)) →
      (∀ (i : Nat) (p : Param) (w₀ : Val),
        ifc.params[i]? = some p → out₁[i]? = some w₀ → p.mode ≠ .erased →
        (p.mode.usage = .once →
          FunOkAt P ext b'' st₁ p.skel (pOnce₁ i) (pFoot₁ i) w₀ ∧
          (∀ l, pFoot₁ i l → Reach st₁.heap w₀ l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l) ∧
          (once₁ = false → ∀ l, ¬ pFoot₁ i l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st₁.heap w₀ ∧ pOnce₁ i = false ∧
          FunOkAt P ext b'' st₁ p.skel false (fun _ => False) w₀ ∧
          (p.mode.isUnique = false → ∀ l, ¬ pFoot₁ i l)) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st₁.heap w₀ ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st₁.heap st₁.regions [] w₀) ∧
          (∀ l, OwnReach P st₁.heap w₀ l → pFoot₁ i l) ∧
          (∀ l, pFoot₁ i l → OwnReach P st₁.heap w₀ l) ∧
          (once₁ = false → ∀ l, ¬ OwnReach P st₁.heap w₀ l)) ∧
        (∀ l, pFoot₁ i l → Reach st₁.heap w₀ l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l)) →
      (∀ (i : Nat) (p : Param) (w₀ : Val),
        ifc.params[i]? = some p → out₁[i]? = some w₀ → p.mode = .erased → ∀ l, ¬ pFoot₁ i l) →
      (∀ (i j : Nat) (pi pj : Param) (wi wj : Val), i ≠ j →
        ifc.params[i]? = some pi → out₁[i]? = some wi →
        ifc.params[j]? = some pj → out₁[j]? = some wj →
        (pi.mode.isUnique = true → ∀ l, OwnReach P st₁.heap wi l → ¬ Reach st₁.heap wj l) ∧
        (pj.mode ≠ .erased → pi.mode.usage = .once → ∀ l, pFoot₁ i l → ¬ Reach st₁.heap wj l) ∧
        (pj.mode ≠ .erased → pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, pFoot₁ i l → ¬ pFoot₁ j l)) →
      FunOkAt P ext b'' st₁
        (ifaceSkel (ifc.params.toList.drop out₁.size) ifc.res ifc.resSkel)
        once₁ (fun l => ∃ i, i < out₁.size ∧ pFoot₁ i l) (.ref loc₁ cap₁ t₁))
    (hvsBase : ∀ v ∈ out.toList ++ [a], ValBaseOk st v ∧ CtorFieldsOk P ext b'' st v)
    (hvsGet : ∀ (i : Nat) (v : Val), (out.toList ++ [a])[i]? = some v →
      (i < out₀.size ∧ out[i]? = some v) ∨ (i = out₀.size ∧ v = a))
    (hr₁ : st₁.regions = st.regions) (hnr₁ : st₁.nextRegion = st.nextRegion)
    (hoss₁ : OldSameShape st.heap st₁.heap)
    (hssf₁ : StaticStrFresh st st₁)
    (hgEq : g = .ref st.heap.objs.size cap₁ (taints out'.toList))
    (hoNew₁ : st₁.heap.objs[st.heap.objs.size]? = some ⟨.pap r out', cap₁⟩)
    (houtSz' : out'.size = (out.toList ++ [a]).length)
    (houtProps' : ∀ (i : Nat) (v : Val), (out.toList ++ [a])[i]? = some v →
      ∃ w, out'[i]? = some w ∧ ValSameShape v w ∧ ValBaseOk st₁ w ∧
        (NoOnceCell st.heap v → NoOnceCell st₁.heap w) ∧
        CtorFieldsOk P ext b'' st₁ w ∧
        (∀ sk onceOnly Foot, FunOkAt P ext b'' st sk onceOnly Foot v →
          FunOkAt P ext b'' st₁ sk onceOnly Foot w))
    (hnoAllVs : (isArrowSkel (ifaceSkel (ifc.params.toList.drop (out₀.size + 1)) ifc.res ifc.resSkel) &&
        (onceOnly || pk.mode.isUnique || pk.mode.usage == .once)) = false →
      ∀ v ∈ out.toList ++ [a], NoOnceCell st.heap v) :
    let cod := ifaceSkel (ifc.params.toList.drop (out₀.size + 1)) ifc.res ifc.resSkel
    let resOnce := isArrowSkel cod && (onceOnly || pk.mode.isUnique || pk.mode.usage == .once)
    ∃ resFoot,
      (∀ l, resFoot l → Reach st₁.heap g l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l) ∧
      FunOkAt P ext b'' st₁ cod resOnce (if resOnce then resFoot else fun _ => False) g := by
  intro cod resOnce
  let k := out₀.size
  let vs : List Val := out.toList ++ [a]
  have hvsLen : vs.length = k + 1 := by simp [vs, houtSz, k]
  have hdrop2 : ifc.params.toList.drop (k + 1) =
      ifc.params[k + 1] :: ifc.params.toList.drop (k + 2) := by
    have hk1L : k + 1 < ifc.params.toList.length := by simpa using hMore
    simpa using list_drop_eq_cons hk1L
  have hArrCod : isArrowSkel cod = true := by
    dsimp only [cod]; rw [hdrop2]; exact isArrowSkel_ifaceSkel_cons ..
  have hresOnceEq : resOnce = (onceOnly || pk.mode.isUnique || (pk.mode.usage == .once)) := by
    dsimp only [resOnce]; rw [hArrCod, Bool.true_and]
  let pOnce' : Nat → Bool := fun i =>
    if i < out₀.size then pOnce i else if i = out₀.size then aOnce else false
  let pFoot' : Nat → Nat → Prop := fun i l =>
    if i < out₀.size then pFoot i l
    else if i = out₀.size then
      if pk.mode.isUnique then OwnReach P st.heap a l
      else if pk.mode.usage == .once then aFoot l
      else False
    else False
  have hrf01 : RegsFuture st st₁ := RegsFuture.same_regions (hnr₁ ▸ Nat.le_refl _) hr₁
  have hfunG_raw : FunOkAt P ext b'' st₁ cod resOnce (fun l => ∃ i, i < out'.size ∧ pFoot' i l) g := by
    rw [hgEq]
    have hltOut' : out'.size < ifc.params.size := by rw [houtSz', hvsLen]; exact hMore
    have hcodEq : ifaceSkel (ifc.params.toList.drop out'.size) ifc.res ifc.resSkel = cod := by
      rw [houtSz', hvsLen]
    rw [← hcodEq]
    refine hih_step (pOnce₁ := pOnce') (pFoot₁ := pFoot') hltOut' hoNew₁ ?_ ?_ ?_ ?_
    · intro i w' hw'
      have hi : i < vs.length := houtSz' ▸ (Array.getElem?_eq_some_iff.mp hw').1
      obtain ⟨w₁, hw₁, _, hbv₁, hno₁, _, _⟩ := houtProps' i vs[i] (List.getElem?_eq_getElem hi)
      rw [hw'] at hw₁; cases hw₁
      exact ⟨hbv₁, fun hroF => hno₁ (hnoAllVs hroF vs[i] (List.getElem_mem hi))⟩
    · intro i p w' hp hw' hne
      have hi : i < vs.length := houtSz' ▸ (Array.getElem?_eq_some_iff.mp hw').1
      obtain ⟨w₁, hw₁, hvsh₁, hbv₁, hno₁, _, hfun₁⟩ := houtProps' i vs[i] (List.getElem?_eq_getElem hi)
      rw [hw'] at hw₁; cases hw₁
      have hloc₁ : SameLoc vs[i] w' := SameLoc.of_valSameShape hvsh₁
      have hsh₁ : SameShapeOn (Reach st.heap vs[i]) st.heap st₁.heap := hoss₁.to_sameShapeOn _
      have hbvOld : ValBaseOk st vs[i] := (hvsBase vs[i] (List.getElem_mem hi)).1
      rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨hiLt, hwOld⟩ | ⟨rfl, haEq⟩
      · have hpF : pFoot' i = pFoot i := by funext l; simp [pFoot', hiLt]
        have hpO : pOnce' i = pOnce i := by simp [pOnce', hiLt]
        rw [hpF, hpO]
        have hL := hOutLift i p vs[i] hp hwOld hne
        have hi₀ : i < out₀.size := hiLt
        have hftBound : ∀ l, pFoot i l → Reach st₁.heap w' l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l := by
          intro l hfl
          have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
          have hbv₀ := (hOutAll₀ i out₀[i] hw₀).1
          obtain ⟨_, hloc0, hsh0, _⟩ := hlifts i out₀[i] vs[i] hw₀ hwOld
          have ⟨hr₀, _, hnum₀⟩ := (hargs₀ i p out₀[i] hp hw₀ hne).2.2.2 l hfl
          have hrSt := Reach_of_sameShapeOn hsh0 hloc0 hr₀
          have hrSt1 := Reach_of_sameShapeOn hsh₁ hloc₁ hrSt
          have hltSt : l < st.heap.objs.size := Reach_lt_size hbvOld.1 hrSt
          have hnotNumSt : ¬ NumLoc st.heap l := fun h => hnum₀ ((NumLoc_sameShape hsh0 hr₀ (hbv₀.1.reach_lt_size hr₀)).mpr h)
          have hnotNum1 : ¬ NumLoc st₁.heap l := fun h => hnotNumSt ((NumLoc_sameShape hsh₁ hrSt hltSt).mpr h)
          have hnotF : ¬ Frame l := fun hF => hFf l hF ⟨i, hi₀, hfl⟩
          have hnotSS1 : ¬ StaticStrLoc st₁ l := fun hss1 => by
            rcases hssf₁ l hss1 with hge | hss0 | hnum1
            · omega
            · exact hnotF (hstat l hss0)
            · exact hnotNum1 hnum1
          exact ⟨hrSt1, hnotSS1, hnotNum1⟩
        refine ⟨fun hu => ?_, fun hnu => ?_, fun hu => ?_, hftBound⟩
        · obtain ⟨hfOld, _⟩ := hL.1 hu
          refine ⟨hfun₁ p.skel (pOnce i) (pFoot i) hfOld, hftBound, fun hroF l hfl => ?_⟩
          rw [hresOnceEq] at hroF
          simp only [Bool.or_eq_false_iff] at hroF
          have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
          exact ((hargs₀ i p out₀[i] hp hw₀ hne).1 hu).2.2 hroF.1.1 l hfl
        · obtain ⟨hnoOld, hpoOld, hnfOld, hfOld⟩ := hL.2.1 hnu
          exact ⟨hno₁ hnoOld, hpoOld, hfun₁ p.skel false (fun _ => False) hfOld,
            fun hnuq l hfl => hnfOld l ⟨hnuq, hfl⟩⟩
        · obtain ⟨htrOld, _, hnbOld, hownSub, hownRev⟩ := hL.2.2 hu
          have hownEq : ∀ l, OwnReach P st₁.heap w' l ↔ OwnReach P st.heap vs[i] l :=
            fun l => ⟨OwnReach_of_sameShapeOn_rev hbvOld.1 hsh₁ hloc₁, OwnReach_of_sameShapeOn hsh₁ hloc₁⟩
          refine ⟨OwnTreeFull_of_sameShapeOn hbvOld.1 hsh₁ hloc₁ htrOld,
            fun hnb => DeepOpenUnder_of_sameShapeOn hbvOld.1 hsh₁ hvsh₁
              (DeepOpenUnder_of_regsFuture hbvOld.2.2.2 (hnbOld hnb) hrf01),
            fun l hor => hownSub l ((hownEq l).mp hor),
            fun l hfl => (hownEq l).mpr (hownRev l hfl),
            fun hroF l hor => ?_⟩
          rw [hresOnceEq] at hroF
          simp only [Bool.or_eq_false_iff] at hroF
          have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
          have hbv₀ := (hOutAll₀ i out₀[i] hw₀).1
          obtain ⟨_, hloc0, hsh0, _⟩ := hlifts i out₀[i] vs[i] hw₀ hwOld
          exact ((hargs₀ i p out₀[i] hp hw₀ hne).2.2.1 hu).2.2.2.2 hroF.1.1 l
            (OwnReach_of_sameShapeOn_rev hbv₀.1 hsh0 hloc0 ((hownEq l).mp hor))
      · rw [hpkGet] at hp; cases hp
        rw [haEq] at hbvOld hvsh₁ hloc₁ hsh₁ hno₁ hfun₁
        have hnotLt : ¬ (out₀.size < out₀.size) := Nat.lt_irrefl out₀.size
        have hpO : pOnce' out₀.size = aOnce := by simp [pOnce']
        rw [hpO]
        obtain ⟨ho1, ho2, ho3⟩ := harg hne
        have hftBound : ∀ l, pFoot' out₀.size l → Reach st₁.heap w' l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l := by
          intro l hfl
          simp only [pFoot', hnotLt, ↓reduceIte] at hfl
          cases hu : pk.mode.isUnique with
          | true =>
            simp only [hu, ↓reduceIte] at hfl
            have hrA : Reach st.heap a l := OwnReach_toReach hfl
            have hr1 := Reach_of_sameShapeOn hsh₁ hloc₁ hrA
            have hltSt : l < st.heap.objs.size := Reach_lt_size haBase.1 hrA
            have hnotNumA : ¬ NumLoc st.heap l := OwnReach_not_numLoc hfl
            have hnotNum1 : ¬ NumLoc st₁.heap l := fun h => hnotNumA ((NumLoc_sameShape hsh₁ hrA hltSt).mpr h)
            have hnotF : ¬ Frame l := ((ho3 hu).2.1 l hfl).1
            have hnotSS1 : ¬ StaticStrLoc st₁ l := fun hss1 => by
              rcases hssf₁ l hss1 with hge | hss0 | hnum1
              · omega
              · exact hnotF (hstat l hss0)
              · exact hnotNum1 hnum1
            exact ⟨hr1, hnotSS1, hnotNum1⟩
          | false =>
            simp only [hu, Bool.false_eq_true, ↓reduceIte] at hfl
            cases ho : (pk.mode.usage == .once) with
            | false => simp only [ho, Bool.false_eq_true, ↓reduceIte] at hfl
            | true =>
              simp only [ho, ↓reduceIte] at hfl
              have ⟨hrA, hnotNumA⟩ := haNum.1 l hfl
              have hr1 := Reach_of_sameShapeOn hsh₁ hloc₁ hrA
              have hltSt : l < st.heap.objs.size := Reach_lt_size haBase.1 hrA
              have hnotNum1 : ¬ NumLoc st₁.heap l := fun h => hnotNumA ((NumLoc_sameShape hsh₁ hrA hltSt).mpr h)
              have hnotF : ¬ Frame l := fun hF => hFa l hF hfl
              have hnotSS1 : ¬ StaticStrLoc st₁ l := fun hss1 => by
                rcases hssf₁ l hss1 with hge | hss0 | hnum1
                · omega
                · exact hnotF (hstat l hss0)
                · exact hnotNum1 hnum1
              exact ⟨hr1, hnotSS1, hnotNum1⟩
        refine ⟨fun hu => ?_, fun hnu => ?_, fun hu => ?_, hftBound⟩
        · have hnuq : pk.mode.isUnique = false := by
            cases hm : pk.mode <;> simp [hm, BinderMode.usage, BinderMode.isUnique] at hu ⊢
          have hpF : pFoot' out₀.size = aFoot := by
            funext l; simp [pFoot', hnuq, hu]
          rw [hpF]
          refine ⟨hfun₁ pk.skel aOnce aFoot (FunOkAt_mono (by omega) (ho1 hu)),
            by simpa [hpF] using hftBound, fun hroF => ?_⟩
          rw [hresOnceEq, hu] at hroF; simp at hroF
        · obtain ⟨hnoA, haO, haF, hfA⟩ := ho2 hnu
          refine ⟨hno₁ hnoA, haO, hfun₁ pk.skel false (fun _ => False) (FunOkAt_mono (by omega) hfA),
            fun hnuq l hfl => ?_⟩
          have hbeqF : (pk.mode.usage == .once) = false := beq_false_of_ne hnu
          simp [pFoot', hnuq, hbeqF] at hfl
        · have hpF : pFoot' out₀.size = OwnReach P st.heap a := by
            funext l; simp [pFoot', hu]
          rw [hpF]
          obtain ⟨htrA, _, hnbA⟩ := ho3 hu
          have hownEq : ∀ l, OwnReach P st₁.heap w' l ↔ OwnReach P st.heap a l :=
            fun l => ⟨OwnReach_of_sameShapeOn_rev haBase.1 hsh₁ hloc₁, OwnReach_of_sameShapeOn hsh₁ hloc₁⟩
          refine ⟨OwnTreeFull_of_sameShapeOn haBase.1 hsh₁ hloc₁ htrA,
            fun hnb => DeepOpenUnder_of_sameShapeOn haBase.1 hsh₁ hvsh₁
              (DeepOpenUnder_of_regsFuture haBase.2.2.2 (hnbA hnb) hrf01),
            fun l hor => (hownEq l).mp hor,
            fun l hor => (hownEq l).mpr hor,
            fun hroF => by rw [hresOnceEq, hu] at hroF; simp at hroF⟩
    · intro i p w' hp hw' hpe l hfl
      have hi : i < vs.length := houtSz' ▸ (Array.getElem?_eq_some_iff.mp hw').1
      rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨hiLt, _⟩ | ⟨rfl, _⟩
      · simp only [pFoot', hiLt, ↓reduceIte] at hfl
        exact herFoot₀ i p out₀[i] hp (Array.getElem?_eq_getElem hiLt) hpe l hfl
      · rw [hpkGet] at hp; cases hp
        simp [pFoot', hpe, BinderMode.isUnique, BinderMode.usage] at hfl
    · intro i j pi pj wi' wj' hij hpi hwi' hpj hwj'
      have hi : i < vs.length := houtSz' ▸ (Array.getElem?_eq_some_iff.mp hwi').1
      have hj : j < vs.length := houtSz' ▸ (Array.getElem?_eq_some_iff.mp hwj').1
      obtain ⟨wi₁, hwi₁, hvshi, _, _, _, _⟩ := houtProps' i vs[i] (List.getElem?_eq_getElem hi)
      obtain ⟨wj₁, hwj₁, hvshj, _, _, _, _⟩ := houtProps' j vs[j] (List.getElem?_eq_getElem hj)
      rw [hwi'] at hwi₁; cases hwi₁
      rw [hwj'] at hwj₁; cases hwj₁
      have hlocI : SameLoc vs[i] wi' := SameLoc.of_valSameShape hvshi
      have hlocJ : SameLoc vs[j] wj' := SameLoc.of_valSameShape hvshj
      have hshI : SameShapeOn (Reach st.heap vs[i]) st.heap st₁.heap := hoss₁.to_sameShapeOn _
      have hshJ : SameShapeOn (Reach st.heap vs[j]) st.heap st₁.heap := hoss₁.to_sameShapeOn _
      have hbiOld := (hvsBase vs[i] (List.getElem_mem hi)).1
      have hbjOld := (hvsBase vs[j] (List.getElem_mem hj)).1
      have hrjRev : ∀ l, Reach st₁.heap wj' l → Reach st.heap vs[j] l :=
        fun l h => Reach_of_sameShapeOn_rev hbjOld.1 hshJ hlocJ h
      have horiRev : ∀ l, OwnReach P st₁.heap wi' l → OwnReach P st.heap vs[i] l :=
        fun l h => OwnReach_of_sameShapeOn_rev hbiOld.1 hshI hlocI h
      rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨hiLt, hwiOld⟩ | ⟨rfl, haEqI⟩
      · rcases hvsGet j vs[j] (List.getElem?_eq_getElem hj) with ⟨hjLt, hwjOld⟩ | ⟨rfl, haEqJ⟩
        · obtain ⟨hd1, hd2, hd3⟩ := hOutDisj i j pi pj vs[i] vs[j] hij hpi hwiOld hpj hwjOld
          refine ⟨fun hu l hor hrj => hd1 hu l (horiRev l hor) (hrjRev l hrj),
            fun hnej hu l hfl hrj => hd2 hnej hu l (by simpa [pFoot', hiLt] using hfl) (hrjRev l hrj),
            fun hnej hui huj l hfi hfj => hd3 hnej hui huj l (by simpa [pFoot', hiLt] using hfi) (by simpa [pFoot', hjLt] using hfj)⟩
        · rw [hpkGet] at hpj; cases hpj
          have hnei_fn : pi.mode.isUnique = true → pi.mode ≠ .erased := fun hu h => by rw [h] at hu; cases hu
          refine ⟨fun hu l hor hrj => ((hOutLift i pi vs[i] hpi hwiOld (hnei_fn hu)).2.2 hu).2.1 l (horiRev l hor) |>.2 (haEqJ ▸ hrjRev l hrj),
            fun _ _ l hfl hrj => haf l (haEqJ ▸ hrjRev l hrj) ⟨i, hiLt, by simpa [pFoot', hiLt] using hfl⟩,
            fun _ _ huj l hfi hfj => ?_⟩
          have hnuqK : pk.mode.isUnique = false := by
            cases hm : pk.mode <;> simp [hm, BinderMode.usage, BinderMode.isUnique] at huj ⊢
          have hfj' : aFoot l := by simpa [pFoot', hnuqK, huj] using hfj
          exact h12 l ⟨i, hiLt, by simpa [pFoot', hiLt] using hfi⟩ hfj'
      · rw [hpkGet] at hpi; cases hpi
        rcases hvsGet j vs[j] (List.getElem?_eq_getElem hj) with ⟨hjLt, hwjOld⟩ | ⟨heq, _⟩
        · refine ⟨fun hu l hor hrj => ?_, fun _ hu l hfl hrj => ?_, fun _ hui _ l hfi hfj => ?_⟩
          · have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
            exact ((harg hne).2.2 hu).2.1 l (haEqI ▸ horiRev l hor) |>.2 ((hOutAll j vs[j] hwjOld).2.2.2.2 l (hrjRev l hrj))
          · have hnuqK : pk.mode.isUnique = false := by
              cases hm : pk.mode <;> simp [hm, BinderMode.usage, BinderMode.isUnique] at hu ⊢
            have hfl' : aFoot l := by simpa [pFoot', hnuqK, hu] using hfl
            exact hfa l ((hOutAll j vs[j] hwjOld).2.2.2.2 l (hrjRev l hrj)) hfl'
          · have hnuqK : pk.mode.isUnique = false := by
              cases hm : pk.mode <;> simp [hm, BinderMode.usage, BinderMode.isUnique] at hui ⊢
            have hfi' : aFoot l := by simpa [pFoot', hnuqK, hui] using hfi
            exact h12 l ⟨j, hjLt, by simpa [pFoot', hjLt] using hfj⟩ hfi'
        · exact absurd heq.symm hij
  let resFoot : Nat → Prop := fun l => ∃ i, i < out'.size ∧ pFoot' i l
  have hresFootFalse : resOnce = false → resFoot = fun _ => False := by
    intro hroF
    funext l; apply propext; constructor
    · rintro ⟨i, hi, hfl⟩
      rw [houtSz', hvsLen] at hi
      rw [hresOnceEq] at hroF
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hroF
      obtain ⟨⟨hooF, hnuqK⟩, hnuK⟩ := hroF
      by_cases hilt : i < out₀.size
      · simp only [pFoot', hilt, ↓reduceIte] at hfl
        have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem (Nat.lt_trans hilt hkLt)
        have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hilt
        by_cases hpe : ifc.params[i].mode = .erased
        · exact herFoot₀ i ifc.params[i] out₀[i] hp hw₀ hpe l hfl
        · have hA := hargs₀ i ifc.params[i] out₀[i] hp hw₀ hpe
          by_cases hu : ifc.params[i].mode.usage = .once
          · exact (hA.1 hu).2.2 hooF l hfl
          · by_cases huq : ifc.params[i].mode.isUnique = true
            · exact (hA.2.2.1 huq).2.2.2.2 hooF l ((hA.2.2.1 huq).2.2.2.1 l hfl)
            · exact (hA.2.1 hu).2.2.2 (Bool.eq_false_iff.mpr huq) l hfl
      · have heq : i = out₀.size := by omega
        subst heq
        have hbeqF : (pk.mode.usage == .once) = false := beq_false_of_ne hnuK
        simp [pFoot', hnuqK, hbeqF] at hfl
    · intro h; exact False.elim h
  have hresFootBound : ∀ l, resFoot l →
      Reach st₁.heap g l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l := by
    rintro l ⟨i, hi, hfl⟩
    have hiV : i < vs.length := houtSz' ▸ hi
    obtain ⟨w', hw', hvsh', _, _, _, _⟩ := houtProps' i vs[i] (List.getElem?_eq_getElem hiV)
    have hwMem : w' ∈ (Cell.pap r out').vals := by
      simpa [Cell.vals] using Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw')
    have hloc' : SameLoc vs[i] w' := SameLoc.of_valSameShape hvsh'
    have hsh' : SameShapeOn (Reach st.heap vs[i]) st.heap st₁.heap := hoss₁.to_sameShapeOn _
    have hbvOld := (hvsBase vs[i] (List.getElem_mem hiV)).1
    have hToG : Reach st.heap vs[i] l → ¬ Frame l → ¬ NumLoc st.heap l →
        Reach st₁.heap g l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l := by
      intro hrOld hnotF hnotNum
      have hr1 := Reach_of_sameShapeOn hsh' hloc' hrOld
      have hrG : Reach st₁.heap g l := by rw [hgEq]; exact .step hoNew₁ hwMem hr1
      have hltSt : l < st.heap.objs.size := Reach_lt_size hbvOld.1 hrOld
      have hnotNum1 : ¬ NumLoc st₁.heap l := fun h => hnotNum ((NumLoc_sameShape hsh' hrOld hltSt).mpr h)
      have hnotSS1 : ¬ StaticStrLoc st₁ l := fun hss1 => by
        rcases hssf₁ l hss1 with hge | hss0 | hnum1
        · omega
        · exact hnotF (hstat l hss0)
        · exact hnotNum1 hnum1
      exact ⟨hrG, hnotF, hnotSS1, hnotNum1⟩
    rcases hvsGet i vs[i] (List.getElem?_eq_getElem hiV) with ⟨hiLt, hwOld⟩ | ⟨rfl, haEq⟩
    · simp only [pFoot', hiLt, ↓reduceIte] at hfl
      have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem (Nat.lt_trans hiLt hkLt)
      have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hiLt
      by_cases hpe : ifc.params[i].mode = .erased
      · exact False.elim (herFoot₀ i ifc.params[i] out₀[i] hp hw₀ hpe l hfl)
      · have hbv₀ := (hOutAll₀ i out₀[i] hw₀).1
        obtain ⟨_, hloc0, hsh0, _⟩ := hlifts i out₀[i] vs[i] hw₀ hwOld
        have ⟨hr₀, _, hnum₀⟩ := (hargs₀ i ifc.params[i] out₀[i] hp hw₀ hpe).2.2.2 l hfl
        exact hToG (Reach_of_sameShapeOn hsh0 hloc0 hr₀)
          (fun hF => hFf l hF ⟨i, hiLt, hfl⟩)
          (fun h => hnum₀ ((NumLoc_sameShape hsh0 hr₀ (hbv₀.1.reach_lt_size hr₀)).mpr h))
    · rw [haEq] at hToG
      simp only [pFoot', Nat.lt_irrefl out₀.size, ↓reduceIte] at hfl
      cases hu : pk.mode.isUnique with
      | true =>
        simp only [hu, ↓reduceIte] at hfl
        have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
        exact hToG (OwnReach_toReach hfl) (((harg hne).2.2 hu).2.1 l hfl).1 (OwnReach_not_numLoc hfl)
      | false =>
        simp only [hu, Bool.false_eq_true, ↓reduceIte] at hfl
        cases ho : (pk.mode.usage == .once) with
        | false => simp only [ho, Bool.false_eq_true, ↓reduceIte] at hfl
        | true =>
          simp only [ho, ↓reduceIte] at hfl
          exact hToG (haNum.1 l hfl).1 (fun hF => hFa l hF hfl) (haNum.1 l hfl).2
  refine ⟨resFoot, hresFootBound, ?_⟩
  cases hro : resOnce with
  | true => simpa [hro] using hfunG_raw
  | false =>
    have hrfEq := hresFootFalse hro
    simpa [hro, resFoot, hrfEq] using hfunG_raw

/-- Helper for Subcase 1 of `pap_iface_funOk` (still under-applied PAP step via `makePap` + `conform`). -/
private theorem pap_iface_under_step {P : Prog} {ext : ExternOracle} {b b'' n' : Nat}
    {st₀ st : St} {loc cap' : Nat} {t' : List Nat}
    {r : Ref} {ifc : Iface} {out₀ out : Array Val}
    {onceOnly : Bool} {pOnce : Nat → Bool} {pFoot : Nat → Nat → Prop}
    {a : Val} {c : Cls} {Frame : Nat → Prop} {fRegs aRegs : List Nat}
    {aOnce : Bool} {aFoot : Nat → Prop} {pk : Param}
    (hkLt : out₀.size < ifc.params.size)
    (hMore : out₀.size + 1 < ifc.params.size)
    (hpkGet : ifc.params[out₀.size]? = some pk)
    (houtSz : out.size = out₀.size)
    (hst : StOk P ext (b'' + 1 + 1) st)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (haBase : ValBaseOk st a)
    (haOpen : DeepOpenUnder st.heap st.regions aRegs a)
    (haCf : CtorFieldsOk P ext (b'' + 1 + 1) st a)
    (hFf : ∀ l, Frame l → ¬ (∃ i, i < out₀.size ∧ pFoot i l))
    (hFa : ∀ l, Frame l → ¬ aFoot l)
    (h12 : ∀ l, (∃ i, i < out₀.size ∧ pFoot i l) → ¬ aFoot l)
    (hfa : ∀ l, Reach st.heap (.ref loc cap' t') l → ¬ aFoot l)
    (haf : ∀ l, Reach st.heap a l → ¬ (∃ i, i < out₀.size ∧ pFoot i l))
    (haNum : (∀ l, aFoot l → Reach st.heap a l ∧ ¬ NumLoc st.heap l) ∧
             (pk.mode = .erased → NoOnceCell st.heap a))
    (harg : pk.mode ≠ .erased →
      (pk.mode.usage = .once → FunOkAt P ext (b'' + 1 + 1) st pk.skel aOnce aFoot a) ∧
      (pk.mode.usage ≠ .once →
        NoOnceCell st.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
        FunOkAt P ext (b'' + 1 + 1) st pk.skel false (fun _ => False) a) ∧
      (pk.mode.isUnique = true →
        OwnTreeFull P st.heap a ∧
        (∀ l, OwnReach P st.heap a l → ¬ Frame l ∧ ¬ Reach st.heap (.ref loc cap' t') l) ∧
        (pk.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] a)))
    (hOutAll₀ : ∀ (i : Nat) (w₀ : Val), out₀[i]? = some w₀ →
      ValBaseOk st₀ w₀ ∧ (onceOnly = false → NoOnceCell st₀.heap w₀))
    (hargs₀ : ∀ (i : Nat) (p : Param) (w₀ : Val),
      ifc.params[i]? = some p → out₀[i]? = some w₀ → p.mode ≠ .erased →
      (p.mode.usage = .once →
        FunOkAt P ext (b + 1) st₀ p.skel (pOnce i) (pFoot i) w₀ ∧
        (∀ l, pFoot i l → Reach st₀.heap w₀ l ∧ ¬ StaticStrLoc st₀ l ∧ ¬ NumLoc st₀.heap l) ∧
        (onceOnly = false → ∀ l, ¬ pFoot i l)) ∧
      (p.mode.usage ≠ .once →
        NoOnceCell st₀.heap w₀ ∧ pOnce i = false ∧
        FunOkAt P ext (b + 1) st₀ p.skel false (fun _ => False) w₀ ∧
        (p.mode.isUnique = false → ∀ l, ¬ pFoot i l)) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st₀.heap w₀ ∧
        (p.mode.isBorrowed = false → DeepOpenUnder st₀.heap st₀.regions [] w₀) ∧
        (∀ l, OwnReach P st₀.heap w₀ l → pFoot i l) ∧
        (∀ l, pFoot i l → OwnReach P st₀.heap w₀ l) ∧
        (onceOnly = false → ∀ l, ¬ OwnReach P st₀.heap w₀ l)) ∧
      (∀ l, pFoot i l → Reach st₀.heap w₀ l ∧ ¬ StaticStrLoc st₀ l ∧ ¬ NumLoc st₀.heap l))
    (herFoot₀ : ∀ (i : Nat) (p : Param) (w₀ : Val),
      ifc.params[i]? = some p → out₀[i]? = some w₀ → p.mode = .erased → ∀ l, ¬ pFoot i l)
    (hlifts : ∀ (i : Nat) (w₀ w : Val), out₀[i]? = some w₀ → out[i]? = some w →
      ValSameShape w₀ w ∧ SameLoc w₀ w ∧ SameShapeOn (Reach st₀.heap w₀) st₀.heap st.heap ∧
      ValBaseOk st w ∧ DeepOpenUnder st.heap st.regions fRegs w ∧ CtorFieldsOk P ext (b'' + 1 + 1) st w ∧
      (∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l))
    (hOutAll : ∀ (i : Nat) (w : Val), out[i]? = some w →
      ValBaseOk st w ∧ DeepOpenUnder st.heap st.regions fRegs w ∧
      CtorFieldsOk P ext b'' st w ∧
      (onceOnly = false → NoOnceCell st.heap w) ∧
      (∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l))
    (hOutLift : ∀ (i : Nat) (p : Param) (w : Val),
      ifc.params[i]? = some p → out[i]? = some w → p.mode ≠ .erased →
      (p.mode.usage = .once →
        FunOkAt P ext b'' st p.skel (pOnce i) (pFoot i) w ∧
        (∀ l, pFoot i l → Reach st.heap w l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
      (p.mode.usage ≠ .once →
        NoOnceCell st.heap w ∧ pOnce i = false ∧ (∀ l, ¬ (p.mode.isUnique = false ∧ pFoot i l)) ∧
        FunOkAt P ext b'' st p.skel false (fun _ => False) w) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap w ∧
        (∀ l, OwnReach P st.heap w l → ¬ Frame l ∧ ¬ Reach st.heap a l) ∧
        (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] w) ∧
        (∀ l, OwnReach P st.heap w l → pFoot i l) ∧
        (∀ l, pFoot i l → OwnReach P st.heap w l)))
    (hOutDisj : ∀ (i j : Nat) (pi pj : Param) (wi wj : Val), i ≠ j →
      ifc.params[i]? = some pi → out[i]? = some wi →
      ifc.params[j]? = some pj → out[j]? = some wj →
      (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap wi l → ¬ Reach st.heap wj l) ∧
      (pj.mode ≠ .erased → pi.mode.usage = .once → ∀ l, pFoot i l → ¬ Reach st.heap wj l) ∧
      (pj.mode ≠ .erased → pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, pFoot i l → ¬ pFoot j l))
    (hih_step : ∀ {st₁ : St} {loc₁ cap₁ : Nat} {t₁ : List Nat}
      {out₁ : Array Val} {once₁ : Bool} {pOnce₁ : Nat → Bool} {pFoot₁ : Nat → Nat → Prop},
      out₁.size < ifc.params.size →
      st₁.heap.objs[loc₁]? = some ⟨.pap r out₁, cap₁⟩ →
      (∀ (i : Nat) (w₀ : Val), out₁[i]? = some w₀ →
        ValBaseOk st₁ w₀ ∧ (once₁ = false → NoOnceCell st₁.heap w₀)) →
      (∀ (i : Nat) (p : Param) (w₀ : Val),
        ifc.params[i]? = some p → out₁[i]? = some w₀ → p.mode ≠ .erased →
        (p.mode.usage = .once →
          FunOkAt P ext b'' st₁ p.skel (pOnce₁ i) (pFoot₁ i) w₀ ∧
          (∀ l, pFoot₁ i l → Reach st₁.heap w₀ l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l) ∧
          (once₁ = false → ∀ l, ¬ pFoot₁ i l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st₁.heap w₀ ∧ pOnce₁ i = false ∧
          FunOkAt P ext b'' st₁ p.skel false (fun _ => False) w₀ ∧
          (p.mode.isUnique = false → ∀ l, ¬ pFoot₁ i l)) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st₁.heap w₀ ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st₁.heap st₁.regions [] w₀) ∧
          (∀ l, OwnReach P st₁.heap w₀ l → pFoot₁ i l) ∧
          (∀ l, pFoot₁ i l → OwnReach P st₁.heap w₀ l) ∧
          (once₁ = false → ∀ l, ¬ OwnReach P st₁.heap w₀ l)) ∧
        (∀ l, pFoot₁ i l → Reach st₁.heap w₀ l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l)) →
      (∀ (i : Nat) (p : Param) (w₀ : Val),
        ifc.params[i]? = some p → out₁[i]? = some w₀ → p.mode = .erased → ∀ l, ¬ pFoot₁ i l) →
      (∀ (i j : Nat) (pi pj : Param) (wi wj : Val), i ≠ j →
        ifc.params[i]? = some pi → out₁[i]? = some wi →
        ifc.params[j]? = some pj → out₁[j]? = some wj →
        (pi.mode.isUnique = true → ∀ l, OwnReach P st₁.heap wi l → ¬ Reach st₁.heap wj l) ∧
        (pj.mode ≠ .erased → pi.mode.usage = .once → ∀ l, pFoot₁ i l → ¬ Reach st₁.heap wj l) ∧
        (pj.mode ≠ .erased → pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, pFoot₁ i l → ¬ pFoot₁ j l)) →
      FunOkAt P ext b'' st₁
        (ifaceSkel (ifc.params.toList.drop out₁.size) ifc.res ifc.resSkel)
        once₁ (fun l => ∃ i, i < out₁.size ∧ pFoot₁ i l) (.ref loc₁ cap₁ t₁)) :
    let cod := ifaceSkel (ifc.params.toList.drop (out₀.size + 1)) ifc.res ifc.resSkel
    let vs : List Val := out.toList ++ [a]
    let runRes : Except Stop (Val × St × Nat) :=
      match (makePap P n' r ifc.params vs).run st with
      | .error e => .error e
      | .ok (g, st₁) =>
        match (conform c g).run st₁ with
        | .error e => .error e
        | .ok (rv, st₂) => .ok (rv, (st₂, b''))
    (∀ k, runRes ≠ .error (.violation k)) ∧
    (∀ rv st' B', runRes = .ok (rv, (st', B')) →
      ∃ (_ : B' ≤ b'' + 1 + 1),
      StOk P ext B' st' ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
      ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
      PreservesLocs Frame st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
      ValBaseOk st' rv ∧ ClsSafe st'.heap c rv ∧
      DeepOpenUnder st'.heap st'.regions (applyResultRegs st .shared c fRegs aRegs) rv ∧
      CtorFieldsOk P ext B' st' rv ∧
      (∀ l, Reach st'.heap rv l →
        st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l ∨
        StaticStrLoc st l ∨ NumLoc st'.heap l) ∧
      (let resOnce := isArrowSkel cod && (onceOnly || pk.mode.isUnique || pk.mode.usage == .once)
       (resOnce = false → NoOnceCell st'.heap rv ∧ FunOkAt P ext B' st' cod false (fun _ => False) rv) ∧
       (resOnce = true → ∃ Foot',
         (∀ l, Foot' l → Reach st'.heap rv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l) ∧
         FunOkAt P ext B' st' cod true Foot' rv)) ∧
      ((ResultMode.shared.isUnique = true ∧ c = .val) →
        OwnTreeFull P st'.heap rv ∧
        (∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l) ∧
        (ResultMode.shared = .unique → (pk.mode.isBorrowed = true ∨ pk.mode = .erased) →
          ∀ l, Reach st'.heap rv l →
            st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨
            StaticStrLoc st l ∨ NumLoc st'.heap l))) := by
  intro cod vs runRes
  let k := out₀.size
  have hvsLen : vs.length = k + 1 := by simp [vs, houtSz, k]
  have hvsGet : ∀ (i : Nat) (v : Val), vs[i]? = some v →
      (i < k ∧ out[i]? = some v) ∨ (i = k ∧ v = a) := by
    intro i v hv
    by_cases hilt : i < out.size
    · have hltL : i < out.toList.length := by simpa using hilt
      rw [List.getElem?_append_left hltL] at hv
      have hszK : out.size = k := houtSz
      left; refine ⟨by omega, ?_⟩
      simpa [Array.getElem?_toList] using hv
    · have hgeL : out.toList.length ≤ i := by simpa using Nat.le_of_not_lt hilt
      rw [List.getElem?_append_right hgeL] at hv
      cases hd : i - out.toList.length with
      | zero =>
        rw [hd] at hv; simp at hv
        right; exact ⟨by have hszK : out.size = k := houtSz; simp only [Array.length_toList] at hgeL hd; omega, hv.symm⟩
      | succ m =>
        rw [hd] at hv; simp at hv
  have hdrop2 : ifc.params.toList.drop (k + 1) =
      ifc.params[k + 1] :: ifc.params.toList.drop (k + 2) := by
    have hk1L : k + 1 < ifc.params.toList.length := by simpa using hMore
    simpa using list_drop_eq_cons hk1L
  have hst'' : StOk P ext b'' st := StOk_mono (by omega) hst
  have hvsBase : ∀ v ∈ vs, ValBaseOk st v ∧ CtorFieldsOk P ext b'' st v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨_, hw⟩ | ⟨_, hveq⟩
    · have h1 := hOutAll i vs[i] hw; exact ⟨h1.1, h1.2.2.1⟩
    · rw [hveq]; exact ⟨haBase, CtorFieldsOk_mono (by omega) haCf⟩
  have hvsUniq : ∀ (i : Nat) (v : Val), vs[i]? = some v →
      ((ifc.params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      NoOnceCell st.heap v ∧ OwnTreeFull P st.heap v ∧
      (((ifc.params[i]?.map Param.mode).getD BinderMode.many).isBorrowed = false →
        OpenUnder st.regions [] v) ∧
      ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l := by
    intro i v hv hu
    rcases hvsGet i v hv with ⟨hilt, hw⟩ | ⟨rfl, rfl⟩
    · have hp : ifc.params[i]? = some ifc.params[i] :=
        Array.getElem?_eq_getElem (Nat.lt_trans hilt hkLt)
      rw [hp] at hu ⊢; simp only [Option.map_some, Option.getD_some] at hu ⊢
      have hne : ifc.params[i].mode ≠ .erased := by intro h; rw [h] at hu; cases hu
      have hnu : ifc.params[i].mode.usage ≠ .once := by
        cases hm : ifc.params[i].mode <;> simp [hm, BinderMode.isUnique, BinderMode.usage] at hu ⊢
      have hL := hOutLift i ifc.params[i] v hp hw hne
      obtain ⟨hno, _, _, _⟩ := hL.2.1 hnu
      obtain ⟨htr, hdisjA, hnb, _, _⟩ := hL.2.2 hu
      exact ⟨hno, htr, fun hb => (hnb hb).self, fun l hor hss => (hdisjA l hor).1 (hstat l hss)⟩
    · rw [hpkGet] at hu ⊢; simp only [Option.map_some, Option.getD_some] at hu ⊢
      have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
      have hnu : pk.mode.usage ≠ .once := by
        cases hm : pk.mode <;> simp [hm, BinderMode.isUnique, BinderMode.usage] at hu ⊢
      obtain ⟨_, ho2, ho3⟩ := harg hne
      obtain ⟨hno, _, _, _⟩ := ho2 hnu
      obtain ⟨htr, hdisjF, hnb⟩ := ho3 hu
      exact ⟨hno, htr, fun hb => (hnb hb).self, fun l hor hss => (hdisjF l hor).1 (hstat l hss)⟩
  have hvsDisj : ∀ (i j : Nat) (vi vj : Val), i ≠ j →
      vs[i]? = some vi → vs[j]? = some vj →
      ((ifc.params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l := by
    intro i j vi vj hij hvi hvj hu l hor hrj
    rcases hvsGet i vi hvi with ⟨hiLt, hwi⟩ | ⟨rfl, rfl⟩
    · have hpi : ifc.params[i]? = some ifc.params[i] :=
        Array.getElem?_eq_getElem (Nat.lt_trans hiLt hkLt)
      rw [hpi] at hu; simp only [Option.map_some, Option.getD_some] at hu
      have hnei : ifc.params[i].mode ≠ .erased := by intro h; rw [h] at hu; cases hu
      rcases hvsGet j vj hvj with ⟨hjLt, hwj⟩ | ⟨rfl, rfl⟩
      · have hpj : ifc.params[j]? = some ifc.params[j] :=
          Array.getElem?_eq_getElem (Nat.lt_trans hjLt hkLt)
        exact (hOutDisj i j ifc.params[i] ifc.params[j] vi vj hij hpi hwi hpj hwj).1 hu l hor hrj
      · exact ((hOutLift i ifc.params[i] vi hpi hwi hnei).2.2 hu).2.1 l hor |>.2 hrj
    · rw [hpkGet] at hu; simp only [Option.map_some, Option.getD_some] at hu
      have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
      rcases hvsGet j vj hvj with ⟨hjLt, hwj⟩ | ⟨heq, _⟩
      · exact ((harg hne).2.2 hu).2.1 l hor |>.2 ((hOutAll j vj hwj).2.2.2.2 l hrj)
      · exact absurd heq.symm hij
  dsimp only [runRes]
  rcases makePap_sound_once (P := P) (ext := ext) (B := b'') (fuel := n')
      (r := r) (params := ifc.params) (vs := vs) hst'' hvsBase hvsUniq hvsDisj with hOOF |
    ⟨g, out', st₁, hmpRun, hr₁, hnr₁, hstat₁, hstr₁, hsz₁, hcap₁, hoss₁, hpres₁,
     honce₁, hssf₁, hst₁, ⟨cap₁, hgEq, hoNew₁⟩, houtSz', houtProps', hbaseG,
     hnoG, hcfG, hdouG, hreachG⟩
  · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  · rw [hmpRun]; dsimp only
    have hpresFrame1 : PreservesLocs Frame st.heap st₁.heap := by
      intro l hFl
      refine hpres₁ l ⟨hFlt l hFl, fun i v hv hu hor => ?_⟩
      rcases hvsGet i v hv with ⟨hiLt, hw⟩ | ⟨rfl, rfl⟩
      · have hp : ifc.params[i]? = some ifc.params[i] :=
          Array.getElem?_eq_getElem (Nat.lt_trans hiLt hkLt)
        rw [hp] at hu; simp only [Option.map_some, Option.getD_some] at hu
        have hne : ifc.params[i].mode ≠ .erased := by intro h; rw [h] at hu; cases hu
        exact ((hOutLift i ifc.params[i] v hp hw hne).2.2 hu).2.1 l hor |>.1 hFl
      · rw [hpkGet] at hu; simp only [Option.map_some, Option.getD_some] at hu
        have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
        exact ((harg hne).2.2 hu).2.1 l hor |>.1 hFl
    have hdouGRes : DeepOpenUnder st₁.heap st₁.regions (applyResultRegs st .shared .val fRegs aRegs) g := by
      rw [hr₁]
      refine hdouG st.regions (applyResultRegs st .shared .val fRegs aRegs) fun v hv => ?_
      have hsubF : ∀ x ∈ fRegs, x ∈ applyResultRegs st .shared .val fRegs aRegs := fun x hx => by
        simp only [applyResultRegs, show (Cls.val != Cls.val) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, List.mem_append]; exact Or.inr hx
      have hsubA : ∀ x ∈ aRegs, x ∈ applyResultRegs st .shared .val fRegs aRegs := fun x hx => by
        simp only [applyResultRegs, show (Cls.val != Cls.val) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, List.mem_append]; exact Or.inl hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨_, hw⟩ | ⟨_, hveq⟩
      · exact (hOutAll i vs[i] hw).2.1.mono hsubF
      · rw [hveq]; exact haOpen.mono hsubA
    let resOnce : Bool := isArrowSkel cod && (onceOnly || pk.mode.isUnique || pk.mode.usage == .once)
    have hArrCod : isArrowSkel cod = true := by
      dsimp only [cod]; rw [hdrop2]; exact isArrowSkel_ifaceSkel_cons ..
    have hresOnceEq : resOnce = (onceOnly || pk.mode.isUnique || (pk.mode.usage == .once)) := by
      dsimp only [resOnce]; rw [hArrCod, Bool.true_and]
    have hnoAllVs : resOnce = false → ∀ v ∈ vs, NoOnceCell st.heap v := by
      intro hrfV v hv
      rw [hresOnceEq] at hrfV
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hrfV
      obtain ⟨⟨hooF, _⟩, hnuK⟩ := hrfV
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨_, hw⟩ | ⟨_, hveq⟩
      · exact (hOutAll i vs[i] hw).2.2.2.1 hooF
      · rw [hveq]
        by_cases hpe : pk.mode = .erased
        · exact haNum.2 hpe
        · exact ((harg hpe).2.1 hnuK).1
    obtain ⟨resFoot, hresFootBound, hfunG_res⟩ :=
      pap_iface_under_funG hkLt hMore hpkGet houtSz hstat haBase hFf hFa h12 hfa haf haNum harg
        hOutAll₀ hargs₀ herFoot₀ hlifts hOutAll hOutLift hOutDisj hih_step
        hvsBase hvsGet hr₁ hnr₁ hoss₁ hssf₁ hgEq hoNew₁ houtSz' houtProps' hnoAllVs
    rcases conform_post_apply (res := .shared) (fRegs := fRegs) (aRegs := aRegs)
        hst₁ hbaseG hcfG (fun h => hnoG (hnoAllVs h)) hfunG_res
        (fun _ => hdouGRes) with hStC |
      ⟨rv, st₂, hcRun, hr₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂,
       hst₂, hbv₂, hcls₂, hdou₂, hcf₂, hreach₂, hno₂, hfun₂, hvalEq₂⟩
    · rw [hStC]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · rw [hcRun]
      refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
      cases hok
      have hpresAll : PreservesLocs Frame st.heap st₂.heap :=
        hpresFrame1.trans (hpres₂.mono fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) (by omega))
      have hssfAll : StaticStrFresh st st₂ :=
        StaticStrFresh.trans (by omega) (hpres₂.mono fun _ hl => StOk_staticStrLoc_lt hst₁ hl) hssf₁ hssf₂
      have hreachAll : ∀ l, Reach st₂.heap rv l →
          st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l ∨
          StaticStrLoc st l ∨ NumLoc st₂.heap l := by
        intro l hrl
        rcases hreach₂ l hrl with hge1 | hrg
        · exact Or.inl (by omega)
        · rcases hreachG l hrg with rfl | ⟨v, hv, hrv⟩
          · exact Or.inl (Nat.le_refl _)
          · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
            rcases hvsGet i vs[i] (List.getElem?_eq_getElem hi) with ⟨_, hw⟩ | ⟨_, hveq⟩
            · exact Or.inr (Or.inl ((hOutAll i vs[i] hw).2.2.2.2 l hrv))
            · exact Or.inr (Or.inr (Or.inl (hveq ▸ hrv)))
      refine ⟨by omega, hst₂, by omega, Nat.le_trans hcap₁ hcap₂,
        hr₂.trans hr₁, by rw [hnr₂, hnr₁]; exact Nat.le_refl _,
        by rw [hstat₂, hstat₁]; exact ArrayExtends.refl _,
        by rw [hstr₂, hstr₁]; exact ArrayExtends.refl _,
        hpresAll, honce₁.trans honce₂, hssfAll,
        hbv₂, hcls₂, by rw [applyResultRegs_eq_of_regions hr₁] at hdou₂; exact hdou₂, hcf₂, hreachAll, ?_,
        fun ⟨h, _⟩ => by cases h⟩
      constructor
      · intro hroF
        have hroF' : resOnce = false := hroF
        refine ⟨hno₂ hroF', ?_⟩
        change FunOkAt P ext b'' st₂ cod resOnce (if resOnce = true then resFoot else fun _ => False) rv at hfun₂
        rw [hroF'] at hfun₂; simpa using hfun₂
      · intro hroT
        have hroT' : resOnce = true := hroT
        by_cases hcv : c = .val
        · obtain ⟨rfl, rfl⟩ := hvalEq₂ hcv
          refine ⟨resFoot, hresFootBound, ?_⟩
          change FunOkAt P ext b'' st₂ cod resOnce (if resOnce = true then resFoot else fun _ => False) rv at hfun₂
          rw [hroT'] at hfun₂; simpa using hfun₂
        · refine ⟨fun _ => False, fun _ h => False.elim h,
            FunOkAt_weaken_onceOnly (ClsSafe_funOkAt P ext b'' st₂ cod hcv hcls₂)⟩

/-- General `FunOkAt` for a runtime `.pap r out` cell whose constant `r` has an interface
(`RunDef.body`, `RunDef.extern`, or `RunDef.stuck`) with `out.size < ifc.params.size`.
Proved by strong induction on `B_call ≤ B + 1` given `FullIH P ext B`. -/
theorem pap_iface_funOk {P : Prog} {ext : ExternOracle} {B : Nat}
    (hext : ExternOk P ext) (hih : FullIH P ext B) :
    ∀ {B_call : Nat} {st₀ : St} {loc cap : Nat} {t₀ : List Nat}
      {r : Ref} {d : RunDef} {ifc : Iface} {out₀ : Array Val}
      {onceOnly : Bool} {pOnce : Nat → Bool} {pFoot : Nat → Nat → Prop},
      B_call ≤ B + 1 →
      P.find? r = some d →
      ifaceOf? d = some ifc →
      out₀.size < ifc.params.size →
      st₀.heap.objs[loc]? = some ⟨.pap r out₀, cap⟩ →
      (∀ (i : Nat) (w₀ : Val), out₀[i]? = some w₀ →
        ValBaseOk st₀ w₀ ∧ (onceOnly = false → NoOnceCell st₀.heap w₀)) →
      (∀ (i : Nat) (p : Param) (w₀ : Val),
        ifc.params[i]? = some p → out₀[i]? = some w₀ → p.mode ≠ .erased →
        (p.mode.usage = .once →
          FunOkAt P ext B_call st₀ p.skel (pOnce i) (pFoot i) w₀ ∧
          (∀ l, pFoot i l → Reach st₀.heap w₀ l ∧ ¬ StaticStrLoc st₀ l ∧ ¬ NumLoc st₀.heap l) ∧
          (onceOnly = false → ∀ l, ¬ pFoot i l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st₀.heap w₀ ∧ pOnce i = false ∧
          FunOkAt P ext B_call st₀ p.skel false (fun _ => False) w₀ ∧
          (p.mode.isUnique = false → ∀ l, ¬ pFoot i l)) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st₀.heap w₀ ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st₀.heap st₀.regions [] w₀) ∧
          (∀ l, OwnReach P st₀.heap w₀ l → pFoot i l) ∧
          (∀ l, pFoot i l → OwnReach P st₀.heap w₀ l) ∧
          (onceOnly = false → ∀ l, ¬ OwnReach P st₀.heap w₀ l)) ∧
        (∀ l, pFoot i l → Reach st₀.heap w₀ l ∧ ¬ StaticStrLoc st₀ l ∧ ¬ NumLoc st₀.heap l)) →
      (∀ (i : Nat) (p : Param) (w₀ : Val),
        ifc.params[i]? = some p → out₀[i]? = some w₀ → p.mode = .erased → ∀ l, ¬ pFoot i l) →
      (∀ (i j : Nat) (pi pj : Param) (wi wj : Val), i ≠ j →
        ifc.params[i]? = some pi → out₀[i]? = some wi →
        ifc.params[j]? = some pj → out₀[j]? = some wj →
        (pi.mode.isUnique = true → ∀ l, OwnReach P st₀.heap wi l → ¬ Reach st₀.heap wj l) ∧
        (pj.mode ≠ .erased → pi.mode.usage = .once → ∀ l, pFoot i l → ¬ Reach st₀.heap wj l) ∧
        (pj.mode ≠ .erased → pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, pFoot i l → ¬ pFoot j l)) →
      FunOkAt P ext B_call st₀
        (ifaceSkel (ifc.params.toList.drop out₀.size) ifc.res ifc.resSkel)
        onceOnly
        (fun l => ∃ i, i < out₀.size ∧ pFoot i l)
        (.ref loc cap t₀) := by
  intro B_call
  induction B_call using Nat.strongRecOn with
  | ind B_call ih =>
    intro st₀ loc cap t₀ r d ifc out₀ onceOnly pOnce pFoot hB hfind hifc hlt ho₀
      hOutAll₀ hargs₀ herFoot₀ hdisj₀
    cases B_call with
    | zero => rw [FunOkAt]; trivial
    | succ b =>
      have hbB : b ≤ B := Nat.le_of_succ_le_succ hB
      let k := out₀.size
      have hkLt : k < ifc.params.size := hlt
      let pk := ifc.params[k]
      have hdropCons : ifc.params.toList.drop k = pk :: ifc.params.toList.drop (k + 1) := by
        have hkL : k < ifc.params.toList.length := by simpa using hkLt
        simpa [pk] using list_drop_eq_cons hkL
      rw [FunOkAt]
      intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hBc hst hstat hFlt hloc hsh hrf
        hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg
      cases f with
      | imm _ => cases hloc
      | ref loc' cap' t' =>
        simp only [SameLoc] at hloc; subst hloc
        cases fuel with
        | zero =>
          simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
          exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        | succ n =>
          cases B_call with
          | zero =>
            simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
            exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          | succ b' =>
            obtain ⟨o, ho, hcap⟩ := hfBase.1.self.1
            obtain ⟨o₂, ho₂, hcs⟩ := hsh loc ⟨.pap r out₀, cap⟩ .here ho₀
            rw [ho] at ho₂; cases ho₂
            cases hc : o.cell with
            | ctor _ _ | num _ | str _ | clo _ _ _ _ _ _ | once _ _ =>
              rw [hc] at hcs; cases hcs
            | pap r' out =>
              rw [hc] at hcs
              obtain ⟨rfl, _, _⟩ := hcs
              have hoPap : st.heap.objs[loc]? = some ⟨.pap r out, cap'⟩ := by
                have hoEq : o = ⟨.pap r out, cap'⟩ := by
                  cases o; simp only at hc hcap; subst hc; subst hcap; rfl
                rw [← hoEq]; exact ho
              obtain ⟨houtSz, hlifts⟩ := pap_arg_lift ho₀ hoPap hsh hfBase hfOpen hfCf
              have hstep1 : (applyOneConformS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) =
                  (match (callWithS P ext n r (out.toList ++ [a]) c).run (st, b') with
                   | .error e => .error e
                   | .ok (g, (st₁, B₁)) =>
                     match (conform c g).run st₁ with
                     | .error e => .error e
                     | .ok (rv, st₂) => .ok (rv, (st₂, B₁))) := by
                unfold applyOneConformS applyOneS
                rw [MS_bind_run, MS_bind_run, MS_spend_succ]; dsimp only
                rw [MS_bind_run, MS_liftM_run, obj_ok hoPap]
                have hbeq : (cap' == cap') = true := by simp
                simp only [hbeq, ↓reduceIte]
                cases (callWithS P ext n r (out.toList ++ [a]) c).run (st, b') with
                | error _ => rfl
                | ok p =>
                  rcases p with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
                  rw [MS_liftM_run]
                  cases (conform c g).run st₁ <;> rfl
              rw [hstep1]
              cases n with
              | zero =>
                have hcw0 : (callWithS P ext 0 r (out.toList ++ [a]) c).run (st, b') = .error .outOfFuel := by
                  cases b' with
                  | zero => unfold callWithS; rw [MS_bind_run, MS_spend_zero]
                  | succ b'' => unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl
                rw [hcw0]
                exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              | succ n' =>
                cases b' with
                | zero =>
                  have hcw0 : (callWithS P ext (n' + 1) r (out.toList ++ [a]) c).run (st, 0) = .error .outOfFuel := by
                    unfold callWithS; rw [MS_bind_run, MS_spend_zero]
                  rw [hcw0]
                  exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                | succ b'' =>
                  have hb''B : b'' ≤ B := by omega
                  -- Dispatch non-callable / `.stuck` `RunDef`s first!
                  have hNotStuck :
                      (callWithS P ext (n' + 1) r (out.toList ++ [a]) c).run (st, b'' + 1) = .error .stuck ∨
                      ((∃ ps res' rc' rs' body', d = .body ps res' rc' rs' body') ∨
                       (∃ ps res' rc' rs', d = .extern ps res' rc' rs')) := by
                    cases d with
                    | body ps res' rc' rs' body' => exact Or.inr (Or.inl ⟨ps, res', rc', rs', body', rfl⟩)
                    | extern ps res' rc' rs' => exact Or.inr (Or.inr ⟨ps, res', rc', rs', rfl⟩)
                    | stuck ps res' rc' rs' =>
                      left
                      unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
                      rw [hfind]; rfl
                    | ind _ | ctor _ _ _ _ | caseDef _ | prim _ => simp [ifaceOf?] at hifc
                  rcases hNotStuck with hStuck | hBodyOrExt
                  · rw [hStuck]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                  -- Lift per-arg properties of `out` from `st₀` to `st` at budget `b''`
                  have hOutAll : ∀ (i : Nat) (w : Val), out[i]? = some w →
                      ValBaseOk st w ∧ DeepOpenUnder st.heap st.regions fRegs w ∧
                      CtorFieldsOk P ext b'' st w ∧
                      (onceOnly = false → NoOnceCell st.heap w) ∧
                      (∀ l, Reach st.heap w l → Reach st.heap (.ref loc cap' t') l) := by
                    intro i w hw
                    have hi : i < out.size := (Array.getElem?_eq_some_iff.mp hw).1
                    have hi₀ : i < out₀.size := houtSz ▸ hi
                    have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
                    obtain ⟨_, hlocW, hshW, hbvW, hopenW, hcfW, hreachW⟩ := hlifts i out₀[i] w hw₀ hw
                    obtain ⟨hbv₀, hno₀⟩ := hOutAll₀ i out₀[i] hw₀
                    exact ⟨hbvW, hopenW, CtorFieldsOk_mono (by omega) hcfW,
                      fun hoo => NoOnceCell_of_sameShape hbv₀.1 hshW hlocW (hno₀ hoo), hreachW⟩
                  have hOutLift : ∀ (i : Nat) (p : Param) (w : Val),
                      ifc.params[i]? = some p → out[i]? = some w → p.mode ≠ .erased →
                      (p.mode.usage = .once →
                        FunOkAt P ext b'' st p.skel (pOnce i) (pFoot i) w ∧
                        (∀ l, pFoot i l → Reach st.heap w l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
                      (p.mode.usage ≠ .once →
                        NoOnceCell st.heap w ∧ pOnce i = false ∧ (∀ l, ¬ (p.mode.isUnique = false ∧ pFoot i l)) ∧
                        FunOkAt P ext b'' st p.skel false (fun _ => False) w) ∧
                      (p.mode.isUnique = true →
                        OwnTreeFull P st.heap w ∧
                        (∀ l, OwnReach P st.heap w l → ¬ Frame l ∧ ¬ Reach st.heap a l) ∧
                        (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] w) ∧
                        (∀ l, OwnReach P st.heap w l → pFoot i l) ∧
                        (∀ l, pFoot i l → OwnReach P st.heap w l)) := by
                    intro i p w hp hw hne
                    have hi : i < out.size := (Array.getElem?_eq_some_iff.mp hw).1
                    have hi₀ : i < out₀.size := houtSz ▸ hi
                    have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
                    obtain ⟨hvshW, hlocW, hshW, _⟩ := hlifts i out₀[i] w hw₀ hw
                    have hbv₀ : ValBaseOk st₀ out₀[i] := (hOutAll₀ i out₀[i] hw₀).1
                    obtain ⟨ho1, ho2, ho3, _⟩ := hargs₀ i p out₀[i] hp hw₀ hne
                    refine ⟨?_, ?_, ?_⟩
                    · intro hu
                      obtain ⟨hf₀, hftB₀, _⟩ := ho1 hu
                      refine ⟨FunOkAt_mono (by omega) (FunOkAt_preserve_sameShape hlocW hshW hrf hf₀), fun l hfl => ?_⟩
                      have ⟨hr₀, _, hnum₀⟩ := hftB₀ l hfl
                      have hr := Reach_of_sameShapeOn hshW hlocW hr₀
                      exact ⟨hr, fun hF => hFf l hF ⟨i, hi₀, hfl⟩,
                        fun hnum => hnum₀ ((NumLoc_sameShape hshW hr₀ (hbv₀.1.reach_lt_size hr₀)).mpr hnum)⟩
                    · intro hnu
                      obtain ⟨hno₀, hpo₀, hf₀, hnf₀⟩ := ho2 hnu
                      exact ⟨NoOnceCell_of_sameShape hbv₀.1 hshW hlocW hno₀, hpo₀,
                        fun l ⟨hnuq, hfl⟩ => hnf₀ hnuq l hfl,
                        FunOkAt_mono (by omega) (FunOkAt_preserve_sameShape hlocW hshW hrf hf₀)⟩
                    · intro hu
                      obtain ⟨htr₀, hnb₀, hownSub, hownRev, _⟩ := ho3 hu
                      have hownEq : ∀ l, OwnReach P st.heap w l ↔ OwnReach P st₀.heap out₀[i] l :=
                        fun l => ⟨OwnReach_of_sameShapeOn_rev hbv₀.1 hshW hlocW, OwnReach_of_sameShapeOn hshW hlocW⟩
                      refine ⟨OwnTreeFull_of_sameShapeOn hbv₀.1 hshW hlocW htr₀,
                        fun l hor => ⟨fun hF => hFf l hF ⟨i, hi₀, hownSub l ((hownEq l).mp hor)⟩,
                                      fun hra => haf l hra ⟨i, hi₀, hownSub l ((hownEq l).mp hor)⟩⟩,
                        fun hnb => DeepOpenUnder_of_sameShapeOn hbv₀.1 hshW hvshW
                          (DeepOpenUnder_of_regsFuture hbv₀.2.2.2 (hnb₀ hnb) hrf),
                        fun l hor => hownSub l ((hownEq l).mp hor),
                        fun l hfl => (hownEq l).mpr (hownRev l hfl)⟩
                  have hOutDisj : ∀ (i j : Nat) (pi pj : Param) (wi wj : Val), i ≠ j →
                      ifc.params[i]? = some pi → out[i]? = some wi →
                      ifc.params[j]? = some pj → out[j]? = some wj →
                      (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap wi l → ¬ Reach st.heap wj l) ∧
                      (pj.mode ≠ .erased → pi.mode.usage = .once → ∀ l, pFoot i l → ¬ Reach st.heap wj l) ∧
                      (pj.mode ≠ .erased → pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, pFoot i l → ¬ pFoot j l) := by
                    intro i j pi pj wi wj hij hpi hwi hpj hwj
                    have hii : i < out.size := (Array.getElem?_eq_some_iff.mp hwi).1
                    have hjj : j < out.size := (Array.getElem?_eq_some_iff.mp hwj).1
                    have hi₀ : i < out₀.size := houtSz ▸ hii
                    have hj₀ : j < out₀.size := houtSz ▸ hjj
                    have hwi₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
                    have hwj₀ : out₀[j]? = some out₀[j] := Array.getElem?_eq_getElem hj₀
                    obtain ⟨_, hlocI, hshI, _⟩ := hlifts i out₀[i] wi hwi₀ hwi
                    obtain ⟨_, hlocJ, hshJ, _⟩ := hlifts j out₀[j] wj hwj₀ hwj
                    obtain ⟨hdu₀, hdf₀, hdff₀⟩ := hdisj₀ i j pi pj out₀[i] out₀[j] hij hpi hwi₀ hpj hwj₀
                    have hbi₀ : ValBaseOk st₀ out₀[i] := (hOutAll₀ i out₀[i] hwi₀).1
                    have hbj₀ : ValBaseOk st₀ out₀[j] := (hOutAll₀ j out₀[j] hwj₀).1
                    refine ⟨fun hu l hor hrj => ?_, fun hnej hu l hfl hrj => ?_, hdff₀⟩
                    · exact hdu₀ hu l (OwnReach_of_sameShapeOn_rev hbi₀.1 hshI hlocI hor)
                        (Reach_of_sameShapeOn_rev hbj₀.1 hshJ hlocJ hrj)
                    · exact hdf₀ hnej hu l hfl (Reach_of_sameShapeOn_rev hbj₀.1 hshJ hlocJ hrj)
                  let vs : List Val := out.toList ++ [a]
                  have hvsLen : vs.length = k + 1 := by simp [vs, houtSz, k]
                  have hvsGet : ∀ (i : Nat) (v : Val), vs[i]? = some v →
                      (i < k ∧ out[i]? = some v) ∨ (i = k ∧ v = a) := by
                    intro i v hv
                    by_cases hilt : i < out.size
                    · have hltL : i < out.toList.length := by simpa using hilt
                      rw [List.getElem?_append_left hltL] at hv
                      have hszK : out.size = k := houtSz
                      left; refine ⟨by omega, ?_⟩
                      simpa [Array.getElem?_toList] using hv
                    · have hgeL : out.toList.length ≤ i := by simpa using Nat.le_of_not_lt hilt
                      rw [List.getElem?_append_right hgeL] at hv
                      cases hd : i - out.toList.length with
                      | zero =>
                        rw [hd] at hv; simp at hv
                        right; exact ⟨by have hszK : out.size = k := houtSz; simp only [Array.length_toList] at hgeL hd; omega, hv.symm⟩
                      | succ m =>
                        rw [hd] at hv; simp at hv
                  have hpkGet : ifc.params[k]? = some pk := Array.getElem?_eq_getElem hkLt
                  -- Split under-applied (`k + 1 < ifc.params.size`) vs saturated (`k + 1 = ifc.params.size`)
                  by_cases hMore : k + 1 < ifc.params.size
                  · -- **Subcase 1: Still under-applied (`k + 1 < ifc.params.size`)!**
                    have hdrop2 : ifc.params.toList.drop (k + 1) =
                        ifc.params[k + 1] :: ifc.params.toList.drop (k + 2) := by
                      have hk1L : k + 1 < ifc.params.toList.length := by simpa using hMore
                      simpa using list_drop_eq_cons hk1L
                    let cod := ifaceSkel (ifc.params.toList.drop (k + 1)) ifc.res ifc.resSkel
                    have hskEq : ifaceSkel (ifc.params.toList.drop out₀.size) ifc.res ifc.resSkel =
                        .arrow pk.mode pk.skel .shared cod := by
                      change ifaceSkel (ifc.params.toList.drop k) ifc.res ifc.resSkel = _
                      dsimp only [cod]; rw [hdropCons, hdrop2]; rfl
                    simp only [hskEq] at haNum harg ⊢
                    have hcwMakePap :
                        ((match (callWithS P ext (n' + 1) r vs c).run (st, b'' + 1) with
                         | .error e => .error e
                         | .ok (g, (st₁, B₁)) =>
                           match (conform c g).run st₁ with
                           | .error e => .error e
                           | .ok (rv, st₂) => .ok (rv, (st₂, B₁))) : Except Stop (Val × St × Nat)) =
                        ((match (makePap P n' r ifc.params vs).run st with
                         | .error e => .error e
                         | .ok (g, st₁) =>
                           match (conform c g).run st₁ with
                           | .error e => .error e
                           | .ok (rv, st₂) => .ok (rv, (st₂, b''))) : Except Stop (Val × St × Nat)) := by
                      have hlenLt : vs.length < ifc.params.size := by rw [hvsLen]; exact hMore
                      unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
                      rw [hfind]
                      rcases hBodyOrExt with ⟨ps, res', rc', rs', body', rfl⟩ | ⟨ps, res', rc', rs', rfl⟩
                      · simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
                        simp only [hlenLt, ↓reduceIte, MS_liftM_run]
                        cases (makePap P n' r ps vs).run st <;> rfl
                      · simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
                        simp only [hlenLt, ↓reduceIte, MS_liftM_run]
                        cases (makePap P n' r ps vs).run st <;> rfl
                    rw [hcwMakePap]
                    exact pap_iface_under_step hkLt hMore hpkGet houtSz
                      hst hstat hFlt haBase haOpen haCf hFf hFa h12 hfa haf haNum
                      (fun hne => let h := harg hne; ⟨h.1, h.2.1, h.2.2.1⟩)
                      hOutAll₀ hargs₀ herFoot₀ hlifts hOutAll hOutLift hOutDisj
                      (fun hlt₁ ho₁ h1 h2 h3 h4 =>
                        ih b'' (by omega) (by omega) hfind hifc hlt₁ ho₁ h1 h2 h3 h4)
                  · -- **Subcase 2: Saturated (`k + 1 = ifc.params.size`)!**
                    have hSatEq : k + 1 = ifc.params.size := by omega
                    have hdrop2 : ifc.params.toList.drop (k + 1) = [] := by
                      simp [hSatEq]
                    have hskEq : ifaceSkel (ifc.params.toList.drop out₀.size) ifc.res ifc.resSkel =
                        .arrow pk.mode pk.skel ifc.res ifc.resSkel := by
                      change ifaceSkel (ifc.params.toList.drop k) ifc.res ifc.resSkel = _
                      rw [hdropCons, hdrop2]; rfl
                    simp only [hskEq] at haNum harg ⊢
                    have hlenEq : vs.length = ifc.params.size := by rw [hvsLen, hSatEq]
                    have hnotLt : ¬ (vs.length < ifc.params.size) := by omega
                    have htake : vs.take ifc.params.size = vs := by rw [← hlenEq]; exact List.take_length
                    have hdrop : vs.drop ifc.params.size = [] := by rw [← hlenEq]; exact List.drop_length
                    have hne0 : (ifc.params.size == 0) = false := by
                      have : ifc.params.size ≠ 0 := by omega
                      exact beq_false_of_ne this
                    -- Now split `d = .body` vs `d = .extern`!
                    rcases hBodyOrExt with ⟨ps, res', rc', rs', body', rfl⟩ | ⟨ps, res', rc', rs', rfl⟩
                    · -- **Subcase 2a: `d = .body`**
                      simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
                      have hcwBody : (callWithS P ext (n' + 1) r vs c).run (st, b'' + 1) =
                          (match (enterS P ext n' ps res' rc' body' vs).run (st, b'') with
                           | .error e => .error e
                           | .ok (g, (st₁, B₁)) => (applyAllS P ext n' g [] c).run (st₁, B₁)) := by
                        unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
                        rw [hfind]; simp only [hnotLt, ↓reduceIte, hne0, Bool.false_eq_true, htake, hdrop]
                        rw [MS_bind_run]
                        cases (enterS P ext n' ps res' rc' body' vs).run (st, b'') with
                        | error _ => rfl
                        | ok p => rcases p with ⟨g, ⟨st₁, B₁⟩⟩; rfl
                      rw [hcwBody]
                      let argOnce : Nat → Bool := fun i => if i < k then pOnce i else aOnce
                      let argFoot : Nat → Nat → Prop := fun i l =>
                        if i < k then (if (ps[i]?.map (fun p => p.mode.usage == .once)).getD false then pFoot i l else False)
                        else if pk.mode.usage == .once then aFoot l else False
                      have hArgsBody : ∀ (i : Nat) (p : Param) (v : Val), ps[i]? = some p → vs[i]? = some v →
                          (p.mode ≠ .erased →
                            ValBaseOk st v ∧ DeepOpenUnder st.heap st.regions (aRegs ++ fRegs) v ∧
                            CtorFieldsOk P ext b'' st v ∧
                            (p.mode.usage = .once →
                              FunOkAt P ext b'' st p.skel (argOnce i) (argFoot i) v ∧
                              (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
                            (p.mode.usage ≠ .once →
                              NoOnceCell st.heap v ∧ argOnce i = false ∧ (∀ l, ¬ argFoot i l) ∧
                              FunOkAt P ext b'' st p.skel false (fun _ => False) v) ∧
                            (p.mode.isUnique = true →
                              OwnTreeFull P st.heap v ∧
                              (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
                              (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v))) := by
                        intro i p v hp hv hne
                        rcases hvsGet i v hv with ⟨hiLt, hw⟩ | ⟨rfl, rfl⟩
                        · have hA := hOutAll i v hw
                          have hL := hOutLift i p v hp hw hne
                          have hO : argOnce i = pOnce i := by simp [argOnce, hiLt]
                          rw [hO]
                          refine ⟨hA.1, hA.2.1.mono (fun x hx => List.mem_append_right _ hx), hA.2.2.1,
                            fun hu => ?_, fun hnu => ?_, fun hu => let h := hL.2.2 hu; ⟨h.1, fun l hor => (h.2.1 l hor).1, h.2.2.1⟩⟩
                          · have hF : argFoot i = pFoot i := by funext l; simp [argFoot, hiLt, hp, hu]
                            rw [hF]; exact hL.1 hu
                          · obtain ⟨hno, hpo, _, hf⟩ := hL.2.1 hnu
                            have hbeqF : (p.mode.usage == .once) = false := beq_false_of_ne hnu
                            exact ⟨hno, hpo, fun l hl => by simp [argFoot, hiLt, hp, hbeqF] at hl, hf⟩
                        · rw [hpkGet] at hp; cases hp
                          have hnotLt : ¬ (k < k) := Nat.lt_irrefl k
                          have hO : argOnce k = aOnce := by simp [argOnce, hnotLt]
                          rw [hO]
                          obtain ⟨ho1, ho2, ho3, _⟩ := harg hne
                          refine ⟨haBase, haOpen.mono (fun x hx => List.mem_append_left _ hx),
                            CtorFieldsOk_mono (by omega) haCf, fun hu => ?_, fun hnu => ?_,
                            fun hu => let h := ho3 hu; ⟨h.1, fun l hor => (h.2.1 l hor).1, h.2.2⟩⟩
                          · have hF : argFoot k = aFoot := by funext l; simp [argFoot, hnotLt, hu]
                            rw [hF]
                            exact ⟨FunOkAt_mono (by omega) (ho1 hu), fun l hl =>
                              ⟨(haNum.1 l hl).1, fun hFr => hFa l hFr hl, (haNum.1 l hl).2⟩⟩
                          · obtain ⟨hno, haO, _, hf⟩ := ho2 hnu
                            have hbeqF : (pk.mode.usage == .once) = false := beq_false_of_ne hnu
                            exact ⟨hno, haO, fun l hl => by simp [argFoot, hnotLt, hbeqF] at hl, FunOkAt_mono (by omega) hf⟩
                      have hDisjBody : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
                          ps[i]? = some pi → vs[i]? = some vi →
                          ps[j]? = some pj → vs[j]? = some vj → pj.mode ≠ .erased →
                          (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) ∧
                          (pi.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap vj l) ∧
                          (pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, argFoot i l → ¬ argFoot j l) := by
                        intro i j pi pj vi vj hij hpi hvi hpj hvj hnej
                        rcases hvsGet i vi hvi with ⟨hiLt, hwi⟩ | ⟨rfl, rfl⟩
                        · rcases hvsGet j vj hvj with ⟨hjLt, hwj⟩ | ⟨rfl, rfl⟩
                          · obtain ⟨hd1, hd2, hd3⟩ := hOutDisj i j pi pj vi vj hij hpi hwi hpj hwj
                            refine ⟨hd1, fun hui l hfl hrj => hd2 hnej hui l (by simpa [argFoot, hiLt, hpi, hui] using hfl) hrj,
                              fun hui huj l hfi hfj => hd3 hnej hui huj l
                                (by simpa [argFoot, hiLt, hpi, hui] using hfi)
                                (by simpa [argFoot, hjLt, hpj, huj] using hfj)⟩
                          · rw [hpkGet] at hpj; cases hpj
                            have hnei : pi.mode.isUnique = true → pi.mode ≠ .erased := fun hu h => by rw [h] at hu; cases hu
                            refine ⟨fun hu l hor hrj => ((hOutLift i pi vi hpi hwi (hnei hu)).2.2 hu).2.1 l hor |>.2 hrj,
                              fun hui l hfl hrj => haf l hrj ⟨i, hiLt, by simpa [argFoot, hiLt, hpi, hui] using hfl⟩,
                              fun hui huj l hfi hfj => h12 l ⟨i, hiLt, by simpa [argFoot, hiLt, hpi, hui] using hfi⟩
                                (by simpa [argFoot, Nat.lt_irrefl k, huj] using hfj)⟩
                        · rw [hpkGet] at hpi; cases hpi
                          rcases hvsGet j vj hvj with ⟨hjLt, hwj⟩ | ⟨heq, _⟩
                          · refine ⟨fun hu l hor hrj => ?_, fun hui l hfl hrj => ?_, fun hui huj l hfi hfj => ?_⟩
                            · have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
                              exact ((harg hne).2.2.1 hu).2.1 l hor |>.2 ((hOutAll j vj hwj).2.2.2.2 l hrj)
                            · exact hfa l ((hOutAll j vj hwj).2.2.2.2 l hrj) (by simpa [argFoot, Nat.lt_irrefl k, hui] using hfl)
                            · exact h12 l ⟨j, hjLt, by simpa [argFoot, hjLt, hpj, huj] using hfj⟩
                                (by simpa [argFoot, Nat.lt_irrefl k, hui] using hfi)
                          · exact absurd heq.symm hij
                      obtain ⟨hnoVE, hokE⟩ := hih.2.1 b'' n' r ps res' rc' rs' body' vs st Frame (aRegs ++ fRegs)
                        argOnce argFoot hb''B hfind hlenEq (StOk_mono (by omega) hst) hstat hFlt hArgsBody hDisjBody
                      cases hent : (enterS P ext n' ps res' rc' body' vs).run (st, b'') with
                      | error e =>
                        refine ⟨fun k' hk' => by cases hk'; exact hnoVE k' hent, fun _ _ _ h => by cases h⟩
                      | ok p =>
                        rcases p with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
                        obtain ⟨hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁, hpres₁, honce₁, hssf₁,
                          hbaseG, hclsG, hnoG, hcfG, hfunG, hopenG, hreachG, huniqG⟩ := hokE g st₁ B₁ hent
                        have hopenGVal : c = .val → DeepOpenUnder st₁.heap st₁.regions (applyResultRegs st res' .val fRegs aRegs) g := by
                          intro _
                          exact hopenG.mono fun x hx =>
                            applyResultRegs_sub_of_pap x
                              (applyResultRegs_mono (fun _ h => by cases h) (fun _ h => h) x hx)
                        have hreachGAll : ∀ l, Reach st₁.heap g l →
                            st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l ∨
                            StaticStrLoc st l ∨ NumLoc st₁.heap l := by
                          intro l hrl
                          rcases hreachG l hrl with hge | ⟨i, p, v, _, hv, _, _, hrv⟩ | hss | hnum
                          · exact Or.inl hge
                          · rcases hvsGet i v hv with ⟨_, hw⟩ | ⟨_, rfl⟩
                            · exact Or.inr (Or.inl ((hOutAll i v hw).2.2.2.2 l hrv))
                            · exact Or.inr (Or.inr (Or.inl hrv))
                          · exact Or.inr (Or.inr (Or.inr (Or.inl hss)))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr hnum)))
                        have hnoArgG : res' = .unique → (pk.mode.isBorrowed = true ∨ pk.mode = .erased) →
                            ∀ l, Reach st₁.heap g l →
                              st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨
                              StaticStrLoc st l ∨ NumLoc st₁.heap l := by
                          intro hru hbe l hrl
                          rcases hreachG l hrl with hge | ⟨i, p, v, hp, hv, hne, hbor, hrv⟩ | hss | hnum
                          · exact Or.inl hge
                          · rcases hvsGet i v hv with ⟨_, hw⟩ | ⟨rfl, rfl⟩
                            · exact Or.inr (Or.inl ((hOutAll i v hw).2.2.2.2 l hrv))
                            · rw [hpkGet] at hp; cases hp
                              rw [hru] at hbor
                              rcases hbor with h1 | h2
                              · cases h1
                              · rcases hbe with h3 | h4
                                · rw [h3] at h2; cases h2
                                · exact absurd h4 hne
                          · exact Or.inr (Or.inr (Or.inl hss))
                          · exact Or.inr (Or.inr (Or.inr hnum))
                        exact pap_sat_finish (onceOnly := onceOnly) (m_in := pk.mode) hFlt (by omega) hst₁ hsz₁ hcap₁ hr₁ hnr₁ hstat₁ hstr₁ hpres₁ honce₁ hssf₁
                          hbaseG hclsG hnoG hcfG hfunG hopenGVal hreachGAll huniqG hnoArgG
                    · -- **Subcase 2b: `d = .extern`**
                      simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
                      have hcwExt : (callWithS P ext (n' + 1) r vs c).run (st, b'' + 1) =
                          (match (callExtern P ext n' r ps res' rc' vs).run st with
                           | .error e => .error e
                           | .ok (g, st₁) => (applyAllS P ext n' g [] c).run (st₁, b'')) := by
                        unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
                        rw [hfind]; simp only [hnotLt, ↓reduceIte, htake, hdrop]
                        rw [MS_bind_run, MS_liftM_run]
                        cases (callExtern P ext n' r ps res' rc' vs).run st with
                        | error _ => rfl
                        | ok p => rcases p with ⟨g, st₁⟩; rfl
                      rw [hcwExt]
                      let baseR : List Nat := if c == .val then fRegs else aRegs ++ fRegs
                      have hArgsExt : ∀ (i : Nat) (p : Param) (v : Val), ps[i]? = some p → vs[i]? = some v →
                          (p.mode ≠ .erased →
                            ValBaseOk st v ∧ DeepOpenUnder st.heap st.regions (aRegs ++ fRegs) v ∧
                            (p.mode.usage ≠ .once → NoOnceCell st.heap v) ∧
                            CtorFieldsOk P ext b'' st v ∧
                            (p.mode.usage ≠ .once → FunOkAt P ext b'' st p.skel false (fun _ => False) v)) ∧
                          (p.mode.isUnique = true →
                            OwnTreeFull P st.heap v ∧
                            (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
                            (p.mode.isBorrowed = false → OpenUnder st.regions [] v)) ∧
                          (res' = .unique → rc' = .val → p.mode = .many → p.cls ≠ .leaf →
                            DeepOpenUnder st.heap st.regions baseR v) := by
                        intro i p v hp hv
                        rcases hvsGet i v hv with ⟨hiLt, hw⟩ | ⟨rfl, rfl⟩
                        · have hA := hOutAll i v hw
                          have hsubF : ∀ x ∈ fRegs, x ∈ baseR := by
                            intro x hx; dsimp only [baseR]
                            cases (c == .val) <;> simp only [Bool.false_eq_true, ↓reduceIte]
                            · exact List.mem_append_right _ hx
                            · exact hx
                          refine ⟨fun hne => ?_, fun hu => ?_, fun _ _ _ _ => hA.2.1.mono hsubF⟩
                          · have hL := hOutLift i p v hp hw hne
                            exact ⟨hA.1, hA.2.1.mono (fun x hx => List.mem_append_right _ hx),
                              fun hnu => (hL.2.1 hnu).1, hA.2.2.1, fun hnu => (hL.2.1 hnu).2.2.2⟩
                          · have hne : p.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
                            have hU := (hOutLift i p v hp hw hne).2.2 hu
                            exact ⟨hU.1, fun l hor => (hU.2.1 l hor).1, fun hnb => (hU.2.2.1 hnb).self⟩
                        · rw [hpkGet] at hp; cases hp
                          refine ⟨fun hne => ?_, fun hu => ?_, fun hru hrc hm _ => ?_⟩
                          · obtain ⟨_, ho2, _, _⟩ := harg hne
                            exact ⟨haBase, haOpen.mono (fun x hx => List.mem_append_left _ hx),
                              fun hnu => (ho2 hnu).1, CtorFieldsOk_mono (by omega) haCf,
                              fun hnu => FunOkAt_mono (by omega) (ho2 hnu).2.2.2⟩
                          · have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
                            have hU := (harg hne).2.2.1 hu
                            exact ⟨hU.1, fun l hor => (hU.2.1 l hor).1, fun hnb => (hU.2.2 hnb).self⟩
                          · by_cases hcv : c = .val
                            · have hne : pk.mode ≠ .erased := by rw [hm]; decide
                              have hEqB : baseR = fRegs := by dsimp [baseR]; rw [hcv]; rfl
                              rw [hEqB]
                              exact ((harg hne).2.2.2 ⟨hru, hcv, Or.inl hm⟩).mono (fun _ h => by cases h)
                            · have hEqB : baseR = aRegs ++ fRegs := by
                                have hbf : (c == .val) = false := by
                                  cases c with
                                  | val => exact absurd rfl hcv
                                  | irr | imm | leaf => rfl
                                dsimp [baseR]; rw [hbf]; rfl
                              rw [hEqB]
                              exact haOpen.mono (fun x hx => List.mem_append_left _ hx)
                      have hDisjExt : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
                          ps[i]? = some pi → vs[i]? = some vi →
                          ps[j]? = some pj → vs[j]? = some vj →
                          pi.mode.isUnique = true → pj.mode ≠ .erased →
                          ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l := by
                        intro i j pi pj vi vj hij hpi hvi hpj hvj hu _ l hor hrj
                        rcases hvsGet i vi hvi with ⟨hiLt, hwi⟩ | ⟨rfl, rfl⟩
                        · rcases hvsGet j vj hvj with ⟨hjLt, hwj⟩ | ⟨rfl, rfl⟩
                          · exact (hOutDisj i j pi pj vi vj hij hpi hwi hpj hwj).1 hu l hor hrj
                          · have hnei : pi.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
                            exact ((hOutLift i pi vi hpi hwi hnei).2.2 hu).2.1 l hor |>.2 hrj
                        · rw [hpkGet] at hpi; cases hpi
                          rcases hvsGet j vj hvj with ⟨hjLt, hwj⟩ | ⟨heq, _⟩
                          · have hne : pk.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
                            exact ((harg hne).2.2.1 hu).2.1 l hor |>.2 ((hOutAll j vj hwj).2.2.2.2 l hrj)
                          · exact absurd heq.symm hij
                      obtain ⟨hnoVE, hokE⟩ := callExtern_sound_base (baseRegs := baseR) (argRegs := aRegs ++ fRegs)
                        hext hfind (StOk_mono (by omega) hst) (hih.1 b'' hb''B) hstat hFlt hArgsExt hDisjExt
                      cases hextRun : (callExtern P ext n' r ps res' rc' vs).run st with
                      | error e =>
                        refine ⟨fun k' hk' => by cases hk'; exact hnoVE k' hextRun, fun _ _ _ h => by cases h⟩
                      | ok p =>
                        rcases p with ⟨g, st₁⟩; dsimp only
                        obtain ⟨hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁, hpres₁, honce₁, hssf₁,
                          hbaseG, hclsG, hopenG, hnoG, hcfG, hfunG, hreachG, huniqG⟩ := hokE g st₁ hextRun
                        have hopenGVal : c = .val → DeepOpenUnder st₁.heap st₁.regions (applyResultRegs st res' .val fRegs aRegs) g := by
                          intro hcv
                          have hEqB : baseR = fRegs := by dsimp [baseR]; rw [hcv]; rfl
                          rw [hEqB] at hopenG
                          exact hopenG.mono (applyResultRegs_sub_of_pap (st := st) (res := res') (rc := rc'))
                        have hreachGAll : ∀ l, Reach st₁.heap g l →
                            st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l ∨
                            StaticStrLoc st l ∨ NumLoc st₁.heap l := by
                          intro l hrl
                          rcases hreachG l hrl with hge | ⟨i, p, v, _, hv, _, hrv⟩ | ⟨o', n, ho', hc'⟩
                          · exact Or.inl hge
                          · rcases hvsGet i v hv with ⟨_, hw⟩ | ⟨_, rfl⟩
                            · exact Or.inr (Or.inl ((hOutAll i v hw).2.2.2.2 l hrv))
                            · exact Or.inr (Or.inr (Or.inl hrv))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨o', n, ho', hc'⟩)))
                        have hnoArgG : res' = .unique → (pk.mode.isBorrowed = true ∨ pk.mode = .erased) →
                            ∀ l, Reach st₁.heap g l →
                              st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨
                              StaticStrLoc st l ∨ NumLoc st₁.heap l := by
                          intro _ hbe l hrl
                          rcases hreachG l hrl with hge | ⟨i, p, v, hp, hv, hm, hrv⟩ | ⟨o', n, ho', hc'⟩
                          · exact Or.inl hge
                          · rcases hvsGet i v hv with ⟨_, hw⟩ | ⟨rfl, rfl⟩
                            · exact Or.inr (Or.inl ((hOutAll i v hw).2.2.2.2 l hrv))
                            · rw [hpkGet] at hp; cases hp
                              rcases hbe with h3 | h4
                              · rw [hm] at h3; cases h3
                              · rw [hm] at h4; cases h4
                          · exact Or.inr (Or.inr (Or.inr ⟨o', n, ho', hc'⟩))
                        exact pap_sat_finish (onceOnly := onceOnly) (m_in := pk.mode) hFlt (by omega) hst₁ hsz₁ hcap₁ hr₁ hnr₁
                          (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _) hpres₁ honce₁ hssf₁
                          hbaseG hclsG hnoG hcfG hfunG hopenGVal hreachGAll
                          (fun h => let hu := huniqG h; ⟨hu.1, fun l hor => (hu.2 l hor).2⟩) hnoArgG

/-- General `FunOkAt .unknown false False` for a runtime `.pap r out` cell of ANY constructor
`P.find? r = some (.ctor ind cidx nP fields)` (including constructors with `@shared`/`@erased`
fields). Proved by strong induction on `B_call`. -/
theorem pap_ctor_funOk {P : Prog} {ext : ExternOracle} :
    ∀ {B_call : Nat} {st₀ : St} {loc cap : Nat} {t₀ : List Nat}
      {r : Ref} {ind : Ref} {cidx nP : Nat} {fields : Array Field} {out₀ : Array Val},
      P.find? r = some (.ctor ind cidx nP fields) →
      st₀.heap.objs[loc]? = some ⟨.pap r out₀, cap⟩ →
      (∀ w ∈ out₀.toList,
        ValBaseOk st₀ w ∧ NoOnceCell st₀.heap w ∧ CtorFieldsOk P ext B_call st₀ w ∧
        FunOkAt P ext B_call st₀ .unknown false (fun _ => False) w) →
      FunOkAt P ext B_call st₀ .unknown false (fun _ => False) (.ref loc cap t₀) := by
  intro B_call
  induction B_call using Nat.strongRecOn with
  | ind B_call ih =>
    intro st₀ loc cap t₀ r ind cidx nP fields out₀ hfind ho₀ hargs₀
    cases B_call with
    | zero => rw [FunOkAt]; trivial
    | succ b =>
      rw [FunOkAt]
      dsimp only [arrowParts]
      intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hBc hst hstat hFlt hloc hsh hrf
        hfBase hfOpen hfCf haBase haOpen haCf _ _ _ _ _ _ harg
      cases f with
      | imm _ => cases hloc
      | ref loc' cap' t' =>
        simp only [SameLoc] at hloc; subst hloc
        cases fuel with
        | zero =>
          simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
          exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        | succ n =>
          cases B_call with
          | zero =>
            simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
            exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          | succ b' =>
            obtain ⟨o, ho, hcap⟩ := hfBase.1.self.1
            obtain ⟨o₂, ho₂, hcs⟩ := hsh loc ⟨.pap r out₀, cap⟩ .here ho₀
            rw [ho] at ho₂; cases ho₂
            cases hc : o.cell with
            | ctor _ _ | num _ | str _ | clo _ _ _ _ _ _ | once _ _ =>
              rw [hc] at hcs; cases hcs
            | pap r' out =>
              rw [hc] at hcs
              obtain ⟨rfl, _, _⟩ := hcs
              have hoPap : st.heap.objs[loc]? = some ⟨.pap r out, cap'⟩ := by
                have hoEq : o = ⟨.pap r out, cap'⟩ := by
                  cases o; simp only at hc hcap; subst hc; subst hcap; rfl
                rw [← hoEq]; exact ho
              obtain ⟨houtSz, hlifts⟩ := pap_arg_lift ho₀ hoPap hsh hfBase hfOpen hfCf
              have hstep1 : (applyOneConformS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) =
                  (match (callWithS P ext n r (out.toList ++ [a]) c).run (st, b') with
                   | .error e => .error e
                   | .ok (g, (st₁, B₁)) =>
                     match (conform c g).run st₁ with
                     | .error e => .error e
                     | .ok (rv, st₂) => .ok (rv, (st₂, B₁))) := by
                unfold applyOneConformS applyOneS
                rw [MS_bind_run, MS_bind_run, MS_spend_succ]; dsimp only
                rw [MS_bind_run, MS_liftM_run, obj_ok hoPap]
                have hbeq : (cap' == cap') = true := by simp
                simp only [hbeq, ↓reduceIte]
                cases (callWithS P ext n r (out.toList ++ [a]) c).run (st, b') with
                | error _ => rfl
                | ok p =>
                  rcases p with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
                  rw [MS_liftM_run]
                  cases (conform c g).run st₁ <;> rfl
              rw [hstep1]
              cases n with
              | zero =>
                have hcw0 : (callWithS P ext 0 r (out.toList ++ [a]) c).run (st, b') = .error .outOfFuel := by
                  cases b' with
                  | zero => unfold callWithS; rw [MS_bind_run, MS_spend_zero]
                  | succ b'' => unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl
                rw [hcw0]
                exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              | succ n' =>
                cases b' with
                | zero =>
                  have hcw0 : (callWithS P ext (n' + 1) r (out.toList ++ [a]) c).run (st, 0) = .error .outOfFuel := by
                    unfold callWithS; rw [MS_bind_run, MS_spend_zero]
                  rw [hcw0]
                  exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                | succ b'' =>
                  obtain ⟨haNo, _, _, haFun⟩ := (harg (by decide)).2.1 (by decide)
                  let vs : List Val := out.toList ++ [a]
                  have hvsProps : ∀ v ∈ vs,
                      ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext b'' st v ∧
                      FunOkAt P ext b'' st .unknown false (fun _ => False) v ∧
                      DeepOpenUnder st.heap st.regions (aRegs ++ fRegs) v ∧
                      (∀ l, Reach st.heap v l → Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l) := by
                    intro v hv
                    rcases List.mem_append.mp hv with hvOut | hvA
                    · obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hvOut)
                      have hi₀ : i < out₀.size := houtSz ▸ hi
                      have hw₀ : out₀[i]? = some out₀[i] := Array.getElem?_eq_getElem hi₀
                      have hw : out[i]? = some out[i] := Array.getElem?_eq_getElem hi
                      obtain ⟨_, hlocW, hshW, hbvW, hopenW, hcfW, hreachW⟩ := hlifts i out₀[i] out[i] hw₀ hw
                      obtain ⟨hbv₀, hno₀, _, hfun₀⟩ := hargs₀ out₀[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi₀))
                      exact ⟨hbvW, NoOnceCell_of_sameShape hbv₀.1 hshW hlocW hno₀,
                        CtorFieldsOk_mono (by omega) hcfW,
                        FunOkAt_mono (by omega) (FunOkAt_preserve_sameShape hlocW hshW hrf hfun₀),
                        hopenW.mono (fun x hx => List.mem_append_right _ hx),
                        fun l hrl => Or.inl (hreachW l hrl)⟩
                    · simp only [List.mem_singleton] at hvA; subst hvA
                      exact ⟨haBase, haNo, CtorFieldsOk_mono (by omega) haCf,
                        FunOkAt_mono (by omega) haFun,
                        haOpen.mono (fun x hx => List.mem_append_left _ hx),
                        fun _ hrl => Or.inr hrl⟩
                  have hst'' : StOk P ext b'' st := StOk_mono (by omega) hst
                  have hcwUnfold : (callWithS P ext (n' + 1) r vs c).run (st, b'' + 1) =
                      if vs.length < nP + fields.size then
                        match (makePap P n' r #[] vs).run st with
                        | .error e => .error e
                        | .ok (g, st₁) => .ok (g, (st₁, b''))
                      else if vs.length > nP + fields.size then .error .stuck
                      else
                        match (construct r fields (vs.drop nP) c).run st with
                        | .error e => .error e
                        | .ok (g, st₁) => .ok (g, (st₁, b'')) := by
                    unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
                    rw [hfind]
                    by_cases hltC : vs.length < nP + fields.size
                    · simp only [hltC, ↓reduceIte, MS_liftM_run]
                      cases (makePap P n' r #[] vs).run st <;> rfl
                    · simp only [hltC, ↓reduceIte]
                      by_cases hgtC : vs.length > nP + fields.size
                      · simp only [hgtC, ↓reduceIte, MS_liftM_run]; rfl
                      · simp only [hgtC, ↓reduceIte, MS_liftM_run]
                        cases (construct r fields (vs.drop nP) c).run st <;> rfl
                  rw [hcwUnfold]
                  by_cases hltC : vs.length < nP + fields.size
                  · simp only [hltC, ↓reduceIte]
                    rcases makePap_sound (P := P) (ext := ext) (B := b'') (fuel := n') (r := r) (params := #[]) (vs := vs)
                        hst'' (fun v hv => let h := hvsProps v hv; ⟨h.1, h.2.1, h.2.2.1⟩)
                        (fun i v _ hu => by simp [BinderMode.isUnique] at hu) (fun i j _ _ _ _ _ hu => by simp [BinderMode.isUnique] at hu) with hOOF |
                      ⟨g, out', st₁, hmpRun, hr₁, hnr₁, hstat₁, hstr₁, hsz₁, hcap₁, _, hpres₁,
                       honce₁, hssf₁, hst₁, ⟨cap₁, hgEq, hoNew₁⟩, houtSz', houtProps', hbaseG,
                       hnoG, hcfG, hdouG, hreachG⟩
                    · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                    · rw [hmpRun]; dsimp only
                      have hfunG : FunOkAt P ext b'' st₁ .unknown false (fun _ => False) g := by
                        rw [hgEq]
                        refine ih b'' (by omega) hfind hoNew₁ fun w' hw' => ?_
                        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hw')
                        have hiV : i < vs.length := houtSz' ▸ hi
                        obtain ⟨w₁, hw₁, _, hbv₁, hno₁, hcf₁, hfun₁⟩ := houtProps' i vs[i] (List.getElem?_eq_getElem hiV)
                        rw [Array.getElem?_eq_getElem hi] at hw₁; cases hw₁
                        exact ⟨hbv₁, hno₁, hcf₁, hfun₁ _ _ _ (hvsProps vs[i] (List.getElem_mem hiV)).2.2.2.1⟩
                      have hdouGRes : DeepOpenUnder st₁.heap st₁.regions (applyResultRegs st .shared .val fRegs aRegs) g := by
                        rw [hr₁]
                        refine hdouG st.regions _ fun v hv => (hvsProps v hv).2.2.2.2.1.mono fun x hx => by
                          simpa [applyResultRegs, show (Cls.val != Cls.val) = false from rfl] using hx
                      rcases conform_post_apply (res := .shared) (fRegs := fRegs) (aRegs := aRegs)
                          hst₁ hbaseG hcfG (fun _ => hnoG) hfunG (fun _ => hdouGRes) with hStC |
                        ⟨rv, st₂, hcRun, hr₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂,
                         hst₂, hbv₂, hcls₂, hdou₂, hcf₂, hreach₂, hno₂, hfun₂, _⟩
                      · rw [hStC]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                      · rw [hcRun]
                        refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
                        cases hok
                        have hpresOld1 : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₁.heap :=
                          hpres₁.mono fun l hlt => ⟨hlt, fun _ _ _ hu => by simp [BinderMode.isUnique] at hu⟩
                        have hpresAll : PreservesLocs Frame st.heap st₂.heap :=
                          (hpresOld1.mono hFlt).trans (hpres₂.mono fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) (by omega))
                        have hssfAll : StaticStrFresh st st₂ :=
                          StaticStrFresh.trans (by omega) (hpres₂.mono fun _ hl => StOk_staticStrLoc_lt hst₁ hl) hssf₁ hssf₂
                        have hreachAll : ∀ l, Reach st₂.heap rv l →
                            st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l ∨
                            StaticStrLoc st l ∨ NumLoc st₂.heap l := by
                          intro l hrl
                          rcases hreach₂ l hrl with hge1 | hrg
                          · exact Or.inl (by omega)
                          · rcases hreachG l hrg with rfl | ⟨v, hv, hrv⟩
                            · exact Or.inl (Nat.le_refl _)
                            · rcases (hvsProps v hv).2.2.2.2.2 l hrv with hf' | ha'
                              · exact Or.inr (Or.inl hf')
                              · exact Or.inr (Or.inr (Or.inl ha'))
                        refine ⟨by omega, hst₂, by omega, Nat.le_trans hcap₁ hcap₂,
                          hr₂.trans hr₁, by rw [hnr₂, hnr₁]; exact Nat.le_refl _,
                          by rw [hstat₂, hstat₁]; exact ArrayExtends.refl _,
                          by rw [hstr₂, hstr₁]; exact ArrayExtends.refl _,
                          hpresAll, honce₁.trans honce₂, hssfAll,
                          hbv₂, hcls₂, by rw [applyResultRegs_eq_of_regions hr₁] at hdou₂; exact hdou₂, hcf₂, hreachAll,
                          ⟨fun _ => ⟨hno₂ rfl, hfun₂⟩, fun h => by simp [BinderMode.isUnique, BinderMode.usage] at h⟩,
                          fun ⟨h, _⟩ => by cases h⟩
                  · simp only [hltC, ↓reduceIte]
                    by_cases hgtC : vs.length > nP + fields.size
                    · simp only [hgtC, ↓reduceIte]
                      exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                    · simp only [hgtC, ↓reduceIte]
                      rcases construct_sound (P := P) (ext := ext) (B := b'') (r := r) (fields := fields)
                          (vs := vs.drop nP) (c := c) hst'' (fun i f v _ hv _ =>
                            let h := hvsProps v (List.mem_of_mem_drop (List.mem_of_getElem? hv))
                            ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) with hStC |
                        ⟨g, st₁, hcRun1, hr₁, hnr₁, hstat₁, hstr₁, hsz₁, hcap₁, hpres₁, _, honce₁, hssf₁,
                         hst₁, hbaseG, hnoG, hcfG, hfunG, hdouG, hreachG, _, _⟩
                      · rw [hStC]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                      · rw [hcRun1]; dsimp only
                        have hdouGRes : DeepOpenUnder st₁.heap st₁.regions (applyResultRegs st .shared .val fRegs aRegs) g := by
                          rw [hr₁]
                          refine hdouG st.regions _ fun i f v _ hv _ =>
                            (hvsProps v (List.mem_of_mem_drop (List.mem_of_getElem? hv))).2.2.2.2.1.mono fun x hx => by
                              simpa [applyResultRegs, show (Cls.val != Cls.val) = false from rfl] using hx
                        rcases conform_post_apply (res := .shared) (fRegs := fRegs) (aRegs := aRegs)
                            hst₁ hbaseG hcfG (fun _ => hnoG) hfunG (fun _ => hdouGRes) with hSt2 |
                          ⟨rv, st₂, hcRun2, hr₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂,
                           hst₂, hbv₂, hcls₂, hdou₂, hcf₂, hreach₂, hno₂, hfun₂, _⟩
                        · rw [hSt2]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                        · rw [hcRun2]
                          refine ⟨(fun _ h => by cases h), fun rv' st' B' hok => ?_⟩
                          cases hok
                          have hpresAll : PreservesLocs Frame st.heap st₂.heap :=
                            (hpres₁.mono hFlt).trans (hpres₂.mono fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁)
                          have hssfAll : StaticStrFresh st st₂ :=
                            StaticStrFresh.trans hsz₁ (hpres₂.mono fun _ hl => StOk_staticStrLoc_lt hst₁ hl) hssf₁ hssf₂
                          have hreachAll : ∀ l, Reach st₂.heap rv l →
                              st.heap.objs.size ≤ l ∨ Reach st.heap (.ref loc cap' t') l ∨ Reach st.heap a l ∨
                              StaticStrLoc st l ∨ NumLoc st₂.heap l := by
                            intro l hrl
                            rcases hreach₂ l hrl with hge1 | hrg
                            · exact Or.inl (Nat.le_trans hsz₁ hge1)
                            · rcases hreachG l hrg with hge0 | ⟨_, _, v, _, hv, _, hrv⟩
                              · exact Or.inl hge0
                              · rcases (hvsProps v (List.mem_of_mem_drop (List.mem_of_getElem? hv))).2.2.2.2.2 l hrv with hf' | ha'
                                · exact Or.inr (Or.inl hf')
                                · exact Or.inr (Or.inr (Or.inl ha'))
                          refine ⟨by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
                            hr₂.trans hr₁, by rw [hnr₂, hnr₁]; exact Nat.le_refl _,
                            by rw [hstat₂, hstat₁]; exact ArrayExtends.refl _,
                            by rw [hstr₂, hstr₁]; exact ArrayExtends.refl _,
                            hpresAll, honce₁.trans honce₂, hssfAll,
                            hbv₂, hcls₂, by rw [applyResultRegs_eq_of_regions hr₁] at hdou₂; exact hdou₂, hcf₂, hreachAll,
                            ⟨fun _ => ⟨hno₂ rfl, hfun₂⟩, fun h => by simp [BinderMode.isUnique, BinderMode.usage] at h⟩,
                            fun ⟨h, _⟩ => by cases h⟩

/-- `FunOkAt .unknown false False` for a runtime `.pap r out` cell of a primitive `P.find? r = some (.prim p)`. -/
theorem pap_prim_funOk {P : Prog} {ext : ExternOracle} {B B_call : Nat}
    {st₀ : St} {loc cap : Nat} {t₀ : List Nat} {r : Ref} {p : Prim} {out₀ : Array Val}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    (hB : B_call ≤ B + 1)
    (hfind : P.find? r = some (.prim p))
    (ho₀ : st₀.heap.objs[loc]? = some ⟨.pap r out₀, cap⟩)
    (hargs₀ : ∀ w ∈ out₀.toList,
      ValBaseOk st₀ w ∧ NoOnceCell st₀.heap w ∧ CtorFieldsOk P ext B_call st₀ w ∧
      FunOkAt P ext B_call st₀ .unknown false (fun _ => False) w) :
    FunOkAt P ext B_call st₀ .unknown false (fun _ => False) (.ref loc cap t₀) :=
  pap_default_funOk hidx hext hih.to_DefaultCallIH hB ho₀
    (fun d hd => by rw [hfind] at hd; cases hd; trivial) hargs₀

/-- Step `FullIH P ext B` → `PapsFunOk P ext (B + 1)` using `pap_iface_funOk`. -/
theorem FullIH_to_PapsFunOk {P : Prog} {ext : ExternOracle} {B : Nat}
    (hext : ExternOk P ext) (hih : FullIH P ext B) :
    PapsFunOk P ext (B + 1) := by
  intro st loc cap r args sk t hst hoPap hps hargs
  have hPapArgToNV : ∀ a, PapArgOk st.heap a → ValBaseOk st a → NonValSafe st.heap a := by
    intro a hpa hbv
    rcases hpa with ⟨i, rfl⟩ | ⟨loc', cap', o', n', rfl, ho', hnum'⟩
    · exact Or.inl ⟨i, rfl⟩
    · obtain ⟨o'', ho'', hcap''⟩ := hbv.1.self.1
      rw [ho'] at ho''; cases ho''
      exact Or.inr ⟨loc', cap', o', n', rfl, ho', hcap'', hnum'⟩
  have hApply : ∀ (d : RunDef) (ifc : Iface),
      P.find? r = some d → ifaceOf? d = some ifc →
      args.size < ifc.params.size →
      sk = ifaceSkel (ifc.params.toList.drop args.size) ifc.res ifc.resSkel →
      FunOkAt P ext (B + 1) st sk false (fun _ => False) (.ref loc cap t) := by
    intro d ifc hfind hifc hlt hskEq
    subst hskEq
    have hRes := pap_iface_funOk hext hih (B_call := B + 1) (st₀ := st) (loc := loc) (cap := cap)
      (t₀ := t) (r := r) (d := d) (ifc := ifc) (out₀ := args) (onceOnly := false)
      (pOnce := fun _ => false) (pFoot := fun _ _ => False)
      (Nat.le_refl _) hfind hifc hlt hoPap
      (fun i w₀ hw₀ =>
        let ⟨hpa, hbv⟩ := hargs w₀ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw₀))
        ⟨hbv, fun _ => (hPapArgToNV w₀ hpa hbv).noOnceCell⟩)
      (fun i p w₀ _ hw₀ _ =>
        let ⟨hpa, hbv⟩ := hargs w₀ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw₀))
        let hnv := hPapArgToNV w₀ hpa hbv
        ⟨fun _ => ⟨hnv.funOkAt P ext (B + 1) st p.skel, fun _ h => False.elim h, fun _ _ h => h⟩,
         fun _ => ⟨hnv.noOnceCell, rfl, hnv.funOkAt P ext (B + 1) st p.skel, fun _ _ h => h⟩,
         fun _ => ⟨hnv.ownTreeFull.1, fun _ => hnv.deepOpenUnder_nil,
           fun l hor => False.elim (hnv.ownTreeFull.2 l hor), fun _ h => False.elim h,
           fun _ l hor => hnv.ownTreeFull.2 l hor⟩,
         fun _ h => False.elim h⟩)
      (fun _ _ _ _ _ _ _ h => h)
      (fun i j _ _ wi _ _ _ hwi _ _ =>
        let ⟨hpa, hbv⟩ := hargs wi (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hwi))
        let hnv := hPapArgToNV wi hpa hbv
        ⟨fun _ l hor _ => hnv.ownTreeFull.2 l hor, fun _ _ _ h => False.elim h, fun _ _ _ _ h => False.elim h⟩)
    have hFootEq : (fun (l : Nat) => ∃ i, i < args.size ∧ False) = (fun _ => False) := by
      funext l; apply propext; simp
    simpa [hFootEq] using hRes
  unfold papSkel at hps
  cases hf : P.find? r with
  | none => rw [hf] at hps; cases hps
  | some d =>
    rw [hf] at hps
    cases d with
    | body ps res rc rs body =>
      simp only at hps
      by_cases hlt : args.size < ps.size
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at hps
        exact hApply _ ⟨ps, res, rc, rs⟩ hf rfl hlt hps.symm
      · simp only [hlt, ↓reduceIte] at hps; cases hps
    | extern ps res rc rs =>
      simp only at hps
      by_cases hlt : args.size < ps.size
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at hps
        exact hApply _ ⟨ps, res, rc, rs⟩ hf rfl hlt hps.symm
      · simp only [hlt, ↓reduceIte] at hps; cases hps
    | ind _ | ctor _ _ _ _ | caseDef _ | prim _ | stuck _ _ _ _ => cases hps

/-! ## 3. Higher-Order Application Bridges (`applyValue_bridge`, `applyAllS_bridge`) -/

private theorem applyResultRegs_sub_interp {st : St} {σ : AState} {I : Interp}
    {resM : ResultMode} {c : Cls} {fav aav res : AVal}
    (hIok : InterpOk σ st I)
    (hval : c = .val →
      (resM = .unique → res.own = .uniq ∧ (∀ x, x ∈ res.deps ↔ x ∈ fav.deps ∨ x ∈ aav.deps) ∧
        (∀ r, r ∈ res.regs ↔ r ∈ fav.regs)) ∧
      (resM = .uniqueBorrowed → res.own = .uniq ∧ (∀ x, x ∈ res.deps ↔ x ∈ fav.deps ∨ x ∈ aav.deps) ∧
        (∀ r, r ∈ res.regs ↔ r = σ.regions.headD 1 ∨ r ∈ fav.regs ∨ r ∈ aav.regs)) ∧
      (resM = .borrowed → res.own = .shared ∧ (∀ x, x ∈ res.deps ↔ x ∈ fav.deps ∨ x ∈ aav.deps) ∧
        (∀ r, r ∈ res.regs ↔ r = σ.regions.headD 1 ∨ r ∈ fav.regs ∨ r ∈ aav.regs)) ∧
      (resM = .shared → res.own = .shared ∧ (∀ x, x ∈ res.deps ↔ x ∈ fav.deps ∨ x ∈ aav.deps) ∧
        (∀ r, r ∈ res.regs ↔ r ∈ fav.regs ∨ r ∈ aav.regs)))
    {x : Nat}
    (hx : x ∈ applyResultRegs st resM c (I.regsOf fav.regs) (I.regsOf aav.regs)) :
    x ∈ I.regsOf res.regs := by
  by_cases hcv : c = .val
  · subst hcv
    obtain ⟨hu, hub, hb, hsh⟩ := hval rfl
    simp only [applyResultRegs, show (Cls.val != Cls.val) = false from rfl,
      Bool.false_eq_true, ↓reduceIte] at hx
    cases resM with
    | unique =>
      obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hx
      exact Interp.mem_regsOf.mpr ⟨r, (hu rfl).2.2 r |>.mpr hr, hxr⟩
    | uniqueBorrowed =>
      cases hsr : st.regions with
      | nil =>
        rw [hsr] at hx; simp only [List.mem_append] at hx
        rcases hx with hxA | hxF
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxA
          exact Interp.mem_regsOf.mpr ⟨r, (hub rfl).2.2 _ |>.mpr (Or.inr (Or.inr hr)), hxr⟩
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxF
          exact Interp.mem_regsOf.mpr ⟨r, (hub rfl).2.2 _ |>.mpr (Or.inr (Or.inl hr)), hxr⟩
      | cons c0 rest =>
        rw [hsr] at hx; simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with hx0 | hxA | hxF
        · rw [hx0]
          exact Interp.mem_regsOf.mpr ⟨σ.regions.headD 1, (hub rfl).2.2 _ |>.mpr (Or.inl rfl),
            hIok.2 c0 (by rw [hsr]; rfl)⟩
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxA
          exact Interp.mem_regsOf.mpr ⟨r, (hub rfl).2.2 _ |>.mpr (Or.inr (Or.inr hr)), hxr⟩
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxF
          exact Interp.mem_regsOf.mpr ⟨r, (hub rfl).2.2 _ |>.mpr (Or.inr (Or.inl hr)), hxr⟩
    | borrowed =>
      cases hsr : st.regions with
      | nil =>
        rw [hsr] at hx; simp only [List.mem_append] at hx
        rcases hx with hxA | hxF
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxA
          exact Interp.mem_regsOf.mpr ⟨r, (hb rfl).2.2 _ |>.mpr (Or.inr (Or.inr hr)), hxr⟩
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxF
          exact Interp.mem_regsOf.mpr ⟨r, (hb rfl).2.2 _ |>.mpr (Or.inr (Or.inl hr)), hxr⟩
      | cons c0 rest =>
        rw [hsr] at hx; simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with hx0 | hxA | hxF
        · rw [hx0]
          exact Interp.mem_regsOf.mpr ⟨σ.regions.headD 1, (hb rfl).2.2 _ |>.mpr (Or.inl rfl),
            hIok.2 c0 (by rw [hsr]; rfl)⟩
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxA
          exact Interp.mem_regsOf.mpr ⟨r, (hb rfl).2.2 _ |>.mpr (Or.inr (Or.inr hr)), hxr⟩
        · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxF
          exact Interp.mem_regsOf.mpr ⟨r, (hb rfl).2.2 _ |>.mpr (Or.inr (Or.inl hr)), hxr⟩
    | shared =>
      simp only [List.mem_append] at hx
      rcases hx with hxA | hxF
      · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxA
        exact Interp.mem_regsOf.mpr ⟨r, (hsh rfl).2.2 _ |>.mpr (Or.inr hr), hxr⟩
      · obtain ⟨r, hr, hxr⟩ := Interp.mem_regsOf.mp hxF
        exact Interp.mem_regsOf.mpr ⟨r, (hsh rfl).2.2 _ |>.mpr (Or.inl hr), hxr⟩
  · have hne : (c != .val) = true := by
      cases c with
      | val => exact absurd rfl hcv
      | irr | imm | leaf => rfl
    simp only [applyResultRegs, hne, ↓reduceIte] at hx
    cases hx

private theorem DeepOpenUnder_mono_in_regions {h : Heap} {rs A B : List Nat} {v : Val}
    (hsub : ∀ x ∈ rs, x ∈ A → x ∈ B) (hd : DeepOpenUnder h rs A v) :
    DeepOpenUnder h rs B v :=
  fun w hw r hrt hmem => hsub r hmem (hd w hw r hrt hmem)

private theorem isArrowSkel_to_mayBePap {sk : Skel} (h : isArrowSkel sk = true) :
    mayBePap sk = true := by
  cases sk with
  | arrow _ _ _ _ => rfl
  | unknown | data | dataApp _ => cases h

/-- Single higher-order application bridge: connects `Runs (applyValue fav aav c w) σ res σ'`
with `applyOneConformS P ext fuel fv av c` at budget `B_call`, preserving `Sim`, `Frame`,
`FrameExtra`, `EnvNoReachForbid`, and producing `VSim`, `ValEnvDisj`, `NoReachForbid` for `res`. -/
theorem applyValue_bridge {P : Prog} {ext : ExternOracle} {B_call fuel : Nat}
    {st : St} {Frame FrameExtra NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {fFoot aFoot : Nat → Prop}
    {fav aav res : AVal} {fv av : Val} {c : Cls} {w : String}
    (hrun : Runs (applyValue fav aav c w) σ res σ')
    (hsim : Sim P ext (B_call + 1) st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hst : StOk P ext B_call st)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hnk' : NoKillOk NoKill σ')
    (hnsp' : NoSpendOk NoSpend σ')
    (hfV : VSim P ext (B_call + 1) st Frame NoKill NoSpend σ I fFoot fav fv)
    (hfDisj : ValEnvDisj P st NoKill Scope env aenv σ envFoot fFoot fav fv)
    (hfNrf : ActiveVal σ fav → NoReachForbid st Forbid BadReg BadDep fav fv)
    (haV : VSim P ext (B_call + 1) st Frame NoKill NoSpend σ I aFoot aav av)
    (haDisj : ValEnvDisj P st NoKill Scope env aenv σ envFoot aFoot aav av)
    (haNrf : ActiveVal σ aav → NoReachForbid st Forbid BadReg BadDep aav av)
    (haNv : ValidDeps σ aav.deps → aav.cls ≠ .val → ValBaseOk st av ∧ NonValSafe st.heap av)
    (hfaUniq : ActiveVal σ aav → Transferable σ NoKill aav → ActiveVal σ fav →
      (∀ d, d ∈ aav.deps → ¬ (d ∈ fav.deps)) → ∀ l, OwnReach P st.heap av l → ¬ Reach st.heap fv l)
    (hfaFoot1 : ActiveVal σ fav → FootActive σ fav → ActiveVal σ aav →
      (fav.src = none ∨ fav.src ≠ aav.src) → ∀ l, fFoot l → ¬ Reach st.heap av l)
    (hfaFoot2 : ActiveVal σ aav → FootActive σ aav → ActiveVal σ fav →
      (aav.src = none ∨ aav.src ≠ fav.src) → ∀ l, aFoot l → ¬ Reach st.heap fv l)
    (hSrcOnce : ∀ x, fav.src = some x → aav.src = some x → fav.onceOnly = aav.onceOnly)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hExLt : ∀ l, FrameExtra l → l < st.heap.objs.size)
    (hExF : (fav.onceOnly = true ∨ IsOnceSrc σ fav) → ∀ l, fFoot l → ¬ FrameExtra l)
    (hExA : (destOf { mode := (arrowParts fav.skel).1, cls := aav.cls, skel := (arrowParts fav.skel).2.1 } (c != .val) = .once ∧
      (aav.onceOnly = true ∨ IsOnceSrc σ aav)) → ∀ l, aFoot l → ¬ FrameExtra l)
    (hExU : ((arrowParts fav.skel).1.isUnique = true ∧ aav.cls = .val) →
      ∀ l, OwnReach P st.heap av l → ¬ FrameExtra l) :
    (∀ k, (applyOneConformS P ext fuel fv av c).run (st, B_call) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (applyOneConformS P ext fuel fv av c).run (st, B_call) = .ok (rv, (st', B')) →
        ∃ (resFoot : Nat → Prop),
          B' ≤ B_call ∧ StOk P ext B' st' ∧
          st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
          st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
          ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
          PreservesLocs Frame st.heap st'.heap ∧
          PreservesLocs FrameExtra st.heap st'.heap ∧
          PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
          (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
          PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
          Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
          EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
          ValBaseOk st' rv ∧ ClsSafe st'.heap c rv ∧ CtorFieldsOk P ext B' st' rv ∧
          VSim P ext B' st' Frame NoKill NoSpend σ' I resFoot res rv ∧
          ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv ∧
          (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
          (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
          (∀ l, Reach st'.heap rv l →
            st.heap.objs.size ≤ l ∨ Reach st.heap fv l ∨ Reach st.heap av l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l) ∧
          (∀ l, resFoot l → ¬ FrameExtra l) ∧
          (Transferable σ' NoKill res → ∀ l, OwnReach P st'.heap rv l → ¬ FrameExtra l) := by
  have hok := hsim.2.1
  have hIok := hsim.2.2.1
  have hrunU := Runs_applyValue hok hrun
  rcases hap : arrowParts fav.skel with ⟨m_in, dom, resM, cod⟩
  rw [hap] at hrunU
  dsimp only at hrunU
  obtain ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hvdF, hunspF, hvdA, honceA, hnonOnceA,
    huniqA, honceSrcA, hrepUA, hclsR, hskelR, hsrcR, hooR, hvalR, hnonValR, hspPt, hstPt⟩ := hrunU
  let p : Param := { mode := m_in, cls := aav.cls, skel := dom }
  let d := destOf p (c != .val)
  have hactF : ActiveVal σ fav := ⟨hvdF, fun _ => hunspF⟩
  have hactA : ActiveVal σ aav := ⟨hvdA, fun his => by
    by_cases hdo : d = .once
    · exact (honceA hdo).2.1
    · exact False.elim ((hnonOnceA hdo).2.2 his)⟩
  obtain ⟨hfBase, hfOpen, hfCf, _, hfPlain, hfOO, hfOS, _⟩ := hfV.2.2.2.2 hactF
  obtain ⟨haBase, haOpen, haCf, _, haPlain, haOO, haOS, haTr⟩ := haV.2.2.2.2 hactA
  -- Helper: check `f` and `a` once/active status
  have hfSrcKilled : fav.onceOnly = true → ∀ x, fav.src = some x → σ'.st[x]? = some .dead := by
    intro hoo x hs
    have hlt := (hfV.2.2.1 x hs).1
    have h1 := hstPt x hlt
    simp only [hoo, hs, and_self, true_or, ↓reduceIte] at h1
    exact h1
  have hfOnceSpent : ∀ x ∈ fav.deps, σ.once[x]? = some true → σ'.spent[x]? = some true := by
    intro x hx ho
    have hlt : x < σ.spent.size := by have h1 := (hvdF x hx).1; have h2 := hok.2.1; omega
    have h1 := hspPt x hlt
    simp only [hx, true_or, ho, and_self, ↓reduceIte] at h1
    exact h1
  have haOnceSpent : ∀ x ∈ aav.deps, σ.once[x]? = some true → σ'.spent[x]? = some true := by
    intro x hx ho
    have hlt : x < σ.spent.size := by have h1 := (hvdA x hx).1; have h2 := hok.2.1; omega
    have h1 := hspPt x hlt
    simp only [hx, or_true, ho, and_self, ↓reduceIte] at h1
    exact h1
  have haSrcKilled : d = .once → aav.onceOnly = true → ∀ x, aav.src = some x → σ'.st[x]? = some .dead := by
    intro hdo hoo x hs
    have hlt := (haV.2.2.1 x hs).1
    have h1 := hstPt x hlt
    have hk : callKills (c != .val) { mode := m_in, cls := aav.cls, skel := dom } aav x := Or.inr ⟨hdo, hoo, hs⟩
    simp only [hk, or_true, ↓reduceIte] at h1
    exact h1
  have haUniqKilled : m_in.isUnique = true → aav.cls = .val → ∀ x ∈ aav.deps, σ'.st[x]? = some .dead := by
    intro hu hcv x hx
    obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (c != .val)).mpr hu
    have hlt := (hvdA x hx).1
    have h1 := hstPt x hlt
    have hk : callKills (c != .val) { mode := m_in, cls := aav.cls, skel := dom } aav x := Or.inl ⟨b, hdu, hcv, hx⟩
    simp only [hk, or_true, ↓reduceIte] at h1
    exact h1
  have haTrOfUniq : m_in.isUnique = true → aav.cls = .val → Transferable σ NoKill aav := by
    intro hu hcv
    obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (c != .val)).mpr hu
    have hneO : d ≠ .once := by dsimp only [d]; rw [hdu]; intro h; cases h
    obtain ⟨_, hooA, hnotOS⟩ := hnonOnceA hneO
    obtain ⟨hown, hlv, _, _⟩ := huniqA b hdu hcv
    refine ⟨hcv, hown, hooA, hnotOS, fun x hx => ⟨hlv x hx, fun hnk => hnk' x hnk (haUniqKilled hu hcv x hx)⟩⟩
  -- Build `fOnce`, `fFoot'`, `aOnce`, `aFoot'`, `FrameCall`
  classical
  let fIsOnce : Bool := fav.onceOnly || decide (IsOnceSrc σ fav)
  let fFoot' : Nat → Prop := if fIsOnce then fFoot else fun _ => False
  let aIsOnce : Bool := if m_in.usage == .once then (aav.onceOnly || decide (IsOnceSrc σ aav)) else false
  let aFoot' : Nat → Prop := if aIsOnce then aFoot else fun _ => False
  have hfFun : FunOkAt P ext (B_call + 1) st fav.skel fIsOnce fFoot' fv := by
    by_cases hfo : fav.onceOnly = true
    · have h1 : fIsOnce = true := by simp [fIsOnce, hfo]
      have h2 : fFoot' = fFoot := by funext l; simp [fFoot', h1]
      rw [h1, h2]; exact (hfOO hfo).2.2.2
    · by_cases hfs : IsOnceSrc σ fav
      · have h1 : fIsOnce = true := by simp [fIsOnce, hfs]
        have h2 : fFoot' = fFoot := by funext l; simp [fFoot', h1]
        rw [h1, h2]; exact (hfOS hfs).2.2
      · have h1 : fIsOnce = false := by
          have hbf : fav.onceOnly = false := Bool.eq_false_iff.mpr hfo
          simp [fIsOnce, hbf, hfs]
        have h2 : fFoot' = fun _ => False := by funext l; simp [fFoot', h1]
        rw [h1, h2]; exact (hfPlain ⟨hfs, Bool.eq_false_iff.mpr hfo⟩).2.2
  let FrameCall : Nat → Prop := fun l =>
    Frame l ∨ FrameExtra l ∨ NumLoc st.heap l ∨
    (∃ (i : Nat) (b : Bnd) (ab : ABnd), Scope i ∧ env[i]? = some b ∧ aenv[i]? = some ab ∧
      ab.mode ≠ .erased ∧ ActiveVal σ' (effVal ab) ∧ Reach st.heap b.val l)
  have hFCallLt : ∀ l, FrameCall l → l < st.heap.objs.size := by
    intro l hfc
    rcases hfc with hF | hEx | ⟨o, n, ho, _⟩ | ⟨i, b, ab, hsc, hbi, habi, hne, ha', hr⟩
    · exact hFlt l hF
    · exact hExLt l hEx
    · exact (Array.getElem?_eq_some_iff.mp ho).1
    · have hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
      have ha0 := ActiveVal.of_AStateLe hok hle' hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) ha'
      exact (hvB.2.2.2.2 ha0).1.1.reach_lt_size hr
  have hfFootNoFrameCall : ∀ l, FrameCall l → ¬ fFoot' l := by
    intro l hfc hfl
    have hfIsT : fIsOnce = true := by
      cases h1 : fIsOnce with
      | true => rfl
      | false => simp [fFoot', h1] at hfl
    have hfl0 : fFoot l := by simpa [fFoot', hfIsT] using hfl
    have hdisjF : fav.onceOnly = true ∨ IsOnceSrc σ fav := by
      simp only [fIsOnce, Bool.or_eq_true, decide_eq_true_eq] at hfIsT; exact hfIsT
    have hftActF : FootActive σ fav := by
      rcases hdisjF with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨h2, hunspF⟩
    rcases hfc with hF | hEx | hNum | ⟨i, b, ab, hsc, hbi, habi, hne, ha', hr⟩
    · rcases hdisjF with hoo | his
      · exact (hfOO hoo).2.1 (fun x hs hnk => hnk' x hnk (hfSrcKilled hoo x hs)) l hfl0 hF
      · exact (hfOS his).2.1 (fun d hd ho hns => hnsp' d hns (hfOnceSpent d hd ho)) l hfl0 hF
    · exact hExF hdisjF l hfl0 hEx
    · rcases hdisjF with hoo | his
      · exact ((hfOO hoo).1 l hfl0).2.2 hNum
      · exact ((hfOS his).1 l hfl0).2.2 hNum
    · have hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
      have ha0 := ActiveVal.of_AStateLe hok hle' hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) ha'
      have hneSrc : fav.src ≠ some ab.id := by
        intro hsrc
        have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
        rcases hdisjF with hoo | ⟨id, hs, ho⟩
        · exact (ha'.1 ab.id habMem).2 (hfSrcKilled hoo ab.id hsrc)
        · rw [hsrc] at hs; cases hs
          have hsp := hfOnceSpent ab.id (hfV.2.2.1 ab.id hsrc).2 ho
          have his' : IsOnceSrc σ' (effVal ab) := ⟨ab.id, rfl, by rw [honce]; exact ho⟩
          have hspF := ha'.2 his' ab.id habMem (by rw [honce]; exact ho)
          rw [hsp] at hspF; cases hspF
      exact (hfDisj i b ab hsc hbi habi hne).2.2.1 hactF hftActF ha0 hneSrc l hfl0 hr
  have haFootNoFrameCall : ∀ l, FrameCall l → ¬ aFoot' l := by
    intro l hfc hfl
    have haIsT : aIsOnce = true := by
      cases h1 : aIsOnce with
      | true => rfl
      | false => simp [aFoot', h1] at hfl
    have hfl0 : aFoot l := by simpa [aFoot', haIsT] using hfl
    have ⟨hmuO, hdisjA⟩ : m_in.usage = .once ∧ (aav.onceOnly = true ∨ IsOnceSrc σ aav) := by
      dsimp only [aIsOnce] at haIsT
      cases hm : (m_in.usage == .once) with
      | false => simp [hm] at haIsT
      | true =>
        simp only [hm, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at haIsT
        exact ⟨by simpa using hm, haIsT⟩
    have hdo : d = .once := (destOf_once_iff p (c != .val)).mpr hmuO
    have hftActA : FootActive σ aav := by
      rcases hdisjA with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨h2, (honceA hdo).2.1⟩
    rcases hfc with hF | hEx | hNum | ⟨i, b, ab, hsc, hbi, habi, hne, ha', hr⟩
    · rcases hdisjA with hoo | his
      · exact (haOO hoo).2.1 (fun x hs hnk => hnk' x hnk (haSrcKilled hdo hoo x hs)) l hfl0 hF
      · exact (haOS his).2.1 (fun x hx ho hns => hnsp' x hns (haOnceSpent x hx ho)) l hfl0 hF
    · exact hExA ⟨by simpa [hap, d, p] using hdo, hdisjA⟩ l hfl0 hEx
    · rcases hdisjA with hoo | his
      · exact ((haOO hoo).1 l hfl0).2.2 hNum
      · exact ((haOS his).1 l hfl0).2.2 hNum
    · have hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
      have ha0 := ActiveVal.of_AStateLe hok hle' hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) ha'
      have hneSrc : aav.src ≠ some ab.id := by
        intro hsrc
        have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
        rcases hdisjA with hoo | ⟨id, hs, ho⟩
        · exact (ha'.1 ab.id habMem).2 (haSrcKilled hdo hoo ab.id hsrc)
        · rw [hsrc] at hs; cases hs
          have hsp := haOnceSpent ab.id (haV.2.2.1 ab.id hsrc).2 ho
          have his' : IsOnceSrc σ' (effVal ab) := ⟨ab.id, rfl, by rw [honce]; exact ho⟩
          have hspF := ha'.2 his' ab.id habMem (by rw [honce]; exact ho)
          rw [hsp] at hspF; cases hspF
      exact (haDisj i b ab hsc hbi habi hne).2.2.1 hactA hftActA ha0 hneSrc l hfl0 hr
  -- Disjointness between `fFoot'` and `a` (and `aFoot'` and `f`, and `fFoot'` and `aFoot'`)
  have hneSrcOfFootF : fIsOnce = true → fav.src = none ∨ fav.src ≠ aav.src := by
    intro hfIsT
    cases hfs : fav.src with
    | none => exact Or.inl rfl
    | some x =>
      right; intro hEq
      have has : aav.src = some x := hEq.symm
      have hxF : x ∈ fav.deps := (hfV.2.2.1 x hfs).2
      have hxA : x ∈ aav.deps := (haV.2.2.1 x has).2
      have hdisjF : fav.onceOnly = true ∨ IsOnceSrc σ fav := by
        simp only [fIsOnce, Bool.or_eq_true, decide_eq_true_eq] at hfIsT; exact hfIsT
      rcases hdisjF with hooF | ⟨id, hs, ho⟩
      · have hooA : aav.onceOnly = true := (hSrcOnce x hfs has).symm.trans hooF
        by_cases hdo : d = .once
        · exact honceSrcA hdo hooA x has hxF
        · rw [(hnonOnceA hdo).2.1] at hooA; cases hooA
      · rw [hfs] at hs; cases hs
        by_cases hdo : d = .once
        · exact (honceA hdo).2.2 x hxA ho hxF
        · exact (hnonOnceA hdo).2.2 ⟨x, has, ho⟩
  have hneSrcOfFootA : aIsOnce = true → aav.src = none ∨ aav.src ≠ fav.src := by
    intro haIsT
    cases has : aav.src with
    | none => exact Or.inl rfl
    | some x =>
      right; intro hEq
      have hfs : fav.src = some x := hEq.symm
      have hxF : x ∈ fav.deps := (hfV.2.2.1 x hfs).2
      have hxA : x ∈ aav.deps := (haV.2.2.1 x has).2
      have ⟨hmuO, hdisjA⟩ : m_in.usage = .once ∧ (aav.onceOnly = true ∨ IsOnceSrc σ aav) := by
        dsimp only [aIsOnce] at haIsT
        cases hm : (m_in.usage == .once) with
        | false => simp [hm] at haIsT
        | true =>
          simp only [hm, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at haIsT
          exact ⟨by simpa using hm, haIsT⟩
      have hdo : d = .once := (destOf_once_iff p (c != .val)).mpr hmuO
      rcases hdisjA with hooA | ⟨id, hs, ho⟩
      · exact honceSrcA hdo hooA x has hxF
      · rw [has] at hs; cases hs
        exact (honceA hdo).2.2 x hxA ho hxF
  have haFootReach : ∀ l, aFoot' l → Reach st.heap av l ∧ ¬ NumLoc st.heap l := by
    intro l hfl
    have haIsT : aIsOnce = true := by
      cases h1 : aIsOnce with | true => rfl | false => simp [aFoot', h1] at hfl
    have hfl0 : aFoot l := by simpa [aFoot', haIsT] using hfl
    have hdisjA : aav.onceOnly = true ∨ IsOnceSrc σ aav := by
      dsimp only [aIsOnce] at haIsT
      cases hm : (m_in.usage == .once) with
      | false => simp [hm] at haIsT
      | true => simp only [hm, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at haIsT; exact haIsT
    rcases hdisjA with hooA | hisA
    · exact ⟨((haOO hooA).1 l hfl0).1, ((haOO hooA).1 l hfl0).2.2⟩
    · exact ⟨((haOS hisA).1 l hfl0).1, ((haOS hisA).1 l hfl0).2.2⟩
  have hfFootReach : ∀ l, fFoot' l → Reach st.heap fv l := by
    intro l hfl
    have hfIsT : fIsOnce = true := by
      cases h1 : fIsOnce with | true => rfl | false => simp [fFoot', h1] at hfl
    have hfl0 : fFoot l := by simpa [fFoot', hfIsT] using hfl
    have hdisjF : fav.onceOnly = true ∨ IsOnceSrc σ fav := by
      simp only [fIsOnce, Bool.or_eq_true, decide_eq_true_eq] at hfIsT; exact hfIsT
    rcases hdisjF with hooF | hisF
    · exact ((hfOO hooF).1 l hfl0).1
    · exact ((hfOS hisF).1 l hfl0).1
  have hfaDisj : ∀ l, Reach st.heap fv l → ¬ aFoot' l := by
    intro l hrf hfl
    have haIsT : aIsOnce = true := by
      cases h1 : aIsOnce with | true => rfl | false => simp [aFoot', h1] at hfl
    have hfl0 : aFoot l := by simpa [aFoot', haIsT] using hfl
    have ⟨hmuO, hdisjA⟩ : m_in.usage = .once ∧ (aav.onceOnly = true ∨ IsOnceSrc σ aav) := by
      dsimp only [aIsOnce] at haIsT
      cases hm : (m_in.usage == .once) with
      | false => simp [hm] at haIsT
      | true =>
        simp only [hm, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at haIsT
        exact ⟨by simpa using hm, haIsT⟩
    have hdo : d = .once := (destOf_once_iff p (c != .val)).mpr hmuO
    have hftActA : FootActive σ aav := by
      rcases hdisjA with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨h2, (honceA hdo).2.1⟩
    exact hfaFoot2 hactA hftActA hactF (hneSrcOfFootA haIsT) l hfl0 hrf
  have hafDisj : ∀ l, Reach st.heap av l → ¬ fFoot' l := by
    intro l hra hfl
    have hfIsT : fIsOnce = true := by
      cases h1 : fIsOnce with | true => rfl | false => simp [fFoot', h1] at hfl
    have hfl0 : fFoot l := by simpa [fFoot', hfIsT] using hfl
    have hdisjF : fav.onceOnly = true ∨ IsOnceSrc σ fav := by
      simp only [fIsOnce, Bool.or_eq_true, decide_eq_true_eq] at hfIsT; exact hfIsT
    have hftActF : FootActive σ fav := by
      rcases hdisjF with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨h2, hunspF⟩
    exact hfaFoot1 hactF hftActF hactA (hneSrcOfFootF hfIsT) l hfl0 hra
  -- Invoke `FunOkAt` on `fv`!
  rw [FunOkAt] at hfFun
  rw [hap] at hfFun
  dsimp only at hfFun
  obtain ⟨hnoViol, hokRun⟩ := hfFun B_call fuel st fv av c FrameCall (I.regsOf fav.regs) (I.regsOf aav.regs)
    aIsOnce aFoot' (Nat.le_refl _) hst (fun l hss => Or.inl (hstat l hss)) hFCallLt
    (SameLoc.refl _) (SameShapeOn.refl _ _) (RegsFuture.refl _)
    hfBase hfOpen (CtorFieldsOk_mono (by omega) hfCf)
    haBase haOpen (CtorFieldsOk_mono (by omega) haCf)
    hfFootNoFrameCall haFootNoFrameCall
    (fun l hff haf => hfaDisj l (hfFootReach l hff) haf)
    hfaDisj hafDisj
    ⟨haFootReach, fun hme => by
      have hneO : d ≠ .once := by
        dsimp only [d, p]; rw [hme]; unfold destOf; cases (c != .val) <;> simp
      have ⟨_, hooA, hnotOS⟩ := hnonOnceA hneO
      exact (haPlain ⟨hnotOS, hooA⟩).1⟩
    (fun hneEr => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hmuO
        have hdo : d = .once := (destOf_once_iff p (c != .val)).mpr hmuO
        have hadm : aav.skel.admitsNA dom = true := Skel.admitsNA_symm dom aav.skel ▸ (honceA hdo).1
        have hEqO : aIsOnce = (aav.onceOnly || decide (IsOnceSrc σ aav)) := by
          simp [aIsOnce, hmuO]
        by_cases hao : aav.onceOnly = true
        · have haT : aIsOnce = true := by rw [hEqO, hao]; rfl
          have hftEq : aFoot' = aFoot := by funext l; simp [aFoot', haT]
          rw [haT, hftEq]
          exact FunOkAt_mono (by omega) (FunOkAt_of_admitsNA hadm (haOO hao).2.2.2)
        · by_cases has : IsOnceSrc σ aav
          · have haT : aIsOnce = true := by rw [hEqO]; simp [has]
            have hftEq : aFoot' = aFoot := by funext l; simp [aFoot', haT]
            rw [haT, hftEq]
            exact FunOkAt_mono (by omega) (FunOkAt_of_admitsNA hadm (haOS has).2.2)
          · have haF : aIsOnce = false := by
              rw [hEqO, Bool.eq_false_iff.mpr hao]; simp [has]
            have hftEq : aFoot' = fun _ => False := by funext l; simp [aFoot', haF]
            rw [haF, hftEq]
            exact FunOkAt_mono (by omega) (FunOkAt_of_admitsNA hadm (haPlain ⟨has, Bool.eq_false_iff.mpr hao⟩).2.2)
      · intro hnuO
        have hneO : d ≠ .once := fun h => hnuO ((destOf_once_iff p (c != .val)).mp h)
        obtain ⟨hadm0, hooA, hnotOS⟩ := hnonOnceA hneO
        have hadm : aav.skel.admits dom = true := Skel.admits_symm dom aav.skel ▸ hadm0
        have haF : aIsOnce = false := by
          have hbf : (m_in.usage == .once) = false := beq_false_of_ne hnuO
          simp [aIsOnce, hbf]
        have hftF : ∀ l, ¬ aFoot' l := fun l h => by simp [aFoot', haF] at h
        obtain ⟨hnoA, _, hfunA⟩ := haPlain ⟨hnotOS, hooA⟩
        exact ⟨hnoA, haF, hftF, FunOkAt_mono (by omega) (FunOkAt_of_admits hadm hfunA)⟩
      · intro hu
        by_cases hcv : aav.cls = .val
        · have htrA := haTrOfUniq hu hcv
          obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (c != .val)).mpr hu
          obtain ⟨_, _, hnb, hdisjFA⟩ := huniqA b hdu hcv
          obtain ⟨htrOwn, hownF⟩ := haTr htrA
          refine ⟨htrOwn, fun l hor => ⟨?_, hfaUniq hactA htrA hactF hdisjFA l hor⟩, fun hnbM => ?_⟩
          · intro hfc
            rcases hfc with hF | hEx | hNum | ⟨i, b', ab, hsc, hbi, habi, hne, ha', hr⟩
            · exact (hownF l hor).1 hF
            · exact hExU ⟨by simpa [hap] using hu, hcv⟩ l hor hEx
            · exact OwnReach_not_numLoc hor hNum
            · have hvB := ((hsim.2.2.2.2.2.1 i b' ab hsc hbi habi).2 hne).2
              have ha0 := ActiveVal.of_AStateLe hok hle' hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) ha'
              have hdd : ∀ x, x ∈ aav.deps → ¬ (x ∈ (effVal ab).deps) := fun x hx hxb =>
                (ha'.1 x hxb).2 (haUniqKilled hu hcv x hx)
              exact (haDisj i b' ab hsc hbi habi hne).1 hactA htrA ha0 hdd l hor hr
          · have hbf : b = false := by
              dsimp only [d, p] at hdu
              cases hm : m_in <;> rw [hm] at hu hnbM hdu <;>
                simp [destOf, BinderMode.isUnique, BinderMode.isBorrowed] at hu hnbM hdu
              exact hdu
            have hregNil := hnb hbf
            simpa [hregNil, Interp.regsOf_nil] using haOpen
        · obtain ⟨_, hnv⟩ := haNv hvdA hcv
          exact ⟨hnv.ownTreeFull.1, fun l hor => False.elim (hnv.ownTreeFull.2 l hor), fun _ => hnv.deepOpenUnder_nil⟩
      · rintro ⟨hru, hcv, hmOr⟩
        by_cases haVal : aav.cls = .val
        · have hneLeaf : aav.cls ≠ .leaf := by rw [haVal]; decide
          have hdSO : d = .share ∨ d = .once := by
            dsimp only [d, p]
            have hcf : (c != .val) = false := by rw [hcv]; rfl
            rw [hcf]
            rcases hmOr with rfl | rfl
            · left; rfl
            · right; rfl
          have hregNil := hrepUA hru hcv hneLeaf hdSO
          simpa [hregNil, Interp.regsOf_nil] using haOpen
        · exact (haNv hvdA haVal).2.deepOpenUnder_nil)
  refine ⟨hnoViol, fun rv st' B' hokRunEq => ?_⟩
  obtain ⟨hB', hst', hsz', hcap', hr', hnr', hstat', hstr', hpresCall, honce', hssf',
    hbv', hcls', hdou', hcf', hreach', hresOncePost, huniqPost⟩ := hokRun rv st' B' hokRunEq
  have hpresF : PreservesLocs Frame st.heap st'.heap := hpresCall.mono fun _ h => Or.inl h
  have hpresEx : PreservesLocs FrameExtra st.heap st'.heap := hpresCall.mono fun _ h => Or.inr (Or.inl h)
  have hpresNum : ∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o :=
    fun l o n ho hc => (hpresCall l (Or.inr (Or.inr (Or.inl ⟨o, n, ho, hc⟩)))).trans ho
  have hpresEnv : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap :=
    fun i b ab hsc hbi habi hne ha' =>
      hpresCall.mono fun l hr => Or.inr (Or.inr (Or.inr ⟨i, b, ab, hsc, hbi, habi, hne, ha', hr⟩))
  have hpresSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
    hpresF.mono fun l hss => hstat l hss
  have hrf' : RegsFuture st st' := RegsFuture.same_regions hnr' hr'
  have hIok' : InterpOk σ' st' I :=
    ⟨fun r hr c hc => Nat.lt_of_lt_of_le (hIok.1 r (hnr ▸ hr) c hc) hnr',
     fun c hc => by rw [hr'] at hc; rw [hreg]; exact hIok.2 c hc⟩
  have hsim' : Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
    Sim_step (by omega) hle' hok' hIok' hrf' honce' hssf' (fun _ _ _ h => h) hpresEnv hsim
  have hEnvNrf' : EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep :=
    EnvNoReachForbid_step hok hle' (Sim_deps_lt hsim) hsim.2.2.2.1 hstat' hstr' hpresSS hpresEnv hEnvNrf
  -- Pick `resFoot` cleanly, handling Gap C (`.ctor` cells always get `fun _ => False`)
  let resOnceRun : Bool := isArrowSkel cod && (fIsOnce || m_in.isUnique || m_in.usage == .once)
  have hresOnceImp : c = .val → resOnceRun = true → res.onceOnly = true := by
    intro hcv hrt
    rw [hooR]
    simp only [resOnceRun, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrt
    refine ⟨hcv, isArrowSkel_to_mayBePap hrt.1, ?_⟩
    rcases hrt.2 with (hf1 | hu) | ho
    · simp only [fIsOnce, Bool.or_eq_true, decide_eq_true_eq] at hf1
      rcases hf1 with hoo | ⟨id, hs, ho⟩
      · exact Or.inl hoo
      · exact Or.inr (Or.inl ⟨id, (hfV.2.2.1 id hs).2, ho⟩)
    · exact Or.inr (Or.inr (Or.inl hu))
    · exact Or.inr (Or.inr (Or.inr ho))
  have hFootBuild : ∃ resFoot : Nat → Prop,
      (res.onceOnly = false → NoOnceCell st'.heap rv ∧ (∀ l, ¬ resFoot l) ∧
        FunOkAt P ext B' st' cod false (fun _ => False) rv) ∧
      (res.onceOnly = true →
        (∀ l, resFoot l → Reach st'.heap rv l ∧ ¬ FrameCall l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l) ∧
        (∀ loc cap t o r fs, rv = .ref loc cap t → st'.heap.objs[loc]? = some o → o.cell = .ctor r fs →
          ∀ l, ¬ resFoot l) ∧
        FunOkAt P ext B' st' cod true resFoot rv) ∧
      (∀ l, resFoot l → ¬ FrameCall l) := by
    by_cases hcv : c = .val
    · cases hro : res.onceOnly with
      | false =>
        have hrunF : resOnceRun = false := by
          cases h1 : resOnceRun with
          | false => rfl
          | true => have h2 := hresOnceImp hcv h1; rw [hro] at h2; cases h2
        obtain ⟨hnoR, hfunR⟩ := hresOncePost.1 hrunF
        exact ⟨fun _ => False, (fun _ => ⟨hnoR, fun _ h => h, hfunR⟩), (fun h => by cases h), (fun _ h => False.elim h)⟩
      | true =>
        cases h1 : resOnceRun with
        | false =>
          obtain ⟨_, hfunR⟩ := hresOncePost.1 h1
          exact ⟨fun _ => False, (fun h => by cases h),
            (fun _ => ⟨fun _ h => False.elim h, fun _ _ _ _ _ _ _ _ _ _ h => h, FunOkAt_weaken_onceOnly hfunR⟩),
            (fun _ h => False.elim h)⟩
        | true =>
          obtain ⟨rf0, hrf0B, hfunR⟩ := hresOncePost.2 h1
          by_cases hCtor : ∃ loc cap t o r fs, rv = .ref loc cap t ∧ st'.heap.objs[loc]? = some o ∧ o.cell = .ctor r fs
          · obtain ⟨loc, cap, t, o, r, fs, hrvEq, hoEq, hcEq⟩ := hCtor
            have hfunCtor : FunOkAt P ext B' st' cod true (fun _ => False) rv := by
              rw [hrvEq]
              exact FunOkAt_weaken_onceOnly (FunOkAt_nonCallable_ref P ext B' st' cod hoEq (by rw [hcEq]; trivial))
            exact ⟨fun _ => False, (fun h => by cases h),
              (fun _ => ⟨fun _ h => False.elim h, fun _ _ _ _ _ _ _ _ _ _ h => h, hfunCtor⟩),
              (fun _ h => False.elim h)⟩
          · exact ⟨rf0, (fun h => by cases h),
              (fun _ => ⟨hrf0B, fun loc cap t o r fs h1 h2 h3 _ _ => hCtor ⟨loc, cap, t, o, r, fs, h1, h2, h3⟩, hfunR⟩),
              (fun l hl => (hrf0B l hl).2.1)⟩
    · have hnv := hcls'.to_nonValSafe hcv hbv'.1.self.1
      have hroF : res.onceOnly = false := by
        cases h1 : res.onceOnly with
        | false => rfl
        | true => exact absurd (hooR.mp h1).1 hcv
      exact ⟨fun _ => False,
        (fun _ => ⟨hnv.noOnceCell, fun _ h => h, hnv.funOkAt P ext B' st' cod⟩),
        (fun h => by rw [hroF] at h; cases h),
        (fun _ h => False.elim h)⟩
  obtain ⟨resFoot, hrfFalse, hrfTrue, hrfNoCall⟩ := hFootBuild
  -- Prove `VSim` for `res`
  have hregsBnd : ∀ r ∈ res.regs, r < σ'.nextRegion := by
    rw [hnr]
    intro r hr
    by_cases hcv : c = .val
    · obtain ⟨hu, hub, hb, hsh⟩ := hvalR hcv
      have hheadLt : σ.regions.headD 1 < σ.nextRegion := by
        cases hsr : σ.regions with
        | nil => have := hok.2.2.1; simp only [List.headD_nil]; omega
        | cons r0 rest => exact (hok.2.2.2.2.2 r0 (by rw [hsr]; exact List.mem_cons_self ..)).2
      cases resM with
      | unique => exact hfV.1 r ((hu rfl).2.2 r |>.mp hr)
      | uniqueBorrowed =>
        rcases (hub rfl).2.2 r |>.mp hr with rfl | hrf | hra
        · exact hheadLt
        · exact hfV.1 r hrf
        · exact haV.1 r hra
      | borrowed =>
        rcases (hb rfl).2.2 r |>.mp hr with rfl | hrf | hra
        · exact hheadLt
        · exact hfV.1 r hrf
        · exact haV.1 r hra
      | shared =>
        rcases (hsh rfl).2.2 r |>.mp hr with hrf | hra
        · exact hfV.1 r hrf
        · exact haV.1 r hra
    · rw [(hnonValR hcv).2] at hr; cases hr
  have hdepsBnd : ∀ x ∈ res.deps, x < σ'.st.size := by
    rw [hszSt]
    intro x hx
    by_cases hcv : c = .val
    · obtain ⟨hu, hub, hb, hsh⟩ := hvalR hcv
      have hdisj : x ∈ fav.deps ∨ x ∈ aav.deps := by
        cases resM with
        | unique => exact (hu rfl).2.1 x |>.mp hx
        | uniqueBorrowed => exact (hub rfl).2.1 x |>.mp hx
        | borrowed => exact (hb rfl).2.1 x |>.mp hx
        | shared => exact (hsh rfl).2.1 x |>.mp hx
      rcases hdisj with hf | ha
      · exact hfV.2.1 x hf
      · exact haV.2.1 x ha
    · rw [(hnonValR hcv).1] at hx; cases hx
  have hresUniqImp : res.cls = .val → res.own = .uniq → resM.isUnique = true ∧ c = .val := by
    intro hcvR hownR
    have hcv : c = .val := hclsR ▸ hcvR
    obtain ⟨hu, hub, hb, hsh⟩ := hvalR hcv
    cases resM with
    | unique | uniqueBorrowed => exact ⟨rfl, hcv⟩
    | borrowed => rw [(hb rfl).1] at hownR; cases hownR
    | shared => rw [(hsh rfl).1] at hownR; cases hownR
  have hVSimRes : VSim P ext B' st' Frame NoKill NoSpend σ' I resFoot res rv := by
    refine ⟨hregsBnd, hdepsBnd, (fun _ hs => by rw [hsrcR] at hs; cases hs),
      (fun _ ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs), fun _ => ?_⟩
    have hdouI : DeepOpenUnder st'.heap st'.regions (I.regsOf res.regs) rv :=
      hdou'.mono fun x hx => applyResultRegs_sub_interp hIok hvalR hx
    refine ⟨hbv', hdouI, hcf',
      (fun _ hne => hcls'.to_nonValSafe (hclsR ▸ hne) hbv'.1.self.1),
      (fun ⟨_, hroF⟩ => by rw [hskelR]; exact hrfFalse hroF),
      (fun hroT => ?_),
      (fun ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs),
      (fun htr => ?_)⟩
    · obtain ⟨hb, hct, hfun⟩ := hrfTrue hroT
      rw [hskelR]
      exact ⟨fun l hl => let h := hb l hl; ⟨h.1, h.2.2.1, h.2.2.2⟩,
        fun _ l hl hF => (hb l hl).2.1 (Or.inl hF), hct, hfun⟩
    · obtain ⟨htrOwn, hownB, _⟩ := huniqPost (hresUniqImp htr.1 htr.2.1)
      exact ⟨htrOwn, fun l hor => ⟨fun hF => (hownB l hor).1 (Or.inl hF), (hownB l hor).2⟩⟩
  -- Prove `ValEnvDisj` for `res`
  have hdepsOfVal : c = .val → ∀ x, x ∈ res.deps ↔ x ∈ fav.deps ∨ x ∈ aav.deps := by
    intro hcv x
    obtain ⟨hu, hub, hb, hsh⟩ := hvalR hcv
    cases resM with
    | unique => exact (hu rfl).2.1 x
    | uniqueBorrowed => exact (hub rfl).2.1 x
    | borrowed => exact (hb rfl).2.1 x
    | shared => exact (hsh rfl).2.1 x
  have hDisjRes : ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv := by
    intro i b ab hsc hbi habi hne
    have hvB := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
    have hsrcB : ∀ x, (effVal ab).src = some x → x < σ.st.size := fun x hx => (hvB.2.2.1 x hx).1
    refine ⟨?_, ?_, ?_, ?_, (fun _ _ hs => by rw [hsrcR] at hs; cases hs),
      (fun hs => by rw [hsrcR] at hs; cases hs), (fun _ hs => by rw [hsrcR] at hs; cases hs)⟩
    · intro _ htrR haB' _ l hor hrB'
      have hpB := hpresEnv i b ab hsc hbi habi hne haB'
      have hrB := (Reach_congr hpB l).mp hrB'
      exact ((huniqPost (hresUniqImp htrR.1 htrR.2.1)).2.1 l hor).1
        (Or.inr (Or.inr (Or.inr ⟨i, b, ab, hsc, hbi, habi, hne, haB', hrB⟩)))
    · intro haB' htrB' _ hdd l horB' hrR'
      have haB0 := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
      have htrB0 := Transferable.of_AStateLe hok hle' hvB.2.1 hsrcB (fun _ h => h) htrB'
      have hpB := hpresEnv i b ab hsc hbi habi hne haB'
      have horB := (OwnReach_congr hpB l).mp horB'
      have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB0).1.1.reach_lt_size (OwnReach_toReach horB)
      have hnotSS : ¬ StaticStrLoc st l := ((hvB.2.2.2.2 haB0).2.2.2.2.2.2.2 htrB0).2 l horB |>.2
      have hnotNum : ¬ NumLoc st'.heap l := OwnReach_not_numLoc horB'
      rcases hreach' l hrR' with hge | hrf | hra | hss | hnum
      · omega
      · by_cases hcv : c = .val
        · exact (hfDisj i b ab hsc hbi habi hne).2.1 haB0 htrB0 hactF
            (fun d hd hdf => hdd d hd ((hdepsOfVal hcv d).mpr (Or.inl hdf))) l horB hrf
        · exact hnotNum ((hcls'.to_nonValSafe hcv hbv'.1.self.1).reach_numLoc hrR')
      · by_cases hcv : c = .val
        · exact (haDisj i b ab hsc hbi habi hne).2.1 haB0 htrB0 hactA
            (fun d hd hda => hdd d hd ((hdepsOfVal hcv d).mpr (Or.inr hda))) l horB hra
        · exact hnotNum ((hcls'.to_nonValSafe hcv hbv'.1.self.1).reach_numLoc hrR')
      · exact hnotSS hss
      · exact hnotNum hnum
    · intro _ _ haB' _ l hfl hrB'
      have hpB := hpresEnv i b ab hsc hbi habi hne haB'
      have hrB := (Reach_congr hpB l).mp hrB'
      exact hrfNoCall l hfl (Or.inr (Or.inr (Or.inr ⟨i, b, ab, hsc, hbi, habi, hne, haB', hrB⟩)))
    · intro haB' hftB' _ _ l hfl hrR'
      have haB0 := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
      have hftB0 := FootActive.of_AStateLe hok hle' hvB.2.1 hsrcB hftB'
      have hpB := hpresEnv i b ab hsc hbi habi hne haB'
      have ⟨hrB, hnotSS, hnotNum0⟩ : Reach st.heap b.val l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
        rcases hftB0 with hooB | ⟨hisB, _⟩
        · exact ((hvB.2.2.2.2 haB0).2.2.2.2.2.1 hooB).1 l hfl
        · exact ((hvB.2.2.2.2 haB0).2.2.2.2.2.2.1 hisB).1 l hfl
      have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB0).1.1.reach_lt_size hrB
      have hnotNum' : ¬ NumLoc st'.heap l := fun hn => hnotNum0 ((NumLoc_congr hpB hrB).mpr hn)
      have hneSrcF : fav.src ≠ some ab.id := by
        intro hsrc
        have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
        rcases hftB' with hooB | ⟨hisB', hunspB'⟩
        · have hooF : fav.onceOnly = true := (hfDisj i b ab hsc hbi habi hne).2.2.2.2.2.1 hsrc hooB
          exact (haB'.1 ab.id habMem).2 (hfSrcKilled hooF ab.id hsrc)
        · obtain ⟨id, hs, ho'⟩ := hisB'
          dsimp [effVal] at hs; cases hs
          have ho0 : σ.once[ab.id]? = some true := by rw [← honce]; exact ho'
          have hsp := hfOnceSpent ab.id (hfV.2.2.1 ab.id hsrc).2 ho0
          have hspF := hunspB' ab.id habMem ho'
          rw [hsp] at hspF; cases hspF
      have hneSrcA : aav.src ≠ some ab.id := by
        intro hsrc
        have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
        rcases hftB' with hooB | ⟨hisB', hunspB'⟩
        · have hooA : aav.onceOnly = true := (haDisj i b ab hsc hbi habi hne).2.2.2.2.2.1 hsrc hooB
          by_cases hdo : d = .once
          · exact (haB'.1 ab.id habMem).2 (haSrcKilled hdo hooA ab.id hsrc)
          · rw [(hnonOnceA hdo).2.1] at hooA; cases hooA
        · obtain ⟨id, hs, ho'⟩ := hisB'
          dsimp [effVal] at hs; cases hs
          have ho0 : σ.once[ab.id]? = some true := by rw [← honce]; exact ho'
          have hsp := haOnceSpent ab.id (haV.2.2.1 ab.id hsrc).2 ho0
          have hspF := hunspB' ab.id habMem ho'
          rw [hsp] at hspF; cases hspF
      rcases hreach' l hrR' with hge | hrf | hra | hss | hnum
      · omega
      · exact (hfDisj i b ab hsc hbi habi hne).2.2.2.1 haB0 hftB0 hactF hneSrcF l hfl hrf
      · exact (haDisj i b ab hsc hbi habi hne).2.2.2.1 haB0 hftB0 hactA hneSrcA l hfl hra
      · exact hnotSS hss
      · exact hnotNum' hnum
  -- Prove `NoReachForbid` for `res`
  have hNrfRes : ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv := by
    intro _ hregsR hdepsR l hr' hnotSS' hnotNum' hForb
    have hltF := hForbidLt l hForb
    by_cases hcv : c = .val
    · have hnotSS0 : ¬ StaticStrLoc st l := fun hss => hnotSS' (StaticStrLoc_mono hstat' hstr' hpresSS hss)
      have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hc⟩ =>
        hnotNum' ⟨o, n, hpresNum l o n ho hc, hc⟩
      have hdepsF : ∀ d ∈ fav.deps, ¬ BadDep d := fun d hd => hdepsR d ((hdepsOfVal hcv d).mpr (Or.inl hd))
      have hdepsA : ∀ d ∈ aav.deps, ¬ BadDep d := fun d hd => hdepsR d ((hdepsOfVal hcv d).mpr (Or.inr hd))
      have hregsF : ∀ r ∈ fav.regs, ¬ BadReg r := by
        intro r hr; obtain ⟨hu, hub, hb, hsh⟩ := hvalR hcv
        refine hregsR r ?_
        cases resM with
        | unique => exact (hu rfl).2.2 r |>.mpr hr
        | uniqueBorrowed => exact (hub rfl).2.2 r |>.mpr (Or.inr (Or.inl hr))
        | borrowed => exact (hb rfl).2.2 r |>.mpr (Or.inr (Or.inl hr))
        | shared => exact (hsh rfl).2.2 r |>.mpr (Or.inl hr)
      rcases hreach' l hr' with hge | hrf | hra | hss | hnum
      · omega
      · exact hfNrf hactF hregsF hdepsF l hrf hnotSS0 hnotNum0 hForb
      · cases hrm : resM with
        | unique =>
          by_cases hbe : m_in.isBorrowed = true ∨ m_in = .erased
          · have hnoA := (huniqPost ⟨by rw [hrm]; rfl, hcv⟩).2.2 hrm hbe l hr'
            rcases hnoA with hge | hrf | hss | hnum
            · omega
            · exact hfNrf hactF hregsF hdepsF l hrf hnotSS0 hnotNum0 hForb
            · exact hnotSS0 hss
            · exact hnotNum' hnum
          · by_cases haVal : aav.cls = .val
            · have hregsA : aav.regs = [] := by
                have hnbM : m_in.isBorrowed = false := Bool.eq_false_iff.mpr fun h => hbe (Or.inl h)
                have hneE : m_in ≠ .erased := fun h => hbe (Or.inr h)
                by_cases hu : m_in.isUnique = true
                · obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (c != .val)).mpr hu
                  have hbf : b = false := by
                    dsimp only [d, p] at hdu
                    cases hm : m_in <;> rw [hm] at hu hnbM hdu <;>
                      simp [destOf, BinderMode.isUnique, BinderMode.isBorrowed] at hu hnbM hdu
                    exact hdu
                  exact (huniqA b hdu haVal).2.2.1 hbf
                · have hneLeaf : aav.cls ≠ .leaf := by rw [haVal]; decide
                  have hdSO : d = .share ∨ d = .once := by
                    dsimp only [d, p]
                    have hcf : (c != .val) = false := by rw [hcv]; rfl
                    rw [hcf]
                    cases hm : m_in <;> rw [hm] at hu hnbM hneE <;>
                      simp [destOf, BinderMode.isUnique, BinderMode.isBorrowed, BinderMode.usage] at hu hnbM hneE ⊢
                  exact hrepUA hrm hcv hneLeaf hdSO
              exact haNrf hactA (fun r hr => by rw [hregsA] at hr; cases hr) hdepsA l hra hnotSS0 hnotNum0 hForb
            · exact hnotNum0 ((haNv hvdA haVal).2.reach_numLoc hra)
        | uniqueBorrowed =>
          have hregsA : ∀ r ∈ aav.regs, ¬ BadReg r := fun r hr =>
            hregsR r (((hvalR hcv).2.1 hrm).2.2 r |>.mpr (Or.inr (Or.inr hr)))
          exact haNrf hactA hregsA hdepsA l hra hnotSS0 hnotNum0 hForb
        | borrowed =>
          have hregsA : ∀ r ∈ aav.regs, ¬ BadReg r := fun r hr =>
            hregsR r (((hvalR hcv).2.2.1 hrm).2.2 r |>.mpr (Or.inr (Or.inr hr)))
          exact haNrf hactA hregsA hdepsA l hra hnotSS0 hnotNum0 hForb
        | shared =>
          have hregsA : ∀ r ∈ aav.regs, ¬ BadReg r := fun r hr =>
            hregsR r (((hvalR hcv).2.2.2 hrm).2.2 r |>.mpr (Or.inr hr))
          exact haNrf hactA hregsA hdepsA l hra hnotSS0 hnotNum0 hForb
      · exact hnotSS0 hss
      · exact hnotNum' hnum
    · exact hnotNum' ((hcls'.to_nonValSafe hcv hbv'.1.self.1).reach_numLoc hr')
  exact ⟨resFoot, hB', hst', hsz', hcap', hr', hnr', hstat', hstr',
    hpresF, hpresEx, hpresEnv, hpresNum, honce', hssf',
    hsim', hEnvNrf', hbv', hcls', hcf', hVSimRes, hDisjRes, hNrfRes,
    fun _ hne => ⟨hbv', hcls'.to_nonValSafe (hclsR ▸ hne) hbv'.1.self.1⟩,
    hreach',
    fun l hfl hEx => hrfNoCall l hfl (Or.inr (Or.inl hEx)),
    fun htr l hor hEx => ((huniqPost (hresUniqImp htr.1 htr.2.1)).2.1 l hor).1 (Or.inr (Or.inl hEx))⟩

/-- Helper: shrinking `Frame` (`Frame₁ ⊆ Frame₂`) preserves `VSim` (since `Frame` occurs only negatively). -/
theorem VSim_shrink_frame {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame₁ Frame₂ NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp}
    {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hsub : ∀ l, Frame₁ l → Frame₂ l)
    (hv : VSim P ext B st Frame₂ NoKill NoSpend σ I Foot av v) :
    VSim P ext B st Frame₁ NoKill NoSpend σ I Foot av v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  refine ⟨h1, h2, h3, h4, fun ha => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h5 ha
  exact ⟨a1, a2, a3, a4, a5,
    fun hoo => let h := a6 hoo; ⟨h.1, fun hnk l hl hF => h.2.1 hnk l hl (hsub l hF), h.2.2⟩,
    fun his => let h := a7 his; ⟨h.1, fun hns l hl hF => h.2.1 hns l hl (hsub l hF), h.2.2⟩,
    fun htr => let h := a8 htr; ⟨h.1, fun l hor => ⟨fun hF => (h.2 l hor).1 (hsub l hF), (h.2 l hor).2⟩⟩⟩

/-- Helper: adding `StaticStrLoc st` to `Frame` preserves `VSim` unconditionally (since `VSim`
already forbids `StaticStrLoc st` on `Foot` and `OwnReach`). -/
theorem VSim_add_staticStr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp}
    {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot av v) :
    VSim P ext B st (fun l => Frame l ∨ StaticStrLoc st l) NoKill NoSpend σ I Foot av v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  refine ⟨h1, h2, h3, h4, fun ha => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h5 ha
  refine ⟨a1, a2, a3, a4, a5, ?_, ?_, ?_⟩
  · intro hoo
    obtain ⟨b1, b2, b3, b4⟩ := a6 hoo
    refine ⟨b1, fun hnk l hl hF => ?_, b3, b4⟩
    rcases hF with hF | hss
    · exact b2 hnk l hl hF
    · exact (b1 l hl).2.1 hss
  · intro his
    obtain ⟨b1, b2, b3⟩ := a7 his
    refine ⟨b1, fun hns l hl hF => ?_, b3⟩
    rcases hF with hF | hss
    · exact b2 hns l hl hF
    · exact (b1 l hl).2.1 hss
  · intro htr
    obtain ⟨b1, b2⟩ := a8 htr
    refine ⟨b1, fun l hor => ⟨fun hF => ?_, (b2 l hor).2⟩⟩
    rcases hF with hF | hss
    · exact (b2 l hor).1 hF
    · exact (b2 l hor).2 hss

theorem Sim_shrink_frame {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame₁ Frame₂ NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsub : ∀ l, Frame₁ l → Frame₂ l)
    (hsim : Sim P ext B st Frame₂ NoKill NoSpend Scope env aenv σ I envFoot) :
    Sim P ext B st Frame₁ NoKill NoSpend Scope env aenv σ I envFoot :=
  ⟨hsim.1, hsim.2.1, hsim.2.2.1, hsim.2.2.2.1, hsim.2.2.2.2.1,
   fun i b ab hsc hbi habi =>
     let h := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
     ⟨h.1, fun hne => let h2 := h.2 hne; ⟨h2.1, VSim_shrink_frame hsub h2.2⟩⟩,
   hsim.2.2.2.2.2.2⟩

theorem Sim_add_staticStr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    Sim P ext B st (fun l => Frame l ∨ StaticStrLoc st l) NoKill NoSpend Scope env aenv σ I envFoot :=
  ⟨hsim.1, hsim.2.1, hsim.2.2.1, hsim.2.2.2.1, hsim.2.2.2.2.1,
   fun i b ab hsc hbi habi =>
     let h := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
     ⟨h.1, fun hne => let h2 := h.2 hne; ⟨h2.1, VSim_add_staticStr h2.2⟩⟩,
   hsim.2.2.2.2.2.2⟩

theorem ArgListOk_add_staticStr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {args : List (Option (Val × AVal × (Nat → Prop)))}
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args) :
    ArgListOk P ext B st (fun l => Frame l ∨ StaticStrLoc st l) NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args :=
  ⟨fun i v av ft hg => let h := hargs.1 i v av ft hg; ⟨VSim_add_staticStr h.1, h.2⟩, hargs.2⟩

/-- Multi-argument higher-order application bridge: connects `AApps fav (args.map (·.2.1)) c σ res σ'`
with `applyAllS P ext fuel fv (args.map (·.1)) c` at budget `B_a`. -/
theorem applyAllS_bridge {P : Prog} {ext : ExternOracle} :
    ∀ {B_a fuel : Nat}
      {st : St} {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
      {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
      {envFoot : Nat → Nat → Prop} {fFoot : Nat → Prop}
      {fav res : AVal} {fv : Val} {args : List (Val × AVal × (Nat → Prop))} {c : Cls},
      AApps fav (args.map (·.2.1)) c σ res σ' →
      Sim P ext B_a st Frame NoKill NoSpend Scope env aenv σ I envFoot →
      StOk P ext B_a st →
      (∀ l, StaticStrLoc st l → Frame l) →
      (∀ l, Frame l → l < st.heap.objs.size) →
      NoKillOk NoKill σ' →
      NoSpendOk NoSpend σ' →
      VSim P ext B_a st Frame NoKill NoSpend σ I fFoot fav fv →
      ValEnvDisj P st NoKill Scope env aenv σ envFoot fFoot fav fv →
      (ActiveVal σ fav → NoReachForbid st Forbid BadReg BadDep fav fv) →
      (ValidDeps σ fav.deps → fav.cls ≠ .val → ValBaseOk st fv ∧ NonValSafe st.heap fv) →
      (args = [] → (ValBaseOk st fv ∧ CtorFieldsOk P ext B_a st fv) ∨ (c = .val ∧ IsOnceSrc σ fav ∧ SpentOnceSafe st.heap fv)) →
      ArgListOk P ext B_a st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep (args.map some) →
      (∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop), args[i]? = some (v, av, ft) →
        (ActiveVal σ av → Transferable σ NoKill av → ActiveVal σ fav →
          (∀ d, d ∈ av.deps → ¬ (d ∈ fav.deps)) → ∀ l, OwnReach P st.heap v l → ¬ Reach st.heap fv l) ∧
        (ActiveVal σ fav → FootActive σ fav → ActiveVal σ av →
          (fav.src = none ∨ fav.src ≠ av.src) → ∀ l, fFoot l → ¬ Reach st.heap v l) ∧
        (ActiveVal σ av → FootActive σ av → ActiveVal σ fav →
          (av.src = none ∨ av.src ≠ fav.src) → ∀ l, ft l → ¬ Reach st.heap fv l) ∧
        (∀ x, fav.src = some x → av.src = some x → fav.onceOnly = av.onceOnly)) →
      (∀ (i j : Nat) (v₁ v₂ : Val) (av₁ av₂ : AVal) (ft₁ ft₂ : Nat → Prop) (x : Nat),
        args[i]? = some (v₁, av₁, ft₁) → args[j]? = some (v₂, av₂, ft₂) →
        av₁.src = some x → av₂.src = some x → av₁.onceOnly = av₂.onceOnly) →
      EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
      (∀ l, Forbid l → l < st.heap.objs.size) →
      (∀ k, (applyAllS P ext fuel fv (args.map (·.1)) c).run (st, B_a) ≠ .error (.violation k)) ∧
      ∀ rv st' B',
        (applyAllS P ext fuel fv (args.map (·.1)) c).run (st, B_a) = .ok (rv, (st', B')) →
          ∃ (resFoot : Nat → Prop),
            B' ≤ B_a ∧ StOk P ext B' st' ∧
            st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
            st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
            ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
            PreservesLocs Frame st.heap st'.heap ∧
            PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
            (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
            PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
            Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
            EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
            VSim P ext B' st' Frame NoKill NoSpend σ' I resFoot res rv ∧
            ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv ∧
            (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
            (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
            ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B' st' rv) ∨ (IsOnceSrc σ' res ∧ SpentOnceSafe st'.heap rv)) := by
  intro B_a fuel st Frame NoKill NoSpend Scope Forbid BadReg BadDep env aenv σ σ' I envFoot fFoot
    fav res fv args c happs
  induction args generalizing B_a fuel st Frame σ I fFoot fav fv with
  | nil =>
    cases happs
    intro hsim hst hstat hFlt _ _ hfV hfDisj hfNrf hfNv hfNilOk _ _ _ hEnvNrf _
    simp only [List.map_nil]
    cases fuel with
    | zero =>
      have h0 : (applyAllS P ext 0 fv [] c).run (st, B_a) = .error .outOfFuel := by
        cases B_a with
        | zero => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
        | succ b => unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B_a with
      | zero =>
        have h0 : (applyAllS P ext (n + 1) fv [] c).run (st, 0) = .error .outOfFuel := by
          unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
        rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b =>
        have hstep : (applyAllS P ext (n + 1) fv [] c).run (st, b + 1) =
            (match (conform c fv).run st with
             | .error e => .error e
             | .ok (rv, st') => .ok (rv, (st', b))) := by
          unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          rw [MS_liftM_run]; cases (conform c fv).run st <;> rfl
        rw [hstep]
        by_cases hcv : c = .val
        · subst hcv
          have hcRun : (conform .val fv).run st = .ok (fv, st) := rfl
          rw [hcRun]
          refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
          cases hok
          have hsim' : Sim P ext b st Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
            Sim_step (by omega) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
              (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
              (fun _ _ _ _ _ _ _ _ => PreservesLocs.refl _ _) hsim
          have hfV' : VSim P ext b st Frame NoKill NoSpend σ' I fFoot { fav with cls := .val } fv := by
            have h1 := VSim_step (B₂ := b) (by omega) hsim.2.1 (AStateLe.refl _) (RegsFuture.refl _)
              (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
              (fun _ => PreservesLocs.refl _ _) hfV
            obtain ⟨h1a, h1b, h1c, h1d, h1e⟩ := h1
            refine ⟨h1a, h1b, h1c, h1d, fun ha => ?_⟩
            obtain ⟨hbv, hdou, hcf, _, hpl, hoo, hos, htr⟩ := h1e ha
            refine ⟨hbv, hdou, hcf, fun _ hne => absurd rfl hne, hpl, hoo, hos, fun htrV => ?_⟩
            by_cases hfv : fav.cls = .val
            · exact htr ⟨hfv, htrV.2.1, htrV.2.2.1, htrV.2.2.2.1, htrV.2.2.2.2⟩
            · have hnv := (hfNv ha.1 hfv).2
              exact ⟨hnv.ownTreeFull.1, fun l hor => False.elim (hnv.ownTreeFull.2 l hor)⟩
          have hfDisj' : ValEnvDisj P st NoKill Scope env aenv σ' envFoot fFoot { fav with cls := .val } fv := by
            intro i b' ab hsc hbi habi hne
            obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hfDisj i b' ab hsc hbi habi hne
            refine ⟨fun ha htrV haB hdd l hor hrB => ?_, d2, d3, d4, d5, d6, d7⟩
            by_cases hfv : fav.cls = .val
            · exact d1 ha ⟨hfv, htrV.2.1, htrV.2.2.1, htrV.2.2.2.1, htrV.2.2.2.2⟩ haB hdd l hor hrB
            · exact False.elim ((hfNv ha.1 hfv).2.ownTreeFull.2 l hor)
          exact ⟨fFoot, by omega, StOk_mono (by omega) hst, Nat.le_refl _, Nat.le_refl _,
            rfl, Nat.le_refl _, ArrayExtends.refl _, ArrayExtends.refl _,
            PreservesLocs.refl _ _, fun _ _ _ _ _ _ _ _ => PreservesLocs.refl _ _,
            fun _ _ _ ho _ => ho, PreservesOnceShell.refl _, StaticStrFresh.refl _,
            hsim', hEnvNrf, hfV', hfDisj', hfNrf, (fun _ hne => absurd rfl hne),
            (hfNilOk rfl).elim (fun ⟨hb, hcf⟩ => Or.inl ⟨hb, CtorFieldsOk_mono (by omega) hcf⟩)
              (fun ⟨_, his, hsp⟩ => Or.inr ⟨his, hsp⟩)⟩
        · have hbvF : ValBaseOk st fv :=
            (hfNilOk rfl).elim (fun h => h.1) (fun ⟨hc, _, _⟩ => absurd hc hcv)
          rcases conform_spec_full (P := P) hst.1 hbvF.1 hbvF.2.1 with hSt |
            ⟨rv, st', hcRun, hr', hnr', hstat', hstr', hsz', hcap', hpres', hc', hdl', hcls', hacyc', _, _, _, _, _⟩
          · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hcRun]
            refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
            cases hok
            have honce' : PreservesOnceShell st.heap st'.heap :=
              PreservesOnceShell.of_preservesLocs (hpres'.mono fun l ⟨o, _, _, ho, _⟩ =>
                (Array.getElem?_eq_some_iff.mp ho).1)
            have hssf' : StaticStrFresh st st' :=
              StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat' hstr'
                (hpres'.mono fun _ h => h.1) (fun _ _ h => h)
            have hst' : StOk P ext b st' :=
              StOk_mono (by omega) (StOk_of_preserves_old hst hc' hr' (hnr' ▸ Nat.le_refl _) hstat' hstr' hpres')
            have hnv' : NonValSafe st'.heap rv := ClsSafe.to_nonValSafe hcv (Or.inr hcls') hdl'.self.1
            have hbv' : ValBaseOk st' rv :=
              ValBaseOk_of_deepLive hdl' hacyc' (by
                intro w hw r hrt
                rcases hw with rfl | ⟨l1, o1, hr1, ho1, hm1⟩
                · rcases hnv' with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, _, _, _⟩ <;> cases hrt
                · obtain ⟨o2, n2, ho2, hnum2⟩ := hnv'.reach_numLoc hr1
                  rw [ho2] at ho1; cases ho1; rw [hnum2] at hm1; cases hm1)
            have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hr'
            have hIok' : InterpOk σ' st' I :=
              ⟨fun r hr c' hc => hnr' ▸ hsim.2.2.1.1 r hr c' hc,
               fun c' hc => by rw [hr'] at hc; exact hsim.2.2.1.2 c' hc⟩
            have hpresEnv : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap :=
              Sim_preserves_of_old (AStateLe.refl _) hpres' hsim
            have hsim' : Sim P ext b st' Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
              Sim_step (by omega) (AStateLe.refl _) hsim.2.1 hIok' hrf' honce' hssf'
                (fun _ _ _ h => h) hpresEnv hsim
            have hEnvNrf' : EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep :=
              EnvNoReachForbid_step hsim.2.1 (AStateLe.refl _) (Sim_deps_lt hsim) hsim.2.2.2.1
                (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
                (hpres'.mono fun _ hl => StOk_staticStrLoc_lt hst hl) hpresEnv hEnvNrf
            have hVSim' : VSim P ext b st' Frame NoKill NoSpend σ' I (fun _ => False) { fav with cls := c } rv := by
              refine ⟨hfV.1, hfV.2.1, hfV.2.2.1,
                (fun hd his => by
                  rcases conform_spentOnceSafe (c := c) (hfV.2.2.2.1 hd his) with hst' | ⟨v', hv', hvc⟩
                  · rw [hcRun] at hst'; cases hst'
                  · have hveq : rv = v' := (Prod.mk.inj (Except.ok.inj (hcRun.symm.trans hv'))).1
                    rcases hvc with ⟨_, hceq⟩ | ⟨hvr, _⟩
                    · exact absurd hceq hcv
                    · rw [hveq, hvr]; exact SpentOnceSafe.irr _),
                fun _ => ⟨hbv', hnv'.deepOpenUnder_nil,
                  hnv'.ctorFieldsOk P ext b st', fun _ _ => hnv',
                  fun _ => ⟨hnv'.noOnceCell, fun _ h => h, hnv'.funOkAt P ext b st' fav.skel⟩,
                  fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
                    fun _ _ _ _ _ _ _ _ _ _ h => h, FunOkAt_weaken_onceOnly (hnv'.funOkAt P ext b st' fav.skel)⟩,
                  fun _ => ⟨fun _ h => False.elim h, fun _ _ h => False.elim h,
                    FunOkAt_weaken_onceOnly (hnv'.funOkAt P ext b st' fav.skel)⟩,
                  fun htr => absurd htr.1 hcv⟩⟩
            have hDisj' : ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) { fav with cls := c } rv := by
              intro i b' ab hsc hbi habi hne
              refine ⟨fun _ htr => absurd htr.1 hcv,
                fun _ _ _ _ l hor' hrR' => OwnReach_not_numLoc hor' (hnv'.reach_numLoc hrR'),
                fun _ _ _ _ _ h => False.elim h,
                fun haB hftB _ _ l hfl hrR' => ?_,
                fun _ _ _ _ h => False.elim h,
                (hfDisj i b' ab hsc hbi habi hne).2.2.2.2.2.1,
                fun _ _ => Or.inr fun l hrR' => hnv'.reach_numLoc hrR'⟩
              have hvB := ((hsim'.2.2.2.2.2.1 i b' ab hsc hbi habi).2 hne).2
              rcases hftB with hooB | ⟨hisB, _⟩
              · exact ((hvB.2.2.2.2 haB).2.2.2.2.2.1 hooB).1 l hfl |>.2.2 (hnv'.reach_numLoc hrR')
              · exact ((hvB.2.2.2.2 haB).2.2.2.2.2.2.1 hisB).1 l hfl |>.2.2 (hnv'.reach_numLoc hrR')
            exact ⟨fun _ => False, by omega, hst', hsz', hcap', hr', hnr' ▸ Nat.le_refl _,
              hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
              hpres'.mono fun l hF => hFlt l hF, hpresEnv,
              fun l o n ho _ => (hpres' l (Array.getElem?_eq_some_iff.mp ho).1).trans ho,
              honce', hssf', hsim', hEnvNrf', hVSim', hDisj',
              fun _ _ _ l hrR' _ hnotNum => False.elim (hnotNum (hnv'.reach_numLoc hrR')),
              (fun _ _ => ⟨hbv', hnv'⟩), Or.inl ⟨hbv', hnv'.ctorFieldsOk P ext b st'⟩⟩
  | cons p0 rest ih =>
    rcases p0 with ⟨av0, aav0, aFoot0⟩
    cases rest with
    | nil =>
      -- Single remaining argument: `AApps.consLast`
      cases happs with
      | @consLast _ _ _ _ g0 _ hrun =>
        intro hsim hst hstat hFlt hnk' hnsp' hfV hfDisj hfNrf _ _ hargs hfaPair _ hEnvNrf hForbidLt
        simp only [List.map_cons, List.map_nil]
        cases fuel with
        | zero =>
          have h0 : (applyAllS P ext 0 fv [av0] c).run (st, B_a) = .error .outOfFuel := by
            cases B_a with
            | zero => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
            | succ b => unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; rfl
          rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        | succ n =>
          cases B_a with
          | zero =>
            have h0 : (applyAllS P ext (n + 1) fv [av0] c).run (st, 0) = .error .outOfFuel := by
              unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
            rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          | succ b =>
            have ha0 := hargs.1 0 av0 aav0 aFoot0 (by simp)
            have hpair0 := hfaPair 0 av0 aav0 aFoot0 (by simp)
            obtain ⟨hnoV, hokRun⟩ := applyValue_bridge (fuel := n) (FrameExtra := fun _ => False)
              hrun hsim (StOk_mono (by omega) hst) hstat hFlt hnk' hnsp'
              hfV hfDisj hfNrf ha0.1 ha0.2.1 ha0.2.2.1 ha0.2.2.2
              hpair0.1 hpair0.2.1 hpair0.2.2.1 hpair0.2.2.2 hEnvNrf hForbidLt
              (fun _ h => False.elim h) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
            have hstep : (applyAllS P ext (n + 1) fv [av0] c).run (st, b + 1) =
                (match (applyOneS P ext n fv av0 c).run (st, b) with
                 | .error e => .error e
                 | .ok (g, (st₁, B₁)) => (applyAllS P ext n g [] c).run (st₁, B₁)) := by
              conv => lhs; unfold applyAllS
              rw [MS_bind_run, MS_spend_succ]; dsimp only
              simp only [List.isEmpty_nil, ↓reduceIte]
              rw [MS_bind_run]
              cases (applyOneS P ext n fv av0 c).run (st, b) with
              | error _ => rfl
              | ok p => rcases p with ⟨g, ⟨st₁, B₁⟩⟩; rfl
            rw [hstep]
            cases hone : (applyOneS P ext n fv av0 c).run (st, b) with
            | error e =>
              refine ⟨fun k hk => ?_, (fun _ _ _ h => by cases h)⟩
              cases hk
              have hEq : (applyOneConformS P ext n fv av0 c).run (st, b) = .error (.violation k) := by
                unfold applyOneConformS; rw [MS_bind_run, hone]
              exact hnoV k hEq
            | ok p =>
              rcases p with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
              cases n with
              | zero =>
                have h0 : (applyAllS P ext 0 g [] c).run (st₁, B₁) = .error .outOfFuel := by
                  cases B₁ with
                  | zero => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
                  | succ b₁ => unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; rfl
                rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              | succ n' =>
                cases B₁ with
                | zero =>
                  have h0 : (applyAllS P ext (n' + 1) g [] c).run (st₁, 0) = .error .outOfFuel := by
                    unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
                  rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                | succ b₁ =>
                  have hstep2 : (applyAllS P ext (n' + 1) g [] c).run (st₁, b₁ + 1) =
                      (match (conform c g).run st₁ with
                       | .error e => .error e
                       | .ok (rv, st') => .ok (rv, (st', b₁))) := by
                    unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; dsimp only
                    rw [MS_liftM_run]; cases (conform c g).run st₁ <;> rfl
                  rw [hstep2]
                  have hconfEq : (applyOneConformS P ext (n' + 1) fv av0 c).run (st, b) =
                      (match (conform c g).run st₁ with
                       | .error e => .error e
                       | .ok (rv, st') => .ok (rv, (st', b₁ + 1))) := by
                    unfold applyOneConformS; rw [MS_bind_run, hone]; dsimp only
                    rw [MS_liftM_run]; cases (conform c g).run st₁ <;> rfl
                  cases hc : (conform c g).run st₁ with
                  | error e =>
                    refine ⟨fun k hk => ?_, (fun _ _ _ h => by cases h)⟩
                    cases hk; rw [hc] at hconfEq; exact hnoV k hconfEq
                  | ok pc =>
                    rcases pc with ⟨rv, st'⟩
                    rw [hc] at hconfEq
                    obtain ⟨resFoot, hB', hst', hsz', hcap', hr', hnr', hstat', hstr',
                      hpresF, _, hpresEnv, hpresNum, honce', hssf', hsim', hEnvNrf',
                      hbv', _, hcf', hVSim', hDisj', hNrf', hNv', _, _, _⟩ := hokRun rv st' (b₁ + 1) hconfEq
                    refine ⟨(fun _ h => by cases h), fun rv' st'' B' hok => ?_⟩
                    cases hok
                    have hclsG : g0.cls = c := (Runs_applyValue hsim.2.1 hrun).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                    have hresEq : { g0 with cls := c } = g0 := by cases g0; simp only at hclsG; subst hclsG; rfl
                    rw [hresEq]
                    exact ⟨resFoot, by omega, StOk_mono (by omega) hst', hsz', hcap', hr', hnr',
                      hstat', hstr', hpresF, hpresEnv, hpresNum, honce', hssf',
                      Sim_step (by omega) (AStateLe.refl _) hsim'.2.1 hsim'.2.2.1 (RegsFuture.refl _)
                        (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
                        (fun _ _ _ _ _ _ _ _ => PreservesLocs.refl _ _) hsim',
                      hEnvNrf',
                      VSim_step (by omega) hsim'.2.1 (AStateLe.refl _) (RegsFuture.refl _)
                        (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
                        (fun _ => PreservesLocs.refl _ _) hVSim',
                      hDisj', hNrf', (fun hd hne => hNv' hd (hclsG.symm ▸ hne)),
                      Or.inl ⟨hbv', CtorFieldsOk_mono (by omega) hcf'⟩⟩
    | cons p1 rest' =>
      -- Multiple remaining arguments: `AApps.consMore`
      cases happs with
      | @consMore _ _ _ _ _ _ gav σ₁ _ _ hrun happsRest =>
        intro hsim hst hstat hFlt hnk' hnsp' hfV hfDisj hfNrf _ _ hargs hfaPair hArgsSrc hEnvNrf hForbidLt
        cases fuel with
        | zero =>
          have h0 : (applyAllS P ext 0 fv (((av0, aav0, aFoot0) :: p1 :: rest').map (·.1)) c).run (st, B_a) = .error .outOfFuel := by
            cases B_a with
            | zero => unfold applyAllS; rw [MS_bind_run, MS_spend_zero]
            | succ b => unfold applyAllS; rw [MS_bind_run, MS_spend_succ]; rfl
          rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        | succ n =>
          cases B_a with
          | zero =>
            have h0 : (applyAllS P ext (n + 1) fv (((av0, aav0, aFoot0) :: p1 :: rest').map (·.1)) c).run (st, 0) = .error .outOfFuel := by
              change (applyAllS P ext (n + 1) fv (av0 :: (p1 :: rest').map (·.1)) c).run (st, 0) = _
              conv => lhs; unfold applyAllS
              rw [MS_bind_run, MS_spend_zero]
            rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          | succ b =>
            have hok0 := hsim.2.1
            have hrunU := Runs_applyValue hok0 hrun
            rcases hap : arrowParts fav.skel with ⟨m_in, dom, resM, cod⟩
            rw [hap] at hrunU; dsimp only at hrunU
            obtain ⟨hok₁, hle₀₁, hszSt₁, honce₁, hszSp₁, _, _, hvdF₀, hunspF₀, hvdA₀, honceA₀, hnonOnceA,
              huniqA₀, _, _, _, _, hsrcG, _, hvalG, _, hspPt₁, hstPt₁⟩ := hrunU
            -- Compute `AStateLe σ₁ σ'` from `happsRest`
            have hle₁' : AStateLe σ₁ σ' := by
              have hleApps : ∀ {f0 : AVal} {xs : List AVal} {c0 : Cls} {s0 s1 : AState} {r0 : AVal},
                  AStateOk s0 → AApps f0 xs c0 s0 r0 s1 → AStateLe s0 s1 := by
                intro f0 xs c0 s0 s1 r0 hokS ha
                induction ha with
                | nil => exact AStateLe.refl _
                | consLast hr => exact (Runs_applyValue hokS hr).2.1
                | consMore hr _ ihA =>
                  have hu := Runs_applyValue hokS hr
                  exact hu.2.1.trans (ihA hu.1)
              exact hleApps hok₁ happsRest
            have hnk₁ : NoKillOk NoKill σ₁ := fun d hd hdead => by
              have hlt : d < σ₁.st.size := (Array.getElem?_eq_some_iff.mp hdead).1
              have hle := hle₁'.2.2.1 d hlt; rw [hdead] at hle
              cases h2 : σ'.st[d]? with
              | none => rw [h2] at hle; exact hle
              | some b2 =>
                rw [h2] at hle
                cases b2 with
                | dead => exact hnk' d hd h2
                | live | shared => exact hle
            have hnsp₁ : NoSpendOk NoSpend σ₁ := fun d hd hsp => by
              have hlt : d < σ₁.spent.size := (Array.getElem?_eq_some_iff.mp hsp).1
              exact hnsp' d hd (hle₁'.2.2.2.2 d hlt hsp)
            let tailArgs := p1 :: rest'
            let FrameExtra : Nat → Prop := fun l =>
              ∃ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
                tailArgs[j]? = some (vj, avj, ftj) ∧ ActiveVal σ₁ avj ∧ Reach st.heap vj l
            have hTailGet : ∀ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
                tailArgs[j]? = some (vj, avj, ftj) →
                ((av0, aav0, aFoot0) :: tailArgs)[j + 1]? = some (vj, avj, ftj) := fun _ _ _ _ h => h
            have hTailMap : ∀ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
                tailArgs[j]? = some (vj, avj, ftj) →
                (((av0, aav0, aFoot0) :: p1 :: rest').map some)[j + 1]? = some (some (vj, avj, ftj)) := by
              intro j vj avj ftj hgj
              simp only [List.map_cons, List.getElem?_cons_succ]
              change (tailArgs.map some)[j]? = _
              rw [List.getElem?_map, hgj]; rfl
            have hExLt : ∀ l, FrameExtra l → l < st.heap.objs.size := by
              rintro l ⟨j, vj, avj, ftj, hgj, ha₁, hrj⟩
              have hvj := (hargs.1 (j + 1) vj avj ftj (hTailMap j vj avj ftj hgj)).1
              have ha0 := ActiveVal.of_AStateLe hok0 hle₀₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) ha₁
              exact (hvj.2.2.2.2 ha0).1.1.reach_lt_size hrj
            have hExF : (fav.onceOnly = true ∨ IsOnceSrc σ fav) → ∀ l, fFoot l → ¬ FrameExtra l := by
              rintro hdisjF l hfl ⟨j, vj, avj, ftj, hgj, ha₁, hrj⟩
              have hvj := (hargs.1 (j + 1) vj avj ftj (hTailMap j vj avj ftj hgj)).1
              have ha0 := ActiveVal.of_AStateLe hok0 hle₀₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) ha₁
              have hactF : ActiveVal σ fav := ⟨hvdF₀, fun _ => hunspF₀⟩
              have hftActF : FootActive σ fav := by
                rcases hdisjF with h1 | h2
                · exact Or.inl h1
                · exact Or.inr ⟨h2, hunspF₀⟩
              have hneSrc : fav.src = none ∨ fav.src ≠ avj.src := by
                cases hfs : fav.src with
                | none => exact Or.inl rfl
                | some x =>
                  right; intro hEq
                  have hxJ : x ∈ avj.deps := (hvj.2.2.1 x hEq.symm).2
                  rcases hdisjF with hoo | ⟨id, hs, ho⟩
                  · have hlt := (hfV.2.2.1 x hfs).1
                    have hdead := hstPt₁ x hlt
                    simp only [hoo, hfs, and_self, true_or, ↓reduceIte] at hdead
                    exact (ha₁.1 x hxJ).2 hdead
                  · rw [hfs] at hs; cases hs
                    have hltSp : x < σ.spent.size := by have h1 := (hfV.2.2.1 x hfs).1; have h2 := hok0.2.1; omega
                    have hsp := hspPt₁ x hltSp
                    simp only [(hfV.2.2.1 x hfs).2, true_or, ho, and_self, ↓reduceIte] at hsp
                    have his₁ : IsOnceSrc σ₁ avj := ⟨x, hEq.symm, by rw [honce₁]; exact ho⟩
                    have hspF := ha₁.2 his₁ x hxJ (by rw [honce₁]; exact ho)
                    rw [hsp] at hspF; cases hspF
              exact (hfaPair (j + 1) vj avj ftj (hTailGet j vj avj ftj hgj)).2.1 hactF hftActF ha0 hneSrc l hfl hrj
            have hExA : (destOf { mode := (arrowParts fav.skel).1, cls := aav0.cls, skel := (arrowParts fav.skel).2.1 } (Cls.val != .val) = .once ∧
                (aav0.onceOnly = true ∨ IsOnceSrc σ aav0)) → ∀ l, aFoot0 l → ¬ FrameExtra l := by
              rintro ⟨hdo, hdisjA⟩ l hfl ⟨j, vj, avj, ftj, hgj, ha₁, hrj⟩
              rw [hap] at hdo; dsimp only at hdo
              have hv0 := (hargs.1 0 av0 aav0 aFoot0 (by simp)).1
              have hvj := (hargs.1 (j + 1) vj avj ftj (hTailMap j vj avj ftj hgj)).1
              have ha0 := ActiveVal.of_AStateLe hok0 hle₀₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) ha₁
              have hactA : ActiveVal σ aav0 := ⟨hvdA₀, fun _ => (honceA₀ hdo).2.1⟩
              have hftActA : FootActive σ aav0 := by
                rcases hdisjA with h1 | h2
                · exact Or.inl h1
                · exact Or.inr ⟨h2, (honceA₀ hdo).2.1⟩
              have hneSrc : aav0.src = none ∨ aav0.src ≠ avj.src := by
                cases has : aav0.src with
                | none => exact Or.inl rfl
                | some x =>
                  right; intro hEq
                  have hxJ : x ∈ avj.deps := (hvj.2.2.1 x hEq.symm).2
                  rcases hdisjA with hoo | ⟨id, hs, ho⟩
                  · have hlt := (hv0.2.2.1 x has).1
                    have hdead := hstPt₁ x hlt
                    have hk : callKills (Cls.val != .val) { mode := m_in, cls := aav0.cls, skel := dom } aav0 x :=
                      Or.inr ⟨hdo, hoo, has⟩
                    simp only [hk, or_true, ↓reduceIte] at hdead
                    exact (ha₁.1 x hxJ).2 hdead
                  · rw [has] at hs; cases hs
                    have hltSp : x < σ.spent.size := by have h1 := (hv0.2.2.1 x has).1; have h2 := hok0.2.1; omega
                    have hsp := hspPt₁ x hltSp
                    simp only [(hv0.2.2.1 x has).2, or_true, ho, and_self, ↓reduceIte] at hsp
                    have his₁ : IsOnceSrc σ₁ avj := ⟨x, hEq.symm, by rw [honce₁]; exact ho⟩
                    have hspF := ha₁.2 his₁ x hxJ (by rw [honce₁]; exact ho)
                    rw [hsp] at hspF; cases hspF
              exact (hargs.2 0 (j + 1) av0 vj aav0 avj aFoot0 ftj (by omega)
                (by simp) (hTailMap j vj avj ftj hgj)).2 hactA hftActA ha0 hneSrc l hfl hrj
            have hExU : ((arrowParts fav.skel).1.isUnique = true ∧ aav0.cls = .val) →
                ∀ l, OwnReach P st.heap av0 l → ¬ FrameExtra l := by
              rintro ⟨hu, hcv⟩ l hor ⟨j, vj, avj, ftj, hgj, ha₁, hrj⟩
              rw [hap] at hu; dsimp only at hu
              have hv0 := (hargs.1 0 av0 aav0 aFoot0 (by simp)).1
              have hvj := (hargs.1 (j + 1) vj avj ftj (hTailMap j vj avj ftj hgj)).1
              have ha0 := ActiveVal.of_AStateLe hok0 hle₀₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) ha₁
              let p0' : Param := { mode := m_in, cls := aav0.cls, skel := dom }
              obtain ⟨b0, hdu⟩ := (destOf_isUniq_iff p0' (Cls.val != .val)).mpr hu
              have hneO : destOf p0' (Cls.val != .val) ≠ .once := by rw [hdu]; intro h; cases h
              obtain ⟨_, hooA, hnotOS⟩ := hnonOnceA hneO
              obtain ⟨hown, hlv, _, _⟩ := huniqA₀ b0 hdu hcv
              have hdeadA : ∀ x ∈ aav0.deps, σ₁.st[x]? = some .dead := by
                intro x hx
                have hlt := hv0.2.1 x hx
                have h1 := hstPt₁ x hlt
                have hk : callKills (Cls.val != .val) { mode := m_in, cls := aav0.cls, skel := dom } aav0 x :=
                  Or.inl ⟨b0, hdu, hcv, hx⟩
                simp only [hk, or_true, ↓reduceIte] at h1; exact h1
              have hactA : ActiveVal σ aav0 := ⟨hvdA₀, fun his => False.elim (hnotOS his)⟩
              have htrA : Transferable σ NoKill aav0 :=
                ⟨hcv, hown, hooA, hnotOS, fun x hx => ⟨hlv x hx, fun hnk => hnk₁ x hnk (hdeadA x hx)⟩⟩
              have hdd : ∀ x, x ∈ aav0.deps → ¬ (x ∈ avj.deps) := fun x hx hxj =>
                (ha₁.1 x hxj).2 (hdeadA x hx)
              exact (hargs.2 0 (j + 1) av0 vj aav0 avj aFoot0 ftj (by omega)
                (by simp) (hTailMap j vj avj ftj hgj)).1 hactA htrA ha0 hdd l hor hrj
            have ha0 := hargs.1 0 av0 aav0 aFoot0 (by simp)
            have hpair0 := hfaPair 0 av0 aav0 aFoot0 (by simp)
            obtain ⟨hnoV1, hokRun1⟩ := applyValue_bridge (fuel := n) (FrameExtra := FrameExtra)
              hrun hsim (StOk_mono (by omega) hst) hstat hFlt hnk₁ hnsp₁
              hfV hfDisj hfNrf ha0.1 ha0.2.1 ha0.2.2.1 ha0.2.2.2
              hpair0.1 hpair0.2.1 hpair0.2.2.1 hpair0.2.2.2 hEnvNrf hForbidLt
              hExLt hExF hExA hExU
            have hstep : (applyAllS P ext (n + 1) fv (((av0, aav0, aFoot0) :: p1 :: rest').map (·.1)) c).run (st, b + 1) =
                (match (applyOneConformS P ext n fv av0 .val).run (st, b) with
                 | .error e => .error e
                 | .ok (g, (st₁, B₁)) => (applyAllS P ext n g (tailArgs.map (·.1)) c).run (st₁, B₁)) := by
              change (applyAllS P ext (n + 1) fv (av0 :: tailArgs.map (·.1)) c).run (st, b + 1) = _
              conv => lhs; unfold applyAllS
              rw [MS_bind_run, MS_spend_succ]; dsimp only
              have hneEmpty : (tailArgs.map (·.1)).isEmpty = false := rfl
              simp only [hneEmpty, Bool.false_eq_true, ↓reduceIte]
              rw [MS_bind_run, ← applyOneConformS_val_eq_applyOneS]
              cases (applyOneConformS P ext n fv av0 .val).run (st, b) with
              | error _ => rfl
              | ok p => rcases p with ⟨g, ⟨st₁, B₁⟩⟩; rfl
            rw [hstep]
            cases hone : (applyOneConformS P ext n fv av0 .val).run (st, b) with
            | error e =>
              refine ⟨fun k hk => ?_, (fun _ _ _ h => by cases h)⟩
              cases hk; exact hnoV1 k hone
            | ok pg =>
              rcases pg with ⟨g, ⟨st₁, B₁⟩⟩; dsimp only
              obtain ⟨gFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
                hpresF₁, hpresEx₁, hpresEnv₁, hpresNum₁, honceSh₁, hssf₁,
                hsim₁, hEnvNrf₁, hbvG, _, _, hVSimG, hDisjG, hNrfG, hNvG, hreachG, hFootExG, hTrExG⟩ :=
                hokRun1 g st₁ B₁ hone
              have hpresSS₁ : PreservesLocs (StaticStrLoc st) st.heap st₁.heap :=
                hpresF₁.mono fun l hss => hstat l hss
              let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
              have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
              have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h => by
                rcases h with hF | hss
                · exact Nat.lt_of_lt_of_le (hFlt l hF) hsz₁
                · exact StOk_staticStrLoc_lt hst₁ hss
              have hrf₁ : RegsFuture st st₁ := RegsFuture.same_regions hnr₁ hr₁
              have htailArgs₀ : ArgListOk P ext (b + 1) st Frame NoKill NoSpend Scope env aenv σ I envFoot
                  Forbid BadReg BadDep (tailArgs.map some) := by
                refine ⟨fun i v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
                · exact hargs.1 (i + 1) v av ft hg
                · exact hargs.2 (i + 1) (j + 1) v₁ v₂ av₁ av₂ ft₁ ft₂ (by omega) hg₁ hg₂
              have htailPres : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
                  (tailArgs.map some)[i]? = some (some (v, av, ft)) → ActiveVal σ₁ av →
                  PreservesLocs (Reach st.heap v) st.heap st₁.heap := by
                intro i v av ft hg ha₁
                have hg' : tailArgs[i]? = some (v, av, ft) := by
                  rw [List.getElem?_map] at hg
                  cases ht : tailArgs[i]? with
                  | none => rw [ht] at hg; cases hg
                  | some p => rw [ht] at hg; simp at hg; subst hg; rfl
                exact hpresEx₁.mono fun l hr => ⟨i, v, av, ft, hg', ha₁, hr⟩
              have htailArgs₁ : ArgListOk P ext B₁ st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
                  Forbid BadReg BadDep (tailArgs.map some) :=
                ArgListOk_add_staticStr (ArgListOk_step (by omega) hok0 hle₀₁ hrf₁ honceSh₁ hssf₁
                  hstat₁ hstr₁ hpresSS₁ (fun _ _ _ h => h) (Sim_deps_lt hsim) hsim.2.2.2.1
                  hpresEnv₁ htailPres hpresNum₁ htailArgs₀)
              have hdepsG : ∀ x, x ∈ gav.deps ↔ x ∈ fav.deps ∨ x ∈ aav0.deps := by
                intro x; obtain ⟨hu, hub, hb, hsh⟩ := hvalG rfl
                cases resM with
                | unique => exact (hu rfl).2.1 x
                | uniqueBorrowed => exact (hub rfl).2.1 x
                | borrowed => exact (hb rfl).2.1 x
                | shared => exact (hsh rfl).2.1 x
              have hactF : ActiveVal σ fav := ⟨hvdF₀, fun _ => hunspF₀⟩
              have hactA : ActiveVal σ aav0 := ⟨hvdA₀, fun his => by
                by_cases hdo : destOf { mode := m_in, cls := aav0.cls, skel := dom } (Cls.val != .val) = .once
                · exact (honceA₀ hdo).2.1
                · exact False.elim ((hnonOnceA hdo).2.2 his)⟩
              have hgaPair : ∀ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
                  tailArgs[j]? = some (vj, avj, ftj) →
                  (ActiveVal σ₁ avj → Transferable σ₁ NoKill avj → ActiveVal σ₁ gav →
                    (∀ d, d ∈ avj.deps → ¬ (d ∈ gav.deps)) → ∀ l, OwnReach P st₁.heap vj l → ¬ Reach st₁.heap g l) ∧
                  (ActiveVal σ₁ gav → FootActive σ₁ gav → ActiveVal σ₁ avj →
                    (gav.src = none ∨ gav.src ≠ avj.src) → ∀ l, gFoot l → ¬ Reach st₁.heap vj l) ∧
                  (ActiveVal σ₁ avj → FootActive σ₁ avj → ActiveVal σ₁ gav →
                    (avj.src = none ∨ avj.src ≠ gav.src) → ∀ l, ftj l → ¬ Reach st₁.heap g l) ∧
                  (∀ x, gav.src = some x → avj.src = some x → gav.onceOnly = avj.onceOnly) := by
                intro j vj avj ftj hgj
                have hvj := (hargs.1 (j + 1) vj avj ftj (hTailMap j vj avj ftj hgj)).1
                have hsrcJ : ∀ x, avj.src = some x → x < σ.st.size := fun x hx => (hvj.2.2.1 x hx).1
                refine ⟨?_, ?_, ?_, fun _ hs => by rw [hsrcG] at hs; cases hs⟩
                · intro haJ₁ htrJ₁ _ hdd l horJ₁ hrG₁
                  have hpJ : PreservesLocs (Reach st.heap vj) st.heap st₁.heap :=
                    hpresEx₁.mono fun l' hr' => ⟨j, vj, avj, ftj, hgj, haJ₁, hr'⟩
                  have haJ₀ := ActiveVal.of_AStateLe hok0 hle₀₁ hvj.2.1 hsrcJ haJ₁
                  have htrJ₀ := Transferable.of_AStateLe hok0 hle₀₁ hvj.2.1 hsrcJ (fun _ h => h) htrJ₁
                  have horJ₀ := (OwnReach_congr hpJ l).mp horJ₁
                  have hltL : l < st.heap.objs.size := (hvj.2.2.2.2 haJ₀).1.1.reach_lt_size (OwnReach_toReach horJ₀)
                  have hnotSS : ¬ StaticStrLoc st l := ((hvj.2.2.2.2 haJ₀).2.2.2.2.2.2.2 htrJ₀).2 l horJ₀ |>.2
                  have hnotNum : ¬ NumLoc st₁.heap l := OwnReach_not_numLoc horJ₁
                  rcases hreachG l hrG₁ with hge | hrf | hra | hss | hnum
                  · omega
                  · exact (hfaPair (j + 1) vj avj ftj (hTailGet j vj avj ftj hgj)).1 haJ₀ htrJ₀ hactF
                      (fun d hd hdf => hdd d hd ((hdepsG d).mpr (Or.inl hdf))) l horJ₀ hrf
                  · exact (hargs.2 (j + 1) 0 vj av0 avj aav0 ftj aFoot0 (by omega)
                      (hTailMap j vj avj ftj hgj) (by simp)).1 haJ₀ htrJ₀ hactA
                      (fun d hd hda => hdd d hd ((hdepsG d).mpr (Or.inr hda))) l horJ₀ hra
                  · exact hnotSS hss
                  · exact hnotNum hnum
                · intro _ _ haJ₁ _ l hfl hrJ₁
                  have hpJ : PreservesLocs (Reach st.heap vj) st.heap st₁.heap :=
                    hpresEx₁.mono fun l' hr' => ⟨j, vj, avj, ftj, hgj, haJ₁, hr'⟩
                  exact hFootExG l hfl ⟨j, vj, avj, ftj, hgj, haJ₁, (Reach_congr hpJ l).mp hrJ₁⟩
                · intro haJ₁ hftJ₁ _ _ l hfl hrG₁
                  have hpJ : PreservesLocs (Reach st.heap vj) st.heap st₁.heap :=
                    hpresEx₁.mono fun l' hr' => ⟨j, vj, avj, ftj, hgj, haJ₁, hr'⟩
                  have haJ₀ := ActiveVal.of_AStateLe hok0 hle₀₁ hvj.2.1 hsrcJ haJ₁
                  have hftJ₀ := FootActive.of_AStateLe hok0 hle₀₁ hvj.2.1 hsrcJ hftJ₁
                  have ⟨hrJ₀, hnotSS, hnotNum0⟩ : Reach st.heap vj l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
                    rcases hftJ₀ with hooJ | ⟨hisJ, _⟩
                    · exact ((hvj.2.2.2.2 haJ₀).2.2.2.2.2.1 hooJ).1 l hfl
                    · exact ((hvj.2.2.2.2 haJ₀).2.2.2.2.2.2.1 hisJ).1 l hfl
                  have hltL : l < st.heap.objs.size := (hvj.2.2.2.2 haJ₀).1.1.reach_lt_size hrJ₀
                  have hnotNum₁ : ¬ NumLoc st₁.heap l := fun hn => hnotNum0 ((NumLoc_congr hpJ hrJ₀).mpr hn)
                  have hneSrcF : avj.src = none ∨ avj.src ≠ fav.src := by
                    cases hjs : avj.src with
                    | none => exact Or.inl rfl
                    | some x =>
                      right; intro hEq
                      have hxJ : x ∈ avj.deps := (hvj.2.2.1 x hjs).2
                      rcases hftJ₁ with hooJ | ⟨⟨id, hs, ho₁⟩, hunspJ₁⟩
                      · have hooF : fav.onceOnly = true := (hfaPair (j + 1) vj avj ftj (hTailGet j vj avj ftj hgj)).2.2.2 x hEq.symm hjs |>.trans hooJ
                        have hlt := (hfV.2.2.1 x hEq.symm).1
                        have hdead := hstPt₁ x hlt
                        simp only [hooF, hEq.symm, and_self, true_or, ↓reduceIte] at hdead
                        exact (haJ₁.1 x hxJ).2 hdead
                      · rw [hjs] at hs; cases hs
                        have ho0 : σ.once[x]? = some true := by rw [← honce₁]; exact ho₁
                        have hltSp : x < σ.spent.size := by have h1 := (hfV.2.2.1 x hEq.symm).1; have h2 := hok0.2.1; omega
                        have hsp := hspPt₁ x hltSp
                        simp only [(hfV.2.2.1 x hEq.symm).2, true_or, ho0, and_self, ↓reduceIte] at hsp
                        have hspF := hunspJ₁ x hxJ ho₁
                        rw [hsp] at hspF; cases hspF
                  have hneSrcA : avj.src = none ∨ avj.src ≠ aav0.src := by
                    cases hjs : avj.src with
                    | none => exact Or.inl rfl
                    | some x =>
                      right; intro hEq
                      have hxJ : x ∈ avj.deps := (hvj.2.2.1 x hjs).2
                      have hv0 := (hargs.1 0 av0 aav0 aFoot0 (by simp)).1
                      rcases hftJ₁ with hooJ | ⟨⟨id, hs, ho₁⟩, hunspJ₁⟩
                      · have hooA : aav0.onceOnly = true :=
                          (hArgsSrc (j + 1) 0 vj av0 avj aav0 ftj aFoot0 x
                            (hTailGet j vj avj ftj hgj) (by simp) hjs hEq.symm).symm.trans hooJ
                        by_cases hdo : destOf { mode := m_in, cls := aav0.cls, skel := dom } (Cls.val != .val) = .once
                        · have hlt := (hv0.2.2.1 x hEq.symm).1
                          have hdead := hstPt₁ x hlt
                          have hk : callKills (Cls.val != .val) { mode := m_in, cls := aav0.cls, skel := dom } aav0 x :=
                            Or.inr ⟨hdo, hooA, hEq.symm⟩
                          simp only [hk, or_true, ↓reduceIte] at hdead
                          exact (haJ₁.1 x hxJ).2 hdead
                        · rw [(hnonOnceA hdo).2.1] at hooA; cases hooA
                      · rw [hjs] at hs; cases hs
                        have ho0 : σ.once[x]? = some true := by rw [← honce₁]; exact ho₁
                        have hltSp : x < σ.spent.size := by have h1 := (hv0.2.2.1 x hEq.symm).1; have h2 := hok0.2.1; omega
                        have hsp := hspPt₁ x hltSp
                        simp only [(hv0.2.2.1 x hEq.symm).2, or_true, ho0, and_self, ↓reduceIte] at hsp
                        have hspF := hunspJ₁ x hxJ ho₁
                        rw [hsp] at hspF; cases hspF
                  rcases hreachG l hrG₁ with hge | hrf | hra | hss | hnum
                  · omega
                  · exact (hfaPair (j + 1) vj avj ftj (hTailGet j vj avj ftj hgj)).2.2.1 haJ₀ hftJ₀ hactF hneSrcF l hfl hrf
                  · exact (hargs.2 (j + 1) 0 vj av0 avj aav0 ftj aFoot0 (by omega)
                      (hTailMap j vj avj ftj hgj) (by simp)).2 haJ₀ hftJ₀ hactA hneSrcA l hfl hra
                  · exact hnotSS hss
                  · exact hnotNum₁ hnum
              obtain ⟨hnoV2, hokRun2⟩ := ih (B_a := B₁) (fuel := n) (Frame := Frame₁) happsRest
                (Sim_add_staticStr hsim₁) hst₁ hstat₁F hFlt₁ hnk' hnsp'
                (VSim_add_staticStr hVSimG) hDisjG hNrfG hNvG (fun h => by cases h)
                htailArgs₁ hgaPair
                (fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂ =>
                  hArgsSrc (i + 1) (j + 1) v₁ v₂ av₁ av₂ ft₁ ft₂ x
                    (hTailGet i v₁ av₁ ft₁ hg₁) (hTailGet j v₂ av₂ ft₂ hg₂) hs₁ hs₂)
                hEnvNrf₁ (fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁)
              refine ⟨hnoV2, fun rv st' B' hok2 => ?_⟩
              obtain ⟨resFoot, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
                hpresF₂, hpresEnv₂, hpresNum₂, honceSh₂, hssf₂,
                hsim₂, hEnvNrf₂, hVSim₂, hDisj₂, hNrf₂, hNv₂, hLive₂⟩ := hokRun2 rv st' B' hok2
              have hpresEnvAll : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap := by
                intro i b' ab hsc hbi habi hne ha'
                have hvB := ((hsim.2.2.2.2.2.1 i b' ab hsc hbi habi).2 hne).2
                have ha₁ := ActiveVal.of_AStateLe hok₁ hle₁' (hszSt₁ ▸ hvB.2.1)
                  (fun x hx => hszSt₁ ▸ (hvB.2.2.1 x hx).1) ha'
                have hp1 := hpresEnv₁ i b' ab hsc hbi habi hne ha₁
                have hp2 := hpresEnv₂ i b' ab hsc hbi habi hne ha'
                exact hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
              exact ⟨resFoot, by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
                hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
                hpresF₁.trans (hpresF₂.mono fun l hF => Or.inl hF),
                hpresEnvAll,
                fun l o n ho hc => hpresNum₂ l o n (hpresNum₁ l o n ho hc) hc,
                honceSh₁.trans honceSh₂,
                StaticStrFresh.trans hsz₁ (hpresF₂.mono fun _ hss => Or.inr hss) hssf₁ hssf₂,
                Sim_shrink_frame (fun _ h => Or.inl h) hsim₂,
                hEnvNrf₂,
                VSim_shrink_frame (fun _ h => Or.inl h) hVSim₂,
                hDisj₂, hNrf₂, hNv₂, hLive₂⟩

/-! ## 4. Argument-List Extension, PAP/Direct Call Bridges (`ArgListOk_push`, `papVal_bridge`, `ctor_pap_bridge`, `prim_pap_bridge`, `callResult_*_bridge`) -/

/-- Source-tracking invariant on an abstract value produced between `σ₀` and `σ₁`:
if `av.src = some x`, either `x` is a non-erased in-scope binding in `aenv` with matching
`onceOnly` and `deps`, or `x` was freshly allocated at `≥ σ₀.st.size` and if `@once`, any
old `@once` dependency `< σ₀.st.size` carried by `av` has already been marked `spent`. -/
def SrcOk (Scope : Nat → Prop) (aenv : List ABnd) (σ₀ σ₁ : AState) (av : AVal) : Prop :=
  ∀ x, av.src = some x →
    (∃ i ab, Scope i ∧ aenv[i]? = some ab ∧ ab.mode ≠ .erased ∧ ab.id = x ∧
      av.onceOnly = ab.val.onceOnly ∧ ∀ d, d ∈ av.deps ↔ d ∈ (effVal ab).deps) ∨
    (σ₀.st.size ≤ x ∧
      (σ₁.once[x]? = some true → ∀ d ∈ av.deps, d < σ₀.st.size →
        σ₁.once[d]? = some true → σ₁.spent[d]? = some true))

/-- Every evaluated argument in `args` whose `src` matches an in-scope binding has matching
`onceOnly` and `deps`. -/
def PrefixSrcOk (Scope : Nat → Prop) (aenv : List ABnd)
    (args : List (Option (Val × AVal × (Nat → Prop)))) : Prop :=
  ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
    args[i]? = some (some (v, av, ft)) →
    ∀ x, av.src = some x →
      ∀ (k : Nat) (ab : ABnd), Scope k → aenv[k]? = some ab → ab.mode ≠ .erased →
        ab.id = x → av.onceOnly = ab.val.onceOnly ∧ ∀ d, d ∈ av.deps ↔ d ∈ (effVal ab).deps

/-- Pairwise `src` consistency across evaluated arguments in `args`. -/
def ArgsSrcOk (args : List (Option (Val × AVal × (Nat → Prop)))) : Prop :=
  ∀ (i j : Nat) (v₁ v₂ : Val) (av₁ av₂ : AVal) (ft₁ ft₂ : Nat → Prop) (x : Nat),
    args[i]? = some (some (v₁, av₁, ft₁)) →
    args[j]? = some (some (v₂, av₂, ft₂)) →
    av₁.src = some x → av₂.src = some x → av₁.onceOnly = av₂.onceOnly

theorem SrcOk_none {Scope : Nat → Prop} {aenv : List ABnd} {σ₀ σ₁ : AState} {av : AVal}
    (h : av.src = none) : SrcOk Scope aenv σ₀ σ₁ av := fun _ hs => by rw [h] at hs; cases hs

theorem SrcOk_weaken_cls {Scope : Nat → Prop} {aenv : List ABnd} {σ₀ σ₁ : AState} {av : AVal} {c : Cls}
    (h : SrcOk Scope aenv σ₀ σ₁ av) : SrcOk Scope aenv σ₀ σ₁ { av with cls := c } := h

/-- Lift `SrcOk` across a monotone state extension `σ₁ → σ₂` given `av.src = some x → x < σ₁.st.size`. -/
theorem SrcOk_step_le_lt {Scope : Nat → Prop} {aenv : List ABnd} {σ₀ σ₁ σ₂ : AState} {av : AVal}
    (hok₁ : AStateOk σ₁) (hle₀₁ : AStateLe σ₀ σ₁) (hle₁₂ : AStateLe σ₁ σ₂)
    (hsrcLt : ∀ x, av.src = some x → x < σ₁.st.size)
    (h : SrcOk Scope aenv σ₀ σ₁ av) : SrcOk Scope aenv σ₀ σ₂ av := by
  intro x hs
  rcases h x hs with hL | ⟨hge, hsp⟩
  · exact Or.inl hL
  · refine Or.inr ⟨hge, fun ho₂ d hd hlt hod₂ => ?_⟩
    have hx1 : x < σ₁.once.size := by rw [← hok₁.1]; exact hsrcLt x hs
    have hltOnce : d < σ₁.once.size := by have := hle₀₁.1; have := hok₁.1; omega
    have hltSp : d < σ₁.spent.size := by have := hle₀₁.1; have := hok₁.2.1; omega
    have ho₁ : σ₁.once[x]? = some true := by rw [← hle₁₂.2.2.2.1 x hx1]; exact ho₂
    have hod₁ : σ₁.once[d]? = some true := by rw [← hle₁₂.2.2.2.1 d hltOnce]; exact hod₂
    exact hle₁₂.2.2.2.2 d hltSp (hsp ho₁ d hd hlt hod₁)

/-- Extending `(Frame, NoKill, NoSpend)` with a selected subset `Pick` of an `ArgListOk` prefix
that remains active at `σ₁` preserves `Sim`, `NoKillOk`, and `NoSpendOk`. -/
theorem Sim_extend_frame_of_args {P : Prog} {ext : ExternOracle} {B : Nat} {st₀ : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₀ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    (Pick : Nat → Prop)
    (hle : AStateLe σ₀ σ₁)
    (hsim : Sim P ext B st₀ Frame NoKill NoSpend Scope env aenv σ₀ I envFoot)
    (hst₀ : StOk P ext B st₀)
    (hFlt : ∀ l, Frame l → l < st₀.heap.objs.size)
    (hnk₁ : NoKillOk NoKill σ₁) (hnsp₁ : NoSpendOk NoSpend σ₁)
    (hargs : ArgListOk P ext B st₀ Frame NoKill NoSpend Scope env aenv σ₀ I envFoot
      Forbid BadReg BadDep args) :
    let Frame' : Nat → Prop := fun l =>
      Frame l ∨ StaticStrLoc st₀ l ∨
      ∃ k v av ft, Pick k ∧ args[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧ Reach st₀.heap v l
    let NoKill' : Nat → Prop := fun d =>
      d < σ₀.st.size ∧ (NoKill d ∨
        ∃ k v av ft, Pick k ∧ args[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧ d ∈ av.deps)
    let NoSpend' : Nat → Prop := fun d =>
      d < σ₀.st.size ∧ (NoSpend d ∨
        ∃ k v av ft, Pick k ∧ args[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧
          IsOnceSrc σ₁ av ∧ av.src = some d ∧ σ₀.once[d]? = some true)
    (∀ l, StaticStrLoc st₀ l → Frame' l) ∧
    (∀ l, Frame' l → l < st₀.heap.objs.size) ∧
    NoKillOk NoKill' σ₁ ∧
    NoSpendOk NoSpend' σ₁ ∧
    Sim P ext B st₀ Frame' NoKill' NoSpend' Scope env aenv σ₀ I envFoot := by
  intro Frame' NoKill' NoSpend'
  have hok₀ := hsim.2.1
  have hFlt' : ∀ l, Frame' l → l < st₀.heap.objs.size := by
    rintro l (hF | hss | ⟨k, v, av, ft, _, hgk, ha₁, hrv⟩)
    · exact hFlt l hF
    · exact StOk_staticStrLoc_lt hst₀ hss
    · have hv := (hargs.1 k v av ft hgk).1
      have ha₀ := ActiveVal.of_AStateLe hok₀ hle hv.2.1 (fun x hx => (hv.2.2.1 x hx).1) ha₁
      exact (hv.2.2.2.2 ha₀).1.1.reach_lt_size hrv
  have hnk' : NoKillOk NoKill' σ₁ := by
    rintro d ⟨_, hnk | ⟨k, v, av, ft, _, _, ha₁, hd⟩⟩
    · exact hnk₁ d hnk
    · exact (ha₁.1 d hd).2
  have hnsp' : NoSpendOk NoSpend' σ₁ := by
    rintro d ⟨hlt, hnsp | ⟨k, v, av, ft, _, hgk, ha₁, his₁, hsrc, ho₀⟩⟩
    · exact hnsp₁ d hnsp
    · have hv := (hargs.1 k v av ft hgk).1
      have hd : d ∈ av.deps := (hv.2.2.1 d hsrc).2
      have hltO : d < σ₀.once.size := by rw [← hok₀.1]; exact hlt
      have ho₁ : σ₁.once[d]? = some true := by rw [hle.2.2.2.1 d hltO]; exact ho₀
      have hspF := ha₁.2 his₁ d hd ho₁
      rw [hspF]; decide
  refine ⟨fun _ h => Or.inr (Or.inl h), hFlt', hnk', hnsp',
    hsim.1, hok₀, hsim.2.2.1, hsim.2.2.2.1, hsim.2.2.2.2.1, ?_, ?_⟩
  · intro i b ab hsc hbi habi
    obtain ⟨hmode, hrest⟩ := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
    refine ⟨hmode, fun hne => ?_⟩
    obtain ⟨honce, hvB⟩ := hrest hne
    refine ⟨honce, hvB.1, hvB.2.1, hvB.2.2.1, hvB.2.2.2.1, fun haB => ?_⟩
    obtain ⟨hbv, hdou, hcf, hnv, hpl, hoo, hos, htr⟩ := hvB.2.2.2.2 haB
    have habLt : ab.id < σ₀.st.size := hsim.2.2.2.1 i ab habi
    refine ⟨hbv, hdou, hcf, hnv, hpl, ?_, ?_, ?_⟩
    · intro hooB
      obtain ⟨h1, h2, h3, h4⟩ := hoo hooB
      refine ⟨h1, fun hnkB l hfl hFr => ?_, h3, h4⟩
      have hnotNK : ¬ NoKill' ab.id := hnkB ab.id (by simp [effVal])
      rcases hFr with hF | hss | ⟨k, v, av, ft, hpk, hgk, ha₁, hrv⟩
      · exact h2 (fun x hx => by
          dsimp [effVal] at hx; cases hx
          exact fun hnk => hnotNK ⟨habLt, Or.inl hnk⟩) l hfl hF
      · exact (h1 l hfl).2.1 hss
      · obtain ⟨hvK, hdisjK, _, _⟩ := hargs.1 k v av ft hgk
        have ha₀ := ActiveVal.of_AStateLe hok₀ hle hvK.2.1 (fun x hx => (hvK.2.2.1 x hx).1) ha₁
        have hneSrc : av.src ≠ some ab.id := fun hs =>
          hnotNK ⟨habLt, Or.inr ⟨k, v, av, ft, hpk, hgk, ha₁, (hvK.2.2.1 ab.id hs).2⟩⟩
        exact (hdisjK i b ab hsc hbi habi hne).2.2.2.1 haB (Or.inl hooB) ha₀ hneSrc l hfl hrv
    · intro hisB
      obtain ⟨h1, h2, h3⟩ := hos hisB
      refine ⟨h1, fun hnspB l hfl hFr => ?_, h3⟩
      have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
      have hoB : σ₀.once[ab.id]? = some true := by
        obtain ⟨id, hs, ho⟩ := hisB; dsimp [effVal] at hs; cases hs; exact ho
      have hnotNSp : ¬ NoSpend' ab.id := hnspB ab.id habMem hoB
      rcases hFr with hF | hss | ⟨k, v, av, ft, hpk, hgk, ha₁, hrv⟩
      · exact h2 (fun d hd hod hnsp => by
          have hdLt := hvB.2.1 d hd
          exact hnspB d hd hod ⟨hdLt, Or.inl hnsp⟩) l hfl hF
      · exact (h1 l hfl).2.1 hss
      · obtain ⟨hvK, hdisjK, _, _⟩ := hargs.1 k v av ft hgk
        have ha₀ := ActiveVal.of_AStateLe hok₀ hle hvK.2.1 (fun x hx => (hvK.2.2.1 x hx).1) ha₁
        have hneSrc : av.src ≠ some ab.id := fun hs =>
          hnotNSp ⟨habLt, Or.inr ⟨k, v, av, ft, hpk, hgk, ha₁,
            ⟨ab.id, hs, by rw [hle.2.2.2.1 ab.id (by rw [← hok₀.1]; exact habLt)]; exact hoB⟩,
            hs, hoB⟩⟩
        exact (hdisjK i b ab hsc hbi habi hne).2.2.2.1 haB (Or.inr ⟨hisB, haB.2 hisB⟩) ha₀ hneSrc l hfl hrv
    · intro htrB
      have htrB₀ : Transferable σ₀ NoKill (effVal ab) :=
        ⟨htrB.1, htrB.2.1, htrB.2.2.1, htrB.2.2.2.1, fun d hd =>
          ⟨(htrB.2.2.2.2 d hd).1, fun hnk => (htrB.2.2.2.2 d hd).2 ⟨hvB.2.1 d hd, Or.inl hnk⟩⟩⟩
      obtain ⟨hotf, hown⟩ := htr htrB₀
      refine ⟨hotf, fun l hor => ⟨fun hFr => ?_, (hown l hor).2⟩⟩
      rcases hFr with hF | hss | ⟨k, v, av, ft, hpk, hgk, ha₁, hrv⟩
      · exact (hown l hor).1 hF
      · exact (hown l hor).2 hss
      · obtain ⟨hvK, hdisjK, _, _⟩ := hargs.1 k v av ft hgk
        have ha₀ := ActiveVal.of_AStateLe hok₀ hle hvK.2.1 (fun x hx => (hvK.2.2.1 x hx).1) ha₁
        have hdd : ∀ d, d ∈ (effVal ab).deps → ¬ (d ∈ av.deps) := fun d hd hdk =>
          (htrB.2.2.2.2 d hd).2 ⟨hvB.2.1 d hd, Or.inr ⟨k, v, av, ft, hpk, hgk, ha₁, hdk⟩⟩
        exact (hdisjK i b ab hsc hbi habi hne).2.1 haB htrB₀ ha₀ hdd l hor hrv
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    obtain ⟨d1, d2⟩ := hsim.2.2.2.2.2.2 i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    refine ⟨fun ha₁ htr₁ ha₂ hdd l hor hr₂ => ?_, d2⟩
    have hv₁ := ((hsim.2.2.2.2.2.1 i b₁ ab₁ hsi hb₁ hab₁).2 hne₁).2
    have htr₁₀ : Transferable σ₀ NoKill (effVal ab₁) :=
      ⟨htr₁.1, htr₁.2.1, htr₁.2.2.1, htr₁.2.2.2.1, fun d hd =>
        ⟨(htr₁.2.2.2.2 d hd).1, fun hnk => (htr₁.2.2.2.2 d hd).2 ⟨hv₁.2.1 d hd, Or.inl hnk⟩⟩⟩
    exact d1 ha₁ htr₁₀ ha₂ hdd l hor hr₂

/-- Appending `none` (an erased argument) preserves `ArgListOk`, `PrefixSrcOk`, and `ArgsSrcOk`. -/
theorem ArgListOk_push_none {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hpreSrc : PrefixSrcOk Scope aenv args)
    (hargsSrc : ArgsSrcOk args) :
    ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep (args ++ [none]) ∧
    PrefixSrcOk Scope aenv (args ++ [none]) ∧
    ArgsSrcOk (args ++ [none]) := by
  have hget : ∀ (i : Nat) (x : Val × AVal × (Nat → Prop)),
      (args ++ [none])[i]? = some (some x) → args[i]? = some (some x) := by
    intro i x hg
    by_cases hi : i < args.length
    · rw [List.getElem?_append_left hi] at hg; exact hg
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg
      cases hd : i - args.length with
      | zero => rw [hd] at hg; cases hg
      | succ k => rw [hd] at hg; simp at hg
  exact ⟨⟨fun i v av ft hg => hargs.1 i v av ft (hget i (v, av, ft) hg),
    fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ =>
      hargs.2 i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij (hget i _ hg₁) (hget j _ hg₂)⟩,
    fun i v av ft hg => hpreSrc i v av ft (hget i _ hg),
    fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ =>
      hargsSrc i j v₁ v₂ av₁ av₂ ft₁ ft₂ x (hget i _ hg₁) (hget j _ hg₂)⟩

/-- Extending an evaluated `ArgListOk` prefix by one newly evaluated argument `(v₂, av₂, ft₂)`
produced by an abstract term step `σ₀ → σ₁` and concrete `MS` computation `m`, given a
universally quantified step hypothesis over `(Frame', NoKill', NoSpend', Forbid', BadReg', BadDep')`. -/
theorem ArgListOk_push {P : Prog} {ext : ExternOracle} {B_in : Nat} {st₀ : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₀ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {av₂ : AVal} {m : MS Val}
    (hle : AStateLe σ₀ σ₁)
    (hsim : Sim P ext B_in st₀ Frame NoKill NoSpend Scope env aenv σ₀ I envFoot)
    (hst₀ : StOk P ext B_in st₀)
    (hFlt : ∀ l, Frame l → l < st₀.heap.objs.size)
    (hnk₁ : NoKillOk NoKill σ₁) (hnsp₁ : NoSpendOk NoSpend σ₁)
    (hEnvNrf₀ : EnvNoReachForbid st₀ Scope env aenv σ₀ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st₀.heap.objs.size)
    (hBadDepLive : ∀ d, BadDep d → σ₁.st[d]? = some .live)
    (hargs : ArgListOk P ext B_in st₀ Frame NoKill NoSpend Scope env aenv σ₀ I envFoot
      Forbid BadReg BadDep args)
    (hpreSrc : PrefixSrcOk Scope aenv args)
    (hargsSrc : ArgsSrcOk args)
    (hStep : ∀ (Frame' NoKill' NoSpend' Forbid' BadReg' BadDep' : Nat → Prop),
      Sim P ext B_in st₀ Frame' NoKill' NoSpend' Scope env aenv σ₀ I envFoot →
      (∀ l, StaticStrLoc st₀ l → Frame' l) →
      (∀ l, Frame' l → l < st₀.heap.objs.size) →
      NoKillOk NoKill' σ₁ →
      NoSpendOk NoSpend' σ₁ →
      EnvNoReachForbid st₀ Scope env aenv σ₀ Forbid' BadReg' BadDep' →
      (∀ l, Forbid' l → l < st₀.heap.objs.size) →
      (∀ d, BadDep' d → σ₁.st[d]? = some .live) →
      (∀ k, m.run (st₀, B_in) ≠ .error (.violation k)) ∧
      ∀ v₂ st₁ B₁, m.run (st₀, B_in) = .ok (v₂, (st₁, B₁)) →
        ∃ ft₂ : Nat → Prop,
          B₁ ≤ B_in ∧
          StOk P ext B₁ st₁ ∧
          st₀.heap.objs.size ≤ st₁.heap.objs.size ∧
          st₀.heap.nextCap ≤ st₁.heap.nextCap ∧
          st₁.regions = st₀.regions ∧
          st₀.nextRegion ≤ st₁.nextRegion ∧
          ArrayExtends st₀.statics st₁.statics ∧
          ArrayExtends st₀.strs st₁.strs ∧
          PreservesLocs Frame' st₀.heap st₁.heap ∧
          PreservesActiveEnv Scope env aenv σ₁ st₀.heap st₁.heap ∧
          (∀ (l : Nat) (o : Obj) (n : Nat), st₀.heap.objs[l]? = some o → o.cell = .num n → st₁.heap.objs[l]? = some o) ∧
          PreservesOnceShell st₀.heap st₁.heap ∧
          StaticStrFresh st₀ st₁ ∧
          Sim P ext B₁ st₁ Frame' NoKill' NoSpend' Scope env aenv σ₁ I envFoot ∧
          EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid' BadReg' BadDep' ∧
          VSim P ext B₁ st₁ Frame' NoKill' NoSpend' σ₁ I ft₂ av₂ v₂ ∧
          ValEnvDisj P st₁ NoKill' Scope env aenv σ₁ envFoot ft₂ av₂ v₂ ∧
          (ActiveVal σ₁ av₂ → NoReachForbid st₁ Forbid' BadReg' BadDep' av₂ v₂) ∧
          (ValidDeps σ₁ av₂.deps → av₂.cls ≠ .val → ValBaseOk st₁ v₂ ∧ NonValSafe st₁.heap v₂) ∧
          SrcOk Scope aenv σ₀ σ₁ av₂) :
    (∀ k, m.run (st₀, B_in) ≠ .error (.violation k)) ∧
    ∀ v₂ st₁ B₁, m.run (st₀, B_in) = .ok (v₂, (st₁, B₁)) →
      ∃ ft₂ : Nat → Prop,
        B₁ ≤ B_in ∧
        StOk P ext B₁ st₁ ∧
        st₀.heap.objs.size ≤ st₁.heap.objs.size ∧
        st₀.heap.nextCap ≤ st₁.heap.nextCap ∧
        st₁.regions = st₀.regions ∧
        st₀.nextRegion ≤ st₁.nextRegion ∧
        ArrayExtends st₀.statics st₁.statics ∧
        ArrayExtends st₀.strs st₁.strs ∧
        PreservesLocs Frame st₀.heap st₁.heap ∧
        PreservesActiveEnv Scope env aenv σ₁ st₀.heap st₁.heap ∧
        (∀ (l : Nat) (o : Obj) (n : Nat), st₀.heap.objs[l]? = some o → o.cell = .num n → st₁.heap.objs[l]? = some o) ∧
        PreservesOnceShell st₀.heap st₁.heap ∧
        StaticStrFresh st₀ st₁ ∧
        Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot ∧
        EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep ∧
        ArgListOk P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot
          Forbid BadReg BadDep (args ++ [some (v₂, av₂, ft₂)]) ∧
        PrefixSrcOk Scope aenv (args ++ [some (v₂, av₂, ft₂)]) ∧
        ArgsSrcOk (args ++ [some (v₂, av₂, ft₂)]) := by
  have hok₀ := hsim.2.1
  -- Call #1: extended frame covering all active prefix items
  obtain ⟨hssAll, hFltAll, hnkAll, hnspAll, hsimAll⟩ :=
    Sim_extend_frame_of_args (fun _ => True) hle hsim hst₀ hFlt hnk₁ hnsp₁ hargs
  obtain ⟨hnoV, hokAll⟩ := hStep _ _ _ Forbid BadReg BadDep
    hsimAll hssAll hFltAll hnkAll hnspAll hEnvNrf₀ hForbidLt hBadDepLive
  refine ⟨hnoV, fun v₂ st₁ B₁ hm => ?_⟩
  obtain ⟨ft₂, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
    hpresAll, hpresEnv₁, hpresNum₁, honce₁, hssf₁,
    hsimAll₁, hEnvNrf₁, hv₂All, hdisj₂All, hNrf₂, hNv₂, hSrc₂⟩ := hokAll v₂ st₁ B₁ hm
  have hpresF₁ : PreservesLocs Frame st₀.heap st₁.heap :=
    hpresAll.mono fun _ h => Or.inl h
  have hpresSS₁ : PreservesLocs (StaticStrLoc st₀) st₀.heap st₁.heap :=
    hpresAll.mono fun _ h => Or.inr (Or.inl h)
  -- Call #2: base `(Frame, NoKill, NoSpend)` (add `StaticStrLoc st₀` to `Frame` to satisfy `hStep`)
  obtain ⟨hssBase, hFltBase, hnkBase, hnspBase, hsimBase⟩ :=
    Sim_extend_frame_of_args (fun _ => False) hle hsim hst₀ hFlt hnk₁ hnsp₁ hargs
  obtain ⟨_, hokBase⟩ := hStep _ _ _ Forbid BadReg BadDep
    hsimBase hssBase hFltBase hnkBase hnspBase hEnvNrf₀ hForbidLt hBadDepLive
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hsimBase₁, _, hv₂Base, hdisj₂Base, _, _, _⟩ := hokBase v₂ st₁ B₁ hm
  have hok₁ := hsimBase₁.2.1
  have hrf₁ : RegsFuture st₀ st₁ := RegsFuture.same_regions hnr₁ hr₁
  -- Step `Sim` to original `(Frame, NoKill, NoSpend)`
  have hsim₁ : Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot :=
    Sim_step (by omega) hle hok₁ hsimAll₁.2.2.1 hrf₁ honce₁ hssf₁
      (fun _ _ _ h => h) hpresEnv₁ hsim
  -- Helper: prefix preservation from `hpresAll`
  have hpresArg : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
      args[i]? = some (some (v, av, ft)) → ActiveVal σ₁ av →
      PreservesLocs (Reach st₀.heap v) st₀.heap st₁.heap :=
    fun i v av ft hgi ha₁ => hpresAll.mono fun l hr => Or.inr (Or.inr ⟨i, v, av, ft, trivial, hgi, ha₁, hr⟩)
  -- Step `args` to `(st₁, σ₁)`
  have hargs₁ : ArgListOk P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot
      Forbid BadReg BadDep args :=
    ArgListOk_step (by omega) hok₀ hle hrf₁ honce₁ hssf₁ hstat₁ hstr₁ hpresSS₁
      (fun _ _ _ h => h) (Sim_deps_lt hsim) hsim.2.2.2.1 hpresEnv₁ hpresArg hpresNum₁ hargs
  -- Lift `hv₂All` to `VSim` at `(Frame, NoKill, NoSpend)` using `ft₂`
  have htrBaseImp : ∀ {av : AVal}, (∀ d ∈ av.deps, d < σ₀.st.size → True) →
      Transferable σ₁ NoKill av →
      Transferable σ₁ (fun d => d < σ₀.st.size ∧ (NoKill d ∨
        ∃ (k : Nat) (v : Val) (av' : AVal) (ft' : Nat → Prop),
          False ∧ args[k]? = some (some (v, av', ft')) ∧ ActiveVal σ₁ av' ∧ d ∈ av'.deps)) av := by
    intro av _ htr
    refine ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1, fun d hd => ⟨(htr.2.2.2.2 d hd).1, ?_⟩⟩
    rintro ⟨_, hnk | ⟨_, _, _, _, hf, _⟩⟩
    · exact (htr.2.2.2.2 d hd).2 hnk
    · exact hf
  have hv₂ : VSim P ext B₁ st₁ Frame NoKill NoSpend σ₁ I ft₂ av₂ v₂ := by
    refine ⟨hv₂All.1, hv₂All.2.1, hv₂All.2.2.1, hv₂All.2.2.2.1, fun ha₂ => ?_⟩
    obtain ⟨hbv, hdou, hcf, hnv, hpl, hoo, hos, _⟩ := hv₂All.2.2.2.2 ha₂
    refine ⟨hbv, hdou, hcf, hnv, hpl, ?_, ?_, ?_⟩
    · intro hoo₂
      obtain ⟨h1, h2, h3, h4⟩ := hoo hoo₂
      refine ⟨h1, fun hnk₂ l hfl hFl => ?_, h3, h4⟩
      cases hs₂ : av₂.src with
      | none => exact h2 (fun _ hs => by rw [hs₂] at hs; cases hs) l hfl (Or.inl hFl)
      | some x =>
        rcases hSrc₂ x hs₂ with ⟨k, ab, hsk, habk, hnek, rfl, hooEq, _⟩ | ⟨hge, _⟩
        · have hkLt : k < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp habk).1
          have ⟨bk, hbk⟩ : ∃ bk, env[k]? = some bk := ⟨env[k], List.getElem?_eq_getElem hkLt⟩
          have hflEnv : envFoot k l := (hdisj₂All k bk ab hsk hbk habk hnek).2.2.2.2.1 ha₂ (Or.inl hoo₂) hs₂ l hfl
          have hvk := ((hsim₁.2.2.2.2.2.1 k bk ab hsk hbk habk).2 hnek).2
          have haK : ActiveVal σ₁ (effVal ab) := by
            have hxDep : ab.id ∈ av₂.deps := (hv₂All.2.2.1 ab.id hs₂).2
            refine ⟨fun d hd => ?_, fun hisK => ?_⟩
            · have hd₂ : d ∈ av₂.deps := by
                rcases hSrc₂ ab.id hs₂ with ⟨k', ab', _, habk', _, hid', _, hdeps⟩ | ⟨hge', _⟩
                · have hkEq := hsim.2.2.2.2.1 k k' ab ab' habk habk' hid'.symm
                  subst hkEq; rw [habk] at habk'; cases habk'; exact (hdeps d).mpr hd
                · have := hsim.2.2.2.1 k ab habk; omega
              exact ha₂.1 d hd₂
            · obtain ⟨id, hsK, hoK⟩ := hisK; dsimp [effVal] at hsK; cases hsK
              have his₂ : IsOnceSrc σ₁ av₂ := ⟨ab.id, hs₂, hoK⟩
              intro d hd hoD
              have hd₂ : d ∈ av₂.deps := by
                rcases hSrc₂ ab.id hs₂ with ⟨k', ab', _, habk', _, hid', _, hdeps⟩ | ⟨hge', _⟩
                · have hkEq := hsim.2.2.2.2.1 k k' ab ab' habk habk' hid'.symm
                  subst hkEq; rw [habk] at habk'; cases habk'; exact (hdeps d).mpr hd
                · have := hsim.2.2.2.1 k ab habk; omega
              exact ha₂.2 his₂ d hd₂ hoD
          have hooK : (effVal ab).onceOnly = true := hooEq.symm.trans hoo₂
          exact ((hvk.2.2.2.2 haK).2.2.2.2.2.1 hooK).2.1
            (fun y hy => by dsimp [effVal] at hy; cases hy; exact hnk₂ ab.id hs₂) l hflEnv hFl
        · exact h2 (fun y hy => by rw [hs₂] at hy; cases hy; intro ⟨hlt, _⟩; omega) l hfl (Or.inl hFl)
    · intro his₂
      obtain ⟨h1, h2, h3⟩ := hos his₂
      refine ⟨h1, fun hnsp₂ l hfl hFl => ?_, h3⟩
      obtain ⟨x, hs₂, hox⟩ := his₂
      rcases hSrc₂ x hs₂ with ⟨k, ab, hsk, habk, hnek, rfl, _, hdepsEq⟩ | ⟨hge, hspOld⟩
      · have hkLt : k < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp habk).1
        have ⟨bk, hbk⟩ : ∃ bk, env[k]? = some bk := ⟨env[k], List.getElem?_eq_getElem hkLt⟩
        have hflEnv : envFoot k l :=
          (hdisj₂All k bk ab hsk hbk habk hnek).2.2.2.2.1 ha₂ (Or.inr ⟨⟨ab.id, hs₂, hox⟩, ha₂.2 ⟨ab.id, hs₂, hox⟩⟩) hs₂ l hfl
        have hvk := ((hsim₁.2.2.2.2.2.1 k bk ab hsk hbk habk).2 hnek).2
        have hisK : IsOnceSrc σ₁ (effVal ab) := ⟨ab.id, by simp [effVal], hox⟩
        have haK : ActiveVal σ₁ (effVal ab) :=
          ⟨fun d hd => ha₂.1 d ((hdepsEq d).mpr hd),
           fun _ d hd hoD => ha₂.2 ⟨ab.id, hs₂, hox⟩ d ((hdepsEq d).mpr hd) hoD⟩
        exact ((hvk.2.2.2.2 haK).2.2.2.2.2.2.1 hisK).2.1
          (fun d hd hoD => hnsp₂ d ((hdepsEq d).mpr hd) hoD) l hflEnv hFl
      · refine h2 (fun d hd hoD ⟨hlt, _⟩ => ?_) l hfl (Or.inl hFl)
        have hspT := hspOld hox d hd hlt hoD
        have hspF := ha₂.2 ⟨x, hs₂, hox⟩ d hd hoD
        rw [hspT] at hspF; cases hspF
    · intro htr₂
      obtain ⟨hotf, hown⟩ := (hv₂Base.2.2.2.2 ha₂).2.2.2.2.2.2.2 (htrBaseImp (fun _ _ _ => trivial) htr₂)
      exact ⟨hotf, fun l hor => ⟨fun hF => (hown l hor).1 (Or.inl hF), (hown l hor).2⟩⟩
  -- Lift `hdisj₂All` to `ValEnvDisj` at `NoKill` using `ft₂`
  have hdisj₂ : ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot ft₂ av₂ v₂ := by
    intro i b ab hsc hbi habi hne
    obtain ⟨_, _, d3, d4, d5, d6, d7⟩ := hdisj₂All i b ab hsc hbi habi hne
    obtain ⟨b1, b2, _, _, _, _, _⟩ := hdisj₂Base i b ab hsc hbi habi hne
    exact ⟨fun ha₂ htr₂ haB hdd l hor hrB => b1 ha₂ (htrBaseImp (fun _ _ _ => trivial) htr₂) haB hdd l hor hrB,
      fun haB htrB ha₂ hdd l hor hr₂ => b2 haB (htrBaseImp (fun _ _ _ => trivial) htrB) ha₂ hdd l hor hr₂,
      d3, d4, d5, d6, d7⟩
  -- Helper: `PrefixSrcOk` and `ArgsSrcOk` for `args ++ [some (v₂, av₂, ft₂)]`
  have hpreSrc' : PrefixSrcOk Scope aenv (args ++ [some (v₂, av₂, ft₂)]) := by
    intro i v av ft hg x hs k ab hsk habk hnek hid
    by_cases hi : i < args.length
    · rw [List.getElem?_append_left hi] at hg
      exact hpreSrc i v av ft hg x hs k ab hsk habk hnek hid
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg
      cases hd : i - args.length with
      | zero =>
        rw [hd] at hg; cases hg
        rcases hSrc₂ x hs with ⟨k', ab', _, habk', _, hid', hooEq, hdepsEq⟩ | ⟨hge, _⟩
        · have hkEq := hsim.2.2.2.2.1 k k' ab ab' habk habk' (hid.trans hid'.symm)
          subst hkEq; rw [habk] at habk'; cases habk'; exact ⟨hooEq, hdepsEq⟩
        · have := hsim.2.2.2.1 k ab habk; omega
      | succ m => rw [hd] at hg; simp at hg
  have hargsSrc' : ArgsSrcOk (args ++ [some (v₂, av₂, ft₂)]) := by
    have hpair : ∀ (i : Nat) (v₁ : Val) (av₁ : AVal) (ft₁ : Nat → Prop) (x : Nat),
        args[i]? = some (some (v₁, av₁, ft₁)) → av₁.src = some x → av₂.src = some x → av₁.onceOnly = av₂.onceOnly := by
      intro i v₁ av₁ ft₁ x hgi hs₁ hs₂
      have hv₁ := (hargs.1 i v₁ av₁ ft₁ hgi).1
      have hlt : x < σ₀.st.size := (hv₁.2.2.1 x hs₁).1
      rcases hSrc₂ x hs₂ with ⟨k, ab, hsk, habk, hnek, hid, hoo₂, _⟩ | ⟨hge, _⟩
      · exact (hpreSrc i v₁ av₁ ft₁ hgi x hs₁ k ab hsk habk hnek hid).1.trans hoo₂.symm
      · omega
    intro i j v₁ v₂' av₁ av₂' ft₁ ft₂' x hg₁ hg₂ hs₁ hs₂
    by_cases hi : i < args.length <;> by_cases hj : j < args.length
    · rw [List.getElem?_append_left hi] at hg₁; rw [List.getElem?_append_left hj] at hg₂
      exact hargsSrc i j v₁ v₂' av₁ av₂' ft₁ ft₂' x hg₁ hg₂ hs₁ hs₂
    · rw [List.getElem?_append_left hi] at hg₁; rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hg₂
      cases hd : j - args.length with
      | zero => rw [hd] at hg₂; cases hg₂; exact hpair i v₁ av₁ ft₁ x hg₁ hs₁ hs₂
      | succ m => rw [hd] at hg₂; simp at hg₂
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg₁; rw [List.getElem?_append_left hj] at hg₂
      cases hd : i - args.length with
      | zero => rw [hd] at hg₁; cases hg₁; exact (hpair j v₂' av₂' ft₂' x hg₂ hs₂ hs₁).symm
      | succ m => rw [hd] at hg₁; simp at hg₁
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg₁
      rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hg₂
      cases hd₁ : i - args.length with
      | succ m => rw [hd₁] at hg₁; simp at hg₁
      | zero =>
        rw [hd₁] at hg₁; cases hg₁
        cases hd₂ : j - args.length with
        | succ m => rw [hd₂] at hg₂; simp at hg₂
        | zero => rw [hd₂] at hg₂; cases hg₂; rfl
  -- Pairwise disjointness between prefix `i` and new `v₂`
  have hPairOldNew : ∀ (i : Nat) (v₁ : Val) (av₁ : AVal) (ft₁ : Nat → Prop),
      args[i]? = some (some (v₁, av₁, ft₁)) →
      ((ActiveVal σ₁ av₁ → Transferable σ₁ NoKill av₁ → ActiveVal σ₁ av₂ →
        (∀ d, d ∈ av₁.deps → ¬ (d ∈ av₂.deps)) → ∀ l, OwnReach P st₁.heap v₁ l → ¬ Reach st₁.heap v₂ l) ∧
       (ActiveVal σ₁ av₁ → FootActive σ₁ av₁ → ActiveVal σ₁ av₂ →
        (av₁.src = none ∨ av₁.src ≠ av₂.src) → ∀ l, ft₁ l → ¬ Reach st₁.heap v₂ l)) := by
    intro i v₁ av₁ ft₁ hgi
    obtain ⟨hv₁₀, hdisj₁₀, _, _⟩ := hargs.1 i v₁ av₁ ft₁ hgi
    obtain ⟨hv₁₁, hdisj₁₁, _, _⟩ := hargs₁.1 i v₁ av₁ ft₁ hgi
    constructor
    · -- Clause 1: `OwnReach` of `v₁` vs `Reach` of `v₂` via `Forbid := OwnReach P st₀.heap v₁`, `BadDep := (· ∈ av₁.deps)`
      intro ha₁ htr₁ ha₂ hdd l hor₁ hr₂
      have hp₁ := hpresArg i v₁ av₁ ft₁ hgi ha₁
      have ha₁₀ := ActiveVal.of_AStateLe hok₀ hle hv₁₀.2.1 (fun x hx => (hv₁₀.2.2.1 x hx).1) ha₁
      have htr₁₀ := Transferable.of_AStateLe hok₀ hle hv₁₀.2.1 (fun x hx => (hv₁₀.2.2.1 x hx).1) (fun _ h => h) htr₁
      have hor₀ : OwnReach P st₀.heap v₁ l := (OwnReach_congr hp₁ l).mp hor₁
      have hEnvF : EnvNoReachForbid st₀ Scope env aenv σ₀ (OwnReach P st₀.heap v₁) (fun _ => False) (fun d => d ∈ av₁.deps) := by
        intro k bk ab hsk hbk habk hnek haK _ hdepsK l' hrK _ _ hor'
        exact (hdisj₁₀ k bk ab hsk hbk habk hnek).1 ha₁₀ htr₁₀ haK
          (fun d hd hdk => hdepsK d hdk hd) l' hor' hrK
      have hForbLt' : ∀ l', OwnReach P st₀.heap v₁ l' → l' < st₀.heap.objs.size :=
        fun l' hor' => (hv₁₀.2.2.2.2 ha₁₀).1.1.reach_lt_size (OwnReach_toReach hor')
      obtain ⟨_, hokC1⟩ := hStep _ _ _ (OwnReach P st₀.heap v₁) (fun _ => False) (fun d => d ∈ av₁.deps)
        hsimBase hssBase hFltBase hnkBase hnspBase hEnvF hForbLt' (fun d hd => (htr₁.2.2.2.2 d hd).1)
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNrfC1, _, _⟩ := hokC1 v₂ st₁ B₁ hm
      have hnotSS₁ : ¬ StaticStrLoc st₁ l := ((hv₁₁.2.2.2.2 ha₁).2.2.2.2.2.2.2 htr₁).2 l hor₁ |>.2
      have hnotNum₁ : ¬ NumLoc st₁.heap l := OwnReach_not_numLoc hor₁
      exact hNrfC1 ha₂ (fun _ _ h => h) (fun d hd2 hd1 => hdd d hd1 hd2) l hr₂ hnotSS₁ hnotNum₁ hor₀
    · -- Clause 2: `ft₁` vs `Reach` of `v₂`
      intro ha₁ hft₁ ha₂ hneSrc l hfl hr₂
      have hp₁ := hpresArg i v₁ av₁ ft₁ hgi ha₁
      have ha₁₀ := ActiveVal.of_AStateLe hok₀ hle hv₁₀.2.1 (fun x hx => (hv₁₀.2.2.1 x hx).1) ha₁
      have hft₁₀ := FootActive.of_AStateLe hok₀ hle hv₁₀.2.1 (fun x hx => (hv₁₀.2.2.1 x hx).1) hft₁
      by_cases hInEnv : ∃ k ab, Scope k ∧ aenv[k]? = some ab ∧ ab.mode ≠ .erased ∧ av₁.src = some ab.id
      · obtain ⟨k, ab, hsk, habk, hnek, hsEq⟩ := hInEnv
        have hkLt : k < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp habk).1
        have ⟨bk, hbk⟩ : ∃ bk, env[k]? = some bk := ⟨env[k], List.getElem?_eq_getElem hkLt⟩
        have hflEnv : envFoot k l := (hdisj₁₁ k bk ab hsk hbk habk hnek).2.2.2.2.1 ha₁ hft₁ hsEq l hfl
        have hne₂ : av₂.src ≠ some ab.id := fun hs₂ => by
          rcases hneSrc with h1 | h2
          · rw [h1] at hsEq; cases hsEq
          · exact h2 (hsEq.trans hs₂.symm)
        obtain ⟨hooEq, hdepsEq⟩ := hpreSrc i v₁ av₁ ft₁ hgi ab.id hsEq k ab hsk habk hnek rfl
        have haK : ActiveVal σ₁ (effVal ab) :=
          ⟨fun d hd => ha₁.1 d ((hdepsEq d).mpr hd),
           fun hisK d hd hoD => ha₁.2 (by
             obtain ⟨id, h1, h2⟩ := hisK; dsimp [effVal] at h1; cases h1; exact ⟨ab.id, hsEq, h2⟩)
             d ((hdepsEq d).mpr hd) hoD⟩
        have hftK : FootActive σ₁ (effVal ab) := by
          rcases hft₁ with hoo₁ | ⟨⟨id, hs1, ho1⟩, hunsp₁⟩
          · exact Or.inl (hooEq.symm.trans hoo₁)
          · rw [hsEq] at hs1; cases hs1
            have hisK : IsOnceSrc σ₁ (effVal ab) := ⟨ab.id, by simp [effVal], ho1⟩
            exact Or.inr ⟨hisK, haK.2 hisK⟩
        exact (hdisj₂ k bk ab hsk hbk habk hnek).2.2.2.1 haK hftK ha₂ hne₂ l hflEnv hr₂
      · -- `av₁.src` does not match any in-scope binding: `Forbid := ft₁`, `BadDep := False`!
        have hEnvF : EnvNoReachForbid st₀ Scope env aenv σ₀ ft₁ (fun _ => False) (fun _ => False) := by
          intro k bk ab hsk hbk habk hnek haK _ _ l' hrK _ _ hfl'
          have hne : av₁.src ≠ some ab.id := fun hs => hInEnv ⟨k, ab, hsk, habk, hnek, hs⟩
          exact (hdisj₁₀ k bk ab hsk hbk habk hnek).2.2.1 ha₁₀ hft₁₀ haK hne l' hfl' hrK
        have hftProp₀ : ∀ l', ft₁ l' → Reach st₀.heap v₁ l' ∧ ¬ StaticStrLoc st₀ l' ∧ ¬ NumLoc st₀.heap l' := by
          rcases hft₁₀ with hoo₁ | ⟨his₁, _⟩
          · exact ((hv₁₀.2.2.2.2 ha₁₀).2.2.2.2.2.1 hoo₁).1
          · exact ((hv₁₀.2.2.2.2 ha₁₀).2.2.2.2.2.2.1 his₁).1
        have hftProp₁ : Reach st₁.heap v₁ l ∧ ¬ StaticStrLoc st₁ l ∧ ¬ NumLoc st₁.heap l := by
          rcases hft₁ with hoo₁ | ⟨his₁, _⟩
          · exact ((hv₁₁.2.2.2.2 ha₁).2.2.2.2.2.1 hoo₁).1 l hfl
          · exact ((hv₁₁.2.2.2.2 ha₁).2.2.2.2.2.2.1 his₁).1 l hfl
        have hForbLt' : ∀ l', ft₁ l' → l' < st₀.heap.objs.size :=
          fun l' hfl' => (hv₁₀.2.2.2.2 ha₁₀).1.1.reach_lt_size (hftProp₀ l' hfl').1
        obtain ⟨_, hokC2⟩ := hStep _ _ _ ft₁ (fun _ => False) (fun _ => False)
          hsimBase hssBase hFltBase hnkBase hnspBase hEnvF hForbLt' (fun _ h => False.elim h)
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNrfC2, _, _⟩ := hokC2 v₂ st₁ B₁ hm
        exact hNrfC2 ha₂ (fun _ _ h => h) (fun _ _ h => h) l hr₂ hftProp₁.2.1 hftProp₁.2.2 hfl
  -- Pairwise disjointness between new `v₂` and prefix `i`
  have hPairNewOld : ∀ (i : Nat) (v₁ : Val) (av₁ : AVal) (ft₁ : Nat → Prop),
      args[i]? = some (some (v₁, av₁, ft₁)) →
      ((ActiveVal σ₁ av₂ → Transferable σ₁ NoKill av₂ → ActiveVal σ₁ av₁ →
        (∀ d, d ∈ av₂.deps → ¬ (d ∈ av₁.deps)) → ∀ l, OwnReach P st₁.heap v₂ l → ¬ Reach st₁.heap v₁ l) ∧
       (ActiveVal σ₁ av₂ → FootActive σ₁ av₂ → ActiveVal σ₁ av₁ →
        (av₂.src = none ∨ av₂.src ≠ av₁.src) → ∀ l, ft₂ l → ¬ Reach st₁.heap v₁ l)) := by
    intro i v₁ av₁ ft₁ hgi
    obtain ⟨hv₁₁, hdisj₁₁, _, _⟩ := hargs₁.1 i v₁ av₁ ft₁ hgi
    constructor
    · -- Clause 3: `OwnReach` of `v₂` vs `Reach` of `v₁` via single-item `Pick := (· = i)`
      intro ha₂ htr₂ ha₁ hdd l hor₂ hr₁
      have hp₁ := hpresArg i v₁ av₁ ft₁ hgi ha₁
      have hr₁₀ : Reach st₀.heap v₁ l := (Reach_congr hp₁ l).mp hr₁
      obtain ⟨hssI, hFltI, hnkI, hnspI, hsimI⟩ :=
        Sim_extend_frame_of_args (fun k => k = i) hle hsim hst₀ hFlt hnk₁ hnsp₁ hargs
      obtain ⟨_, hokC3⟩ := hStep _ _ _ (fun _ => False) (fun _ => False) (fun _ => False)
        hsimI hssI hFltI hnkI hnspI
        (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => False.elim h)
        (fun _ h => False.elim h) (fun _ h => False.elim h)
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv₂I, _, _, _, _⟩ := hokC3 v₂ st₁ B₁ hm
      have htr₂I : Transferable σ₁ (fun d => d < σ₀.st.size ∧ (NoKill d ∨
          ∃ k v av ft, k = i ∧ args[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧ d ∈ av.deps)) av₂ := by
        refine ⟨htr₂.1, htr₂.2.1, htr₂.2.2.1, htr₂.2.2.2.1, fun d hd => ⟨(htr₂.2.2.2.2 d hd).1, ?_⟩⟩
        rintro ⟨_, hnk | ⟨k, v, av, ft, rfl, hgk, _, hdk⟩⟩
        · exact (htr₂.2.2.2.2 d hd).2 hnk
        · rw [hgi] at hgk; cases hgk; exact hdd d hd hdk
      exact ((hv₂I.2.2.2.2 ha₂).2.2.2.2.2.2.2 htr₂I).2 l hor₂ |>.1
        (Or.inr (Or.inr ⟨i, v₁, av₁, ft₁, rfl, hgi, ha₁, hr₁₀⟩))
    · -- Clause 4: `ft₂` vs `Reach` of `v₁` (directly from Call #1 + `SrcOk`!)
      intro ha₂ hft₂ ha₁ hneSrc l hfl hr₁
      have hp₁ := hpresArg i v₁ av₁ ft₁ hgi ha₁
      have hr₁₀ : Reach st₀.heap v₁ l := (Reach_congr hp₁ l).mp hr₁
      rcases hft₂ with hoo₂ | ⟨his₂, hunsp₂⟩
      · cases hs₂ : av₂.src with
        | none =>
          exact ((hv₂All.2.2.2.2 ha₂).2.2.2.2.2.1 hoo₂).2.1
            (fun _ hs => by rw [hs₂] at hs; cases hs) l hfl
            (Or.inr (Or.inr ⟨i, v₁, av₁, ft₁, trivial, hgi, ha₁, hr₁₀⟩))
        | some x =>
          rcases hSrc₂ x hs₂ with ⟨k, ab, hsk, habk, hnek, rfl, hooEq, hdepsEq⟩ | ⟨hge, _⟩
          · have hkLt : k < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp habk).1
            have ⟨bk, hbk⟩ : ∃ bk, env[k]? = some bk := ⟨env[k], List.getElem?_eq_getElem hkLt⟩
            have hflEnv : envFoot k l := (hdisj₂ k bk ab hsk hbk habk hnek).2.2.2.2.1 ha₂ (Or.inl hoo₂) hs₂ l hfl
            have haK : ActiveVal σ₁ (effVal ab) :=
              ⟨fun d hd => ha₂.1 d ((hdepsEq d).mpr hd),
               fun hisK d hd hoD => ha₂.2 (by
                 obtain ⟨id, h1, h2⟩ := hisK; dsimp [effVal] at h1; cases h1; exact ⟨ab.id, hs₂, h2⟩)
                 d ((hdepsEq d).mpr hd) hoD⟩
            have hne₁ : av₁.src ≠ some ab.id := fun hs₁ => by
              rcases hneSrc with h1 | h2
              · rw [h1] at hs₂; cases hs₂
              · exact h2 (hs₂.trans hs₁.symm)
            exact (hdisj₁₁ k bk ab hsk hbk habk hnek).2.2.2.1 haK (Or.inl (hooEq.symm.trans hoo₂)) ha₁ hne₁ l hflEnv hr₁
          · exact ((hv₂All.2.2.2.2 ha₂).2.2.2.2.2.1 hoo₂).2.1
              (fun y hy => by rw [hs₂] at hy; cases hy; intro ⟨hlt, _⟩; omega) l hfl
              (Or.inr (Or.inr ⟨i, v₁, av₁, ft₁, trivial, hgi, ha₁, hr₁₀⟩))
      · obtain ⟨x, hs₂, hox⟩ := his₂
        rcases hSrc₂ x hs₂ with ⟨k, ab, hsk, habk, hnek, rfl, _, hdepsEq⟩ | ⟨hge, hspOld⟩
        · have hkLt : k < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp habk).1
          have ⟨bk, hbk⟩ : ∃ bk, env[k]? = some bk := ⟨env[k], List.getElem?_eq_getElem hkLt⟩
          have hflEnv : envFoot k l :=
            (hdisj₂ k bk ab hsk hbk habk hnek).2.2.2.2.1 ha₂ (Or.inr ⟨⟨ab.id, hs₂, hox⟩, hunsp₂⟩) hs₂ l hfl
          have hisK : IsOnceSrc σ₁ (effVal ab) := ⟨ab.id, by simp [effVal], hox⟩
          have haK : ActiveVal σ₁ (effVal ab) :=
            ⟨fun d hd => ha₂.1 d ((hdepsEq d).mpr hd),
             fun _ d hd hoD => hunsp₂ d ((hdepsEq d).mpr hd) hoD⟩
          have hne₁ : av₁.src ≠ some ab.id := fun hs₁ => by
            rcases hneSrc with h1 | h2
            · rw [h1] at hs₂; cases hs₂
            · exact h2 (hs₂.trans hs₁.symm)
          exact (hdisj₁₁ k bk ab hsk hbk habk hnek).2.2.2.1 haK (Or.inr ⟨hisK, haK.2 hisK⟩) ha₁ hne₁ l hflEnv hr₁
        · exact ((hv₂All.2.2.2.2 ha₂).2.2.2.2.2.2.1 ⟨x, hs₂, hox⟩).2.1
            (fun d hd hoD ⟨hlt, _⟩ => by
              have hspT := hspOld hox d hd hlt hoD
              have hspF := hunsp₂ d hd hoD
              rw [hspT] at hspF; cases hspF) l hfl
            (Or.inr (Or.inr ⟨i, v₁, av₁, ft₁, trivial, hgi, ha₁, hr₁₀⟩))
  -- Assemble final `ArgListOk`
  refine ⟨ft₂, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
    hpresF₁, hpresEnv₁, hpresNum₁, honce₁, hssf₁, hsim₁, hEnvNrf₁, ⟨?_, ?_⟩, hpreSrc', hargsSrc'⟩
  · intro i v av ft hg
    by_cases hi : i < args.length
    · rw [List.getElem?_append_left hi] at hg; exact hargs₁.1 i v av ft hg
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg
      cases hd : i - args.length with
      | zero => rw [hd] at hg; cases hg; exact ⟨hv₂, hdisj₂, hNrf₂, hNv₂⟩
      | succ m => rw [hd] at hg; simp at hg
  · intro i j v₁ v₂' av₁ av₂' ft₁ ft₂' hij hg₁ hg₂
    by_cases hi : i < args.length <;> by_cases hj : j < args.length
    · rw [List.getElem?_append_left hi] at hg₁; rw [List.getElem?_append_left hj] at hg₂
      exact hargs₁.2 i j v₁ v₂' av₁ av₂' ft₁ ft₂' hij hg₁ hg₂
    · rw [List.getElem?_append_left hi] at hg₁; rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hg₂
      cases hd : j - args.length with
      | zero => rw [hd] at hg₂; cases hg₂; exact hPairOldNew i v₁ av₁ ft₁ hg₁
      | succ m => rw [hd] at hg₂; simp at hg₂
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg₁; rw [List.getElem?_append_left hj] at hg₂
      cases hd : i - args.length with
      | zero => rw [hd] at hg₁; cases hg₁; exact hPairNewOld j v₂' av₂' ft₂' hg₂
      | succ m => rw [hd] at hg₁; simp at hg₁
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hg₁
      rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hg₂
      cases hd₁ : i - args.length with
      | succ m => rw [hd₁] at hg₁; simp at hg₁
      | zero =>
        cases hd₂ : j - args.length with
        | succ m => rw [hd₂] at hg₂; simp at hg₂
        | zero => omega

/-- If `bindAt P fuel s m .leaf v` succeeds with `m ≠ .erased`, every location reachable from `v`
is a `.num` cell in `st.heap`. -/
theorem bindAt_leaf_arg_numLoc {P : Prog} {fuel s : Nat} {m : BinderMode} {v : Val}
    {bnd : Bnd} {st st' : St}
    (hba : (bindAt P fuel s m .leaf v).run st = .ok (bnd, st'))
    (hne : m ≠ .erased) :
    ∀ l, Reach st.heap v l → NumLoc st.heap l := by
  have hmne : (m == .erased) = false := beq_false_of_ne hne
  unfold bindAt at hba
  simp only [hmne, Bool.false_eq_true, ↓reduceIte] at hba
  rw [M_bind_run] at hba
  cases hc : (conform .leaf v).run st with
  | error e => rw [hc] at hba; cases hba
  | ok p2 =>
    intro l hrl
    cases v with
    | imm i => cases hrl
    | ref loc cap t =>
      unfold conform at hc; rw [M_bind_run] at hc
      cases hn : (numOf? (.ref loc cap t)).run st with
      | error e => rw [hn] at hc; cases hc
      | ok pn =>
        rw [hn] at hc; dsimp only at hc
        cases ho : pn.1 with
        | none => rw [ho] at hc; cases hc
        | some n =>
          unfold numOf? at hn; rw [M_bind_run] at hn
          cases hobj : (obj loc).run st with
          | error e => rw [hobj] at hn; cases hn
          | ok po =>
            rw [hobj] at hn; dsimp only at hn
            unfold obj at hobj
            cases hg : st.heap.objs[loc]? with
            | none => simp [hg, stuckM, throw, throwThe, MonadExceptOf.throw] at hobj; cases hobj
            | some o =>
              simp [hg] at hobj
              obtain ⟨rfl, rfl⟩ := hobj
              cases hcell : o.cell with
              | num n' =>
                cases hrl with
                | here => exact ⟨o, n', hg, hcell⟩
                | step ho1 hm1 _ => rw [hg] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
              | ctor _ _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ | str _ =>
                by_cases hcap : o.cap = cap
                · simp [hcell, hcap] at hn; cases hn; cases ho
                · simp [hcell, hcap, violate, throw, throwThe, MonadExceptOf.throw] at hn; cases hn

/-- If `bindParamsM` succeeds under `bindParamsM_spec`'s hypotheses, any non-erased `.leaf`
parameter argument reaches only `.num` cells in `st.heap`. -/
theorem bindParamsM_leaf_arg_numLoc {P : Prog} {fuel s : Nat}
    {xs : List (Param × Val)} {env env' : List Bnd} {st st' : St}
    (hc : CapsOk st.heap)
    (hxs : ∀ (i : Nat) (p : Param) (v : Val), xs[i]? = some (p, v) →
      (p.mode ≠ .erased → DeepLive st.heap v ∧ AcyclicFrom st.heap v) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap v ∧ (p.mode.isBorrowed = false → OpenUnder st.regions [] v)))
    (hdisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      xs[i]? = some (pi, vi) → xs[j]? = some (pj, vj) →
      pi.mode.isUnique = true → pj.mode ≠ .erased →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l)
    (hbp : (bindParamsM P fuel s xs env).run st = .ok (env', st'))
    (i : Nat) (p : Param) (v : Val)
    (hi : xs[i]? = some (p, v)) (hne : p.mode ≠ .erased) (hleaf : p.cls = .leaf) :
    ∀ l, Reach st.heap v l → NumLoc st.heap l := by
  induction xs generalizing env st i with
  | nil => cases hi
  | cons pv rest ih =>
    rcases pv with ⟨p0, v0⟩
    unfold bindParamsM at hbp; rw [M_bind_run] at hbp
    cases hba : (bindAt P fuel s p0.mode p0.cls v0).run st with
    | error e => rw [hba] at hbp; cases hbp
    | ok pb =>
      rcases pb with ⟨b0, st₁⟩; rw [hba] at hbp; dsimp only at hbp
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rw [hleaf] at hba
        exact bindAt_leaf_arg_numLoc hba hne
      | succ i' =>
        simp only [List.getElem?_cons_succ] at hi
        have h0 := hxs 0 p0 v0 (by simp)
        rcases bindAt_spec (P := P) (fuel := fuel) (s := s) (m := p0.mode) (c := p0.cls) (v := v0)
          hc (fun hn => (h0.1 hn).1) (fun hn => (h0.1 hn).2) (fun hu => (h0.2 hu).1) (fun hu hb => (h0.2 hu).2 hb) with
          hstuck | hoof | ⟨b0', st₁', hba', _, hr₁, _, _, _, hsz₁, _, hc₁, hoss₁, hpres₁, _⟩
        · rw [hstuck] at hba; cases hba
        · rw [hoof] at hba; cases hba
        · rw [hba] at hba'; cases hba'
          have hpresRest : ∀ (k : Nat) (pk : Param) (vk : Val), rest[k]? = some (pk, vk) → pk.mode ≠ .erased →
              PreservesLocs (Reach st.heap vk) st.heap st₁.heap := by
            intro k pk vk hk hnek
            have hxk := (hxs (k + 1) pk vk hk).1 hnek
            exact hpres₁.mono fun l hr => ⟨hxk.1.reach_lt_size hr, fun hu hor =>
              hdisj 0 (k + 1) p0 pk v0 vk (by omega) (by simp) hk hu hnek l hor hr⟩
          have hxs₁ : ∀ (k : Nat) (pk : Param) (vk : Val), rest[k]? = some (pk, vk) →
              (pk.mode ≠ .erased → DeepLive st₁.heap vk ∧ AcyclicFrom st₁.heap vk) ∧
              (pk.mode.isUnique = true →
                OwnTreeFull P st₁.heap vk ∧ (pk.mode.isBorrowed = false → OpenUnder st₁.regions [] vk)) := by
            intro k pk vk hk
            have hxk := hxs (k + 1) pk vk hk
            refine ⟨fun hnek => ?_, fun hu => ?_⟩
            · have hp := hpresRest k pk vk hk hnek
              exact ⟨(DeepLive_congr hp).mpr (hxk.1 hnek).1, (AcyclicFrom_congr hp).mpr (hxk.1 hnek).2⟩
            · have hnek : pk.mode ≠ .erased := by
                cases hpm : pk.mode <;> rw [hpm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
              have hp := hpresRest k pk vk hk hnek
              exact ⟨(OwnTreeFull_congr hp).mpr (hxk.2 hu).1, fun hb => hr₁ ▸ (hxk.2 hu).2 hb⟩
          have hdisj₁ : ∀ (k₁ k₂ : Nat) (p₁ p₂ : Param) (v₁ v₂ : Val), k₁ ≠ k₂ →
              rest[k₁]? = some (p₁, v₁) → rest[k₂]? = some (p₂, v₂) →
              p₁.mode.isUnique = true → p₂.mode ≠ .erased →
              ∀ l, OwnReach P st₁.heap v₁ l → ¬ Reach st₁.heap v₂ l := by
            intro k₁ k₂ p₁ p₂ v₁ v₂ hne12 hk₁ hk₂ hu₁ hne₂ l hor₁ hr₂
            have hne₁ : p₁.mode ≠ .erased := by
              cases hpm : p₁.mode <;> rw [hpm] at hu₁ <;> simp [BinderMode.isUnique] at hu₁ ⊢
            have hp₁ := hpresRest k₁ p₁ v₁ hk₁ hne₁
            have hp₂ := hpresRest k₂ p₂ v₂ hk₂ hne₂
            exact hdisj (k₁ + 1) (k₂ + 1) p₁ p₂ v₁ v₂ (by omega) hk₁ hk₂ hu₁ hne₂ l
              ((OwnReach_congr hp₁ l).mp hor₁) ((Reach_congr hp₂ l).mp hr₂)
          have hpV := hpresRest i' p v hi hne
          intro l hrl
          have hnum₁ := ih hc₁ hxs₁ hdisj₁ hbp i' hi l ((Reach_congr hpV l).mpr hrl)
          exact (NumLoc_congr hpV hrl).mpr hnum₁

/-- Synchronizes the unified `ArgListOk` list `args` with concrete runtime arguments `vs`
and abstract `Option AVal` arguments `avs` (`none` corresponds to `.imm .irr` for erased positions). -/
def ArgsMatch (args : List (Option (Val × AVal × (Nat → Prop))))
    (vs : List Val) (avs : List (Option AVal)) : Prop :=
  args.length = vs.length ∧ args.length = avs.length ∧
  ∀ (i : Nat), match args[i]? with
    | some (some (v, av, _)) => vs[i]? = some v ∧ avs[i]? = some (some av)
    | some none => vs[i]? = some (Val.imm .irr) ∧ avs[i]? = some none
    | none => vs[i]? = none ∧ avs[i]? = none

theorem erasedAt_of_ifaceOf {d : RunDef} {ifc : Iface} (hifc : ifaceOf? d = some ifc) (i : Nat) :
    erasedAt d i = (ifc.params[i]?.map fun p => p.mode == .erased).getD false := by
  cases d <;> simp [ifaceOf?] at hifc <;> subst hifc <;> rfl

theorem captureTransfers_eq_isUnique (m : BinderMode) :
    captureTransfers m = m.isUnique := by
  cases m <;> rfl

theorem ArgsMatch_getElem_vs {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)}
    (hm : ArgsMatch args vs avs) {i : Nat} {v : Val} (hv : vs[i]? = some v) :
    (v = .imm .irr ∧ args[i]? = some none ∧ avs[i]? = some none) ∨
    (∃ av ft, args[i]? = some (some (v, av, ft)) ∧ avs[i]? = some (some av)) := by
  have hi := hm.2.2 i
  cases hg : args[i]? with
  | none => rw [hg] at hi; rw [hi.1] at hv; cases hv
  | some opt =>
    rw [hg] at hi
    cases opt with
    | none => rw [hi.1] at hv; cases hv; exact Or.inl ⟨rfl, rfl, hi.2⟩
    | some t =>
      rcases t with ⟨v', av, ft⟩
      rw [hi.1] at hv; cases hv
      exact Or.inr ⟨av, ft, rfl, hi.2⟩

theorem ArgsMatch_getElem_avs {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)}
    (hm : ArgsMatch args vs avs) {i : Nat} {av : AVal} (ha : avs[i]? = some (some av)) :
    ∃ v ft, args[i]? = some (some (v, av, ft)) ∧ vs[i]? = some v := by
  have hi := hm.2.2 i
  cases hg : args[i]? with
  | none => rw [hg] at hi; rw [hi.2] at ha; cases ha
  | some opt =>
    rw [hg] at hi
    cases opt with
    | none => rw [hi.2] at ha; cases ha
    | some t =>
      rcases t with ⟨v', av', ft⟩
      rw [hi.2] at ha; cases ha
      exact ⟨v', ft, rfl, hi.1⟩

/-- Bridge for `ACall.ifacePap`: simulates `makePap P fuel r ifc.params vs` against
`Runs (papVal ifc avs.toArray w) σ res σ'`, using `makePap_sound_once` + `pap_iface_funOk`. -/
theorem papVal_bridge {P : Prog} {ext : ExternOracle} {B B_call fuel : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {r : Ref} {d : RunDef} {ifc : Iface} {w : String}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {res : AVal}
    (hext : ExternOk P ext) (hih : FullIH P ext B) (hB : B_call ≤ B + 1)
    (hfind : P.find? r = some d) (hifc : ifaceOf? d = some ifc)
    (hlt : vs.length < ifc.params.size)
    (hmatch : ArgsMatch args vs avs)
    (hErased : ∀ i, i < avs.length → (avs[i]? = some none ↔ erasedAt d i = true))
    (hrun : Runs (papVal ifc avs.toArray w) σ res σ')
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hst : StOk P ext B_call st)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hnk' : NoKillOk NoKill σ') (_hnsp' : NoSpendOk NoSpend σ')
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hBadDepLive : ∀ x, BadDep x → σ'.st[x]? = some .live) :
    (∀ k, (makePap P fuel r ifc.params vs).run st ≠ .error (.violation k)) ∧
    ∀ rv st', (makePap P fuel r ifc.params vs).run st = .ok (rv, st') →
      ∃ resFoot : Nat → Prop,
        StOk P ext B_call st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧
        st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧
        ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
        (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        Sim P ext B_call st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
        EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
        VSim P ext B_call st' Frame NoKill NoSpend σ' I resFoot res rv ∧
        ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv ∧
        (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
        (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
        ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B_call st' rv) ∨ (IsOnceSrc σ' res ∧ SpentOnceSafe st'.heap rv)) ∧
        SrcOk Scope aenv σ σ' res := by
  have hok := hsim.2.1
  have hIok := hsim.2.2.1
  obtain ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hclsR, hownR, hsrcR, hskelR,
    hooIff, hperArg, hpairDisj, hdepsSub, hregsSub, hspPt, hstPt⟩ := Runs_papVal hok hrun
  have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
  have hAvsArrSz : avs.toArray.size = vs.length := by simp [hlenEq]
  -- Helper: non-erased param ↔ `some (some av)` in `avs`
  have hParamNonErased : ∀ (i : Nat) (p : Param) (v : Val),
      ifc.params[i]? = some p → vs[i]? = some v →
      (p.mode = .erased → v = .imm .irr ∧ args[i]? = some none ∧ avs[i]? = some none) ∧
      (p.mode ≠ .erased → ∃ av ft, args[i]? = some (some (v, av, ft)) ∧ avs[i]? = some (some av)) := by
    intro i p v hp hv
    have hiLt : i < avs.length := by rw [hlenEq]; exact (List.getElem?_eq_some_iff.mp hv).1
    have herEq : erasedAt d i = (p.mode == .erased) := by
      rw [erasedAt_of_ifaceOf hifc i, hp]; rfl
    rcases ArgsMatch_getElem_vs hmatch hv with ⟨rfl, hg, ha⟩ | ⟨av, ft, hg, ha⟩
    · have hpm : p.mode = .erased := by
        have h1 := (hErased i hiLt).mp ha
        rw [herEq] at h1; exact eq_of_beq h1
      exact ⟨fun _ => ⟨rfl, hg, ha⟩, fun hne => absurd hpm hne⟩
    · have hpm : p.mode ≠ .erased := by
        intro hEq
        have h1 : avs[i]? = some none := (hErased i hiLt).mpr (by rw [herEq, hEq]; rfl)
        rw [ha] at h1; cases h1
      exact ⟨fun hEq => absurd hEq hpm, fun _ => ⟨av, ft, hg, ha⟩⟩
  have hArgKilled : ∀ (i : Nat) (p : Param) (a : AVal),
      ifc.params[i]? = some p → avs[i]? = some (some a) →
      p.mode.isUnique = true → a.cls = .val → ∀ x ∈ a.deps, σ'.st[x]? = some .dead := by
    intro i p a hp ha hu hcv x hx
    have hct : captureTransfers p.mode = true := (captureTransfers_eq_isUnique p.mode).trans hu
    have ha' : avs.toArray[i]? = some (some a) := by simpa using ha
    have hvd := (hperArg i p a hp ha').1
    have h1 := hstPt x (hvd x hx).1
    have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal),
        ifc.params[i']? = some p' ∧ avs.toArray[i']? = some (some a') ∧
        captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps :=
      ⟨i, p, a, hp, ha', hct, hcv, hx⟩
    simp only [hex, ↓reduceIte] at h1; exact h1
  have hArgTr : ∀ (i : Nat) (p : Param) (v : Val) (a : AVal) (ft : Nat → Prop),
      ifc.params[i]? = some p → args[i]? = some (some (v, a, ft)) →
      p.mode.isUnique = true → a.cls = .val → Transferable σ NoKill a := by
    intro i p v a ft hp hg hu hcv
    have ha : avs[i]? = some (some a) := by have h1 := hmatch.2.2 i; rw [hg] at h1; exact h1.2
    have ha' : avs.toArray[i]? = some (some a) := by simpa using ha
    have hct : captureTransfers p.mode = true := (captureTransfers_eq_isUnique p.mode).trans hu
    obtain ⟨_, hoo, hnotOS, _, _, htrInfo, _⟩ := hperArg i p a hp ha'
    obtain ⟨hown, hlv, _⟩ := htrInfo hct hcv
    exact ⟨hcv, hown, hoo, hnotOS, fun x hx => ⟨hlv x hx, fun hnk => hnk' x hnk (hArgKilled i p a hp ha hu hcv x hx)⟩⟩
  -- Check `makePap_sound_once` hypotheses
  have hvsBase : ∀ v ∈ vs, ValBaseOk st v ∧ CtorFieldsOk P ext B_call st v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hgetV : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
    have hiP : i < ifc.params.size := Nat.lt_trans hi hlt
    have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hiP
    by_cases her : ifc.params[i].mode = .erased
    · obtain ⟨hEq, _, _⟩ := (hParamNonErased i _ _ hp hgetV).1 her
      rw [hEq]; exact ⟨ValBaseOk_imm st .irr, CtorFieldsOk_imm P ext B_call st .irr⟩
    · obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hgetV).2 her
      have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
      obtain ⟨hvd, _, hnotOS, _, _, _, _⟩ := hperArg i _ av hp ha'
      have hvSim := (hargs.1 i _ av ft hg).1
      have hact : ActiveVal σ av := ⟨hvd, fun his => False.elim (hnotOS his)⟩
      exact ⟨(hvSim.2.2.2.2 hact).1, (hvSim.2.2.2.2 hact).2.2.1⟩
  have huniqPap : ∀ (i : Nat) (v : Val), vs[i]? = some v →
      ((ifc.params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      NoOnceCell st.heap v ∧ OwnTreeFull P st.heap v ∧
      (((ifc.params[i]?.map Param.mode).getD BinderMode.many).isBorrowed = false → OpenUnder st.regions [] v) ∧
      ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l := by
    intro i v hv hu
    have hiLt : i < vs.length := (List.getElem?_eq_some_iff.mp hv).1
    have hiP : i < ifc.params.size := Nat.lt_trans hiLt hlt
    have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hiP
    simp only [hp, Option.map_some, Option.getD_some] at hu ⊢
    have hne : ifc.params[i].mode ≠ .erased := by
      cases hm : ifc.params[i].mode <;> rw [hm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
    obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hv).2 hne
    have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
    obtain ⟨hvd, hoo, hnotOS, _, _, htrInfo, _⟩ := hperArg i _ av hp ha'
    have hact : ActiveVal σ av := ⟨hvd, fun his => False.elim (hnotOS his)⟩
    obtain ⟨hvSim, _, _, hnv⟩ := hargs.1 i v av ft hg
    have hno := ((hvSim.2.2.2.2 hact).2.2.2.2.1 ⟨hnotOS, hoo⟩).1
    by_cases hcv : av.cls = .val
    · have htr := hArgTr i _ v av ft hp hg hu hcv
      obtain ⟨hotf, hown⟩ := (hvSim.2.2.2.2 hact).2.2.2.2.2.2.2 htr
      have hct : captureTransfers ifc.params[i].mode = true := (captureTransfers_eq_isUnique _).trans hu
      refine ⟨hno, hotf, fun hnb => ?_, fun l hor => (hown l hor).2⟩
      have hregs0 := (htrInfo hct hcv).2.2 hnb
      have hdou := (hvSim.2.2.2.2 hact).2.1
      rw [hregs0, Interp.regsOf_nil] at hdou
      exact hdou v (HeldBy.refl _ _)
    · have hnv' := (hnv hvd hcv).2
      exact ⟨hno, hnv'.ownTreeFull.1, fun _ => hnv'.deepOpenUnder_nil v (HeldBy.refl _ _),
        fun l hor => False.elim (hnv'.ownTreeFull.2 l hor)⟩
  have hdisjPap : ∀ (i j : Nat) (vi vj : Val), i ≠ j →
      vs[i]? = some vi → vs[j]? = some vj →
      ((ifc.params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l := by
    intro i j vi vj hij hvi hvj hui l hor hrj
    have hiP : i < ifc.params.size := Nat.lt_trans (List.getElem?_eq_some_iff.mp hvi).1 hlt
    have hjP : j < ifc.params.size := Nat.lt_trans (List.getElem?_eq_some_iff.mp hvj).1 hlt
    have hpi : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hiP
    have hpj : ifc.params[j]? = some ifc.params[j] := Array.getElem?_eq_getElem hjP
    simp only [hpi, Option.map_some, Option.getD_some] at hui
    have hnei : ifc.params[i].mode ≠ .erased := by
      cases hm : ifc.params[i].mode <;> rw [hm] at hui <;> simp [BinderMode.isUnique] at hui ⊢
    obtain ⟨ai, fti, hgi, hai⟩ := (hParamNonErased i _ _ hpi hvi).2 hnei
    by_cases hnej : ifc.params[j].mode = .erased
    · rw [(hParamNonErased j _ _ hpj hvj).1 hnej |>.1] at hrj; cases hrj
    · obtain ⟨aj, ftj, hgj, haj⟩ := (hParamNonErased j _ _ hpj hvj).2 hnej
      have hai' : avs.toArray[i]? = some (some ai) := by simpa using hai
      have haj' : avs.toArray[j]? = some (some aj) := by simpa using haj
      obtain ⟨hvdi, _, hnotOSi, _, _, _, _⟩ := hperArg i _ ai hpi hai'
      obtain ⟨hvdj, _, hnotOSj, _, _, _, _⟩ := hperArg j _ aj hpj haj'
      by_cases hcvi : ai.cls = .val
      · by_cases hcvj : aj.cls = .val
        · have hct : captureTransfers ifc.params[i].mode = true := (captureTransfers_eq_isUnique _).trans hui
          have hdd := hpairDisj i j _ _ ai aj hij hpi hai' hpj haj' hct hcvi (Or.inr hcvj)
          exact (hargs.2 i j vi vj ai aj fti ftj hij hgi hgj).1
            ⟨hvdi, fun h => False.elim (hnotOSi h)⟩ (hArgTr i _ vi ai fti hpi hgi hui hcvi)
            ⟨hvdj, fun h => False.elim (hnotOSj h)⟩ hdd l hor hrj
        · exact OwnReach_not_numLoc hor (((hargs.1 j vj aj ftj hgj).2.2.2 hvdj hcvj).2.reach_numLoc hrj)
      · exact ((hargs.1 i vi ai fti hgi).2.2.2 hvdi hcvi).2.ownTreeFull.2 l hor
  -- Apply `makePap_sound_once`
  rcases makePap_sound_once (P := P) (ext := ext) (B := B_call) (fuel := fuel)
    (r := r) (params := ifc.params) (vs := vs) hst hvsBase huniqPap hdisjPap with hOOF |
    ⟨rv, out, st', hrunPap, hr', hnr', hstat', hstr', hsz', hcap', hoss', hpres',
      honce', hssf', hst', hrvObj, houtSz, houtProps, hbvRv, _, hcfRv, hdouRv, hreachRv⟩
  · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
  · rw [hrunPap]
    refine ⟨(fun _ h => by cases h), fun rv' st'' hokPap => ?_⟩
    cases hokPap
    obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
    have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hr'
    have hIok' : InterpOk σ' st' I :=
      ⟨fun r' hr1 c' hc' => hnr' ▸ hIok.1 r' (hnr ▸ hr1) c' hc',
       fun c' hc' => by rw [hreg]; rw [hr'] at hc'; exact hIok.2 c' hc'⟩
    have hpresF : PreservesLocs Frame st.heap st'.heap := by
      refine hpres'.mono fun l hF => ⟨hFlt l hF, fun i v hv hu hor => ?_⟩
      have hiP : i < ifc.params.size := Nat.lt_trans (List.getElem?_eq_some_iff.mp hv).1 hlt
      have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hiP
      simp only [hp, Option.map_some, Option.getD_some] at hu
      have hne : ifc.params[i].mode ≠ .erased := by
        cases hm : ifc.params[i].mode <;> rw [hm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
      obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hv).2 hne
      have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
      obtain ⟨hvd, _, hnotOS, _, _, _, _⟩ := hperArg i _ av hp ha'
      by_cases hcv : av.cls = .val
      · exact (((hargs.1 i v av ft hg).1.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.2.2.2.2.2.2
          (hArgTr i _ v av ft hp hg hu hcv)).2 l hor |>.1 hF
      · exact ((hargs.1 i v av ft hg).2.2.2 hvd hcv).2.ownTreeFull.2 l hor
    have hpresEnv : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap := by
      intro k b ab hsc hbk habk hne haB'
      have hvB := ((hsim.2.2.2.2.2.1 k b ab hsc hbk habk).2 hne).2
      have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) haB'
      refine hpres'.mono fun l hrB => ⟨(hvB.2.2.2.2 haB₀).1.1.reach_lt_size hrB, fun i v hv hu hor => ?_⟩
      have hiP : i < ifc.params.size := Nat.lt_trans (List.getElem?_eq_some_iff.mp hv).1 hlt
      have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hiP
      simp only [hp, Option.map_some, Option.getD_some] at hu
      have hnei : ifc.params[i].mode ≠ .erased := by
        cases hm : ifc.params[i].mode <;> rw [hm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
      obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hv).2 hnei
      have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
      obtain ⟨hvd, _, hnotOS, _, _, _, _⟩ := hperArg i _ av hp ha'
      by_cases hcv : av.cls = .val
      · have hdd : ∀ x, x ∈ av.deps → ¬ (x ∈ (effVal ab).deps) := fun x hx hxb =>
          (haB'.1 x hxb).2 (hArgKilled i _ av hp ha hu hcv x hx)
        exact ((hargs.1 i v av ft hg).2.1 k b ab hsc hbk habk hne).1
          ⟨hvd, fun h => False.elim (hnotOS h)⟩ (hArgTr i _ v av ft hp hg hu hcv) haB₀ hdd l hor hrB
      · exact ((hargs.1 i v av ft hg).2.2.2 hvd hcv).2.ownTreeFull.2 l hor
    have hpresNum : ∀ (l : Nat) (o : Obj) (n : Nat),
        st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o := fun l o n ho hc =>
      (hpres' l ⟨(Array.getElem?_eq_some_iff.mp ho).1,
        fun _ _ _ _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hc⟩⟩).trans ho
    have hsim' : Sim P ext B_call st' Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
      Sim_step (Nat.le_refl _) hle' hok' hIok' hrf' honce' hssf' (fun _ _ _ h => h) hpresEnv hsim
    have hEnvNrf' : EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep :=
      EnvNoReachForbid_step hok hle' (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
        (hpresF.mono fun _ hss => hstat _ hss) hpresEnv hEnvNrf
    -- Define per-arg footprint `pFoot` and total `resFoot` matching `pap_iface_funOk`
    let pFoot : Nat → Nat → Prop := fun i l =>
      ∃ p w, ifc.params[i]? = some p ∧ out[i]? = some w ∧ p.mode.isUnique = true ∧ OwnReach P st'.heap w l
    let resFoot : Nat → Prop := fun l => ∃ i, i < out.size ∧ pFoot i l
    have hOutReachBack : ∀ (i : Nat) (v w : Val), vs[i]? = some v → out[i]? = some w →
        ∀ l, OwnReach P st'.heap w l ↔ OwnReach P st.heap v l := by
      intro i v w hv hw l
      obtain ⟨w', hw', hvsh, _, _, _, _⟩ := houtProps i v hv
      rw [hw] at hw'; cases hw'
      have hdlV : DeepLive st.heap v := (hvsBase v (List.mem_of_getElem? hv)).1.1
      exact ⟨fun hor => OwnReach_of_sameShapeOn_rev hdlV (hoss'.to_sameShapeOn _) (SameLoc.of_valSameShape hvsh) hor,
        fun hor => OwnReach_of_sameShapeOn (hoss'.to_sameShapeOn _) (SameLoc.of_valSameShape hvsh) hor⟩
    have hOutReachTo : ∀ (i : Nat) (v w : Val), vs[i]? = some v → out[i]? = some w →
        ∀ l, Reach st'.heap w l ↔ Reach st.heap v l := by
      intro i v w hv hw l
      obtain ⟨w', hw', hvsh, _, _, _, _⟩ := houtProps i v hv
      rw [hw] at hw'; cases hw'
      have hdlV : DeepLive st.heap v := (hvsBase v (List.mem_of_getElem? hv)).1.1
      exact ⟨fun hr => Reach_of_sameShapeOn_rev hdlV (hoss'.to_sameShapeOn _) (SameLoc.of_valSameShape hvsh) hr,
        fun hr => Reach_of_sameShapeOn (hoss'.to_sameShapeOn _) (SameLoc.of_valSameShape hvsh) hr⟩
    have hOutNoOnce : ∀ (i : Nat) (w : Val), out[i]? = some w → NoOnceCell st'.heap w := by
      intro i w hw
      have hiV : i < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hw).1
      have hv : vs[i]? = some vs[i] := List.getElem?_eq_getElem hiV
      obtain ⟨w', hw', hvsh, _, _, _, _⟩ := houtProps i vs[i] hv
      rw [hw] at hw'; cases hw'
      have hiP : i < ifc.params.size := Nat.lt_trans hiV hlt
      have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hiP
      by_cases her : ifc.params[i].mode = .erased
      · obtain ⟨hEq, _, _⟩ := (hParamNonErased i _ _ hp hv).1 her
        have hwIrr : w = .imm .irr := by rw [hEq] at hvsh; cases w <;> simp [ValSameShape] at hvsh; exact congrArg Val.imm hvsh.symm
        rw [hwIrr]; exact NoOnceCell_imm _ _
      · obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hv).2 her
        have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
        obtain ⟨hvd, hoo, hnotOS, _, _, _, _⟩ := hperArg i _ av hp ha'
        have hvSim := (hargs.1 i _ av ft hg).1
        have hact : ActiveVal σ av := ⟨hvd, fun h => False.elim (hnotOS h)⟩
        have hno0 := ((hvSim.2.2.2.2 hact).2.2.2.2.1 ⟨hnotOS, hoo⟩).1
        exact NoOnceCell_of_sameShape (hvSim.2.2.2.2 hact).1.1 (hoss'.to_sameShapeOn _)
          (SameLoc.of_valSameShape hvsh) hno0
    have hNoOnceRv : NoOnceCell st'.heap rv := by
      intro l o hr' ho' t' sp' hcell'
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell'
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp (by simpa [Cell.vals] using hm1))
        exact hOutNoOnce i out[i] (Array.getElem?_eq_getElem hi) l o hr2 ho' t' sp' hcell'
    have hFootEmptyOfFalse : res.onceOnly = false → ∀ i, i < out.size → ∀ l, ¬ pFoot i l := by
      intro hrf i hi l ⟨p, w, hp, hw, hu, hor⟩
      have hne : p.mode ≠ .erased := by cases hm : p.mode <;> rw [hm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
      have hiV : i < vs.length := houtSz ▸ hi
      obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i p vs[i] hp (List.getElem?_eq_getElem hiV)).2 hne
      have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
      have hrt : res.onceOnly = true := hooIff.mpr ⟨i, p, av, hp, ha', (captureTransfers_eq_isUnique p.mode).trans hu⟩
      rw [hrf] at hrt; cases hrt
    have hFootProps : ∀ i, i < out.size → ∀ l, pFoot i l →
        Reach st'.heap rv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l := by
      intro i hi l ⟨p, w, hp, hw, hu, hor⟩
      have hiV : i < vs.length := houtSz ▸ hi
      have hv : vs[i]? = some vs[i] := List.getElem?_eq_getElem hiV
      have hor0 : OwnReach P st.heap vs[i] l := (hOutReachBack i vs[i] w hv hw l).mp hor
      have hne : p.mode ≠ .erased := by cases hm : p.mode <;> rw [hm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
      obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i p vs[i] hp hv).2 hne
      have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
      obtain ⟨hvd, _, hnotOS, _, _, _, _⟩ := hperArg i p av hp ha'
      have hwMem : w ∈ out.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw)
      have hreach : Reach st'.heap rv l := by
        rw [hrvEq]; exact Reach.step hoNew (by simpa [Cell.vals] using hwMem) (OwnReach_toReach hor)
      by_cases hcv : av.cls = .val
      · have htr := hArgTr i p vs[i] av ft hp hg hu hcv
        obtain ⟨hnotF, hnotSS0⟩ := (((hargs.1 i vs[i] av ft hg).1.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.2.2.2.2.2.2 htr).2 l hor0
        have hnotSS' : ¬ StaticStrLoc st' l := fun hss => by
          rcases hssf' l hss with hge | hss0 | hnum
          · have hlt0 := ((hargs.1 i vs[i] av ft hg).1.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).1.1.reach_lt_size (OwnReach_toReach hor0)
            omega
          · exact hnotSS0 hss0
          · exact OwnReach_not_numLoc hor hnum
        exact ⟨hreach, hnotF, hnotSS', OwnReach_not_numLoc hor⟩
      · exact False.elim (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.ownTreeFull.2 l hor0)
    -- Apply `pap_iface_funOk`
    have hFunRv : FunOkAt P ext B_call st' res.skel res.onceOnly resFoot rv := by
      have hskEq : res.skel = ifaceSkel (ifc.params.toList.drop out.size) ifc.res ifc.resSkel := by
        rw [hskelR, hAvsArrSz, houtSz]
      rw [hskEq, hrvEq]
      refine pap_iface_funOk (B := B) (B_call := B_call) (onceOnly := res.onceOnly)
        (pOnce := fun _ => false) (pFoot := pFoot) hext hih hB hfind hifc (houtSz ▸ hlt) hoNew ?_ ?_ ?_ ?_
      · intro i w hw
        have hiV : i < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hw).1
        obtain ⟨w', hw', _, hbw, _, _, _⟩ := houtProps i vs[i] (List.getElem?_eq_getElem hiV)
        rw [hw] at hw'; cases hw'
        exact ⟨hbw, fun _ => hOutNoOnce i w hw⟩
      · intro i p w hp hw hne
        have hiV : i < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hw).1
        have hv : vs[i]? = some vs[i] := List.getElem?_eq_getElem hiV
        obtain ⟨w', hw', hvsh, hbw, _, _, hfunLift⟩ := houtProps i vs[i] hv
        rw [hw] at hw'; cases hw'
        obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i p vs[i] hp hv).2 hne
        have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
        obtain ⟨hvd, hoo, hnotOS, hadm, _, htrInfo, _⟩ := hperArg i p av hp ha'
        have hvSim := (hargs.1 i vs[i] av ft hg).1
        have hact : ActiveVal σ av := ⟨hvd, fun h => False.elim (hnotOS h)⟩
        have hfunW : FunOkAt P ext B_call st' p.skel false (fun _ => False) w :=
          FunOkAt_of_admits (Skel.admits_symm p.skel av.skel ▸ hadm)
            (hfunLift av.skel false (fun _ => False) ((hvSim.2.2.2.2 hact).2.2.2.2.1 ⟨hnotOS, hoo⟩).2.2)
        have hpfB : ∀ l, pFoot i l → Reach st'.heap w l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l := by
          rintro l ⟨p', w', hp', hw', hu', hor'⟩
          rw [hw] at hw'; cases hw'
          have hfp := hFootProps i (houtSz ▸ hiV) l ⟨p', w, hp', hw, hu', hor'⟩
          exact ⟨OwnReach_toReach hor', hfp.2.2.1, hfp.2.2.2⟩
        refine ⟨fun hoU => ?_, fun hnoU => ?_, fun hu => ?_, hpfB⟩
        · have hnotU : p.mode.isUnique = false := by
            cases hm : p.mode <;> rw [hm] at hoU <;> simp [BinderMode.usage, BinderMode.isUnique] at hoU ⊢
          have hpfE : ∀ l, ¬ pFoot i l := fun l ⟨p', _, hp', _, hu', _⟩ => by
            rw [hp] at hp'; cases hp'; rw [hnotU] at hu'; cases hu'
          exact ⟨FunOkAt_weaken_foot (Foot₁ := fun _ => False) (Foot₂ := pFoot i) (fun _ h => False.elim h) hfunW,
            hpfB, fun _ => hpfE⟩
        · exact ⟨hOutNoOnce i w hw, rfl, hfunW, fun hnu l ⟨p', _, hp', _, hu', _⟩ => by
            rw [hp] at hp'; cases hp'; rw [hnu] at hu'; cases hu'⟩
        · have hdlV : DeepLive st.heap vs[i] := (hvsBase vs[i] (List.mem_of_getElem? hv)).1.1
          have hotfW : OwnTreeFull P st'.heap w :=
            OwnTreeFull_of_sameShapeOn hdlV (hoss'.to_sameShapeOn _) (SameLoc.of_valSameShape hvsh)
              (huniqPap i vs[i] hv (by rw [hp]; exact hu)).2.1
          have hnbOpen : p.mode.isBorrowed = false → DeepOpenUnder st'.heap st'.regions [] w := by
            intro hnb
            by_cases hcv : av.cls = .val
            · have hct : captureTransfers p.mode = true := (captureTransfers_eq_isUnique p.mode).trans hu
              have hregs0 := (htrInfo hct hcv).2.2 hnb
              have hdou0 := (hvSim.2.2.2.2 hact).2.1
              rw [hregs0, Interp.regsOf_nil] at hdou0
              exact DeepOpenUnder_of_sameShapeOn hdlV (hoss'.to_sameShapeOn _) hvsh (hr' ▸ hdou0)
            · have hnv0 := ((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2
              exact (NonValSafe.of_sameShape (hoss'.to_sameShapeOn _) hvsh hbw.1.self.1 hnv0).deepOpenUnder_nil
          refine ⟨hotfW, hnbOpen,
            fun l hor => ⟨p, w, hp, hw, hu, hor⟩,
            fun l ⟨p', w', hp', hw', _, hor'⟩ => by rw [hw] at hw'; cases hw'; exact hor',
            fun hrf l hor => hFootEmptyOfFalse hrf i (houtSz ▸ hiV) l ⟨p, w, hp, hw, hu, hor⟩⟩
      · intro i p w hp hw her l ⟨p', _, hp', _, hu', _⟩
        rw [hp] at hp'; cases hp'; rw [her] at hu'; cases hu'
      · intro i j pi pj wi wj hij hpi hwi hpj hwj
        have hiV : i < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hwi).1
        have hjV : j < vs.length := houtSz ▸ (Array.getElem?_eq_some_iff.mp hwj).1
        have hvi : vs[i]? = some vs[i] := List.getElem?_eq_getElem hiV
        have hvj : vs[j]? = some vs[j] := List.getElem?_eq_getElem hjV
        have hnotUofO : pi.mode.usage = .once → pi.mode.isUnique = false := fun h => by
          cases hm : pi.mode <;> rw [hm] at h <;> simp [BinderMode.usage, BinderMode.isUnique] at h ⊢
        refine ⟨fun hui l hor hrj => ?_,
          (fun _ hoi l ⟨p', _, hp', _, hu', _⟩ => by rw [hpi] at hp'; cases hp'; rw [hnotUofO hoi] at hu'; cases hu'),
          (fun _ hoi _ l ⟨p', _, hp', _, hu', _⟩ => by rw [hpi] at hp'; cases hp'; rw [hnotUofO hoi] at hu'; cases hu')⟩
        exact hdisjPap i j vs[i] vs[j] hij hvi hvj (by rw [hpi]; exact hui) l
          ((hOutReachBack i vs[i] wi hvi hwi l).mp hor) ((hOutReachTo j vs[j] wj hvj hwj l).mp hrj)
    -- `DeepOpenUnder` of `rv`
    have hOpenRv : DeepOpenUnder st'.heap st'.regions (I.regsOf res.regs) rv := by
      refine hdouRv st'.regions (I.regsOf res.regs) fun v hv => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      have hgetV : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
      have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem (Nat.lt_trans hi hlt)
      by_cases her : ifc.params[i].mode = .erased
      · rw [(hParamNonErased i _ _ hp hgetV).1 her |>.1]; exact DeepOpenUnder_imm _ _ _ _
      · obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hgetV).2 her
        have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
        obtain ⟨hvd, _, hnotOS, _, hregsSubA, _, _⟩ := hperArg i _ av hp ha'
        have hvSim := (hargs.1 i vs[i] av ft hg).1
        have hdou := (hvSim.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.1
        rw [hr']
        exact hdou.mono fun c hc => by
          obtain ⟨r', hr', hc'⟩ := Interp.mem_regsOf.mp hc
          exact Interp.mem_regsOf.mpr ⟨r', hregsSubA r' hr', hc'⟩
    -- Build `VSim`, `ValEnvDisj`, `NoReachForbid`
    have hVSimRes : VSim P ext B_call st' Frame NoKill NoSpend σ' I resFoot res rv := by
      refine ⟨fun r' hr' => ?_, fun d' hd' => ?_,
        (fun _ hs => by rw [hsrcR] at hs; cases hs),
        (fun _ ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs), fun _ => ?_⟩
      · obtain ⟨i, p, a, _, ha', hrA⟩ := hregsSub r' hr'
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by simpa using ha')
        rw [hnr]; exact (hargs.1 i v a ft hg).1.1 r' hrA
      · obtain ⟨i, p, a, _, ha', _, hdA⟩ := hdepsSub d' hd'
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by simpa using ha')
        rw [hszSt]; exact (hargs.1 i v a ft hg).1.2.1 d' hdA
      · refine ⟨hbvRv, hOpenRv, hcfRv, fun _ hne => absurd hclsR hne,
          fun ⟨_, hooF⟩ => ⟨hNoOnceRv, fun l ⟨i, hi, hpf⟩ => hFootEmptyOfFalse hooF i hi l hpf,
            (by
              have hEqF : resFoot = fun _ => False := funext fun l => propext
                ⟨fun ⟨i, hi, hpf⟩ => hFootEmptyOfFalse hooF i hi l hpf, False.elim⟩
              rw [hooF, hEqF] at hFunRv; exact hFunRv)⟩,
          fun hooT => ⟨fun l ⟨i, hi, hpf⟩ => let h := hFootProps i hi l hpf; ⟨h.1, h.2.2.1, h.2.2.2⟩,
            fun _ l ⟨i, hi, hpf⟩ => (hFootProps i hi l hpf).2.1,
            (fun loc' cap' t' o' r' fs' h1 h2 h3 => by
              rw [hrvEq] at h1; cases h1; rw [hoNew] at h2; cases h2; cases h3),
            hooT ▸ hFunRv⟩,
          (fun ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs),
          (fun htr => by have h1 := htr.2.1; rw [hownR] at h1; cases h1)⟩
    have hDisjRes : ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv := by
      intro k b ab hsc hbk habk hne
      have hvB := ((hsim.2.2.2.2.2.1 k b ab hsc hbk habk).2 hne).2
      have hsrcB : ∀ x, (effVal ab).src = some x → x < σ.st.size := fun x hx => (hvB.2.2.1 x hx).1
      refine ⟨(fun _ htr => by have h1 := htr.2.1; rw [hownR] at h1; cases h1),
        fun haB' htrB' _ hdd l horB' hrRv' => ?_,
        fun _ _ haB' _ l ⟨i, hi, p, w, hp, hw, hu, horW⟩ hrB' => ?_,
        fun haB' hftB' _ _ l hfl hrRv' => ?_,
        (fun _ _ hs => by rw [hsrcR] at hs; cases hs),
        (fun hs => by rw [hsrcR] at hs; cases hs),
        (fun _ hs => by rw [hsrcR] at hs; cases hs)⟩
      · have hpB := hpresEnv k b ab hsc hbk habk hne haB'
        have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have htrB₀ := Transferable.of_AStateLe hok hle' hvB.2.1 hsrcB (fun _ h => h) htrB'
        have horB₀ := (OwnReach_congr hpB l).mp horB'
        have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size (OwnReach_toReach horB₀)
        rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
        · omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
          have hgetV : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
          have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem (Nat.lt_trans hi hlt)
          by_cases her : ifc.params[i].mode = .erased
          · rw [(hParamNonErased i _ _ hp hgetV).1 her |>.1] at hrv; cases hrv
          · obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hgetV).2 her
            have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
            obtain ⟨hvd, _, hnotOS, _, _, _, hdepsA⟩ := hperArg i _ av hp ha'
            have hdd' : ∀ x, x ∈ (effVal ab).deps → ¬ (x ∈ av.deps) := by
              intro x hx hxa
              by_cases hct : captureTransfers ifc.params[i].mode = true
              · by_cases hcv : av.cls = .val
                · exact (haB'.1 x hx).2 (hArgKilled i _ av hp ha ((captureTransfers_eq_isUnique _).symm.trans hct) hcv x hxa)
                · exact absurd (OwnReach_not_numLoc horB₀ (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.reach_numLoc hrv)) (fun h => h)
              · have hcf : captureTransfers ifc.params[i].mode = false := Bool.eq_false_iff.mpr hct
                exact hdd x hx (hdepsA hcf x hxa)
            exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.1
              haB₀ htrB₀ ⟨hvd, fun h => False.elim (hnotOS h)⟩ hdd' l horB₀ hrv
      · have hpB := hpresEnv k b ab hsc hbk habk hne haB'
        have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have hiV : i < vs.length := houtSz ▸ hi
        have hgetV : vs[i]? = some vs[i] := List.getElem?_eq_getElem hiV
        have hor0 := (hOutReachBack i vs[i] w hgetV hw l).mp horW
        have hnei : p.mode ≠ .erased := by cases hm : p.mode <;> rw [hm] at hu <;> simp [BinderMode.isUnique] at hu ⊢
        obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i p vs[i] hp hgetV).2 hnei
        have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
        obtain ⟨hvd, _, hnotOS, _, _, _, _⟩ := hperArg i p av hp ha'
        by_cases hcv : av.cls = .val
        · have hdd : ∀ x, x ∈ av.deps → ¬ (x ∈ (effVal ab).deps) := fun x hx hxb =>
            (haB'.1 x hxb).2 (hArgKilled i p av hp ha hu hcv x hx)
          exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).1
            ⟨hvd, fun h => False.elim (hnotOS h)⟩ (hArgTr i p vs[i] av ft hp hg hu hcv) haB₀ hdd l hor0
            ((Reach_congr hpB l).mp hrB')
        · exact ((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.ownTreeFull.2 l hor0
      · have hpB := hpresEnv k b ab hsc hbk habk hne haB'
        have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have hftB₀ := FootActive.of_AStateLe hok hle' hvB.2.1 hsrcB hftB'
        have hrB₀ : Reach st.heap b.val l := by
          rcases hftB₀ with hooB | ⟨hisB, _⟩
          · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.1 hooB).1 l hfl |>.1
          · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.2.1 hisB).1 l hfl |>.1
        have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size hrB₀
        rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
        · omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
          have hgetV : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
          have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem (Nat.lt_trans hi hlt)
          by_cases her : ifc.params[i].mode = .erased
          · rw [(hParamNonErased i _ _ hp hgetV).1 her |>.1] at hrv; cases hrv
          · obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hgetV).2 her
            have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
            obtain ⟨hvd, hoo, hnotOS, _, _, _, _⟩ := hperArg i _ av hp ha'
            have hneSrc : av.src ≠ some ab.id := by
              intro hsrc
              rcases hftB₀ with hooB | ⟨hisB, _⟩
              · have h1 := ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.2.2.2.2.1 hsrc hooB
                rw [hoo] at h1; cases h1
              · obtain ⟨id, hs1, ho1⟩ := hisB; dsimp [effVal] at hs1; cases hs1
                exact hnotOS ⟨ab.id, hsrc, ho1⟩
            exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.2.2.1
              haB₀ hftB₀ ⟨hvd, fun h => False.elim (hnotOS h)⟩ hneSrc l hfl hrv
    have hNrfRes : ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv := by
      intro _ hregsR hdepsR l hrRv' hnotSS' hnotNum' hForb
      have hltF := hForbidLt l hForb
      rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
      · omega
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
        have hgetV : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
        have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem (Nat.lt_trans hi hlt)
        by_cases her : ifc.params[i].mode = .erased
        · rw [(hParamNonErased i _ _ hp hgetV).1 her |>.1] at hrv; cases hrv
        · obtain ⟨av, ft, hg, ha⟩ := (hParamNonErased i _ _ hp hgetV).2 her
          have ha' : avs.toArray[i]? = some (some av) := by simpa using ha
          obtain ⟨hvd, _, hnotOS, _, hregsA, _, hdepsA⟩ := hperArg i _ av hp ha'
          have hnotSS0 : ¬ StaticStrLoc st l := fun hss =>
            hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
              (hpresF.mono fun _ h => hstat _ h) hss)
          have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hc⟩ =>
            hnotNum' ⟨o, n, hpresNum l o n ho hc, hc⟩
          by_cases hct : captureTransfers ifc.params[i].mode = true
          · by_cases hcv : av.cls = .val
            · have hdepsN : ∀ d ∈ av.deps, ¬ BadDep d := fun d hd hbd => by
                have hlv := hBadDepLive d hbd
                have hdead := hArgKilled i _ av hp ha ((captureTransfers_eq_isUnique _).symm.trans hct) hcv d hd
                rw [hdead] at hlv; cases hlv
              exact (hargs.1 i vs[i] av ft hg).2.2.1 ⟨hvd, fun h => False.elim (hnotOS h)⟩
                (fun r' hr' => hregsR r' (hregsA r' hr')) hdepsN l hrv hnotSS0 hnotNum0 hForb
            · exact hnotNum0 (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.reach_numLoc hrv)
          · have hcf : captureTransfers ifc.params[i].mode = false := Bool.eq_false_iff.mpr hct
            exact (hargs.1 i vs[i] av ft hg).2.2.1 ⟨hvd, fun h => False.elim (hnotOS h)⟩
              (fun r' hr' => hregsR r' (hregsA r' hr'))
              (fun d' hd' => hdepsR d' (hdepsA hcf d' hd')) l hrv hnotSS0 hnotNum0 hForb
    exact ⟨resFoot, hst', by omega, hcap', hr', hnr' ▸ Nat.le_refl _,
      hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
      hpresF, hpresEnv, hpresNum, honce', hssf', hsim', hEnvNrf',
      hVSimRes, hDisjRes, hNrfRes, (fun _ hne => absurd hclsR hne), Or.inl ⟨hbvRv, hcfRv⟩, SrcOk_none hsrcR⟩

/-- Bridge for `ACall.ctor` when under-applied (`vs.length < nP + fields.size`): simulates
`makePap P fuel r #[] vs` against `Runs (anCtor nP fields avs.toArray c) σ res σ'`. -/
theorem ctor_pap_bridge {P : Prog} {ext : ExternOracle} {B_call fuel : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {r ind : Ref} {cidx nP : Nat} {fields : Array Field} {c : Cls}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {res : AVal}
    (hfind : P.find? r = some (.ctor ind cidx nP fields))
    (hlt : vs.length < nP + fields.size)
    (hmatch : ArgsMatch args vs avs)
    (hrun : Runs (anCtor nP fields avs.toArray c) σ res σ')
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hst : StOk P ext B_call st)
    (_hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size) :
    (∀ k, (makePap P fuel r #[] vs).run st ≠ .error (.violation k)) ∧
    ∀ rv st', (makePap P fuel r #[] vs).run st = .ok (rv, st') →
      StOk P ext B_call st' ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      st'.regions = st.regions ∧
      st.nextRegion ≤ st'.nextRegion ∧
      ArrayExtends st.statics st'.statics ∧
      ArrayExtends st.strs st'.strs ∧
      PreservesLocs Frame st.heap st'.heap ∧
      PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
      (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      Sim P ext B_call st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
      EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
      VSim P ext B_call st' Frame NoKill NoSpend σ' I (fun _ => False) res rv ∧
      ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) res rv ∧
      (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
      (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
      ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B_call st' rv) ∨ (IsOnceSrc σ' res ∧ SpentOnceSafe st'.heap rv)) ∧
      SrcOk Scope aenv σ σ' res := by
  have hok := hsim.2.1
  have hIok := hsim.2.2.1
  have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
  have hltA : avs.toArray.size < nP + fields.size := by simpa [hlenEq] using hlt
  obtain ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, hPart, _⟩ := Runs_anCtor hok hrun
  obtain ⟨hclsR, hownR, hskelR, hooR, hsrcR, hperA, hdepsSub, hregsSub, _, _⟩ := hPart hltA
  have hvsOk : ∀ v ∈ vs, ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext B_call st v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
    · rw [hEq]; exact ⟨ValBaseOk_imm st .irr, NoOnceCell_imm _ _, CtorFieldsOk_imm P ext B_call st .irr⟩
    · have hmem : some av ∈ avs.toArray.toList := by simp; exact List.mem_of_getElem? ha
      obtain ⟨hvd, _, hoo, hnotOS, _, _⟩ := hperA av hmem
      have hvSim := (hargs.1 i vs[i] av ft hg).1
      have hact : ActiveVal σ av := ⟨hvd, fun h => False.elim (hnotOS h)⟩
      exact ⟨(hvSim.2.2.2.2 hact).1, ((hvSim.2.2.2.2 hact).2.2.2.2.1 ⟨hnotOS, hoo⟩).1,
        (hvSim.2.2.2.2 hact).2.2.1⟩
  have hnoU : ∀ (i : Nat), ((((#[] : Array Param)[i]?.map Param.mode).getD BinderMode.many).isUnique = true) → False := by
    intro i h; simp [BinderMode.isUnique] at h
  rcases makePap_sound (P := P) (ext := ext) (B := B_call) (fuel := fuel)
    (r := r) (params := #[]) (vs := vs) hst hvsOk
    (fun i _ _ hu => False.elim (hnoU i hu))
    (fun i _ _ _ _ _ _ hu => False.elim (hnoU i hu)) with hOOF |
    ⟨rv, out, st', hrunPap, hr', hnr', hstat', hstr', hsz', hcap', hoss', hpres',
      honce', hssf', hst', ⟨cap, hrvEq, hoNew⟩, houtSz, houtProps, hbvRv, hnoRv, hcfRv, hdouRv, hreachRv⟩
  · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
  · rw [hrunPap]
    refine ⟨(fun _ h => by cases h), fun rv' st'' hokPap => ?_⟩
    cases hokPap
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
      hpres'.mono fun l hltL => ⟨hltL, fun i _ _ hu => False.elim (hnoU i hu)⟩
    have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hr'
    have hIok' : InterpOk σ' st' I :=
      ⟨fun r' hr1 c' hc' => hnr' ▸ hIok.1 r' (hnr ▸ hr1) c' hc',
       fun c' hc' => by rw [hreg]; rw [hr'] at hc'; exact hIok.2 c' hc'⟩
    have hpresEnv : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap :=
      Sim_preserves_of_old hle' hpresOld hsim
    have hpresNum : ∀ (l : Nat) (o : Obj) (n : Nat),
        st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o :=
      fun l o n ho _ => (hpresOld l (Array.getElem?_eq_some_iff.mp ho).1).trans ho
    have hsim' : Sim P ext B_call st' Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
      Sim_step (Nat.le_refl _) hle' hok' hIok' hrf' honce' hssf' (fun _ _ _ h => h) hpresEnv hsim
    have hEnvNrf' : EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep :=
      EnvNoReachForbid_step hok hle' (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
        (hpresOld.mono fun _ hss => StOk_staticStrLoc_lt hst hss) hpresEnv hEnvNrf
    have hFunRv : FunOkAt P ext B_call st' .unknown false (fun _ => False) rv := by
      rw [hrvEq]
      refine pap_ctor_funOk hfind hoNew fun w hw => ?_
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hw)
      have hiV : i < vs.length := houtSz ▸ hi
      obtain ⟨w', hw', _, hbw, hnoW, hcfW, hfunLift⟩ := houtProps i vs[i] (List.getElem?_eq_getElem hiV)
      rw [Array.getElem?_eq_getElem hi] at hw'; cases hw'
      refine ⟨hbw, hnoW, hcfW, ?_⟩
      rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hiV) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
      · exact hfunLift .unknown false (fun _ => False)
          (NonValSafe.funOkAt P ext B_call st .unknown (Or.inl ⟨.irr, hEq⟩))
      · have hmem : some av ∈ avs.toArray.toList := by simp; exact List.mem_of_getElem? ha
        obtain ⟨hvd, hadm, hoo, hnotOS, _, _⟩ := hperA av hmem
        have hvSim := (hargs.1 i vs[i] av ft hg).1
        exact FunOkAt_of_admits (Skel.admits_symm .unknown av.skel ▸ hadm)
          (hfunLift av.skel false (fun _ => False)
            ((hvSim.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.2.2.2.1 ⟨hnotOS, hoo⟩).2.2)
    have hOpenRv : DeepOpenUnder st'.heap st'.regions (I.regsOf res.regs) rv := by
      refine hdouRv st'.regions (I.regsOf res.regs) fun v hv => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
      · rw [hEq]; exact DeepOpenUnder_imm _ _ _ _
      · have hmem : some av ∈ avs.toArray.toList := by simp; exact List.mem_of_getElem? ha
        obtain ⟨hvd, _, _, hnotOS, _, hregsA⟩ := hperA av hmem
        have hvSim := (hargs.1 i vs[i] av ft hg).1
        rw [hr']
        exact ((hvSim.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.1).mono fun c' hc' => by
          obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hc'
          exact Interp.mem_regsOf.mpr ⟨r', hregsA r' hr', hc1⟩
    have hVSimRes : VSim P ext B_call st' Frame NoKill NoSpend σ' I (fun _ => False) res rv := by
      refine ⟨fun r' hr' => ?_, fun d' hd' => ?_,
        (fun _ hs => by rw [hsrcR] at hs; cases hs),
        (fun _ ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs), fun _ => ?_⟩
      · obtain ⟨a, haMem, hrA⟩ := hregsSub r' hr'
        have haMem' : some a ∈ avs := by simpa using haMem
        obtain ⟨i, hi, haEq⟩ := List.getElem_of_mem haMem'
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [List.getElem?_eq_getElem hi, haEq])
        rw [hnr]; exact (hargs.1 i v a ft hg).1.1 r' hrA
      · obtain ⟨a, haMem, hdA⟩ := hdepsSub d' hd'
        have haMem' : some a ∈ avs := by simpa using haMem
        obtain ⟨i, hi, haEq⟩ := List.getElem_of_mem haMem'
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [List.getElem?_eq_getElem hi, haEq])
        rw [hszSt]; exact (hargs.1 i v a ft hg).1.2.1 d' hdA
      · exact ⟨hbvRv, hOpenRv, hcfRv, fun _ hne => absurd hclsR hne,
          fun _ => ⟨hnoRv, fun _ h => h, hskelR ▸ hFunRv⟩,
          (fun hoo => by rw [hooR] at hoo; cases hoo),
          (fun ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs),
          (fun htr => by have h1 := htr.2.1; rw [hownR] at h1; cases h1)⟩
    have hDisjRes : ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) res rv := by
      intro k b ab hsc hbk habk hne
      have hvB := ((hsim.2.2.2.2.2.1 k b ab hsc hbk habk).2 hne).2
      have hsrcB : ∀ x, (effVal ab).src = some x → x < σ.st.size := fun x hx => (hvB.2.2.1 x hx).1
      refine ⟨(fun _ htr => by have h1 := htr.2.1; rw [hownR] at h1; cases h1),
        fun haB' htrB' _ hdd l horB' hrRv' => ?_,
        fun _ _ _ _ _ h => False.elim h,
        fun haB' hftB' _ _ l hfl hrRv' => ?_,
        fun _ _ _ _ h => False.elim h,
        (fun hs => by rw [hsrcR] at hs; cases hs),
        (fun _ hs => by rw [hsrcR] at hs; cases hs)⟩
      · have hpB := hpresEnv k b ab hsc hbk habk hne haB'
        have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have htrB₀ := Transferable.of_AStateLe hok hle' hvB.2.1 hsrcB (fun _ h => h) htrB'
        have horB₀ := (OwnReach_congr hpB l).mp horB'
        have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size (OwnReach_toReach horB₀)
        rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
        · omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
          rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
          · rw [hEq] at hrv; cases hrv
          · have hmem : some av ∈ avs.toArray.toList := by simp; exact List.mem_of_getElem? ha
            obtain ⟨hvd, _, _, hnotOS, hdepsA, _⟩ := hperA av hmem
            exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.1
              haB₀ htrB₀ ⟨hvd, fun h => False.elim (hnotOS h)⟩
              (fun d hd hda => hdd d hd (hdepsA d hda)) l horB₀ hrv
      · have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have hftB₀ := FootActive.of_AStateLe hok hle' hvB.2.1 hsrcB hftB'
        have hrB₀ : Reach st.heap b.val l := by
          rcases hftB₀ with hooB | ⟨hisB, _⟩
          · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.1 hooB).1 l hfl |>.1
          · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.2.1 hisB).1 l hfl |>.1
        have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size hrB₀
        rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
        · omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
          rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
          · rw [hEq] at hrv; cases hrv
          · have hmem : some av ∈ avs.toArray.toList := by simp; exact List.mem_of_getElem? ha
            obtain ⟨hvd, _, hoo, hnotOS, _, _⟩ := hperA av hmem
            have hneSrc : av.src ≠ some ab.id := by
              intro hsrc
              rcases hftB₀ with hooB | ⟨hisB, _⟩
              · have h1 := ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.2.2.2.2.1 hsrc hooB
                rw [hoo] at h1; cases h1
              · obtain ⟨id, hs1, ho1⟩ := hisB; dsimp [effVal] at hs1; cases hs1
                exact hnotOS ⟨ab.id, hsrc, ho1⟩
            exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.2.2.1
              haB₀ hftB₀ ⟨hvd, fun h => False.elim (hnotOS h)⟩ hneSrc l hfl hrv
    have hNrfRes : ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv := by
      intro _ hregsR hdepsR l hrRv' hnotSS' hnotNum' hForb
      have hltF := hForbidLt l hForb
      rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
      · omega
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
        rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
        · rw [hEq] at hrv; cases hrv
        · have hmem : some av ∈ avs.toArray.toList := by simp; exact List.mem_of_getElem? ha
          obtain ⟨hvd, _, _, hnotOS, hdepsA, hregsA⟩ := hperA av hmem
          have hnotSS0 : ¬ StaticStrLoc st l := fun hss =>
            hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
              (hpresOld.mono fun _ h => StOk_staticStrLoc_lt hst h) hss)
          have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hc⟩ =>
            hnotNum' ⟨o, n, hpresNum l o n ho hc, hc⟩
          exact (hargs.1 i vs[i] av ft hg).2.2.1 ⟨hvd, fun h => False.elim (hnotOS h)⟩
            (fun r' hr' => hregsR r' (hregsA r' hr'))
            (fun d' hd' => hdepsR d' (hdepsA d' hd')) l hrv hnotSS0 hnotNum0 hForb
    exact ⟨hst', by omega, hcap', hr', hnr' ▸ Nat.le_refl _,
      hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
      hpresOld.mono fun l hF => hFlt l hF, hpresEnv, hpresNum, honce', hssf', hsim', hEnvNrf',
      hVSimRes, hDisjRes, hNrfRes, (fun _ hne => absurd hclsR hne), Or.inl ⟨hbvRv, hcfRv⟩, SrcOk_none hsrcR⟩

/-- Complete unpacking of `APrimArgs` (for `prim_pap_bridge`). -/
theorem APrimArgs_spec {avs : List (Option AVal)} {σ σ' : AState}
    {deps₀ regs₀ deps regs : List Nat}
    (hok : AStateOk σ) (h : APrimArgs avs σ deps₀ regs₀ deps regs σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    (∀ d ∈ deps₀, d ∈ deps) ∧ (∀ r ∈ regs₀, r ∈ regs) ∧
    (∀ a, some a ∈ avs →
      ValidDeps σ a.deps ∧
      (a.cls = .val → Skel.unknown.admits a.skel = true ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a ∧
        (∀ d ∈ a.deps, d ∈ deps) ∧ (∀ r ∈ a.regs, r ∈ regs))) ∧
    (∀ d ∈ deps, d ∈ deps₀ ∨ ∃ a, some a ∈ avs ∧ a.cls = .val ∧ d ∈ a.deps) ∧
    (∀ r ∈ regs, r ∈ regs₀ ∨ ∃ a, some a ∈ avs ∧ a.cls = .val ∧ r ∈ a.regs) := by
  induction h with
  | nil =>
    exact ⟨hok, AStateLe.refl _, rfl, rfl, rfl, rfl, rfl, fun _ h => h, fun _ h => h,
      (fun _ h => by cases h), fun _ h => Or.inl h, fun _ h => Or.inl h⟩
  | consNone _ ih =>
    obtain ⟨hok', hle', h1, h2, h3, h4, h5, hdM, hrM, hall, hdSub, hrSub⟩ := ih hok
    exact ⟨hok', hle', h1, h2, h3, h4, h5, hdM, hrM,
      fun a ha => hall a (by simpa using ha),
      fun d hd => (hdSub d hd).imp id (fun ⟨a, ha, rest⟩ => ⟨a, List.mem_cons_of_mem _ ha, rest⟩),
      fun r hr => (hrSub r hr).imp id (fun ⟨a, ha, rest⟩ => ⟨a, List.mem_cons_of_mem _ ha, rest⟩)⟩
  | @consNonVal a rest σ0 σ1 deps0 regs0 deps1 regs1 σ2 hne hval _ ih =>
    obtain ⟨hvd, rfl⟩ := Runs_valid hval
    obtain ⟨hok', hle', h1, h2, h3, h4, h5, hdM, hrM, hall, hdSub, hrSub⟩ := ih hok
    refine ⟨hok', hle', h1, h2, h3, h4, h5, hdM, hrM, fun a' ha' => ?_,
      fun d hd => (hdSub d hd).imp id (fun ⟨a', ha', rest⟩ => ⟨a', List.mem_cons_of_mem _ ha', rest⟩),
      fun r hr => (hrSub r hr).imp id (fun ⟨a', ha', rest⟩ => ⟨a', List.mem_cons_of_mem _ ha', rest⟩)⟩
    rcases List.mem_cons.mp ha' with hEq | hmem
    · cases hEq; exact ⟨hvd, fun hc => absurd hc hne⟩
    · exact hall a' hmem
  | @consVal a rest σ0 σ1 deps0 regs0 deps1 regs1 σ2 hcls hflow _ ih =>
    obtain ⟨hok1, hle1, hszSt1, honce1, hszSp1, hreg1, hnr1, hvd, _, hnonOnce, _, _, _, _, _⟩ :=
      Runs_flowTo hok hflow
    obtain ⟨hadm, hoo, hnotOS⟩ := hnonOnce (fun hc => by cases hc)
    obtain ⟨hok2, hle2, hszSt2, honce2, hszSp2, hreg2, hnr2, hdM2, hrM2, hall2, hdSub2, hrSub2⟩ := ih hok1
    refine ⟨hok2, hle1.trans hle2, hszSt2.trans hszSt1, honce2.trans honce1, hszSp2.trans hszSp1,
      hreg2.trans hreg1, hnr2.trans hnr1,
      fun d hd => hdM2 d ((mem_natUnion ..).mpr (Or.inl hd)),
      fun r hr => hrM2 r ((mem_natUnion ..).mpr (Or.inl hr)),
      fun a' ha' => ?_, fun d hd => ?_, fun r hr => ?_⟩
    · rcases List.mem_cons.mp ha' with hEq | hmem
      · cases hEq
        exact ⟨hvd, fun _ => ⟨hadm, hoo, hnotOS,
          fun d hd => hdM2 d ((mem_natUnion ..).mpr (Or.inr hd)),
          fun r hr => hrM2 r ((mem_natUnion ..).mpr (Or.inr hr))⟩⟩
      · obtain ⟨hvd1, hval1⟩ := hall2 a' hmem
        refine ⟨ValidDeps.of_AStateLe hle1 (fun d hd => hszSt1 ▸ (hvd1 d hd).1) hvd1, fun hc => ?_⟩
        obtain ⟨had1, hoo1, hno1, hda1, hra1⟩ := hval1 hc
        exact ⟨had1, hoo1, fun ⟨id, hs, ho0⟩ => hno1 ⟨id, hs, by rw [honce1]; exact ho0⟩, hda1, hra1⟩
    · rcases hdSub2 d hd with hu | ⟨a', ha', hca', hda'⟩
      · rcases (mem_natUnion ..).mp hu with h0 | ha
        · exact Or.inl h0
        · exact Or.inr ⟨a, List.mem_cons_self, hcls, ha⟩
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hca', hda'⟩
    · rcases hrSub2 r hr with hu | ⟨a', ha', hca', hra'⟩
      · rcases (mem_natUnion ..).mp hu with h0 | ha
        · exact Or.inl h0
        · exact Or.inr ⟨a, List.mem_cons_self, hcls, ha⟩
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hca', hra'⟩

/-- Bridge for `ACall.prim` when under-applied (`vs.length < p.arity`): simulates
`makePap P fuel r #[] vs` against `APrimArgs avs σ [] [] deps regs σ'`. -/
theorem prim_pap_bridge {P : Prog} {ext : ExternOracle} {B B_call fuel : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {r : Ref} {p : Prim} {deps regs : List Nat}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B) (hB : B_call ≤ B + 1)
    (hfind : P.find? r = some (.prim p))
    (hmatch : ArgsMatch args vs avs)
    (hprim : APrimArgs avs σ [] [] deps regs σ')
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hst : StOk P ext B_call st)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size) :
    let res : AVal := { cls := .val, deps, regs, skel := .unknown }
    (∀ k, (makePap P fuel r #[] vs).run st ≠ .error (.violation k)) ∧
    ∀ rv st', (makePap P fuel r #[] vs).run st = .ok (rv, st') →
      StOk P ext B_call st' ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      st'.regions = st.regions ∧
      st.nextRegion ≤ st'.nextRegion ∧
      ArrayExtends st.statics st'.statics ∧
      ArrayExtends st.strs st'.strs ∧
      PreservesLocs Frame st.heap st'.heap ∧
      PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
      (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      Sim P ext B_call st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
      EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
      VSim P ext B_call st' Frame NoKill NoSpend σ' I (fun _ => False) res rv ∧
      ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) res rv ∧
      (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
      (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
      SrcOk Scope aenv σ σ' res := by
  intro res
  have hok := hsim.2.1
  have hIok := hsim.2.2.1
  obtain ⟨hok', hle', hszSt, honce, hszSp, hreg, hnr, _, _, hperA, hdepsSub, hregsSub⟩ :=
    APrimArgs_spec hok hprim
  have hvsOk : ∀ v ∈ vs, ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext B_call st v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
    · rw [hEq]; exact ⟨ValBaseOk_imm st .irr, NoOnceCell_imm _ _, CtorFieldsOk_imm P ext B_call st .irr⟩
    · obtain ⟨hvd, hval⟩ := hperA av (List.mem_of_getElem? ha)
      by_cases hcv : av.cls = .val
      · obtain ⟨_, hoo, hnotOS, _, _⟩ := hval hcv
        have hvSim := (hargs.1 i vs[i] av ft hg).1
        have hact : ActiveVal σ av := ⟨hvd, fun h => False.elim (hnotOS h)⟩
        exact ⟨(hvSim.2.2.2.2 hact).1, ((hvSim.2.2.2.2 hact).2.2.2.2.1 ⟨hnotOS, hoo⟩).1,
          (hvSim.2.2.2.2 hact).2.2.1⟩
      · obtain ⟨hbv, hnv⟩ := (hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv
        exact ⟨hbv, hnv.noOnceCell, hnv.ctorFieldsOk P ext B_call st⟩
  have hnoU : ∀ (i : Nat), ((((#[] : Array Param)[i]?.map Param.mode).getD BinderMode.many).isUnique = true) → False := by
    intro i h; simp [BinderMode.isUnique] at h
  rcases makePap_sound (P := P) (ext := ext) (B := B_call) (fuel := fuel)
    (r := r) (params := #[]) (vs := vs) hst hvsOk
    (fun i _ _ hu => False.elim (hnoU i hu))
    (fun i _ _ _ _ _ _ hu => False.elim (hnoU i hu)) with hOOF |
    ⟨rv, out, st', hrunPap, hr', hnr', hstat', hstr', hsz', hcap', hoss', hpres',
      honce', hssf', hst', ⟨cap, hrvEq, hoNew⟩, houtSz, houtProps, hbvRv, hnoRv, hcfRv, hdouRv, hreachRv⟩
  · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
  · rw [hrunPap]
    refine ⟨(fun _ h => by cases h), fun rv' st'' hokPap => ?_⟩
    cases hokPap
    have hpresOld : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap :=
      hpres'.mono fun l hltL => ⟨hltL, fun i _ _ hu => False.elim (hnoU i hu)⟩
    have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hr'
    have hIok' : InterpOk σ' st' I :=
      ⟨fun r' hr1 c' hc' => hnr' ▸ hIok.1 r' (hnr ▸ hr1) c' hc',
       fun c' hc' => by rw [hreg]; rw [hr'] at hc'; exact hIok.2 c' hc'⟩
    have hpresEnv : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap :=
      Sim_preserves_of_old hle' hpresOld hsim
    have hpresNum : ∀ (l : Nat) (o : Obj) (n : Nat),
        st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o :=
      fun l o n ho _ => (hpresOld l (Array.getElem?_eq_some_iff.mp ho).1).trans ho
    have hsim' : Sim P ext B_call st' Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
      Sim_step (Nat.le_refl _) hle' hok' hIok' hrf' honce' hssf' (fun _ _ _ h => h) hpresEnv hsim
    have hEnvNrf' : EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep :=
      EnvNoReachForbid_step hok hle' (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
        (hpresOld.mono fun _ hss => StOk_staticStrLoc_lt hst hss) hpresEnv hEnvNrf
    have hFunRv : FunOkAt P ext B_call st' .unknown false (fun _ => False) rv := by
      rw [hrvEq]
      refine pap_prim_funOk hidx hext hih hB hfind hoNew fun w hw => ?_
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hw)
      have hiV : i < vs.length := houtSz ▸ hi
      obtain ⟨w', hw', _, hbw, hnoW, hcfW, hfunLift⟩ := houtProps i vs[i] (List.getElem?_eq_getElem hiV)
      rw [Array.getElem?_eq_getElem hi] at hw'; cases hw'
      refine ⟨hbw, hnoW, hcfW, ?_⟩
      rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hiV) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
      · exact hfunLift .unknown false (fun _ => False)
          (NonValSafe.funOkAt P ext B_call st .unknown (Or.inl ⟨.irr, hEq⟩))
      · obtain ⟨hvd, hval⟩ := hperA av (List.mem_of_getElem? ha)
        by_cases hcv : av.cls = .val
        · obtain ⟨hadm, hoo, hnotOS, _, _⟩ := hval hcv
          have hvSim := (hargs.1 i vs[i] av ft hg).1
          exact FunOkAt_of_admits (Skel.admits_symm .unknown av.skel ▸ hadm)
            (hfunLift av.skel false (fun _ => False)
              ((hvSim.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.2.2.2.1 ⟨hnotOS, hoo⟩).2.2)
        · exact hfunLift .unknown false (fun _ => False)
            (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.funOkAt P ext B_call st .unknown)
    have hOpenRv : DeepOpenUnder st'.heap st'.regions (I.regsOf res.regs) rv := by
      refine hdouRv st'.regions (I.regsOf res.regs) fun v hv => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
      · rw [hEq]; exact DeepOpenUnder_imm _ _ _ _
      · obtain ⟨hvd, hval⟩ := hperA av (List.mem_of_getElem? ha)
        by_cases hcv : av.cls = .val
        · obtain ⟨_, _, hnotOS, _, hregsA⟩ := hval hcv
          have hvSim := (hargs.1 i vs[i] av ft hg).1
          rw [hr']
          exact ((hvSim.2.2.2.2 ⟨hvd, fun h => False.elim (hnotOS h)⟩).2.1).mono fun c' hc' => by
            obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hc'
            exact Interp.mem_regsOf.mpr ⟨r', hregsA r' hr', hc1⟩
        · exact ((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.deepOpenUnder_nil
    have hVSimRes : VSim P ext B_call st' Frame NoKill NoSpend σ' I (fun _ => False) res rv := by
      refine ⟨fun r' hr' => ?_, fun d' hd' => ?_,
        (fun _ hs => by cases hs),
        (fun _ ⟨_, hs, _⟩ => by cases hs), fun _ => ?_⟩
      · rcases hregsSub r' hr' with h0 | ⟨a, haMem, _, hrA⟩
        · cases h0
        · obtain ⟨i, hi, haEq⟩ := List.getElem_of_mem haMem
          obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [List.getElem?_eq_getElem hi, haEq])
          rw [hnr]; exact (hargs.1 i v a ft hg).1.1 r' hrA
      · rcases hdepsSub d' hd' with h0 | ⟨a, haMem, _, hdA⟩
        · cases h0
        · obtain ⟨i, hi, haEq⟩ := List.getElem_of_mem haMem
          obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [List.getElem?_eq_getElem hi, haEq])
          rw [hszSt]; exact (hargs.1 i v a ft hg).1.2.1 d' hdA
      · exact ⟨hbvRv, hOpenRv, hcfRv, fun _ hne => absurd rfl hne,
          fun _ => ⟨hnoRv, fun _ h => h, hFunRv⟩,
          (fun hoo => by cases hoo),
          (fun ⟨_, hs, _⟩ => by cases hs),
          (fun htr => by cases htr.2.1)⟩
    have hDisjRes : ValEnvDisj P st' NoKill Scope env aenv σ' envFoot (fun _ => False) res rv := by
      intro k b ab hsc hbk habk hne
      have hvB := ((hsim.2.2.2.2.2.1 k b ab hsc hbk habk).2 hne).2
      have hsrcB : ∀ x, (effVal ab).src = some x → x < σ.st.size := fun x hx => (hvB.2.2.1 x hx).1
      refine ⟨(fun _ htr => by cases htr.2.1),
        fun haB' htrB' _ hdd l horB' hrRv' => ?_,
        fun _ _ _ _ _ h => False.elim h,
        fun haB' hftB' _ _ l hfl hrRv' => ?_,
        fun _ _ _ _ h => False.elim h,
        (fun hs => by cases hs),
        (fun _ hs => by cases hs)⟩
      · have hpB := hpresEnv k b ab hsc hbk habk hne haB'
        have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have htrB₀ := Transferable.of_AStateLe hok hle' hvB.2.1 hsrcB (fun _ h => h) htrB'
        have horB₀ := (OwnReach_congr hpB l).mp horB'
        have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size (OwnReach_toReach horB₀)
        rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
        · omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
          rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
          · rw [hEq] at hrv; cases hrv
          · obtain ⟨hvd, hval⟩ := hperA av (List.mem_of_getElem? ha)
            by_cases hcv : av.cls = .val
            · obtain ⟨_, _, hnotOS, hdepsA, _⟩ := hval hcv
              exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.1
                haB₀ htrB₀ ⟨hvd, fun h => False.elim (hnotOS h)⟩
                (fun d hd hda => hdd d hd (hdepsA d hda)) l horB₀ hrv
            · exact OwnReach_not_numLoc horB₀ (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.reach_numLoc hrv)
      · have haB₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 hsrcB haB'
        have hftB₀ := FootActive.of_AStateLe hok hle' hvB.2.1 hsrcB hftB'
        have ⟨hrB₀, _, hnotNum0⟩ : Reach st.heap b.val l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
          rcases hftB₀ with hooB | ⟨hisB, _⟩
          · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.1 hooB).1 l hfl
          · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.2.1 hisB).1 l hfl
        have hltL : l < st.heap.objs.size := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size hrB₀
        rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
        · omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
          rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
          · rw [hEq] at hrv; cases hrv
          · obtain ⟨hvd, hval⟩ := hperA av (List.mem_of_getElem? ha)
            by_cases hcv : av.cls = .val
            · obtain ⟨_, hoo, hnotOS, _, _⟩ := hval hcv
              have hneSrc : av.src ≠ some ab.id := by
                intro hsrc
                rcases hftB₀ with hooB | ⟨hisB, _⟩
                · have h1 := ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.2.2.2.2.1 hsrc hooB
                  rw [hoo] at h1; cases h1
                · obtain ⟨id, hs1, ho1⟩ := hisB; dsimp [effVal] at hs1; cases hs1
                  exact hnotOS ⟨ab.id, hsrc, ho1⟩
              exact ((hargs.1 i vs[i] av ft hg).2.1 k b ab hsc hbk habk hne).2.2.2.1
                haB₀ hftB₀ ⟨hvd, fun h => False.elim (hnotOS h)⟩ hneSrc l hfl hrv
            · exact hnotNum0 (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.reach_numLoc hrv)
    have hNrfRes : ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv := by
      intro _ hregsR hdepsR l hrRv' hnotSS' hnotNum' hForb
      have hltF := hForbidLt l hForb
      rcases hreachRv l hrRv' with rfl | ⟨v, hvMem, hrv⟩
      · omega
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvMem
        rcases ArgsMatch_getElem_vs hmatch (List.getElem?_eq_getElem hi) with ⟨hEq, _, _⟩ | ⟨av, ft, hg, ha⟩
        · rw [hEq] at hrv; cases hrv
        · obtain ⟨hvd, hval⟩ := hperA av (List.mem_of_getElem? ha)
          have hnotSS0 : ¬ StaticStrLoc st l := fun hss =>
            hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
              (hpresOld.mono fun _ h => StOk_staticStrLoc_lt hst h) hss)
          have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hc⟩ =>
            hnotNum' ⟨o, n, hpresNum l o n ho hc, hc⟩
          by_cases hcv : av.cls = .val
          · obtain ⟨_, _, hnotOS, hdepsA, hregsA⟩ := hval hcv
            exact (hargs.1 i vs[i] av ft hg).2.2.1 ⟨hvd, fun h => False.elim (hnotOS h)⟩
              (fun r' hr' => hregsR r' (hregsA r' hr'))
              (fun d' hd' => hdepsR d' (hdepsA d' hd')) l hrv hnotSS0 hnotNum0 hForb
          · exact hnotNum0 (((hargs.1 i vs[i] av ft hg).2.2.2 hvd hcv).2.reach_numLoc hrv)
    exact ⟨hst', by omega, hcap', hr', hnr' ▸ Nat.le_refl _,
      hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
      hpresOld.mono fun l hF => hFlt l hF, hpresEnv, hpresNum, honce', hssf', hsim', hEnvNrf',
      hVSimRes, hDisjRes, hNrfRes, fun _ hne => absurd rfl hne, SrcOk_none rfl⟩

/-- A 0-parameter extern produces a value with empty taints everywhere (`DeepOpenUnder ... [] rv`). -/
theorem callExtern_zero_deepOpen_nil {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {r : Ref} {res : ResultMode} {rc : Cls} {rs : Skel} {st st' : St} {rv : Val}
    (hext : ExternOk P ext)
    (hfind : P.find? r = some (.extern #[] res rc rs))
    (hst : StOk P ext B st)
    (hcall : (callExtern P ext fuel r #[] res rc []).run st = .ok (rv, st')) :
    DeepOpenUnder st'.heap st'.regions [] rv := by
  let s := st.nextRegion
  let cur := st.regions.headD 0
  let st₀ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
  have hunfold : (callExtern P ext fuel r #[] res rc []).run st =
      (match ext r [] st₀.heap with
       | none => .error .stuck
       | some (h₂, v) =>
         match (ret P fuel s cur res rc v).run { st₀ with heap := h₂ } with
         | .error e => .error e
         | .ok (rv', st₃) => .ok (rv', { st₃ with regions := st₃.regions.filter (· != s) })) := by
    unfold callExtern
    have hopen : openRegion.run st = .ok ((s, cur), st₀) := rfl
    rw [M_bind_run, hopen]; dsimp only
    have hfor : (forIn (m := M) (([] : List Param).zip ([] : List Val)) ([] : List Val)
        (fun (pv : Param × Val) acc => bindAt P fuel s pv.1.mode pv.1.cls pv.2 >>= fun b => pure (.yield (acc ++ [b.val])))).run st₀ =
        .ok ([], st₀) := rfl
    rw [M_bind_run, hfor]; dsimp only
    have hget : (get : M St).run st₀ = .ok (st₀, st₀) := rfl
    rw [M_bind_run, hget]; dsimp only
    cases he : ext r [] st₀.heap with
    | none => rfl
    | some p =>
      rcases p with ⟨h₂, v⟩; dsimp only
      have hset : (set ({ st₀ with heap := h₂ } : St) : M PUnit).run st₀ = .ok ((), { st₀ with heap := h₂ }) := rfl
      rw [M_bind_run, hset]; dsimp only
      rw [M_bind_run]
      cases hr : (ret P fuel s cur res rc v).run { st₀ with heap := h₂ } with
      | error e => rfl
      | ok pr =>
        rcases pr with ⟨rv', st₃⟩; dsimp only
        have hclose : (closeRegion s).run st₃ = .ok ((), { st₃ with regions := st₃.regions.filter (· != s) }) := rfl
        rw [M_bind_run, hclose]; rfl
  rw [hunfold] at hcall
  cases he : ext r [] st₀.heap with
  | none => rw [he] at hcall; cases hcall
  | some p =>
    rcases p with ⟨h₂, v⟩
    rw [he] at hcall; dsimp only at hcall
    cases hret : (ret P fuel s cur res rc v).run { st₀ with heap := h₂ } with
    | error e => rw [hret] at hcall; cases hcall
    | ok pr =>
      rcases pr with ⟨rv', st₃⟩
      rw [hret] at hcall; cases hcall
      obtain ⟨hsz, hcap, hold, hfresh, hvRet, hrcIrr, hrcImm, hrcLeaf, hresUniq⟩ :=
        hext r #[] res rc rs [] st₀.heap h₂ v hfind he
      -- Every cell reachable from `v` in `h₂` is either fresh (`≥ st₀.heap.objs.size`) or `.num`
      have hvTaintEmpty : v.taint = [] := by
        rcases hvRet with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, _, _, _, _⟩ | ⟨i, p, a, hp, _⟩
        · rfl
        · rfl
        · simp at hp
      have hfreshOrNum : ∀ l, Reach h₂ v l →
          st₀.heap.objs.size ≤ l ∨ ∃ o n, h₂.objs[l]? = some o ∧ o.cell = .num n := by
        have hstep : ∀ {w : Val} {l : Nat},
            ((∃ i, w = .imm i) ∨
             (∃ loc cap, w = .ref loc cap [] ∧ st₀.heap.objs.size ≤ loc) ∨
             (∃ loc cap o n, w = .ref loc cap [] ∧ h₂.objs[loc]? = some o ∧ o.cell = .num n)) →
            Reach h₂ w l →
            st₀.heap.objs.size ≤ l ∨ ∃ o n, h₂.objs[l]? = some o ∧ o.cell = .num n := by
          intro w l hw hr
          induction hr with
          | @here loc cap t =>
            rcases hw with ⟨_, h⟩ | ⟨loc', cap', h, hge⟩ | ⟨loc', cap', o, n, h, ho, hnum⟩
            · cases h
            · cases h; exact Or.inl hge
            · cases h; exact Or.inr ⟨o, n, ho, hnum⟩
          | @step loc cap t o w' l' ho hm hr' ih =>
            rcases hw with ⟨_, h⟩ | ⟨loc', cap', h, hge⟩ | ⟨loc', cap', o1, n1, h, ho1, hnum1⟩
            · cases h
            · cases h
              obtain ⟨hinc, _, hcellOk⟩ := hfresh loc o hge ho
              cases hc : o.cell with
              | num _ | str _ => rw [hc] at hm; cases hm
              | clo _ _ _ _ _ _ | once _ _ => rw [hc] at hinc; cases hinc
              | ctor r' fs =>
                rw [hc] at hm hcellOk
                have hfv := (hcellOk w' (by simpa [Cell.vals] using hm)).1
                rcases hfv with ⟨i, rfl⟩ | ⟨loc2, cap2, o2, rfl, hge2, _, _, _⟩ | ⟨i, p, a, hp, _⟩
                · exact ih (Or.inl ⟨i, rfl⟩)
                · exact ih (Or.inr (Or.inl ⟨loc2, cap2, rfl, hge2⟩))
                · simp at hp
              | pap r' as =>
                rw [hc] at hm hcellOk
                have hpOk := (hcellOk w' (by simpa [Cell.vals] using hm)).1
                rcases hpOk with ⟨i, rfl⟩ | ⟨loc2, cap2, o2, n2, rfl, ho2, hnum2⟩
                · exact ih (Or.inl ⟨i, rfl⟩)
                · exact ih (Or.inr (Or.inr ⟨loc2, cap2, o2, n2, rfl, ho2, hnum2⟩))
            · cases h; rw [ho1] at ho; cases ho; rw [hnum1] at hm; cases hm
        intro l hr
        refine hstep ?_ hr
        rcases hvRet with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, hge, _, _, _⟩ | ⟨i, p, a, hp, _⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr (Or.inl ⟨loc, cap, rfl, hge⟩)
        · simp at hp
      have hHeldEmpty : ∀ w, HeldBy h₂ v w → w.taint = [] := by
        intro w hw
        rcases hw with rfl | ⟨l, o, hr, ho, hm⟩
        · exact hvTaintEmpty
        · rcases hfreshOrNum l hr with hge | ⟨o', n', ho', hnum'⟩
          · obtain ⟨hinc, _, hcellOk⟩ := hfresh l o hge ho
            cases hc : o.cell with
            | num _ | str _ => rw [hc] at hm; cases hm
            | clo _ _ _ _ _ _ | once _ _ => rw [hc] at hinc; cases hinc
            | ctor r' fs =>
              rw [hc] at hm hcellOk
              rcases (hcellOk w (by simpa [Cell.vals] using hm)).1 with
                ⟨i, rfl⟩ | ⟨loc2, cap2, o2, rfl, _, _, _, _⟩ | ⟨i, p, a, hp, _⟩
              · rfl
              · rfl
              · simp at hp
            | pap r' as =>
              rw [hc] at hm hcellOk
              rcases (hcellOk w (by simpa [Cell.vals] using hm)).1 with
                ⟨i, rfl⟩ | ⟨loc2, cap2, o2, n2, rfl, _, _⟩
              · rfl
              · rfl
          · rw [ho'] at ho; cases ho; rw [hnum'] at hm; cases hm
      have hc2 : CapsOk h₂ := by
        intro l o ho
        by_cases hlt : l < st₀.heap.objs.size
        · have ho₀ : st₀.heap.objs[l]? = some st₀.heap.objs[l] := Array.getElem?_eq_getElem hlt
          obtain ⟨o', ho', hcase⟩ := hold l st₀.heap.objs[l] ho₀
          rw [ho] at ho'; cases ho'
          rcases hcase with ⟨_, hcapEq⟩ | ⟨_, hcapLt, _⟩
          · exact Nat.lt_of_lt_of_le (hcapEq ▸ hst.1 l st₀.heap.objs[l] ho₀) hcap
          · exact hcapLt
        · exact (hfresh l o (Nat.le_of_not_lt hlt) ho).2.1
      have hdlV : DeepLive h₂ v := by
        intro w hw
        rcases hw with rfl | ⟨l, o, hr, ho, hm⟩
        · rcases hvRet with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, hge, ho, hcapO, _⟩ | ⟨i, p, a, hp, _⟩
          · exact ⟨trivial, trivial⟩
          · exact ⟨⟨o, ho, hcapO⟩, fun _ _ _ _ => rfl⟩
          · simp at hp
        · rcases hfreshOrNum l hr with hge | ⟨o', n', ho', hnum'⟩
          · obtain ⟨hinc, _, hcellOk⟩ := hfresh l o hge ho
            cases hc : o.cell with
            | num _ | str _ => rw [hc] at hm; cases hm
            | clo _ _ _ _ _ _ | once _ _ => rw [hc] at hinc; cases hinc
            | ctor r' fs =>
              rw [hc] at hm hcellOk
              rcases (hcellOk w (by simpa [Cell.vals] using hm)).1 with
                ⟨i, rfl⟩ | ⟨loc2, cap2, o2, rfl, hge2, ho2, hcap2, _⟩ | ⟨i, p, a, hp, _⟩
              · exact ⟨trivial, trivial⟩
              · exact ⟨⟨o2, ho2, hcap2⟩, fun _ _ _ _ => rfl⟩
              · simp at hp
            | pap r' as =>
              rw [hc] at hm hcellOk
              have ⟨hpOk, hvalOk, _⟩ := hcellOk w (by simpa [Cell.vals] using hm)
              rcases hpOk with ⟨i, rfl⟩ | ⟨loc2, cap2, o2, n2, rfl, ho2, hnum2⟩
              · exact ⟨trivial, trivial⟩
              · exact ⟨⟨o2, ho2, by obtain ⟨_, o2', ho2', hc2'⟩ := hvalOk; rw [ho2] at ho2'; cases ho2'; exact hc2'⟩,
                  fun _ _ _ _ => rfl⟩
          · rw [ho'] at ho; cases ho; rw [hnum'] at hm; cases hm
      have hacycV : AcyclicFrom h₂ v := by
        intro l o w hr ho hm hrw
        rcases hfreshOrNum l hr with hge | ⟨o', n', ho', hnum'⟩
        · obtain ⟨hinc, _, hcellOk⟩ := hfresh l o hge ho
          cases hc : o.cell with
          | num _ | str _ => rw [hc] at hm; cases hm
          | clo _ _ _ _ _ _ | once _ _ => rw [hc] at hinc; cases hinc
          | ctor r' fs =>
            rw [hc] at hm hcellOk
            exact (hcellOk w (by simpa [Cell.vals] using hm)).2 hrw
          | pap r' as =>
            rw [hc] at hm hcellOk
            exact (hcellOk w (by simpa [Cell.vals] using hm)).2.2 hrw
        · rw [ho'] at ho; cases ho; rw [hnum'] at hm; cases hm
      have htreeV : res.isUnique = true → OwnTreeFull P h₂ v := by
        intro hru
        cases hrc : rc with
        | irr => rw [hrcIrr hrc]; exact OwnTreeFull_imm P _ _
        | imm => obtain ⟨i', hi'⟩ := hrcImm hrc; rw [hi']; exact OwnTreeFull_imm P _ _
        | leaf =>
          obtain ⟨loc', cap', o', n', hvEq, ho', hnum'⟩ := hrcLeaf hrc
          rw [hvEq]; exact OwnTreeFull_num ho' hnum'
        | val =>
          obtain ⟨_, _, _, _, htr, _⟩ := hresUniq hru hrc
          exact htr
      rcases ret_spec (P := P) (fuel := fuel) (s := s) (cur := cur) (r := res) (c := rc) (v := v)
        (st := { st₀ with heap := h₂ }) hc2 hdlV hacycV htreeV
        (fun _ r' hr' _ => by rw [hvTaintEmpty] at hr'; cases hr')
        (fun _ r' hr' _ => by rw [hvTaintEmpty] at hr'; cases hr') with hSt | hOOF |
        ⟨rv₂, st₃', hret', _, _, _, _, _, _, _, hoss₃, _, hcls₃, hdl₃, _, _, htSU₃, htB₃, _, _, _, _, _⟩
      · rw [hSt] at hret; cases hret
      · rw [hOOF] at hret; cases hret
      · rw [hret] at hret'; cases hret'
        by_cases hrcV : rc = .val
        · subst hrcV
          obtain ⟨_, _, hheldV⟩ := ret_val_sameLoc hc2 hdlV hacycV htreeV
            (fun _ r' hr' _ => by rw [hvTaintEmpty] at hr'; cases hr') hret
          intro w hw r' hr' _
          rcases hheldV w hw with rfl | ⟨w₀, hw₀, hvsW⟩
          · cases hresE : res with
            | shared | unique =>
              have h1 := htSU₃ (by rw [hresE]; simp) r' hr'
              rw [hvTaintEmpty] at h1; cases h1
            | borrowed | uniqueBorrowed =>
              rcases htB₃ (by rw [hresE]; rfl) r' hr' with ⟨h1, _⟩ | ⟨_, _, h2⟩
              · rw [hvTaintEmpty] at h1; cases h1
              · rw [hvTaintEmpty] at h2; cases h2
          · rw [← hvsW.taint_eq, hHeldEmpty w₀ hw₀] at hr'; cases hr'
        · exact ClsSafe_deepOpenUnder_nil hrcV (ClsSafe.of_clsOk hcls₃)

/-- Bridge for `ACall.ifaceFullZero` (`ifc.params.size = 0`): simulates `callWithS P ext fuel r vs c`
for both 0-ary `.body` (`staticS`) and 0-ary `.extern` (`callExtern`), followed by `applyAllS_bridge`. -/
theorem callResult_zero_bridge {P : Prog} {ext : ExternOracle} {B B_call fuel : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ' : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {r : Ref} {d : RunDef} {ifc : Iface} {c : Cls}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {res : AVal}
    (hext : ExternOk P ext) (hih : FullIH P ext B) (hB : B_call ≤ B + 1)
    (hfind : P.find? r = some d) (hifc : ifaceOf? d = some ifc)
    (hzero : ifc.params.size = 0)
    (hmatch : ArgsMatch args vs avs)
    (hErased : ∀ i, i < avs.length → (avs[i]? = some none ↔ erasedAt d i = true))
    (happs : AApps { cls := ifc.resCls, skel := ifc.resSkel } (avs.filterMap id) c σ res σ')
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hst : StOk P ext B_call st)
    (_hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hnk' : NoKillOk NoKill σ') (hnsp' : NoSpendOk NoSpend σ')
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hargsSrc : ArgsSrcOk args)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size) :
    (∀ k, (callWithS P ext fuel r vs c).run (st, B_call) ≠ .error (.violation k)) ∧
    ∀ rv st' B', (callWithS P ext fuel r vs c).run (st, B_call) = .ok (rv, (st', B')) →
      ∃ resFoot : Nat → Prop,
        B' ≤ B_call ∧
        StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧
        st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧
        ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
        (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
        EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
        VSim P ext B' st' Frame NoKill NoSpend σ' I resFoot res rv ∧
        ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv ∧
        (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
        (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
        ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B' st' rv) ∨ (IsOnceSrc σ' res ∧ SpentOnceSafe st'.heap rv)) ∧
        SrcOk Scope aenv σ σ' res := by
  -- Every entry of `args` is `some _` because `ifc.params.size = 0` ⇒ `erasedAt d i = false`
  have hNoneFalse : ∀ i, i < args.length → args[i]? ≠ some none := by
    intro i hi hEq
    have h1 := hmatch.2.2 i; rw [hEq] at h1
    have hiA : i < avs.length := hmatch.2.1 ▸ hi
    have her := (hErased i hiA).mp h1.2
    rw [erasedAt_of_ifaceOf hifc i, Array.getElem?_eq_none (by omega)] at her
    cases her
  let argsF : List (Val × AVal × (Nat → Prop)) := args.filterMap id
  have hMapSome : argsF.map some = args := by
    have hgo : ∀ (xs : List (Option (Val × AVal × (Nat → Prop)))),
        (∀ i, i < xs.length → xs[i]? ≠ some none) → (xs.filterMap id).map some = xs := by
      intro xs
      induction xs with
      | nil => intro _; rfl
      | cons x rest ih =>
        intro hne
        cases x with
        | none => exact False.elim (hne 0 (by simp) rfl)
        | some p =>
          simp only [List.filterMap_cons, id_eq, List.map_cons]
          exact congrArg (some p :: ·) (ih fun i hi => hne (i + 1) (by simpa using hi))
    exact hgo args hNoneFalse
  have hMapVal : argsF.map (·.1) = vs := by
    apply List.ext_getElem?
    intro i
    have hi := hmatch.2.2 i
    rw [← hMapSome] at hi
    rw [List.getElem?_map] at hi
    rw [List.getElem?_map]
    cases hfg : argsF[i]? with
    | none => simp only [hfg, Option.map_none] at hi ⊢; exact hi.1.symm
    | some p => simp only [hfg, Option.map_some] at hi ⊢; exact hi.1.symm
  have hMapAv : argsF.map (·.2.1) = avs.filterMap id := by
    have hEqAvs : avs = argsF.map (fun p => some p.2.1) := by
      apply List.ext_getElem?
      intro i
      have hi := hmatch.2.2 i
      rw [← hMapSome] at hi
      rw [List.getElem?_map] at hi
      rw [List.getElem?_map]
      cases hfg : argsF[i]? with
      | none => simp only [hfg, Option.map_none] at hi ⊢; exact hi.2
      | some p => simp only [hfg, Option.map_some] at hi ⊢; exact hi.2
    rw [hEqAvs]
    have hfm : ∀ (xs : List (Val × AVal × (Nat → Prop))),
        (xs.map fun p => some p.2.1).filterMap id = xs.map (·.2.1) := by
      intro xs; induction xs with
      | nil => rfl
      | cons p rest ih => simp [ih]
    exact (hfm argsF).symm
  have hArgsFGet : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
      argsF[i]? = some (v, av, ft) → args[i]? = some (some (v, av, ft)) := by
    intro i v av ft hg; rw [← hMapSome, List.getElem?_map, hg]; rfl
  -- Shared continuation: given 0-ary call result `(f, st₁, B₁)`, finish via `applyAllS_bridge`!
  have hCont : ∀ (n' b B₁ : Nat) (f : Val) (st₁ : St),
      B₁ ≤ b → b + 1 = B_call →
      StOk P ext B₁ st₁ →
      st.heap.objs.size ≤ st₁.heap.objs.size →
      st.heap.nextCap ≤ st₁.heap.nextCap →
      st₁.regions = st.regions →
      st.nextRegion ≤ st₁.nextRegion →
      ArrayExtends st.statics st₁.statics →
      ArrayExtends st.strs st₁.strs →
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₁.heap →
      PreservesOnceShell st.heap st₁.heap →
      StaticStrFresh st st₁ →
      ValBaseOk st₁ f →
      ClsSafe st₁.heap ifc.resCls f →
      DeepOpenUnder st₁.heap st₁.regions [] f →
      NoOnceCell st₁.heap f →
      CtorFieldsOk P ext B₁ st₁ f →
      FunOkAt P ext B₁ st₁ ifc.resSkel false (fun _ => False) f →
      (∀ l, Reach st₁.heap f l → st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st₁.heap l) →
      (∀ k, (applyAllS P ext n' f vs c).run (st₁, B₁) ≠ .error (.violation k)) ∧
      ∀ rv st' B', (applyAllS P ext n' f vs c).run (st₁, B₁) = .ok (rv, (st', B')) →
        ∃ resFoot : Nat → Prop,
          B' ≤ B_call ∧ StOk P ext B' st' ∧
          st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
          st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
          ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
          PreservesLocs Frame st.heap st'.heap ∧ PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
          (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
          PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
          Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
          EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
          VSim P ext B' st' Frame NoKill NoSpend σ' I resFoot res rv ∧
          ValEnvDisj P st' NoKill Scope env aenv σ' envFoot resFoot res rv ∧
          (ActiveVal σ' res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
          (ValidDeps σ' res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
          ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B' st' rv) ∨ (IsOnceSrc σ' res ∧ SpentOnceSafe st'.heap rv)) ∧
          SrcOk Scope aenv σ σ' res := by
    intro n' b B₁ f st₁ hB₁ hbEq hst₁ hsz₁ hcap₁ hr₁ hnr₁ hstat₁ hstr₁ hpresOld₁ honce₁ hssf₁
      hbvF hclsF hopenF hnoF hcfF hfunF hreachF
    have hok := hsim.2.1
    have hrf₁ : RegsFuture st st₁ := RegsFuture.same_regions hnr₁ hr₁
    have hIok₁ : InterpOk σ st₁ I :=
      ⟨fun r' hr' c' hc' => Nat.lt_of_lt_of_le (hsim.2.2.1.1 r' hr' c' hc') hnr₁,
       fun c' hc' => hsim.2.2.1.2 c' (hr₁ ▸ hc')⟩
    have hpresEnv₁ : PreservesActiveEnv Scope env aenv σ st.heap st₁.heap :=
      Sim_preserves_of_old (AStateLe.refl _) hpresOld₁ hsim
    have hpresNum₁ : ∀ (l : Nat) (o : Obj) (n : Nat),
        st.heap.objs[l]? = some o → o.cell = .num n → st₁.heap.objs[l]? = some o :=
      fun l o n ho _ => (hpresOld₁ l (Array.getElem?_eq_some_iff.mp ho).1).trans ho
    have hpresF₁ : PreservesLocs Frame st.heap st₁.heap :=
      hpresOld₁.mono fun l hF => hFlt l hF
    have hpresSS₁ : PreservesLocs (StaticStrLoc st) st.heap st₁.heap :=
      hpresOld₁.mono fun l hss => StOk_staticStrLoc_lt hst hss
    have hsim₁ : Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ I envFoot :=
      Sim_step (by omega) (AStateLe.refl _) hok hIok₁ hrf₁ honce₁ hssf₁ (fun _ _ _ h => h) hpresEnv₁ hsim
    have hEnvNrf₁ : EnvNoReachForbid st₁ Scope env aenv σ Forbid BadReg BadDep :=
      EnvNoReachForbid_step hok (AStateLe.refl _) (Sim_deps_lt hsim) hsim.2.2.2.1
        hstat₁ hstr₁ hpresSS₁ hpresEnv₁ hEnvNrf
    have hargs₁ : ArgListOk P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ I envFoot
        Forbid BadReg BadDep (argsF.map some) := by
      rw [hMapSome]
      exact ArgListOk_step (by omega) hok (AStateLe.refl _) hrf₁ honce₁ hssf₁
        hstat₁ hstr₁ hpresSS₁ (fun _ _ _ h => h) (Sim_deps_lt hsim) hsim.2.2.2.1 hpresEnv₁
        (fun i v av ft hg ha => hpresOld₁.mono fun l hr =>
          ((hargs.1 i v av ft hg).1.2.2.2.2 ha).1.1.reach_lt_size hr)
        hpresNum₁ hargs
    let fav : AVal := { cls := ifc.resCls, skel := ifc.resSkel }
    let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
    have hfV₁ : VSim P ext B₁ st₁ Frame₁ NoKill NoSpend σ I (fun _ => False) fav f := by
      refine ⟨(fun _ h => by cases h), (fun _ h => by cases h),
        (fun _ h => by cases h), (fun _ ⟨_, h, _⟩ => by cases h), fun _ => ?_⟩
      exact ⟨hbvF, hopenF, hcfF, fun _ hne => hclsF.to_nonValSafe hne hbvF.1.self.1,
        fun _ => ⟨hnoF, fun _ h => h, hfunF⟩,
        (fun h => by cases h), (fun ⟨_, h, _⟩ => by cases h), (fun htr => by cases htr.2.1)⟩
    have hfDisj₁ : ValEnvDisj P st₁ NoKill Scope env aenv σ envFoot (fun _ => False) fav f := by
      intro k b ab hsc hbk habk hne
      have hvB := ((hsim.2.2.2.2.2.1 k b ab hsc hbk habk).2 hne).2
      refine ⟨(fun _ htr => by cases htr.2.1),
        fun haB htrB _ _ l horB' hrF' => ?_,
        fun _ _ _ _ _ h => False.elim h,
        fun haB hftB _ _ l hfl hrF' => ?_,
        fun _ _ _ _ h => False.elim h,
        (fun h => by cases h), (fun _ h => by cases h)⟩
      · have hpB := hpresEnv₁ k b ab hsc hbk habk hne haB
        have horB₀ := (OwnReach_congr hpB l).mp horB'
        have hltL := (hvB.2.2.2.2 haB).1.1.reach_lt_size (OwnReach_toReach horB₀)
        rcases hreachF l hrF' with hge | hss | hnum
        · omega
        · exact ((hvB.2.2.2.2 haB).2.2.2.2.2.2.2 htrB).2 l horB₀ |>.2 hss
        · exact OwnReach_not_numLoc horB' hnum
      · have hpB := hpresEnv₁ k b ab hsc hbk habk hne haB
        have ⟨hrB₀, hnotSS0, hnotNum0⟩ : Reach st.heap b.val l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
          rcases hftB with hooB | ⟨hisB, _⟩
          · exact ((hvB.2.2.2.2 haB).2.2.2.2.2.1 hooB).1 l hfl
          · exact ((hvB.2.2.2.2 haB).2.2.2.2.2.2.1 hisB).1 l hfl
        have hltL := (hvB.2.2.2.2 haB).1.1.reach_lt_size hrB₀
        rcases hreachF l hrF' with hge | hss | hnum
        · omega
        · exact hnotSS0 hss
        · exact hnotNum0 ((NumLoc_congr hpB hrB₀).mpr hnum)
    have hfNrf₁ : ActiveVal σ fav → NoReachForbid st₁ Forbid BadReg BadDep fav f := by
      intro _ _ _ l hrF' hnotSS' hnotNum' hForb
      have hltF := hForbidLt l hForb
      rcases hreachF l hrF' with hge | hss | hnum
      · omega
      · exact hnotSS' (StaticStrLoc_mono hstat₁ hstr₁ hpresSS₁ hss)
      · exact hnotNum' hnum
    have hfaPair : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
        argsF[i]? = some (v, av, ft) →
        (ActiveVal σ av → Transferable σ NoKill av → ActiveVal σ fav →
          (∀ d, d ∈ av.deps → ¬ (d ∈ fav.deps)) → ∀ l, OwnReach P st₁.heap v l → ¬ Reach st₁.heap f l) ∧
        (ActiveVal σ fav → FootActive σ fav → ActiveVal σ av →
          (fav.src = none ∨ fav.src ≠ av.src) → ∀ l, False → ¬ Reach st₁.heap v l) ∧
        (ActiveVal σ av → FootActive σ av → ActiveVal σ fav →
          (av.src = none ∨ av.src ≠ fav.src) → ∀ l, ft l → ¬ Reach st₁.heap f l) ∧
        (∀ x, fav.src = some x → av.src = some x → fav.onceOnly = av.onceOnly) := by
      intro i v av ft hgi
      have hga := hArgsFGet i v av ft hgi
      have hv0 := (hargs.1 i v av ft hga).1
      refine ⟨fun haA htrA _ _ l hor' hrF' => ?_, fun _ _ _ _ _ h => False.elim h,
        fun haA hftA _ _ l hfl hrF' => ?_, fun _ hs => by cases hs⟩
      · have hpA : PreservesLocs (Reach st.heap v) st.heap st₁.heap :=
          hpresOld₁.mono fun l' hr' => (hv0.2.2.2.2 haA).1.1.reach_lt_size hr'
        have hor0 := (OwnReach_congr hpA l).mp hor'
        have hltL := (hv0.2.2.2.2 haA).1.1.reach_lt_size (OwnReach_toReach hor0)
        rcases hreachF l hrF' with hge | hss | hnum
        · omega
        · exact ((hv0.2.2.2.2 haA).2.2.2.2.2.2.2 htrA).2 l hor0 |>.2 hss
        · exact OwnReach_not_numLoc hor' hnum
      · have hpA : PreservesLocs (Reach st.heap v) st.heap st₁.heap :=
          hpresOld₁.mono fun l' hr' => (hv0.2.2.2.2 haA).1.1.reach_lt_size hr'
        have ⟨hr0, hnotSS0, hnotNum0⟩ : Reach st.heap v l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
          rcases hftA with hooA | ⟨hisA, _⟩
          · exact ((hv0.2.2.2.2 haA).2.2.2.2.2.1 hooA).1 l hfl
          · exact ((hv0.2.2.2.2 haA).2.2.2.2.2.2.1 hisA).1 l hfl
        have hltL := (hv0.2.2.2.2 haA).1.1.reach_lt_size hr0
        rcases hreachF l hrF' with hge | hss | hnum
        · omega
        · exact hnotSS0 hss
        · exact hnotNum0 ((NumLoc_congr hpA hr0).mpr hnum)
    have happs' : AApps fav (argsF.map (·.2.1)) c σ res σ' := by rw [hMapAv]; exact happs
    obtain ⟨hnoVA, hokA⟩ := applyAllS_bridge (B_a := B₁) (fuel := n') (Frame := Frame₁)
      happs' (Sim_add_staticStr hsim₁) hst₁ (fun _ h => Or.inr h)
      (fun l h => h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss))
      hnk' hnsp' hfV₁ hfDisj₁ hfNrf₁ (fun _ hne => ⟨hbvF, hclsF.to_nonValSafe hne hbvF.1.self.1⟩)
      (fun _ => Or.inl ⟨hbvF, hcfF⟩) (ArgListOk_add_staticStr hargs₁) hfaPair
      (fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂ =>
        hargsSrc i j v₁ v₂ av₁ av₂ ft₁ ft₂ x (hArgsFGet i v₁ av₁ ft₁ hg₁) (hArgsFGet j v₂ av₂ ft₂ hg₂) hs₁ hs₂)
      hEnvNrf₁ (fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁)
    rw [hMapVal] at hnoVA hokA
    refine ⟨hnoVA, fun rv st' B' hokRun => ?_⟩
    obtain ⟨resFoot, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
      hpresF₂, hpresEnv₂, hpresNum₂, honce₂, hssf₂,
      hsim₂, hEnvNrf₂, hVSim₂, hDisj₂, hNrf₂, hNv₂, hLive₂⟩ := hokA rv st' B' hokRun
    have hresSrcNone : res.src = none := by
      have hgo : ∀ {f0 : AVal} {xs : List AVal} {c0 : Cls} {s0 s1 : AState} {r0 : AVal},
          AStateOk s0 → f0.src = none → AApps f0 xs c0 s0 r0 s1 → r0.src = none := by
        intro f0 xs c0 s0 s1 r0 hokS hs0 ha
        induction ha with
        | nil => exact hs0
        | consLast hr' =>
          have hru := Runs_applyValue hokS hr'
          rcases arrowParts f0.skel with ⟨_, _, _, _⟩
          exact hru.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        | consMore hr' _ ihA =>
          have hru := Runs_applyValue hokS hr'
          rcases arrowParts f0.skel with ⟨_, _, _, _⟩
          exact ihA hru.1 hru.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact hgo hok rfl happs'
    have hle' : AStateLe σ σ' := by
      have hgo : ∀ {f0 : AVal} {xs : List AVal} {c0 : Cls} {s0 s1 : AState} {r0 : AVal},
          AStateOk s0 → AApps f0 xs c0 s0 r0 s1 → AStateLe s0 s1 := by
        intro f0 xs c0 s0 s1 r0 hokS ha
        induction ha with
        | nil => exact AStateLe.refl _
        | consLast hr' => exact (Runs_applyValue hokS hr').2.1
        | consMore hr' _ ihA =>
          have hu := Runs_applyValue hokS hr'
          exact hu.2.1.trans (ihA hu.1)
      exact hgo hok happs'
    have hpresEnvAll : PreservesActiveEnv Scope env aenv σ' st.heap st'.heap := by
      intro i b' ab hsc hbi habi hne ha'
      have hvB := ((hsim.2.2.2.2.2.1 i b' ab hsc hbi habi).2 hne).2
      have ha₀ := ActiveVal.of_AStateLe hok hle' hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) ha'
      have hp1 := hpresEnv₁ i b' ab hsc hbi habi hne ha₀
      have hp2 := hpresEnv₂ i b' ab hsc hbi habi hne ha'
      exact hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
    exact ⟨resFoot, by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
      hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
      hpresF₁.trans (hpresF₂.mono fun _ hF => Or.inl hF),
      hpresEnvAll,
      fun l o n ho hc => hpresNum₂ l o n (hpresNum₁ l o n ho hc) hc,
      honce₁.trans honce₂,
      StaticStrFresh.trans hsz₁ (hpresF₂.mono fun _ hss => Or.inr hss) hssf₁ hssf₂,
      Sim_shrink_frame (fun _ h => Or.inl h) hsim₂,
      hEnvNrf₂,
      VSim_shrink_frame (fun _ h => Or.inl h) hVSim₂,
      hDisj₂, hNrf₂, hNv₂, hLive₂, SrcOk_none hresSrcNone⟩
  -- Unfold `callWithS` and dispatch `.body` vs `.extern`
  cases fuel with
  | zero =>
    cases B_call with
    | zero =>
      have h0 : (callWithS P ext 0 r vs c).run (st, 0) = .error .outOfFuel := by
        unfold callWithS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have h0 : (callWithS P ext 0 r vs c).run (st, b + 1) = .error .outOfFuel := by
        unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n' =>
    cases B_call with
    | zero =>
      have h0 : (callWithS P ext (n' + 1) r vs c).run (st, 0) = .error .outOfFuel := by
        unfold callWithS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have hbB : b ≤ B := Nat.le_of_succ_le_succ hB
      cases d with
      | ind _ | ctor _ _ _ _ | prim _ | caseDef _ => simp [ifaceOf?] at hifc
      | stuck _ _ _ _ =>
        have h0 : (callWithS P ext (n' + 1) r vs c).run (st, b + 1) = .error .stuck := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [hfind, MS_liftM_run]; rfl
        rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | body params res' rc' rs' body =>
        simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
        have hpsEmpty : params = #[] := Array.eq_empty_of_size_eq_zero hzero
        subst hpsEmpty
        have hstep : (callWithS P ext (n' + 1) r vs c).run (st, b + 1) =
            (match (staticS P ext n' r body rc').run (st, b) with
             | .error e => .error e
             | .ok (f, (st₁, B₁)) => (applyAllS P ext n' f vs c).run (st₁, B₁)) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [hfind, Array.size_empty, Nat.not_lt_zero, ↓reduceIte, beq_self_eq_true, List.drop_zero]
          rw [MS_bind_run]
          cases (staticS P ext n' r body rc').run (st, b) with
          | error _ => rfl
          | ok p => rcases p with ⟨f, ⟨st₁, B₁⟩⟩; rfl
        rw [hstep]
        obtain ⟨hnoVS, hokS⟩ := hih.2.2 b n' r res' rc' rs' body st hbB hfind (StOk_mono (by omega) hst)
        cases hsRun : (staticS P ext n' r body rc').run (st, b) with
        | error e =>
          refine ⟨fun k hk => by cases hk; exact hnoVS k hsRun, fun _ _ _ h => by cases h⟩
        | ok ps =>
          rcases ps with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨hstep₁, hbvF, hclsF, hopenF, hnoF, hcfF, hfunF, hreachF⟩ := hokS f st₁ B₁ hsRun
          exact hCont n' b B₁ f st₁ hstep₁.1 rfl hstep₁.2.1 hstep₁.2.2.1 hstep₁.2.2.2.1
            hstep₁.2.2.2.2.1 hstep₁.2.2.2.2.2.1 hstep₁.2.2.2.2.2.2.1 hstep₁.2.2.2.2.2.2.2.1
            hstep₁.preserves_old hstep₁.2.2.2.2.2.2.2.2.2.1 hstep₁.staticStrFresh
            hbvF hclsF hopenF hnoF hcfF hfunF hreachF
      | extern params res' rc' rs' =>
        simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
        have hpsEmpty : params = #[] := Array.eq_empty_of_size_eq_zero hzero
        subst hpsEmpty
        have hstep : (callWithS P ext (n' + 1) r vs c).run (st, b + 1) =
            (match (callExtern P ext n' r #[] res' rc' []).run st with
             | .error e => .error e
             | .ok (f, st₁) => (applyAllS P ext n' f vs c).run (st₁, b)) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [hfind, Array.size_empty, Nat.not_lt_zero, ↓reduceIte, List.take_zero, List.drop_zero]
          rw [MS_bind_run, MS_liftM_run]
          cases (callExtern P ext n' r #[] res' rc' []).run st <;> rfl
        rw [hstep]
        obtain ⟨hnoVE, hokE⟩ := callExtern_sound_base (P := P) (ext := ext) (B := b) (fuel := n')
          (Frame := fun l => l < st.heap.objs.size) (baseRegs := []) (argRegs := [])
          hext hfind (StOk_mono (by omega) hst) (hih.1 b hbB)
          (fun _ hss => StOk_staticStrLoc_lt hst hss) (fun _ h => h)
          (fun _ _ _ hp => by simp at hp) (fun _ _ _ _ _ _ _ hp => by simp at hp)
        cases heRun : (callExtern P ext n' r #[] res' rc' []).run st with
        | error e =>
          refine ⟨fun k hk => by cases hk; exact hnoVE k heRun, fun _ _ _ h => by cases h⟩
        | ok pe =>
          rcases pe with ⟨f, st₁⟩; dsimp only
          obtain ⟨hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁, hpresOld₁, honce₁, hssf₁,
            hbvF, hclsF, _, hnoF, hcfF, hfunF, hreachE, _⟩ := hokE f st₁ heRun
          have hopenF := callExtern_zero_deepOpen_nil hext hfind (StOk_mono (B₁ := b) (by omega) hst) heRun
          have hreachF : ∀ l, Reach st₁.heap f l → st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st₁.heap l := by
            intro l hrl
            rcases hreachE l hrl with hge | ⟨_, _, _, hp, _⟩ | hnum
            · exact Or.inl hge
            · simp at hp
            · exact Or.inr (Or.inr hnum)
          exact hCont n' b b f st₁ (Nat.le_refl _) rfl hst₁ hsz₁ hcap₁ hr₁ hnr₁
            (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _)
            hpresOld₁ honce₁ hssf₁ hbvF hclsF hopenF hnoF hcfF hfunF hreachF

section
attribute [local instance] Classical.propDecidable

/-- Helper 1 for `ACall.ifaceFullPos`: from `Runs (callResult ifc (avs.toArray.extract 0 k) w) σ r0 σ₁`
and `ArgListOk`, constructs `FrameCall`, `argRegs`, `argOnce`, `argFoot`, and all per-argument and
pairwise disjointness hypotheses needed by both `FullIH.2.1` (`enterS`) and `callExtern_sound_base`. -/
theorem callResult_pos_args_prep {P : Prog} {ext : ExternOracle} {B_call : Nat} {st : St}
    {Frame FrameExtra NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {d : RunDef} {ifc : Iface} {w : String}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {r0 : AVal}
    (hifc : ifaceOf? d = some ifc)
    (hleLen : ifc.params.size ≤ vs.length)
    (hmatch : ArgsMatch args vs avs)
    (hErased : ∀ i, i < avs.length → (avs[i]? = some none ↔ erasedAt d i = true))
    (hrun : Runs (callResult ifc (avs.toArray.extract 0 ifc.params.size) w) σ r0 σ₁)
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (_hst : StOk P ext B_call st)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hnk₁ : NoKillOk NoKill σ₁) (hnsp₁ : NoSpendOk NoSpend σ₁)
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hargsSrc : ArgsSrcOk args)
    (hExLt : ∀ l, FrameExtra l → l < st.heap.objs.size)
    (hExU : ∀ (i : Nat) (p : Param) (v : Val) (a : AVal) (ft : Nat → Prop),
      ifc.params[i]? = some p → args[i]? = some (some (v, a, ft)) →
      p.mode.isUnique = true → a.cls = .val → ∀ l, OwnReach P st.heap v l → ¬ FrameExtra l)
    (hExO : ∀ (i : Nat) (p : Param) (v : Val) (a : AVal) (ft : Nat → Prop),
      ifc.params[i]? = some p → args[i]? = some (some (v, a, ft)) →
      p.mode.usage = .once → (a.onceOnly = true ∨ IsOnceSrc σ a) → ∀ l, ft l → ¬ FrameExtra l) :
    let k := ifc.params.size
    let vs0 := vs.take k
    let FrameCall : Nat → Prop := fun l =>
      Frame l ∨ FrameExtra l ∨ NumLoc st.heap l ∨
      ∃ (j : Nat) (b : Bnd) (ab : ABnd), Scope j ∧ env[j]? = some b ∧ aenv[j]? = some ab ∧
        ab.mode ≠ .erased ∧ ActiveVal σ₁ (effVal ab) ∧ Reach st.heap b.val l
    let argRegs : List Nat := (args.take k).flatMap fun opt =>
      match opt with | some (_, av, _) => I.regsOf av.regs | none => []
    let argOnce : Nat → Bool := fun i =>
      match ifc.params[i]?, args[i]? with
      | some p, some (some (_, av, _)) =>
        if p.mode.usage == .once then av.onceOnly || decide (IsOnceSrc σ av) else false
      | _, _ => false
    let argFoot : Nat → Nat → Prop := fun i l =>
      match ifc.params[i]?, args[i]? with
      | some p, some (some (_, av, ft)) =>
        if p.mode.usage == .once && (av.onceOnly || decide (IsOnceSrc σ av)) then ft l else False
      | _, _ => False
    (∀ l, StaticStrLoc st l → FrameCall l) ∧
    (∀ l, FrameCall l → l < st.heap.objs.size) ∧
    (∀ (i : Nat) (p : Param) (v : Val), ifc.params[i]? = some p → vs0[i]? = some v →
      (p.mode ≠ .erased →
        ValBaseOk st v ∧
        DeepOpenUnder st.heap st.regions argRegs v ∧
        CtorFieldsOk P ext B_call st v ∧
        (p.mode.usage = .once →
          FunOkAt P ext B_call st p.skel (argOnce i) (argFoot i) v ∧
          (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ FrameCall l ∧ ¬ NumLoc st.heap l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st.heap v ∧ argOnce i = false ∧ (∀ l, ¬ argFoot i l) ∧
          FunOkAt P ext B_call st p.skel false (fun _ => False) v) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st.heap v ∧
          (∀ l, OwnReach P st.heap v l → ¬ FrameCall l) ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v)))) ∧
    (∀ (i : Nat) (p : Param) (v : Val), ifc.params[i]? = some p → vs0[i]? = some v →
      ifc.res = .unique → ifc.resCls = .val → p.mode = .many → p.cls ≠ .leaf →
      DeepOpenUnder st.heap st.regions [] v) ∧
    (∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      ifc.params[i]? = some pi → vs0[i]? = some vi →
      ifc.params[j]? = some pj → vs0[j]? = some vj →
      pj.mode ≠ .erased →
      (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) ∧
      (pi.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap vj l) ∧
      (pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, argFoot i l → ¬ argFoot j l)) := by
  classical
  intro k vs0 FrameCall argRegs argOnce argFoot
  have hok := hsim.2.1
  let avs0 := avs.toArray.extract 0 k
  obtain ⟨hok₁, hle₁, hszSt₁, honce₁, hszSp₁, hreg₁, hnr₁, hclsR, hskelR, hooR, hsrcR,
    hperArg, hpairDisj, _, _, _, hspPt, hstPt⟩ := Runs_callResult hok hrun
  have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
  have havs0Get : ∀ (i : Nat), i < k → avs0[i]? = avs[i]? := by
    intro i hi
    have hiA : i < avs.toArray.size := by simp [hlenEq]; omega
    simp [avs0, hi]
  have hvs0Get : ∀ (i : Nat) (v : Val), vs0[i]? = some v → i < k ∧ vs[i]? = some v := by
    intro i v hv
    have hi : i < k := by
      have h1 := (List.getElem?_eq_some_iff.mp hv).1
      rw [List.length_take] at h1; omega
    rw [List.getElem?_take_of_lt hi] at hv
    exact ⟨hi, hv⟩
  have hParamNE : ∀ (i : Nat) (p : Param) (v : Val), ifc.params[i]? = some p → vs0[i]? = some v →
      p.mode ≠ .erased → ∃ av ft, args[i]? = some (some (v, av, ft)) ∧ avs0[i]? = some (some av) := by
    intro i p v hp hv0 hne
    obtain ⟨hi, hv⟩ := hvs0Get i v hv0
    have hiA : i < avs.length := by rw [hlenEq]; omega
    rcases ArgsMatch_getElem_vs hmatch hv with ⟨_, _, ha⟩ | ⟨av, ft, hg, ha⟩
    · have her := (hErased i hiA).mp ha
      rw [erasedAt_of_ifaceOf hifc i, hp] at her
      exact absurd (eq_of_beq her) hne
    · exact ⟨av, ft, hg, by rw [havs0Get i hi, ha]⟩
  have hArgKilledU : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) →
      p.mode.isUnique = true → a.cls = .val → ∀ x ∈ a.deps, σ₁.st[x]? = some .dead := by
    intro i p a hp ha hu hcv x hx
    obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (ifc.resCls != .val)).mpr hu
    have hvd := (hperArg i p a hp ha).1
    have h1 := hstPt x (hvd x hx).1
    have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
        (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
        callKills (ifc.resCls != .val) p' a' x := ⟨i, p, a, hp, ha, Or.inl ⟨b, hdu, hcv, hx⟩⟩
    split at h1
    · exact h1
    · rename_i hn; exact False.elim (hn hex)
  have hArgKilledO : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) →
      p.mode.usage = .once → a.onceOnly = true → ∀ x, a.src = some x → σ₁.st[x]? = some .dead := by
    intro i p a hp ha ho hoo x hs
    have hdo : destOf p (ifc.resCls != .val) = .once := (destOf_once_iff p _).mpr ho
    have hi : i < k := (Array.getElem?_eq_some_iff.mp hp).1
    obtain ⟨v', ft', hg', _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
    have hsrcD := (hargs.1 i v' a ft' hg').1.2.2.1 x hs
    have h1 := hstPt x hsrcD.1
    have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
        (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
        callKills (ifc.resCls != .val) p' a' x := ⟨i, p, a, hp, ha, Or.inr ⟨hdo, hoo, hs⟩⟩
    split at h1
    · exact h1
    · rename_i hn; exact False.elim (hn hex)
  have hArgSpentO : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) →
      ∀ x ∈ a.deps, σ.once[x]? = some true → σ₁.spent[x]? = some true := by
    intro i p a hp ha x hx ho
    have hvd := (hperArg i p a hp ha).1
    have hltSp : x < σ.spent.size := by have h1 := (hvd x hx).1; have h2 := hok.2.1; omega
    have h1 := hspPt x hltSp
    have hex : (∃ (i' : Nat) (p' : Param) (a' : AVal),
        ifc.params[i']? = some p' ∧ (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧ x ∈ a'.deps) ∧
        σ.once[x]? = some true :=
      ⟨⟨i, p, a, hp, ha, hx⟩, ho⟩
    split at h1
    · exact h1
    · rename_i hn; exact False.elim (hn hex)
  have hArgAct : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) →
      ActiveVal σ a := by
    intro i p a hp ha
    obtain ⟨hvd, honce, hnonOnce, _, _⟩ := hperArg i p a hp ha
    refine ⟨hvd, fun his => ?_⟩
    by_cases hdo : destOf p (ifc.resCls != .val) = .once
    · exact (honce hdo).2
    · exact False.elim ((hnonOnce hdo).2.2 his)
  have hArgTr : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) →
      p.mode.isUnique = true → a.cls = .val → Transferable σ NoKill a := by
    intro i p a hp ha hu hcv
    obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (ifc.resCls != .val)).mpr hu
    have hneO : destOf p (ifc.resCls != .val) ≠ .once := by rw [hdu]; intro h; cases h
    obtain ⟨_, _, hnonOnce, huniq, _⟩ := hperArg i p a hp ha
    obtain ⟨_, hoo, hnotOS⟩ := hnonOnce hneO
    obtain ⟨hown, hlv, _⟩ := huniq b hdu hcv
    exact ⟨hcv, hown, hoo, hnotOS, fun x hx => ⟨hlv x hx, fun hnk => hnk₁ x hnk (hArgKilledU i p a hp ha hu hcv x hx)⟩⟩
  have hFCallLt : ∀ l, FrameCall l → l < st.heap.objs.size := by
    rintro l (hF | hEx | ⟨o, _, ho, _⟩ | ⟨j, b, ab, hsc, hbj, habj, hne, ha₁, hrB⟩)
    · exact hFlt l hF
    · exact hExLt l hEx
    · exact (Array.getElem?_eq_some_iff.mp ho).1
    · have hvB := ((hsim.2.2.2.2.2.1 j b ab hsc hbj habj).2 hne).2
      have ha₀ := ActiveVal.of_AStateLe hok hle₁ hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) ha₁
      exact (hvB.2.2.2.2 ha₀).1.1.reach_lt_size hrB
  refine ⟨fun _ hss => Or.inl (hstat _ hss), hFCallLt, ?_, ?_, ?_⟩
  · -- Per-argument properties
    intro i p v hp hv0 hne
    obtain ⟨hi, hv⟩ := hvs0Get i v hv0
    obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hne
    obtain ⟨hvSim, hdisjA, _, hnvA⟩ := hargs.1 i v av ft hg
    have hact := hArgAct i p av hp ha
    obtain ⟨hbv, hdou, hcf, _, hpl, hooP, hosP, htrP⟩ := hvSim.2.2.2.2 hact
    obtain ⟨hvd, honceA, hnonOnceA, huniqA, _⟩ := hperArg i p av hp ha
    have hdouAll : DeepOpenUnder st.heap st.regions argRegs v := by
      refine hdou.mono fun c hc => List.mem_flatMap.mpr ⟨some (v, av, ft), ?_, hc⟩
      have hgTake : (args.take k)[i]? = some (some (v, av, ft)) := by rw [List.getElem?_take_of_lt hi, hg]
      exact List.mem_of_getElem? hgTake
    refine ⟨hbv, hdouAll, hcf, ?_, ?_, ?_⟩
    · -- `p.mode.usage = .once`
      intro hoU
      have hdo : destOf p (ifc.resCls != .val) = .once := (destOf_once_iff p _).mpr hoU
      have hadm : av.skel.admitsNA p.skel = true := Skel.admitsNA_symm p.skel av.skel ▸ (honceA hdo).1
      have hoUbeq : (p.mode.usage == .once) = true := by rw [hoU]; rfl
      have hnotFCall : (av.onceOnly = true ∨ IsOnceSrc σ av) → ∀ l, ft l → ¬ FrameCall l := by
        rintro hdisj l hfl (hF | hEx | hNum | ⟨j, b, ab, hsc, hbj, habj, hneB, haB₁, hrB⟩)
        · rcases hdisj with hoo | his
          · exact (hooP hoo).2.1 (fun x hs hnk => hnk₁ x hnk (hArgKilledO i p av hp ha hoU hoo x hs)) l hfl hF
          · exact (hosP his).2.1 (fun d hd hoD hnsp => hnsp₁ d hnsp (hArgSpentO i p av hp ha d hd hoD)) l hfl hF
        · exact hExO i p v av ft hp hg hoU hdisj l hfl hEx
        · rcases hdisj with hoo | his
          · exact ((hooP hoo).1 l hfl).2.2 hNum
          · exact ((hosP his).1 l hfl).2.2 hNum
        · have hvB := ((hsim.2.2.2.2.2.1 j b ab hsc hbj habj).2 hneB).2
          have haB₀ := ActiveVal.of_AStateLe hok hle₁ hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) haB₁
          have hftAct : FootActive σ av := by
            rcases hdisj with hoo | his
            · exact Or.inl hoo
            · exact Or.inr ⟨his, (honceA hdo).2⟩
          have hneSrc : av.src ≠ some ab.id := by
            intro hs
            have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
            rcases hdisj with hoo | ⟨id, hs1, ho1⟩
            · exact (haB₁.1 ab.id habMem).2 (hArgKilledO i p av hp ha hoU hoo ab.id hs)
            · rw [hs] at hs1; cases hs1
              have hsp := hArgSpentO i p av hp ha ab.id (hvSim.2.2.1 ab.id hs).2 ho1
              have ho₁' : σ₁.once[ab.id]? = some true := by rw [honce₁]; exact ho1
              have hspF := haB₁.2 ⟨ab.id, by simp [effVal], ho₁'⟩ ab.id habMem ho₁'
              rw [hsp] at hspF; cases hspF
          exact (hdisjA j b ab hsc hbj habj hneB).2.2.1 hact hftAct haB₀ hneSrc l hfl hrB
      by_cases hoo : av.onceOnly = true
      · have haoT : argOnce i = true := by dsimp only [argOnce]; rw [hp, hg]; dsimp only; rw [hoUbeq, hoo]; rfl
        have haftEq : argFoot i = ft := by funext l; dsimp only [argFoot]; rw [hp, hg]; dsimp only; rw [hoUbeq, hoo]; rfl
        rw [haoT, haftEq]
        exact ⟨FunOkAt_of_admitsNA hadm (hooP hoo).2.2.2,
          fun l hfl => ⟨((hooP hoo).1 l hfl).1, hnotFCall (Or.inl hoo) l hfl, ((hooP hoo).1 l hfl).2.2⟩⟩
      · by_cases his : IsOnceSrc σ av
        · have haoT : argOnce i = true := by
            dsimp only [argOnce]; rw [hp, hg]; dsimp only; rw [hoUbeq, decide_eq_true his]; simp
          have haftEq : argFoot i = ft := by
            funext l; dsimp only [argFoot]; rw [hp, hg]; dsimp only; rw [hoUbeq, decide_eq_true his]; simp
          rw [haoT, haftEq]
          exact ⟨FunOkAt_of_admitsNA hadm (hosP his).2.2,
            fun l hfl => ⟨((hosP his).1 l hfl).1, hnotFCall (Or.inr his) l hfl, ((hosP his).1 l hfl).2.2⟩⟩
        · have hooF : av.onceOnly = false := Bool.eq_false_iff.mpr hoo
          have haoF : argOnce i = false := by
            dsimp only [argOnce]; rw [hp, hg]; dsimp only; rw [hoUbeq, hooF, decide_eq_false his]; rfl
          have haftEq : argFoot i = fun _ => False := by
            funext l; dsimp only [argFoot]; rw [hp, hg]; dsimp only; rw [hoUbeq, hooF, decide_eq_false his]; rfl
          rw [haoF, haftEq]
          exact ⟨FunOkAt_of_admitsNA hadm (hpl ⟨his, hooF⟩).2.2, fun _ h => False.elim h⟩
    · -- `p.mode.usage ≠ .once`
      intro hnuO
      have hneO : destOf p (ifc.resCls != .val) ≠ .once := fun h => hnuO ((destOf_once_iff p _).mp h)
      obtain ⟨hadm0, hooF, hnotOS⟩ := hnonOnceA hneO
      have hadm : av.skel.admits p.skel = true := Skel.admits_symm p.skel av.skel ▸ hadm0
      have hbf : (p.mode.usage == .once) = false := beq_false_of_ne hnuO
      have haoF : argOnce i = false := by dsimp only [argOnce]; rw [hp, hg]; dsimp only; rw [hbf]; rfl
      have haftF : ∀ l, ¬ argFoot i l := fun l h => by dsimp only [argFoot] at h; rw [hp, hg] at h; dsimp only at h; rw [hbf] at h; exact h
      exact ⟨(hpl ⟨hnotOS, hooF⟩).1, haoF, haftF, FunOkAt_of_admits hadm (hpl ⟨hnotOS, hooF⟩).2.2⟩
    · -- `p.mode.isUnique = true`
      intro hu
      obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (ifc.resCls != .val)).mpr hu
      by_cases hcv : av.cls = .val
      · have htr := hArgTr i p av hp ha hu hcv
        obtain ⟨hotf, hown⟩ := htrP htr
        refine ⟨hotf, fun l hor hfc => ?_, fun hnb => ?_⟩
        · rcases hfc with hF | hEx | hNum | ⟨j, b', ab, hsc, hbj, habj, hneB, haB₁, hrB⟩
          · exact (hown l hor).1 hF
          · exact hExU i p v av ft hp hg hu hcv l hor hEx
          · exact OwnReach_not_numLoc hor hNum
          · have hvB := ((hsim.2.2.2.2.2.1 j b' ab hsc hbj habj).2 hneB).2
            have haB₀ := ActiveVal.of_AStateLe hok hle₁ hvB.2.1 (fun x hx => (hvB.2.2.1 x hx).1) haB₁
            have hdd : ∀ x, x ∈ av.deps → ¬ (x ∈ (effVal ab).deps) := fun x hx hxb =>
              (haB₁.1 x hxb).2 (hArgKilledU i p av hp ha hu hcv x hx)
            exact (hdisjA j b' ab hsc hbj habj hneB).1 hact htr haB₀ hdd l hor hrB
        · have hbf : b = false := by
            cases hm : p.mode <;> simp [hm, destOf, BinderMode.isUnique, BinderMode.isBorrowed] at hu hnb hdu
            exact hdu
          have hregs0 := (huniqA b hdu hcv).2.2 hbf
          rw [hregs0, Interp.regsOf_nil] at hdou; exact hdou
      · have hnv' := (hnvA hvd hcv).2
        exact ⟨hnv'.ownTreeFull.1, fun l hor _ => hnv'.ownTreeFull.2 l hor, fun _ => hnv'.deepOpenUnder_nil⟩
  · -- Repair U `.many` unconfined condition for `callExtern_sound_base`
    intro i p v hp hv0 hru hrc hpm hneLeaf
    have hne : p.mode ≠ .erased := by rw [hpm]; decide
    obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hne
    obtain ⟨hvd, _, _, _, hrepU⟩ := hperArg i p av hp ha
    by_cases hcv : av.cls = .val
    · have haNeLeaf : av.cls ≠ .leaf := by rw [hcv]; decide
      have hdoS : destOf p (ifc.resCls != .val) = .share := by
        have hcf : (ifc.resCls != .val) = false := by rw [hrc]; rfl
        simp [destOf, hpm, hcf, BinderMode.isUnique, BinderMode.usage, BinderMode.isBorrowed]
      have hregs0 := hrepU hru hrc haNeLeaf hneLeaf (Or.inl hdoS)
      have hdou := ((hargs.1 i v av ft hg).1.2.2.2.2 (hArgAct i p av hp ha)).2.1
      rw [hregs0, Interp.regsOf_nil] at hdou; exact hdou
    · exact ((hargs.1 i v av ft hg).2.2.2 hvd hcv).2.deepOpenUnder_nil
  · -- Pairwise disjointness across call arguments
    intro i j pi pj vi vj hij hpi hvi0 hpj hvj0 hnej
    have hnei_of_u : pi.mode.isUnique = true → pi.mode ≠ .erased := fun h => by
      cases hm : pi.mode <;> rw [hm] at h <;> simp [BinderMode.isUnique] at h ⊢
    have hnei_of_o : pi.mode.usage = .once → pi.mode ≠ .erased := fun h => by
      cases hm : pi.mode <;> rw [hm] at h <;> simp [BinderMode.usage] at h ⊢
    obtain ⟨aj, ftj, hgj, haj⟩ := hParamNE j pj vj hpj hvj0 hnej
    have hactJ := hArgAct j pj aj hpj haj
    have hFootDisj : pi.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap vj l := by
      intro hoi l hfi hrj
      obtain ⟨ai, fti, hgi, hai⟩ := hParamNE i pi vi hpi hvi0 (hnei_of_o hoi)
      have hoiBeq : (pi.mode.usage == .once) = true := by rw [hoi]; rfl
      simp only [argFoot, hpi, hgi, hoiBeq, Bool.true_and] at hfi
      split at hfi
      · rename_i hcond
        have hactI := hArgAct i pi ai hpi hai
        have hdoi : destOf pi (ifc.resCls != .val) = .once := (destOf_once_iff pi _).mpr hoi
        have hvI := (hargs.1 i vi ai fti hgi).1
        have hvJ := (hargs.1 j vj aj ftj hgj).1
        have hdisjI : ai.onceOnly = true ∨ IsOnceSrc σ ai := by
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hcond; exact hcond
        have hftActI : FootActive σ ai := by
          rcases hdisjI with hoo | his
          · exact Or.inl hoo
          · exact Or.inr ⟨his, ((hperArg i pi ai hpi hai).2.1 hdoi).2⟩
        have hneSrc : ai.src = none ∨ ai.src ≠ aj.src := by
          cases hisI : ai.src with
          | none => exact Or.inl rfl
          | some x =>
            right; intro hEq
            have hxI : x ∈ ai.deps := (hvI.2.2.1 x hisI).2
            have hxJ : x ∈ aj.deps := (hvJ.2.2.1 x hEq.symm).2
            rcases hdisjI with hoo | ⟨id, hs1, ho1⟩
            · rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
              · exact (hpairDisj i j pi pj ai aj hij hpi hai hpj haj).2.1 hdoi hoo x hisI (Or.inl hlt) hxJ
              · by_cases hdojL : destOf pj (ifc.resCls != .val) = .lend
                · exact (hpairDisj i j pi pj ai aj hij hpi hai hpj haj).2.1 hdoi hoo x hisI (Or.inr hdojL) hxJ
                · by_cases hdojO : destOf pj (ifc.resCls != .val) = .once
                  · have hooJ : aj.onceOnly = true := (hargsSrc i j vi vj ai aj fti ftj x hgi hgj hisI hEq.symm).symm.trans hoo
                    exact (hpairDisj j i pj pi aj ai hij.symm hpj haj hpi hai).2.1 hdojO hooJ x hEq.symm (Or.inl hgt) hxI
                  · have hooJF := ((hperArg j pj aj hpj haj).2.2.1 hdojO).2.1
                    have hooJT : aj.onceOnly = true := (hargsSrc i j vi vj ai aj fti ftj x hgi hgj hisI hEq.symm).symm.trans hoo
                    rw [hooJF] at hooJT; cases hooJT
            · rw [hisI] at hs1; cases hs1
              rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
              · by_cases hdojO : destOf pj (ifc.resCls != .val) = .once
                · exact (hpairDisj i j pi pj ai aj hij hpi hai hpj haj).2.2 hlt hdojO x hxJ ho1 hxI
                · exact ((hperArg j pj aj hpj haj).2.2.1 hdojO).2.2 ⟨x, hEq.symm, ho1⟩
              · exact (hpairDisj j i pj pi aj ai hij.symm hpj haj hpi hai).2.2 hgt hdoi x hxI ho1 hxJ
        exact (hargs.2 i j vi vj ai aj fti ftj hij hgi hgj).2 hactI hftActI hactJ hneSrc l hfi hrj
      · exact hfi
    refine ⟨?_, hFootDisj, fun hoi hoj l hfi hfj => ?_⟩
    · -- `pi.mode.isUnique = true`
      intro hui l hor hrj
      obtain ⟨ai, fti, hgi, hai⟩ := hParamNE i pi vi hpi hvi0 (hnei_of_u hui)
      by_cases hcvi : ai.cls = .val
      · by_cases hcvj : aj.cls = .val
        · obtain ⟨b, hdui⟩ := (destOf_isUniq_iff pi (ifc.resCls != .val)).mpr hui
          have hdd := (hpairDisj i j pi pj ai aj hij hpi hai hpj haj).1 b hdui hcvi (Or.inr (Or.inr hcvj))
          exact (hargs.2 i j vi vj ai aj fti ftj hij hgi hgj).1
            (hArgAct i pi ai hpi hai) (hArgTr i pi ai hpi hai hui hcvi) hactJ hdd l hor hrj
        · exact OwnReach_not_numLoc hor
            (((hargs.1 j vj aj ftj hgj).2.2.2 (hperArg j pj aj hpj haj).1 hcvj).2.reach_numLoc hrj)
      · exact ((hargs.1 i vi ai fti hgi).2.2.2 (hperArg i pi ai hpi hai).1 hcvi).2.ownTreeFull.2 l hor
    · -- `argFoot i l → ¬ argFoot j l`
      have hojBeq : (pj.mode.usage == .once) = true := by rw [hoj]; rfl
      simp only [argFoot, hpj, hgj, hojBeq, Bool.true_and] at hfj
      split at hfj
      · rename_i hcondJ
        have hvJ := (hargs.1 j vj aj ftj hgj).1
        have hdisjJ : aj.onceOnly = true ∨ IsOnceSrc σ aj := by
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hcondJ; exact hcondJ
        have hrj : Reach st.heap vj l := by
          rcases hdisjJ with hooJ | hisJ
          · exact ((hvJ.2.2.2.2 hactJ).2.2.2.2.2.1 hooJ).1 l hfj |>.1
          · exact ((hvJ.2.2.2.2 hactJ).2.2.2.2.2.2.1 hisJ).1 l hfj |>.1
        exact hFootDisj hoi l hfi hrj
      · exact hfj

/-- Helper 2 for `ACall.ifaceFullPos`: turns the result `(f, st₁, B₁)` of either `enterS` or
`callExtern` on `vs.take k` into `Sim`, `EnvNoReachForbid`, `VSim`, `ValEnvDisj`, `NoReachForbid`,
`NonValSafe`, and `FrameExtra` disjointness on `(r0, f)`. -/
theorem callResult_pos_post {P : Prog} {ext : ExternOracle} {B_call B₁ : Nat} {st st₁ : St}
    {Frame FrameExtra NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ₁ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {d : RunDef} {ifc : Iface} {w : String}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {r0 : AVal} {f : Val}
    (hifc : ifaceOf? d = some ifc)
    (hleLen : ifc.params.size ≤ vs.length)
    (hmatch : ArgsMatch args vs avs)
    (hErased : ∀ i, i < avs.length → (avs[i]? = some none ↔ erasedAt d i = true))
    (hrun : Runs (callResult ifc (avs.toArray.extract 0 ifc.params.size) w) σ r0 σ₁)
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hBadDepLive : ∀ x, BadDep x → σ₁.st[x]? = some .live)
    (hB₁ : B₁ ≤ B_call) (_hst₁ : StOk P ext B₁ st₁)
    (_hsz₁ : st.heap.objs.size ≤ st₁.heap.objs.size)
    (hr₁ : st₁.regions = st.regions) (hnr₁ : st.nextRegion ≤ st₁.nextRegion)
    (hstat₁ : ArrayExtends st.statics st₁.statics) (hstr₁ : ArrayExtends st.strs st₁.strs)
    (hpresCall : PreservesLocs (fun l => Frame l ∨ FrameExtra l ∨ NumLoc st.heap l ∨
      ∃ (j : Nat) (b : Bnd) (ab : ABnd), Scope j ∧ env[j]? = some b ∧ aenv[j]? = some ab ∧
        ab.mode ≠ .erased ∧ ActiveVal σ₁ (effVal ab) ∧ Reach st.heap b.val l) st.heap st₁.heap)
    (honce₁ : PreservesOnceShell st.heap st₁.heap) (hssf₁ : StaticStrFresh st st₁)
    (hbvF : ValBaseOk st₁ f) (hclsF : ClsSafe st₁.heap ifc.resCls f)
    (hnoF : NoOnceCell st₁.heap f) (hcfF : CtorFieldsOk P ext B₁ st₁ f)
    (hfunF : FunOkAt P ext B₁ st₁ ifc.resSkel false (fun _ => False) f)
    (hopenF : DeepOpenUnder st₁.heap st₁.regions
      (applyResultRegs st ifc.res ifc.resCls []
        ((args.take ifc.params.size).flatMap fun opt =>
          match opt with | some (_, av, _) => I.regsOf av.regs | none => [])) f)
    (hreachF : ∀ l, Reach st₁.heap f l →
      st.heap.objs.size ≤ l ∨
      (∃ (i : Nat) (p : Param) (v : Val),
        ifc.params[i]? = some p ∧ (vs.take ifc.params.size)[i]? = some v ∧ p.mode ≠ .erased ∧
        (ifc.res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧ Reach st.heap v l) ∨
      StaticStrLoc st l ∨ NumLoc st₁.heap l)
    (huniqF : ifc.res.isUnique = true ∧ ifc.resCls = .val →
      OwnTreeFull P st₁.heap f ∧
      ∀ l, OwnReach P st₁.heap f l →
        ¬ (Frame l ∨ FrameExtra l ∨ NumLoc st.heap l ∨
          ∃ (j : Nat) (b : Bnd) (ab : ABnd), Scope j ∧ env[j]? = some b ∧ aenv[j]? = some ab ∧
            ab.mode ≠ .erased ∧ ActiveVal σ₁ (effVal ab) ∧ Reach st.heap b.val l) ∧
        ¬ StaticStrLoc st₁ l)
    (hLeafNum : ∀ (i : Nat) (p : Param) (v : Val),
      ifc.params[i]? = some p → (vs.take ifc.params.size)[i]? = some v →
      p.mode ≠ .erased → p.cls = .leaf → ∀ l, Reach st.heap v l → NumLoc st.heap l) :
    PreservesLocs Frame st.heap st₁.heap ∧
    PreservesLocs FrameExtra st.heap st₁.heap ∧
    PreservesActiveEnv Scope env aenv σ₁ st.heap st₁.heap ∧
    (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st₁.heap.objs[l]? = some o) ∧
    Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot ∧
    EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep ∧
    VSim P ext B₁ st₁ Frame NoKill NoSpend σ₁ I (fun _ => False) r0 f ∧
    ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot (fun _ => False) r0 f ∧
    (ActiveVal σ₁ r0 → NoReachForbid st₁ Forbid BadReg BadDep r0 f) ∧
    (ValidDeps σ₁ r0.deps → r0.cls ≠ .val → ValBaseOk st₁ f ∧ NonValSafe st₁.heap f) ∧
    (Transferable σ₁ NoKill r0 → ∀ l, OwnReach P st₁.heap f l → ¬ FrameExtra l) := by
  have hok := hsim.2.1
  have hIok := hsim.2.2.1
  let k := ifc.params.size
  let avs0 := avs.toArray.extract 0 k
  obtain ⟨hok₁, hle₁, hszSt₁, honceEq₁, hszSp₁, hregEq₁, hnrEq₁, hclsR, hskelR, hooR, hsrcR,
    hperArg, _, hIrrImmR, hLeafR, hValR, hspPt, hstPt⟩ := Runs_callResult hok hrun
  have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
  have havs0Get : ∀ (i : Nat), i < k → avs0[i]? = avs[i]? := by
    intro i hi
    simp [avs0, hi]
  have hParamNE : ∀ (i : Nat) (p : Param) (v : Val), ifc.params[i]? = some p → (vs.take k)[i]? = some v →
      p.mode ≠ .erased → ∃ av ft, args[i]? = some (some (v, av, ft)) ∧ avs0[i]? = some (some av) := by
    intro i p v hp hv0 hne
    have hi : i < k := by have h1 := (List.getElem?_eq_some_iff.mp hv0).1; rw [List.length_take] at h1; omega
    rw [List.getElem?_take_of_lt hi] at hv0
    have hiA : i < avs.length := by rw [hlenEq]; omega
    rcases ArgsMatch_getElem_vs hmatch hv0 with ⟨_, _, ha⟩ | ⟨av, ft, hg, ha⟩
    · have her := (hErased i hiA).mp ha
      rw [erasedAt_of_ifaceOf hifc i, hp] at her
      exact absurd (eq_of_beq her) hne
    · exact ⟨av, ft, hg, by rw [havs0Get i hi, ha]⟩
  have hArgAct : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) →
      ActiveVal σ a := by
    intro i p a hp ha
    obtain ⟨hvd, honce, hnonOnce, _, _⟩ := hperArg i p a hp ha
    refine ⟨hvd, fun his => ?_⟩
    by_cases hdo : destOf p (ifc.resCls != .val) = .once
    · exact (honce hdo).2
    · exact False.elim ((hnonOnce hdo).2.2 his)
  have hpresF : PreservesLocs Frame st.heap st₁.heap := hpresCall.mono fun _ h => Or.inl h
  have hpresEx : PreservesLocs FrameExtra st.heap st₁.heap := hpresCall.mono fun _ h => Or.inr (Or.inl h)
  have hpresNum : ∀ (l : Nat) (o : Obj) (n : Nat),
      st.heap.objs[l]? = some o → o.cell = .num n → st₁.heap.objs[l]? = some o :=
    fun l o n ho hc => (hpresCall l (Or.inr (Or.inr (Or.inl ⟨o, n, ho, hc⟩)))).trans ho
  have hpresEnv : PreservesActiveEnv Scope env aenv σ₁ st.heap st₁.heap :=
    fun j b ab hsc hbj habj hne ha₁ =>
      hpresCall.mono fun l hr => Or.inr (Or.inr (Or.inr ⟨j, b, ab, hsc, hbj, habj, hne, ha₁, hr⟩))
  have hpresSS : PreservesLocs (StaticStrLoc st) st.heap st₁.heap := hpresF.mono fun _ h => hstat _ h
  have hrf₁ : RegsFuture st st₁ := RegsFuture.same_regions hnr₁ hr₁
  have hIok₁ : InterpOk σ₁ st₁ I :=
    ⟨fun r' hr' c' hc' => Nat.lt_of_lt_of_le (hIok.1 r' (hnrEq₁ ▸ hr') c' hc') hnr₁,
     fun c' hc' => by rw [hregEq₁]; exact hIok.2 c' (hr₁ ▸ hc')⟩
  have hsim₁ : Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot :=
    Sim_step hB₁ hle₁ hok₁ hIok₁ hrf₁ honce₁ hssf₁ (fun _ _ _ h => h) hpresEnv hsim
  have hEnvNrf₁ : EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep :=
    EnvNoReachForbid_step hok hle₁ (Sim_deps_lt hsim) hsim.2.2.2.1 hstat₁ hstr₁ hpresSS hpresEnv hEnvNrf
  -- Show `r0.own = .uniq ∧ r0.cls = .val → ifc.res.isUnique = true ∧ ifc.resCls = .val`
  have hr0Uniq : r0.cls = .val → r0.own = .uniq → ifc.res.isUnique = true ∧ ifc.resCls = .val := by
    intro hcv hown
    have hrcV : ifc.resCls = .val := hclsR.symm.trans hcv
    refine ⟨?_, hrcV⟩
    obtain ⟨hu, hub, hb, hsh⟩ := hValR hrcV
    cases hrm : ifc.res with
    | unique | uniqueBorrowed => rfl
    | borrowed => rw [(hb hrm).1] at hown; cases hown
    | shared => rw [(hsh hrm).1] at hown; cases hown
  -- Show `DeepOpenUnder st₁.heap st₁.regions (I.regsOf r0.regs) f`
  have hOpenR0 : DeepOpenUnder st₁.heap st₁.regions (I.regsOf r0.regs) f := by
    by_cases hrcV : ifc.resCls = .val
    · have hArgRegsSub : ∀ c', c' ∈ ((args.take k).flatMap fun opt =>
          match opt with | some (_, av, _) => I.regsOf av.regs | none => []) →
          ∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs0[i]? = some (some a) ∧ c' ∈ I.regsOf a.regs := by
        intro c' hc'
        obtain ⟨opt, hoptM, hcOpt⟩ := List.mem_flatMap.mp hc'
        cases opt with
        | none => cases hcOpt
        | some t =>
          rcases t with ⟨v, av, ft⟩
          obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hoptM
          have hiK : i < k := by rw [List.length_take] at hi; omega
          have hgi : args[i]? = some (some (v, av, ft)) := by
            have h1 := List.getElem?_eq_getElem hi
            rw [hget, List.getElem?_take_of_lt hiK] at h1; exact h1
          have ha : avs0[i]? = some (some av) := by
            rw [havs0Get i hiK]; have h1 := hmatch.2.2 i; rw [hgi] at h1; exact h1.2
          exact ⟨i, ifc.params[i], av, Array.getElem?_eq_getElem hiK, ha, hcOpt⟩
      obtain ⟨_, hub, hb, hsh⟩ := hValR hrcV
      refine hopenF.mono fun c' hc' => ?_
      rw [hrcV] at hc'
      cases hrm : ifc.res with
      | unique =>
        rw [hrm] at hc'; simp [applyResultRegs] at hc'
      | uniqueBorrowed =>
        rw [hrm] at hc'; unfold applyResultRegs at hc'
        simp only [List.append_nil] at hc'
        cases hrg : st.regions with
        | nil =>
          rw [hrg] at hc'
          obtain ⟨i, p, a, hp, ha, hcA⟩ := hArgRegsSub c' hc'
          obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hcA
          exact Interp.mem_regsOf.mpr ⟨r', ((hub hrm).2.2 r').mpr (Or.inr ⟨i, p, a, hp, ha, hr'⟩), hc1⟩
        | cons h0 tl =>
          rw [hrg] at hc'
          rcases List.mem_cons.mp hc' with rfl | hArg
          · exact Interp.mem_regsOf.mpr ⟨σ.regions.headD 1, ((hub hrm).2.2 _).mpr (Or.inl rfl),
              hIok.2 c' (by rw [hrg]; rfl)⟩
          · obtain ⟨i, p, a, hp, ha, hcA⟩ := hArgRegsSub c' hArg
            obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hcA
            exact Interp.mem_regsOf.mpr ⟨r', ((hub hrm).2.2 r').mpr (Or.inr ⟨i, p, a, hp, ha, hr'⟩), hc1⟩
      | borrowed =>
        rw [hrm] at hc'; unfold applyResultRegs at hc'
        simp only [List.append_nil] at hc'
        cases hrg : st.regions with
        | nil =>
          rw [hrg] at hc'
          obtain ⟨i, p, a, hp, ha, hcA⟩ := hArgRegsSub c' hc'
          obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hcA
          exact Interp.mem_regsOf.mpr ⟨r', ((hb hrm).2.2 r').mpr (Or.inr ⟨i, p, a, hp, ha, hr'⟩), hc1⟩
        | cons h0 tl =>
          rw [hrg] at hc'
          rcases List.mem_cons.mp hc' with rfl | hArg
          · exact Interp.mem_regsOf.mpr ⟨σ.regions.headD 1, ((hb hrm).2.2 _).mpr (Or.inl rfl),
              hIok.2 c' (by rw [hrg]; rfl)⟩
          · obtain ⟨i, p, a, hp, ha, hcA⟩ := hArgRegsSub c' hArg
            obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hcA
            exact Interp.mem_regsOf.mpr ⟨r', ((hb hrm).2.2 r').mpr (Or.inr ⟨i, p, a, hp, ha, hr'⟩), hc1⟩
      | shared =>
        rw [hrm] at hc'; unfold applyResultRegs at hc'
        simp only [List.append_nil] at hc'
        obtain ⟨i, p, a, hp, ha, hcA⟩ := hArgRegsSub c' hc'
        obtain ⟨r', hr', hc1⟩ := Interp.mem_regsOf.mp hcA
        exact Interp.mem_regsOf.mpr ⟨r', ((hsh hrm).2.2 r').mpr ⟨i, p, a, hp, ha, hr'⟩, hc1⟩
    · exact (hclsF.to_nonValSafe hrcV hbvF.1.self.1).deepOpenUnder_nil
  -- Bounds on `r0.regs` and `r0.deps`
  have hr0RegsBnd : ∀ r' ∈ r0.regs, r' < σ₁.nextRegion := by
    intro r' hr'
    rw [hnrEq₁]
    cases hrc : ifc.resCls with
    | irr | imm => rw [hIrrImmR (by rw [hrc]; simp)] at hr'; cases hr'
    | leaf => rw [hLeafR hrc] at hr'; cases hr'
    | val =>
      obtain ⟨hu, hub, hb, hsh⟩ := hValR hrc
      have hheadLt : σ.regions.headD 1 < σ.nextRegion := by
        cases hrL : σ.regions with
        | nil => simp [List.headD]; have := hok.2.2.1; omega
        | cons r0' _ => exact (hok.2.2.2.2.2 r0' (by rw [hrL]; exact List.mem_cons_self)).2
      cases hrm : ifc.res with
      | unique => rw [hu hrm] at hr'; cases hr'
      | uniqueBorrowed =>
        rcases ((hub hrm).2.2 r').mp hr' with rfl | ⟨i, p, a, hp, ha, hrA⟩
        · exact hheadLt
        · have hi := (Array.getElem?_eq_some_iff.mp hp).1
          obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
          exact (hargs.1 i v a ft hg).1.1 r' hrA
      | borrowed =>
        rcases ((hb hrm).2.2 r').mp hr' with rfl | ⟨i, p, a, hp, ha, hrA⟩
        · exact hheadLt
        · have hi := (Array.getElem?_eq_some_iff.mp hp).1
          obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
          exact (hargs.1 i v a ft hg).1.1 r' hrA
      | shared =>
        obtain ⟨i, p, a, hp, ha, hrA⟩ := ((hsh hrm).2.2 r').mp hr'
        have hi := (Array.getElem?_eq_some_iff.mp hp).1
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
        exact (hargs.1 i v a ft hg).1.1 r' hrA
  have hr0DepsBnd : ∀ d' ∈ r0.deps, d' < σ₁.st.size := by
    intro d' hd'
    rw [hszSt₁]
    cases hrc : ifc.resCls with
    | irr | imm => rw [hIrrImmR (by rw [hrc]; simp)] at hd'; cases hd'
    | leaf => rw [hLeafR hrc] at hd'; cases hd'
    | val =>
      obtain ⟨hu, hub, hb, hsh⟩ := hValR hrc
      cases hrm : ifc.res with
      | unique => rw [hu hrm] at hd'; cases hd'
      | uniqueBorrowed =>
        obtain ⟨i, p, a, hp, ha, _, hdA⟩ := ((hub hrm).2.1 d').mp hd'
        have hi := (Array.getElem?_eq_some_iff.mp hp).1
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
        exact (hargs.1 i v a ft hg).1.2.1 d' hdA
      | borrowed =>
        obtain ⟨i, p, a, hp, ha, _, hdA⟩ := ((hb hrm).2.1 d').mp hd'
        have hi := (Array.getElem?_eq_some_iff.mp hp).1
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
        exact (hargs.1 i v a ft hg).1.2.1 d' hdA
      | shared =>
        obtain ⟨i, p, a, hp, ha, _, hdA⟩ := ((hsh hrm).2.1 d').mp hd'
        have hi := (Array.getElem?_eq_some_iff.mp hp).1
        obtain ⟨v, ft, hg, _⟩ := ArgsMatch_getElem_avs hmatch (by rw [← havs0Get i hi]; exact ha)
        exact (hargs.1 i v a ft hg).1.2.1 d' hdA
  -- Helper: any `.val` arg `a` with `p.mode ≠ .erased ∧ (ifc.res.isBorrowed ∨ p.mode.isBorrowed = false)`
  -- has `σ₁.st[x]? ≠ some .live` whenever `x ∈ a.deps` and `x ∉ r0.deps` (when `ifc.resCls = .val`)!
  have hArgDepNotLive : ∀ (i : Nat) (p : Param) (a : AVal), ifc.resCls = .val →
      ifc.params[i]? = some p → avs0[i]? = some (some a) →
      p.mode ≠ .erased → (ifc.res.isBorrowed = true ∨ p.mode.isBorrowed = false) → a.cls = .val →
      ∀ x ∈ a.deps, x ∉ r0.deps → σ₁.st[x]? ≠ some .live := by
    intro i p a hrcV hp ha hne hbor hcv x hx hnotIn hlive
    have hvd := (hperArg i p a hp ha).1
    have hlt := (hvd x hx).1
    have h1 := hstPt x hlt
    rw [hlive] at h1
    have hcf : (ifc.resCls != .val) = false := by rw [hrcV]; rfl
    obtain ⟨_, hub, hb, hsh⟩ := hValR hrcV
    have hnotKill : ¬ (∃ (i' : Nat) (p' : Param) (a' : AVal),
        ifc.params[i']? = some p' ∧ (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
        callKills (ifc.resCls != .val) p' a' x) := by
      intro hK
      split at h1
      · cases h1
      · rename_i hn; exact False.elim (hn hK)
    have hnotShare : ¬ ((∃ (i' : Nat) (p' : Param) (a' : AVal),
        ifc.params[i']? = some p' ∧ (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
        callShares (ifc.resCls != .val) p' a' x) ∧
        σ.st[x]? = some .live) := by
      intro hS
      split at h1
      · rename_i hk; exact False.elim (hnotKill hk)
      · cases h1
    have hst0Live : σ.st[x]? = some .live := by
      split at h1
      · rename_i hk; exact False.elim (hnotKill hk)
      · exact h1.symm
    cases hrm : ifc.res with
    | uniqueBorrowed => exact hnotIn (((hub hrm).2.1 x).mpr ⟨i, p, a, hp, ha, hcv, hx⟩)
    | borrowed => exact hnotIn (((hb hrm).2.1 x).mpr ⟨i, p, a, hp, ha, hcv, hx⟩)
    | shared =>
      rw [hrm] at hbor; simp only [ResultMode.isBorrowed, Bool.false_eq_true, false_or] at hbor
      cases hpm : p.mode with
      | erased => exact absurd hpm hne
      | borrowed | uniqueBorrowed | onceBorrowed => rw [hpm] at hbor; simp [BinderMode.isBorrowed] at hbor
      | many =>
        have hds : destOf p false = .share := by simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage, BinderMode.isBorrowed]
        exact hnotIn (((hsh hrm).2.1 x).mpr ⟨i, p, a, hp, ha, hds, hx⟩)
      | unique =>
        have hdu : destOf p (ifc.resCls != .val) = .uniq false := by
          simp [destOf, hpm, BinderMode.isUnique, BinderMode.isBorrowed]
        exact hnotKill ⟨i, p, a, hp, ha, Or.inl ⟨false, hdu, hcv, hx⟩⟩
      | once =>
        have hdo : destOf p (ifc.resCls != .val) = .once := by
          simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage]
        exact hnotShare ⟨⟨i, p, a, hp, ha, Or.inr hdo, hcv, hx⟩, hst0Live⟩
    | unique =>
      rw [hrm] at hbor; simp only [ResultMode.isBorrowed, Bool.false_eq_true, false_or] at hbor
      cases hpm : p.mode with
      | erased => exact absurd hpm hne
      | borrowed | uniqueBorrowed | onceBorrowed => rw [hpm] at hbor; simp [BinderMode.isBorrowed] at hbor
      | many =>
        have hds : destOf p (ifc.resCls != .val) = .share := by
          simp [destOf, hpm, hcf, BinderMode.isUnique, BinderMode.usage, BinderMode.isBorrowed]
        exact hnotShare ⟨⟨i, p, a, hp, ha, Or.inl hds, hcv, hx⟩, hst0Live⟩
      | unique =>
        have hdu : destOf p (ifc.resCls != .val) = .uniq false := by
          simp [destOf, hpm, BinderMode.isUnique, BinderMode.isBorrowed]
        exact hnotKill ⟨i, p, a, hp, ha, Or.inl ⟨false, hdu, hcv, hx⟩⟩
      | once =>
        have hdo : destOf p (ifc.resCls != .val) = .once := by
          simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage]
        exact hnotShare ⟨⟨i, p, a, hp, ha, Or.inr hdo, hcv, hx⟩, hst0Live⟩
  -- Build `VSim`, `ValEnvDisj`, `NoReachForbid`
  have hVSimR0 : VSim P ext B₁ st₁ Frame NoKill NoSpend σ₁ I (fun _ => False) r0 f := by
    refine ⟨hr0RegsBnd, hr0DepsBnd,
      (fun _ hs => by rw [hsrcR] at hs; cases hs),
      (fun _ ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs), fun _ => ?_⟩
    exact ⟨hbvF, hOpenR0, hcfF, fun _ hne => hclsF.to_nonValSafe (hclsR ▸ hne) hbvF.1.self.1,
      fun _ => ⟨hnoF, fun _ h => h, hskelR ▸ hfunF⟩,
      (fun hoo => by rw [hooR] at hoo; cases hoo),
      (fun ⟨_, hs, _⟩ => by rw [hsrcR] at hs; cases hs),
      fun htr => let ⟨ht, ho⟩ := huniqF (hr0Uniq htr.1 htr.2.1); ⟨ht, fun l hor => ⟨fun hF => (ho l hor).1 (Or.inl hF), (ho l hor).2⟩⟩⟩
  have hDisjR0 : ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot (fun _ => False) r0 f := by
    intro j b ab hsc hbj habj hneB
    have hvB := ((hsim.2.2.2.2.2.1 j b ab hsc hbj habj).2 hneB).2
    have hsrcB : ∀ x, (effVal ab).src = some x → x < σ.st.size := fun x hx => (hvB.2.2.1 x hx).1
    refine ⟨?_, ?_, (fun _ _ _ _ _ h => False.elim h), ?_,
      (fun _ _ _ _ h => False.elim h),
      (fun hs => by rw [hsrcR] at hs; cases hs),
      (fun _ hs => by rw [hsrcR] at hs; cases hs)⟩
    · intro _ htr haB₁ _ l horF hrB₁
      have hpB := hpresEnv j b ab hsc hbj habj hneB haB₁
      exact (huniqF (hr0Uniq htr.1 htr.2.1)).2 l horF |>.1
        (Or.inr (Or.inr (Or.inr ⟨j, b, ab, hsc, hbj, habj, hneB, haB₁, (Reach_congr hpB l).mp hrB₁⟩)))
    · intro haB₁ htrB₁ _ hdd l horB₁ hrF₁
      have hpB := hpresEnv j b ab hsc hbj habj hneB haB₁
      have haB₀ := ActiveVal.of_AStateLe hok hle₁ hvB.2.1 hsrcB haB₁
      have htrB₀ := Transferable.of_AStateLe hok hle₁ hvB.2.1 hsrcB (fun _ h => h) htrB₁
      have horB₀ := (OwnReach_congr hpB l).mp horB₁
      have hltL := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size (OwnReach_toReach horB₀)
      by_cases hrcV : ifc.resCls = .val
      · rcases hreachF l hrF₁ with hge | ⟨i, p, v, hp, hv0, hneP, hbor, hrv⟩ | hss | hnum
        · omega
        · obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hneP
          by_cases hcv : av.cls = .val
          · have hdd' : ∀ x, x ∈ (effVal ab).deps → ¬ (x ∈ av.deps) := fun x hx hxa => by
              by_cases hIn : x ∈ r0.deps
              · exact hdd x hx hIn
              · exact hArgDepNotLive i p av hrcV hp ha hneP hbor hcv x hxa hIn (htrB₁.2.2.2.2 x hx).1
            exact ((hargs.1 i v av ft hg).2.1 j b ab hsc hbj habj hneB).2.1
              haB₀ htrB₀ (hArgAct i p av hp ha) hdd' l horB₀ hrv
          · exact OwnReach_not_numLoc horB₀ (((hargs.1 i v av ft hg).2.2.2 (hperArg i p av hp ha).1 hcv).2.reach_numLoc hrv)
        · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.2.2 htrB₀).2 l horB₀ |>.2 hss
        · exact OwnReach_not_numLoc horB₁ hnum
      · exact OwnReach_not_numLoc horB₁ ((hclsF.to_nonValSafe hrcV hbvF.1.self.1).reach_numLoc hrF₁)
    · intro haB₁ hftB₁ _ _ l hfl hrF₁
      have hpB := hpresEnv j b ab hsc hbj habj hneB haB₁
      have haB₀ := ActiveVal.of_AStateLe hok hle₁ hvB.2.1 hsrcB haB₁
      have hftB₀ := FootActive.of_AStateLe hok hle₁ hvB.2.1 hsrcB hftB₁
      have ⟨hrB₀, hnotSS0, hnotNum0⟩ : Reach st.heap b.val l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
        rcases hftB₀ with hooB | ⟨hisB, _⟩
        · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.1 hooB).1 l hfl
        · exact ((hvB.2.2.2.2 haB₀).2.2.2.2.2.2.1 hisB).1 l hfl
      have hltL := (hvB.2.2.2.2 haB₀).1.1.reach_lt_size hrB₀
      have hnotNum₁ : ¬ NumLoc st₁.heap l := fun hn => hnotNum0 ((NumLoc_congr hpB hrB₀).mpr hn)
      rcases hreachF l hrF₁ with hge | ⟨i, p, v, hp, hv0, hneP, _, hrv⟩ | hss | hnum
      · omega
      · obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hneP
        have hneSrc : av.src ≠ some ab.id := by
          intro hsrc
          have habMem : ab.id ∈ (effVal ab).deps := by simp [effVal]
          have hvA := (hargs.1 i v av ft hg).1
          rcases hftB₁ with hooB | ⟨hisB₁, hunspB₁⟩
          · have hooA : av.onceOnly = true :=
              ((hargs.1 i v av ft hg).2.1 j b ab hsc hbj habj hneB).2.2.2.2.2.1 hsrc hooB
            by_cases hdo : destOf p (ifc.resCls != .val) = .once
            · have h1 := hstPt ab.id (hvA.2.2.1 ab.id hsrc).1
              have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
                  (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
                  callKills (ifc.resCls != .val) p' a' ab.id :=
                ⟨i, p, av, hp, ha, Or.inr ⟨hdo, hooA, hsrc⟩⟩
              split at h1
              · exact (haB₁.1 ab.id habMem).2 h1
              · rename_i hn; exact False.elim (hn hex)
            · rw [((hperArg i p av hp ha).2.2.1 hdo).2.1] at hooA; cases hooA
          · obtain ⟨id, hs1, ho1⟩ := hisB₁; dsimp [effVal] at hs1; cases hs1
            have ho0 : σ.once[ab.id]? = some true := by rw [← honceEq₁]; exact ho1
            have hltSp : ab.id < σ.spent.size := by have h1 := (hvA.2.2.1 ab.id hsrc).1; have h2 := hok.2.1; omega
            have h1 := hspPt ab.id hltSp
            have hex : (∃ (i' : Nat) (p' : Param) (a' : AVal),
                ifc.params[i']? = some p' ∧ (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
                ab.id ∈ a'.deps) ∧
                σ.once[ab.id]? = some true := ⟨⟨i, p, av, hp, ha, (hvA.2.2.1 ab.id hsrc).2⟩, ho0⟩
            split at h1
            · have hspF := hunspB₁ ab.id habMem ho1
              rw [h1] at hspF; cases hspF
            · rename_i hn; exact False.elim (hn hex)
        exact ((hargs.1 i v av ft hg).2.1 j b ab hsc hbj habj hneB).2.2.2.1
          haB₀ hftB₀ (hArgAct i p av hp ha) hneSrc l hfl hrv
      · exact hnotSS0 hss
      · exact hnotNum₁ hnum
  have hNrfR0 : ActiveVal σ₁ r0 → NoReachForbid st₁ Forbid BadReg BadDep r0 f := by
    intro _ hregsR hdepsR l hrF₁ hnotSS' hnotNum' hForb
    have hltF := hForbidLt l hForb
    by_cases hrcV : ifc.resCls = .val
    · have hnotSS0 : ¬ StaticStrLoc st l := fun hss => hnotSS' (StaticStrLoc_mono hstat₁ hstr₁ hpresSS hss)
      have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hc⟩ => hnotNum' ⟨o, n, hpresNum l o n ho hc, hc⟩
      rcases hreachF l hrF₁ with hge | ⟨i, p, v, hp, hv0, hneP, hbor, hrv⟩ | hss | hnum
      · omega
      · obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hneP
        by_cases hcv : av.cls = .val
        · have hdepsA : ∀ x ∈ av.deps, ¬ BadDep x := fun x hx hbd => by
            by_cases hIn : x ∈ r0.deps
            · exact hdepsR x hIn hbd
            · exact hArgDepNotLive i p av hrcV hp ha hneP hbor hcv x hx hIn (hBadDepLive x hbd)
          have hregsA : ∀ r' ∈ av.regs, ¬ BadReg r' := by
            intro r' hr'
            obtain ⟨_, hub, hb, hsh⟩ := hValR hrcV
            cases hrm : ifc.res with
            | uniqueBorrowed => exact hregsR r' (((hub hrm).2.2 r').mpr (Or.inr ⟨i, p, av, hp, ha, hr'⟩))
            | borrowed => exact hregsR r' (((hb hrm).2.2 r').mpr (Or.inr ⟨i, p, av, hp, ha, hr'⟩))
            | shared => exact hregsR r' (((hsh hrm).2.2 r').mpr ⟨i, p, av, hp, ha, hr'⟩)
            | unique =>
              by_cases hleaf : p.cls = .leaf
              · exact False.elim (hnotNum0 (hLeafNum i p v hp hv0 hneP hleaf l hrv))
              · rw [hrm] at hbor; simp only [ResultMode.isBorrowed, Bool.false_eq_true, false_or] at hbor
                have hcf : (ifc.resCls != .val) = false := by rw [hrcV]; rfl
                have hregsNil : av.regs = [] := by
                  cases hpm : p.mode with
                  | erased => exact absurd hpm hneP
                  | borrowed | uniqueBorrowed | onceBorrowed => rw [hpm] at hbor; simp [BinderMode.isBorrowed] at hbor
                  | unique =>
                    have hdu : destOf p (ifc.resCls != .val) = .uniq false := by
                      simp [destOf, hpm, BinderMode.isUnique, BinderMode.isBorrowed]
                    exact ((hperArg i p av hp ha).2.2.2.1 false hdu hcv).2.2 rfl
                  | many =>
                    have hds : destOf p (ifc.resCls != .val) = .share := by
                      simp [destOf, hpm, hcf, BinderMode.isUnique, BinderMode.usage, BinderMode.isBorrowed]
                    exact (hperArg i p av hp ha).2.2.2.2 hrm hrcV (by rw [hcv]; decide) hleaf (Or.inl hds)
                  | once =>
                    have hdo : destOf p (ifc.resCls != .val) = .once := by
                      simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage]
                    exact (hperArg i p av hp ha).2.2.2.2 hrm hrcV (by rw [hcv]; decide) hleaf (Or.inr hdo)
                rw [hregsNil] at hr'; cases hr'
          exact (hargs.1 i v av ft hg).2.2.1 (hArgAct i p av hp ha) hregsA hdepsA l hrv hnotSS0 hnotNum0 hForb
        · exact hnotNum0 (((hargs.1 i v av ft hg).2.2.2 (hperArg i p av hp ha).1 hcv).2.reach_numLoc hrv)
      · exact hnotSS0 hss
      · exact hnotNum' hnum
    · exact hnotNum' ((hclsF.to_nonValSafe hrcV hbvF.1.self.1).reach_numLoc hrF₁)
  exact ⟨hpresF, hpresEx, hpresEnv, hpresNum, hsim₁, hEnvNrf₁, hVSimR0, hDisjR0, hNrfR0,
    fun _ hne => ⟨hbvF, hclsF.to_nonValSafe (hclsR ▸ hne) hbvF.1.self.1⟩,
    fun htr l hor hEx => (huniqF (hr0Uniq htr.1 htr.2.1)).2 l hor |>.1 (Or.inr (Or.inl hEx))⟩

/-- Bridge for `ACall.ifaceFullPos` (`0 < ifc.params.size ≤ vs.length`): simulates
`callWithS P ext fuel r vs c` for `.body` (`enterS`), `.extern` (`callExtern`), and `.stuck`,
followed by `applyAllS_bridge` on any extra arguments `vs.drop ifc.params.size`. -/
theorem callResult_pos_bridge {P : Prog} {ext : ExternOracle} {B B_call fuel : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ₁ σ₂ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {r : Ref} {d : RunDef} {ifc : Iface} {w : String} {c : Cls}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {r0 res : AVal}
    (hext : ExternOk P ext) (hih : FullIH P ext B) (hB : B_call ≤ B + 1)
    (hfind : P.find? r = some d) (hifc : ifaceOf? d = some ifc)
    (hpos : 0 < ifc.params.size) (hleLen : ifc.params.size ≤ vs.length)
    (hmatch : ArgsMatch args vs avs)
    (hErased : ∀ i, i < avs.length → (avs[i]? = some none ↔ erasedAt d i = true))
    (hrun : Runs (callResult ifc (avs.toArray.extract 0 ifc.params.size) w) σ r0 σ₁)
    (happs : AApps r0 ((avs.drop ifc.params.size).filterMap id) c σ₁ res σ₂)
    (hsim : Sim P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hst : StOk P ext B_call st)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hnk₂ : NoKillOk NoKill σ₂) (hnsp₂ : NoSpendOk NoSpend σ₂)
    (hargs : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep args)
    (hargsSrc : ArgsSrcOk args)
    (hEnvNrf : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hForbidLt : ∀ l, Forbid l → l < st.heap.objs.size)
    (hBadDepLive : ∀ x, BadDep x → σ₂.st[x]? = some .live) :
    (∀ k, (callWithS P ext fuel r vs c).run (st, B_call) ≠ .error (.violation k)) ∧
    ∀ rv st' B', (callWithS P ext fuel r vs c).run (st, B_call) = .ok (rv, (st', B')) →
      ∃ resFoot : Nat → Prop,
        B' ≤ B_call ∧
        StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧
        st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧
        ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesActiveEnv Scope env aenv σ₂ st.heap st'.heap ∧
        (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ₂ I envFoot ∧
        EnvNoReachForbid st' Scope env aenv σ₂ Forbid BadReg BadDep ∧
        VSim P ext B' st' Frame NoKill NoSpend σ₂ I resFoot res rv ∧
        ValEnvDisj P st' NoKill Scope env aenv σ₂ envFoot resFoot res rv ∧
        (ActiveVal σ₂ res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
        (ValidDeps σ₂ res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
        ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B' st' rv) ∨ (IsOnceSrc σ₂ res ∧ SpentOnceSafe st'.heap rv)) ∧
        SrcOk Scope aenv σ σ₂ res := by
  have hok := hsim.2.1
  let k := ifc.params.size
  let avs0 := avs.toArray.extract 0 k
  obtain ⟨hok₁, hle₁, hszSt₁, honceEq₁, hszSp₁, _, _, hclsR, _, _, hsrcR,
    hperArg, _, _, _, hValR, hspPt, hstPt⟩ := Runs_callResult hok hrun
  have hle₁₂ : AStateLe σ₁ σ₂ := by
    have hgo : ∀ {f0 : AVal} {xs : List AVal} {c0 : Cls} {s0 s1 : AState} {r' : AVal},
        AStateOk s0 → AApps f0 xs c0 s0 r' s1 → AStateLe s0 s1 := by
      intro f0 xs c0 s0 s1 r' hokS ha
      induction ha with
      | nil => exact AStateLe.refl _
      | consLast hr' => exact (Runs_applyValue hokS hr').2.1
      | consMore hr' _ ihA =>
        have hu := Runs_applyValue hokS hr'
        exact hu.2.1.trans (ihA hu.1)
    exact hgo hok₁ happs
  have hnk₁ : NoKillOk NoKill σ₁ := fun d hd hdead => by
    have hlt := (Array.getElem?_eq_some_iff.mp hdead).1
    have h1 := hle₁₂.2.2.1 d hlt; rw [hdead] at h1
    cases h2 : σ₂.st[d]? with
    | none => rw [h2] at h1; exact h1
    | some b2 => rw [h2] at h1; cases b2 with | dead => exact hnk₂ d hd h2 | live | shared => exact h1
  have hnsp₁ : NoSpendOk NoSpend σ₁ := fun d hd hsp =>
    hnsp₂ d hd (hle₁₂.2.2.2.2 d (Array.getElem?_eq_some_iff.mp hsp).1 hsp)
  have hBadDepLive₁ : ∀ x, BadDep x → σ₁.st[x]? = some .live := fun x hbd => by
    have hlv₂ := hBadDepLive x hbd
    have hlt₂ := (Array.getElem?_eq_some_iff.mp hlv₂).1
    by_cases hlt₁ : x < σ₁.st.size
    · have h1 := hle₁₂.2.2.1 x hlt₁; rw [hlv₂] at h1
      cases hx : σ₁.st[x]? with
      | none => rw [hx] at h1; exact False.elim h1
      | some b1 => rw [hx] at h1; cases b1 with | live => rfl | shared | dead => exact False.elim h1
    · -- `BadDep` at `x ≥ σ₁.st.size` cannot occur for `x < σ.st.size`; if `x ≥ σ₁.st.size`, wait:
      -- in `callResult_pos_post`, `hBadDepLive` is only queried on `x ∈ av.deps` which has `x < σ.st.size = σ₁.st.size`!
      -- Actually `σ₁.st.size = σ₂.st.size` because `AApps` never changes `st.size`!
      have hsz₁₂ : σ₂.st.size = σ₁.st.size := by
        have hgo : ∀ {f0 : AVal} {xs : List AVal} {c0 : Cls} {s0 s1 : AState} {r' : AVal},
            AStateOk s0 → AApps f0 xs c0 s0 r' s1 → s1.st.size = s0.st.size := by
          intro f0 xs c0 s0 s1 r' hokS ha
          induction ha with
          | nil => rfl
          | consLast hr' => exact (Runs_applyValue hokS hr').2.2.1
          | consMore hr' _ ihA =>
            have hu := Runs_applyValue hokS hr'
            exact (ihA hu.1).trans hu.2.2.1
        exact hgo hok₁ happs
      omega
  have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
  have havs0Get : ∀ (i : Nat), i < k → avs0[i]? = avs[i]? := by
    intro i hi; simp [avs0, hi]
  -- Extra args (`args.drop k`) have zero `none` entries since `erasedAt d (k + j) = false`
  have hExtraNonNone : ∀ j, j < (args.drop k).length → (args.drop k)[j]? ≠ some none := by
    intro j hj hEq
    rw [List.getElem?_drop] at hEq
    have h1 := hmatch.2.2 (k + j); rw [hEq] at h1
    have hjA : k + j < avs.length := by rw [List.length_drop] at hj; rw [← hmatch.2.1]; omega
    have her := (hErased (k + j) hjA).mp h1.2
    rw [erasedAt_of_ifaceOf hifc (k + j), Array.getElem?_eq_none (by omega)] at her
    cases her
  let extraF : List (Val × AVal × (Nat → Prop)) := (args.drop k).filterMap id
  have hExtraMapSome : extraF.map some = args.drop k := by
    have hgo : ∀ (xs : List (Option (Val × AVal × (Nat → Prop)))),
        (∀ i, i < xs.length → xs[i]? ≠ some none) → (xs.filterMap id).map some = xs := by
      intro xs; induction xs with
      | nil => intro _; rfl
      | cons x rest ih =>
        intro hne; cases x with
        | none => exact False.elim (hne 0 (by simp) rfl)
        | some p => simp only [List.filterMap_cons, id_eq, List.map_cons]; exact congrArg (some p :: ·) (ih fun i hi => hne (i + 1) (by simpa using hi))
    exact hgo (args.drop k) hExtraNonNone
  have hExtraGet : ∀ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
      extraF[j]? = some (vj, avj, ftj) → args[k + j]? = some (some (vj, avj, ftj)) := by
    intro j vj avj ftj hgj
    have h1 : (args.drop k)[j]? = some (some (vj, avj, ftj)) := by rw [← hExtraMapSome, List.getElem?_map, hgj]; rfl
    rwa [List.getElem?_drop] at h1
  have hExtraMapVal : extraF.map (·.1) = vs.drop k := by
    apply List.ext_getElem?; intro j
    have hi := hmatch.2.2 (k + j)
    have h1 : args[k + j]? = (extraF.map some)[j]? := by rw [hExtraMapSome, List.getElem?_drop]
    rw [h1, List.getElem?_map] at hi; rw [List.getElem?_map, List.getElem?_drop]
    cases hfg : extraF[j]? with
    | none => simp only [hfg, Option.map_none] at hi ⊢; exact hi.1.symm
    | some p => simp only [hfg, Option.map_some] at hi ⊢; exact hi.1.symm
  have hExtraMapAv : extraF.map (·.2.1) = (avs.drop k).filterMap id := by
    have hEqAvs : avs.drop k = extraF.map (fun p => some p.2.1) := by
      apply List.ext_getElem?; intro j
      have hi := hmatch.2.2 (k + j)
      have h1 : args[k + j]? = (extraF.map some)[j]? := by rw [hExtraMapSome, List.getElem?_drop]
      rw [h1, List.getElem?_map] at hi; rw [List.getElem?_map, List.getElem?_drop]
      cases hfg : extraF[j]? with
      | none => simp only [hfg, Option.map_none] at hi ⊢; exact hi.2
      | some p => simp only [hfg, Option.map_some] at hi ⊢; exact hi.2
    rw [hEqAvs]
    have hfm : ∀ (xs : List (Val × AVal × (Nat → Prop))),
        (xs.map fun p => some p.2.1).filterMap id = xs.map (·.2.1) := by
      intro xs; induction xs with | nil => rfl | cons p r ih => simp [ih]
    exact (hfm extraF).symm
  -- Define `FrameExtra` covering active extra arguments at `σ₁`
  let FrameExtra : Nat → Prop := fun l =>
    ∃ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
      extraF[j]? = some (vj, avj, ftj) ∧ ActiveVal σ₁ avj ∧ Reach st.heap vj l
  have hExLt : ∀ l, FrameExtra l → l < st.heap.objs.size := by
    rintro l ⟨j, vj, avj, ftj, hgj, ha₁, hrj⟩
    have hvj := (hargs.1 (k + j) vj avj ftj (hExtraGet j vj avj ftj hgj)).1
    have ha₀ := ActiveVal.of_AStateLe hok hle₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) ha₁
    exact (hvj.2.2.2.2 ha₀).1.1.reach_lt_size hrj
  have hExU : ∀ (i : Nat) (p : Param) (v : Val) (a : AVal) (ft : Nat → Prop),
      ifc.params[i]? = some p → args[i]? = some (some (v, a, ft)) →
      p.mode.isUnique = true → a.cls = .val → ∀ l, OwnReach P st.heap v l → ¬ FrameExtra l := by
    rintro i p v a ft hp hg hu hcv l hor ⟨j, vj, avj, ftj, hgj, haJ₁, hrj⟩
    have hi : i < k := (Array.getElem?_eq_some_iff.mp hp).1
    have ha : avs0[i]? = some (some a) := by rw [havs0Get i hi]; have h1 := hmatch.2.2 i; rw [hg] at h1; exact h1.2
    obtain ⟨b, hdu⟩ := (destOf_isUniq_iff p (ifc.resCls != .val)).mpr hu
    have hneO : destOf p (ifc.resCls != .val) ≠ .once := by rw [hdu]; intro h; cases h
    obtain ⟨hvd, _, hnonOnce, huniq, _⟩ := hperArg i p a hp ha
    obtain ⟨_, hoo, hnotOS⟩ := hnonOnce hneO
    obtain ⟨hown, hlv, _⟩ := huniq b hdu hcv
    have hkill : ∀ x ∈ a.deps, σ₁.st[x]? = some .dead := fun x hx => by
      have h1 := hstPt x (hvd x hx).1
      have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
          (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
          callKills (ifc.resCls != .val) p' a' x := ⟨i, p, a, hp, ha, Or.inl ⟨b, hdu, hcv, hx⟩⟩
      split at h1
      · exact h1
      · rename_i hn; exact False.elim (hn hex)
    have htrA : Transferable σ NoKill a :=
      ⟨hcv, hown, hoo, hnotOS, fun x hx => ⟨hlv x hx, fun hnk => hnk₁ x hnk (hkill x hx)⟩⟩
    have hvj := (hargs.1 (k + j) vj avj ftj (hExtraGet j vj avj ftj hgj)).1
    have haJ₀ := ActiveVal.of_AStateLe hok hle₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) haJ₁
    have hdd : ∀ x, x ∈ a.deps → ¬ (x ∈ avj.deps) := fun x hx hxj => (haJ₁.1 x hxj).2 (hkill x hx)
    exact (hargs.2 i (k + j) v vj a avj ft ftj (by omega) hg (hExtraGet j vj avj ftj hgj)).1
      ⟨hvd, fun h => False.elim (hnotOS h)⟩ htrA haJ₀ hdd l hor hrj
  have hExO : ∀ (i : Nat) (p : Param) (v : Val) (a : AVal) (ft : Nat → Prop),
      ifc.params[i]? = some p → args[i]? = some (some (v, a, ft)) →
      p.mode.usage = .once → (a.onceOnly = true ∨ IsOnceSrc σ a) → ∀ l, ft l → ¬ FrameExtra l := by
    rintro i p v a ft hp hg hoU hdisj l hfl ⟨j, vj, avj, ftj, hgj, haJ₁, hrj⟩
    have hi : i < k := (Array.getElem?_eq_some_iff.mp hp).1
    have ha : avs0[i]? = some (some a) := by rw [havs0Get i hi]; have h1 := hmatch.2.2 i; rw [hg] at h1; exact h1.2
    have hdo : destOf p (ifc.resCls != .val) = .once := (destOf_once_iff p _).mpr hoU
    obtain ⟨hvd, honce, _, _, _⟩ := hperArg i p a hp ha
    have hvA := (hargs.1 i v a ft hg).1
    have hvj := (hargs.1 (k + j) vj avj ftj (hExtraGet j vj avj ftj hgj)).1
    have haJ₀ := ActiveVal.of_AStateLe hok hle₁ hvj.2.1 (fun x hx => (hvj.2.2.1 x hx).1) haJ₁
    have hftAct : FootActive σ a := by
      rcases hdisj with hoo | his
      · exact Or.inl hoo
      · exact Or.inr ⟨his, (honce hdo).2⟩
    have hneSrc : a.src = none ∨ a.src ≠ avj.src := by
      cases hsa : a.src with
      | none => exact Or.inl rfl
      | some x =>
        right; intro hEq
        have hxJ : x ∈ avj.deps := (hvj.2.2.1 x hEq.symm).2
        rcases hdisj with hoo | ⟨id, hs1, ho1⟩
        · have h1 := hstPt x (hvA.2.2.1 x hsa).1
          have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
              (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
              callKills (ifc.resCls != .val) p' a' x := ⟨i, p, a, hp, ha, Or.inr ⟨hdo, hoo, hsa⟩⟩
          split at h1
          · exact (haJ₁.1 x hxJ).2 h1
          · rename_i hn; exact False.elim (hn hex)
        · rw [hsa] at hs1; cases hs1
          have hltSp : x < σ.spent.size := by have h1 := (hvA.2.2.1 x hsa).1; have h2 := hok.2.1; omega
          have h1 := hspPt x hltSp
          have hex : (∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
              (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
              x ∈ a'.deps) ∧ σ.once[x]? = some true := ⟨⟨i, p, a, hp, ha, (hvA.2.2.1 x hsa).2⟩, ho1⟩
          split at h1
          · have ho₁' : σ₁.once[x]? = some true := by rw [honceEq₁]; exact ho1
            have hspF := haJ₁.2 ⟨x, hEq.symm, ho₁'⟩ x hxJ ho₁'
            rw [h1] at hspF; cases hspF
          · rename_i hn; exact False.elim (hn hex)
    exact (hargs.2 i (k + j) v vj a avj ft ftj (by omega) hg (hExtraGet j vj avj ftj hgj)).2
      ⟨hvd, fun _ => (honce hdo).2⟩ hftAct haJ₀ hneSrc l hfl hrj
  -- Shared continuation from `(f, st₁, B₁)` + `callResult_pos_post` to `applyAllS_bridge`!
  have hContPos : ∀ (n' b B₁ : Nat) (f : Val) (st₁ : St),
      B₁ ≤ b → b + 1 = B_call →
      StOk P ext B₁ st₁ →
      st.heap.objs.size ≤ st₁.heap.objs.size →
      st.heap.nextCap ≤ st₁.heap.nextCap →
      st₁.regions = st.regions →
      st.nextRegion ≤ st₁.nextRegion →
      ArrayExtends st.statics st₁.statics →
      ArrayExtends st.strs st₁.strs →
      PreservesLocs Frame st.heap st₁.heap →
      PreservesLocs FrameExtra st.heap st₁.heap →
      PreservesActiveEnv Scope env aenv σ₁ st.heap st₁.heap →
      (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st₁.heap.objs[l]? = some o) →
      PreservesOnceShell st.heap st₁.heap →
      StaticStrFresh st st₁ →
      Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot →
      EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep →
      ValBaseOk st₁ f →
      ClsSafe st₁.heap ifc.resCls f →
      CtorFieldsOk P ext B₁ st₁ f →
      VSim P ext B₁ st₁ Frame NoKill NoSpend σ₁ I (fun _ => False) r0 f →
      ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot (fun _ => False) r0 f →
      (ActiveVal σ₁ r0 → NoReachForbid st₁ Forbid BadReg BadDep r0 f) →
      (ValidDeps σ₁ r0.deps → r0.cls ≠ .val → ValBaseOk st₁ f ∧ NonValSafe st₁.heap f) →
      (∀ l, Reach st₁.heap f l →
        st.heap.objs.size ≤ l ∨
        (∃ (i : Nat) (p : Param) (v : Val),
          ifc.params[i]? = some p ∧ (vs.take k)[i]? = some v ∧ p.mode ≠ .erased ∧
          (ifc.res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧ Reach st.heap v l) ∨
        StaticStrLoc st l ∨ NumLoc st₁.heap l) →
      (Transferable σ₁ NoKill r0 → ∀ l, OwnReach P st₁.heap f l → ¬ FrameExtra l) →
      (∀ k', (applyAllS P ext n' f (vs.drop k) c).run (st₁, B₁) ≠ .error (.violation k')) ∧
      ∀ rv st' B', (applyAllS P ext n' f (vs.drop k) c).run (st₁, B₁) = .ok (rv, (st', B')) →
        ∃ resFoot : Nat → Prop,
          B' ≤ B_call ∧ StOk P ext B' st' ∧
          st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
          st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
          ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
          PreservesLocs Frame st.heap st'.heap ∧ PreservesActiveEnv Scope env aenv σ₂ st.heap st'.heap ∧
          (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
          PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
          Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ₂ I envFoot ∧
          EnvNoReachForbid st' Scope env aenv σ₂ Forbid BadReg BadDep ∧
          VSim P ext B' st' Frame NoKill NoSpend σ₂ I resFoot res rv ∧
          ValEnvDisj P st' NoKill Scope env aenv σ₂ envFoot resFoot res rv ∧
          (ActiveVal σ₂ res → NoReachForbid st' Forbid BadReg BadDep res rv) ∧
          (ValidDeps σ₂ res.deps → res.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
          ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B' st' rv) ∨ (IsOnceSrc σ₂ res ∧ SpentOnceSafe st'.heap rv)) ∧
          SrcOk Scope aenv σ σ₂ res := by
    intro n' b B₁ f st₁ hB₁ hbEq hst₁ hsz₁ hcap₁ hr₁ hnr₁ hstat₁ hstr₁
      hpresF₁ hpresEx₁ hpresEnv₁ hpresNum₁ honce₁ hssf₁ hsim₁ hEnvNrf₁
      hbvF hclsF hcfF hVSimR0 hDisjR0 hNrfR0 hNvR0 hreachF _
    have hpresSS₁ : PreservesLocs (StaticStrLoc st) st.heap st₁.heap := hpresF₁.mono fun _ h => hstat _ h
    have hrf₁ : RegsFuture st st₁ := RegsFuture.same_regions hnr₁ hr₁
    let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
    have hexArgs₀ : ArgListOk P ext B_call st Frame NoKill NoSpend Scope env aenv σ I envFoot
        Forbid BadReg BadDep (extraF.map some) := by
      refine ⟨fun j vj avj ftj hg => ?_, fun j₁ j₂ v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
      · have hg' : extraF[j]? = some (vj, avj, ftj) := by
          rw [List.getElem?_map] at hg; cases h : extraF[j]? with | none => rw [h] at hg; cases hg | some p => rw [h] at hg; simp at hg; subst hg; rfl
        exact hargs.1 (k + j) vj avj ftj (hExtraGet j vj avj ftj hg')
      · have hg₁' : extraF[j₁]? = some (v₁, av₁, ft₁) := by
          rw [List.getElem?_map] at hg₁; cases h : extraF[j₁]? with | none => rw [h] at hg₁; cases hg₁ | some p => rw [h] at hg₁; simp at hg₁; subst hg₁; rfl
        have hg₂' : extraF[j₂]? = some (v₂, av₂, ft₂) := by
          rw [List.getElem?_map] at hg₂; cases h : extraF[j₂]? with | none => rw [h] at hg₂; cases hg₂ | some p => rw [h] at hg₂; simp at hg₂; subst hg₂; rfl
        exact hargs.2 (k + j₁) (k + j₂) v₁ v₂ av₁ av₂ ft₁ ft₂ (by omega)
          (hExtraGet j₁ v₁ av₁ ft₁ hg₁') (hExtraGet j₂ v₂ av₂ ft₂ hg₂')
    have hexArgs₁ : ArgListOk P ext B₁ st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
        Forbid BadReg BadDep (extraF.map some) :=
      ArgListOk_add_staticStr (ArgListOk_step (by omega) hok hle₁ hrf₁ honce₁ hssf₁
        hstat₁ hstr₁ hpresSS₁ (fun _ _ _ h => h) (Sim_deps_lt hsim) hsim.2.2.2.1 hpresEnv₁
        (fun j vj avj ftj hg ha₁ => by
          have hg' : extraF[j]? = some (vj, avj, ftj) := by
            rw [List.getElem?_map] at hg; cases h : extraF[j]? with | none => rw [h] at hg; cases hg | some p => rw [h] at hg; simp at hg; subst hg; rfl
          exact hpresEx₁.mono fun l hr => ⟨j, vj, avj, ftj, hg', ha₁, hr⟩)
        hpresNum₁ hexArgs₀)
    have hParamNE : ∀ (i : Nat) (p : Param) (v : Val), ifc.params[i]? = some p → (vs.take k)[i]? = some v →
        p.mode ≠ .erased → ∃ av ft, args[i]? = some (some (v, av, ft)) ∧ avs0[i]? = some (some av) := by
      intro i p v hp hv0 hne
      have hi : i < k := by have h1 := (List.getElem?_eq_some_iff.mp hv0).1; rw [List.length_take] at h1; omega
      rw [List.getElem?_take_of_lt hi] at hv0
      have hiA : i < avs.length := by rw [hlenEq]; omega
      rcases ArgsMatch_getElem_vs hmatch hv0 with ⟨_, _, ha⟩ | ⟨av, ft, hg, ha⟩
      · have her := (hErased i hiA).mp ha; rw [erasedAt_of_ifaceOf hifc i, hp] at her; exact absurd (eq_of_beq her) hne
      · exact ⟨av, ft, hg, by rw [havs0Get i hi, ha]⟩
    have hArgAct : ∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs0[i]? = some (some a) → ActiveVal σ a := by
      intro i p a hp ha; obtain ⟨hvd, honce, hnonOnce, _, _⟩ := hperArg i p a hp ha
      refine ⟨hvd, fun his => ?_⟩
      by_cases hdo : destOf p (ifc.resCls != .val) = .once
      · exact (honce hdo).2
      · exact False.elim ((hnonOnce hdo).2.2 his)
    have hArgDepNotLive : ∀ (i : Nat) (p : Param) (a : AVal), ifc.resCls = .val →
        ifc.params[i]? = some p → avs0[i]? = some (some a) →
        p.mode ≠ .erased → (ifc.res.isBorrowed = true ∨ p.mode.isBorrowed = false) → a.cls = .val →
        ∀ x ∈ a.deps, x ∉ r0.deps → σ₁.st[x]? ≠ some .live := by
      intro i p a hrcV hp ha hne hbor hcv x hx hnotIn hlive
      have hvd := (hperArg i p a hp ha).1
      have h1 := hstPt x (hvd x hx).1; rw [hlive] at h1
      have hcf : (ifc.resCls != .val) = false := by rw [hrcV]; rfl
      obtain ⟨_, hub, hb, hsh⟩ := hValR hrcV
      have hnotKill : ¬ (∃ (i' : Nat) (p' : Param) (a' : AVal),
          ifc.params[i']? = some p' ∧ (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
          callKills (ifc.resCls != .val) p' a' x) := by
        intro hK
        split at h1
        · cases h1
        · rename_i hn; exact False.elim (hn hK)
      have hnotShare : ¬ ((∃ (i' : Nat) (p' : Param) (a' : AVal),
          ifc.params[i']? = some p' ∧ (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
          callShares (ifc.resCls != .val) p' a' x) ∧
          σ.st[x]? = some .live) := by
        intro hS
        split at h1
        · rename_i hk; exact False.elim (hnotKill hk)
        · cases h1
      have hst0Live : σ.st[x]? = some .live := by
        split at h1
        · rename_i hk; exact False.elim (hnotKill hk)
        · exact h1.symm
      cases hrm : ifc.res with
      | uniqueBorrowed => exact hnotIn (((hub hrm).2.1 x).mpr ⟨i, p, a, hp, ha, hcv, hx⟩)
      | borrowed => exact hnotIn (((hb hrm).2.1 x).mpr ⟨i, p, a, hp, ha, hcv, hx⟩)
      | shared =>
        rw [hrm] at hbor; simp only [ResultMode.isBorrowed, Bool.false_eq_true, false_or] at hbor
        cases hpm : p.mode with
        | erased => exact absurd hpm hne
        | borrowed | uniqueBorrowed | onceBorrowed => rw [hpm] at hbor; simp [BinderMode.isBorrowed] at hbor
        | many =>
          have hds : destOf p false = .share := by simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage, BinderMode.isBorrowed]
          exact hnotIn (((hsh hrm).2.1 x).mpr ⟨i, p, a, hp, ha, hds, hx⟩)
        | unique =>
          have hdu : destOf p (ifc.resCls != .val) = .uniq false := by simp [destOf, hpm, BinderMode.isUnique, BinderMode.isBorrowed]
          exact hnotKill ⟨i, p, a, hp, ha, Or.inl ⟨false, hdu, hcv, hx⟩⟩
        | once =>
          have hdo : destOf p (ifc.resCls != .val) = .once := by simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage]
          exact hnotShare ⟨⟨i, p, a, hp, ha, Or.inr hdo, hcv, hx⟩, hst0Live⟩
      | unique =>
        rw [hrm] at hbor; simp only [ResultMode.isBorrowed, Bool.false_eq_true, false_or] at hbor
        cases hpm : p.mode with
        | erased => exact absurd hpm hne
        | borrowed | uniqueBorrowed | onceBorrowed => rw [hpm] at hbor; simp [BinderMode.isBorrowed] at hbor
        | many =>
          have hds : destOf p (ifc.resCls != .val) = .share := by simp [destOf, hpm, hcf, BinderMode.isUnique, BinderMode.usage, BinderMode.isBorrowed]
          exact hnotShare ⟨⟨i, p, a, hp, ha, Or.inl hds, hcv, hx⟩, hst0Live⟩
        | unique =>
          have hdu : destOf p (ifc.resCls != .val) = .uniq false := by simp [destOf, hpm, BinderMode.isUnique, BinderMode.isBorrowed]
          exact hnotKill ⟨i, p, a, hp, ha, Or.inl ⟨false, hdu, hcv, hx⟩⟩
        | once =>
          have hdo : destOf p (ifc.resCls != .val) = .once := by simp [destOf, hpm, BinderMode.isUnique, BinderMode.usage]
          exact hnotShare ⟨⟨i, p, a, hp, ha, Or.inr hdo, hcv, hx⟩, hst0Live⟩
    have hfaPair : ∀ (j : Nat) (vj : Val) (avj : AVal) (ftj : Nat → Prop),
        extraF[j]? = some (vj, avj, ftj) →
        (ActiveVal σ₁ avj → Transferable σ₁ NoKill avj → ActiveVal σ₁ r0 →
          (∀ x, x ∈ avj.deps → ¬ (x ∈ r0.deps)) → ∀ l, OwnReach P st₁.heap vj l → ¬ Reach st₁.heap f l) ∧
        (ActiveVal σ₁ r0 → FootActive σ₁ r0 → ActiveVal σ₁ avj →
          (r0.src = none ∨ r0.src ≠ avj.src) → ∀ l, False → ¬ Reach st₁.heap vj l) ∧
        (ActiveVal σ₁ avj → FootActive σ₁ avj → ActiveVal σ₁ r0 →
          (avj.src = none ∨ avj.src ≠ r0.src) → ∀ l, ftj l → ¬ Reach st₁.heap f l) ∧
        (∀ x, r0.src = some x → avj.src = some x → r0.onceOnly = avj.onceOnly) := by
      intro j vj avj ftj hgj
      have hga := hExtraGet j vj avj ftj hgj
      have hvj := (hargs.1 (k + j) vj avj ftj hga).1
      have hsrcJ : ∀ x, avj.src = some x → x < σ.st.size := fun x hx => (hvj.2.2.1 x hx).1
      refine ⟨?_, fun _ _ _ _ _ h => False.elim h, ?_, fun _ hs => by rw [hsrcR] at hs; cases hs⟩
      · intro haJ₁ htrJ₁ _ hdd l horJ₁ hrF₁
        have hpJ : PreservesLocs (Reach st.heap vj) st.heap st₁.heap :=
          hpresEx₁.mono fun l' hr' => ⟨j, vj, avj, ftj, hgj, haJ₁, hr'⟩
        have haJ₀ := ActiveVal.of_AStateLe hok hle₁ hvj.2.1 hsrcJ haJ₁
        have htrJ₀ := Transferable.of_AStateLe hok hle₁ hvj.2.1 hsrcJ (fun _ h => h) htrJ₁
        have horJ₀ := (OwnReach_congr hpJ l).mp horJ₁
        have hltL := (hvj.2.2.2.2 haJ₀).1.1.reach_lt_size (OwnReach_toReach horJ₀)
        by_cases hrcV : ifc.resCls = .val
        · rcases hreachF l hrF₁ with hge | ⟨i, p, v, hp, hv0, hneP, hbor, hrv⟩ | hss | hnum
          · omega
          · have hi := (Array.getElem?_eq_some_iff.mp hp).1
            obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hneP
            by_cases hcv : av.cls = .val
            · have hdd' : ∀ x, x ∈ avj.deps → ¬ (x ∈ av.deps) := fun x hx hxa => by
                by_cases hIn : x ∈ r0.deps
                · exact hdd x hx hIn
                · exact hArgDepNotLive i p av hrcV hp ha hneP hbor hcv x hxa hIn (htrJ₁.2.2.2.2 x hx).1
              exact (hargs.2 (k + j) i vj v avj av ftj ft (by omega) hga hg).1
                haJ₀ htrJ₀ (hArgAct i p av hp ha) hdd' l horJ₀ hrv
            · exact OwnReach_not_numLoc horJ₀ (((hargs.1 i v av ft hg).2.2.2 (hperArg i p av hp ha).1 hcv).2.reach_numLoc hrv)
          · exact ((hvj.2.2.2.2 haJ₀).2.2.2.2.2.2.2 htrJ₀).2 l horJ₀ |>.2 hss
          · exact OwnReach_not_numLoc horJ₁ hnum
        · exact OwnReach_not_numLoc horJ₁ ((hclsF.to_nonValSafe hrcV hbvF.1.self.1).reach_numLoc hrF₁)
      · intro haJ₁ hftJ₁ _ _ l hfl hrF₁
        have hpJ : PreservesLocs (Reach st.heap vj) st.heap st₁.heap :=
          hpresEx₁.mono fun l' hr' => ⟨j, vj, avj, ftj, hgj, haJ₁, hr'⟩
        have haJ₀ := ActiveVal.of_AStateLe hok hle₁ hvj.2.1 hsrcJ haJ₁
        have hftJ₀ := FootActive.of_AStateLe hok hle₁ hvj.2.1 hsrcJ hftJ₁
        have ⟨hrJ₀, hnotSS0, hnotNum0⟩ : Reach st.heap vj l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l := by
          rcases hftJ₀ with hooJ | ⟨hisJ, _⟩
          · exact ((hvj.2.2.2.2 haJ₀).2.2.2.2.2.1 hooJ).1 l hfl
          · exact ((hvj.2.2.2.2 haJ₀).2.2.2.2.2.2.1 hisJ).1 l hfl
        have hltL := (hvj.2.2.2.2 haJ₀).1.1.reach_lt_size hrJ₀
        have hnotNum₁ : ¬ NumLoc st₁.heap l := fun hn => hnotNum0 ((NumLoc_congr hpJ hrJ₀).mpr hn)
        rcases hreachF l hrF₁ with hge | ⟨i, p, v, hp, hv0, hneP, _, hrv⟩ | hss | hnum
        · omega
        · have hi := (Array.getElem?_eq_some_iff.mp hp).1
          obtain ⟨av, ft, hg, ha⟩ := hParamNE i p v hp hv0 hneP
          have hvA := (hargs.1 i v av ft hg).1
          have hneSrc : avj.src = none ∨ avj.src ≠ av.src := by
            cases hjs : avj.src with
            | none => exact Or.inl rfl
            | some x =>
              right; intro hEq
              have hxJ : x ∈ avj.deps := (hvj.2.2.1 x hjs).2
              rcases hftJ₁ with hooJ | ⟨⟨id, hs1, ho1⟩, hunspJ₁⟩
              · have hooA : av.onceOnly = true := (hargsSrc (k + j) i vj v avj av ftj ft x hga hg hjs hEq.symm).symm.trans hooJ
                by_cases hdo : destOf p (ifc.resCls != .val) = .once
                · have h1 := hstPt x (hvA.2.2.1 x hEq.symm).1
                  have hex : ∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
                      (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧
                      callKills (ifc.resCls != .val) p' a' x :=
                    ⟨i, p, av, hp, ha, Or.inr ⟨hdo, hooA, hEq.symm⟩⟩
                  split at h1
                  · exact (haJ₁.1 x hxJ).2 h1
                  · rename_i hn; exact False.elim (hn hex)
                · rw [((hperArg i p av hp ha).2.2.1 hdo).2.1] at hooA; cases hooA
              · rw [hjs] at hs1; cases hs1
                have ho0 : σ.once[x]? = some true := by rw [← honceEq₁]; exact ho1
                have hltSp : x < σ.spent.size := by have h1 := (hvA.2.2.1 x hEq.symm).1; have h2 := hok.2.1; omega
                have h1 := hspPt x hltSp
                have hex : (∃ (i' : Nat) (p' : Param) (a' : AVal), ifc.params[i']? = some p' ∧
                    (avs.toArray.extract 0 ifc.params.size)[i']? = some (some a') ∧ x ∈ a'.deps) ∧
                    σ.once[x]? = some true :=
                  ⟨⟨i, p, av, hp, ha, (hvA.2.2.1 x hEq.symm).2⟩, ho0⟩
                split at h1
                · have hspF := hunspJ₁ x hxJ ho1
                  rw [h1] at hspF; cases hspF
                · rename_i hn; exact False.elim (hn hex)
          exact (hargs.2 (k + j) i vj v avj av ftj ft (by omega) hga hg).2
            haJ₀ hftJ₀ (hArgAct i p av hp ha) hneSrc l hfl hrv
        · exact hnotSS0 hss
        · exact hnotNum₁ hnum
    have happs' : AApps r0 (extraF.map (·.2.1)) c σ₁ res σ₂ := by rw [hExtraMapAv]; exact happs
    obtain ⟨hnoVA, hokA⟩ := applyAllS_bridge (B_a := B₁) (fuel := n') (Frame := Frame₁)
      happs' (Sim_add_staticStr hsim₁) hst₁ (fun _ h => Or.inr h)
      (fun l h => h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss))
      hnk₂ hnsp₂ (VSim_add_staticStr hVSimR0) hDisjR0 hNrfR0 hNvR0 (fun _ => Or.inl ⟨hbvF, hcfF⟩)
      hexArgs₁ hfaPair
      (fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂ =>
        hargsSrc (k + i) (k + j) v₁ v₂ av₁ av₂ ft₁ ft₂ x
          (hExtraGet i v₁ av₁ ft₁ hg₁) (hExtraGet j v₂ av₂ ft₂ hg₂) hs₁ hs₂)
      hEnvNrf₁ (fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁)
    rw [hExtraMapVal] at hnoVA hokA
    refine ⟨hnoVA, fun rv st' B' hokRun => ?_⟩
    obtain ⟨resFoot, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
      hpresF₂, hpresEnv₂, hpresNum₂, honce₂, hssf₂,
      hsim₂, hEnvNrf₂, hVSim₂, hDisj₂, hNrf₂, hNv₂, hLive₂⟩ := hokA rv st' B' hokRun
    have hresSrcNone : res.src = none := by
      have hgo : ∀ {f0 : AVal} {xs : List AVal} {c0 : Cls} {s0 s1 : AState} {r' : AVal},
          AStateOk s0 → f0.src = none → AApps f0 xs c0 s0 r' s1 → r'.src = none := by
        intro f0 xs c0 s0 s1 r' hokS hs0 ha
        induction ha with
        | nil => exact hs0
        | consLast hr' =>
          have hru := Runs_applyValue hokS hr'
          rcases arrowParts f0.skel with ⟨_, _, _, _⟩
          exact hru.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        | consMore hr' _ ihA =>
          have hru := Runs_applyValue hokS hr'
          rcases arrowParts f0.skel with ⟨_, _, _, _⟩
          exact ihA hru.1 hru.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact hgo hok₁ hsrcR happs'
    have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st'.heap := by
      intro i b' ab hsc hbi habi hne ha₂
      have hvB := ((hsim.2.2.2.2.2.1 i b' ab hsc hbi habi).2 hne).2
      have ha₁ := ActiveVal.of_AStateLe hok₁ hle₁₂ (hszSt₁ ▸ hvB.2.1)
        (fun x hx => hszSt₁ ▸ (hvB.2.2.1 x hx).1) ha₂
      have hp1 := hpresEnv₁ i b' ab hsc hbi habi hne ha₁
      have hp2 := hpresEnv₂ i b' ab hsc hbi habi hne ha₂
      exact hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
    exact ⟨resFoot, by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
      hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
      hpresF₁.trans (hpresF₂.mono fun _ hF => Or.inl hF),
      hpresEnvAll,
      fun l o n ho hc => hpresNum₂ l o n (hpresNum₁ l o n ho hc) hc,
      honce₁.trans honce₂,
      StaticStrFresh.trans hsz₁ (hpresF₂.mono fun _ hss => Or.inr hss) hssf₁ hssf₂,
      Sim_shrink_frame (fun _ h => Or.inl h) hsim₂,
      hEnvNrf₂,
      VSim_shrink_frame (fun _ h => Or.inl h) hVSim₂,
      hDisj₂, hNrf₂, hNv₂, hLive₂, SrcOk_none hresSrcNone⟩
  -- Unfold `callWithS` and dispatch `.body` / `.extern` / `.stuck`
  cases fuel with
  | zero =>
    cases B_call with
    | zero =>
      have h0 : (callWithS P ext 0 r vs c).run (st, 0) = .error .outOfFuel := by
        unfold callWithS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have h0 : (callWithS P ext 0 r vs c).run (st, b + 1) = .error .outOfFuel := by
        unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n' =>
    cases B_call with
    | zero =>
      have h0 : (callWithS P ext (n' + 1) r vs c).run (st, 0) = .error .outOfFuel := by
        unfold callWithS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b =>
      have hbB : b ≤ B := Nat.le_of_succ_le_succ hB
      obtain ⟨hssC, hFltC, hArgsBody, hRepUExt, hDisjBody⟩ :=
        callResult_pos_args_prep hifc hleLen hmatch hErased hrun hsim hst hstat hFlt hnk₁ hnsp₁
          hargs hargsSrc hExLt hExU hExO
      have hnotLt : ¬ (vs.length < k) := Nat.not_lt.mpr hleLen
      have hneZero : (k == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpos)
      have hlenTake : (vs.take k).length = k := by rw [List.length_take]; exact Nat.min_eq_left hleLen
      have hbpHyps : ∀ (i : Nat) (p : Param) (v : Val), (ifc.params.toList.zip (vs.take k))[i]? = some (p, v) →
          (p.mode ≠ .erased → DeepLive st.heap v ∧ AcyclicFrom st.heap v) ∧
          (p.mode.isUnique = true → OwnTreeFull P st.heap v ∧ (p.mode.isBorrowed = false → OpenUnder st.regions [] v)) := by
        intro i p v hi
        obtain ⟨hltZ, hgetZ⟩ := List.getElem?_eq_some_iff.mp hi
        rw [List.length_zip, Array.length_toList, hlenTake, Nat.min_self] at hltZ
        rw [List.getElem_zip] at hgetZ; cases hgetZ
        have hp : ifc.params[i]? = some ifc.params[i] := Array.getElem?_eq_getElem hltZ
        have hiTake : i < (vs.take k).length := by rw [hlenTake]; exact hltZ
        have hv : (vs.take k)[i]? = some (vs.take k)[i] := List.getElem?_eq_getElem hiTake
        have ha := hArgsBody i ifc.params[i] (vs.take k)[i] hp hv
        refine ⟨fun hne => ⟨(ha hne).1.1, (ha hne).1.2.1⟩, fun hu => ?_⟩
        have hne : ifc.params[i].mode ≠ .erased := by
          cases hm : ifc.params[i].mode <;> simp [hm, BinderMode.isUnique] at hu ⊢
        exact ⟨((ha hne).2.2.2.2.2 hu).1, fun hnb => ((ha hne).2.2.2.2.2 hu).2.2 hnb _ (HeldBy.refl _ _)⟩
      have hbpDisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
          (ifc.params.toList.zip (vs.take k))[i]? = some (pi, vi) →
          (ifc.params.toList.zip (vs.take k))[j]? = some (pj, vj) →
          pi.mode.isUnique = true → pj.mode ≠ .erased →
          ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l := by
        intro i j pi pj vi vj hij hi hj hui hnej l hor hrj
        obtain ⟨hltI, hgetI⟩ := List.getElem?_eq_some_iff.mp hi
        obtain ⟨hltJ, hgetJ⟩ := List.getElem?_eq_some_iff.mp hj
        rw [List.length_zip, Array.length_toList, hlenTake, Nat.min_self] at hltI hltJ
        rw [List.getElem_zip] at hgetI hgetJ; cases hgetI; cases hgetJ
        exact (hDisjBody i j _ _ _ _ hij (Array.getElem?_eq_getElem hltI) (List.getElem?_eq_getElem (by rw [hlenTake]; exact hltI))
          (Array.getElem?_eq_getElem hltJ) (List.getElem?_eq_getElem (by rw [hlenTake]; exact hltJ)) hnej).1 hui l hor hrj
      cases d with
      | ind _ | ctor _ _ _ _ | prim _ | caseDef _ => simp [ifaceOf?] at hifc
      | stuck _ _ _ _ =>
        have h0 : (callWithS P ext (n' + 1) r vs c).run (st, b + 1) = .error .stuck := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [hfind, MS_liftM_run]; rfl
        rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | body params res' rc' rs' body =>
        simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
        have hnotLt' : ¬ (vs.length < params.size) := hnotLt
        have hneZero' : (params.size == 0) = false := hneZero
        have hstep : (callWithS P ext (n' + 1) r vs c).run (st, b + 1) =
            (match (enterS P ext n' params res' rc' body (vs.take params.size)).run (st, b) with
             | .error e => .error e
             | .ok (f, (st₁, B₁)) => (applyAllS P ext n' f (vs.drop params.size) c).run (st₁, B₁)) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          rw [hfind]; dsimp only
          rw [ite_eq_right (fun h => absurd h hnotLt'), hneZero']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [MS_bind_run]
          cases (enterS P ext n' params res' rc' body (vs.take params.size)).run (st, b) with
          | error _ => rfl
          | ok p => rcases p with ⟨f, ⟨st₁, B₁⟩⟩; rfl
        rw [hstep]
        obtain ⟨hnoVE, hokE⟩ := hih.2.1 b n' r params res' rc' rs' body (vs.take params.size) st
          _ _ _ _ hbB hfind hlenTake (StOk_mono (by omega) hst) hssC hFltC
          (fun i p v hp hv hne =>
            let h := hArgsBody i p v hp hv hne
            ⟨h.1, h.2.1, CtorFieldsOk_mono (by omega) h.2.2.1,
             fun hoU => ⟨FunOkAt_mono (by omega) (h.2.2.2.1 hoU).1, (h.2.2.2.1 hoU).2⟩,
             fun hnuO => ⟨(h.2.2.2.2.1 hnuO).1, (h.2.2.2.2.1 hnuO).2.1, (h.2.2.2.2.1 hnuO).2.2.1,
               FunOkAt_mono (by omega) (h.2.2.2.2.1 hnuO).2.2.2⟩,
             h.2.2.2.2.2⟩)
          hDisjBody
        cases hent : (enterS P ext n' params res' rc' body (vs.take params.size)).run (st, b) with
        | error e =>
          refine ⟨fun k' hk' => by cases hk'; exact hnoVE k' hent, fun _ _ _ h => by cases h⟩
        | ok pe =>
          rcases pe with ⟨f, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁, hpresCall, honce₁, hssf₁,
            hbvF, hclsF, hnoF, hcfF, hfunF, hopenF, hreachF, huniqF⟩ := hokE f st₁ B₁ hent
          have hLeafNum : ∀ (i : Nat) (p : Param) (v : Val),
              params[i]? = some p → (vs.take params.size)[i]? = some v →
              p.mode ≠ .erased → p.cls = .leaf → ∀ l, Reach st.heap v l → NumLoc st.heap l := by
            intro i p v hp hv hne hleaf l hrl
            cases n' with
            | zero =>
              cases b with
              | zero => unfold enterS at hent; rw [MS_bind_run, MS_spend_zero] at hent; cases hent
              | succ b' => unfold enterS at hent; rw [MS_bind_run, MS_spend_succ] at hent; cases hent
            | succ n'' =>
              cases b with
              | zero => unfold enterS at hent; rw [MS_bind_run, MS_spend_zero] at hent; cases hent
              | succ b' =>
                unfold enterS at hent; rw [MS_bind_run, MS_spend_succ] at hent; dsimp only at hent
                rw [MS_bind_run, MS_liftM_run] at hent
                let st_o : St := { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions }
                have hopen : openRegion.run st = .ok ((st.nextRegion, st.regions.headD 0), st_o) := rfl
                rw [hopen] at hent; dsimp only at hent
                rw [MS_bind_run, MS_liftM_run] at hent
                cases hbp : (bindParamsM P n'' st.nextRegion (params.toList.zip (vs.take params.size)) []).run st_o with
                | error e => rw [hbp] at hent; cases hent
                | ok pbp =>
                  have hi : i < params.size := (Array.getElem?_eq_some_iff.mp hp).1
                  have hz : (params.toList.zip (vs.take params.size))[i]? = some (p, v) := by
                    rw [List.getElem?_eq_getElem (by rw [List.length_zip, Array.length_toList, hlenTake, Nat.min_self]; exact hi)]
                    rw [List.getElem_zip]
                    have hp' : params[i] = p := by rw [Array.getElem?_eq_getElem hi] at hp; exact Option.some.inj hp
                    have hv' : (vs.take params.size)[i]'(by rw [hlenTake]; exact hi) = v := by
                      rw [List.getElem?_eq_getElem (by rw [hlenTake]; exact hi)] at hv; exact Option.some.inj hv
                    simp [hp', hv']
                  have hbpHyps' : ∀ (i' : Nat) (p' : Param) (v' : Val),
                      (params.toList.zip (vs.take params.size))[i']? = some (p', v') →
                      (p'.mode ≠ .erased → DeepLive st_o.heap v' ∧ AcyclicFrom st_o.heap v') ∧
                      (p'.mode.isUnique = true → OwnTreeFull P st_o.heap v' ∧
                        (p'.mode.isBorrowed = false → OpenUnder st_o.regions [] v')) := by
                    intro i' p' v' h'
                    have hh := hbpHyps i' p' v' h'
                    refine ⟨hh.1, fun hu => ⟨(hh.2 hu).1, fun hnb r' hr' hopen' => ?_⟩⟩
                    rcases List.mem_cons.mp hopen' with rfl | hmem
                    · obtain ⟨hltZ, hgetZ⟩ := List.getElem?_eq_some_iff.mp h'
                      rw [List.length_zip, Array.length_toList, hlenTake, Nat.min_self] at hltZ
                      rw [List.getElem_zip] at hgetZ; cases hgetZ
                      have hne' : params[i'].mode ≠ .erased := by
                        cases hm : params[i'].mode <;> simp [hm, BinderMode.isUnique] at hu ⊢
                      have htb := (hArgsBody i' _ _ (Array.getElem?_eq_getElem hltZ)
                        (List.getElem?_eq_getElem (by rw [hlenTake]; exact hltZ)) hne').1.2.2.2 _ (HeldBy.refl _ _) st.nextRegion hr'
                      exact absurd htb (Nat.lt_irrefl _)
                    · exact (hh.2 hu).2 hnb r' hr' hmem
                  exact bindParamsM_leaf_arg_numLoc (st := st_o) hst.1 hbpHyps' hbpDisj hbp i p v hz hne hleaf l hrl
          obtain ⟨hpresF₁, hpresEx₁, hpresEnv₁, hpresNum₁, hsim₁, hEnvNrf₁, hVSimR0, hDisjR0, hNrfR0, hNvR0, hTrEx⟩ :=
            callResult_pos_post (d := .body params res' rc' rs' body) rfl hleLen hmatch hErased hrun hsim hstat hargs hEnvNrf hForbidLt hBadDepLive₁
              (by omega) hst₁ hsz₁ hr₁ hnr₁ hstat₁ hstr₁ hpresCall honce₁ hssf₁
              hbvF hclsF hnoF hcfF hfunF hopenF hreachF huniqF hLeafNum
          exact hContPos n' b B₁ f st₁ hB₁ rfl hst₁ hsz₁ hcap₁ hr₁ hnr₁ hstat₁ hstr₁
            hpresF₁ hpresEx₁ hpresEnv₁ hpresNum₁ honce₁ hssf₁ hsim₁ hEnvNrf₁
            hbvF hclsF hcfF hVSimR0 hDisjR0 hNrfR0 hNvR0 hreachF hTrEx
      | extern params res' rc' rs' =>
        simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
        have hnotLt' : ¬ (vs.length < params.size) := hnotLt
        have hstep : (callWithS P ext (n' + 1) r vs c).run (st, b + 1) =
            (match (callExtern P ext n' r params res' rc' (vs.take params.size)).run st with
             | .error e => .error e
             | .ok (f, st₁) => (applyAllS P ext n' f (vs.drop params.size) c).run (st₁, b)) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only
          rw [hfind]; dsimp only
          rw [ite_eq_right (fun h => absurd h hnotLt'), MS_bind_run, MS_liftM_run]
          cases (callExtern P ext n' r params res' rc' (vs.take params.size)).run st <;> rfl
        rw [hstep]
        obtain ⟨hnoVE, hokE⟩ := callExtern_sound_base (P := P) (ext := ext) (B := b) (fuel := n')
          (baseRegs := [])
          hext hfind (StOk_mono (by omega) hst) (hih.1 b hbB) hssC hFltC
          (fun i p v hp hv =>
            ⟨fun hne =>
              let h := hArgsBody i p v hp hv hne
              ⟨h.1, h.2.1, fun hnuO => (h.2.2.2.2.1 hnuO).1, CtorFieldsOk_mono (by omega) h.2.2.1,
               fun hnuO => FunOkAt_mono (by omega) (h.2.2.2.2.1 hnuO).2.2.2⟩,
             fun hu =>
              have hne : p.mode ≠ .erased := by
                cases hm : p.mode <;> simp [hm, BinderMode.isUnique] at hu ⊢
              let h := (hArgsBody i p v hp hv hne).2.2.2.2.2 hu
              ⟨h.1, h.2.1, fun hnb => h.2.2 hnb v (HeldBy.refl _ _)⟩,
             fun hru hrc hpm hnl => hRepUExt i p v hp hv hru hrc hpm hnl⟩)
          (fun i j pi pj vi vj hij hpi hvi hpj hvj hui hnej =>
            (hDisjBody i j pi pj vi vj hij hpi hvi hpj hvj hnej).1 hui)
        cases heRun : (callExtern P ext n' r params res' rc' (vs.take params.size)).run st with
        | error e =>
          refine ⟨fun k' hk' => by cases hk'; exact hnoVE k' heRun, fun _ _ _ h => by cases h⟩
        | ok pe =>
          rcases pe with ⟨f, st₁⟩; dsimp only
          obtain ⟨hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁, hpresCall, honce₁, hssf₁,
            hbvF, hclsF, hopenF, hnoF, hcfF, hfunF, hreachE, huniqE⟩ := hokE f st₁ heRun
          have hreachF : ∀ l, Reach st₁.heap f l →
              st.heap.objs.size ≤ l ∨
              (∃ (i : Nat) (p : Param) (v : Val),
                params[i]? = some p ∧ (vs.take params.size)[i]? = some v ∧ p.mode ≠ .erased ∧
                (res'.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧ Reach st.heap v l) ∨
              StaticStrLoc st l ∨ NumLoc st₁.heap l := by
            intro l hrl
            rcases hreachE l hrl with hge | ⟨i, p, vi, hp, hvi, hpm, hrvi⟩ | hnum
            · exact Or.inl hge
            · exact Or.inr (Or.inl ⟨i, p, vi, hp, hvi, by rw [hpm]; decide, Or.inr (by rw [hpm]; rfl), hrvi⟩)
            · exact Or.inr (Or.inr (Or.inr hnum))
          have huniqF : res'.isUnique = true ∧ rc' = .val →
              OwnTreeFull P st₁.heap f ∧
              ∀ l, OwnReach P st₁.heap f l →
                ¬ (Frame l ∨ FrameExtra l ∨ NumLoc st.heap l ∨
                  ∃ (j : Nat) (b' : Bnd) (ab : ABnd), Scope j ∧ env[j]? = some b' ∧ aenv[j]? = some ab ∧
                    ab.mode ≠ .erased ∧ ActiveVal σ₁ (effVal ab) ∧ Reach st.heap b'.val l) ∧
                ¬ StaticStrLoc st₁ l := fun h =>
            let ⟨ht, ho⟩ := huniqE h; ⟨ht, fun l hor => ⟨(ho l hor).2.1, (ho l hor).2.2⟩⟩
          have hLeafNum : ∀ (i : Nat) (p : Param) (v : Val),
              params[i]? = some p → (vs.take params.size)[i]? = some v →
              p.mode ≠ .erased → p.cls = .leaf → ∀ l, Reach st.heap v l → NumLoc st.heap l := by
            intro i p v hp hv hne hleaf l hrl
            unfold callExtern at heRun
            let st_o : St := { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions }
            have hopen : openRegion.run st = .ok ((st.nextRegion, st.regions.headD 0), st_o) := rfl
            rw [M_bind_run, hopen] at heRun; dsimp only at heRun
            rw [M_bind_run, forIn_list_bindAtVals_eq_bindParamsM P n' st.nextRegion
              (params.toList.zip (vs.take params.size)) [] [] _ rfl, M_bind_run] at heRun
            cases hbp : (bindParamsM P n' st.nextRegion (params.toList.zip (vs.take params.size)) []).run st_o with
            | error e => rw [hbp] at heRun; cases heRun
            | ok pbp =>
              have hi : i < params.size := (Array.getElem?_eq_some_iff.mp hp).1
              have hz : (params.toList.zip (vs.take params.size))[i]? = some (p, v) := by
                rw [List.getElem?_eq_getElem (by rw [List.length_zip, Array.length_toList, hlenTake, Nat.min_self]; exact hi)]
                rw [List.getElem_zip]
                have hp' : params[i] = p := by rw [Array.getElem?_eq_getElem hi] at hp; exact Option.some.inj hp
                have hv' : (vs.take params.size)[i]'(by rw [hlenTake]; exact hi) = v := by
                  rw [List.getElem?_eq_getElem (by rw [hlenTake]; exact hi)] at hv; exact Option.some.inj hv
                simp [hp', hv']
              have hbpHyps' : ∀ (i' : Nat) (p' : Param) (v' : Val),
                  (params.toList.zip (vs.take params.size))[i']? = some (p', v') →
                  (p'.mode ≠ .erased → DeepLive st_o.heap v' ∧ AcyclicFrom st_o.heap v') ∧
                  (p'.mode.isUnique = true → OwnTreeFull P st_o.heap v' ∧
                    (p'.mode.isBorrowed = false → OpenUnder st_o.regions [] v')) := by
                intro i' p' v' h'
                have hh := hbpHyps i' p' v' h'
                refine ⟨hh.1, fun hu => ⟨(hh.2 hu).1, fun hnb r' hr' hopen' => ?_⟩⟩
                rcases List.mem_cons.mp hopen' with rfl | hmem
                · obtain ⟨hltZ, hgetZ⟩ := List.getElem?_eq_some_iff.mp h'
                  rw [List.length_zip, Array.length_toList, hlenTake, Nat.min_self] at hltZ
                  rw [List.getElem_zip] at hgetZ; cases hgetZ
                  have hne' : params[i'].mode ≠ .erased := by
                    cases hm : params[i'].mode <;> simp [hm, BinderMode.isUnique] at hu ⊢
                  have htb := (hArgsBody i' _ _ (Array.getElem?_eq_getElem hltZ)
                    (List.getElem?_eq_getElem (by rw [hlenTake]; exact hltZ)) hne').1.2.2.2 _ (HeldBy.refl _ _) st.nextRegion hr'
                  exact absurd htb (Nat.lt_irrefl _)
                · exact (hh.2 hu).2 hnb r' hr' hmem
              exact bindParamsM_leaf_arg_numLoc (st := st_o) hst.1 hbpHyps' hbpDisj hbp i p v hz hne hleaf l hrl
          obtain ⟨hpresF₁, hpresEx₁, hpresEnv₁, hpresNum₁, hsim₁, hEnvNrf₁, hVSimR0, hDisjR0, hNrfR0, hNvR0, hTrEx⟩ :=
            callResult_pos_post (d := .extern params res' rc' rs') rfl hleLen hmatch hErased hrun hsim hstat hargs hEnvNrf hForbidLt hBadDepLive₁
              (by omega) hst₁ hsz₁ hr₁ hnr₁ (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _)
              hpresCall honce₁ hssf₁ hbvF hclsF hnoF hcfF hfunF hopenF hreachF huniqF hLeafNum
          exact hContPos n' b b f st₁ (Nat.le_refl _) rfl hst₁ hsz₁ hcap₁ hr₁ hnr₁
            (hstat₁ ▸ ArrayExtends.refl _) (hstr₁ ▸ ArrayExtends.refl _)
            hpresF₁ hpresEx₁ hpresEnv₁ hpresNum₁ honce₁ hssf₁ hsim₁ hEnvNrf₁
            hbvF hclsF hcfF hVSimR0 hDisjR0 hNrfR0 hNvR0 hreachF hTrEx

end

end IxCK.Resource.Proof
