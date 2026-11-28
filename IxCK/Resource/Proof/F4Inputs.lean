import IxCK.Resource.Proof.F4Inv
import IxCK.Resource.Proof.Ops
import IxCK.Resource.Proof.ModeOk

/-!
# Skeleton Coercions, `PapsFunOk`, Extern Calls, and Input Heaps (`F4Inputs`)

Bridges `IxCK.Resource.Statement`'s skeleton/extern/input contracts (`Skel.admits`,
`Skel.admitsNA`, `PapArgOk`, `ClosureAt`, `DefaultPaps`, `ExternOk`, `InputsOk`)
to the `F4Inv` behavioral logical relation (`FunOkAt`, `CtorFieldsOk`, `StOk`, `VSim`):

1. **Skeleton coercions** (`FunOkAt_default_equiv`, `FunOkAt_of_admits`, `FunOkAt_of_admitsNA`,
   `VSim_of_admits`, `VSim_of_admitsNA`).
2. **`PapsFunOk` & heap bridges** (`DefaultPaps_to_FunOkAt_and_CtorFieldsOk`, `ClosureAt_to_FunOkAt`).
3. **Extern call soundness** (`callExtern_sound`).
4. **Input heap initialization** (`InputsOk_to_StOk_and_Args`).
-/

namespace IxCK.Resource.Proof

open IxCK.Resource Ixon

/-! ## 1. `FunOkAt` & `VSim` Skeleton Coercions -/

theorem Skel.admitsNA_isArrowSkel {s₁ s₂ : Skel} (h : s₁.admitsNA s₂ = true) :
    isArrowSkel s₁ = isArrowSkel s₂ := by
  cases s₁ <;> cases s₂ <;> simp [Skel.admitsNA, isArrowSkel] at h ⊢

theorem arrowParts_isDefault {sk : Skel} (hd : sk.isDefault = true) :
    (arrowParts sk).1 = .many ∧
    (arrowParts sk).2.1.isDefault = true ∧
    (arrowParts sk).2.2.1 = .shared ∧
    (arrowParts sk).2.2.2.isDefault = true := by
  cases sk with
  | data | unknown | dataApp _ _ =>
    exact ⟨rfl, rfl, rfl, rfl⟩
  | arrow i d r c =>
    simp only [Skel.isDefault, Bool.and_eq_true, beq_iff_eq] at hd
    exact ⟨hd.1.1.1, hd.1.2, hd.1.1.2, hd.2⟩

theorem FunOkAt_nonArrow_eq_unknown {P : Prog} {ext : ExternOracle} {B : Nat}
    {st : St} {sk : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f : Val}
    (hna : isArrowSkel sk = false) :
    FunOkAt P ext B st sk onceOnly Foot f ↔ FunOkAt P ext B st .unknown onceOnly Foot f := by
  cases B with
  | zero => simp [FunOkAt]
  | succ b =>
    cases sk with
    | data | unknown | dataApp _ _ => simp only [FunOkAt, arrowParts]
    | arrow _ _ _ _ => simp [isArrowSkel] at hna

/-- Core mutual strong induction over budget `B` proving default equivalence, `admits` coercion
(for `onceOnly = false`), and `admitsNA` coercion (for arbitrary `onceOnly`). -/
private theorem FunOkAt_coercions_le (P : Prog) (ext : ExternOracle) :
    ∀ (N : Nat), ∀ B ≤ N,
      (∀ {st : St} {sk₁ sk₂ : Skel} {Foot : Nat → Prop} {f : Val},
        sk₁.isDefault = true → sk₂.isDefault = true →
        FunOkAt P ext B st sk₁ false Foot f → FunOkAt P ext B st sk₂ false Foot f) ∧
      (∀ {st : St} {sk₁ sk₂ : Skel} {Foot : Nat → Prop} {f : Val},
        sk₁.admits sk₂ = true →
        FunOkAt P ext B st sk₁ false Foot f → FunOkAt P ext B st sk₂ false Foot f) ∧
      (∀ {st : St} {sk₁ sk₂ : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f : Val},
        sk₁.admitsNA sk₂ = true →
        FunOkAt P ext B st sk₁ onceOnly Foot f → FunOkAt P ext B st sk₂ onceOnly Foot f) := by
  intro N
  induction N with
  | zero =>
    intro B hle
    have hB : B = 0 := Nat.eq_zero_of_le_zero hle
    subst hB
    exact ⟨fun _ _ _ => by rw [FunOkAt]; trivial,
           fun _ _ => by rw [FunOkAt]; trivial,
           fun _ _ => by rw [FunOkAt]; trivial⟩
  | succ n ih =>
    intro B hle
    cases B with
    | zero =>
      exact ⟨fun _ _ _ => by rw [FunOkAt]; trivial,
             fun _ _ => by rw [FunOkAt]; trivial,
             fun _ _ => by rw [FunOkAt]; trivial⟩
    | succ b =>
      have hbn : b ≤ n := Nat.le_of_succ_le_succ hle
      have hDef : ∀ {st : St} {sk₁ sk₂ : Skel} {Foot : Nat → Prop} {f : Val},
          sk₁.isDefault = true → sk₂.isDefault = true →
          FunOkAt P ext (b + 1) st sk₁ false Foot f → FunOkAt P ext (b + 1) st sk₂ false Foot f := by
        intro st₀ sk₁ sk₂ Foot f₀ hd₁ hd₂ hf
        have hp₁ := arrowParts_isDefault hd₁
        have hp₂ := arrowParts_isDefault hd₂
        rw [FunOkAt] at hf ⊢
        rcases hap₁ : arrowParts sk₁ with ⟨m₁, d₁, r₁, c₁⟩
        rcases hap₂ : arrowParts sk₂ with ⟨m₂, d₂, r₂, c₂⟩
        rw [hap₁] at hp₁ hf
        rw [hap₂] at hp₂
        obtain ⟨rfl, hd₁', rfl, hc₁'⟩ := hp₁
        obtain ⟨rfl, hd₂', rfl, hc₂'⟩ := hp₂
        dsimp only at hf ⊢
        intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
          hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg
        have harg₁ : BinderMode.many ≠ .erased →
            (BinderMode.many.usage = .once → FunOkAt P ext B_call st d₁ aOnce aFoot a) ∧
            (BinderMode.many.usage ≠ .once →
              NoOnceCell st.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
              FunOkAt P ext B_call st d₁ false (fun _ => False) a) ∧
            (BinderMode.many.isUnique = true →
              OwnTreeFull P st.heap a ∧
              (∀ l, OwnReach P st.heap a l → ¬ Frame l ∧ ¬ Reach st.heap f l) ∧
              (BinderMode.many.isBorrowed = false → DeepOpenUnder st.heap st.regions [] a)) ∧
            ((ResultMode.shared = .unique ∧ c = .val ∧
              (BinderMode.many = .many ∨ BinderMode.many = .once)) →
              DeepOpenUnder st.heap st.regions [] a) := by
          intro hne
          obtain ⟨ho1, ho2, ho3, ho4⟩ := harg hne
          refine ⟨(fun h => by cases h), (fun hnu => ?_), ho3, ho4⟩
          obtain ⟨hno, haO, haF, hfun⟩ := ho2 hnu
          exact ⟨hno, haO, haF, (ih B_call (Nat.le_trans hB hbn)).1 hd₂' hd₁' hfun⟩
        obtain ⟨hnoViol, hok⟩ := hf B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
          hloc hsh hrf hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg₁
        refine ⟨hnoViol, fun rv st' B' hrun => ?_⟩
        obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
          hbase, hcls, hopen, hcf, hrb, ⟨hroF, _⟩, huniq⟩ := hok rv st' B' hrun
        refine ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
          hbase, hcls, hopen, hcf, hrb, ⟨?_, ?_⟩, huniq⟩
        · intro _
          have hfalse₁ : (isArrowSkel c₁ && (false || BinderMode.many.isUnique || (BinderMode.many.usage == .once))) = false := by
            simp [BinderMode.isUnique, BinderMode.usage]
          obtain ⟨hno, hfun⟩ := hroF hfalse₁
          exact ⟨hno, (ih B' (Nat.le_trans hB' (Nat.le_trans hB hbn))).1 hc₁' hc₂' hfun⟩
        · intro htrue
          simp [BinderMode.isUnique, BinderMode.usage] at htrue
      have hAdm : ∀ {st : St} {sk₁ sk₂ : Skel} {Foot : Nat → Prop} {f : Val},
          sk₁.admits sk₂ = true →
          FunOkAt P ext (b + 1) st sk₁ false Foot f → FunOkAt P ext (b + 1) st sk₂ false Foot f := by
        intro st₀ sk₁ sk₂ Foot f₀ hadm hf
        cases sk₁ with
        | unknown =>
          have hd₂ : sk₂.isDefault = true := Skel.admits_default_left rfl hadm
          exact hDef rfl hd₂ hf
        | data =>
          cases sk₂ with
          | unknown => exact hDef rfl rfl hf
          | data | dataApp _ _ =>
            exact (FunOkAt_nonArrow_eq_unknown rfl).mpr ((FunOkAt_nonArrow_eq_unknown rfl).mp hf)
          | arrow _ _ _ _ => simp [Skel.admits] at hadm
        | dataApp f₁ a₁ =>
          cases sk₂ with
          | unknown =>
            have hd₁ : (Skel.dataApp f₁ a₁).isDefault = true := Skel.admits_default_right rfl hadm
            exact hDef hd₁ rfl hf
          | data | dataApp _ _ =>
            exact (FunOkAt_nonArrow_eq_unknown rfl).mpr ((FunOkAt_nonArrow_eq_unknown rfl).mp hf)
          | arrow _ _ _ _ => simp [Skel.admits] at hadm
        | arrow i₁ d₁ r₁ c₁ =>
          cases sk₂ with
          | unknown =>
            have hd₁ : (Skel.arrow i₁ d₁ r₁ c₁).isDefault = true := Skel.admits_default_right rfl hadm
            exact hDef hd₁ rfl hf
          | data | dataApp _ _ => simp [Skel.admits] at hadm
          | arrow i₂ d₂ r₂ c₂ =>
            simp only [Skel.admits, Bool.and_eq_true, beq_iff_eq] at hadm
            obtain ⟨⟨⟨rfl, rfl⟩, hd⟩, hc⟩ := hadm
            rw [FunOkAt] at hf ⊢
            dsimp only [arrowParts] at hf ⊢
            intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
              hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg
            have harg₁ : i₁ ≠ .erased →
                (i₁.usage = .once → FunOkAt P ext B_call st d₁ aOnce aFoot a) ∧
                (i₁.usage ≠ .once →
                  NoOnceCell st.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
                  FunOkAt P ext B_call st d₁ false (fun _ => False) a) ∧
                (i₁.isUnique = true →
                  OwnTreeFull P st.heap a ∧
                  (∀ l, OwnReach P st.heap a l → ¬ Frame l ∧ ¬ Reach st.heap f l) ∧
                  (i₁.isBorrowed = false → DeepOpenUnder st.heap st.regions [] a)) ∧
                ((r₁ = .unique ∧ c = .val ∧ (i₁ = .many ∨ i₁ = .once)) →
                  DeepOpenUnder st.heap st.regions [] a) := by
              intro hne
              obtain ⟨ho1, ho2, ho3, ho4⟩ := harg hne
              refine ⟨fun hu => ?_, fun hnu => ?_, ho3, ho4⟩
              · have hdNA : d₁.admitsNA d₂ = true := by simpa [hu] using hd
                have hdNA' : d₂.admitsNA d₁ = true := by rwa [Skel.admitsNA_symm]
                exact (ih B_call (Nat.le_trans hB hbn)).2.2 hdNA' (ho1 hu)
              · have hdA : d₁.admits d₂ = true := by simp [hnu] at hd; exact hd
                have hdA' : d₂.admits d₁ = true := by rwa [Skel.admits_symm]
                obtain ⟨hno, haO, haF, hfun⟩ := ho2 hnu
                exact ⟨hno, haO, haF, (ih B_call (Nat.le_trans hB hbn)).2.1 hdA' hfun⟩
            obtain ⟨hnoViol, hok⟩ := hf B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
              hloc hsh hrf hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg₁
            refine ⟨hnoViol, fun rv st' B' hrun => ?_⟩
            obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
              hbase, hcls, hopen, hcf, hrb, ⟨hroF, hroT⟩, huniq⟩ := hok rv st' B' hrun
            refine ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
              hbase, hcls, hopen, hcf, hrb, ?_, huniq⟩
            cases hflag : (i₁.isUnique || (i₁.usage == .once)) with
            | true =>
              have hcNA : c₁.admitsNA c₂ = true := by simpa [hflag] using hc
              have hArrEq : isArrowSkel c₁ = isArrowSkel c₂ := Skel.admitsNA_isArrowSkel hcNA
              constructor
              · intro hfalse
                have hfalse₁ : (isArrowSkel c₁ && (false || i₁.isUnique || (i₁.usage == .once))) = false := by
                  simpa [hArrEq] using hfalse
                obtain ⟨hno, hfun⟩ := hroF hfalse₁
                exact ⟨hno, (ih B' (Nat.le_trans hB' (Nat.le_trans hB hbn))).2.2 hcNA hfun⟩
              · intro htrue
                have htrue₁ : (isArrowSkel c₁ && (false || i₁.isUnique || (i₁.usage == .once))) = true := by
                  simpa [hArrEq] using htrue
                obtain ⟨resFoot, hrfBnd, hfun⟩ := hroT htrue₁
                exact ⟨resFoot, hrfBnd, (ih B' (Nat.le_trans hB' (Nat.le_trans hB hbn))).2.2 hcNA hfun⟩
            | false =>
              have hcA : c₁.admits c₂ = true := by simpa [hflag] using hc
              constructor
              · intro _
                have hfalse₁ : (isArrowSkel c₁ && (false || i₁.isUnique || (i₁.usage == .once))) = false := by
                  simp [hflag]
                obtain ⟨hno, hfun⟩ := hroF hfalse₁
                exact ⟨hno, (ih B' (Nat.le_trans hB' (Nat.le_trans hB hbn))).2.1 hcA hfun⟩
              · intro htrue
                simp [hflag] at htrue
      have hAdmNA : ∀ {st : St} {sk₁ sk₂ : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f : Val},
          sk₁.admitsNA sk₂ = true →
          FunOkAt P ext (b + 1) st sk₁ onceOnly Foot f → FunOkAt P ext (b + 1) st sk₂ onceOnly Foot f := by
        intro st₀ sk₁ sk₂ onceOnly Foot f₀ hadm hf
        cases sk₁ with
        | unknown | data | dataApp _ _ =>
          cases sk₂ with
          | unknown | data | dataApp _ _ =>
            exact (FunOkAt_nonArrow_eq_unknown rfl).mpr ((FunOkAt_nonArrow_eq_unknown rfl).mp hf)
          | arrow _ _ _ _ => simp [Skel.admitsNA] at hadm
        | arrow i₁ d₁ r₁ c₁ =>
          cases sk₂ with
          | unknown | data | dataApp _ _ => simp [Skel.admitsNA] at hadm
          | arrow i₂ d₂ r₂ c₂ =>
            simp only [Skel.admitsNA, Bool.and_eq_true, beq_iff_eq] at hadm
            obtain ⟨⟨⟨rfl, rfl⟩, hd⟩, hcNA⟩ := hadm
            have hArrEq : isArrowSkel c₁ = isArrowSkel c₂ := Skel.admitsNA_isArrowSkel hcNA
            rw [FunOkAt] at hf ⊢
            dsimp only [arrowParts] at hf ⊢
            intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
              hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg
            have harg₁ : i₁ ≠ .erased →
                (i₁.usage = .once → FunOkAt P ext B_call st d₁ aOnce aFoot a) ∧
                (i₁.usage ≠ .once →
                  NoOnceCell st.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
                  FunOkAt P ext B_call st d₁ false (fun _ => False) a) ∧
                (i₁.isUnique = true →
                  OwnTreeFull P st.heap a ∧
                  (∀ l, OwnReach P st.heap a l → ¬ Frame l ∧ ¬ Reach st.heap f l) ∧
                  (i₁.isBorrowed = false → DeepOpenUnder st.heap st.regions [] a)) ∧
                ((r₁ = .unique ∧ c = .val ∧ (i₁ = .many ∨ i₁ = .once)) →
                  DeepOpenUnder st.heap st.regions [] a) := by
              intro hne
              obtain ⟨ho1, ho2, ho3, ho4⟩ := harg hne
              refine ⟨fun hu => ?_, fun hnu => ?_, ho3, ho4⟩
              · have hdNA : d₁.admitsNA d₂ = true := by simpa [hu] using hd
                have hdNA' : d₂.admitsNA d₁ = true := by rwa [Skel.admitsNA_symm]
                exact (ih B_call (Nat.le_trans hB hbn)).2.2 hdNA' (ho1 hu)
              · have hdA : d₁.admits d₂ = true := by simp [hnu] at hd; exact hd
                have hdA' : d₂.admits d₁ = true := by rwa [Skel.admits_symm]
                obtain ⟨hno, haO, haF, hfun⟩ := ho2 hnu
                exact ⟨hno, haO, haF, (ih B_call (Nat.le_trans hB hbn)).2.1 hdA' hfun⟩
            obtain ⟨hnoViol, hok⟩ := hf B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
              hloc hsh hrf hfBase hfOpen hfCf haBase haOpen haCf hFf hFa h12 hfa haf haNum harg₁
            refine ⟨hnoViol, fun rv st' B' hrun => ?_⟩
            obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
              hbase, hcls, hopen, hcf, hrb, ⟨hroF, hroT⟩, huniq⟩ := hok rv st' B' hrun
            refine ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf,
              hbase, hcls, hopen, hcf, hrb, ⟨?_, ?_⟩, huniq⟩
            · intro hfalse
              have hfalse₁ : (isArrowSkel c₁ && (onceOnly || i₁.isUnique || (i₁.usage == .once))) = false := by
                simpa [hArrEq] using hfalse
              obtain ⟨hno, hfun⟩ := hroF hfalse₁
              exact ⟨hno, (ih B' (Nat.le_trans hB' (Nat.le_trans hB hbn))).2.2 hcNA hfun⟩
            · intro htrue
              have htrue₁ : (isArrowSkel c₁ && (onceOnly || i₁.isUnique || (i₁.usage == .once))) = true := by
                simpa [hArrEq] using htrue
              obtain ⟨resFoot, hrfBnd, hfun⟩ := hroT htrue₁
              exact ⟨resFoot, hrfBnd, (ih B' (Nat.le_trans hB' (Nat.le_trans hB hbn))).2.2 hcNA hfun⟩
      exact ⟨hDef, hAdm, hAdmNA⟩

theorem FunOkAt_default_equiv {P : Prog} {ext : ExternOracle} {B : Nat}
    {st : St} {sk₁ sk₂ : Skel} {Foot : Nat → Prop} {f : Val}
    (hd₁ : sk₁.isDefault = true) (hd₂ : sk₂.isDefault = true) :
    FunOkAt P ext B st sk₁ false Foot f ↔ FunOkAt P ext B st sk₂ false Foot f :=
  ⟨(FunOkAt_coercions_le P ext B B (Nat.le_refl _)).1 hd₁ hd₂,
   (FunOkAt_coercions_le P ext B B (Nat.le_refl _)).1 hd₂ hd₁⟩

theorem FunOkAt_of_admits {P : Prog} {ext : ExternOracle} {B : Nat}
    {st : St} {sk₁ sk₂ : Skel} {Foot : Nat → Prop} {f : Val}
    (hadm : sk₁.admits sk₂ = true)
    (hf : FunOkAt P ext B st sk₁ false Foot f) :
    FunOkAt P ext B st sk₂ false Foot f :=
  (FunOkAt_coercions_le P ext B B (Nat.le_refl _)).2.1 hadm hf

theorem FunOkAt_of_admitsNA {P : Prog} {ext : ExternOracle} {B : Nat}
    {st : St} {sk₁ sk₂ : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f : Val}
    (hadm : sk₁.admitsNA sk₂ = true)
    (hf : FunOkAt P ext B st sk₁ onceOnly Foot f) :
    FunOkAt P ext B st sk₂ onceOnly Foot f :=
  (FunOkAt_coercions_le P ext B B (Nat.le_refl _)).2.2 hadm hf

theorem VSim_of_admitsNA {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp}
    {Foot : Nat → Prop} {av : AVal} {sk : Skel} {v : Val}
    (hadm : av.skel.admitsNA sk = true)
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot av v) :
    VSim P ext B st Frame NoKill NoSpend σ I Foot { av with skel := sk } v := by
  obtain ⟨hregs, hdeps, hsrc, hspent, hact⟩ := hv
  refine ⟨hregs, hdeps, hsrc, hspent, fun ha => ?_⟩
  obtain ⟨hbase, hopen, hcf, hcls, hplain, hoO, hsrcO, htr⟩ := hact ha
  refine ⟨hbase, hopen, hcf, hcls, ?_, ?_, ?_, htr⟩
  · intro hp
    obtain ⟨hno, hnf, hfun⟩ := hplain hp
    exact ⟨hno, hnf, FunOkAt_of_admitsNA hadm hfun⟩
  · intro ho
    obtain ⟨h1, h2, hctor, hfun⟩ := hoO ho
    exact ⟨h1, h2, hctor, FunOkAt_of_admitsNA hadm hfun⟩
  · intro hs
    obtain ⟨h1, h2, hfun⟩ := hsrcO hs
    exact ⟨h1, h2, FunOkAt_of_admitsNA hadm hfun⟩

theorem VSim_of_admits {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp}
    {Foot : Nat → Prop} {av : AVal} {sk : Skel} {v : Val}
    (hadm : av.skel.admits sk = true)
    (hnoOnceOnly : av.onceOnly = false)
    (hnotOnceSrc : ¬ IsOnceSrc σ av)
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot av v) :
    VSim P ext B st Frame NoKill NoSpend σ I Foot { av with skel := sk } v := by
  obtain ⟨hregs, hdeps, hsrc, hspent, hact⟩ := hv
  refine ⟨hregs, hdeps, hsrc, hspent, fun ha => ?_⟩
  obtain ⟨hbase, hopen, hcf, hcls, hplain, _, _, htr⟩ := hact ha
  refine ⟨hbase, hopen, hcf, hcls, ?_, ?_, ?_, htr⟩
  · intro hp
    obtain ⟨hno, hnf, hfun⟩ := hplain hp
    exact ⟨hno, hnf, FunOkAt_of_admits hadm hfun⟩
  · intro ho; rw [hnoOnceOnly] at ho; cases ho
  · intro hs; exact absurd hs hnotOnceSrc

/-! ## 2. `PapsFunOk` & Input/Extern Heap Bridges -/

/-- Assumption (proved in `F4.lean` by induction on `B`) that every partial application of a
program constant holding valid `PapArgOk` arguments satisfies `FunOkAt` at its remaining
interface skeleton `papSkel P r args.size`. -/
def PapsFunOk (P : Prog) (ext : ExternOracle) (B : Nat) : Prop :=
  ∀ (st : St) (loc cap : Nat) (r : Ref) (args : Array Val) (sk : Skel) (t : List Nat),
    StOk P ext B st →
    st.heap.objs[loc]? = some ⟨.pap r args, cap⟩ →
    papSkel P r args.size = some sk →
    (∀ a ∈ args.toList, PapArgOk st.heap a ∧ ValBaseOk st a) →
    FunOkAt P ext B st sk false (fun _ => False) (.ref loc cap t)

theorem PapArgOk_noOnceCell {h : Heap} {a : Val} (hpa : PapArgOk h a) :
    NoOnceCell h a := by
  intro l o hr ho t sp hcell
  rcases hpa with ⟨i, rfl⟩ | ⟨loc, cap, o₀, n, rfl, ho₀, hnum⟩
  · cases hr
  · cases hr with
    | here => rw [ho₀] at ho; cases ho; rw [hnum] at hcell; cases hcell
    | step ho1 hm1 _ => rw [ho₀] at ho1; cases ho1; rw [hnum] at hm1; cases hm1

theorem PapArgOk_not_reach_ctor {h : Heap} {a : Val} {l : Nat} {o : Obj} {r : Ref} {fs : Array Val}
    (hpa : PapArgOk h a) (hr : Reach h a l) (ho : h.objs[l]? = some o) (hcell : o.cell = .ctor r fs) :
    False := by
  rcases hpa with ⟨i, rfl⟩ | ⟨loc, cap, o₀, n, rfl, ho₀, hnum⟩
  · cases hr
  · cases hr with
    | here => rw [ho₀] at ho; cases ho; rw [hnum] at hcell; cases hcell
    | step ho1 hm1 _ => rw [ho₀] at ho1; cases ho1; rw [hnum] at hm1; cases hm1

theorem ClosureAt_to_FunOkAt {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {s : Skel} {v : Val}
    (hst : StOk P ext B st)
    (hpaps : PapsFunOk P ext B)
    (hbase : ValBaseOk st v)
    (hclo : ClosureAt P st.heap s v) :
    FunOkAt P ext B st s false (fun _ => False) v ∧
    NoOnceCell st.heap v ∧
    CtorFieldsOk P ext B st v := by
  obtain ⟨loc, cap, r, args, o, sk, rfl, ho, hcell, hargs, hps, hadm⟩ := hclo
  obtain ⟨o', ho', hcap'⟩ := hbase.1.self.1
  rw [ho] at ho'; cases ho'
  have hoPap : st.heap.objs[loc]? = some ⟨.pap r args, cap⟩ := by
    cases o with
    | mk cell cap₀ =>
      dsimp only at hcell hcap'
      subst hcell; subst hcap'; exact ho
  have hargsFull : ∀ a ∈ args.toList, PapArgOk st.heap a ∧ ValBaseOk st a := by
    intro a ha
    have hmem : a ∈ o.cell.vals := by rw [hcell]; exact ha
    exact ⟨hargs a ha, hbase.sub (HeldBy_of_mem_vals ho hmem)⟩
  have hfunSk : FunOkAt P ext B st sk false (fun _ => False) (.ref loc cap []) :=
    hpaps st loc cap r args sk [] hst hoPap hps hargsFull
  have hadm' : sk.admits s = true := by rwa [Skel.admits_symm]
  refine ⟨FunOkAt_of_admits hadm' hfunSk, ?_, ?_⟩
  · intro l o₁ hr ho₁ t sp hc₁
    cases hr with
    | here => rw [ho] at ho₁; cases ho₁; rw [hcell] at hc₁; cases hc₁
    | step ho2 hm2 hr2 =>
      rw [ho] at ho2; cases ho2; rw [hcell] at hm2
      exact PapArgOk_noOnceCell (hargs _ hm2) l o₁ hr2 ho₁ t sp hc₁
  · intro l o₁ r₁ fs₁ w hr ho₁ hc₁ _
    cases hr with
    | here => rw [ho] at ho₁; cases ho₁; rw [hcell] at hc₁; cases hc₁
    | step ho2 hm2 hr2 =>
      rw [ho] at ho2; cases ho2; rw [hcell] at hm2
      exact False.elim (PapArgOk_not_reach_ctor (hargs _ hm2) hr2 ho₁ hc₁)

theorem DefaultPaps_to_FunOkAt_and_CtorFieldsOk {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {sk : Skel} {v : Val}
    (hst : StOk P ext B st)
    (hpaps : PapsFunOk P ext B)
    (hbase : ValBaseOk st v)
    (hinput : ∀ l o, Reach st.heap v l → st.heap.objs[l]? = some o → InputCell P o.cell)
    (hdp : DefaultPaps P st.heap v)
    (hsk : sk.isDefault = true) :
    NoOnceCell st.heap v ∧
    FunOkAt P ext B st sk false (fun _ => False) v ∧
    CtorFieldsOk P ext B st v := by
  have hFunOne : ∀ {u : Val} {sk' : Skel},
      ValBaseOk st u →
      (∀ l o, Reach st.heap u l → st.heap.objs[l]? = some o → InputCell P o.cell) →
      DefaultPaps P st.heap u →
      sk'.isDefault = true →
      NoOnceCell st.heap u ∧ FunOkAt P ext B st sk' false (fun _ => False) u := by
    intro u sk' huBase huInput huDp hsk'
    refine ⟨?_, ?_⟩
    · intro l o hr ho t sp hc
      have hin := huInput l o hr ho
      rw [hc] at hin; exact hin
    · cases u with
      | imm i =>
        cases i with
        | irr => exact FunOkAt_imm_irr P ext B st sk'
        | con _ => exact FunOkAt_nonCallable_imm P ext B st sk' (by intro h; cases h)
        | bits _ => exact FunOkAt_nonCallable_imm P ext B st sk' (by intro h; cases h)
      | ref loc cap t =>
        obtain ⟨o, ho, hcap⟩ := huBase.1.self.1
        have hin := huInput loc o .here ho
        cases hcell : o.cell with
        | ctor _ _ => exact FunOkAt_nonCallable_ref P ext B st sk' ho (by rw [hcell]; trivial)
        | num _ => exact FunOkAt_nonCallable_ref P ext B st sk' ho (by rw [hcell]; trivial)
        | str _ => exact FunOkAt_nonCallable_ref P ext B st sk' ho (by rw [hcell]; trivial)
        | clo _ _ _ _ _ _ | once _ _ => rw [hcell] at hin; cases hin
        | pap r args =>
          obtain ⟨hargs, sk₀, hps, hsk₀⟩ := huDp loc o r args .here ho hcell
          have hoPap : st.heap.objs[loc]? = some ⟨.pap r args, cap⟩ := by
            cases o with
            | mk cell cap₀ =>
              dsimp only at hcell hcap
              subst hcell; subst hcap; exact ho
          have hargsFull : ∀ a ∈ args.toList, PapArgOk st.heap a ∧ ValBaseOk st a := by
            intro a ha
            have hmem : a ∈ o.cell.vals := by rw [hcell]; exact ha
            exact ⟨hargs a ha, huBase.sub (HeldBy_of_mem_vals ho hmem)⟩
          exact (FunOkAt_default_equiv hsk₀ hsk').mp (hpaps st loc cap r args sk₀ t hst hoPap hps hargsFull)
  obtain ⟨hno, hfun⟩ := hFunOne hbase hinput hdp hsk
  refine ⟨hno, hfun, ?_⟩
  intro l o r fs w hr ho hcell hw
  have hheld : HeldBy st.heap v w := Or.inr ⟨l, o, hr, ho, by rw [hcell]; exact hw⟩
  exact hFunOne (hbase.sub hheld)
    (fun l' o' hr' ho' => hinput l' o' (Reach_of_HeldBy hheld hr') ho')
    (fun l' o' r' as' hr' ho' hc' => hdp l' o' r' as' (Reach_of_HeldBy hheld hr') ho' hc')
    rfl

/-! ## 3. `callExtern_sound` (`Eval.callExtern`) -/

theorem DataReach.toReach {h : Heap} {v : Val} {l : Nat} (hd : DataReach h v l) :
    Reach h v l := by
  induction hd with
  | here => exact .here
  | step ho hcell hmem _ ih =>
    exact .step ho (by rw [hcell]; exact hmem) ih

private theorem obj_state_eq {loc : Nat} {st st' : St} {o : Obj}
    (h : (obj loc).run st = .ok (o, st')) : st' = st := by
  unfold obj at h
  rw [M_bind_run] at h
  have hget : (get : M St).run st = .ok (st, st) := rfl
  rw [hget] at h; dsimp only at h
  cases hg : st.heap.objs[loc]? with
  | none => rw [hg] at h; cases h
  | some o₀ => rw [hg] at h; cases h; rfl

private theorem isLeaf_state_eq {v : Val} {st st' : St} {b : Bool}
    (h : (isLeaf v).run st = .ok (b, st')) : st' = st := by
  unfold isLeaf at h
  simp only [show (natClass != .leaf) = false from rfl, Bool.false_eq_true, ↓reduceIte] at h
  cases v with
  | imm _ => cases h; rfl
  | ref loc cap t =>
    rw [M_bind_run] at h
    cases ho : (obj loc).run st with
    | error e => rw [ho] at h; cases h
    | ok po =>
      have hst := obj_state_eq ho; subst hst
      rw [ho] at h; dsimp only at h
      cases hc : po.1.cell <;> rw [hc] at h <;> rw [M_pure_run] at h <;> cases h <;> rfl

theorem bindAt_many_val_ok {P : Prog} {fuel s : Nat} {v : Val} {st st' : St} {bnd : Bnd}
    (h : (bindAt P fuel s .many .val v).run st = .ok (bnd, st')) :
    bnd = ⟨v, .many⟩ ∧ st' = st := by
  unfold bindAt at h
  simp only [show (BinderMode.many == .erased) = false from rfl, Bool.false_eq_true, ↓reduceIte] at h
  unfold conform at h
  rw [M_bind_run, M_pure_run] at h; dsimp only at h
  simp only [BinderMode.isUnique, BinderMode.isBorrowed, BinderMode.usage,
    show (Usage.many == Usage.once) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
  rw [M_bind_run, M_pure_run] at h; dsimp only at h
  rw [M_bind_run] at h
  cases hl : (isLeaf v).run st with
  | error e => rw [hl] at h; cases h
  | ok pl =>
    have hst₁ := isLeaf_state_eq hl; subst hst₁
    rw [hl] at h; dsimp only at h
    rw [M_bind_run, M_pure_run] at h; dsimp only at h
    rw [M_bind_run, M_pure_run] at h; dsimp only at h
    cases h; exact ⟨rfl, rfl⟩

theorem bindParamsM_many_val_eq {P : Prog} {fuel s : Nat}
    {xs : List (Param × Val)} {env bs : List Bnd} {st st' : St}
    (hrun : (bindParamsM P fuel s xs env).run st = .ok (bs.reverse ++ env, st'))
    (hlen : bs.length = xs.length)
    {i : Nat} {p : Param} {v : Val} {bnd : Bnd}
    (hxs : xs[i]? = some (p, v)) (hbs : bs[i]? = some bnd)
    (hm : p.mode = .many) (hc : p.cls = .val) :
    bnd = ⟨v, .many⟩ := by
  induction xs generalizing env bs st i with
  | nil => simp at hxs
  | cons pv rest ih =>
    rcases pv with ⟨p₀, v₀⟩
    cases bs with
    | nil => simp at hlen
    | cons b₀ bsRest =>
      unfold bindParamsM at hrun
      rw [M_bind_run] at hrun
      cases hba : (bindAt P fuel s p₀.mode p₀.cls v₀).run st with
      | error e => rw [hba] at hrun; cases hrun
      | ok p₁ =>
        rcases p₁ with ⟨b₁, st₁⟩
        rw [hba] at hrun; dsimp only at hrun
        have hlenRest : bsRest.length = rest.length := by simpa using hlen
        have hrev : (b₀ :: bsRest).reverse ++ env = bsRest.reverse ++ (b₀ :: env) := by
          simp [List.reverse_cons, List.append_assoc]
        rw [hrev] at hrun
        have hrunLen : ∀ (ys : List (Param × Val)) (e₀ e₁ : List Bnd) (s₀ s₁ : St),
            (bindParamsM P fuel s ys e₀).run s₀ = .ok (e₁, s₁) →
            ∃ cs : List Bnd, cs.length = ys.length ∧ e₁ = cs.reverse ++ e₀ := by
          intro ys
          induction ys with
          | nil =>
            intro e₀ e₁ s₀ s₁ hr; unfold bindParamsM at hr; cases hr
            exact ⟨[], rfl, rfl⟩
          | cons q qs ihq =>
            intro e₀ e₁ s₀ s₁ hr
            unfold bindParamsM at hr; rw [M_bind_run] at hr
            cases hb' : (bindAt P fuel s q.1.mode q.1.cls q.2).run s₀ with
            | error e => rw [hb'] at hr; cases hr
            | ok pq =>
              rw [hb'] at hr; dsimp only at hr
              obtain ⟨cs, hcsLen, hcsEq⟩ := ihq (pq.1 :: e₀) e₁ pq.2 s₁ hr
              exact ⟨pq.1 :: cs, by simp [hcsLen], by simpa [List.reverse_cons, List.append_assoc] using hcsEq⟩
        obtain ⟨cs, hcsLen, hcsEq⟩ := hrunLen rest (b₁ :: env) (bsRest.reverse ++ (b₀ :: env)) st₁ st' hrun
        have hsplit : bsRest.reverse = cs.reverse ∧ b₀ :: env = b₁ :: env := by
          have hlenEq : bsRest.reverse.length = cs.reverse.length := by simp [hlenRest, hcsLen]
          exact List.append_inj hcsEq hlenEq
        have hb01 : b₀ = b₁ := (List.cons.inj hsplit.2).1
        subst hb01
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hxs hbs
          rcases hxs with ⟨rfl, rfl⟩
          subst hbs
          rw [hm, hc] at hba
          exact (bindAt_many_val_ok hba).1
        | succ k =>
          simp only [List.getElem?_cons_succ] at hxs hbs
          exact ih hrun hlenRest hxs hbs

theorem ret_val_sameLoc {P : Prog} {fuel s cur : Nat} {res : ResultMode} {v v' : Val} {st st' : St}
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v)
    (htree : res.isUnique = true → OwnTreeFull P st.heap v)
    (hnoOpen : res = .unique → OpenUnder st.regions [] v)
    (hrun : (ret P fuel s cur res .val v).run st = .ok (v', st')) :
    SameLoc v v' ∧ st'.heap.objs.size = st.heap.objs.size ∧
      (∀ w, HeldBy st'.heap v' w → w = v' ∨ ∃ w₀, HeldBy st.heap v w₀ ∧ ValSameShape w₀ w) := by
  unfold ret at hrun
  rw [M_bind_run] at hrun
  unfold conform at hrun
  rw [M_pure_run] at hrun; dsimp only at hrun
  cases res with
  | shared =>
    cases hconf : confinedTo s v with
    | true => simp [hconf] at hrun; cases hrun
    | false =>
      simp [hconf] at hrun
      cases hrun
      exact ⟨SameLoc.refl v, rfl, fun w hw => Or.inr ⟨w, hw, ValSameShape.refl w⟩⟩
  | borrowed =>
    cases hrun
    refine ⟨SameLoc.renameTaint_right s cur v, rfl, fun w hw => ?_⟩
    cases v with
    | imm i => exact Or.inr ⟨w, hw, ValSameShape.refl w⟩
    | ref loc cap t =>
      simp only [renameTaint] at hw ⊢
      cases hc : t.contains s <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      · exact Or.inr ⟨w, hw, ValSameShape.refl w⟩
      · rcases HeldBy_ref_taint (t2 := t) hw with rfl | hwOld
        · exact Or.inl rfl
        · exact Or.inr ⟨w, hwOld, ValSameShape.refl w⟩
  | unique =>
    cases hconf : confinedTo s v with
    | true => simp [hconf] at hrun; cases hrun
    | false =>
      simp only [hconf, Bool.false_eq_true, ↓reduceIte] at hrun
      rcases transfer_spec (fuel := fuel) (toBorrowed := false) hc hdl hacyc (htree rfl)
        (fun _ => hnoOpen rfl) with hOOF |
        ⟨v₂, st₂, htr, _, _, _, _, hsz₂, _, _, hh₂, hv₂, _, _⟩
      · rw [hOOF] at hrun; cases hrun
      · rw [htr] at hrun; cases hrun
        refine ⟨SameLoc.of_valSameShape hv₂, hsz₂, fun w hw => ?_⟩
        rcases hw with rfl | ⟨l, o₂, hr₂, ho₂, hm₂⟩
        · exact Or.inl rfl
        · have hr₁ : Reach st.heap v l := (Reach_iff_sameShape hh₂ hv₂ l).mpr hr₂
          obtain ⟨o₁, ho₁, hcs⟩ := hh₂.symm.getElem?_some ho₂
          obtain ⟨w₁, hm₁, hvsW⟩ := hcs.vals_fwd hm₂
          exact Or.inr ⟨w₁, Or.inr ⟨l, o₁, hr₁, ho₁, hm₁⟩, hvsW.symm⟩
  | uniqueBorrowed =>
    rw [M_bind_run] at hrun
    rcases transfer_spec (fuel := fuel) (toBorrowed := true) hc hdl hacyc (htree rfl)
      (fun h => by cases h) with hOOF |
      ⟨v₂, st₂, htr, _, _, _, _, hsz₂, _, _, hh₂, hv₂, _, _⟩
    · rw [hOOF] at hrun; cases hrun
    · rw [htr] at hrun; dsimp only at hrun; cases hrun
      refine ⟨(SameLoc.of_valSameShape hv₂).trans (SameLoc.renameTaint_right s cur v₂), hsz₂, fun w hw => ?_⟩
      have hfromV₂ : ∀ w', HeldBy st'.heap v₂ w' → w' = v₂ ∨ ∃ w₀, HeldBy st.heap v w₀ ∧ ValSameShape w₀ w' := by
        intro w' hw'
        rcases hw' with rfl | ⟨l, o₂, hr₂, ho₂, hm₂⟩
        · exact Or.inl rfl
        · have hr₁ : Reach st.heap v l := (Reach_iff_sameShape hh₂ hv₂ l).mpr hr₂
          obtain ⟨o₁, ho₁, hcs⟩ := hh₂.symm.getElem?_some ho₂
          obtain ⟨w₁, hm₁, hvsW⟩ := hcs.vals_fwd hm₂
          exact Or.inr ⟨w₁, Or.inr ⟨l, o₁, hr₁, ho₁, hm₁⟩, hvsW.symm⟩
      cases v₂ with
      | imm i =>
        rcases hfromV₂ w hw with hEq | hOld
        · exact Or.inl hEq
        · exact Or.inr hOld
      | ref loc cap t =>
        simp only [renameTaint] at hw ⊢
        cases hc : t.contains s <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hw ⊢
        · rcases hfromV₂ w hw with hEq | hOld
          · subst hEq
            exact Or.inr ⟨v, HeldBy.refl _ _, hv₂⟩
          · exact Or.inr hOld
        · rcases HeldBy_ref_taint (t2 := t) hw with rfl | hwOld
          · exact Or.inl rfl
          · rcases hfromV₂ w hwOld with hEq | hOld
            · subst hEq
              exact Or.inr ⟨v, HeldBy.refl _ _, hv₂⟩
            · exact Or.inr hOld

private theorem open_close_regions_eq {st : St} (hregs : RegsOk st) :
    (st.nextRegion :: st.regions).filter (· != st.nextRegion) = st.regions := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine List.filter_eq_self.mpr ?_
  intro r hr
  have hlt := (hregs.2.2 r hr).2
  simp [Nat.ne_of_lt hlt]

/-- Closure predicate for values reachable from an extern's returned value or fresh `.ctor` fields. -/
private def ExtVal (ps : Array Param) (bs : List Val) (h₁ h' : Heap) (w : Val) : Prop :=
  (∃ i, w = .imm i) ∨
  (∃ loc cap o, w = .ref loc cap [] ∧ h₁.objs.size ≤ loc ∧ h'.objs[loc]? = some o ∧ o.cap = cap) ∨
  (∃ loc cap o n, w = .ref loc cap [] ∧ h'.objs[loc]? = some o ∧ o.cap = cap ∧ o.cell = .num n) ∨
  (∃ (i : Nat) (p : Param) (a : Val), ps[i]? = some p ∧ bs[i]? = some a ∧ p.mode = .many ∧ HeldBy h' a w)

/-- Soundness and framing for `Eval.callExtern` under `ExternOk P ext` and `PapsFunOk P ext B`,
parameterized by `baseRegs` (empty for direct calls, `fRegs` for saturated PAP calls). -/
theorem callExtern_sound_base {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {r : Ref} {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel}
    {vs : List Val} {st : St} {Frame : Nat → Prop} {baseRegs argRegs : List Nat}
    (hext : ExternOk P ext)
    (hfind : P.find? r = some (.extern ps res rc rs))
    (hst : StOk P ext B st)
    (hpaps : PapsFunOk P ext B)
    (hFrameSS : ∀ l, StaticStrLoc st l → Frame l)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ∀ (i : Nat) (p : Param) (v : Val), ps[i]? = some p → vs[i]? = some v →
      (p.mode ≠ .erased →
        ValBaseOk st v ∧
        DeepOpenUnder st.heap st.regions argRegs v ∧
        (p.mode.usage ≠ .once → NoOnceCell st.heap v) ∧
        CtorFieldsOk P ext B st v ∧
        (p.mode.usage ≠ .once → FunOkAt P ext B st p.skel false (fun _ => False) v)) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap v ∧
        (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
        (p.mode.isBorrowed = false → OpenUnder st.regions [] v)) ∧
      (res = .unique → rc = .val → p.mode = .many → p.cls ≠ .leaf →
        DeepOpenUnder st.heap st.regions baseRegs v))
    (hdisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      ps[i]? = some pi → vs[i]? = some vi →
      ps[j]? = some pj → vs[j]? = some vj →
      pi.mode.isUnique = true → pj.mode ≠ .erased →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) :
    (∀ k, (callExtern P ext fuel r ps res rc vs).run st ≠ .error (.violation k)) ∧
    ∀ rv st', (callExtern P ext fuel r ps res rc vs).run st = .ok (rv, st') →
      StOk P ext B st' ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      st'.regions = st.regions ∧
      st.nextRegion ≤ st'.nextRegion ∧
      st'.statics = st.statics ∧
      st'.strs = st.strs ∧
      PreservesLocs Frame st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      ValBaseOk st' rv ∧
      ClsSafe st'.heap rc rv ∧
      DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc baseRegs argRegs) rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      FunOkAt P ext B st' rs false (fun _ => False) rv ∧
      (∀ l, Reach st'.heap rv l →
        st.heap.objs.size ≤ l ∨
        (∃ (i : Nat) (p : Param) (vi : Val), ps[i]? = some p ∧ vs[i]? = some vi ∧ p.mode = .many ∧ Reach st.heap vi l) ∨
        (∃ o n, st'.heap.objs[l]? = some o ∧ o.cell = .num n)) ∧
      (res.isUnique = true ∧ rc = .val →
        OwnTreeFull P st'.heap rv ∧
        ∀ l, OwnReach P st'.heap rv l → st.heap.objs.size ≤ l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l) := by
  let s := st.nextRegion
  let cur := st.regions.headD 0
  let st₀ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
  have hst₀ : StOk P ext B st₀ := StOk_openRegion hst
  have hrf₀ : RegsFuture st st₀ := RegsFuture.openRegion st
  have hopenRun : openRegion.run st = .ok ((s, cur), st₀) := rfl
  have hzipGet : ∀ (i : Nat) (p : Param) (v : Val),
      (ps.toList.zip vs)[i]? = some (p, v) → ps[i]? = some p ∧ vs[i]? = some v := by
    intro i p v hi
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hi
    rw [List.length_zip] at hlt
    have hlt1 : i < ps.size := by have := Nat.lt_of_lt_of_le hlt (Nat.min_le_left _ _); simpa using this
    have hlt2 : i < vs.length := Nat.lt_of_lt_of_le hlt (Nat.min_le_right _ _)
    rw [List.getElem_zip] at heq
    simp only [Prod.mk.injEq] at heq
    exact ⟨by rw [Array.getElem?_eq_getElem hlt1, ← heq.1]; simp,
           by rw [List.getElem?_eq_getElem hlt2, ← heq.2]⟩
  have hxsBind : ∀ (i : Nat) (p : Param) (v : Val), (ps.toList.zip vs)[i]? = some (p, v) →
      (p.mode ≠ .erased → DeepLive st₀.heap v ∧ AcyclicFrom st₀.heap v) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st₀.heap v ∧ (p.mode.isBorrowed = false → OpenUnder st₀.regions [] v)) := by
    intro i p v hi
    obtain ⟨hp, hv⟩ := hzipGet i p v hi
    obtain ⟨hne, hu, _⟩ := hargs i p v hp hv
    refine ⟨fun hner => ⟨(hne hner).1.1, (hne hner).1.2.1⟩, fun hui => ?_⟩
    obtain ⟨htr, _, hop⟩ := hu hui
    refine ⟨htr, fun hnb r' hr' hopen => ?_⟩
    have hner : p.mode ≠ .erased := by intro h; rw [h] at hui; cases hui
    have hlt : r' < s := (hne hner).1.2.2.2 v (HeldBy.refl _ _) r' hr'
    rcases List.mem_cons.mp hopen with rfl | hrOld
    · exact absurd hlt (Nat.lt_irrefl _)
    · exact hop hnb r' hr' hrOld
  have hdisjBind : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      (ps.toList.zip vs)[i]? = some (pi, vi) → (ps.toList.zip vs)[j]? = some (pj, vj) →
      pi.mode.isUnique = true → pj.mode ≠ .erased →
      ∀ l, OwnReach P st₀.heap vi l → ¬ Reach st₀.heap vj l := by
    intro i j pi pj vi vj hne hi hj hui hnerj
    obtain ⟨hpi, hvi⟩ := hzipGet i pi vi hi
    obtain ⟨hpj, hvj⟩ := hzipGet j pj vj hj
    exact hdisj i j pi pj vi vj hne hpi hvi hpj hvj hui hnerj
  have hcallUnfold : (callExtern P ext fuel r ps res rc vs).run st =
      ((bindParamsM P fuel s (ps.toList.zip vs) []) >>= fun env' =>
        let bs := env'.reverse.map (·.val)
        fun st₁ =>
          match ext r bs st₁.heap with
          | none => .error .stuck
          | some (h', v) =>
            ((ret P fuel s cur res rc v) >>= fun v' =>
             (closeRegion s) >>= fun _ => pure v').run { st₁ with heap := h' }).run st₀ := by
    unfold callExtern
    rw [M_bind_run, hopenRun]; dsimp only
    rw [M_bind_run]
    have hfor := forIn_list_bindAtVals_eq_bindParamsM P fuel s (ps.toList.zip vs) [] [] st₀ rfl
    erw [hfor]
    rw [M_bind_run, M_bind_run]
    cases (bindParamsM P fuel s (ps.toList.zip vs) []).run st₀ with
    | error e => rfl
    | ok p₁ =>
      dsimp only
      rw [M_pure_run]; dsimp only
      rw [M_bind_run]
      have hget : (get : M St).run p₁.2 = .ok (p₁.2, p₁.2) := rfl
      rw [hget]; dsimp only [StateT.run]
      cases ext r (List.map (fun x => x.val) p₁.1.reverse) p₁.2.heap with
      | none => rfl
      | some hv => rfl
  rcases bindParamsM_spec (P := P) (fuel := fuel) (s := s) (xs := ps.toList.zip vs) (env := [])
      hst₀.1 hxsBind hdisjBind with hStuck1 | hOOF1 |
    ⟨bsBnd, st₁, hbindRun, hbsLen, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hc₁, _hoss₁,
      hpres₁, hspec₁, hdisj₁⟩
  · -- `bindParamsM` stuck
    rw [hcallUnfold, M_bind_run, hStuck1]
    exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
  · -- `bindParamsM` outOfFuel
    rw [hcallUnfold, M_bind_run, hOOF1]
    exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
  · -- `bindParamsM` succeeded with `(bsBnd.reverse, st₁)`
    dsimp only [st₀] at hsz₁ hnr₁ hcap₁ hr₁
    let bs : List Val := bsBnd.map (·.val)
    have hbsEq : bsBnd.reverse.reverse.map (·.val) = bs := by simp [bs]
    have hcallStep1 : (callExtern P ext fuel r ps res rc vs).run st =
        (match ext r bs st₁.heap with
         | none => .error .stuck
         | some (h', v) =>
           ((ret P fuel s cur res rc v) >>= fun v' =>
            (closeRegion s) >>= fun _ => pure v').run { st₁ with heap := h' }) := by
      rw [hcallUnfold, M_bind_run]
      have hbindRun' : (bindParamsM P fuel s (ps.toList.zip vs) []).run st₀ = .ok (bsBnd.reverse, st₁) := by
        simpa using hbindRun
      rw [hbindRun']; dsimp only; rw [hbsEq]; rfl
    cases hextRun : ext r bs st₁.heap with
    | none =>
      rw [hcallStep1, hextRun]
      exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
    | some hv =>
      rcases hv with ⟨h', v⟩
      rw [hcallStep1, hextRun]; dsimp only
      -- Extract `ExternOk` properties on `(h', v)`.
      obtain ⟨hsz12, hcap12, hold12, hfresh12, hretVal, hrcIrr, hrcImm, hrcLeaf, hresUniq⟩ :=
        hext r ps res rc rs bs st₁.heap h' v hfind hextRun
      let st₂ : St := { st₁ with heap := h' }
      -- Helper: indexing into `bs` and `bsBnd` from `ps` and `bs`.
      have hbsGet : ∀ (i : Nat) (a : Val), bs[i]? = some a →
          ∃ p vi bnd, ps[i]? = some p ∧ vs[i]? = some vi ∧
            (ps.toList.zip vs)[i]? = some (p, vi) ∧ bsBnd[i]? = some bnd ∧ bnd.val = a := by
        intro i a ha
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp ha
        have hltB : i < bsBnd.length := by simpa [bs] using hlt
        have hltZ : i < (ps.toList.zip vs).length := hbsLen ▸ hltB
        rcases hzip : (ps.toList.zip vs)[i] with ⟨p, vi⟩
        have hzi : (ps.toList.zip vs)[i]? = some (p, vi) := by
          rw [List.getElem?_eq_getElem hltZ, hzip]
        obtain ⟨hp, hv⟩ := hzipGet i p vi hzi
        refine ⟨p, vi, bsBnd[i], hp, hv, hzi, List.getElem?_eq_getElem hltB, ?_⟩
        simpa [bs] using heq
      -- `PreservesLocs Frame st.heap st₁.heap` and `StOk P ext B st₁`
      have hpresFrame01 : PreservesLocs Frame st.heap st₁.heap := by
        intro l hFl
        refine hpres₁ l ⟨hFrameLt l hFl, fun i p vi hzi hu hor => ?_⟩
        obtain ⟨hp, hv⟩ := hzipGet i p vi hzi
        exact (hargs i p vi hp hv).2.1 hu |>.2.1 l hor hFl
      have hpresSS01 : PreservesLocs (StaticStrLoc st) st.heap st₁.heap :=
        hpresFrame01.mono hFrameSS
      have hst₁Ok : StOk P ext B st₁ := by
        have hregs₁ : RegsOk st₁ := by
          obtain ⟨hpos, hnd, hlt⟩ := hst₀.2.1
          dsimp only [st₀] at hpos hnd hlt
          exact ⟨by omega, by rw [hr₁]; exact hnd, fun x hx => by
            have := hlt x (by rwa [← hr₁]); exact ⟨this.1, by omega⟩⟩
        exact StOk_preserve hst₀ hc₁ hregs₁ (RegsFuture.same_regions (by dsimp [st₀]; omega) (by dsimp [st₀]; exact hr₁)) hst₁ hstr₁ hpresSS01
      -- `PreservesOnceShell st.heap st₁.heap`
      have honce01 : PreservesOnceShell st.heap st₁.heap := by
        refine PreservesOnceShell.of_preservesLocs ?_
        intro l ⟨o, tgt, sp, ho, hcell⟩
        have hlt : l < st.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
        refine hpres₁ l ⟨hlt, fun i p vi hzi hu hor => ?_⟩
        obtain ⟨hp, hv⟩ := hzipGet i p vi hzi
        have hner : p.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
        have hnoOnce : p.mode.usage ≠ .once := by cases hm : p.mode <;> simp [hm, BinderMode.isUnique, BinderMode.usage] at hu ⊢
        exact (hargs i p vi hp hv).1 hner |>.2.2.1 hnoOnce l o (OwnReach_toReach hor) ho tgt sp hcell
      -- Every `p.mode = .many` bound arg `a` in `bs` has full invariants in `st₁`.
      have hmanySt₁ : ∀ (i : Nat) (p : Param) (a : Val), ps[i]? = some p → bs[i]? = some a →
          p.mode = .many →
          ∃ vi, vs[i]? = some vi ∧
            ValBaseOk st₁ a ∧
            DeepTaintsBounded st₁.heap s a ∧
            DeepOpenUnder st₁.heap st₁.regions argRegs a ∧
            (res = .unique → rc = .val → DeepOpenUnder st₁.heap st₁.regions baseRegs a) ∧
            NoOnceCell st₁.heap a ∧
            CtorFieldsOk P ext B st₁ a ∧
            FunOkAt P ext B st₁ p.skel false (fun _ => False) a ∧
            (∀ l, Reach st₁.heap a l → st.heap.objs.size ≤ l ∨ Reach st.heap vi l) := by
        intro i p a hp ha hm
        obtain ⟨p', vi, bnd, hp', hvi, hzi, hbnd, hba⟩ := hbsGet i a ha
        rw [hp] at hp'; cases hp'
        subst hba
        have hsp := hspec₁ i p vi bnd hzi hbnd
        obtain ⟨_, hdlB, hacycB, _, _, hclsB, _, _, _, hdouB, hreachB, _⟩ := hsp
        have hner : p.mode ≠ .erased := by rw [hm]; decide
        have hnoOnce : p.mode.usage ≠ .once := by rw [hm]; decide
        have hargI := (hargs i p vi hp hvi).1 hner
        refine ⟨vi, hvi, ?_⟩
        by_cases hval : p.cls = .val
        · -- `p.mode = .many ∧ p.cls = .val`: `bnd = ⟨vi, .many⟩` and `Reach st.heap vi` preserved!
          have hbndEq : bnd = ⟨vi, .many⟩ :=
            bindParamsM_many_val_eq hbindRun hbsLen hzi hbnd hm hval
          have hvalEq : bnd.val = vi := congrArg Bnd.val hbndEq
          have hpresVi : PreservesLocs (Reach st.heap vi) st.heap st₁.heap := by
            intro l hrl
            have hlt : l < st.heap.objs.size := Reach_lt_size hargI.1.1 hrl
            refine hpres₁ l ⟨hlt, fun j pj vj hzj huj horj => ?_⟩
            obtain ⟨hpj, hvj⟩ := hzipGet j pj vj hzj
            have hneji : j ≠ i := by
              intro heq; subst heq; rw [hp] at hpj; cases hpj
              rw [hm] at huj; simp [BinderMode.isUnique] at huj
            exact hdisj j i pj p vj vi hneji hpj hvj hp hvi huj hner l horj hrl
          rw [hvalEq]
          have hrf01 : RegsFuture st st₁ :=
            hrf₀.trans (RegsFuture.same_regions (by dsimp [st₀]; omega) hr₁)
          refine ⟨ValBaseOk_congr hpresVi (by omega) hargI.1,
            DeepTaintsBounded_congr hpresVi hargI.1.2.2.2,
            (DeepOpenUnder_congr hpresVi).mpr (DeepOpenUnder_of_regsFuture hargI.1.2.2.2 hargI.2.1 hrf01),
            fun hru hrc => (DeepOpenUnder_congr hpresVi).mpr
              (DeepOpenUnder_of_regsFuture hargI.1.2.2.2
                ((hargs i p vi hp hvi).2.2 hru hrc hm (by rw [hval]; decide)) hrf01),
            NoOnceCell_congr hargI.1.1 hpresVi (hargI.2.2.1 hnoOnce),
            CtorFieldsOk_congr hargI.1.1 hpresVi hrf01 hargI.2.2.2.1,
            FunOkAt_preserve_locs hpresVi hrf01 (hargI.2.2.2.2 hnoOnce),
            fun l hl => Or.inr ((Reach_congr hpresVi l).mp hl)⟩
        · -- `p.cls ≠ .val`: `ClsOk st₁.heap p.cls bnd.val` gives imm or `.num` cell!
          have hclsSafe : ClsSafe st₁.heap p.cls bnd.val := ClsSafe.of_clsOk (hclsB hner hnoOnce)
          have htb : DeepTaintsBounded st₁.heap s bnd.val := by
            intro w hw r' hr'
            have hdou := ClsSafe_deepOpenUnder_nil (rs := [r']) (A := []) hval hclsSafe
            exact False.elim (List.not_mem_nil (hdou w hw r' hr' List.mem_cons_self))
          refine ⟨⟨hdlB, hacycB, fun w hw => (hdlB w hw).2, htb.mono (by rw [hnr₁]; exact Nat.le_succ _)⟩,
            htb,
            ClsSafe_deepOpenUnder_nil hval hclsSafe,
            fun _ _ => (ClsSafe_deepOpenUnder_nil (A := []) hval hclsSafe).mono (fun _ h => by cases h),
            ClsSafe_noOnceCell hval hclsSafe,
            ClsSafe_ctorFieldsOk P ext B st₁ hval hclsSafe,
            ClsSafe_funOkAt P ext B st₁ p.skel hval hclsSafe,
            fun l hl => (hreachB l hl).imp id (fun h => h.2)⟩
      -- `CapsOk h'`
      have hc₂ : CapsOk h' := by
        intro l o' ho'
        by_cases hlt : l < st₁.heap.objs.size
        · obtain ⟨o₁, ho₁⟩ : ∃ o₁, st₁.heap.objs[l]? = some o₁ :=
            ⟨st₁.heap.objs[l], Array.getElem?_eq_getElem hlt⟩
          obtain ⟨o₂, ho₂, hor⟩ := hold12 l o₁ ho₁
          rw [ho'] at ho₂; cases ho₂
          rcases hor with ⟨_, hcapEq⟩ | ⟨_, hltCap, _⟩
          · rw [hcapEq]; exact Nat.lt_of_lt_of_le (hc₁ l o₁ ho₁) hcap12
          · exact hltCap
        · exact (hfresh12 l o' (Nat.le_of_not_lt hlt) ho').2.1
      -- Locations `< st₁.heap.objs.size` outside unique bound args' `OwnReach` are preserved in `h'`.
      have hpresExt : PreservesLocs
          (fun l => l < st₁.heap.objs.size ∧
            ∀ (i : Nat) (p : Param) (a : Val), ps[i]? = some p → bs[i]? = some a → p.mode.isUnique = true →
              ¬ OwnReach P st₁.heap a l)
          st₁.heap h' := by
        intro l ⟨hlt, hno⟩
        have ho₁ : st₁.heap.objs[l]? = some st₁.heap.objs[l] := Array.getElem?_eq_getElem hlt
        obtain ⟨o', ho', hor⟩ := hold12 l st₁.heap.objs[l] ho₁
        rcases hor with ⟨hcellEq, hcapEq⟩ | ⟨_, _, i, p, a, hp, ha, hu, hor⟩
        · have heq : o' = st₁.heap.objs[l] := by
            cases o'; exact congr (congrArg Obj.mk hcellEq) hcapEq
          rw [ho', ho₁, heq]
        · exact False.elim (hno i p a hp ha hu hor)
      -- `PreservesLocs Frame st₁.heap h'` and `StOk P ext B st₂`
      have hpresFrame12 : PreservesLocs Frame st₁.heap h' := by
        intro l hFl
        have hlt0 : l < st.heap.objs.size := hFrameLt l hFl
        refine hpresExt l ⟨Nat.lt_of_lt_of_le hlt0 hsz₁, fun i p a hp ha hu hor => ?_⟩
        obtain ⟨p', vi, bnd, hp', hvi, hzi, hbnd, hba⟩ := hbsGet i a ha
        rw [hp] at hp'; cases hp'; subst hba
        rcases (hspec₁ i p vi bnd hzi hbnd).2.2.2.2.2.2.2.2.2.2.2 l hor with hge | ⟨_, hor0⟩
        · dsimp only [st₀] at hge; omega
        · exact ((hargs i p vi hp hvi).2.1 hu).2.1 l hor0 hFl
      have hpresSS12 : PreservesLocs (StaticStrLoc st₁) st₁.heap h' := by
        intro l hl
        apply hpresFrame12 l
        apply hFrameSS l
        rcases hl with ⟨r', v', hm, hr⟩ | ⟨s', v', hm, hr⟩
        · rw [hst₁] at hm
          exact Or.inl ⟨r', v', hm, (Reach_congr (hpresSS01.mono fun x hx => Or.inl ⟨r', v', hm, hx⟩) l).mp hr⟩
        · rw [hstr₁] at hm
          exact Or.inr ⟨s', v', hm, (Reach_congr (hpresSS01.mono fun x hx => Or.inr ⟨s', v', hm, hx⟩) l).mp hr⟩
      have hst₂Ok : StOk P ext B st₂ :=
        StOk_preserve hst₁Ok hc₂ hst₁Ok.2.1 (RegsFuture.refl st₁) rfl rfl hpresSS12
      -- `PreservesOnceShell st₁.heap h'` (for `.once` cells from `st`, hence `PreservesOnceShell st.heap h'`)
      have honce02 : PreservesOnceShell st.heap h' := by
        intro l o tgt sp ho hcell
        have hlt0 : l < st.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
        have ho₁ : st₁.heap.objs[l]? = some o := by
          have := hpres₁ l ⟨hlt0, fun i p vi hzi hu hor => ?_⟩
          · exact this.trans ho
          · obtain ⟨hp, hv⟩ := hzipGet i p vi hzi
            have hner : p.mode ≠ .erased := by intro h; rw [h] at hu; cases hu
            have hnoOnce : p.mode.usage ≠ .once := by cases hm : p.mode <;> simp [hm, BinderMode.isUnique, BinderMode.usage] at hu ⊢
            exact (hargs i p vi hp hv).1 hner |>.2.2.1 hnoOnce l o (OwnReach_toReach hor) ho tgt sp hcell
        have ho₂ : h'.objs[l]? = some o := by
          refine (hpresExt l ⟨Nat.lt_of_lt_of_le hlt0 hsz₁, fun i p a hp ha hu hor => ?_⟩).trans ho₁
          obtain ⟨p', vi, bnd, hp', hvi, hzi, hbnd, hba⟩ := hbsGet i a ha
          rw [hp] at hp'; cases hp'; subst hba
          rcases (hspec₁ i p vi bnd hzi hbnd).2.2.2.2.2.2.2.2.2.2.2 l hor with hge | ⟨hner, hor0⟩
          · dsimp only [st₀] at hge; omega
          · have hnoOnce : p.mode.usage ≠ .once := by cases hm : p.mode <;> simp [hm, BinderMode.isUnique, BinderMode.usage] at hu ⊢
            exact (hargs i p vi hp hvi).1 hner |>.2.2.1 hnoOnce l o (OwnReach_toReach hor0) ho tgt sp hcell
        exact ⟨o, tgt, sp, ho₂, rfl, hcell⟩
      -- Every `p.mode = .many` bound arg `a` has its entire `Reach` preserved in `h'`!
      have hpresMany : ∀ (i : Nat) (p : Param) (a : Val), ps[i]? = some p → bs[i]? = some a →
          p.mode = .many → PreservesLocs (Reach st₁.heap a) st₁.heap h' := by
        intro i p a hp ha hm l hrl
        obtain ⟨vi, _, hbaseA, _⟩ := hmanySt₁ i p a hp ha hm
        have hlt1 : l < st₁.heap.objs.size := Reach_lt_size hbaseA.1 hrl
        refine hpresExt l ⟨hlt1, fun j pj aj hpj haj huj horj => ?_⟩
        obtain ⟨p', vi', bi, hp', _, hzi, hbi, hbai⟩ := hbsGet i a ha
        rw [hp] at hp'; cases hp'; subst hbai
        obtain ⟨pj', vj', bj, hpj', _, hzj, hbj, hbaj⟩ := hbsGet j aj haj
        rw [hpj] at hpj'; cases hpj'; subst hbaj
        have hneji : j ≠ i := by
          intro heq; subst heq; rw [hp] at hpj; cases hpj
          rw [hm] at huj; simp [BinderMode.isUnique] at huj
        have hneri : p.mode ≠ .erased := by rw [hm]; decide
        exact hdisj₁ j i pj p vj' vi' bj bi hneji hzj hzi hbj hbi huj hneri l horj hrl
      have hmanySt₂ : ∀ (i : Nat) (p : Param) (a : Val), ps[i]? = some p → bs[i]? = some a →
          p.mode = .many →
          ∃ vi, vs[i]? = some vi ∧
            ValBaseOk st₂ a ∧
            DeepTaintsBounded h' s a ∧
            DeepOpenUnder h' st₂.regions argRegs a ∧
            (res = .unique → rc = .val → DeepOpenUnder h' st₂.regions baseRegs a) ∧
            NoOnceCell h' a ∧
            CtorFieldsOk P ext B st₂ a ∧
            FunOkAt P ext B st₂ p.skel false (fun _ => False) a ∧
            (∀ l, Reach h' a l → st.heap.objs.size ≤ l ∨ Reach st.heap vi l) := by
        intro i p a hp ha hm
        obtain ⟨vi, hvi, hbase, htb, hopen, hopenU, hno, hcf, hfun, hreach⟩ := hmanySt₁ i p a hp ha hm
        have hpA := hpresMany i p a hp ha hm
        exact ⟨vi, hvi,
          ValBaseOk_congr hpA (Nat.le_refl _) hbase,
          DeepTaintsBounded_congr hpA htb,
          (DeepOpenUnder_congr hpA).mpr hopen,
          fun hru hrc => (DeepOpenUnder_congr hpA).mpr (hopenU hru hrc),
          NoOnceCell_congr hbase.1 hpA hno,
          CtorFieldsOk_congr hbase.1 hpA (RegsFuture.refl st₁) hcf,
          FunOkAt_preserve_locs hpA (RegsFuture.refl st₁) hfun,
          fun l hl => hreach l ((Reach_congr hpA l).mp hl)⟩
      -- `DataFieldOf st₁.heap a w` gives `HeldBy h' a w` for `p.mode = .many` arg `a`!
      have hdataFieldHeld : ∀ (i : Nat) (p : Param) (a w : Val),
          ps[i]? = some p → bs[i]? = some a → p.mode = .many →
          DataFieldOf st₁.heap a w → HeldBy h' a w ∧ CtorFieldsOk P ext B st₂ w ∧
            NoOnceCell h' w ∧ FunOkAt P ext B st₂ .unknown false (fun _ => False) w := by
        intro i p a w hp ha hm ⟨l, o, rc', fs, hdr, ho, hcell, hmem⟩
        have hr1 : Reach st₁.heap a l := DataReach.toReach hdr
        have hpA := hpresMany i p a hp ha hm
        have hr2 : Reach h' a l := (Reach_congr hpA l).mpr hr1
        have ho2 : h'.objs[l]? = some o := (hpA l hr1).trans ho
        have hheld : HeldBy h' a w := Or.inr ⟨l, o, hr2, ho2, by rw [hcell]; exact hmem⟩
        obtain ⟨_, _, _, _, _, _, _, hcfA, _, _⟩ := hmanySt₂ i p a hp ha hm
        obtain ⟨hnoW, hfunW⟩ := hcfA l o rc' fs w hr2 ho2 hcell hmem
        exact ⟨hheld, CtorFieldsOk.sub hcfA hheld, hnoW, hfunW⟩
      -- `ExternFieldVal` implies `ExtVal`.
      have hExtField_to_ExtVal : ∀ {w : Val}, ExternFieldVal P ps bs st₁.heap h' w →
          ExtVal ps bs st₁.heap h' w := by
        intro w hw
        rcases hw with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, hge, ho, hcap, _⟩ |
          ⟨i, p, a, hp, ha, hm, ⟨rfl, _⟩ | hdf⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr (Or.inl ⟨loc, cap, o, rfl, hge, ho, hcap⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨i, p, w, hp, ha, hm, HeldBy.refl _ _⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨i, p, a, hp, ha, hm, (hdataFieldHeld i p a w hp ha hm hdf).1⟩))
      -- `ExternRetVal` implies `ExtVal`.
      have hExtRet_to_ExtVal : ∀ {w : Val}, ExternRetVal P ps bs rs st₁.heap h' w →
          ExtVal ps bs st₁.heap h' w := by
        intro w hw
        rcases hw with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, hge, ho, hcap, _⟩ |
          ⟨i, p, a, hp, ha, hm, ⟨rfl, _⟩ | ⟨hdf, _⟩⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr (Or.inl ⟨loc, cap, o, rfl, hge, ho, hcap⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨i, p, w, hp, ha, hm, HeldBy.refl _ _⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨i, p, a, hp, ha, hm, (hdataFieldHeld i p a w hp ha hm hdf).1⟩))
      -- Closure of `ExtVal` under `Reach h'` (simultaneous reach classification + `HeldBy` closure).
      have hExtVal_reach : ∀ {u : Val} {l : Nat}, ExtVal ps bs st₁.heap h' u → Reach h' u l →
          (st₁.heap.objs.size ≤ l ∧ ∃ o, h'.objs[l]? = some o) ∨
          (∃ o n, h'.objs[l]? = some o ∧ o.cell = .num n) ∨
          (∃ (i : Nat) (p : Param) (a : Val), ps[i]? = some p ∧ bs[i]? = some a ∧ p.mode = .many ∧ Reach h' a l) := by
        intro u l hu hr
        induction hr with
        | @here loc cap t =>
          rcases hu with ⟨_, h⟩ | ⟨loc', cap', o, heq, hge, ho, _⟩ |
            ⟨loc', cap', o, n, heq, ho, _, hnum⟩ | ⟨i, p, a, hp, ha, hm, hheld⟩
          · cases h
          · cases heq; exact Or.inl ⟨hge, o, ho⟩
          · cases heq; exact Or.inr (Or.inl ⟨o, n, ho, hnum⟩)
          · exact Or.inr (Or.inr ⟨i, p, a, hp, ha, hm, Reach_of_HeldBy hheld .here⟩)
        | @step loc cap t o w l' ho hmem _ ih =>
          rcases hu with ⟨_, h⟩ | ⟨loc', cap', o', heq, hge, ho', _⟩ |
            ⟨loc', cap', o', n, heq, ho', _, hnum⟩ | ⟨i, p, a, hp, ha, hm, hheld⟩
          · cases h
          · cases heq
            rw [ho] at ho'; cases ho'
            obtain ⟨hin, _, hbody⟩ := hfresh12 loc o hge ho
            cases hcell : o.cell with
            | num _ | str _ => rw [hcell] at hmem; cases hmem
            | clo _ _ _ _ _ _ | once _ _ => rw [hcell] at hin; cases hin
            | ctor r_c fs =>
              rw [hcell] at hmem hbody
              exact ih (hExtField_to_ExtVal (hbody w hmem).1)
            | pap r_p as_p =>
              rw [hcell] at hmem hbody
              obtain ⟨hpa, hvok, _⟩ := hbody w hmem
              apply ih
              rcases hpa with ⟨i', rfl⟩ | ⟨loc₂, cap₂, o₂, n₂, rfl, ho₂, hnum₂⟩
              · exact Or.inl ⟨i', rfl⟩
              · obtain ⟨_, o₂', ho₂', hcap₂'⟩ := hvok
                rw [ho₂] at ho₂'; cases ho₂'
                exact Or.inr (Or.inr (Or.inl ⟨loc₂, cap₂, o₂, n₂, rfl, ho₂, hcap₂', hnum₂⟩))
          · cases heq
            rw [ho] at ho'; cases ho'; rw [hnum] at hmem; cases hmem
          · exact ih (Or.inr (Or.inr (Or.inr ⟨i, p, a, hp, ha, hm,
              hheld.trans (HeldBy_of_mem_vals ho hmem)⟩)))
      have hExtVal_held : ∀ {u w : Val}, ExtVal ps bs st₁.heap h' u → HeldBy h' u w →
          ExtVal ps bs st₁.heap h' w := by
        intro u w hu hw
        rcases hw with rfl | ⟨l, o, hr, ho, hmem⟩
        · exact hu
        · rcases hExtVal_reach hu hr with ⟨hge, o', ho'⟩ | ⟨o', n, ho', hnum⟩ |
            ⟨i, p, a, hp, ha, hm, hra⟩
          · obtain ⟨hin, _, hbody⟩ := hfresh12 l o hge ho
            cases hcell : o.cell with
            | num _ | str _ => rw [hcell] at hmem; cases hmem
            | clo _ _ _ _ _ _ | once _ _ => rw [hcell] at hin; cases hin
            | ctor r_c fs =>
              rw [hcell] at hmem hbody
              exact hExtField_to_ExtVal (hbody w hmem).1
            | pap r_p as_p =>
              rw [hcell] at hmem hbody
              obtain ⟨hpa, hvok, _⟩ := hbody w hmem
              rcases hpa with ⟨i', rfl⟩ | ⟨loc₂, cap₂, o₂, n₂, rfl, ho₂, hnum₂⟩
              · exact Or.inl ⟨i', rfl⟩
              · obtain ⟨_, o₂', ho₂', hcap₂'⟩ := hvok
                rw [ho₂] at ho₂'; cases ho₂'
                exact Or.inr (Or.inr (Or.inl ⟨loc₂, cap₂, o₂, n₂, rfl, ho₂, hcap₂', hnum₂⟩))
          · rw [ho] at ho'; cases ho'; rw [hnum] at hmem; cases hmem
          · exact Or.inr (Or.inr (Or.inr ⟨i, p, a, hp, ha, hm, Or.inr ⟨l, o, hra, ho, hmem⟩⟩))
      -- Every `ExtVal` satisfies `ValBaseOk st₂`, `DeepTaintsBounded h' s`, `DeepOpenUnder`, `NoOnceCell`!
      have hExtVal_props : ∀ {u : Val}, ExtVal ps bs st₁.heap h' u →
          ValBaseOk st₂ u ∧ DeepTaintsBounded h' s u ∧
          DeepOpenUnder h' st₂.regions argRegs u ∧
          (res = .unique → rc = .val → DeepOpenUnder h' st₂.regions baseRegs u) ∧
          NoOnceCell h' u := by
        intro u hu
        have hdlU : DeepLive h' u := by
          intro w hw
          rcases hExtVal_held hu hw with ⟨i, rfl⟩ | ⟨loc, cap, o, rfl, _, ho, hcap⟩ |
            ⟨loc, cap, o, n, rfl, ho, hcap, _⟩ | ⟨i, p, a, hp, ha, hm, hwa⟩
          · exact ⟨trivial, trivial⟩
          · exact ⟨⟨o, ho, hcap⟩, fun _ _ _ _ => rfl⟩
          · exact ⟨⟨o, ho, hcap⟩, fun _ _ _ _ => rfl⟩
          · obtain ⟨_, _, hbaseA, _⟩ := hmanySt₂ i p a hp ha hm
            exact hbaseA.1 w hwa
        have hacycU : AcyclicFrom h' u := by
          intro l o w hr ho hmem hwl
          rcases hExtVal_reach hu hr with ⟨hge, _⟩ | ⟨o', n, ho', hnum⟩ |
            ⟨i, p, a, hp, ha, hm, hra⟩
          · obtain ⟨hin, _, hbody⟩ := hfresh12 l o hge ho
            cases hcell : o.cell with
            | num _ | str _ => rw [hcell] at hmem; cases hmem
            | clo _ _ _ _ _ _ | once _ _ => rw [hcell] at hin; cases hin
            | ctor r_c fs =>
              rw [hcell] at hmem hbody
              exact (hbody w hmem).2 hwl
            | pap r_p as_p =>
              rw [hcell] at hmem hbody
              exact (hbody w hmem).2.2 hwl
          · rw [ho] at ho'; cases ho'; rw [hnum] at hmem; cases hmem
          · obtain ⟨_, _, hbaseA, _⟩ := hmanySt₂ i p a hp ha hm
            exact hbaseA.2.1 l o w hra ho hmem hwl
        have htbU : DeepTaintsBounded h' s u := by
          intro w hw r' hr'
          rcases hExtVal_held hu hw with ⟨_, rfl⟩ | ⟨_, _, _, rfl, _⟩ |
            ⟨_, _, _, _, rfl, _⟩ | ⟨i, p, a, hp, ha, hm, hwa⟩
          · cases hr'
          · cases hr'
          · cases hr'
          · obtain ⟨_, _, _, htbA, _⟩ := hmanySt₂ i p a hp ha hm
            exact htbA w hwa r' hr'
        have hopenU : DeepOpenUnder h' st₂.regions argRegs u := by
          intro w hw r' hr' hopen
          rcases hExtVal_held hu hw with ⟨_, rfl⟩ | ⟨_, _, _, rfl, _⟩ |
            ⟨_, _, _, _, rfl, _⟩ | ⟨i, p, a, hp, ha, hm, hwa⟩
          · cases hr'
          · cases hr'
          · cases hr'
          · obtain ⟨_, _, _, _, hopenA, _⟩ := hmanySt₂ i p a hp ha hm
            exact hopenA w hwa r' hr' hopen
        have hopenUniq : res = .unique → rc = .val → DeepOpenUnder h' st₂.regions baseRegs u := by
          intro hru hrc w hw r' hr' hopen
          rcases hExtVal_held hu hw with ⟨_, rfl⟩ | ⟨_, _, _, rfl, _⟩ |
            ⟨_, _, _, _, rfl, _⟩ | ⟨i, p, a, hp, ha, hm, hwa⟩
          · cases hr'
          · cases hr'
          · cases hr'
          · obtain ⟨_, _, _, _, _, hopenUA, _⟩ := hmanySt₂ i p a hp ha hm
            exact hopenUA hru hrc w hwa r' hr' hopen
        have hnoU : NoOnceCell h' u := by
          intro l o hr ho t sp hcell
          rcases hExtVal_reach hu hr with ⟨hge, _⟩ | ⟨o', n, ho', hnum⟩ |
            ⟨i, p, a, hp, ha, hm, hra⟩
          · have hin := (hfresh12 l o hge ho).1
            rw [hcell] at hin; exact hin
          · rw [ho] at ho'; cases ho'; rw [hnum] at hcell; cases hcell
          · obtain ⟨_, _, _, _, _, _, hnoA, _⟩ := hmanySt₂ i p a hp ha hm
            exact hnoA l o hra ho t sp hcell
        exact ⟨⟨hdlU, hacycU, fun w hw => (hdlU w hw).2, htbU.mono (by dsimp [st₂]; omega)⟩,
          htbU, hopenU, hopenUniq, hnoU⟩
      -- Helper: `FunOkAt` for any fresh cell in `h'` with a known `.pap` skeleton property.
      have hFreshFun : ∀ {loc cap : Nat} {o : Obj} {sk : Skel},
          st₁.heap.objs.size ≤ loc → h'.objs[loc]? = some o → o.cap = cap →
          (∀ r_p as_p, o.cell = .pap r_p as_p →
            ∃ sk₀, papSkel P r_p as_p.size = some sk₀ ∧ sk.admits sk₀ = true) →
          FunOkAt P ext B st₂ sk false (fun _ => False) (.ref loc cap []) := by
        intro loc cap o sk hge ho hcap hpapSk
        obtain ⟨hin, _, hbody⟩ := hfresh12 loc o hge ho
        cases hcell : o.cell with
        | ctor _ _ => exact FunOkAt_nonCallable_ref P ext B st₂ sk ho (by rw [hcell]; trivial)
        | num _ => exact FunOkAt_nonCallable_ref P ext B st₂ sk ho (by rw [hcell]; trivial)
        | str _ => exact FunOkAt_nonCallable_ref P ext B st₂ sk ho (by rw [hcell]; trivial)
        | clo _ _ _ _ _ _ | once _ _ => rw [hcell] at hin; cases hin
        | pap r_p as_p =>
          rw [hcell] at hbody
          obtain ⟨sk₀, hps₀, hadm₀⟩ := hpapSk r_p as_p hcell
          have hoPap : st₂.heap.objs[loc]? = some ⟨.pap r_p as_p, cap⟩ := by
            cases o with
            | mk cell cap₀ =>
              dsimp only at hcell hcap
              subst hcell; subst hcap; exact ho
          have hargsFull : ∀ a ∈ as_p.toList, PapArgOk h' a ∧ ValBaseOk st₂ a := by
            intro a ha
            obtain ⟨hpa, hvok, _⟩ := hbody a ha
            have haExt : ExtVal ps bs st₁.heap h' a := by
              rcases hpa with ⟨i', rfl⟩ | ⟨loc₂, cap₂, o₂, n₂, rfl, ho₂, hnum₂⟩
              · exact Or.inl ⟨i', rfl⟩
              · obtain ⟨_, o₂', ho₂', hcap₂'⟩ := hvok
                rw [ho₂] at ho₂'; cases ho₂'
                exact Or.inr (Or.inr (Or.inl ⟨loc₂, cap₂, o₂, n₂, rfl, ho₂, hcap₂', hnum₂⟩))
            exact ⟨hpa, (hExtVal_props haExt).1⟩
          have hadm' : sk₀.admits sk = true := by rwa [Skel.admits_symm]
          exact FunOkAt_of_admits hadm' (hpaps st₂ loc cap r_p as_p sk₀ [] hst₂Ok hoPap hps₀ hargsFull)
      -- Establish `ValBaseOk`, `DeepTaintsBounded`, `DeepOpenUnder`, `NoOnceCell`, `CtorFieldsOk`, `FunOkAt` for `v` in `st₂`.
      have hvExt : ExtVal ps bs st₁.heap h' v := hExtRet_to_ExtVal hretVal
      obtain ⟨hvBase, hvTaints, hvOpen, hvOpenUniq, hvNoOnce⟩ := hExtVal_props hvExt
      have hvCtorFields : CtorFieldsOk P ext B st₂ v := by
        intro l o rc' fs w hr ho hcell hw
        rcases hExtVal_reach hvExt hr with ⟨hge, _⟩ | ⟨o', n, ho', hnum⟩ |
          ⟨i, p, a, hp, ha, hm, hra⟩
        · obtain ⟨_, _, hbody⟩ := hfresh12 l o hge ho
          rw [hcell] at hbody
          have hfv := (hbody w hw).1
          refine ⟨(hExtVal_props (hExtField_to_ExtVal hfv)).2.2.2.2, ?_⟩
          rcases hfv with ⟨i', rfl⟩ | ⟨loc', cap', o', rfl, hge', ho', hcap', hpap'⟩ |
            ⟨i, p, a, hp, ha, hm, ⟨rfl, hdef⟩ | hdf⟩
          · cases i' with
            | irr => exact FunOkAt_imm_irr P ext B st₂ .unknown
            | con _ => exact FunOkAt_nonCallable_imm P ext B st₂ .unknown (by intro h; cases h)
            | bits _ => exact FunOkAt_nonCallable_imm P ext B st₂ .unknown (by intro h; cases h)
          · exact hFreshFun hge' ho' hcap' (fun r_p as_p hcp => by
              obtain ⟨sk₀, hps₀, hdef₀⟩ := hpap' r_p as_p hcp
              exact ⟨sk₀, hps₀, by simpa [Skel.admits] using hdef₀⟩)
          · obtain ⟨_, _, _, _, _, _, _, _, hfunA, _⟩ := hmanySt₂ i p w hp ha hm
            exact (FunOkAt_default_equiv hdef rfl).mp hfunA
          · exact (hdataFieldHeld i p a w hp ha hm hdf).2.2.2
        · rw [ho] at ho'; cases ho'; rw [hnum] at hcell; cases hcell
        · obtain ⟨_, _, _, _, _, _, _, hcfA, _, _⟩ := hmanySt₂ i p a hp ha hm
          exact hcfA l o rc' fs w hra ho hcell hw
      have hvFun : FunOkAt P ext B st₂ rs false (fun _ => False) v := by
        rcases hretVal with ⟨i', rfl⟩ | ⟨loc', cap', o', rfl, hge', ho', hcap', hpap'⟩ |
          ⟨i, p, a, hp, ha, hm, ⟨rfl, hadm⟩ | ⟨hdf, hdef⟩⟩
        · cases i' with
          | irr => exact FunOkAt_imm_irr P ext B st₂ rs
          | con _ => exact FunOkAt_nonCallable_imm P ext B st₂ rs (by intro h; cases h)
          | bits _ => exact FunOkAt_nonCallable_imm P ext B st₂ rs (by intro h; cases h)
        · exact hFreshFun hge' ho' hcap' hpap'
        · obtain ⟨_, _, _, _, _, _, _, _, hfunA, _⟩ := hmanySt₂ i p v hp ha hm
          have hadm' : p.skel.admits rs = true := by rwa [Skel.admits_symm]
          exact FunOkAt_of_admits hadm' hfunA
        · exact (FunOkAt_default_equiv rfl hdef).mp (hdataFieldHeld i p a v hp ha hm hdf).2.2.2
      -- Step 4: `ret P fuel s cur res rc v`
      have htreeV : res.isUnique = true → OwnTreeFull P st₂.heap v := by
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
      have hnoS : (res = .shared ∨ res = .unique) → OpenUnder [s] [] v := by
        intro _ r' hr' hopen
        simp only [List.mem_singleton] at hopen
        subst hopen
        exact absurd (hvTaints v (HeldBy.refl _ _) s hr') (Nat.lt_irrefl _)
      have hnoOpen : res = .unique → OpenUnder st₂.regions [] v := by
        intro hru r' hr' _
        have hnil : v.taint = [] := by
          cases hrc : rc with
          | irr => rw [hrcIrr hrc]; rfl
          | imm => obtain ⟨_, hi'⟩ := hrcImm hrc; rw [hi']; rfl
          | leaf => obtain ⟨_, _, _, _, hvEq, _⟩ := hrcLeaf hrc; rw [hvEq]; rfl
          | val =>
            have hru' : res.isUnique = true := by rw [hru]; rfl
            obtain ⟨_, _, hvEq, _⟩ := hresUniq hru' hrc
            rw [hvEq]; rfl
        rw [hnil] at hr'; cases hr'
      rcases ret_spec (P := P) (fuel := fuel) (s := s) (cur := cur) (r := res) (c := rc) (v := v)
          hc₂ hvBase.1 hvBase.2.1 htreeV hnoS hnoOpen with hStuck2 | hOOF2 |
        ⟨rv, st₃, hretRun, hr₃, hnr₃, hst₃, hstr₃, hsz₃, hcap₃, hc₃, hoss₃, hpres₃,
          hcls₃, hdl₃, hacyc₃, htree₃, htSU₃, htB₃, hdouSU₃, _, hdouClose₃, hreach₃, hown₃⟩
      · rw [M_bind_run, hStuck2]
        exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
      · rw [M_bind_run, hOOF2]
        exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
      · -- Step 5: `closeRegion s`
        let st' : St := { st₃ with regions := st₃.regions.filter (· != s) }
        have hfinRun : ((ret P fuel s cur res rc v) >>= fun v' =>
            (closeRegion s) >>= fun _ => pure v').run st₂ = .ok (rv, st') := by
          rw [M_bind_run, hretRun]; dsimp only
          rw [M_bind_run]; rfl
        rw [hfinRun]
        refine ⟨(fun _ h => by cases h), fun rv' st'' hok => ?_⟩
        cases hok
        -- Regions restored cleanly to `st.regions`!
        have hregEnd : st'.regions = st.regions := by
          dsimp only [st']
          rw [hr₃]; dsimp only [st₂]; rw [hr₁]
          exact open_close_regions_eq hst.2.1
        -- `ret` preserves every location `< st₁.heap.objs.size`!
        have hpresRetOld : PreservesLocs (fun l => l < st₁.heap.objs.size) st₂.heap st₃.heap := by
          intro l hlt1
          refine hpres₃ l ⟨Nat.lt_of_lt_of_le hlt1 hsz12, fun hru hor => ?_⟩
          cases hrc : rc with
          | irr =>
            rw [hrcIrr hrc] at hor; exact OwnReach_imm_false P _ _ l hor
          | imm =>
            obtain ⟨_, hi'⟩ := hrcImm hrc; rw [hi'] at hor; exact OwnReach_imm_false P _ _ l hor
          | leaf =>
            obtain ⟨_, _, o', n', hvEq, ho', hnum'⟩ := hrcLeaf hrc
            rw [hvEq] at hor; exact OwnReach_num_false ho' hnum' l hor
          | val =>
            obtain ⟨_, _, _, _, _, hownFresh⟩ := hresUniq hru hrc
            have hge := (hownFresh l hor).1
            omega
        have hpresFrame23 : PreservesLocs Frame st₂.heap st'.heap :=
          hpresRetOld.mono fun l hFl => Nat.lt_of_lt_of_le (hFrameLt l hFl) hsz₁
        have hpresFrameAll : PreservesLocs Frame st.heap st'.heap :=
          (hpresFrame01.trans hpresFrame12).trans hpresFrame23
        have hpresSS23 : PreservesLocs (StaticStrLoc st₂) st₂.heap st₃.heap := by
          intro l hl
          apply hpresFrame23 l
          apply hFrameSS l
          have h1 : StaticStrLoc st₁ l := by
            rcases hl with ⟨r', v', hm, hr⟩ | ⟨s', v', hm, hr⟩
            · exact Or.inl ⟨r', v', hm, (Reach_congr (hpresSS12.mono fun x hx => Or.inl ⟨r', v', hm, hx⟩) l).mp hr⟩
            · exact Or.inr ⟨s', v', hm, (Reach_congr (hpresSS12.mono fun x hx => Or.inr ⟨s', v', hm, hx⟩) l).mp hr⟩
          rcases h1 with ⟨r', v', hm, hr⟩ | ⟨s', v', hm, hr⟩
          · rw [hst₁] at hm
            exact Or.inl ⟨r', v', hm, (Reach_congr (hpresSS01.mono fun x hx => Or.inl ⟨r', v', hm, hx⟩) l).mp hr⟩
          · rw [hstr₁] at hm
            exact Or.inr ⟨s', v', hm, (Reach_congr (hpresSS01.mono fun x hx => Or.inr ⟨s', v', hm, hx⟩) l).mp hr⟩
        have hst₃Ok : StOk P ext B st₃ :=
          StOk_preserve hst₂Ok hc₃ (by
            obtain ⟨hpos, hnd, hlt⟩ := hst₂Ok.2.1
            exact ⟨by omega, by rw [hr₃]; exact hnd, fun x hx => by
              have := hlt x (by rwa [← hr₃]); exact ⟨this.1, by omega⟩⟩)
            (RegsFuture.same_regions (by omega) hr₃) hst₃ hstr₃ hpresSS23
        have hst'Ok : StOk P ext B st' := StOk_closeRegion s hst₃Ok
        have hstatEq : st'.statics = st.statics := hst₃.trans hst₁
        have hstrEq : st'.strs = st.strs := hstr₃.trans hstr₁
        have honceAll : PreservesOnceShell st.heap st'.heap := by
          intro l o tgt sp ho hcell
          obtain ⟨o₂, tgt₂, sp₂, ho₂, hcap₂, hcell₂⟩ := honce02 l o tgt sp ho hcell
          have hlt1 : l < st₁.heap.objs.size := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp ho).1 hsz₁
          exact ⟨o₂, tgt₂, sp₂, (hpresRetOld l hlt1).trans ho₂, hcap₂, hcell₂⟩
        have hssBack : ∀ l, StaticStrLoc st' l → StaticStrLoc st l := by
          intro l hl
          have hpSSAll : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
            hpresFrameAll.mono hFrameSS
          rcases hl with ⟨r', v', hm, hr⟩ | ⟨s', v', hm, hr⟩
          · rw [hstatEq] at hm
            exact Or.inl ⟨r', v', hm, (Reach_congr (hpSSAll.mono fun x hx => Or.inl ⟨r', v', hm, hx⟩) l).mp hr⟩
          · rw [hstrEq] at hm
            exact Or.inr ⟨s', v', hm, (Reach_congr (hpSSAll.mono fun x hx => Or.inr ⟨s', v', hm, hx⟩) l).mp hr⟩
        -- `ValBaseOk st' rv`, `NoOnceCell`, `CtorFieldsOk`, `FunOkAt`
        have hrvProps : ValBaseOk st' rv ∧ NoOnceCell st'.heap rv ∧
            CtorFieldsOk P ext B st' rv ∧ FunOkAt P ext B st' rs false (fun _ => False) rv := by
          by_cases hrcVal : rc = .val
          · subst hrcVal
            obtain ⟨hlocV, _, hheldV⟩ := ret_val_sameLoc hc₂ hvBase.1 hvBase.2.1 htreeV hnoOpen hretRun
            have hshV : SameShapeOn (Reach st₂.heap v) st₂.heap st'.heap :=
              fun l o₁ _ ho₁ => hoss₃.2 l o₁ ho₁
            have hrf2' : RegsFuture st₂ st' := by
              refine ⟨by dsimp [st']; omega, fun r' hr' => ?_⟩
              rw [hregEnd] at hr'
              left; dsimp [st₂]; rw [hr₁]; exact List.mem_cons_of_mem s hr'
            have htbRv : DeepTaintsBounded st'.heap st'.nextRegion rv := by
              intro w hw r' hr'
              rcases hheldV w hw with rfl | ⟨w₀, hw₀, hvsW⟩
              · have hltS : r' < s := by
                  cases hres' : res with
                  | shared | unique =>
                    have hmem := htSU₃ (by rw [hres']; simp) r' hr'
                    exact hvTaints v (HeldBy.refl _ _) r' hmem
                  | borrowed | uniqueBorrowed =>
                    rcases htB₃ (by rw [hres']; rfl) r' hr' with ⟨hmv, _⟩ | ⟨rfl, hne0, _⟩
                    · exact hvTaints v (HeldBy.refl _ _) r' hmv
                    · cases hregsL : st.regions with
                      | nil => simp [cur, hregsL] at hne0
                      | cons c₀ _ =>
                        have hcEq : cur = c₀ := by simp [cur, hregsL]
                        rw [hcEq]
                        exact (hst.2.1.2.2 c₀ (by rw [hregsL]; exact List.mem_cons_self)).2
                have : st'.nextRegion = s + 1 := by dsimp [st']; rw [hnr₃]; dsimp [st₂]; rw [hnr₁]
                omega
              · rw [← hvsW.taint_eq] at hr'
                have hltS := hvTaints w₀ hw₀ r' hr'
                have : st'.nextRegion = s + 1 := by dsimp [st']; rw [hnr₃]; dsimp [st₂]; rw [hnr₁]
                omega
            exact ⟨⟨hdl₃, hacyc₃, fun w hw => (hdl₃ w hw).2, htbRv⟩,
              NoOnceCell_of_sameShape hvBase.1 hshV hlocV hvNoOnce,
              CtorFieldsOk_of_sameShape hvBase.1 hshV hlocV hrf2' hvCtorFields,
              FunOkAt_preserve_sameShape hlocV hshV hrf2' hvFun⟩
          · have hcs : ClsSafe st'.heap rc rv := ClsSafe.of_clsOk hcls₃
            have htbRv : DeepTaintsBounded st'.heap st'.nextRegion rv := by
              intro w hw r' hr'
              exact False.elim (List.not_mem_nil (ClsSafe_deepOpenUnder_nil (rs := [r']) (A := [])
                hrcVal hcs w hw r' hr' List.mem_cons_self))
            exact ⟨⟨hdl₃, hacyc₃, fun w hw => (hdl₃ w hw).2, htbRv⟩,
              ClsSafe_noOnceCell hrcVal hcs,
              ClsSafe_ctorFieldsOk P ext B st' hrcVal hcs,
              ClsSafe_funOkAt P ext B st' rs hrcVal hcs⟩
        -- `DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc baseRegs argRegs) rv`
        have hrvOpen : DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc baseRegs argRegs) rv := by
          by_cases hrcVal : rc = .val
          · subst hrcVal
            have hvalNe : (Cls.val != Cls.val) = false := rfl
            cases hres' : res with
            | unique =>
              have hdou := hdouSU₃ st₂.regions baseRegs (Or.inr hres') (hvOpenUniq hres' rfl)
              have hsub : ∀ r' ∈ st'.regions, r' ∈ st₂.regions := by
                intro r' hr'; rw [hregEnd] at hr'; dsimp [st₂]; rw [hr₁]; exact List.mem_cons_of_mem s hr'
              simpa [applyResultRegs, hvalNe, hres'] using hdou.weaken_open hsub
            | shared =>
              have hdou := hdouSU₃ st₂.regions (argRegs ++ baseRegs) (Or.inl hres')
                (hvOpen.mono fun _ hx => List.mem_append_left _ hx)
              have hsub : ∀ r' ∈ st'.regions, r' ∈ st₂.regions := by
                intro r' hr'; rw [hregEnd] at hr'; dsimp [st₂]; rw [hr₁]; exact List.mem_cons_of_mem s hr'
              simpa [applyResultRegs, hvalNe, hres'] using hdou.weaken_open hsub
            | borrowed =>
              have hcur : cur = 0 ∨ cur ∈ applyResultRegs st .borrowed .val baseRegs argRegs := by
                cases hregsL : st.regions with
                | nil => left; simp [cur, hregsL]
                | cons c₀ _ =>
                  right; simp [cur, applyResultRegs, hvalNe, hregsL]
              have hdouS : DeepOpenUnder st₂.heap st₂.regions
                  (s :: applyResultRegs st .borrowed .val baseRegs argRegs) v := by
                refine hvOpen.mono fun x hx => List.mem_cons_of_mem s ?_
                cases hregsL : st.regions <;> simp [applyResultRegs, hvalNe, hregsL, hx]
              have hclosed := hdouClose₃ st₂.regions (applyResultRegs st .borrowed .val baseRegs argRegs) hcur hdouS
              have hfiltEq : st₂.regions.filter (· != s) = st'.regions := by
                rw [hregEnd]; dsimp [st₂]; rw [hr₁]; exact open_close_regions_eq hst.2.1
              simpa [hfiltEq, hres'] using hclosed
            | uniqueBorrowed =>
              have hcur : cur = 0 ∨ cur ∈ applyResultRegs st .uniqueBorrowed .val baseRegs argRegs := by
                cases hregsL : st.regions with
                | nil => left; simp [cur, hregsL]
                | cons c₀ _ =>
                  right; simp [cur, applyResultRegs, hvalNe, hregsL]
              have hdouS : DeepOpenUnder st₂.heap st₂.regions
                  (s :: applyResultRegs st .uniqueBorrowed .val baseRegs argRegs) v := by
                refine hvOpen.mono fun x hx => List.mem_cons_of_mem s ?_
                cases hregsL : st.regions <;> simp [applyResultRegs, hvalNe, hregsL, hx]
              have hclosed := hdouClose₃ st₂.regions (applyResultRegs st .uniqueBorrowed .val baseRegs argRegs) hcur hdouS
              have hfiltEq : st₂.regions.filter (· != s) = st'.regions := by
                rw [hregEnd]; dsimp [st₂]; rw [hr₁]; exact open_close_regions_eq hst.2.1
              simpa [hfiltEq, hres'] using hclosed
          · have hcs : ClsSafe st'.heap rc rv := ClsSafe.of_clsOk hcls₃
            exact ClsSafe_deepOpenUnder_nil hrcVal hcs
        refine ⟨hst'Ok,
          Nat.le_trans hsz₁ (Nat.le_trans hsz12 hsz₃),
          Nat.le_trans hcap₁ (Nat.le_trans hcap12 hcap₃),
          hregEnd,
          (by dsimp [st']; rw [hnr₃]; dsimp [st₂]; rw [hnr₁]; exact Nat.le_succ _),
          hstatEq, hstrEq,
          hpresFrameAll, honceAll,
          fun l hl => Or.inr (Or.inl (hssBack l hl)),
          hrvProps.1, ClsSafe.of_clsOk hcls₃, hrvOpen,
          hrvProps.2.1, hrvProps.2.2.1, hrvProps.2.2.2, ?_, ?_⟩
        · -- `Reach` bound
          intro l hrl
          rcases hreach₃ l hrl with hge2 | hrv2
          · exact Or.inl (Nat.le_trans hsz₁ (Nat.le_trans hsz12 hge2))
          · rcases hExtVal_reach hvExt hrv2 with ⟨hge1, _⟩ | ⟨o₂, n, ho₂, hnum₂⟩ |
              ⟨i, p, a, hp, ha, hm, hra⟩
            · exact Or.inl (Nat.le_trans hsz₁ hge1)
            · obtain ⟨o', ho', hcs⟩ := hoss₃.2 l o₂ ho₂
              rw [hnum₂] at hcs
              cases hc' : o'.cell <;> rw [hc'] at hcs <;> try cases hcs
              exact Or.inr (Or.inr ⟨o', n, ho', hc'⟩)
            · obtain ⟨vi, hvi, _, _, _, _, _, _, _, hreachA⟩ := hmanySt₂ i p a hp ha hm
              rcases hreachA l hra with hge0 | hrvi
              · exact Or.inl hge0
              · exact Or.inr (Or.inl ⟨i, p, vi, hp, hvi, hm, hrvi⟩)
        · -- Unique result ownership + freshness
          rintro ⟨hru, hrc⟩
          refine ⟨htree₃ hru, fun l hor => ?_⟩
          have hor2 : OwnReach P st₂.heap v l := hown₃ l hor
          obtain ⟨_, _, _, _, _, hownFresh⟩ := hresUniq hru hrc
          have hge1 : st₁.heap.objs.size ≤ l := (hownFresh l hor2).1
          have hge0 : st.heap.objs.size ≤ l := Nat.le_trans hsz₁ hge1
          refine ⟨hge0, fun hFl => absurd (hFrameLt l hFl) (Nat.not_lt.mpr hge0),
            fun hss => absurd (hFrameLt l (hFrameSS l (hssBack l hss))) (Nat.not_lt.mpr hge0)⟩

/-- Direct-call specialization of `callExtern_sound_base` with `baseRegs = []`. -/
theorem callExtern_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {r : Ref} {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel}
    {vs : List Val} {st : St} {Frame : Nat → Prop} {argRegs : List Nat}
    (hext : ExternOk P ext)
    (hfind : P.find? r = some (.extern ps res rc rs))
    (hst : StOk P ext B st)
    (hpaps : PapsFunOk P ext B)
    (hFrameSS : ∀ l, StaticStrLoc st l → Frame l)
    (hFrameLt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ∀ (i : Nat) (p : Param) (v : Val), ps[i]? = some p → vs[i]? = some v →
      (p.mode ≠ .erased →
        ValBaseOk st v ∧
        DeepOpenUnder st.heap st.regions argRegs v ∧
        NoOnceCell st.heap v ∧
        CtorFieldsOk P ext B st v ∧
        FunOkAt P ext B st p.skel false (fun _ => False) v) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap v ∧
        (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
        (p.mode.isBorrowed = false → OpenUnder st.regions [] v)) ∧
      (res = .unique → rc = .val → p.mode = .many → p.cls ≠ .leaf →
        DeepOpenUnder st.heap st.regions [] v))
    (hdisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      ps[i]? = some pi → vs[i]? = some vi →
      ps[j]? = some pj → vs[j]? = some vj →
      pi.mode.isUnique = true → pj.mode ≠ .erased →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) :
    (∀ k, (callExtern P ext fuel r ps res rc vs).run st ≠ .error (.violation k)) ∧
    ∀ rv st', (callExtern P ext fuel r ps res rc vs).run st = .ok (rv, st') →
      StOk P ext B st' ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      st'.regions = st.regions ∧
      st.nextRegion ≤ st'.nextRegion ∧
      st'.statics = st.statics ∧
      st'.strs = st.strs ∧
      PreservesLocs Frame st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      ValBaseOk st' rv ∧
      ClsSafe st'.heap rc rv ∧
      DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc [] argRegs) rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      FunOkAt P ext B st' rs false (fun _ => False) rv ∧
      (∀ l, Reach st'.heap rv l →
        st.heap.objs.size ≤ l ∨
        (∃ (i : Nat) (p : Param) (vi : Val), ps[i]? = some p ∧ vs[i]? = some vi ∧ p.mode = .many ∧ Reach st.heap vi l) ∨
        (∃ o n, st'.heap.objs[l]? = some o ∧ o.cell = .num n)) ∧
      (res.isUnique = true ∧ rc = .val →
        OwnTreeFull P st'.heap rv ∧
        ∀ l, OwnReach P st'.heap rv l → st.heap.objs.size ≤ l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l) :=
  callExtern_sound_base (baseRegs := []) hext hfind hst hpaps hFrameSS hFrameLt
    (fun i p v hp hv =>
      let h := hargs i p v hp hv
      ⟨fun hne => let h1 := h.1 hne; ⟨h1.1, h1.2.1, fun _ => h1.2.2.1, h1.2.2.2.1, fun _ => h1.2.2.2.2⟩,
       h.2.1, h.2.2⟩) hdisj

/-! ## 4. `InputsOk_to_StOk_and_Args` (`Statement.InputsOk`) -/

theorem HeapOk_valOk_props {P : Prog} {h : Heap} {v : Val}
    (hh : HeapOk P h) (hv : ValOk h v) :
    (∀ w, HeldBy h v w → ValOk h w) ∧
    ValBaseOk { heap := h } v ∧
    DeepOpenUnder h [] [] v ∧
    NoOnceCell h v ∧
    (∀ l o, Reach h v l → h.objs[l]? = some o → InputCell P o.cell) := by
  have hReachValOk : ∀ {u : Val} {l : Nat} {o : Obj},
      ValOk h u → Reach h u l → h.objs[l]? = some o →
      InputCell P o.cell ∧ ∀ w ∈ o.cell.vals, ValOk h w ∧ ¬ Reach h w l := by
    intro u l o _ _ ho
    obtain ⟨hin, _, hvals⟩ := hh l o ho
    exact ⟨hin, hvals⟩
  have hHeldValOk : ∀ w, HeldBy h v w → ValOk h w := by
    intro w hw
    rcases hw with rfl | ⟨l, o, hr, ho, hmem⟩
    · exact hv
    · exact ((hReachValOk hv hr ho).2 w hmem).1
  have hdl : DeepLive h v := by
    intro w hw
    have hvw := hHeldValOk w hw
    cases w with
    | imm _ => exact ⟨trivial, trivial⟩
    | ref loc cap t =>
      obtain ⟨rfl, o, ho, hcap⟩ := hvw
      exact ⟨⟨o, ho, hcap⟩, fun _ _ _ _ => rfl⟩
  have hacyc : AcyclicFrom h v := by
    intro l o w hr ho hmem hwl
    exact ((hReachValOk hv hr ho).2 w hmem).2 hwl
  have htb : DeepTaintsBounded h 1 v := by
    intro w hw r hr
    have hvw := hHeldValOk w hw
    cases w with
    | imm _ => cases hr
    | ref _ _ t => obtain ⟨rfl, _⟩ := hvw; cases hr
  have hopen : DeepOpenUnder h [] [] v :=
    fun _ _ _ _ hmem => by cases hmem
  have hno : NoOnceCell h v := by
    intro l o hr ho t sp hcell
    have hin := (hReachValOk hv hr ho).1
    rw [hcell] at hin; exact hin
  exact ⟨hHeldValOk, ⟨hdl, hacyc, fun w hw => (hdl w hw).2, htb⟩,
    hopen, hno, fun l o hr ho => (hReachValOk hv hr ho).1⟩

/-- Translates `Statement.InputsOk P h params args` (plus `PapsFunOk P ext B`) into the initial
`StOk P ext B { heap := h }` state and all per-argument invariants required to enter a seed body. -/
theorem InputsOk_to_StOk_and_Args {P : Prog} {ext : ExternOracle} {B : Nat}
    {h : Heap} {params : Array Param} {args : List Val}
    (hinp : InputsOk P h params args)
    (hpaps : PapsFunOk P ext B) :
    let st : St := { heap := h }
    StOk P ext B st ∧
    args.length = params.size ∧
    (∀ (i : Nat) (p : Param) (a : Val), params[i]? = some p → args[i]? = some a →
      ValBaseOk st a ∧
      DeepOpenUnder st.heap st.regions [] a ∧
      NoOnceCell st.heap a ∧
      (p.mode = .erased → a = .imm .irr) ∧
      (p.mode ≠ .erased →
        ClsSafe st.heap p.cls a ∧
        CtorFieldsOk P ext B st a ∧
        FunOkAt P ext B st p.skel false (fun _ => False) a) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st.heap a ∧
        ∀ (j : Nat) (b : Val) (l : Nat), j ≠ i → args[j]? = some b →
          OwnReach P st.heap a l → ¬ Reach st.heap b l)) := by
  obtain ⟨hlen, hheap, hargOk, huniqOk⟩ := hinp
  let st : St := { heap := h }
  have hstOk : StOk P ext B st :=
    ⟨fun l o ho => (hheap l o ho).2.1, RegsOk_init h, by simp [st], by simp [st]⟩
  refine ⟨hstOk, hlen, fun i p a hp ha => ?_⟩
  obtain ⟨hvalOk, her, hner⟩ := hargOk i p a hp ha
  obtain ⟨_, hbase, hopen, hno, hinput⟩ := HeapOk_valOk_props hheap hvalOk
  refine ⟨hbase, hopen, hno, her, fun hne => ?_, fun hu => huniqOk i p a hp ha hu⟩
  obtain ⟨hirr, himm, hleaf, hskBody⟩ := hner hne
  have hcls : ClsSafe h p.cls a := by
    cases hc : p.cls with
    | irr => rw [hirr hc]; exact ClsSafe.irr h .irr
    | imm => obtain ⟨imm, rfl⟩ := himm hc; exact ClsSafe.of_clsOk ⟨imm, rfl⟩
    | leaf =>
      obtain ⟨loc, cap, o, n, rfl, ho, hnum⟩ := hleaf hc
      obtain ⟨_, o', ho', hcap'⟩ := hvalOk
      rw [ho] at ho'; cases ho'
      exact ClsSafe.of_clsOk ⟨loc, cap, o, n, rfl, ho, hnum, hcap'⟩
    | val => exact ClsSafe.of_clsOk trivial
  have hcfFun : CtorFieldsOk P ext B st a ∧ FunOkAt P ext B st p.skel false (fun _ => False) a := by
    cases hsk : p.skel with
    | arrow m d r c =>
      rw [hsk] at hskBody
      obtain ⟨hfun, _, hcf⟩ := ClosureAt_to_FunOkAt hstOk hpaps hbase hskBody
      exact ⟨hcf, hfun⟩
    | data =>
      rw [hsk] at hskBody
      obtain ⟨_, hfun, hcf⟩ := DefaultPaps_to_FunOkAt_and_CtorFieldsOk (sk := .data)
        hstOk hpaps hbase hinput hskBody rfl
      exact ⟨hcf, hfun⟩
    | unknown =>
      rw [hsk] at hskBody
      obtain ⟨_, hfun, hcf⟩ := DefaultPaps_to_FunOkAt_and_CtorFieldsOk (sk := .unknown)
        hstOk hpaps hbase hinput hskBody rfl
      exact ⟨hcf, hfun⟩
    | dataApp f g =>
      rw [hsk] at hskBody
      obtain ⟨_, hfun, hcf⟩ := DefaultPaps_to_FunOkAt_and_CtorFieldsOk (sk := .unknown)
        hstOk hpaps hbase hinput hskBody rfl
      exact ⟨hcf, (FunOkAt_nonArrow_eq_unknown (sk := .dataApp f g) rfl).mpr hfun⟩
  exact ⟨hcls, hcfFun.1, hcfFun.2⟩

end IxCK.Resource.Proof
