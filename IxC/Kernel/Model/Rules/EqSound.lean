module

public import IxC.Kernel.Model.Rules.Inputs
import IxC.Kernel.Model.Rules.Reads
import IxC.Kernel.Model.Rules.IotaSoundKit
import IxC.Kernel.Model.Rules.InferSoundKit
import IxC.Kernel.Model.Rules.DefEqSoundKit
import IxC.Kernel.Semantics.Frame
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.Annot.BitInst
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Model.Annot.BitClosed
import IxC.Kernel.Semantics.DenoteClosed
import IxC.Kernel.Semantics.Kit
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Leaves

public section

/-!
# Equality reflection is sound

`Red.eqProof` rewrites a constant application `a` to `b` given a proof of
`@Eq.{u} T a b`. In the model `Eq` denotes equality (`eq_law`): the proof's
reading is a member of `eqv ⟦a⟧ ⟦b⟧`, so `⟦a⟧ = ⟦b⟧`. The typings of `a` and `b`
at `T` and of `T` at `u` supply the law's three domain memberships; the proof's
inferred type supplies `b`'s frame and reading. No new model input: `eq_law` is
an `EnvModelM` field.
-/

namespace Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key ConstantInfo)
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {m : EnvModel V env}
  {φ : LevelParam → Nat}

/-- An application's reading is the application of its parts' readings. -/
theorem denoteMeta_app_inv {acval : Key md → (LevelParam → Nat) → AnnotTerm} {d : Nat}
    {f x : Expr md} {r : AnnotTerm} (h : denoteMeta acval env φ d (.app f x) = some r) :
    ∃ fr xr, denoteMeta acval env φ d f = some fr ∧ denoteMeta acval env φ d x = some xr ∧
      r = .app fr xr := by
  rw [denoteMeta_app] at h
  cases hf : denoteMeta acval env φ d f with
  | none => simp [hf] at h
  | some fr =>
    cases hx : denoteMeta acval env φ d x with
    | none => simp [hf, hx] at h
    | some xr =>
      simp [hf, hx] at h
      exact ⟨fr, xr, rfl, rfl, h.symm⟩

/-- An application's frame gives its parts'. -/
theorem frame_app_split {d : Nat} {f x : Expr md} (h : Frame d (.app f x)) :
    Frame d f ∧ Frame d x := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩,
    ⟨hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩⟩

/-- **`Red.eqProof` is sound.** -/
theorem Red.eqProof_sound (hin : RulesInputs V m φ) {d : Nat} {a b p T ta tb sT : Expr md}
    {u v : Level} {ci : ConstantInfo md}
    (hfE : env.find? eqName = some ci)
    (hp : Infer env .full d p (.app (.app (.app (.const eqName [u]) T) a) b))
    (hwp : p.wscopedB d = true) (hbp : p.looseBVarsBounded 0 = true)
    (hlp : ∀ l ∈ p.fvarLeaves, l ∈ a.fvarLeaves)
    (sp : InferSemFull m φ d p (.app (.app (.app (.const eqName [u]) T) a) b))
    (sa : InferSemFull m φ d a ta) (sda : DefEqSem m φ d ta T)
    (sb : InferSemFull m φ d b tb) (sdb : DefEqSem m φ d tb T)
    (sTT : InferSemFull m φ d T sT) (sred : RedSem m φ d sT (.sort v))
    (hv : ∀ φ : LevelParam → Nat, Level.eval φ v = Level.eval φ u) :
    RedSem m φ d a b := by
  intro hfa Δa aa hCa haa _
  -- the proof reads, with its type
  have hwp' : Expr.WScoped d p := Expr.WScoped.of_wscopedB hwp
  have hLp : Expr.LeavesBounded p := fun l hl => hfa.2.2 l (hlp l hl)
  have hCp : CtxOk m φ d Δa p := hCa.of_subset hlp
  obtain ⟨pa, hpa⟩ := Ix.Kernel.Model.infer_reads m φ hp rfl hwp' hbp hLp
  obtain ⟨hfS, hsubS, Sa, hSa, -, -, hmemP⟩ :=
    sp (⟨hwp', hbp, hLp⟩ : Expr.WScoped d p ∧ p.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded p) hCp hpa
  -- the type's pieces
  obtain ⟨hf3, hfb⟩ := frame_app_split hfS
  obtain ⟨hf2, -⟩ := frame_app_split hf3
  obtain ⟨-, hfT⟩ := frame_app_split hf2
  have hCT : CtxOk m φ d Δa T :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  have hCb : CtxOk m φ d Δa b :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  obtain ⟨r3, br, h3, hbr, rfl⟩ := denoteMeta_app_inv hSa
  obtain ⟨r2, ar, h2, har, rfl⟩ := denoteMeta_app_inv h3
  obtain ⟨Er, Tr, h1, hTr, rfl⟩ := denoteMeta_app_inv h2
  have hara : ar = aa := Option.some.inj (har.symm.trans haa)
  subst ar
  -- the stored `Eq` is the pinned one, and its reading is the leaf
  have hci : ci = eqA := by
    rw [(m.basis_pinned eqName ci hfE (by (cases md <;> decide))).1]
    unfold pinnedInfo
    rw [if_pos rfl]
  subst hci
  rw [denoteMeta_const hfE (by rfl)] at h1
  obtain rfl := Option.some.inj h1
  -- the typings
  obtain ⟨hfta, hsubta, tar, htar, -, hgta, hmemA⟩ := sa hfa hCa haa
  obtain ⟨hfsT, hsubsT, sTr, hsTr, hgT, hgsT, hmemT⟩ := sTT hfT hCT hTr
  obtain ⟨hftb, hsubtb, tbr, htbr, hgB, hgtb, hmemB⟩ := sb hfb hCb hbr
  have heqA := sda hfta hfT (hCa.of_subset hsubta) hCT htar hTr hgta hgT
  have heqB := sdb hftb hfT (hCb.of_subset hsubtb) hCT htbr hTr hgtb hgT
  obtain ⟨-, -, sa', hsa', -, heqS⟩ := sred hfsT (hCT.of_subset hsubsT) hsTr hgsT
  rw [denoteMeta_sort] at hsa'
  obtain rfl : sa' = AnnotTerm.sort (v.eval φ) := (Option.some.inj hsa').symm
  have hlaw := (hin.eq_law hfE (Level.substFn φ (eqA (md := md)).toConstantVal.levelParams [u])).1
  refine ⟨hfb, fun l hl => hlp l (hsubS l (by simp [Expr.fvarLeaves, hl])), br, hbr, hgB,
    fun ρ hρ => ?_⟩
  have hTu : interp V ρ Tr ∈ˢ
      (univ (Level.substFn φ (eqA (md := md)).toConstantVal.levelParams [u] uN) : V) := by
    have h := hmemT ρ hρ
    rw [heqS ρ hρ, interp_sort, hv φ] at h
    exact h
  have ha' : interp V ρ aa ∈ˢ interp V ρ Tr := heqA ρ hρ ▸ hmemA ρ hρ
  have hb' : interp V ρ br ∈ˢ interp V ρ Tr := heqB ρ hρ ▸ hmemB ρ hρ
  have hP := hmemP ρ hρ
  simp only [interp_app] at hP
  rw [hlaw ρ _ _ _ hTu ha' hb'] at hP
  exact mem_eqv hP

/-- **`Red.defEqClosed` is sound.** -/
theorem Red.defEqClosed_sound {d : Nat} {a a' b b' ta tb : Expr md}
    (haf : a.hasFvar = false) (hab : a.looseBVarsBounded 0 = true)
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (ha'f : a'.hasFvar = false) (ha'b : a'.looseBVarsBounded 0 = true)
    (hb'f : b'.hasFvar = false) (hb'b : b'.looseBVarsBounded 0 = true)
    (hia : Infer env .full 0 a' ta)
    (hib : Infer env .full 0 b' tb)
    (sia : InferSemFull m φ 0 a' ta) (sra : RedSem m φ 0 a' a)
    (sib : InferSemFull m φ 0 b' tb) (srb : RedSem m φ 0 b' b)
    (sde : DefEqSem m φ 0 a' b') :
    RedSem m φ d a b := by
  intro _ Δa aa _ haa _
  obtain ⟨hfa', hCa'⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (d := 0) (Δa := []) ha'f ha'b rfl
  obtain ⟨a'r, ha'r⟩ := Ix.Kernel.Model.infer_reads m φ hia rfl hfa'.1 hfa'.2.1 hfa'.2.2
  obtain ⟨-, -, -, -, hga', -, -⟩ := sia hfa' hCa' ha'r
  obtain ⟨-, -, ar, har, -, heqA⟩ := sra hfa' hCa' ha'r hga'
  obtain ⟨hfb', hCb'⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (d := 0) (Δa := []) hb'f hb'b rfl
  obtain ⟨b'r, hb'r⟩ := Ix.Kernel.Model.infer_reads m φ hib rfl hfb'.1 hfb'.2.1 hfb'.2.2
  obtain ⟨-, -, -, -, hgb', -, -⟩ := sib hfb' hCb' hb'r
  obtain ⟨-, -, br, hbr, hgb, heqB⟩ := srb hfb' hCb' hb'r hgb'
  have heqAB := sde hfa' hfb' hCa' hCb' ha'r hb'r hga' hgb'
  have harD : denoteMeta m.acval env φ d a = some ar :=
    denoteMeta_depth_of_closed m.acval_closed haf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed haf hab har 1 k) har d
  have hbrD : denoteMeta m.acval env φ d b = some br :=
    denoteMeta_depth_of_closed m.acval_closed hbf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hbf hbb hbr 1 k) hbr d
  obtain rfl : aa = ar := Option.some.inj (haa.symm.trans harD)
  have hnl := Expr.fvarLeaves_eq_nil_of_not_hasFvar hbf
  have hfb : Frame d b :=
    ⟨Expr.WScoped.of_not_hasFvar hbf, hbb, Expr.LeavesBounded.of_not_hasFvar hbf⟩
  have hleaves : LeavesSub b a := fun l hl => by rw [hnl] at hl; cases hl
  have hgb' : Graded V Δa br := fun ρ _ => hgb ρ (Sat_nil V ρ)
  refine ⟨hfb, hleaves, br, hbrD, hgb', fun ρ _ => ?_⟩
  have hρ := Sat_nil V ρ
  exact (heqA ρ hρ).symm.trans ((heqAB ρ hρ).trans (heqB ρ hρ))

/-- **`DefEq.eqProof` is sound.** -/
theorem DefEq.eqProof_sound (hin : RulesInputs V m φ) {d : Nat} {a b p T ta tb sT : Expr md}
    {u v : Level} {ci : ConstantInfo md}
    (hfE : env.find? eqName = some ci)
    (haf : a.hasFvar = false) (hab : a.looseBVarsBounded 0 = true)
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (hpf : p.hasFvar = false) (hpb : p.looseBVarsBounded 0 = true)
    (hp : Infer env .full 0 p (.app (.app (.app (.const eqName [u]) T) a) b))
    (sp : InferSemFull m φ 0 p (.app (.app (.app (.const eqName [u]) T) a) b))
    (sa : InferSemFull m φ 0 a ta) (sda : DefEqSem m φ 0 ta T)
    (sb : InferSemFull m φ 0 b tb) (sdb : DefEqSem m φ 0 tb T)
    (sTT : InferSemFull m φ 0 T sT) (sred : RedSem m φ 0 sT (.sort v))
    (hv : ∀ φ : LevelParam → Nat, Level.eval φ v = Level.eval φ u) :
    DefEqSem m φ d a b := by
  intro _ _ Δa aa ba _ _ haa hba _ _ ρ _
  obtain ⟨hfp, hCp⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (d := 0) (Δa := []) hpf hpb rfl
  obtain ⟨pa, hpa⟩ := Ix.Kernel.Model.infer_reads m φ hp rfl hfp.1 hfp.2.1 hfp.2.2
  obtain ⟨hfS, hsubS, Sa, hSa, -, -, hmemP⟩ := sp hfp hCp hpa
  obtain ⟨hf3, hfb0⟩ := frame_app_split hfS
  obtain ⟨hf2, hfa0⟩ := frame_app_split hf3
  obtain ⟨-, hfT⟩ := frame_app_split hf2
  have hCT : CtxOk m φ 0 [] T :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  have hCa0 : CtxOk m φ 0 [] a :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  have hCb0 : CtxOk m φ 0 [] b :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  obtain ⟨r3, br, h3, hbr, rfl⟩ := denoteMeta_app_inv hSa
  obtain ⟨r2, ar, h2, har, rfl⟩ := denoteMeta_app_inv h3
  obtain ⟨Er, Tr, h1, hTr, rfl⟩ := denoteMeta_app_inv h2
  have hci : ci = eqA := by
    rw [(m.basis_pinned eqName ci hfE (by (cases md <;> decide))).1]
    unfold pinnedInfo
    rw [if_pos rfl]
  subst hci
  rw [denoteMeta_const hfE (by rfl)] at h1
  obtain rfl := Option.some.inj h1
  obtain ⟨hfta, hsubta, tar, htar, -, hgta, hmemA⟩ := sa hfa0 hCa0 har
  obtain ⟨hfsT, hsubsT, sTr, hsTr, hgT, hgsT, hmemT⟩ := sTT hfT hCT hTr
  obtain ⟨hftb, hsubtb, tbr, htbr, -, hgtb, hmemB⟩ := sb hfb0 hCb0 hbr
  have heqA := sda hfta hfT (hCa0.of_subset hsubta) hCT htar hTr hgta hgT
  have heqB := sdb hftb hfT (hCb0.of_subset hsubtb) hCT htbr hTr hgtb hgT
  obtain ⟨-, -, sa', hsa', -, heqS⟩ := sred hfsT (hCT.of_subset hsubsT) hsTr hgsT
  rw [denoteMeta_sort] at hsa'
  obtain rfl : sa' = AnnotTerm.sort (v.eval φ) := (Option.some.inj hsa').symm
  have harD : denoteMeta m.acval env φ d a = some ar :=
    denoteMeta_depth_of_closed m.acval_closed haf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed haf hab har 1 k) har d
  have hbrD : denoteMeta m.acval env φ d b = some br :=
    denoteMeta_depth_of_closed m.acval_closed hbf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hbf hbb hbr 1 k) hbr d
  obtain rfl : aa = ar := Option.some.inj (haa.symm.trans harD)
  obtain rfl : ba = br := Option.some.inj (hba.symm.trans hbrD)
  have hlaw := (hin.eq_law hfE (Level.substFn φ (eqA (md := md)).toConstantVal.levelParams [u])).1
  have hρ := Sat_nil V ρ
  have hTu : interp V ρ Tr ∈ˢ
      (univ (Level.substFn φ (eqA (md := md)).toConstantVal.levelParams [u] uN) : V) := by
    have h := hmemT ρ hρ
    rw [heqS ρ hρ, interp_sort, hv φ] at h
    exact h
  have ha' : interp V ρ aa ∈ˢ interp V ρ Tr := heqA ρ hρ ▸ hmemA ρ hρ
  have hb' : interp V ρ ba ∈ˢ interp V ρ Tr := heqB ρ hρ ▸ hmemB ρ hρ
  have hP := hmemP ρ hρ
  simp only [interp_app] at hP
  rw [hlaw ρ _ _ _ hTu ha' hb'] at hP
  exact mem_eqv hP

private theorem denoteMeta_zero_of_depth {env : Env md} {φ : LevelParam → Nat}
    {acval : Key md → (LevelParam → Nat) → AnnotTerm}
    {cval : TConstVal md}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    (hacl : ∀ (n : Key md) (ψ : LevelParam → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {e : Expr md} {ea : AnnotTerm} (hfv : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true) :
    ∀ d : Nat, denoteMeta acval env φ d e = some ea → denoteMeta acval env φ 0 e = some ea := by
  intro d hd
  have hsome : ∃ ea0, denoteMeta acval env φ 0 e = some ea0 := by
    induction d generalizing ea with
    | zero => exact ⟨ea, hd⟩
    | succ d ih =>
      have hs := denoteMeta_shiftFrom (env := env) (acval := acval) (φ := φ)
        (p := 0) hacl e d (Nat.zero_le d) (Expr.WScoped.of_not_hasFvar hfv)
      rw [Expr.shiftFrom_eq_self_of_not_hasFvar hfv] at hs
      rw [hs] at hd
      cases hprev : denoteMeta acval env φ d e with
      | none => rw [hprev] at hd; cases hd
      | some ea' => exact ih hprev
  obtain ⟨ea0, hea0⟩ := hsome
  have hEq := denoteMeta_depth_of_closed hacl hfv
    (fun k => denoteMeta_closed hlink hcl hfv hb hea0 1 k) hea0 d
  obtain rfl : ea0 = ea := Option.some.inj (hEq.symm.trans hd)
  exact hea0

omit [SetTheory V] in
private theorem cons_agree_below' {k : Nat} {ρ ρ' : Nat → V} (hag : ∀ i, i < k → ρ i = ρ' i)
    (x : V) : ∀ i, i < k + 1 → cons x ρ i = cons x ρ' i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)

private theorem wellDenoted_congr_below' :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      Term.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (WellDenoted V ρ e ↔ WellDenoted V ρ' e) := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | prf => intros; simp
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_app, WellDenoted_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag,
      interp_congr_below V f k ρ ρ' hb.1 hag, interp_congr_below V a k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_lam, WellDenoted_lam, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mp (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [← interp_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below' hag x)]
      exact hB x hx
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mpr (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [interp_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below' hag x)]
      exact hB x hx
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_pi, WellDenoted_pi, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mpr (h2 x hx)⟩
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_eqE, WellDenoted_eqE, iha k ρ ρ' hb.1 hag, ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_fst, WellDenoted_fst, ihe k ρ ρ' hb hag,
      interp_congr_below V e k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_snd, WellDenoted_snd, ihe k ρ ρ' hb hag,
      interp_congr_below V e k ρ ρ' hb hag]
  | chain g e ihg ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_chain, WellDenoted_chain, ihe k ρ ρ' hb.2 hag]
    exact and_congr (forall_congr' fun m => ihg m k ρ ρ' (hb.1 m) hag) Iff.rfl
  | bgraph _ f ihf =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_bgraph, WellDenoted_bgraph, ihf k ρ ρ' hb hag]

private theorem annotValid_congr_below' :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      Term.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (AnnotValid V ρ e ↔ AnnotValid V ρ' e) := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | prf => intros; simp [AnnotValid]
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_app, AnnotValid_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_lam, AnnotValid_lam, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mpr (h2 x hx)⟩
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_pi, AnnotValid_pi, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mp (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [← interp_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below' hag x)]
      exact h3 h0 x hx
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below' hag x)).mpr (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [interp_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below' hag x)]
      exact h3 h0 x hx
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_eqE, AnnotValid_eqE, iha k ρ ρ' hb.1 hag, ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_fst, AnnotValid_fst, ihe k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_snd, AnnotValid_snd, ihe k ρ ρ' hb hag]
  | chain g e ihg ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_chain, AnnotValid_chain, ihe k ρ ρ' hb.2 hag]
    exact and_congr (forall_congr' fun m => ihg m k ρ ρ' (hb.1 m) hag) Iff.rfl
  | bgraph _ f ihf =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_bgraph, AnnotValid_bgraph, ihf k ρ ρ' hb hag]

private theorem wellDenotedV_closed_congr {e : AnnotTerm} {ρ ρ' : Nat → V}
    (hb : Term.bvarsBelow 0 e.erase) (h : WellDenotedV V ρ e) : WellDenotedV V ρ' e :=
  ⟨(wellDenoted_congr_below' e 0 ρ ρ' hb (fun _ hi => absurd hi (Nat.not_lt_zero _))).mp h.1,
   (annotValid_congr_below' e 0 ρ ρ' hb (fun _ hi => absurd hi (Nat.not_lt_zero _))).mp h.2⟩

/-- **`DefEq.instClosed` is sound.** -/
theorem DefEq.instClosed_sound {d : Nat} {ks : List LevelParam} {us : List Level}
    {a b : Expr md}
    (haf : a.hasFvar = false) (hab : a.looseBVarsBounded 0 = true)
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (sde : DefEqSem m (Level.substFn φ ks us) 0 a b) :
    DefEqSem m φ d (a.instantiateLevelParams ks us) (b.instantiateLevelParams ks us) := by
  intro _ _ Δa aa ba _ _ haa hba hga hgb ρ hsat
  let ψ := Level.substFn φ ks us
  obtain ⟨hfa, hCa⟩ := frame_of_not_hasFvar (m := m) (φ := ψ) (d := 0) (Δa := []) haf hab rfl
  obtain ⟨hfb, hCb⟩ := frame_of_not_hasFvar (m := m) (φ := ψ) (d := 0) (Δa := []) hbf hbb rfl
  rw [denotePInstLevels m φ ks us d a] at haa
  rw [denotePInstLevels m φ ks us d b] at hba
  have ha0 := denoteMeta_zero_of_depth m.acval_erase m.cval_closed m.acval_closed haf hab d haa
  have hb0 := denoteMeta_zero_of_depth m.acval_erase m.cval_closed m.acval_closed hbf hbb d hba
  have hba0 : Term.bvarsBelow 0 aa.erase :=
    denote_closed m.cval_closed haf hab (denoteMeta_erase m.acval_erase 0 a ha0)
  have hbb0 : Term.bvarsBelow 0 ba.erase :=
    denote_closed m.cval_closed hbf hbb (denoteMeta_erase m.acval_erase 0 b hb0)
  have hga0 : Graded V [] aa := fun ρ' _ => wellDenotedV_closed_congr hba0 (hga ρ hsat)
  have hgb0 : Graded V [] ba := fun ρ' _ => wellDenotedV_closed_congr hbb0 (hgb ρ hsat)
  exact sde hfa hfb hCa hCb ha0 hb0 hga0 hgb0 ρ (Sat_nil V ρ)

/-- **`PiRed.ofRed` is sound.** -/
theorem PiRed.ofRed_sound {d : Nat} {e e' : Expr md} (h : RedSem m φ d e e') :
    PiRedSem m φ d e e' := fun hf hC hea hg => by
  obtain ⟨_, _, ea', hea', hga', heq⟩ := h hf hC hea hg
  exact ⟨ea', hea', hga', heq⟩

/-- **`PiRed.app` is sound.** -/
theorem PiRed.app_sound {d : Nat} {f f' a a' : Expr md}
    (sf : PiRedSem m φ d f f') (sa : PiRedSem m φ d a a') :
    PiRedSem m φ d (.app f a) (.app f' a') := by
  intro Δa ea hf hC hea hg
  obtain ⟨hff, hfa⟩ := frame_app_split hf
  obtain ⟨fa, aa, hfaD, haaD, rfl⟩ := denoteMeta_app_inv hea
  have hgf : Graded V Δa fa := fun ρ hρ =>
    ⟨((WellDenoted_app V ρ fa aa) ▸ (hg ρ hρ).1).1, ((AnnotValid_app V ρ fa aa) ▸ (hg ρ hρ).2).1⟩
  have hga : Graded V Δa aa := fun ρ hρ =>
    ⟨((WellDenoted_app V ρ fa aa) ▸ (hg ρ hρ).1).2.1, ((AnnotValid_app V ρ fa aa) ▸ (hg ρ hρ).2).2⟩
  obtain ⟨fa', hfa', hgf', heqF⟩ := sf hff hC.app_fn hfaD hgf
  obtain ⟨aa', haa', hga', heqA⟩ := sa hfa hC.app_arg haaD hga
  have hden' : denoteMeta m.acval env φ d (.app f' a') = some (.app fa' aa') := by
    rw [denoteMeta_app, hfa', haa']; rfl
  refine ⟨.app fa' aa', hden', ?_, ?_⟩
  · intro ρ hρ
    have hwd := (WellDenoted_app V ρ fa aa) ▸ (hg ρ hρ).1
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨(hgf' ρ hρ).1, (hga' ρ hρ).1, ?_⟩
      obtain ⟨r, A, B, hF, hX, h0⟩ := hwd.2.2
      exact ⟨r, A, B, heqF ρ hρ ▸ hF, heqA ρ hρ ▸ hX, h0⟩
    · rw [AnnotValid_app]
      exact ⟨(hgf' ρ hρ).2, (hga' ρ hρ).2⟩
  · intro ρ hρ
    simp only [interp_app, heqF ρ hρ, heqA ρ hρ]

/-- **`PiRed.forallE` is sound.** -/
theorem PiRed.forallE_sound {d : Nat} {A A' B B' : Expr md} {mb : BinderMeta}
    (sA : PiRedSem m φ d A A')
    (sB : PiRedSem m φ (d + 1) (B.instantiate1 (.fvar d A)) (B'.instantiate1 (.fvar d A))) :
    PiRedSem m φ d (.forallE A B mb) (.forallE A' B' mb) := by
  intro Δa ea hf hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLA : Expr.LeavesBounded A := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
  have hLB : Expr.LeavesBounded B := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ := frame_open2 hws.1 hb.1 hws.2 hb.2 hLA hLB
  obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hea
  obtain ⟨hgt, hgb⟩ := WellDenotedV.hoist_pi (V := V) hg
  obtain ⟨ta', hta', hgt', heqA⟩ := sA ⟨hws.1, hb.1, hLA⟩ hC.forallE_ty hta hgt
  have hCop : CtxOk m φ (d + 1) (ta :: Δa) (B.instantiate1 (.fvar d A)) :=
    CtxOk.openS hC.forallE_ty hC.forallE_body hta hgt
  obtain ⟨ba', hba', hgb', heqB⟩ := sB ⟨hwopen, hbopen, hLopen⟩ hCop hba hgb
  have hba'' : denoteMeta m.acval env φ (d + 1) (B'.instantiate1 (.fvar d A')) = some ba' :=
    denoteMeta_open_rename hba'
  have hden' : denoteMeta m.acval env φ d (.forallE A' B' mb) =
      some (.pi 0 (pwBit φ mb.pw) ta' ba') := by
    rw [denoteMeta_forallE, hta', hba'']; rfl
  refine ⟨.pi 0 (pwBit φ mb.pw) ta' ba', hden', ?_, ?_⟩
  · intro ρ hρ
    have hsat' : ∀ x, x ∈ˢ interp V ρ ta' → Sat V (ta :: Δa) (cons x ρ) := fun x hx =>
      Sat_cons V hρ (by rwa [heqA ρ hρ])
    have hpi := hg ρ hρ
    have hpiA := (AnnotValid_pi V ρ 0 (pwBit φ mb.pw) ta ba) ▸ hpi.2
    refine ⟨⟨(hgt' ρ hρ).1, fun x hx => (hgb' (cons x ρ) (hsat' x hx)).1⟩, ?_⟩
    rw [AnnotValid_pi]
    refine ⟨(hgt' ρ hρ).2, fun x hx => (hgb' (cons x ρ) (hsat' x hx)).2, fun h0 x hx => ?_⟩
    have hx' : x ∈ˢ interp V ρ ta := by rwa [heqA ρ hρ]
    rw [← heqB (cons x ρ) (hsat' x hx)]
    exact hpiA.2.2 h0 x hx'
  · intro ρ hρ
    rw [interp_pi, interp_pi, heqA ρ hρ]
    exact piR_congr fun x hx => heqB (cons x ρ) (Sat_cons V hρ (by rwa [heqA ρ hρ]))

/-- **`PiRed.lam` is sound.** -/
theorem PiRed.lam_sound {d : Nat} {A A' B B' : Expr md} {mb : BinderMeta}
    (sA : PiRedSem m φ d A A')
    (sB : PiRedSem m φ (d + 1) (B.instantiate1 (.fvar d A)) (B'.instantiate1 (.fvar d A))) :
    PiRedSem m φ d (.lam A B mb) (.lam A' B' mb) := by
  intro Δa ea hf hC hea hg
  obtain ⟨hws, hb, hLb⟩ := hf
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLA : Expr.LeavesBounded A := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
  have hLB : Expr.LeavesBounded B := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ := frame_open2 hws.1 hb.1 hws.2 hb.2 hLA hLB
  obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv hea
  obtain ⟨hgt, hgb⟩ := Graded.lam hg
  obtain ⟨ta', hta', hgt', heqA⟩ := sA ⟨hws.1, hb.1, hLA⟩ hC.lam_ty hta hgt
  have hCop : CtxOk m φ (d + 1) (ta :: Δa) (B.instantiate1 (.fvar d A)) :=
    CtxOk.openS hC.lam_ty hC.lam_body hta hgt
  obtain ⟨ba', hba', hgb', heqB⟩ := sB ⟨hwopen, hbopen, hLopen⟩ hCop hba hgb
  have hba'' : denoteMeta m.acval env φ (d + 1) (B'.instantiate1 (.fvar d A')) = some ba' :=
    denoteMeta_open_rename hba'
  have hden' : denoteMeta m.acval env φ d (.lam A' B' mb) =
      some (.lam (pwBit φ mb.pw) ta' ba') := by
    rw [denoteMeta_lam, hta', hba'']; rfl
  refine ⟨.lam (pwBit φ mb.pw) ta' ba', hden', ?_, ?_⟩
  · intro ρ hρ
    have hsat' : ∀ x, x ∈ˢ interp V ρ ta' → Sat V (ta :: Δa) (cons x ρ) := fun x hx =>
      Sat_cons V hρ (by rwa [heqA ρ hρ])
    have hlam := hg ρ hρ
    have hwd := (WellDenoted_lam V ρ (pwBit φ mb.pw) ta ba) ▸ hlam.1
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam]
      refine ⟨(hgt' ρ hρ).1, fun x hx => (hgb' (cons x ρ) (hsat' x hx)).1, ?_⟩
      obtain ⟨Bf, hmem, h0⟩ := hwd.2.2
      exact ⟨Bf, fun x hx => by
          rw [← heqB (cons x ρ) (hsat' x hx)]
          exact hmem x (by rwa [heqA ρ hρ]),
        fun hv x hx => h0 hv x (by rwa [heqA ρ hρ])⟩
    · rw [AnnotValid_lam]
      exact ⟨(hgt' ρ hρ).2, fun x hx => (hgb' (cons x ρ) (hsat' x hx)).2⟩
  · intro ρ hρ
    rw [interp_lam, interp_lam, heqA ρ hρ]
    exact lamR_congr fun x hx => heqB (cons x ρ) (Sat_cons V hρ (by rwa [heqA ρ hρ]))

/-- **`DefEq.transClosed` is sound.** -/
theorem DefEq.transClosed_sound {d : Nat} {a b b' c tb : Expr md}
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (hb'f : b'.hasFvar = false) (hb'b : b'.looseBVarsBounded 0 = true)
    (hib : Infer env .full 0 b' tb)
    (sib : InferSemFull m φ 0 b' tb) (spb : PiRedSem m φ 0 b' b)
    (sab : DefEqSem m φ d a b) (sbc : DefEqSem m φ d b c) :
    DefEqSem m φ d a c := by
  intro hfa hfc Δa aa ca hCa hCc haa hca hga hgc ρ hρ
  obtain ⟨hfb', hCb'⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (d := 0) (Δa := []) hb'f hb'b rfl
  obtain ⟨b'r, hb'r⟩ := Ix.Kernel.Model.infer_reads m φ hib rfl hfb'.1 hfb'.2.1 hfb'.2.2
  obtain ⟨-, -, -, -, hgb', -, -⟩ := sib hfb' hCb' hb'r
  obtain ⟨br, hbr, hgb0, -⟩ := spb hfb' hCb' hb'r hgb'
  have hbrD : denoteMeta m.acval env φ d b = some br :=
    denoteMeta_depth_of_closed m.acval_closed hbf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hbf hbb hbr 1 k) hbr d
  have hgb : Graded V Δa br := fun ρ' _ => hgb0 ρ' (Sat_nil V ρ')
  obtain ⟨hfb, hCb⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (d := d) (Δa := Δa) hbf hbb hCa.1
  exact (sab hfa hfb hCa hCb haa hbrD hga hgb ρ hρ).trans
    (sbc hfb hfc hCb hCc hbrD hca hgb hgc ρ hρ)

end Ix.Kernel.Model.Rules
