module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst

public section

/-!
# The soundness of the three list walks (task #305, lane S-red)

`Certs` (`certs_teleLic`, `Model/Steps/IotaGate.lean:123`, one step
per constructor), `DefEqList` (`map_interp_of_defEqListFueled`,
`Stuck.lean:223`) and `EtaProjCerts` (pointwise).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem Certs.nil_sound {d : Nat} {lic : Bool} {T : Expr} :
    CertsSem m φ d lic T [] := by
  intro _ Δa Ta _ vs _ _ hgT _ hsp _ _
  cases hsp
  exact ⟨Ta, fun _ _ => .nil, hgT⟩

/-- **One slot of the certificate walk, after the slot membership.**
The two `Certs` rules differ only in how `hmemA` is obtained — the
licence's transfer or the certificate's run — so everything downstream
(the residual's reading, its frame, its grading, the licence handed to
the tail, and `TeleFitPA.cons`) is shared
(`certs_telePA`/`certs_teleLic`'s common step). -/
theorem certs_step {d : Nat} {lic : Bool} {ty body arg : Expr}
    {mb : ConLeche.BinderMeta} {rest : List Expr}
    {Δa : List AnnotTerm} {doma bodya fa aa : AnnotTerm}
    {vs' : List AnnotTerm}
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest)
    (hCT : CtxOk m φ d Δa (.forallE ty body mb))
    (hgT : Graded V Δa (.pi 0 (pwBit φ mb.pw) doma bodya))
    (hargs : ∀ x ∈ arg :: rest, Frame d x ∧ CtxOk m φ d Δa x)
    (hsp' : DenoteMetaSpine m.acval env φ d rest vs')
    (hgvs : ∀ x ∈ aa :: vs', Graded V Δa x)
    (hlicP : lic = true →
      Graded V Δa (AnnotTerm.mkAppN fa (aa :: vs')) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ fa ∈ˢ interp V ρ (.pi 0 (pwBit φ mb.pw) doma bodya))
    (hbodyw : Expr.WScoped d body)
    (hbodyb : Expr.looseBVarsBounded 1 body = true)
    (hLbty : Expr.LeavesBounded (.forallE ty body mb))
    (hbodya : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) = some bodya)
    (haa : denoteMeta m.acval env φ d arg = some aa)
    (hfarg : Frame d arg) (hCarg : CtxOk m φ d Δa arg)
    (hokA : Graded V Δa aa)
    (hokBody : ∀ ρ : Nat → V, Sat V Δa ρ →
      ∀ x, x ∈ˢ interp V ρ doma → WellDenotedV V (cons x ρ) bodya)
    (hmemA : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ doma) :
    ∃ resta : AnnotTerm,
      (∀ ρ : Nat → V, Sat V Δa ρ →
        TeleFitPA V ρ (.pi 0 (pwBit φ mb.pw) doma bodya) (aa :: vs') resta) ∧
        Graded V Δa resta := by
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denoteMeta m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hCbody : CtxOk m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hCT.2 l (by simp [Expr.fvarLeaves, hl'])
    · exact hCarg.2 l hl'
  have hokBody' : Graded V Δa (bodya.inst aa) := fun ρ hρ =>
    (WellDenotedV_inst0 (hokA ρ hρ)).mpr (hokBody ρ hρ _ (hmemA ρ hρ))
  have hlicP' : lic = true →
      Graded V Δa (AnnotTerm.mkAppN (.app fa aa) vs') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ (.app fa aa) ∈ˢ interp V ρ (bodya.inst aa) := by
    intro hl
    obtain ⟨hokS, hfaM⟩ := hlicP hl
    refine ⟨hokS, fun ρ hρ => ?_⟩
    have hoks : ∀ x ∈ [aa], WellDenotedV V ρ x := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hokA ρ hρ
    exact (mkAppN_of_fitA [aa] (hgT ρ hρ) (mkAppN_head (aa :: vs') (hokS ρ hρ))
      hoks (hfaM ρ hρ) (TeleFitPA.cons (hmemA ρ hρ) .nil)).2
  obtain ⟨resta, hfit, hgresta⟩ :=
    hrest ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hCbody hbody' hokBody'
      (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
      (fun x hx => hgvs x (List.mem_cons_of_mem aa hx)) hlicP'
  exact ⟨resta, fun ρ hρ => .cons (hmemA ρ hρ) (hfit ρ hρ), hgresta⟩

/-- The licensed slot: `iota_slot_transfer` (`Steps/IotaGate.lean:63`). -/
theorem Certs.skip_sound {d : Nat} {lic : Bool}
    {ty body arg : Expr} {mb : BinderMeta} {rest : List Expr}
    (hlic : lic = true) (hnev : mb.pw.isNever = true)
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest) :
    CertsSem m φ d lic (.forallE ty body mb) (arg :: rest) := by
  intro hfT Δa Ta fa vs hCT hTa hgT hargs hsp hgvs hlicP
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  have hokA : Graded V Δa aa := hgvs aa List.mem_cons_self
  have hokBody : ∀ (ρ : Nat → V), Sat V Δa ρ →
      ∀ x, x ∈ˢ interp V ρ doma → WellDenotedV V (cons x ρ) bodya :=
    fun ρ hρ x hx =>
      ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hgT ρ hρ).1).2 x hx,
        ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hgT ρ hρ).2).2.1 x hx⟩
  -- THE LICENCE: the binder's datum is `.never`, so the head prefix's
  -- own app slot transfers the argument into the telescope's domain
  have hmemA : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ doma := by
    intro ρ hρ
    obtain ⟨hokS, hfaM⟩ := hlicP hlic
    have hokApp : WellDenotedV V ρ (.app fa aa) :=
      mkAppN_head vs' (hokS ρ hρ)
    obtain ⟨v', A', B', hslot, ha, -⟩ :=
      ((WellDenoted_app V ρ fa aa) ▸ hokApp.1).2.2
    have hf' := hfaM ρ hρ
    rw [interp_pi] at hf'
    exact slotTransfer (pwBit_ne_zero_of_isNever hnev φ) hf' hslot ha
  exact certs_step hrest hCT hgT hargs hsp' hgvs hlicP hbodyw hbodyb hLbty
    hbodya haa hfarg hCarg hokA hokBody hmemA

/-- The certified slot: `certs_telePA`'s step (`Steps/IotaKit.lean:246`). -/
theorem Certs.cert_sound {d : Nat} {lic : Bool}
    {ty body arg ta : Expr} {mb : BinderMeta} {rest : List Expr}
    (hta : InferSemIO m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest) :
    CertsSem m φ d lic (.forallE ty body mb) (arg :: rest) := by
  intro hfT Δa Ta fa vs hCT hTa hgT hargs hsp hgvs hlicP
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOk m φ d Δa ty :=
    hCT.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  have hokA : Graded V Δa aa := hgvs aa List.mem_cons_self
  have hokDom : Graded V Δa doma := fun ρ hρ =>
    ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hgT ρ hρ).1).1,
      ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hgT ρ hρ).2).1⟩
  have hokBody : ∀ (ρ : Nat → V), Sat V Δa ρ →
      ∀ x, x ∈ˢ interp V ρ doma → WellDenotedV V (cons x ρ) bodya :=
    fun ρ hρ x hx =>
      ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hgT ρ hρ).1).2 x hx,
        ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hgT ρ hρ).2).2.1 x hx⟩
  -- the certificate: the argument inhabits the binder's domain
  obtain ⟨hfta, hsubta, taA, htaA, hgtaA, hmem⟩ := hta hfarg hCarg haa hokA
  have hmemA : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ doma := fun ρ hρ =>
    (hd hfta ⟨hdomw, hdomb, hLbdom⟩ (hCarg.of_subset hsubta) hCdom htaA hdoma
      hgtaA hokDom ρ hρ) ▸ hmem ρ hρ
  exact certs_step hrest hCT hgT hargs hsp' hgvs hlicP hbodyw hbodyb hLbty
    hbodya haa hfarg hCarg hokA hokBody hmemA

theorem DefEqList.nil_sound {d : Nat} : DefEqListSem m φ d [] [] := by
  refine ⟨rfl, ?_⟩
  intro Δa asa bsa _ _ hsa hsb _ _ _ _
  cases hsa
  cases hsb
  rfl

theorem DefEqList.cons_sound {d : Nat} {a b : Expr} {as bs : List Expr}
    (h : DefEqSem m φ d a b) (hs : DefEqListSem m φ d as bs) :
    DefEqListSem m φ d (a :: as) (b :: bs) := by
  refine ⟨by simp [hs.1], ?_⟩
  intro Δa asa bsa hfa hfb hsa hsb hga hgb ρ hρ
  cases hsa with | @cons _ va _ vas hva hsa' =>
  cases hsb with | @cons _ vb _ vbs hvb hsb' =>
  obtain ⟨hfa1, hCa1⟩ := hfa a List.mem_cons_self
  obtain ⟨hfb1, hCb1⟩ := hfb b List.mem_cons_self
  simp only [List.map_cons, List.cons.injEq]
  refine ⟨h hfa1 hfb1 hCa1 hCb1 hva hvb (hga va List.mem_cons_self)
      (hgb vb List.mem_cons_self) ρ hρ,
    hs.2 (fun x hx => hfa x (List.mem_cons_of_mem a hx))
      (fun x hx => hfb x (List.mem_cons_of_mem b hx)) hsa' hsb'
      (fun x hx => hga x (List.mem_cons_of_mem va hx))
      (fun x hx => hgb x (List.mem_cons_of_mem vb hx)) ρ hρ⟩

theorem EtaProjCerts.nil_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} :
    EtaProjCertsSem m φ d T us' targs b lpsT [] := by
  intro i hi
  exact nomatch hi

theorem EtaProjCerts.cons_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} {i : Nat}
    {rest : List Nat} {cvp : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hf : env.find? (projFnName T i) = some (.recInfo cvp mI rP rules))
    (hlps : cvp.levelParams = lpsT)
    (hstrip : (cvp.type.stripPis (targs.length + 1)).isSome = true)
    (hcerts : CertsSem m φ d false
      (cvp.type.instantiateLevelParams cvp.levelParams us') (targs ++ [b]))
    (hrest : EtaProjCertsSem m φ d T us' targs b lpsT rest) :
    EtaProjCertsSem m φ d T us' targs b lpsT (i :: rest) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact ⟨cvp, mI, rP, rules, hf, hlps, hstrip, hcerts⟩
  · exact hrest j hj'

end ConLeche.Model.Rules
