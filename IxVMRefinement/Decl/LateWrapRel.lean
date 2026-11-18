import IxVMRefinement.Decl.NativeRecRules
import IxVMRefinement.Core.CallScope

/-! # `wrap_rel` under a general keying and a narrow load contract

The specifications of `KernelCheck::wrap_rel`, `wrap_dom`, `wrap_binder` and `consume_wrapper`
(`NativeRec.lean`, `NativeRecRules.lean`) are stated there at the table's keying and under the
unrestricted load contract. The only load these functions make is the `get_ci` of the head
constant of an application spine in `consume_wrapper`, whose answer matters only when it is a
definition. This module restates the specifications at any keying `κ` and any lookup `find?`,
assuming only `WrapLoads`: a `get_ci` at an address whose key resolves answers the constant
`find?` stores at that key, or a value that is not a definition. The resolution of the key comes
from the spine head being represented (`Tm.const_key_ne`). A scoped context whose calls are all
allowed gives `WrapLoads` at its keying (`WrapLoads.of_scoped`). -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam RecRule)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (ConsumeStar consumeWrapper wrapperArity lamFirstArity letFree)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

local macro "rec_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

/-- The loads `wrap_rel` makes under the keying `κ`: a `get_ci` at an address whose key resolves
answers the constant `find?` stores at that key, or a value that is not a definition. -/
def WrapLoads (c : Ctx) (κ : _root_.Address → KKey)
    (find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)) : Prop :=
  ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr → κ (ixAddr a) ≠ unresolvedKey →
      (∃ ci, find? (κ (ixAddr a)) = some ci ∧ CIPtrRep κ h' ptr ci) ∨
      (∀ v, loadValue h' ptr = .ok v → ∀ xs, v ≠ .construct kciEnum "Defn" xs)

/-- A scoped context all of whose calls are allowed answers every resolved `get_ci` with the
constant its environment stores at the key. -/
theorem WrapLoads.of_scoped {c : ScopedCtx} (hlf : ScopedLoadFacts c) (hall : ∀ cl, c.allowed cl) :
    WrapLoads c.toCtx c.κ c.env.find? := by
  intro addr ptr h h' cs a ev hg hrep hres
  exact Or.inl (hlf.getCI addr ptr h h' cs a ev (hall _) hres
    (CoreGood.ofRaw hg (fun cl _ => hall cl)) hrep)

private theorem wrapL_tm_lam_descent {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p w20 xb xm : SourceValue F} {steps : Nat}
    (hE : Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [w20, xb, xm]))
    (hdesc : RomBound.HeapDescent h (.enum kexprEnum) xb steps) :
    RomBound.HeapDescent h (.enum kexprEnum) p (steps + 1) := by
  cases hE with
  | @lam _ addr tp bp lp _ _ _ cell _ _ _ =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 _
    subst h1 h2
    exact .down cell (by simp [Value.type]) (by simp [RomBound.cellArgs]) hdesc
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact False.elim (load_cell_ne cell ld (by decide))

private theorem wrapL_tm_ptr_descent_zero {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hE : Tm κ d Γ h k E p) :
    RomBound.HeapDescent h (.enum kexprEnum) p 0 := by
  cases hE with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact .here cell (by simp [Value.type])

private theorem wrapL_hasFvar_false_of_fvarIdxLt_zero :
    ∀ {e : KExpr}, fvarIdxLt 0 e = true → e.hasFvar = false
  | .fvar _ _, h => by simp [fvarIdxLt] at h
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, wrapL_hasFvar_false_of_fvarIdxLt_zero h.1,
      wrapL_hasFvar_false_of_fvarIdxLt_zero h.2]
  | .lam t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, wrapL_hasFvar_false_of_fvarIdxLt_zero h.1,
      wrapL_hasFvar_false_of_fvarIdxLt_zero h.2]
  | .forallE t b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, wrapL_hasFvar_false_of_fvarIdxLt_zero h.1,
      wrapL_hasFvar_false_of_fvarIdxLt_zero h.2]
  | .letE t v b _, h => by
    simp only [fvarIdxLt, Bool.and_eq_true] at h
    simp [Expr.hasFvar, wrapL_hasFvar_false_of_fvarIdxLt_zero h.1.1,
      wrapL_hasFvar_false_of_fvarIdxLt_zero h.1.2, wrapL_hasFvar_false_of_fvarIdxLt_zero h.2]
  | .proj _ _ e, h => by
    simp only [fvarIdxLt] at h
    simpa [Expr.hasFvar] using wrapL_hasFvar_false_of_fvarIdxLt_zero h

private theorem wrapL_lam_first_arity_go {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xv steps → n + steps < 549755813888) →
        Tm κ 0 Γ h n E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          RomBound.HeapDescent h (.enum kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xv steps → n + steps < 549755813888) →
        Tm κ 0 Γ h n E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          RomBound.HeapDescent h (.enum kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h)
    (fun fname args h r h' cs ev ih hfn n E xv xk hargs hr hbnd_desc hE => by
      subst hfn hargs hr
      match Obs.«KernelCheck::lam_first_arity».obs ev with
      | .Lam_Succ_other (he118 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_other (he141 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_n0 (he186 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_other_other (he264 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .other (he287 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_Succ_Zero (w20 := w20) (x_b := xb) (x_m := xm) (x_z := xz)
          (cs82 := cs82) (v86 := v86)
          (ld12 := ld12) (ld47 := ld47) (ld71 := ld71)
          (op107 := op107) (ev84 := ev84) (hc109 := hc109) =>
        subst hc109
        obtain ⟨T, B, ℓ, rfl, _, hB, hℓ⟩ := hE.lam_of_load ld12
        obtain ⟨u, rfl, hu⟩ := Levels.rep_succ_of_load hℓ ld47
        obtain rfl := Levels.rep_zero_of_load hu ld71
        have hv86 : v86 = .field ((n + 1 : Nat) : F) := evalBinOp_add_one n op107
        rw [hv86] at ev84
        have hbnd_b : ∀ steps, RomBound.HeapDescent h (.enum kexprEnum) xb steps →
            (n + 1) + steps < 549755813888 := by
          intro steps hdb
          have hdp := wrapL_tm_lam_descent hE ld12 hdb
          have hlt := hbnd_desc (steps + 1) hdp
          omega
        obtain ⟨k_out, steps, hxk, hk_eq, hdb, hlam, hh⟩ :=
          ih _ _ _ _ _ _ (by rec_lt_calls) ev84 rfl (n + 1) B xb xk rfl rfl hbnd_b hB
        refine ⟨k_out, steps + 1, hxk, by omega, wrapL_tm_lam_descent hE ld12 hdb, ?_, hh⟩
        simpa [lamFirstArity, bmeta, Level.zeronessOf] using hlam
      | .BVar_other_n0 (x_i := xi) (y215 := y215)
          (ld12 := ld12) (hne201 := hne201) (op230 := op230) (op221 := op221)
          (he240 := he240) (he254 := he254) .. =>
        injection he240 with hxs; injection hxs with _ hxs; injection hxs with hxk _
        have hxk' : xk = .field (n : F) := hxk
        have hn_pos : 0 < n := by
          cases n with
          | zero => exact absurd rfl hne201
          | succ _ => omega
        cases n with
        | zero => omega
        | succ m =>
          have hy215 : y215 = .field (m : F) := evalBinOp_sub_succ m op230
          obtain ⟨i_f, rfl, _, hbvar⟩ := hE.bvar_of_load ld12
          rcases hbvar with ⟨hi_lt, rfl⟩ | ⟨_, hbad, _⟩
          · rw [hy215] at op221
            simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
              Except.ok.injEq, Value.field.injEq] at op221
            have hif : i_f = (m : F) := sub_eq_zero.mp op221
            have hn_lt : m + 1 < 549755813888 := by
              have := hbnd_desc 0 (wrapL_tm_ptr_descent_zero hE)
              omega
            have hval_i : ZMod.val i_f = m := by
              rw [hif]
              exact ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : m < 549755813888) (by decide))
            refine ⟨m + 1, 0, hxk', by omega, wrapL_tm_ptr_descent_zero hE, ?_, he254⟩
            simp [lamFirstArity, hval_i]
          · omega)

/-- Soundness of `KernelCheck::consume_wrapper` returning `(.field 1, x_a)` at the keying `κ`:
the head constant of the spine is a stored definition whose arity the spine meets, and the
result represents the argument the wrapper projects. -/
theorem wrapL_consume_wrapper_one_spec {c : Ctx} {κ : _root_.Address → KKey}
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)} {d : Nat} {Γ : Nat → KExpr}
    {T : KExpr} {xt xa : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlf : WrapLoads c κ find?) (hgood : Good c cs)
    (hT : Tm κ d Γ h 0 T xt)
    (ev : ObsFn W "KernelCheck::consume_wrapper" [xt] h (.tuple [.field 1, xa]) h' cs) :
    ∃ A : KExpr, consumeWrapper find? T = some A ∧ Tm κ d Γ h' 0 A xa := by
  match Obs.«KernelCheck::consume_wrapper».obsx ev with
  | .Const_Cons_Defn_n1_bind_other (he276 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_Cons_Defn_other (he299 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_Cons_other (he323 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_other (he347 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .other (he371 := he) .. =>
    injection he with hxs; injection hxs with h10 _
    exact absurd (Value.field.inj h10) one_ne_zero
  | .Const_Cons_Defn_n1_bind_n0 (m2 := m2) (cs12 := cs12) (x_h := xh) (x_args := xargs)
      (x_w := xw) (w55 := w55) (x_a := xa') (x_rest := xrest) (m96 := m96) (p104 := p104)
      (cs110 := cs110) (w127 := w127) (w128 := w128) (x_v := xv) (w129 := w129) (w130 := w130)
      (m157 := m157) (cs168 := cs168) (x_k := xk) (y214 := y214) (x222 := x222)
      (m224 := m224) (cs233 := cs233)
      (ev14 := ev14) (ld47 := ld47) (ld77 := ld77) (ev112 := ev112) (ld106 := ld106)
      (ev170 := ev170) (ev235 := ev235) (op229 := op229) (op220 := op220)
      (he252 := he252) (he266 := he266) (hc267 := hc267) =>
    subst hc267 he266
    injection he252 with hxs; injection hxs with _ hxs; injection hxs with hxa_eq _
    subst hxa_eq
    have hbnd_sp : IxVM.Consistency.Bounded cs12 :=
      RomBound.bounded_mono hgood.2 (fun z hz => by simp [hz])
    obtain ⟨hd, sp, H, As, hpair, hH, hAs, rfl⟩ :=
      SubstAux.gall κ .collect_spine _ _ _ _ _ ev14 xt rfl hbnd_sp d Γ 0 T hT
    injection hpair with hlist; injection hlist with hhd hlist; injection hlist with hsp _
    subst hhd hsp
    obtain ⟨aw, us, rfl, haw, _, _, _⟩ := hH.const_of_load ld47
    obtain ⟨A, rest, rfl, hA, hrest⟩ := RepList.cons_of_load hAs ld77
    have hg_ci : Good c cs110 := hgood.sub (fun z hz => by simp [hz])
    obtain ⟨ci, hfind, p_v, hp_ld, hci_rep⟩ :
        ∃ ci, find? (κ (ixAddr aw)) = some ci ∧ CIPtrRep κ m96 p104 ci := by
      rcases hlf xw p104 m2 m96 cs110 aw ev112 hg_ci haw hH.const_key_ne with hl | hnd
      · exact hl
      · exact (hnd _ ld106 _ rfl).elim
    rw [hp_ld] at ld106
    injection ld106 with hv_eq
    subst hv_eq
    obtain ⟨cv, V, hn, rfl, _, hV⟩ := CIRep.defn_inv hci_rep
    have e_ci := ev112.heap_extends
    have hbnd_call_lfa :
        ∀ steps, RomBound.HeapDescent m96 (.enum kexprEnum) xv steps →
          0 + steps < 549755813888 := by
      intro steps hdesc
      have hlt := RomBound.bounded_descent_lt hgood.2
        (c := ⟨"KernelCheck::lam_first_arity", [xv, .field 0], m96⟩)
        (by simp) List.mem_cons_self hdesc
      simpa using hlt
    obtain ⟨k_out, steps_v, hxk, hk_steps, hdesc_xv, hlam_pos, hm157⟩ :=
      wrapL_lam_first_arity_go _ _ _ _ _ _ ev170 rfl 0 (posOf cv.levelParams V) xv xk
        rfl rfl hbnd_call_lfa (hV 0 (fun _ => default))
    subst m157
    rw [lamFirstArity_posOf] at hlam_pos
    have hrest_m96 : RepList kexprListEnum (fun h E p => Tm κ d Γ h 0 E p) m96 rest xrest :=
      repList_heapMono₂ kexprListEnum (fun _ _ _ _ ext r => r.mono ext) e_ci hrest
    have hlen_rest_lt : rest.length < 549755813888 :=
      RomBound.bounded_length_lt hgood.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xrest], m96⟩)
        (by simp) List.mem_cons_self hrest_m96
    obtain ⟨hx222, rfl⟩ :=
      Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
        (R := fun h E p => Tm κ d Γ h 0 E p)
        (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev235)
        (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hrest_m96)
    rw [hx222] at op229
    have hy214 : y214 = .field ((rest.length + 1 : Nat) : F) :=
      evalBinOp_add_one rest.length op229
    rw [hxk, hy214] at op220
    simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
      Except.ok.injEq, Value.field.injEq] at op220
    have hk_lt : k_out < 549755813888 := by
      have := hbnd_call_lfa steps_v hdesc_xv
      omega
    have hk_eq : k_out = rest.length + 1 := by
      have hf : (k_out : F) = ((rest.length + 1 : Nat) : F) := sub_eq_zero.mp op220
      have hv1 : ((k_out : F)).val = k_out :=
        ZMod.val_natCast_of_lt (Nat.lt_trans hk_lt (by decide))
      have hv2 : (((rest.length + 1 : Nat) : F)).val = rest.length + 1 :=
        ZMod.val_natCast_of_lt (Nat.lt_trans (show rest.length + 1 < 549755813889 by omega) (by decide))
      have hv := congrArg ZMod.val hf
      omega
    subst hk_eq
    have hwrap : wrapperArity find? (κ (ixAddr aw)) = some (rest.length + 1) := by
      simp [wrapperArity, hfind, hlam_pos]
    exact ⟨A, Ix.Kernel.Semantics.consumeWrapper_mkAppN hwrap, hA.mono e_ci⟩

private theorem wrapL_rel_family {c : Ctx} {κ : _root_.Address → KKey}
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)} (hlf : WrapLoads c κ find?) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 → Good c cs →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (G D : KExpr) (xg xd : SourceValue F),
          args = [.field 0, xg, xd] → Tm κ d Γ h 0 G xg → Tm κ d Γ h 0 D xd →
          WrapTSem find? G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T T2 : KExpr) (xt xt2 : SourceValue F),
          args = [.field 0, xt, xt2] → Tm κ d Γ h 0 T xt → Tm κ d Γ h 0 T2 xt2 →
          ∃ A : KExpr, ConsumeStar find? T A ∧ WrapTSem find? A T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel)
          (xt xb xm xt2 xb2 xm2 : SourceValue F),
          args = [.field 0, xt, xb, xm, xt2, xb2, xm2] →
          Tm κ d Γ h 0 T xt → Tm κ d Γ h 1 B xb → RepKLevel h ℓ xm →
          Tm κ d Γ h 0 T2 xt2 → Tm κ d Γ h 1 B2 xb2 → RepKLevel h ℓ2 xm2 →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ A : KExpr, ConsumeStar find? T A ∧ WrapTSem find? A T2) ∧
          WrapTSem find? B B2)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 → Good c cs →
      ((fname = "KernelCheck::wrap_rel" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (G D : KExpr) (xg xd : SourceValue F),
          args = [.field 0, xg, xd] → Tm κ d Γ h 0 G xg → Tm κ d Γ h 0 D xd →
          WrapTSem find? G D) ∧
       (fname = "KernelCheck::wrap_dom" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T T2 : KExpr) (xt xt2 : SourceValue F),
          args = [.field 0, xt, xt2] → Tm κ d Γ h 0 T xt → Tm κ d Γ h 0 T2 xt2 →
          ∃ A : KExpr, ConsumeStar find? T A ∧ WrapTSem find? A T2) ∧
       (fname = "KernelCheck::wrap_binder" →
        ∀ (d : Nat) (Γ : Nat → KExpr) (T B T2 B2 : KExpr) (ℓ ℓ2 : KLevel)
          (xt xb xm xt2 xb2 xm2 : SourceValue F),
          args = [.field 0, xt, xb, xm, xt2, xb2, xm2] →
          Tm κ d Γ h 0 T xt → Tm κ d Γ h 1 B xb → RepKLevel h ℓ xm →
          Tm κ d Γ h 0 T2 xt2 → Tm κ d Γ h 1 B2 xb2 → RepKLevel h ℓ2 xm2 →
          (bmeta ℓ).pw = (bmeta ℓ2).pw ∧
          (∃ A : KExpr, ConsumeStar find? T A ∧ WrapTSem find? A T2) ∧
          WrapTSem find? B B2)))
    (fun fname args h r h' cs ev ih hr hgood => by
      subst hr
      refine ⟨fun hfn d Γ G D xg xd hargs hG hD => ?_,
        fun hfn d Γ T T2 xt xt2 hargs hT hT2 => ?_,
        fun hfn d Γ T B T2 B2 ℓ ℓ2 xt xb xm xt2 xb2 xm2 hargs hT hB hℓ hT2 hB2 hℓ2 => ?_⟩
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he351 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_App_other (he358 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Lam_other (he476 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Forall_other (he594 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Proj_Proj_other (he746 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_Proj_other (he753 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_other (he166 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_other (he173 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_other (he180 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_Let (he224 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_n1 (x_v := xv) (x_b := xb) (x_v2 := xv2) (x_b2 := xb2)
            (m70 := m70) (cs81 := cs81) (m105 := m105) (cs116 := cs116) (cs142 := cs142)
            (ld12 := ld12) (ld46 := ld46) (ev83 := ev83) (ev118 := ev118) (ev144 := ev144)
            (hc161 := hc161) .. =>
          -- a `let` against a `let`: the values and the bodies are related, so their
          -- expansions (what `Tm` reads a `let` as) are
          subst hc161
          obtain ⟨_, V, B, rfl, _, hV, hB⟩ := hG.letE_of_load ld12
          obtain ⟨_, V2, B2, rfl, _, hV2, hB2⟩ := hD.letE_of_load ld46
          have hB : Tm κ d Γ h 1 B xb := hB
          have hB2 : Tm κ d Γ h 1 B2 xb2 := hB2
          have e1 := ev83.heap_extends
          have e2 := ev118.heap_extends
          have hwV := (ih _ _ _ _ _ _ (by rec_lt_calls) ev118 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ V V2 xv xv2 rfl
            (hV.mono e1) (hV2.mono e1)
          let Γ' := Ghost.extend Γ d (.sort .zero)
          have hB_open : Tm κ (d + 1) Γ' m105 0 (B.instantiate1 (.fvar d (.sort .zero))) xb :=
            (hB.mono (e1.trans e2)).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hB2_open : Tm κ (d + 1) Γ' m105 0 (B2.instantiate1 (.fvar d (.sort .zero))) xb2 :=
            (hB2.mono (e1.trans e2)).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hw_open := (ih _ _ _ _ _ _ (by rec_lt_calls) ev144 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl (d + 1) Γ'
            (B.instantiate1 (.fvar d (.sort .zero))) (B2.instantiate1 (.fvar d (.sort .zero)))
            xb xb2 rfl hB_open hB2_open
          have hw_abs := hw_open.abstract1 d 0
          rw [abstract1_instantiate1_cancel (.sort .zero) 0 (tm_fvarIdxLt hB) hB.looseBVarsBounded,
            abstract1_instantiate1_cancel (.sort .zero) 0 (tm_fvarIdxLt hB2) hB2.looseBVarsBounded]
            at hw_abs
          rw [instShift_eq_instantiate1 hV.looseBVarsBounded 0 B,
            instShift_eq_instantiate1 hV2.looseBVarsBounded 0 B2]
          exact WrapTSem.instantiate1 hwV hw_abs 0
        | .other_other_App_App_n1 (x_f := xf) (x_a := xa) (x_f2 := xf2) (x_a2 := xa2)
            (m290 := m240) (cs301 := cs251) (cs327 := cs277)
            (ld242 := ld192) (ld271 := ld221) (ev303 := ev253) (ev329 := ev279)
            (hc346 := hc296) .. =>
          subst hc296
          obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := hG.app_of_load ld192
          obtain ⟨Ef2, Ea2, rfl, hEf2, hEa2⟩ := hD.app_of_load ld221
          have e1 := ev253.heap_extends
          exact .app
            ((ih _ _ _ _ _ _ (by rec_lt_calls) ev253 rfl
              (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ Ef Ef2 xf xf2 rfl hEf hEf2)
            ((ih _ _ _ _ _ _ (by rec_lt_calls) ev279 rfl
              (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ Ea Ea2 xa xa2 rfl
              (hEa.mono e1) (hEa2.mono e1))
        | .other_other_Lam_Lam (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs420 := cs370)
            (ld242 := ld192) (ld394 := ld344) (ev422 := ev372) (hc471 := hc421) .. =>
          subst hc421
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hG.lam_of_load ld192
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := hD.lam_of_load ld344
          obtain ⟨hpw, ⟨A, hs, hw_dom⟩, hw_body⟩ :=
            (ih _ _ _ _ _ _ (by rec_lt_calls) ev372 rfl
              (hgood.sub fun z hz => by simp [hz])).2.2 rfl d Γ T B T2 B2 ℓ ℓ2
              xt xb xm xt2 xb2 xm2 rfl hT hB hℓ hT2 hB2 hℓ2
          exact .lam hpw hs hw_dom hw_body
        | .other_other_Forall_Forall (x_t := xt) (x_b := xb) (x_m := xm)
            (x_t2 := xt2) (x_b2 := xb2) (x_m2 := xm2) (cs538 := cs488)
            (ld242 := ld192) (ld512 := ld462) (ev540 := ev490) (hc589 := hc539) .. =>
          subst hc539
          obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hG.forallE_of_load ld192
          obtain ⟨T2, B2, ℓ2, rfl, hT2, hB2, hℓ2⟩ := hD.forallE_of_load ld462
          obtain ⟨hpw, ⟨A, hs, hw_dom⟩, hw_body⟩ :=
            (ih _ _ _ _ _ _ (by rec_lt_calls) ev490 rfl
              (hgood.sub fun z hz => by simp [hz])).2.2 rfl d Γ T B T2 B2 ℓ ℓ2
              xt xb xm xt2 xb2 xm2 rfl hT hB hℓ hT2 hB2 hℓ2
          exact .forallE hpw hs hw_dom hw_body
        | .other_other_Proj_Proj_n1 (x_s := xs) (x_i := xi) (x_e := xe)
            (x_s2 := xs2) (x_i2 := xi2) (x_e2 := xe2) (m654 := m604)
            (x662 := x612) (y663 := y613) (m664 := m614)
            (cs673 := cs623) (cs695 := cs645) (v698 := v648) (cs722 := cs672)
            (ld242 := ld192) (ld630 := ld580) (ev675 := ev625) (op712 := op662)
            (ev697 := ev647) (op669 := op619) (ev724 := ev674) (hc741 := hc691) .. =>
          subst hc691
          obtain ⟨sa, fa, Ea, rfl, rfl, hsa, hEa⟩ := hG.proj_of_load ld192
          obtain ⟨sb, fb, Eb, rfl, rfl, hsb, hEb⟩ := hD.proj_of_load ld580
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev625 hsa hsb
          obtain ⟨hiz, rfl⟩ := Lib.is_zero_spec ev647
          have hs_eq : sa = sb := by
            by_cases hab : sa = sb
            · exact hab
            · rw [ite_eq_right hab] at haddr
              rw [haddr, hiz] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          subst hs_eq
          have hv648 : v648 = .field 0 := by
            by_cases h0 : v648 = .field 0
            · exact h0
            · rw [hiz, ite_eq_right h0, haddr] at op619
              simp [evalBinOp, bind, Except.bind, pure, Except.pure] at op619
          rw [hv648] at op662
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op662
          have hfeq : fa = fb := sub_eq_zero.mp op662
          subst hfeq
          exact .proj
            ((ih _ _ _ _ _ _ (by rec_lt_calls) ev674 rfl
              (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ Ea Eb xe xe2 rfl hEa hEb)
        | .other_other_other (cs763 := cs713) (ev765 := ev715) (hc782 := hc732) .. =>
          subst hc732
          exact (kexpr_struct_eq_tm_one hG hD ev715).toWrapTSem find?
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_dom».obsx ev with
        | .other_n0_other_other (he_vjzsmrqa := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other_other_n1_bind (hne_trdykyhf := hsm) .. | .other_other_other (hne_trdykyhf := hsm) .. =>
          exact absurd rfl hsm
        | .Let (cs41 := cs41) (ev43 := ev43) (hc60 := hc60) .. =>
          -- a domain that is a `let` is compared whole
          subst hc60
          have hw := (ih _ _ _ _ _ _ (by rec_lt_calls) ev43 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ T T2 xt xt2 rfl hT hT2
          exact ⟨T, .refl T, hw⟩
        | .other_n0_n1 (cs_inoibkuh := cs103) (ev_teknbelh := ev105) (hc_mhrqvtgu := hc128) .. =>
          subst hc128
          have hw := (ih _ _ _ _ _ _ (by rec_lt_calls) ev105 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl d Γ T T2 xt xt2 rfl hT hT2
          exact ⟨T, .refl T, hw⟩
        | .other_n0_other_n1_bind (m_fwvfxwkq := m92) (cs_inoibkuh := cs103) (m_iludgrvx := m134)
            (cs_szysaksf := cs145) (x_a := xa) (cs_bhijnlkz := cs177)
            (ev_teknbelh := ev105) (ev_tyrbnlfr := ev147) (ev_jqflmfnr := ev179)
            (hc_uuoaavue := hc196) .. =>
          subst hc196
          have e1 := ev105.heap_extends
          have e2 := ev147.heap_extends
          obtain ⟨A₁, hc₁, hA₁⟩ := wrapL_consume_wrapper_one_spec hlf
            (hgood.sub fun z hz => by simp [hz]) (hT.mono e1) ev147
          obtain ⟨A₂, hs₂, hw₂⟩ := (ih _ _ _ _ _ _ (by rec_lt_calls) ev179 rfl
            (hgood.sub fun z hz => by simp [hz])).2.1 rfl d Γ A₁ T2 xa xt2 rfl
            hA₁ (hT2.mono (e1.trans e2))
          exact ⟨A₂, .step hc₁ hs₂, hw₂⟩
      · subst hfn hargs
        match Obs.«KernelCheck::wrap_binder».obs ev with
        | .n1_other (he98 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .other (he105 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .n1_n1 (m2 := m2) (cs13 := cs13) (m37 := m37) (cs48 := cs48) (cs74 := cs74)
            (ev15 := ev15) (ev50 := ev50) (ev76 := ev76) (hc93 := hc93) =>
          subst hc93
          have hpw := pw_eq_one hℓ hℓ2 ev15
          have e1 := ev15.heap_extends
          have e2 := ev50.heap_extends
          have hdom := (ih _ _ _ _ _ _ (by rec_lt_calls) ev50 rfl
            (hgood.sub fun z hz => by simp [hz])).2.1 rfl d Γ T T2 xt xt2 rfl
            (hT.mono e1) (hT2.mono e1)
          let Γ' := Ghost.extend Γ d (.sort .zero)
          have hB_open : Tm κ (d + 1) Γ' m37 0 (B.instantiate1 (.fvar d (.sort .zero))) xb :=
            (hB.mono (e1.trans e2)).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hB2_open : Tm κ (d + 1) Γ' m37 0 (B2.instantiate1 (.fvar d (.sort .zero))) xb2 :=
            (hB2.mono (e1.trans e2)).open_body (Ghost.extend_at _ _ _) (Ghost.extend_below _ _ _)
          have hw_open := (ih _ _ _ _ _ _ (by rec_lt_calls) ev76 rfl
            (hgood.sub fun z hz => by simp [hz])).1 rfl (d + 1) Γ'
            (B.instantiate1 (.fvar d (.sort .zero))) (B2.instantiate1 (.fvar d (.sort .zero)))
            xb xb2 rfl hB_open hB2_open
          have hw_abs := hw_open.abstract1 d 0
          rw [abstract1_instantiate1_cancel (.sort .zero) 0 (tm_fvarIdxLt hB) hB.looseBVarsBounded,
            abstract1_instantiate1_cancel (.sort .zero) 0 (tm_fvarIdxLt hB2) hB2.looseBVarsBounded]
            at hw_abs
          exact ⟨hpw, hdom, hw_abs⟩)

/-- `KernelCheck::wrap_rel` returning `.field 1` on two closed heap terms at the keying `κ`
certifies `WrapRelSem find? G D`. -/
theorem wrapL_rel_spec {c : Ctx} {κ : _root_.Address → KKey}
    {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)} {Γ : Nat → KExpr} {G D : KExpr}
    {xg xd : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlf : WrapLoads c κ find?) (hgood : Good c cs)
    (hG : Tm κ 0 Γ h 0 G xg) (hD : Tm κ 0 Γ h 0 D xd)
    (ev : ObsFn W "KernelCheck::wrap_rel" [.field 0, xg, xd] h (.field 1) h' cs) :
    WrapRelSem find? G D :=
  ((wrapL_rel_family hlf _ _ _ _ _ _ ev rfl hgood).1 rfl 0 Γ G D xg xd rfl hG hD).toWrapRelSem
    (wrapL_hasFvar_false_of_fvarIdxLt_zero (tm_fvarIdxLt hG))

private theorem wrapL_getAppFn_mkAppN_eq : ∀ (As : List KExpr) (f : KExpr),
    (Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [wrapL_getAppFn_mkAppN_eq As (.app f a)]
    rfl

/-- `KernelCheck::wrap_rel` returning `.field 1` on two application spines over literal constant
heads compares the heads' level lists literally. -/
theorem wrapL_rel_appHeadConstLvls {a_g a_d : Bytes.Address} {ls_g ls_d : List KLevel} :
    ∀ {xg xd : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      AppHeadConstLvls h a_g ls_g xg →
      AppHeadConstLvls h a_d ls_d xd →
      ObsFn W "KernelCheck::wrap_rel" [.field 0, xg, xd] h (.field 1) h' cs →
      ls_g = ls_d := by
  intro xg xd h h' cs hg hd ev
  induction hg generalizing xd h' cs with
  | const cell_g _ rls_g =>
    match Obs.«KernelCheck::wrap_rel».obs ev with
    | .other_other_App_App_other (he351 := he) ..
    | .other_other_App_other (he358 := he) ..
    | .other_other_Lam_other (he476 := he) ..
    | .other_other_Forall_other (he594 := he) ..
    | .other_other_Proj_Proj_other (he746 := he) ..
    | .other_other_Proj_other (he753 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Let_Let_n1_n1 (ld12 := ld) ..
    | .Let_Let_n1_other (ld12 := ld) ..
    | .Let_Let_other (ld12 := ld) ..
    | .Let_other (ld12 := ld) ..
    | .other_other_App_App_n1 (ld242 := ld) ..
    | .other_other_Lam_Lam (ld242 := ld) ..
    | .other_other_Forall_Forall (ld242 := ld) ..
    | .other_other_Proj_Proj_n1 (ld242 := ld) .. =>
      exact (load_cell_ne cell_g ld (by decide)).elim
    | .other_Let (ld198 := ld) .. =>
      cases hd with
      | const cell_d _ _ | app cell_d _ =>
        exact (load_cell_ne cell_d ld (by decide)).elim
    | .other_other_other (ev765 := ev715) .. =>
      rcases Obs.«KernelCheck::kexpr_struct_eq».obs ev715 with
        ⟨_, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, he, _, _⟩ |
        ⟨x_ca, x_lsa, x_cb, x_lsb, m202, _, _, ld12, ld183, ev215, ev241, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, ld12, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, ld12, _, _, _⟩ |
        ⟨_, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he, _, _⟩
      all_goals try exact absurd (Value.field.inj he) one_ne_zero
      all_goals try exact (load_cell_ne cell_g ld12 (by decide)).elim
      · obtain ⟨-, hxs1⟩ := load_cell cell_g ld12
        injection hxs1 with _ hxs1
        injection hxs1 with hlsa
        rw [hlsa] at rls_g
        cases hd with
        | app cell_d _ => exact (load_cell_ne cell_d ld183 (by decide)).elim
        | const cell_d _ rls_d =>
          obtain ⟨-, hxs2⟩ := load_cell cell_d ld183
          injection hxs2 with _ hxs2
          injection hxs2 with hlsb
          rw [hlsb] at rls_d
          exact (level_list_struct_eq_one
            (rls_g.mono ev215.heap_extends) (rls_d.mono ev215.heap_extends) ev241).1
  | app cell_g rf_g ih =>
    match Obs.«KernelCheck::wrap_rel».obs ev with
    | .other_other_App_App_other (he351 := he) ..
    | .other_other_App_other (he358 := he) ..
    | .other_other_Lam_other (he476 := he) ..
    | .other_other_Forall_other (he594 := he) ..
    | .other_other_Proj_Proj_other (he746 := he) ..
    | .other_other_Proj_other (he753 := he) .. =>
      exact absurd (Value.field.inj he) one_ne_zero
    | .Let_Let_n1_n1 (ld12 := ld) ..
    | .Let_Let_n1_other (ld12 := ld) ..
    | .Let_Let_other (ld12 := ld) ..
    | .Let_other (ld12 := ld) ..
    | .other_other_Lam_Lam (ld242 := ld) ..
    | .other_other_Forall_Forall (ld242 := ld) ..
    | .other_other_Proj_Proj_n1 (ld242 := ld) .. =>
      exact (load_cell_ne cell_g ld (by decide)).elim
    | .other_Let (ld198 := ld) .. =>
      cases hd with
      | const cell_d _ _ | app cell_d _ =>
        exact (load_cell_ne cell_d ld (by decide)).elim
    | .other_other_other (ld242 := ld192) (hne361 := hne311) .. =>
      rw [loadValue_enum_cell cell_g] at ld192
      injection ld192 with hv
      exact (hne311 [_, _] rfl hv.symm).elim
    | .other_other_App_App_n1 (ld242 := ld192) (ld271 := ld221) (ev303 := ev253) .. =>
      obtain ⟨-, hxs1⟩ := load_cell cell_g ld192
      injection hxs1 with hfg _
      cases hd with
      | const cell_d _ _ => exact (load_cell_ne cell_d ld221 (by decide)).elim
      | app cell_d rf_d =>
        obtain ⟨-, hxs2⟩ := load_cell cell_d ld221
        injection hxs2 with hfd _
        rw [← hfg, ← hfd] at ev253
        exact ih rf_d ev253

/-- `KernelCheck::wrap_rel` returning `.field 1` on a generated left side whose `m`-th binder
domain is an application of the inductive `T`, against a right side of the same binder shape,
compares the two domains' head level lists literally: the domain of `T` is not consumed as a
wrapper, since `T` is stored as an inductive, not a definition. -/
theorem wrapL_rel_forallDomHeadLvls
    {c : Ctx} {κ : _root_.Address → KKey} {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)}
    {T : KKey} {a_g a_d : Bytes.Address} {ls_g ls_d : List KLevel}
    (hlf : WrapLoads c κ find?)
    (hT_ind : ∃ cv caps, find? T = some (.indInfo cv caps)) :
    ∀ (m : Nat) {k : Nat} {xg xd : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Good c cs →
      ForallDomHeadLvls κ 0 (fun _ => default) h T a_g ls_g m k xg →
      ForallRightHeadLvls h a_d ls_d m xd →
      ObsFn W "KernelCheck::wrap_rel" [.field 0, xg, xd] h (.field 1) h' cs →
      ls_g = ls_d
  | 0, k, xg, xd, h, h', cs, hgood, hg, hd, ev => by
    cases hg with
    | @zero _ _ _ _ _ dom cell_g hdom hfn hhead_g =>
      cases hd with
      | zero cell_d hhead_d =>
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he351 := he) ..
        | .other_other_App_other (he358 := he) ..
        | .other_other_Lam_other (he476 := he) ..
        | .other_other_Forall_other (he594 := he) ..
        | .other_other_Proj_Proj_other (he746 := he) ..
        | .other_other_Proj_other (he753 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_n1 (ld12 := ld) ..
        | .Let_Let_n1_other (ld12 := ld) ..
        | .Let_Let_other (ld12 := ld) ..
        | .Let_other (ld12 := ld) ..
        | .other_other_App_App_n1 (ld242 := ld) ..
        | .other_other_Lam_Lam (ld242 := ld) ..
        | .other_other_Proj_Proj_n1 (ld242 := ld) .. =>
          exact (load_cell_ne cell_g ld (by decide)).elim
        | .other_Let (ld198 := ld) .. =>
          exact (load_cell_ne cell_d ld (by decide)).elim
        | .other_other_other (ld242 := ld192) (hne597 := hne547) .. =>
          rw [loadValue_enum_cell cell_g] at ld192
          injection ld192 with hv
          exact (hne547 [_, _, _] rfl hv.symm).elim
        | .other_other_Forall_Forall (ld242 := ld192) (ld512 := ld462)
            (ev540 := ev490) (hc589 := hc539) .. =>
          obtain ⟨-, hxs1⟩ := load_cell cell_g ld192
          injection hxs1 with htg _
          obtain ⟨-, hxs2⟩ := load_cell cell_d ld462
          injection hxs2 with htd _
          rw [htg] at hdom hhead_g
          rw [htd] at hhead_d
          match Obs.«KernelCheck::wrap_binder».obs ev490 with
          | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
            exact absurd (Value.field.inj he) one_ne_zero
          | .n1_n1 (m2 := m2) (cs48 := cs48) (ev15 := ev15) (ev50 := ev50) (hc93 := hc93) .. =>
            have e1 := ev15.heap_extends
            match Obs.«KernelCheck::wrap_dom».obsx ev50 with
            | .other_n0_other_other (he_vjzsmrqa := he) .. =>
              exact absurd (Value.field.inj he) one_ne_zero
            | .other_other_n1_bind (hne_trdykyhf := hsm) ..
            | .other_other_other (hne_trdykyhf := hsm) .. =>
              exact absurd rfl hsm
            | .Let (ld12 := ld12) .. =>
              cases hhead_g with
              | const cg _ _ | app cg _ =>
                exact (load_cell_ne (e1.getElem?_eq cg) ld12 (by decide)).elim
            | .other_n0_n1 (ev_teknbelh := ev105) .. =>
              exact wrapL_rel_appHeadConstLvls (hhead_g.mono e1) (hhead_d.mono e1) ev105
            | .other_n0_other_n1_bind (m_fwvfxwkq := m92) (cs_szysaksf := cs145)
                (ev_teknbelh := ev105) (ev_tyrbnlfr := ev147) (hc_uuoaavue := hc196) .. =>
              have hgood_cw : Good c cs145 :=
                hgood.sub (fun z hz => by subst hc539 hc93 hc196; simp [hz])
              match Obs.«KernelCheck::consume_wrapper».obsx ev147 with
              | .Const_Cons_Defn_n1_bind_other (he276 := he) ..
              | .Const_Cons_Defn_other (he299 := he) ..
              | .Const_Cons_other (he323 := he) ..
              | .Const_other (he347 := he) ..
              | .other (he371 := he) .. =>
                injection he with hxs; injection hxs with h10 _
                exact absurd (Value.field.inj h10) one_ne_zero
              | .Const_Cons_Defn_n1_bind_n0 (m2 := mc2) (cs12 := cs12)
                  (x_w := xw) (m96 := m96) (p104 := p104) (cs110 := cs110)
                  (ev14 := ev14) (ld47 := ld47) (ev112 := ev112) (ld106 := ld106)
                  (hc267 := hc267) .. =>
                have hbnd_sp : IxVM.Consistency.Bounded cs12 :=
                  RomBound.bounded_mono hgood_cw.2 (fun z hz => by subst hc267; simp [hz])
                have hdom_92 : Tm κ 0 (fun _ => default) m92 k dom _ :=
                  (hdom.mono e1).mono ev105.heap_extends
                obtain ⟨hd_sp, sp, H, As, hpair, hH, _, heq_dom⟩ :=
                  SubstAux.gall κ .collect_spine _ _ _ _ _ ev14 _ rfl hbnd_sp
                    0 (fun _ => default) k dom hdom_92
                injection hpair with hlist; injection hlist with hhd _
                subst hhd
                obtain ⟨aw, us, rfl, haw, _, _, _⟩ := hH.const_of_load ld47
                have hg_ci : Good c cs110 :=
                  hgood_cw.sub (fun z hz => by subst hc267; simp [hz])
                rcases hlf xw p104 mc2 m96 cs110 aw ev112 hg_ci haw hH.const_key_ne with
                  ⟨ci, hfind, p_v, hp_ld, hci_rep⟩ | hnd
                · rw [hp_ld] at ld106
                  injection ld106 with hv_eq; subst hv_eq
                  obtain ⟨_, _, _, rfl, _, _⟩ := CIRep.defn_inv hci_rep
                  rw [heq_dom, wrapL_getAppFn_mkAppN_eq] at hfn
                  injection hfn with hkey_eq _
                  rw [hkey_eq] at hfind
                  obtain ⟨_, _, hfind_ind⟩ := hT_ind
                  rw [hfind] at hfind_ind
                  cases hfind_ind
                · exact (hnd _ ld106 _ rfl).elim
  | m + 1, k, xg, xd, h, h', cs, hgood, hg, hd, ev => by
    cases hg with
    | succ cell_g hrest_g =>
      cases hd with
      | succ cell_d hrest_d =>
        match Obs.«KernelCheck::wrap_rel».obs ev with
        | .other_other_App_App_other (he351 := he) ..
        | .other_other_App_other (he358 := he) ..
        | .other_other_Lam_other (he476 := he) ..
        | .other_other_Forall_other (he594 := he) ..
        | .other_other_Proj_Proj_other (he746 := he) ..
        | .other_other_Proj_other (he753 := he) .. =>
          exact absurd (Value.field.inj he) one_ne_zero
        | .Let_Let_n1_n1 (ld12 := ld) ..
        | .Let_Let_n1_other (ld12 := ld) ..
        | .Let_Let_other (ld12 := ld) ..
        | .Let_other (ld12 := ld) ..
        | .other_other_App_App_n1 (ld242 := ld) ..
        | .other_other_Lam_Lam (ld242 := ld) ..
        | .other_other_Proj_Proj_n1 (ld242 := ld) .. =>
          exact (load_cell_ne cell_g ld (by decide)).elim
        | .other_Let (ld198 := ld) .. =>
          exact (load_cell_ne cell_d ld (by decide)).elim
        | .other_other_other (ld242 := ld192) (hne597 := hne547) .. =>
          rw [loadValue_enum_cell cell_g] at ld192
          injection ld192 with hv
          exact (hne547 [_, _, _] rfl hv.symm).elim
        | .other_other_Forall_Forall (ld242 := ld192) (ld512 := ld462)
            (ev540 := ev490) (hc589 := hc539) .. =>
          obtain ⟨-, hxs1⟩ := load_cell cell_g ld192
          injection hxs1 with _ hxs1; injection hxs1 with hbg _
          obtain ⟨-, hxs2⟩ := load_cell cell_d ld462
          injection hxs2 with _ hxs2; injection hxs2 with hbd _
          rw [hbg] at hrest_g
          rw [hbd] at hrest_d
          match Obs.«KernelCheck::wrap_binder».obs ev490 with
          | .n1_other (he98 := he) .. | .other (he105 := he) .. =>
            exact absurd (Value.field.inj he) one_ne_zero
          | .n1_n1 (ev15 := ev15) (ev50 := ev50) (cs74 := cs74) (ev76 := ev76) (hc93 := hc93) .. =>
            have e12 := ev15.heap_extends.trans ev50.heap_extends
            have hgood76 : Good c cs74 :=
              hgood.sub (fun z hz => by subst hc539 hc93; simp [hz])
            exact wrapL_rel_forallDomHeadLvls hlf hT_ind m hgood76
              (hrest_g.mono e12) (hrest_d.mono e12) ev76

end IxVM.Refinement.Decl
