import IxVMRefinement.Assembly.GuardRawRep
import IxVMRefinement.Callees.Loads
import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Infer.Basic

/-! # Scoped representation preservation by the classifier head operation

The classifier's data-only normalization preserves a term representation under the actual
prefix's scoped load facts. It also preserves a represented input already headed by a sort,
Pi or lambda. No reduction or typing judgement is concluded: raw data beta need not have the
licence required by `Rules.Red`.
-/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.KernelLevels (RepKLevelList)

set_option maxHeartbeats 2400000

/-- Actual definition loading and structural substitution return a represented expression. -/
theorem definition_value_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {a : Bytes.Address} {ps : List KLevel}
    {ap params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hg : CoreGood c cs) (ha : Bytes.RepAddressRef addrTy h a ap)
    (hr : c.κ (ixAddr a) ≠ unresolvedKey) (hp : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::definition_value" [ap, params] h r h' cs) :
    ∃ E, Tm c.κ d Γ h' 0 E r := by
  match Obs.«KernelGuard::definition_value».obs ev with
  | .run (cs15 := loads) (ev17 := load) (ld11 := ld) (ev81 := len)
      (ev103 := inst) (hc120 := allCalls) .. =>
    have hsub : ∀ cl ∈ loads, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
    have hallow : c.allowed ⟨"Ingress::get_ci", [ap], h⟩ :=
      hg.allAllowed _ (by rw [allCalls]; simp)
    obtain ⟨ci, -, ptr⟩ := get_ci_step c hc load ap a rfl hallow hr (hg.sub hsub) ha
    obtain ⟨v, hv, hci⟩ := ptr
    rw [ld] at hv
    have he := Except.ok.inj hv
    subst v
    obtain ⟨cv, V, hint, -, -, hV⟩ := CIRep.defn_inv hci
    exact expr_inst_raw_rep ((hV d Γ).mono len.heap_extends)
      (hp.mono (load.heap_extends.trans len.heap_extends)) inst

private theorem const_type_rep {κ : _root_.Address → KKey} {ci : Ix.Kernel.ConstantInfo .anon}
    {v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hci : CIRep κ h v ci)
    (ev : ObsFn W "KernelInfer::const_type_of" [v] h r h' cs) :
    TmC κ h' (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) r := by
  match Obs.«KernelInfer::const_type_of».obs ev with
  | .Axiom (hv15 := hv) (he35 := he) (he36 := hh) ..
  | .Defn (hv43 := hv) (he75 := he) (he76 := hh) ..
  | .Thm (hv83 := hv) (he103 := he) (he104 := hh) ..
  | .Opaque (hv111 := hv) (he137 := he) (he138 := hh) ..
  | .Quot (hv145 := hv) (he165 := he) (he166 := hh) ..
  | .Induct (hv173 := hv) (he223 := he) (he224 := hh) ..
  | .Ctor (hv231 := hv) (he281 := he) (he282 := hh) ..
  | .Rec (hv289 := hv) (he357 := he) (he358 := hh) .. =>
    rw [he, hh]
    exact hci.ty_of_eq hv

/-- The declared-type branch has the same weak representation guarantee. -/
theorem declared_type_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {a : Bytes.Address} {ps : List KLevel}
    {ap params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hg : CoreGood c cs) (ha : Bytes.RepAddressRef addrTy h a ap)
    (hr : c.κ (ixAddr a) ≠ unresolvedKey) (hp : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::declared_type" [ap, params] h r h' cs) :
    ∃ E, Tm c.κ d Γ h' 0 E r := by
  match Obs.«KernelGuard::declared_type».obs ev with
  | .run (cs15 := loads) (ev17 := load) (ld11 := ld) (ev50 := len) (ev70 := num)
      (ev99 := ty) (ev85 := inst) (hc115 := allCalls) .. =>
    have hsub : ∀ cl ∈ loads, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
    have hallow : c.allowed ⟨"Ingress::get_ci", [ap], h⟩ :=
      hg.allAllowed _ (by rw [allCalls]; simp)
    obtain ⟨ci, -, ptr⟩ := get_ci_step c hc load ap a rfl hallow hr (hg.sub hsub) ha
    obtain ⟨v, hv, hci⟩ := ptr
    rw [ld] at hv
    have he := Except.ok.inj hv
    subst v
    have ext := len.heap_extends.trans num.heap_extends
    have hty := const_type_rep (hci.mono ext) ty
    exact expr_inst_raw_rep (hty d Γ)
      (hp.mono (load.heap_extends.trans (ext.trans ty.heap_extends))) inst

/-- Rigid heads which the classifier returns without further normalization. -/
def rigidHead : KExpr → Bool
  | .sort _ | .forallE .. | .lam .. => true
  | _ => false

private theorem head_rep_go {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ fuel : Nat, ∀ {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {p budget r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → CoreGood c cs → Tm c.κ d Γ h 0 E p →
      ObsFn W "KernelGuard::head" [p, budget] h r h' cs →
      ∃ E', Tm c.κ d Γ h' 0 E' r ∧ (rigidHead E = true → E' = E) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro d Γ E p budget r h h' cs hlen hg hE ev
    match Obs.«KernelGuard::head».obs ev with
    | .n0 (heq40 := he) .. | .other_other (heq453 := he) .. =>
      exact (zero_ne_one (Value.field.inj he)).elim
    | .other_Srt (he75 := hr) (he76 := hh) ..
    | .other_Forall (he104 := hr) (he105 := hh) ..
    | .other_Lam (he133 := hr) (he134 := hh) .. =>
      subst hr hh
      exact ⟨E, hE, fun _ => rfl⟩
    | .other_Const (cs156 := children) (cs170 := loads) (ld60 := ld)
        (ev172 := value) (ev158 := child) (hc204 := allCalls) .. =>
      obtain ⟨a, us, rfl, ha, ps, hp, -⟩ := hE.const_of_load ld
      have hload : ∀ cl ∈ loads, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hlt : children.length < fuel := by
        rw [allCalls] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      obtain ⟨V, hV⟩ := definition_value_rep hc (hg.sub hload) ha hE.const_key_ne hp value
      obtain ⟨E', hE', -⟩ := ih children.length hlt (Nat.le_refl _) (hg.sub hsub) hV child
      exact ⟨E', hE', fun hfalse => nomatch hfalse⟩
    | .other_App (cs236 := first) (cs300 := subs) (cs286 := children)
        (ld60 := ld) (ev238 := funHead) (ld232 := lam) (ev302 := inst)
        (ev288 := child) (hc341 := allCalls) .. =>
      obtain ⟨f, a, rfl, hf, ha⟩ := hE.app_of_load ld
      have hfst : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hinst : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hlt1 : first.length < fuel := by
        rw [allCalls] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have hlt : children.length < fuel := by
        rw [allCalls] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      obtain ⟨f', hf', -⟩ := ih first.length hlt1 (Nat.le_refl _) (hg.sub hfst) hf funHead
      obtain ⟨D, B, level, rfl, -, hB, -⟩ := hf'.lam_of_load lam
      have hArg := ha.mono funHead.heap_extends
      have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub hinst hg.2) d Γ B a
        (by simpa only [ZMod.val_zero, Nat.zero_add] using hB) hArg
      simp only [ZMod.val_zero] at hi
      obtain ⟨E', hE', -⟩ := ih children.length hlt (Nat.le_refl _) (hg.sub hsub) hi child
      exact ⟨E', hE', fun hfalse => nomatch hfalse⟩
    | .other_Let (cs382 := subs) (cs368 := children) (ld60 := ld)
        (ev384 := inst) (ev370 := child) (hc423 := allCalls) .. =>
      obtain ⟨D, V, B, rfl, -, hV, hB⟩ := hE.letE_of_load ld
      have hinst : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hlt : children.length < fuel := by
        rw [allCalls] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub hinst hg.2) d Γ B V
        (by simpa only [ZMod.val_zero, Nat.zero_add] using hB) hV
      simp only [ZMod.val_zero] at hi
      rw [instShift_eq_instantiate1 hV.looseBVarsBounded 0 B]
      exact ih children.length hlt (Nat.le_refl _) (hg.sub hsub) hi child

/-- Actual classifier head computation preserves representation, and preserves a rigid input.
The conclusion is deliberately independent of `Rules.Red`. -/
theorem head_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p budget r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::head" [p, budget] h r h' cs) :
    ∃ E', Tm c.κ d Γ h' 0 E' r ∧ (rigidHead E = true → E' = E) :=
  head_rep_go hc cs.length (Nat.le_refl _) hg hE ev

end IxVM.Refinement.Core.GuardData
