import IxVMRefinement.Assembly.GuardRawTm
import IxVMRefinement.Assembly.GuardHeadRep
import IxVMRefinement.Guard.Loads
import IxVMRefinement.Whnf.Delta
import IxVMRefinement.Core.Steps.Whnf
import IxC.Kernel.Model.HeadDeltaBetaLevels

/-! # The classifier head operation follows the head trace

`KernelGuard::head` returns a sort, `∀` or `λ` node unchanged, unfolds a definition at a
constant (`definition_value`), reduces the function of an application to a `λ` and substitutes
the argument, and substitutes the value of a `let`.

`definition_value_unfold` names the result of the definition arm: it represents the stored
value instantiated at the constant's own level parameters, which is what
`Ix.Kernel.unfoldDefinition` returns at that constant. `declared_type_inst` is the same for the
classifier's other load, the declared type of a constant at a level list. `head_trace` then says that the result
of `head` represents the end of a `HeadDeltaBeta.Trace` from the term its input represents, and
that this end is a sort, `∀` or `λ`, hence has no further head step
(`normal_of_rigidHead`): by `Trace.normal_unique` the represented result is determined by the
represented input.

Tolerance, as for every statement at the term seam: the input term is any term the input
pointer represents; the levels of the constant being unfolded are the term's own, which the
heap list equals pointwise semantically. The run's budget does not enter the statement: a run
that exhausts it is not an observation. A heap `let` takes no trace step, because the term seam
already reads it as its substitution instance. The term is read at local depth `0`, at any
opening depth, where a beta argument has no loose bound variable and the non-lifting
substitution of the head trace is the circuit's lifting one.

The existence-only lemmas `definition_value_rep` and `head_rep` are unchanged. -/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel.HeadDeltaBeta (Trace Step Normal)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

/-- A sort, `∀` or `λ` has no head step. -/
theorem normal_of_rigidHead {env : Ix.Kernel.Env .anon} {E : KExpr}
    (h : rigidHead E = true) : Normal env E := by
  intro e hs
  cases hs with
  | delta _ => simp [rigidHead] at h
  | beta => simp [rigidHead] at h
  | appFn _ => simp [rigidHead] at h

/-- **`definition_value` is the unfolding of the constant.** The loaded constant is a stored
definition whose level-parameter count is the length of the level list, and the result
represents its value instantiated at its own level parameters by any list `us` pointwise
semantically equal to the represented list. -/
theorem definition_value_unfold {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {a : Bytes.Address} {us ps : List KLevel}
    {ap params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hg : CoreGood c cs) (ha : Bytes.RepAddressRef addrTy h a ap)
    (resolved : c.κ (ixAddr a) ≠ unresolvedKey) (parameters : RepKLevelList h ps params)
    (hus : LvEqList us ps)
    (ev : ObsFn W "KernelGuard::definition_value" [ap, params] h r h' cs) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (V : KExpr) (hint : Ix.Kernel.ReducibilityHint),
      c.env.find? (c.κ (ixAddr a)) = some (.defnInfo cv V hint) ∧
      us.length = cv.levelParams.length ∧
      Ix.Kernel.unfoldDefinition c.env (.const (c.κ (ixAddr a)) us) =
        some (V.instantiateLevelParams cv.levelParams us) ∧
      Tm c.κ d Γ h' 0 (V.instantiateLevelParams cv.levelParams us) r := by
  match Obs.«KernelGuard::definition_value».obs ev with
  | .run (m2 := loaded) (p9 := ptr) (cs15 := loadCalls)
      (x_nl := nl) (w29 := ty) (x_value := value) (w30 := flag) (w31 := hintPtr)
      (m71 := beforeInst) (cs101 := instCalls) (ev17 := load) (ld11 := shape)
      (ev81 := length) (heq97 := arity) (ev103 := inst) (hc120 := events) .. =>
    have loadInside : ∀ cl ∈ loadCalls, cl ∈ cs := by
      intro cl member; rw [events]; simp [member]
    have allowed : c.allowed ⟨"Ingress::get_ci", [ap], h⟩ :=
      hg.allAllowed _ (by rw [events]; simp)
    obtain ⟨ci, found, actual, loadedValue, represented⟩ :=
      get_ci_step c hc.base load ap a rfl allowed resolved (hg.sub loadInside) ha
    rw [shape] at loadedValue
    have same := Except.ok.inj loadedValue
    subst actual
    obtain ⟨cv, V, hint, rfl, valRep, bodyRep⟩ := CIRep.defn_inv represented
    have psLoaded := parameters.mono load.heap_extends
    obtain ⟨lengthValue, _⟩ :=
      ProjAux.levels_length length ⟨ps, psLoaded, LvEqList.refl ps⟩
    have psBound : ps.length < 549755813888 := by
      have bound := RomBound.bounded_length_lt hg.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [params], loaded⟩)
        (p := params) (by rw [events]; simp) (by simp) psLoaded
      simpa using bound
    have levelsBound : cv.levelParams.length < 4294967296 := valRep.2.1
    rw [lengthValue, valRep.1] at arity
    have arityExact : ps.length = cv.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj arity)
    have hlenus : us.length = cv.levelParams.length :=
      (SubstAux.evalEqList_length (hus (fun _ => 0))).trans arityExact
    have hinst := expr_inst_raw_tm (Γ := Γ) ((bodyRep 0 Γ).mono length.heap_extends)
      ⟨ps, psLoaded.mono length.heap_extends, hus⟩ inst
    rw [WhnfAux.posOf_ilp_perm valRep.2.2.1 hlenus] at hinst
    have hd : Ix.Kernel.unfoldDefinition c.env (.const (c.κ (ixAddr a)) us) =
        some (V.instantiateLevelParams cv.levelParams us) := by
      simpa only [Ix.Kernel.Expr.mkAppN] using unfold_const_mkAppN [] found hlenus
    exact ⟨cv, V, hint, found, hlenus, hd, hinst.of_depth_zero d⟩

/-- **`declared_type` is the declared type at the levels.** The loaded constant has as many
level parameters as the level list has levels, and the result represents its declared type
instantiated at its own level parameters by any list `us` pointwise semantically equal to the
represented list. -/
theorem declared_type_inst {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {a : Bytes.Address} {us ps : List KLevel}
    {ap params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hg : CoreGood c cs) (ha : Bytes.RepAddressRef addrTy h a ap)
    (resolved : c.κ (ixAddr a) ≠ unresolvedKey) (parameters : RepKLevelList h ps params)
    (hus : LvEqList us ps)
    (ev : ObsFn W "KernelGuard::declared_type" [ap, params] h r h' cs) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      c.env.find? (c.κ (ixAddr a)) = some ci ∧
      us.length = ci.toConstantVal.levelParams.length ∧
      Tm c.κ d Γ h' 0
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) r := by
  match Obs.«KernelGuard::declared_type».obs ev with
  | .run (v1 := value) (m2 := loaded) (p9 := ptr) (cs15 := loadCalls)
      (cs68 := countCalls) (cs83 := instCalls) (v86 := typePtr) (m60 := beforeType)
      (m89 := beforeInst) (cs97 := typeCalls) (ev17 := load) (ld11 := shape)
      (ev50 := length) (ev70 := count) (heq79 := arity)
      (ev99 := getType) (ev85 := inst) (hc115 := events) .. =>
    have loadInside : ∀ cl ∈ loadCalls, cl ∈ cs := by
      intro cl member; rw [events]; simp [member]
    have countInside : ∀ cl ∈ countCalls, cl ∈ cs := by
      intro cl member; rw [events]; simp [member]
    have typeInside : ∀ cl ∈ typeCalls, cl ∈ cs := by
      intro cl member; rw [events]; simp [member]
    have allowed : c.allowed ⟨"Ingress::get_ci", [ap], h⟩ :=
      hg.allAllowed _ (by rw [events]; simp)
    obtain ⟨ci, found, actual, loadedValue, represented⟩ :=
      get_ci_step c hc.base load ap a rfl allowed resolved (hg.sub loadInside) ha
    rw [shape] at loadedValue
    have same := Except.ok.inj loadedValue
    subst actual
    have psLoaded := parameters.mono load.heap_extends
    obtain ⟨lengthValue, _⟩ :=
      ProjAux.levels_length length ⟨ps, psLoaded, LvEqList.refl ps⟩
    have countSpec := Registry.induction c (scoped_steps c hc) (.infer .const_num_lvls)
      _ _ _ _ _ count
    obtain ⟨countValue, _⟩ := countSpec value ci rfl (hg.sub countInside)
      (represented.mono length.heap_extends)
    have psBound : ps.length < 549755813888 := by
      have bound := RomBound.bounded_length_lt hg.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [params], loaded⟩)
        (p := params) (by rw [events]; simp) (by simp) psLoaded
      simpa using bound
    obtain ⟨_, _, _, _, _, valRep⟩ := represented.head
    have levelsBound : ci.toConstantVal.levelParams.length < 4294967296 := valRep.2.1
    rw [lengthValue, countValue] at arity
    have arityExact : ps.length = ci.toConstantVal.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj arity)
    have beforeExtension := length.heap_extends.trans count.heap_extends
    have typeSpec := Registry.induction c (scoped_steps c hc) (.infer .const_type_of)
      _ _ _ _ _ getType
    obtain ⟨typeRep, _⟩ := typeSpec value ci rfl (hg.sub typeInside)
      (represented.mono beforeExtension)
    have extension := beforeExtension.trans getType.heap_extends
    have hlenus : us.length = ci.toConstantVal.levelParams.length :=
      (SubstAux.evalEqList_length (hus (fun _ => 0))).trans arityExact
    have hinst := expr_inst_raw_tm (Γ := Γ) (typeRep 0 Γ)
      ⟨ps, psLoaded.mono extension, hus⟩ inst
    rw [WhnfAux.posOf_ilp_perm valRep.2.2.1 hlenus] at hinst
    exact ⟨ci, found, hlenus, hinst.of_depth_zero d⟩

private theorem head_trace_go {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ fuel : Nat, ∀ {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {p budget r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → CoreGood c cs → Tm c.κ d Γ h 0 E p →
      ObsFn W "KernelGuard::head" [p, budget] h r h' cs →
      ∃ E', Trace c.env E E' ∧ rigidHead E' = true ∧ Tm c.κ d Γ h' 0 E' r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro d Γ E p budget r h h' cs hlen hg hE ev
    match Obs.«KernelGuard::head».obs ev with
    | .n0 (heq40 := he) .. | .other_other (heq453 := he) .. =>
      exact (zero_ne_one (Value.field.inj he)).elim
    | .other_Srt (ld60 := ld) (he75 := hr) (he76 := hh) .. =>
      subst hr hh
      obtain ⟨u, rfl, -⟩ := hE.sort_of_load ld
      exact ⟨_, .refl, rfl, hE⟩
    | .other_Forall (ld60 := ld) (he104 := hr) (he105 := hh) .. =>
      subst hr hh
      obtain ⟨T, B, l, rfl, -⟩ := hE.forallE_of_load ld
      exact ⟨_, .refl, rfl, hE⟩
    | .other_Lam (ld60 := ld) (he133 := hr) (he134 := hh) .. =>
      subst hr hh
      obtain ⟨T, B, l, rfl, -⟩ := hE.lam_of_load ld
      exact ⟨_, .refl, rfl, hE⟩
    | .other_Const (cs156 := children) (cs170 := loads) (ld60 := ld)
        (ev172 := value) (ev158 := child) (hc204 := allCalls) .. =>
      obtain ⟨a, us, rfl, ha, ps, hp, hus⟩ := hE.const_of_load ld
      have hload : ∀ cl ∈ loads, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [allCalls]; simp [hm]
      have hlt : children.length < fuel := by
        rw [allCalls] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      obtain ⟨cv, V, hint, -, -, hd, hV⟩ :=
        definition_value_unfold (d := d) (Γ := Γ) hc (hg.sub hload) ha hE.const_key_ne hp hus
          value
      obtain ⟨E', htr, hrig, hE'⟩ :=
        ih children.length hlt (Nat.le_refl _) (hg.sub hsub) hV child
      exact ⟨E', .cons (.delta hd) htr, hrig, hE'⟩
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
      obtain ⟨f', htrf, -, hf'⟩ :=
        ih first.length hlt1 (Nat.le_refl _) (hg.sub hfst) hf funHead
      obtain ⟨D, B, level, rfl, -, hB, -⟩ := hf'.lam_of_load lam
      have hArg := ha.mono funHead.heap_extends
      have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub hinst hg.2) d Γ B a
        (by simpa only [ZMod.val_zero, Nat.zero_add] using hB) hArg
      simp only [ZMod.val_zero] at hi
      obtain ⟨E', htr, hrig, hE'⟩ :=
        ih children.length hlt (Nat.le_refl _) (hg.sub hsub) hi child
      exact ⟨E', (htrf.appFn a).trans (.cons .beta htr), hrig, hE'⟩
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

/-- **`head` follows the head trace.** If `p` represents `E` at local depth `0`, the result of
an observed `KernelGuard::head` run represents the end `E'` of a head trace from `E` in the
context's environment, and `E'` is a sort, `∀` or `λ`. -/
theorem head_trace {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p budget r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::head" [p, budget] h r h' cs) :
    ∃ E', Trace c.env E E' ∧ rigidHead E' = true ∧ Tm c.κ d Γ h' 0 E' r :=
  head_trace_go hc cs.length (Nat.le_refl _) hg hE ev

/-- **The represented result of `head` is determined by the represented input**: two runs, in
contexts with one environment, on pointers that represent one term, return pointers that
represent one term. -/
theorem head_trace_unique {env : Ix.Kernel.Env .anon} {E E₁ E₂ : KExpr}
    (h₁ : Trace env E E₁) (r₁ : rigidHead E₁ = true)
    (h₂ : Trace env E E₂) (r₂ : rigidHead E₂ = true) : E₁ = E₂ :=
  h₁.normal_unique (normal_of_rigidHead r₁) h₂ (normal_of_rigidHead r₂)

end IxVM.Refinement.Core.GuardData
