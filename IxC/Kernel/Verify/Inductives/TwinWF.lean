module

public import IxC.Kernel.Verify.Inductives.TwinRun
public import IxC.Kernel.Verify.Inductives.StructWF

public section

/-! # Well-formed environments for the twin checker's annotation phases -/

namespace Ix.Kernel.NativeTwin

open Ix.Kernel.Semantics

private theorem constWF_mono {env env' : Env md}
    (hf : ∀ name, (env.find? name).isSome = true → (env'.find? name).isSome = true)
    {ci : ConstantInfo md} (h : ConstWF env ci) : ConstWF env' ci := by
  have resolve : ∀ {e : Expr md}, e.constsResolve env = true → e.constsResolve env' = true :=
    Expr.constsResolve_le hf
  obtain ⟨h1, h2, h3, h4, hdefn, hrec, hproj, hcaps⟩ := h
  refine ⟨h1, h2, resolve h3, h4, ?_, ?_, ?_, hcaps⟩
  · intro cv value hint heq
    obtain ⟨hv1, hv2, hv3, hv4⟩ := hdefn cv value hint heq
    exact ⟨hv1, hv2, resolve hv3, hv4⟩
  · intro cv mI rP rules heq rule hmember
    obtain ⟨hr1, hr2, hr3, hr4, hnested⟩ := hrec cv mI rP rules heq rule hmember
    refine ⟨hr1, hr2, resolve hr3, hr4, ?_⟩
    intro levels pins hfire
    obtain ⟨hcount, hlevels, hpins, hshape⟩ := hnested levels pins hfire
    refine ⟨hcount, hlevels, ?_, hshape⟩
    intro pin hpin
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hpins pin hpin
    exact ⟨hp1, hp2, resolve hp3, hp4⟩
  · intro table heq
    obtain ⟨hsize, hbodies⟩ := hproj table heq
    refine ⟨hsize, ?_⟩
    intro i body hbody
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbodies i body hbody
    exact ⟨hb1, hb2, resolve hb3, hb4⟩

private theorem present_append (env : Env md) (added : List (ConstantInfo md))
    (name : Key md) (h : (env.find? name).isSome = true) :
    ((⟨added ++ env.consts⟩ : Env md).find? name).isSome = true := by
  simp only [Env.find?, List.find?_append]
  cases ha : added.find? (·.name == name) <;> simp only [ha, Option.orElse_none, Option.orElse_some]
  · exact h
  · rfl

private theorem wf_append {env : Env md} (hbase : EnvWF env)
    (added : List (ConstantInfo md)) (hadded : ∀ ci ∈ added, ConstWF env ci) :
    EnvWF ⟨added ++ env.consts⟩ := by
  intro ci hci
  apply constWF_mono (present_append env added)
  rcases List.mem_append.mp hci with added | base
  · exact hadded ci added
  · exact hbase ci base

theorem HeaderChecked.provision_wf {mode : CheckMode} {fuel : Nat} {env : Env md}
    {part : Part md} (h : HeaderChecked mode fuel env part) :
    ConstWF env (.recInfo part.annotated part.majorIndex part.rulePrefix []) := by
  obtain ⟨_, _, _, _, hbounded, hfvar, ty, sty, level, hann, hlevels, hresolve, _, _, hannotated⟩ := h.1.inv
  obtain ⟨htf, htb⟩ := annotate_syntax hann hfvar hbounded
  rw [hannotated]
  refine structConstWF htf hlevels hresolve htb (fun _ _ _ heq => nomatch heq) ?_
  intro cv mI rP rules heq rule hmember
  have hempty : [] = rules := (ConstantInfo.recInfo.inj heq).2.2.2
  rw [← hempty] at hmember
  cases hmember

theorem CanonicalPart.model_wf {env : Env md} (hbase : EnvWF env)
    {part : Part md} (h : CanonicalPart env part) {ci : ConstantInfo md}
    (hci : modelInfo? part = some ci) : ConstWF env ci := by
  cases hm : part.model? with
  | none => simp only [modelInfo?, hm, Option.map_none] at hci; cases hci
  | some data =>
    obtain ⟨cv, value, hint⟩ := data
    simp only [modelInfo?, hm, Option.map_some, Option.some.injEq] at hci
    subst ci
    have hlookup : env.find? (auxKey part.canonicalKey .model) = some (.defnInfo cv value hint) := by
      simpa only [ModelSource, hm] using h.model
    obtain ⟨htf, htl, htr, htb, hv, _, _, _⟩ := hbase _ (List.mem_of_find?_eq_some hlookup)
    refine structConstWF htf htl htr htb ?_ (fun _ _ _ _ heq => nomatch heq)
    intro cv' value' hint' heq
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
    exact hv cv value hint rfl

/-- The actual header phase builds a well-formed environment for rule annotation. The
proof uses the original stored model copies and checked header syntax, without a model
existence assumption. -/
theorem prepare_self_wf {mode : CheckMode} {fuel : Nat} {env : Env md}
    {block : List (ConstantInfo md)} {parts : List (Part md)} (hbase : EnvWF env)
    (h : prepare (fueledOps mode fuel) env block = .ok parts) : EnvWF (selfEnv env parts) := by
  have headers := (prepare_spec h).2.2.2.2
  apply wf_append hbase (provision parts ++ models parts)
  intro ci hci
  rcases List.mem_append.mp hci with provisional | model
  · obtain ⟨part, hpart, rfl⟩ := List.mem_map.mp provisional
    exact (headers part hpart).provision_wf
  · obtain ⟨part, hpart, hci⟩ := List.mem_filterMap.mp model
    exact (headers part hpart).2.2.model_wf hbase hci

end Ix.Kernel.NativeTwin
