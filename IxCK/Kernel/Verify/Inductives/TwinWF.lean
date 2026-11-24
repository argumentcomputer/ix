module

public import IxCK.Kernel.Verify.Inductives.TwinRun
public import IxCK.Kernel.Verify.Inductives.StructWF

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
  cases added.find? (·.name == name) with
  | none => exact h
  | some _ => rfl

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

private theorem present_iff_name (env : Env md) (name : Key md) :
    (env.find? name).isSome = true ↔ name ∈ env.consts.map (·.name) := by
  simp only [Env.find?, List.find?_isSome, List.mem_map, beq_iff_eq]

private theorem zip_right_member {α β γ : Type} {R : α × β → γ → Prop} :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, xs.length = ys.length →
      Forall₂ R (xs.zip ys) zs → ∀ y ∈ ys, ∃ x z, z ∈ zs ∧ R (x, y) z
  | [], [], _, _, _, _, hy => by cases hy
  | [], _ :: _, _, hlen, _, _, _ => by cases hlen
  | _ :: _, [], _, hlen, _, _, _ => by cases hlen
  | x :: xs, y :: ys, zs, hlen, hrel, found, hfound => by
    cases hrel with
    | cons hhead htail =>
      rcases List.mem_cons.mp hfound with rfl | hfound
      · exact ⟨x, _, List.mem_cons_self, hhead⟩
      · obtain ⟨x', z, hz, hR⟩ := zip_right_member (Nat.succ.inj hlen) htail found hfound
        exact ⟨x', z, List.mem_cons_of_mem _ hz, hR⟩

private theorem copied_model_wf {env : Env md} (hbase : EnvWF env)
    {key : Key md} {cv : ConstantVal md} {value : Expr md} {hint : ReducibilityHint}
    (hlookup : env.find? key = some (.defnInfo cv value hint)) (name : Key md) :
    ConstWF env (.defnInfo { cv with name := name } value hint) := by
  obtain ⟨htf, htl, htr, htb, hv, _, _, _⟩ := hbase _ (List.mem_of_find?_eq_some hlookup)
  refine structConstWF htf htl htr htb ?_ (fun _ _ _ _ heq => nomatch heq)
  intro cv' value' hint' heq
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
  exact hv cv value hint rfl

/-- Attaching the checked twin rules preserves the syntactic environment invariant. This
uses the canonical rules' stored nested metadata and the actual rule annotation checks. -/
theorem check_wf {mode : CheckMode} {fuel : Nat} {env output : Env md}
    {block : List (ConstantInfo md)} (hbase : EnvWF env)
    (h : check (fueledOps mode fuel) env block = .ok output) : EnvWF output := by
  obtain ⟨parts, rename, _, _, houtput, _, _, _, checked⟩ := check_semantic h
  let target : Env md := ⟨twinRecs parts ++ (twinModels parts ++ env.consts)⟩
  let provisional : Env md := ⟨twinProv parts ++ (twinModels parts ++ env.consts)⟩
  have fromBase : ∀ name, (env.find? name).isSome = true → (target.find? name).isSome = true := by
    intro name hn
    simpa only [target, List.append_assoc] using present_append env (twinRecs parts ++ twinModels parts) name hn
  have sameNames : provisional.consts.map (·.name) = target.consts.map (·.name) := by
    simp only [provisional, target, List.map_append, twinProv, twinRecs, List.map_map]
    rfl
  have fromProvisional : ∀ name, (provisional.find? name).isSome = true →
      (target.find? name).isSome = true := by
    intro name hn
    rw [present_iff_name] at hn ⊢
    rwa [sameNames] at hn
  rw [houtput]
  change EnvWF target
  intro ci hci
  rcases List.mem_append.mp hci with recursor | tail
  · obtain ⟨part, hpart, rfl⟩ := List.mem_map.mp recursor
    obtain ⟨hcv, _, hcanonical, hlevels, _, _, hlen, hrules⟩ := checked part hpart
    have levelNames : part.cvW'.levelParams = part.cvC.levelParams := hcv.levelParams_eq.trans hlevels
    have typeFacts : part.cvW'.type.hasFvar = false ∧
        part.cvW'.type.allLevelParamsDefined part.cvW'.levelParams = true ∧
        part.cvW'.type.constsResolve env = true ∧ part.cvW'.type.looseBVarsBounded 0 = true := by
      obtain ⟨_, _, _, _, hb, hf, ty, sty, level, hann, hl, hr, _, _, heq⟩ := hcv.inv
      obtain ⟨htf, htb⟩ := annotate_syntax hann hf hb
      rw [heq]
      exact ⟨htf, hl, hr, htb⟩
    refine structConstWF typeFacts.1 typeFacts.2.1
      (Expr.constsResolve_le fromBase typeFacts.2.2.1) typeFacts.2.2.2
      (fun _ _ _ heq => nomatch heq) ?_
    intro cv mI rP rules heq rule hmember
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
    obtain ⟨raw, canonical, hcanonicalMember, hchecked⟩ := zip_right_member hlen hrules rule hmember
    obtain ⟨_, _, hb, hf, hann, hl, hr, _, _, _, _, hfire, _, _, _, _, hshape, _⟩ := hchecked
    obtain ⟨hf', hb'⟩ := annotate_syntax hann hf hb
    refine ⟨hf', ?_, Expr.constsResolve_le fromProvisional hr, hb', ?_⟩
    · rwa [levelNames]
    · intro levels pins hmode
      obtain ⟨_, _, _, _, _, canonicalWF, _, _⟩ :=
        hbase _ (List.mem_of_find?_eq_some hcanonical)
      obtain ⟨_, _, _, _, hnested⟩ :=
        canonicalWF part.cvC part.mI part.rP part.rulesC rfl canonical hcanonicalMember
      obtain ⟨hcount, hlevels, hpins, _⟩ := hnested levels pins (hfire.symm.trans hmode)
      refine ⟨hcount, ?_, ?_, hshape levels pins hmode⟩
      · intro level hlevel
        rw [levelNames]
        exact hlevels level hlevel
      · intro pin hpin
        obtain ⟨hp1, hp2, hp3, hp4⟩ := hpins pin hpin
        refine ⟨hp1, ?_, Expr.constsResolve_le fromBase hp3, hp4⟩
        rwa [levelNames]
  · rcases List.mem_append.mp tail with model | old
    · obtain ⟨part, hpart, hmodel⟩ := List.mem_filterMap.mp model
      unfold TwinRecPart.modelInfo? at hmodel
      obtain ⟨⟨cv, value, hint⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp hmodel
      have hlookup := (checked part hpart).2.2.2.2.1
      rw [hp] at hlookup
      exact constWF_mono fromBase (copied_model_wf hbase hlookup _)
    · exact constWF_mono fromBase (hbase ci old)

end Ix.Kernel.NativeTwin
