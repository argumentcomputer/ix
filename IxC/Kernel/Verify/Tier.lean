module

public import IxC.Kernel.Tier.Check
public import IxC.Kernel.Rules.Rel
public import IxC.Kernel.Verify.EnvWF
public import IxC.Kernel.Verify.Cached.InstalledC
import IxC.Kernel.Verify.CheckerSplit
import IxC.Kernel.Verify.Rules.Bridge
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Verify.CheckerF
import IxC.Kernel.Verify.EnvBound
import IxC.Kernel.Verify.Inductives.StructWF
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Verify.Shift
import IxC.Kernel.Verify.Cached.MainC

public section

/-!
# The typing tier's theorems

`checkTierC_typed`: if the tier fold accepts `ds` at the index of a
well-formed logical environment `env`, then

* the index it returns is the index of `env.extendOpaque ts`, which is
  well-formed;
* no tier constant is a constant of `env` (`env.find?` misses it);
* every tier constant `c` is **typed**: it comes from a member `(cv, v)` of a
  partial block of `ds`, its header is the install of `cv` at the
  environment of the tier constants before its block
  (`installConstantVal`: the guards, the annotation, resolution), and in the
  environment with its block and the constants before it (its *scope*,
  every tier constant opaque, as `axiomInfo`) its type is a sort and its
  value annotates to a term whose type is convertible to its type, by
  derivations of the rules tier (`Rules.Infer`, `Rules.Red`,
  `Rules.DefEq`, through the bridge from the executable core).

The scope is Lean's lattice: a partial constant sees the logical
environment, the partial constants before its block and its own block.
Nothing here is about meaning: no model is claimed for a tier constant.

**The fence** is `checkDecls_closed` with the freshness above: the logical
fold's accept is well-formed (`EnvWF`: every term it stores resolves in it),
and no tier constant resolves in it. So no accepted logical declaration
names a tier constant.

The proofs are composition: the run lemmas of the cached fold
(`annotConstantValC_run`, `annotValC_run`, `checkPending_run`,
`IxC/Kernel/Verify/Cached/InstalledC.lean`), `EnvWF.cons` per install, and
the bridge.
-/

namespace Ix.Kernel.Tier

open Ix.Kernel Ix.Kernel.Cached

universe w

/-! ## Typing, as the tier states it -/

/-- **A typed member** in `E`: its type is a sort, and its value annotates
(`installValue`) to a term whose type is convertible to its type. -/
@[expose] def Typed (E : Env md) (c : ConstantVal md) (v : Expr md) : Prop :=
  (∃ s u, Rules.Infer E .full 0 c.type s ∧ Rules.Red E 0 s (.sort u)) ∧
  ∃ F jv vt, installValue (fueledOps .verified F) E c v = .ok jv ∧
    Rules.Infer E .full 0 jv vt ∧ Rules.DefEq E 0 vt c.type

/-- **`c` is a typed tier constant of `ts`, from `ds`**: `ts` is the
constants after `c`'s block, its block, and the ones before it (`pre`);
`c` is the install of a member `(cv, v)` of a partial block of `ds` at
`env.extendOpaque pre`, and typed in `env.extendOpaque (blk ++ pre)`. -/
@[expose] def TypedIn (env : Env md) (ds : List (TierDecl md)) (ts : List (TierConst md))
    (c : TierConst md) : Prop :=
  c.safety = .part ∧
  ∃ later blk pre, ts = later ++ blk ++ pre ∧ c ∈ blk ∧
    ∃ ms, TierDecl.defs .part ms ∈ ds ∧ ∃ m ∈ ms,
      (∃ F, installConstantVal (fueledOps .verified F) (env.extendOpaque pre) m.1 = .ok c.cv) ∧
      Typed (env.extendOpaque (blk ++ pre)) c.cv m.2

/-- Two lists related element by element (Mathlib's `List.Forall₂`, which
the kernel's closure does not have). -/
inductive Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Pairs R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      R a b → Pairs R l₁ l₂ → Pairs R (a :: l₁) (b :: l₂)

/-! ## The environment and the index -/

theorem extendOpaque_append (env : Env md) (blk acc : List (TierConst md)) :
    (env.extendOpaque acc).extendOpaque blk = env.extendOpaque (blk ++ acc) := by
  simp [Env.extendOpaque, TierConst.infos]

theorem extendOpaque_nil (env : Env md) : env.extendOpaque [] = env := rfl

/-- A key the extension misses, `env` misses. -/
theorem find?_of_extendOpaque {env : Env md} {ts : List (TierConst md)} {n : Key md}
    (h : (env.extendOpaque ts).find? n = none) : env.find? n = none := by
  unfold Env.find? at h ⊢
  rw [show (env.extendOpaque ts).consts = TierConst.infos ts ++ env.consts from rfl,
    List.find?_append] at h
  cases hl : (TierConst.infos ts).find? (·.name == n) with
  | none => rw [hl] at h; simpa using h
  | some c => rw [hl] at h; exact nomatch h

/-- The headers pushed are the extension by the block. -/
theorem pushHeaders_mkFEnv : ∀ (E : Env md) (hs : List (ConstantVal md)) (s : Safety),
    pushHeaders (mkFEnv E) hs = mkFEnv (E.extendOpaque (blockConsts s hs))
  | E, [], _ => rfl
  | E, h :: hs, s => by
    rw [pushHeaders, push_mkFEnv, pushHeaders_mkFEnv _ hs s]
    congr 1
    simp [Env.extendOpaque, TierConst.infos, blockConsts, List.map_reverse]

/-! ## The headers -/

/-- The four type-slot facts of a header installed at `E`. -/
theorem installConstantVal_typeFacts {E : Env md} {F : Nat} {cv c : ConstantVal md}
    (h : installConstantVal (fueledOps .verified F) E cv = .ok c) :
    c.type.hasFvar = false ∧ c.type.allLevelParamsDefined c.levelParams = true ∧
      c.type.constsResolve E = true ∧ c.type.looseBVarsBounded 0 = true ∧
      c.name = cv.name ∧ E.find? cv.name = none := by
  obtain ⟨hfind, -, -, -, hlb, hif, type', hann, htp, htr, rfl⟩ := installConstantVal_inv h
  exact ⟨Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F cv.type hann (Expr.WScoped.of_not_hasFvar hif)).fvarsBelow),
    htp, htr, annotateCore_looseBVars F cv.type hann hlb, rfl, hfind⟩

/-- A block's headers, checked at `mkFEnv E`: each the install of its
member's header at `E`, well scoped. -/
theorem headersC_ok {E : Env md} (hE : EnvWF E) :
    ∀ {ms : List (ConstantVal md × Expr md)} {hs : List (ConstantVal md)},
      headersC (mkFEnv E) ms = .ok hs →
      Pairs (fun (m : ConstantVal md × Expr md) (c : ConstantVal md) =>
        (∃ F, installConstantVal (fueledOps .verified F) E m.1 = .ok c) ∧
          Expr.WScoped 0 c.type) ms hs
  | [], hs, h => by
    simp only [headersC, Except.ok.injEq] at h
    subst h
    exact .nil
  | (cv, v) :: ms, hs, h => by
    simp only [headersC] at h
    split at h
    · exact nomatch h
    · rename_i cvA jty s' ha
      split at h
      · exact nomatch h
      · rename_i rest hr
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨-, hcvA, hwty, F, hI⟩ := annotConstantValC_run rfl hE (CSOK.empty E) ha
        refine .cons ⟨⟨F, hI⟩, ?_⟩ (headersC_ok hE hr)
        rw [hcvA]
        exact hwty

/-- Installing headers whose type-slot facts hold at `E` keeps the
environment well formed. -/
theorem envWF_blockConsts : ∀ {E : Env md} (_hE : EnvWF E) (s : Safety) {hs : List (ConstantVal md)},
    (∀ c ∈ hs, c.type.hasFvar = false ∧ c.type.allLevelParamsDefined c.levelParams = true ∧
      c.type.constsResolve E = true ∧ c.type.looseBVarsBounded 0 = true) →
    EnvWF (E.extendOpaque (blockConsts s hs))
  | E, hE, _, [], _ => hE
  | E, hE, s, h :: hs, hf => by
    obtain ⟨h1, h2, h3, h4⟩ := hf h List.mem_cons_self
    have hE₁ : EnvWF ⟨.axiomInfo h :: E.consts⟩ :=
      EnvWF.cons hE (structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    have ih := envWF_blockConsts hE₁ s (hs := hs) fun c hc =>
      let ⟨g1, g2, g3, g4⟩ := hf c (List.mem_cons_of_mem _ hc)
      ⟨g1, g2, Expr.constsResolve_mono g3, g4⟩
    have heq : (⟨.axiomInfo h :: E.consts⟩ : Env md).extendOpaque (blockConsts s hs) =
        E.extendOpaque (blockConsts s (h :: hs)) := by
      simp [Env.extendOpaque, TierConst.infos, blockConsts, List.map_reverse]
    rw [← heq]
    exact ih

/-! ## The values -/

/-- A member's value checked at `mkFEnv E`: typed in `E`. -/
theorem valueC_ok {E : Env md} (hE : EnvWF E) {c : ConstantVal md} {v : Expr md}
    (hwty : Expr.WScoped 0 c.type) (h : valueC (mkFEnv E) c v = .ok ()) : Typed E c v := by
  simp only [valueC] at h
  split at h
  · exact nomatch h
  · rename_i jv s₁ hval
    split at h
    · exact nomatch h
    · rename_i r hchk
      obtain ⟨-, hwjv, F₁, hV⟩ := annotValC_run rfl hE (CSOK.empty E) hval
      rcases r with ⟨⟨⟩, s₂⟩
      obtain ⟨-, F₂, hC⟩ := checkPending_run (feFinal := mkFEnv E)
        (pc := ⟨⟨.defn, c, jv⟩, 0, (mkFEnv E).visibleBelow⟩) rfl hE
        (fun n => mkFEnv_find? E n) hwty (fun _ => hwjv) CSOKF.empty hchk
      obtain ⟨stype, u, hst, hsort, -, jv', -, hjv', vtype, hvt, hde⟩ := checkValueGroup_inv hC
      obtain rfl : jv' = jv := hjv' (fun h => nomatch h)
      exact ⟨⟨stype, u, Rules.inferTypeCore_bridge hst,
          Rules.whnf_bridge (ensureSortCore_inv hsort)⟩,
        F₁, _, vtype, hV, Rules.inferTypeCore_bridge hvt, Rules.isDefEqCore_bridge hde⟩

/-- Every member's value checked at `mkFEnv E`. -/
theorem valuesC_ok {E : Env md} (hE : EnvWF E)
    {R : ConstantVal md × Expr md → ConstantVal md → Prop}
    (hR : ∀ m c, R m c → Expr.WScoped 0 c.type) :
    ∀ {ms : List (ConstantVal md × Expr md)} {hs : List (ConstantVal md)},
      Pairs R ms hs → valuesC (mkFEnv E) hs ms = .ok () →
      Pairs (fun m c => R m c ∧ Typed E c m.2) ms hs
  | [], [], .nil, _ => .nil
  | (cv, v) :: ms, c :: hs, .cons hr rest, h => by
    simp only [valuesC] at h
    split at h
    · exact nomatch h
    · rename_i hv
      exact .cons ⟨hr, valueC_ok hE (hR _ _ hr) hv⟩ (valuesC_ok hE hR rest h)

/-! ## One declaration, and the fold -/

/-- A related pair for every element on the right. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Pairs R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => (List.not_mem_nil hb).elim
  | a :: _, _ :: _, .cons hr rest, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hr⟩
    · obtain ⟨a', ha', hr'⟩ := forall₂_mem_right rest hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

/-- **One tier declaration**, accepted at `mkFEnv E`: a partial block, the
returned index is the extension by its constants, which is well formed, and
each of its constants is the install of a member's header at `E`, typed in
the extension. -/
theorem checkDeclC_ok {E : Env md} (hE : EnvWF E) {d : TierDecl md} {fe' : FEnv md}
    {blk : List (TierConst md)} (h : checkDeclC (mkFEnv E) d = .ok (fe', blk)) :
    fe' = mkFEnv (E.extendOpaque blk) ∧ EnvWF (E.extendOpaque blk) ∧
      ∃ ms, d = .defs .part ms ∧ ∀ c ∈ blk, c.safety = .part ∧
        ∃ m ∈ ms, (∃ F, installConstantVal (fueledOps .verified F) E m.1 = .ok c.cv) ∧
          Typed (E.extendOpaque blk) c.cv m.2 := by
  match d, h with
  | .defs .unsaf _, h => exact absurd h (by simp [checkDeclC])
  | .defs .part ms, h =>
    simp only [checkDeclC] at h
    split at h
    · exact nomatch h
    split at h
    · exact nomatch h
    rename_i hs hhs
    split at h
    · exact nomatch h
    rename_i hvals
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hfe := pushHeaders_mkFEnv E hs .part
    have h₂ := headersC_ok hE hhs
    have hfacts : ∀ c ∈ hs, c.type.hasFvar = false ∧ c.type.allLevelParamsDefined c.levelParams = true ∧
        c.type.constsResolve E = true ∧ c.type.looseBVarsBounded 0 = true := by
      intro c hc
      obtain ⟨m, -, ⟨⟨F, hI⟩, -⟩⟩ := forall₂_mem_right h₂ hc
      obtain ⟨g1, g2, g3, g4, -⟩ := installConstantVal_typeFacts hI
      exact ⟨g1, g2, g3, g4⟩
    have hE' := envWF_blockConsts hE .part hfacts
    rw [hfe] at hvals
    have h₃ := valuesC_ok hE' (fun _ _ hr => hr.2) h₂ hvals
    refine ⟨hfe, hE', ms, rfl, ?_⟩
    intro c hc
    simp only [blockConsts, List.mem_reverse, List.mem_map] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc
    obtain ⟨m, hm, ⟨⟨F, hI⟩, -⟩, hty⟩ := forall₂_mem_right h₃ hcv
    exact ⟨rfl, m, hm, ⟨F, hI⟩, hty⟩

/-- The fold from an accumulator. -/
theorem checkTierFrom_typed {env : Env md} :
    ∀ {ds : List (TierDecl md)} {acc : List (TierConst md)} {i : Nat}
      {fe' : FEnv md} {ts : List (TierConst md)},
      EnvWF (env.extendOpaque acc) →
      checkTierFrom (mkFEnv (env.extendOpaque acc)) acc i ds = .ok (fe', ts) →
      fe' = mkFEnv (env.extendOpaque ts) ∧ EnvWF (env.extendOpaque ts) ∧
        (∃ new, ts = new ++ acc) ∧
        ∀ c ∈ ts, c ∈ acc ∨ TypedIn env ds ts c
  | [], acc, i, fe', ts, hwf, h => by
    simp only [checkTierFrom, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hwf, ⟨[], rfl⟩, fun c hc => .inl hc⟩
  | d :: ds, acc, i, fe', ts, hwf, h => by
    simp only [checkTierFrom] at h
    split at h
    · rename_i fe₁ blk hd
      obtain ⟨rfl, hwf₁, ms, rfl, hblk⟩ := checkDeclC_ok hwf hd
      rw [extendOpaque_append] at hwf₁ hblk
      rw [extendOpaque_append] at h
      obtain ⟨hfe, hwfT, ⟨new, hnew⟩, hall⟩ := checkTierFrom_typed hwf₁ h
      refine ⟨hfe, hwfT, ⟨new ++ blk, by rw [hnew, List.append_assoc]⟩, ?_⟩
      intro c hc
      rcases hall c hc with hin | ht
      · rcases List.mem_append.mp hin with hb | ha
        · obtain ⟨hs, m, hm, hI, hty⟩ := hblk c hb
          exact .inr ⟨hs, new, blk, acc, by rw [hnew, List.append_assoc], hb, ms,
            List.mem_cons_self, m, hm, hI, hty⟩
        · exact .inl ha
      · obtain ⟨hs, later, b, pre, hts, hb, ms', hms', rest⟩ := ht
        exact .inr ⟨hs, later, b, pre, hts, hb, ms', List.mem_cons_of_mem _ hms', rest⟩
    · exact nomatch h

/-- **The tier's guarantee: typing only, tier constants opaque.** If the
tier fold accepts `ds` at the index of a well-formed environment `env`, the
returned index is that of `env.extendOpaque ts`, which is well formed; no
tier constant is a constant of `env`; and every tier constant is typed in
its scope (`TypedIn`). -/
theorem checkTierC_typed {env : Env md} (hwf : EnvWF env) {ds : List (TierDecl md)}
    {fe' : FEnv md} {ts : List (TierConst md)}
    (h : checkTierC (mkFEnv env) ds = .ok (fe', ts)) :
    fe' = mkFEnv (env.extendOpaque ts) ∧ EnvWF (env.extendOpaque ts) ∧
      (∀ c ∈ ts, env.find? c.cv.name = none) ∧ ∀ c ∈ ts, TypedIn env ds ts c := by
  obtain ⟨hfe, hwfT, -, hall⟩ := checkTierFrom_typed (acc := []) hwf h
  have htyped : ∀ c ∈ ts, TypedIn env ds ts c := fun c hc =>
    (hall c hc).resolve_left (List.not_mem_nil)
  refine ⟨hfe, hwfT, ?_, htyped⟩
  intro c hc
  obtain ⟨-, -, -, pre, -, -, -, -, m, -, ⟨F, hI⟩, -⟩ := htyped c hc
  obtain ⟨-, -, -, -, hname, hfind⟩ := installConstantVal_typeFacts hI
  rw [hname]
  exact find?_of_extendOpaque hfind

/-! ## The fence -/

/-- **The logical fold's accept is well formed**: every term it stores
resolves in it (`EnvWF`). Stated at a set theory, like the entry theorems:
it is the model's well-formedness (`checkDecls_sound`). -/
theorem checkDecls_closed (V : Type w) [SetTheory V] {ev : Evidences md}
    {ds : Array (Declaration md)} {env : Env md}
    (h : checkDecls .verified ev ds = .ok env) : EnvWF env := by
  obtain ⟨mp⟩ := checkDecls_sound (V := V) rfl h
  exact mp.toEnvFacts.wf

/-- **The tier over the logical fold's accept**: the logical environment is
well formed, no tier constant resolves in it (so no accepted logical
declaration names one: every term it stores resolves), and every tier
constant is typed in its scope. -/
theorem checkDecls_checkTierC (V : Type w) [SetTheory V] {ev : Evidences md}
    {decls : Array (Declaration md)} {env : Env md} {ds : List (TierDecl md)}
    {fe' : FEnv md} {ts : List (TierConst md)}
    (hl : checkDecls .verified ev decls = .ok env)
    (ht : checkTierC (mkFEnv env) ds = .ok (fe', ts)) :
    EnvWF env ∧ (∀ c ∈ ts, env.find? c.cv.name = none) ∧
      EnvWF (env.extendOpaque ts) ∧ ∀ c ∈ ts, TypedIn env ds ts c := by
  have hwf := checkDecls_closed V hl
  obtain ⟨-, hwfT, hfresh, htyped⟩ := checkTierC_typed hwf ht
  exact ⟨hwf, hfresh, hwfT, htyped⟩

end Ix.Kernel.Tier
