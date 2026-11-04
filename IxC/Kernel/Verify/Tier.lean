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
import IxC.Kernel.Verify.Cached.KnotC
import IxC.Kernel.Verify.Cached.BridgeC
import IxC.Kernel.Verify.Cached.BridgeCS4
import IxC.Kernel.Verify.Cached.SimC

public section

/-!
# The typing tier's theorems

`checkTierC_typed`: if the tier fold accepts `ds` at the index of a
well-formed logical environment `env`, then

* the index it returns is the index of `env.extendOpaque ts`, which is
  well-formed;
* no tier constant is a constant of `env` (`env.find?` misses it);
* every tier constant `c` is **typed in its scope** (`TypedIn`): it comes
  from a declaration `d` of `ds`, its header is the install of `d`'s header
  (`installConstantVal`: the guards, the annotation, resolution), and in its
  scope (`ScopeOf`: the logical environment extended by the tier constants
  its check saw, every one opaque, as `axiomInfo`) its value annotates to a
  term whose type is convertible to its type and its type is a sort, or, for
  an axiom, its type is a sort, by derivations of the rules tier
  (`Rules.Infer`, `Rules.Red`, `Rules.DefEq`, through the bridge from the
  executable core).

The scope is Lean's lattice, by staging: a partial member's is its block and
the tier constants before it, **all partial** (partial code sees no unsafe
constant); an unsafe opaque's is empty, the logical environment (Lean checks
an opaque in safe mode); an unsafe member's is its block and every tier
constant before it; an unsafe axiom's, every tier constant before it.
Nothing here is about meaning: no model is claimed for a tier constant.

**The fence** is `checkDecls_closed` with the freshness above: the logical
fold's accept is well-formed (`EnvWF`: every term it stores resolves in it),
and no tier constant resolves in it. So no accepted logical declaration
names a tier constant.

The proofs are composition: the run lemmas of the cached fold
(`annotConstantValC_run`, `annotValC_run`, `checkPending_run`, and the
simulations of `infer` and `ensureSort`, `IxC/Kernel/Verify/Cached/`),
`EnvWF.cons` per install, and the bridge.
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

/-- **A header whose type is a sort** in `E` (an axiom's typing). -/
@[expose] def SortTyped (E : Env md) (c : ConstantVal md) : Prop :=
  ∃ s u, Rules.Infer E .full 0 c.type s ∧ Rules.Red E 0 s (.sort u)

/-- **A tier constant's scope** (Lean's lattice by staging), given the tier
constants `pre` checked before its declaration and the declaration's own
constants `blk`: the tier constants its check sees beside the logical
environment. A block member's is its block and every tier constant before it
(a partial block's are all partial, `TypedIn`); an unsafe opaque's is none
(Lean checks it in safe mode); an unsafe axiom's, the tier constants before
it. -/
@[expose] def ScopeOf (pre blk : List (TierConst md)) : TierDecl md → List (TierConst md)
  | .defs .. => blk ++ pre
  | .unsafeOpaque .. => []
  | .unsafeAxiom _ => pre

/-- **What the tier establishes of a constant `c`** of the declaration `d`,
whose constants are `blk`, checked after the tier constants `pre`: its
safety is `d`'s; a block member is the install of a member's header at the
extension by `pre`, and typed in its scope; an unsafe opaque, the only
constant of its declaration, is the install of its header at the logical
environment and typed in its scope (the logical environment); an unsafe
axiom, likewise alone, is the install of its header at the extension by
`pre`, its type a sort in its scope. -/
@[expose] def DeclTyped (env : Env md) (pre blk : List (TierConst md)) (c : TierConst md) :
    TierDecl md → Prop
  | .defs s ms => c.safety = s ∧ ∃ m ∈ ms,
      (∃ F, installConstantVal (fueledOps .verified F) (env.extendOpaque pre) m.1 = .ok c.cv) ∧
      Typed (env.extendOpaque (ScopeOf pre blk (.defs s ms))) c.cv m.2
  | .unsafeOpaque cv v => c.safety = .unsaf ∧ blk = [c] ∧
      (∃ F, installConstantVal (fueledOps .verified F) env cv = .ok c.cv) ∧
      Typed (env.extendOpaque (ScopeOf pre blk (.unsafeOpaque cv v))) c.cv v
  | .unsafeAxiom cv => c.safety = .unsaf ∧ blk = [c] ∧
      (∃ F, installConstantVal (fueledOps .verified F) (env.extendOpaque pre) cv = .ok c.cv) ∧
      SortTyped (env.extendOpaque (ScopeOf pre blk (.unsafeAxiom cv))) c.cv

/-- **`c` is a typed tier constant of `ts`, from `ds`**: `ts` is the
constants after `c`'s declaration, the declaration's own (`blk`), and the
ones before it (`pre`); `c` is typed in its scope as a constant of a
declaration `d` of `ds` (`DeclTyped`); and a partial member's scope is
partial: partial code sees no unsafe constant. -/
@[expose] def TypedIn (env : Env md) (ds : List (TierDecl md)) (ts : List (TierConst md))
    (c : TierConst md) : Prop :=
  ∃ later blk pre, ts = later ++ blk ++ pre ∧ c ∈ blk ∧ ∃ d ∈ ds, DeclTyped env pre blk c d ∧
    (d.stage = 0 → ∀ x ∈ ScopeOf pre blk d, x.safety = .part)

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

/-- What resolves in `env` resolves in an extension of it. -/
theorem constsResolve_extendOpaque {env : Env md} {e : Expr md} (h : e.constsResolve env = true) :
    ∀ ts : List (TierConst md), e.constsResolve (env.extendOpaque ts) = true
  | [] => h
  | t :: ts => by
    show e.constsResolve ⟨.axiomInfo t.cv :: (env.extendOpaque ts).consts⟩ = true
    exact Expr.constsResolve_mono (constsResolve_extendOpaque h ts)

/-- The headers pushed are the extension by the block. -/
theorem pushHeaders_mkFEnv : ∀ (E : Env md) (hs : List (ConstantVal md)) (s : Safety),
    pushHeaders (mkFEnv E) hs = mkFEnv (E.extendOpaque (blockConsts s hs))
  | E, [], _ => rfl
  | E, h :: hs, s => by
    rw [pushHeaders, push_mkFEnv, pushHeaders_mkFEnv _ hs s]
    congr 1
    simp [Env.extendOpaque, TierConst.infos, blockConsts, List.map_reverse]

/-- Every constant of a block's has the block's safety. -/
theorem blockConsts_safety {s : Safety} {hs : List (ConstantVal md)} :
    ∀ c ∈ blockConsts s hs, c.safety = s := by
  intro c hc
  simp only [blockConsts, List.mem_reverse, List.mem_map] at hc
  obtain ⟨_, -, rfl⟩ := hc
  rfl

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

/-- A header's type checked to be a sort at `mkFEnv E` (`sortC`): a sort in
`E`. -/
theorem sortC_ok {E : Env md} (hE : EnvWF E) {c : ConstantVal md}
    (hwty : Expr.WScoped 0 c.type) (h : sortC (mkFEnv E) c = .ok ()) : SortTyped E c := by
  simp only [sortC] at h
  split at h
  · exact nomatch h
  · rename_i r hrun
    obtain ⟨⟨⟩, s₄⟩ := r
    obtain ⟨jsty, s₂, hst, h₂⟩ := bindC_ok hrun
    obtain ⟨hs₂, wsty, ⟨rfl, hwsty⟩, F₁, hF₁⟩ :=
      (ssimC rfl E hE checkFuel).infer (CSOK.empty E) rfl hwty jsty s₂ hst
    obtain ⟨u, s₃, hsort, -⟩ := bindC_ok h₂
    obtain ⟨-, u', rfl, F₂, hF₂⟩ := opSIxC_sim rfl hE hs₂ rfl hwsty u s₃ hsort
    exact ⟨jsty, u, Rules.inferTypeCore_bridge hF₁, Rules.whnf_bridge (ensureSortCore_inv hF₂)⟩

/-! ## One declaration -/

/-- A related pair for every element on the right. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Pairs R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => (List.not_mem_nil hb).elim
  | a :: _, _ :: _, .cons hr rest, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hr⟩
    · obtain ⟨a', ha', hr'⟩ := forall₂_mem_right rest hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

/-- **A definition block**, accepted at `mkFEnv E`: the returned index is
the extension by its constants, which is well formed, every one of its
constants has its safety, and each is the install of a member's header at
`E`, typed in the extension. -/
theorem blockC_ok {E : Env md} (hE : EnvWF E) {s : Safety} {ms : List (ConstantVal md × Expr md)}
    {fe' : FEnv md} {blk : List (TierConst md)} (h : blockC (mkFEnv E) s ms = .ok (fe', blk)) :
    fe' = mkFEnv (E.extendOpaque blk) ∧ EnvWF (E.extendOpaque blk) ∧
      ∀ c ∈ blk, c.safety = s ∧ ∃ m ∈ ms,
        (∃ F, installConstantVal (fueledOps .verified F) E m.1 = .ok c.cv) ∧
        Typed (E.extendOpaque blk) c.cv m.2 := by
  simp only [blockC] at h
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
  have hfe := pushHeaders_mkFEnv E hs s
  have h₂ := headersC_ok hE hhs
  have hfacts : ∀ c ∈ hs, c.type.hasFvar = false ∧ c.type.allLevelParamsDefined c.levelParams = true ∧
      c.type.constsResolve E = true ∧ c.type.looseBVarsBounded 0 = true := by
    intro c hc
    obtain ⟨m, -, ⟨⟨F, hI⟩, -⟩⟩ := forall₂_mem_right h₂ hc
    obtain ⟨g1, g2, g3, g4, -⟩ := installConstantVal_typeFacts hI
    exact ⟨g1, g2, g3, g4⟩
  have hE' := envWF_blockConsts hE s hfacts
  rw [hfe] at hvals
  have h₃ := valuesC_ok hE' (fun _ _ hr => hr.2) h₂ hvals
  refine ⟨hfe, hE', ?_⟩
  intro c hc
  have hsafe := blockConsts_safety c hc
  simp only [blockConsts, List.mem_reverse, List.mem_map] at hc
  obtain ⟨cv, hcv, rfl⟩ := hc
  obtain ⟨m, hm, ⟨⟨F, hI⟩, -⟩, hty⟩ := forall₂_mem_right h₃ hcv
  exact ⟨hsafe, m, hm, ⟨F, hI⟩, hty⟩

/-- A single header installed at `E` with its type-slot facts at `E`:
the extension by it is well formed. -/
theorem envWF_single {E : Env md} (hE : EnvWF E) (s : Safety) {cvA : ConstantVal md}
    (hf : cvA.type.hasFvar = false ∧ cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
      cvA.type.constsResolve E = true ∧ cvA.type.looseBVarsBounded 0 = true) :
    EnvWF (E.extendOpaque (blockConsts s [cvA])) :=
  envWF_blockConsts hE s fun c hc => by
    rcases List.mem_singleton.mp hc with rfl
    exact hf

/-- A single header pushed is the extension by it. -/
theorem push_single (E : Env md) (s : Safety) (cvA : ConstantVal md) :
    (mkFEnv E).push (.axiomInfo cvA) = mkFEnv (E.extendOpaque (blockConsts s [cvA])) :=
  pushHeaders_mkFEnv E [cvA] s

/-- **An unsafe opaque**, accepted with the logical view `mkFEnv env` at
`mkFEnv E`, `E` an extension of `env`: the returned index is the extension
by its one constant, which is well formed, an unsafe constant that is the
install of its header at `env` and typed in `env`. -/
theorem opaqueC_ok {env : Env md} (henv : EnvWF env) {acc : List (TierConst md)}
    (hE : EnvWF (env.extendOpaque acc)) {cv : ConstantVal md} {v : Expr md}
    {fe' : FEnv md} {blk : List (TierConst md)}
    (h : opaqueC (mkFEnv env) (mkFEnv (env.extendOpaque acc)) cv v = .ok (fe', blk)) :
    fe' = mkFEnv ((env.extendOpaque acc).extendOpaque blk) ∧
      EnvWF ((env.extendOpaque acc).extendOpaque blk) ∧
      ∃ c, blk = [c] ∧ c.safety = .unsaf ∧
        (∃ F, installConstantVal (fueledOps .verified F) env cv = .ok c.cv) ∧ Typed env c.cv v := by
  simp only [opaqueC] at h
  split at h
  · exact nomatch h
  rename_i cvA jty s₁ ha
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  rename_i hval
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨-, hcvA, hwty, F, hI⟩ := annotConstantValC_run rfl henv (CSOK.empty env) ha
  have hwty' : Expr.WScoped 0 cvA.type := by rw [hcvA]; exact hwty
  obtain ⟨g1, g2, g3, g4, -⟩ := installConstantVal_typeFacts hI
  refine ⟨push_single _ .unsaf cvA,
    envWF_single hE .unsaf ⟨g1, g2, constsResolve_extendOpaque g3 acc, g4⟩,
    ⟨cvA, .unsaf⟩, rfl, rfl, ⟨F, hI⟩, valueC_ok henv hwty' hval⟩

/-- **An unsafe axiom**, accepted at `mkFEnv E`: the returned index is the
extension by its one constant, which is well formed, an unsafe constant that
is the install of its header at `E`, its type a sort in `E`. -/
theorem axiomC_ok {E : Env md} (hE : EnvWF E) {cv : ConstantVal md}
    {fe' : FEnv md} {blk : List (TierConst md)} (h : axiomC (mkFEnv E) cv = .ok (fe', blk)) :
    fe' = mkFEnv (E.extendOpaque blk) ∧ EnvWF (E.extendOpaque blk) ∧
      ∃ c, blk = [c] ∧ c.safety = .unsaf ∧
        (∃ F, installConstantVal (fueledOps .verified F) E cv = .ok c.cv) ∧ SortTyped E c.cv := by
  simp only [axiomC] at h
  split at h
  · exact nomatch h
  rename_i cvA jty s₁ ha
  split at h
  · exact nomatch h
  rename_i hsort
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨-, hcvA, hwty, F, hI⟩ := annotConstantValC_run rfl hE (CSOK.empty E) ha
  have hwty' : Expr.WScoped 0 cvA.type := by rw [hcvA]; exact hwty
  obtain ⟨g1, g2, g3, g4, -⟩ := installConstantVal_typeFacts hI
  exact ⟨push_single _ .unsaf cvA, envWF_single hE .unsaf ⟨g1, g2, g3, g4⟩,
    ⟨cvA, .unsaf⟩, rfl, rfl, ⟨F, hI⟩, sortC_ok hE hwty' hsort⟩

/-- **One tier declaration**, accepted with the logical view `mkFEnv env` at
the index of the extension by `acc`: the returned index is the extension by
its constants `blk` too, which is well formed; every constant of `blk` has
the declaration's safety and is typed in its scope (`DeclTyped`). -/
theorem checkDeclC_ok {env : Env md} (henv : EnvWF env) {acc : List (TierConst md)}
    (hE : EnvWF (env.extendOpaque acc)) {d : TierDecl md} {fe' : FEnv md}
    {blk : List (TierConst md)}
    (h : checkDeclC (mkFEnv env) (mkFEnv (env.extendOpaque acc)) d = .ok (fe', blk)) :
    fe' = mkFEnv (env.extendOpaque (blk ++ acc)) ∧ EnvWF (env.extendOpaque (blk ++ acc)) ∧
      ∀ c ∈ blk, c.safety = d.safety ∧ DeclTyped env acc blk c d := by
  rw [← extendOpaque_append]
  match d, h with
  | .defs s ms, h =>
    obtain ⟨hfe, hwf, hall⟩ := blockC_ok hE h
    refine ⟨hfe, hwf, fun c hc => ?_⟩
    obtain ⟨hs, m, hm, hI, hty⟩ := hall c hc
    refine ⟨hs, hs, m, hm, hI, ?_⟩
    simpa only [ScopeOf, extendOpaque_append] using hty
  | .unsafeOpaque cv v, h =>
    obtain ⟨hfe, hwf, c, rfl, hs, hI, hty⟩ := opaqueC_ok henv hE h
    refine ⟨hfe, hwf, fun c' hc' => ?_⟩
    rcases List.mem_singleton.mp hc' with rfl
    exact ⟨hs, hs, rfl, hI, hty⟩
  | .unsafeAxiom cv, h =>
    obtain ⟨hfe, hwf, c, rfl, hs, hI, hty⟩ := axiomC_ok hE h
    refine ⟨hfe, hwf, fun c' hc' => ?_⟩
    rcases List.mem_singleton.mp hc' with rfl
    exact ⟨hs, hs, rfl, hI, hty⟩

/-! ## The fold -/

/-- **The fold from an accumulator**, with the logical view `mkFEnv env`:
the returned index is the extension by the constants, which is well formed,
and every new constant is typed in its scope as a constant of one of the
declarations, whose constants all have its safety. -/
theorem checkTierFrom_typed {env : Env md} (henv : EnvWF env) :
    ∀ {xs : List (Nat × TierDecl md)} {acc : List (TierConst md)}
      {fe' : FEnv md} {ts : List (TierConst md)},
      EnvWF (env.extendOpaque acc) →
      checkTierFrom (mkFEnv env) (mkFEnv (env.extendOpaque acc)) acc xs = .ok (fe', ts) →
      fe' = mkFEnv (env.extendOpaque ts) ∧ EnvWF (env.extendOpaque ts) ∧
        (∃ new, ts = new ++ acc) ∧
        ∀ c ∈ ts, c ∈ acc ∨ ∃ later blk pre, ts = later ++ blk ++ pre ∧ c ∈ blk ∧
          ∃ x ∈ xs, DeclTyped env pre blk c x.2 ∧ ∀ y ∈ blk, y.safety = x.2.safety
  | [], acc, fe', ts, hwf, h => by
    simp only [checkTierFrom, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hwf, ⟨[], rfl⟩, fun c hc => .inl hc⟩
  | (i, d) :: xs, acc, fe', ts, hwf, h => by
    simp only [checkTierFrom] at h
    split at h
    · rename_i fe₁ blk hd
      obtain ⟨rfl, hwf₁, hblk⟩ := checkDeclC_ok henv hwf hd
      obtain ⟨hfe, hwfT, ⟨new, hnew⟩, hall⟩ := checkTierFrom_typed henv hwf₁ h
      refine ⟨hfe, hwfT, ⟨new ++ blk, by rw [hnew, List.append_assoc]⟩, ?_⟩
      intro c hc
      rcases hall c hc with hin | ht
      · rcases List.mem_append.mp hin with hb | ha
        · obtain ⟨-, hty⟩ := hblk c hb
          exact .inr ⟨new, blk, acc, by rw [hnew, List.append_assoc], hb, (i, d),
            List.mem_cons_self, hty, fun y hy => (hblk y hy).1⟩
        · exact .inl ha
      · obtain ⟨later, b, pre, hts, hb, x, hx, rest⟩ := ht
        exact .inr ⟨later, b, pre, hts, hb, x, List.mem_cons_of_mem _ hx, rest⟩
    · exact nomatch h

/-- The fold over two lists is the fold over the first, then over the
second from where it stopped. -/
theorem checkTierFrom_append {fe₀ : FEnv md} :
    ∀ {xs ys : List (Nat × TierDecl md)} {fe : FEnv md} {acc : List (TierConst md)}
      {r : FEnv md × List (TierConst md)},
      checkTierFrom fe₀ fe acc (xs ++ ys) = .ok r →
      ∃ fe₁ acc₁, checkTierFrom fe₀ fe acc xs = .ok (fe₁, acc₁) ∧
        checkTierFrom fe₀ fe₁ acc₁ ys = .ok r
  | [], ys, fe, acc, r, h => ⟨fe, acc, rfl, h⟩
  | (i, d) :: xs, ys, fe, acc, r, h => by
    simp only [List.cons_append, checkTierFrom] at h ⊢
    split at h
    · exact checkTierFrom_append h
    · exact nomatch h

/-- A declaration of stage 0 is a partial block. -/
theorem TierDecl.stage_eq_zero {d : TierDecl md} (h : d.stage = 0) : ∃ ms, d = .defs .part ms := by
  cases d with
  | defs s ms =>
    cases s with
    | part => exact ⟨ms, rfl⟩
    | unsaf => simp [TierDecl.stage] at h
  | unsafeOpaque cv v => simp [TierDecl.stage] at h
  | unsafeAxiom cv => simp [TierDecl.stage] at h

/-- The declarations with their positions, from position `i`. -/
theorem mem_indexed {ds : List (TierDecl md)} {x : Nat × TierDecl md} :
    ∀ {i : Nat}, x ∈ indexed i ds → x.2 ∈ ds := by
  induction ds with
  | nil => intro i hx; simp [indexed] at hx
  | cons d ds ih =>
    intro i hx
    simp only [indexed, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hx)

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
  simp only [checkTierC, staged] at h
  obtain ⟨fe₁, ts₁, h₁, h₂⟩ := checkTierFrom_append h
  -- the partial stage, from nothing
  obtain ⟨rfl, hwf₁, -, hall₁⟩ :=
    checkTierFrom_typed (acc := []) hwf (by exact hwf) (by exact h₁)
  -- every constant of the partial stage is partial
  have hpart : ∀ c ∈ ts₁, c.safety = .part := by
    intro c hc
    rcases hall₁ c hc with hin | ⟨-, blk, -, -, hb, x, hx, -, hsafe⟩
    · exact absurd hin List.not_mem_nil
    · obtain ⟨-, hx0⟩ := List.mem_filter.mp hx
      obtain ⟨ms, hxd⟩ := TierDecl.stage_eq_zero (by simpa using hx0)
      simp [hsafe c hb, hxd, TierDecl.safety]
  -- the unsafe stages, from there
  obtain ⟨hfe, hwfT, ⟨new, rfl⟩, hall⟩ := checkTierFrom_typed hwf hwf₁ h₂
  have htyped : ∀ c ∈ new ++ ts₁, TypedIn env ds (new ++ ts₁) c := by
    intro c hc
    rcases hall c hc with hin | ⟨later, blk, pre, hts, hb, x, hx, hty, hsafe⟩
    · rcases hall₁ c hin with hnil | ⟨later₁, blk, pre, hts₁, hb, x, hx, hty, hsafe⟩
      · exact absurd hnil List.not_mem_nil
      · obtain ⟨hxm, hx0⟩ := List.mem_filter.mp hx
        obtain ⟨ms, hxd⟩ := TierDecl.stage_eq_zero (by simpa using hx0)
        refine ⟨new ++ later₁, blk, pre, by rw [hts₁]; simp, hb, x.2, mem_indexed hxm, hty,
          fun _ y hy => ?_⟩
        rw [hxd] at hy hsafe
        simp only [ScopeOf, List.mem_append] at hy
        rcases hy with hy | hy
        · exact hsafe y hy
        · exact hpart y (by rw [hts₁]; simp [hy])
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hxm, hx1⟩ := List.mem_filter.mp hx
        refine ⟨later, blk, pre, hts, hb, x.2, mem_indexed hxm, hty, fun h0 => ?_⟩
        simp only [beq_iff_eq] at hx1
        exact absurd (hx1.symm.trans h0) (by decide)
      · obtain ⟨hxm, hx2⟩ := List.mem_filter.mp hx
        refine ⟨later, blk, pre, hts, hb, x.2, mem_indexed hxm, hty, fun h0 => ?_⟩
        simp only [beq_iff_eq] at hx2
        exact absurd (hx2.symm.trans h0) (by decide)
  refine ⟨hfe, hwfT, ?_, htyped⟩
  intro c hc
  obtain ⟨later, blk, pre, -, hb, d, -, hty, -⟩ := htyped c hc
  have key : ∃ cv F, ∃ E : List (TierConst md),
      installConstantVal (fueledOps .verified F) (env.extendOpaque E) cv = .ok c.cv := by
    match d, hty with
    | .defs _ _, ⟨_, m, _, ⟨F, hI⟩, _⟩ => exact ⟨m.1, F, pre, hI⟩
    | .unsafeOpaque cv _, ⟨_, _, ⟨F, hI⟩, _⟩ => exact ⟨cv, F, [], hI⟩
    | .unsafeAxiom cv, ⟨_, _, ⟨F, hI⟩, _⟩ => exact ⟨cv, F, pre, hI⟩
  obtain ⟨cv, F, E, hI⟩ := key
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
