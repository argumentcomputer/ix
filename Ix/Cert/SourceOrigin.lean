import Ix.Cert.SourceNames

/-! # Base origins of generated declaration names

Both generator rungs emit names whose bases belong to the input block's
type, constructor or recursor names. The concrete endpoints instantiate the
internal scope from those inputs and require only actual generation success.
Arbitrary input keys are allowed, so their bases are taken explicitly.

The proof reuses SourceNames.Generated's unary producer framework, adding
membership-aware loops and targeted lookup/name leaves. It does not inspect
expression bodies. Name distinctness, no-drop, accepted declaration streams,
Source/Ixon correspondence and the final compiler theorem remain separate.
-/

namespace Ix.Cert.SourceOrigin

open Ix.Kernel Ix.Kernel.Frontend.InModel SourceNames.Generated

def roots (b : BlockRec md) : List (Key md) :=
  ((b.types.map (·.cv.name)) ++ b.ctors.map (·.cv.name) ++ b.recs.map (·.cv.name)).map Key.base

/-- Internal fixed root set for the shared unary producer walk. -/
class Scope (md : Mode) where
  bases : List (Key md)

def Named [s : Scope md] (k : Key md) : Prop := k.base ∈ s.bases

section Origin

variable [Scope md]

local instance (priority := 2000) : Safe (Declaration md) := ⟨fun d => ∀ k ∈ d.names, Named k⟩
local instance (priority := 2000) : Safe (Ix.Kernel.ConstantInfo md) := ⟨fun c => Named c.name⟩
local instance (priority := 2000) : Safe (IndTypeRec md) := ⟨fun c => Named c.cv.name⟩
local instance (priority := 2000) : Safe (IndCtorRec md) := ⟨fun c => Named c.cv.name⟩
local instance (priority := 2000) : Safe (IndRecRec md) := ⟨fun c => Named c.cv.name⟩
local instance (priority := 2000) : Safe (MCtor md) := ⟨fun c => Named c.c.cv.name⟩
local instance (priority := 2100) : Safe (Key md × Nat × Ix.Kernel.Expr md × List Nat) := ⟨fun c => Named c.1⟩

def BlockOrigin (b : BlockRec md) : Prop :=
  Safe.holds b.types ∧ Safe.holds b.ctors ∧ Safe.holds b.recs

theorem named_aux {k : Key md} (d : Derived) (h : Named k) : Named (auxKey k d) := h

theorem origin_ctors (lps : List LevelParam) (nP : Nat)
    {cs : List (Key md × Nat × Ix.Kernel.Expr md × List Nat)} (hc : Safe.holds cs) :
    Safe.holds (cs.map fun (c, nF, ty, _) => Ix.Kernel.ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) := by
  intro ci hi; obtain ⟨⟨c, nF, ty, flags⟩, hm, rfl⟩ := List.mem_map.mp hi; exact hc _ hm

theorem origin_ind {block : List (Ix.Kernel.ConstantInfo md)} (n : Nat)
    (hs : Safe.holds block) : Safe.holds (.indDecl block n : Declaration md) := by
  intro k hk; obtain ⟨ci, hi, rfl⟩ := List.mem_map.mp hk; exact hs ci hi

theorem origin_defn (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) (h : ReducibilityHint)
    (hn : Named cv.name) : Safe.holds (.defnDecl cv v h : Declaration md) := by
  simpa [Safe.holds, Declaration.names] using hn

theorem origin_thm (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md)
    (hn : Named cv.name) : Safe.holds (.thmDecl cv v : Declaration md) := by
  simpa [Safe.holds, Declaration.names] using hn

variable {α β σ ε : Type}

theorem ex_forIn_mem [Safe σ] (xs : List α) (body : α → σ → Except ε (ForInStep σ))
    (hb : ∀ x ∈ xs, ∀ s, Safe.holds s → ExSafe (body x s)) :
    ∀ s, Safe.holds s → ExSafe (forIn xs s body) := by
  induction xs with
  | nil => intro s hs; exact ex_pure hs
  | cons x xs ih =>
    intro s hs; rw [List.forIn_cons]; apply ex_bind (hb x List.mem_cons_self s hs)
    intro step hstep; cases step with
    | done v => exact ex_pure hstep
    | yield v => exact ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) v hstep

theorem ex_forIn_array_mem [Safe σ] (xs : Array α) (body : α → σ → Except ε (ForInStep σ))
    (hb : ∀ x ∈ xs, ∀ s, Safe.holds s → ExSafe (body x s)) (s : σ) (hs : Safe.holds s) :
    ExSafe (ForIn.forIn xs s body) := by
  rw [← Array.forIn_toList]; exact ex_forIn_mem _ _ (fun x hx => hb x (Array.mem_toList_iff.mp hx)) s hs

theorem ex_mapM_mem [Safe β] (f : α → Except ε β) (xs : List α)
    (h : ∀ a ∈ xs, ExSafe (f a)) : ExSafe (xs.mapM f) := by
  induction xs with
  | nil => intro ys hy; cases hy; simp [Safe.holds]
  | cons x xs ih =>
    simp only [List.mapM_cons]; apply ex_bind (h x List.mem_cons_self); intro y hy
    apply ex_bind (ih fun a ha => h a (List.mem_cons_of_mem _ ha)); intro ys hys
    exact ex_pure (safe_cons hy hys)

theorem safe_getD [Safe α] {xs : List α} (h : Safe.holds xs) {i : Nat}
    (hi : i ∈ List.range xs.length) (d : α) : Safe.holds (xs.getD i d) := by
  have bound := List.mem_range.mp hi
  rw [← List.getElem_eq_getD (h := bound) d]
  exact h _ (List.getElem_mem bound)

theorem safe_find [Safe α] {xs : List α} (h : Safe.holds xs) {p : α → Bool} {a : α}
    (ha : xs.find? p = some a) : Safe.holds a := h a (List.mem_of_find?_eq_some ha)

theorem safe_getElem [Safe α] {xs : List α} (h : Safe.holds xs) {i : Nat} {a : α}
    (ha : xs[i]? = some a) : Safe.holds a := h a (List.mem_of_getElem? ha)

theorem safe_head [Safe α] {xs : List α} (h : Safe.holds xs) {a : α} {as : List α}
    (ha : xs = a :: as) : Safe.holds a := h a (ha ▸ List.mem_cons_self)

theorem mctor_mem {cs : List (MCtor md)} (h : Safe.holds cs) {c : MCtor md}
    (hc : c ∈ cs) : Named c.c.cv.name := h c hc

theorem named_find {cs : List (IndCtorRec md)} (h : Safe.holds cs) {k : Key md} {c : IndCtorRec md}
    (hc : cs.find? (·.cv.name == k) = some c) : Named k := by
  have found : (c.cv.name == k) = true :=
    List.find?_some (p := fun x : IndCtorRec md => x.cv.name == k) hc
  have hn : c.cv.name = k := beq_iff_eq.mp found
  rw [← hn]; exact safe_find h hc

open Lean Elab Tactic in
elab "origin_step" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  if t.isAppOf ``ExSafe then
    let e := t.getAppArgs.back!.consumeMData
    if e.isAppOf ``ForIn.forIn then evalTactic (← `(tactic| first | apply ex_forIn_mem | apply ex_forIn_array_mem))
    else if e.isAppOf ``List.mapM then evalTactic (← `(tactic| apply ex_mapM_mem))
    else throwError "not a membership-aware producer step"
  else if t.isAppOf ``Safe.holds then
    let e := t.getAppArgs.back!.consumeMData
    if e.isAppOf ``List.map then evalTactic (← `(tactic| apply origin_ctors))
    else if e.isAppOf ``Ix.Kernel.Declaration.indDecl then evalTactic (← `(tactic| apply origin_ind))
    else if e.isAppOf ``Ix.Kernel.Declaration.defnDecl then evalTactic (← `(tactic| apply origin_defn))
    else if e.isAppOf ``Ix.Kernel.Declaration.thmDecl then evalTactic (← `(tactic| apply origin_thm))
    else evalTactic (← `(tactic| change Named _))
  else throwError "not an origin goal"

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 200000 in
theorem classifyCtor_origin (T : Key md) (members : List (Key md × Nat × Nat))
    (lps : List LevelParam) (nP k J : Nat) (minor : Option (Ix.Kernel.Expr md))
    (m j : Nat) (c : IndCtorRec md) (hc : Safe.holds c) :
    ExSafe (classifyCtor T members lps nP k J minor m j c) := by
  unfold classifyCtor
  simp only [← Bool.cond_eq_ite]
  name_repeat 2000 first
    | name_all
    | origin_step
    | name_step
    | assumption
    | rfl
    | solve | simp [Safe.holds]
    | (split)

open Lean Elab Tactic in
elab "origin_ctor" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``ExSafe && t.getAppArgs.back!.consumeMData.isAppOf ``classifyCtor do
    throwError "not a constructor-classification producer"
  evalTactic (← `(tactic| apply classifyCtor_origin))

open Lean Elab Tactic in
elab "origin_leaf" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``Safe.holds || t.isAppOf ``Named do throwError "not a name-origin leaf"

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 3000 in
theorem genMutual_origin (ctx : Ix.Kernel.Frontend.InModel.Ctx md) (b : BlockRec md)
    (hb : BlockOrigin b) : ExSafe (genMutual ctx b) := by
  obtain ⟨ht, hc, hr⟩ := hb
  unfold genMutual
  simp only [← Bool.cond_eq_ite]
  name_repeat 4000 first
    | name_all
    | origin_ctor
    | origin_step
    | name_step
    | assumption
    | rfl
    | solve | exact safe_getD ht (by assumption) _
    | solve | exact safe_find hc (by assumption)
    | solve | exact safe_getElem hr (by assumption)
    | solve | exact safe_head ht (by assumption)
    | solve | exact mctor_mem (by assumption) (by assumption)
    | solve | apply_assumption
    | (origin_leaf; solve | simp [Safe.holds])
    | (split)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
theorem genNested_origin (ctx : Ix.Kernel.Frontend.InModel.Ctx md) (b : BlockRec md)
    (hb : BlockOrigin b) : ExSafe (genNested ctx b) := by
  obtain ⟨ht, hc, hr⟩ := hb
  unfold genNested
  simp only [← Bool.cond_eq_ite]
  name_repeat 12000 first
    | name_all
    | origin_step
    | name_step
    | assumption
    | rfl
    | (origin_leaf; first
      | solve | exact safe_getD ht (by assumption) _
      | solve | exact safe_find hc (by assumption)
      | solve | exact safe_getElem hr (by assumption)
      | solve | exact safe_head ht (by assumption)
      | solve | simpa only [Named, modelName, auxKey, Key.base] using (named_find hc (by assumption))
      | solve | apply_assumption)
    | (origin_leaf; solve | simp [Safe.holds])
    | (split)

end Origin

/-- The input names themselves supply the internal producer scope. -/
theorem blockOrigin_roots (b : BlockRec md) : @BlockOrigin md ⟨roots b⟩ b := by
  change (∀ t ∈ b.types, t.cv.name.base ∈ roots b) ∧
    (∀ c ∈ b.ctors, c.cv.name.base ∈ roots b) ∧ (∀ r ∈ b.recs, r.cv.name.base ∈ roots b)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [roots, List.mem_map, List.mem_append]
    exact ⟨t.cv.name, Or.inl (Or.inl ⟨t, ht, rfl⟩), rfl⟩
  · intro c hc
    simp only [roots, List.mem_map, List.mem_append]
    exact ⟨c.cv.name, Or.inl (Or.inr ⟨c, hc, rfl⟩), rfl⟩
  · intro r hr
    simp only [roots, List.mem_map, List.mem_append]
    exact ⟨r.cv.name, Or.inr ⟨r, hr, rfl⟩, rfl⟩

/-- Every emitted name is rooted at an input block name. Input keys need
not be ordinary, so the conclusion takes their bases explicitly. -/
theorem genMutual_bases {ctx : Ix.Kernel.Frontend.InModel.Ctx md} {b : BlockRec md}
    {ds : List (Declaration md)} (h : genMutual ctx b = .ok ds) :
    ∀ d ∈ ds, ∀ k ∈ d.names, k.base ∈ roots b := by
  letI : Scope md := ⟨roots b⟩
  exact genMutual_origin ctx b (blockOrigin_roots b) ds h

theorem genNested_bases {ctx : Ix.Kernel.Frontend.InModel.Ctx md} {b : BlockRec md}
    {ds : List (Declaration md)} (h : genNested ctx b = .ok ds) :
    ∀ d ∈ ds, ∀ k ∈ d.names, k.base ∈ roots b := by
  letI : Scope md := ⟨roots b⟩
  exact genNested_origin ctx b (blockOrigin_roots b) ds h

/-- Successful generation alone supplies base origin. No distinctness,
acceptance, context agreement or no-drop premise is required or concluded. -/
theorem generate_bases {ctx : Ix.Kernel.Frontend.InModel.Ctx md} {b : BlockRec md}
    {ds : List (Declaration md)} (h : generate ctx b = .ok ds) :
    ∀ d ∈ ds, ∀ k ∈ d.names, k.base ∈ roots b := by
  unfold generate at h
  split at h
  · exact genNested_bases h
  · exact genMutual_bases h

end Ix.Cert.SourceOrigin
