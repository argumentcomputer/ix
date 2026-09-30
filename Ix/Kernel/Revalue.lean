/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Claims
import Ix.Kernel.Model.Extension

/-! # Constants valued by closed terms

A block can be admitted through an encoding: a canonical block the kernel
already supports is installed, and the supplied constants are then valued by
closed terms over it (`σ`), such as a constructor that takes its fields in
another order. `Assignment.revalue` is that assignment, and interpretation
commutes with it: a term denotes under the revalued assignment what the term
with the constants replaced (`AExpr.substConsts`) denotes under the original
one (`interp_revalue`, `wellDenoted_revalue`). So claims the kernel checks
about the substituted terms transfer to the supplied constants. -/

namespace Ix.Kernel.Model

open SetTheory

universe u v

variable {β : Type u}

/-- Replace the constants `σ` values by its terms, at each occurrence's
universe instance. -/
def AExpr.substConsts (σ : ConstRef β → Option (AExpr β)) : AExpr β → AExpr β
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls =>
    match σ r with
    | some w => w.instL ls
    | none => .const r ls
  | .app f a => .app (f.substConsts σ) (a.substConsts σ)
  | .lam p a b => .lam p (a.substConsts σ) (b.substConsts σ)
  | .forallE p a b => .forallE p (a.substConsts σ) (b.substConsts σ)
  | .letE t w b => .letE (t.substConsts σ) (w.substConsts σ) (b.substConsts σ)
  | .proj r i x => .proj r i (x.substConsts σ)
  | .natLit r n => .natLit r n

variable {V : Type v} [SetTheory V]

/-- The assignment valuing each constant of `σ` by its term's denotation. -/
noncomputable def Assignment.revalue (constants : Assignment β V)
    (σ : ConstRef β → Option (AExpr β)) : Assignment β V := fun r levels =>
  match σ r with
  | some w => interp constants levels (fun _ => empty) w
  | none => constants r levels

/-- Every term of `σ` is closed. -/
def ClosedTerms (σ : ConstRef β → Option (AExpr β)) : Prop :=
  ∀ r w, σ r = some w → ∃ n, w.Scope n 0

theorem interp_revalue {σ : ConstRef β → Option (AExpr β)} (hσ : ClosedTerms σ)
    (constants : Assignment β V) (levels : List Nat) (e : AExpr β) (env : Nat → V) :
    interp (constants.revalue σ) levels env e = interp constants levels env (e.substConsts σ) := by
  induction e generalizing env with
  | const r ls =>
    simp only [interp, AExpr.substConsts, Assignment.revalue]
    cases hr : σ r with
    | none => rfl
    | some w =>
      obtain ⟨n, hs⟩ := hσ r w hr
      simp only [interp_instL]
      exact interp_closed w constants _ hs _ _
  | app f a hf ha => simp only [interp, AExpr.substConsts, hf, ha]
  | lam p a b ha hb | forallE p a b ha hb =>
    simp only [interp, AExpr.substConsts, ha]
    congr 1
    funext x
    exact hb _
  | letE t w b ht hw hb => simp only [interp, AExpr.substConsts, hw, hb]
  | proj r i x hx => simp only [interp, AExpr.substConsts, hx]
  | bvar _ | sort _ | natLit _ _ => rfl

/-- Every term of `σ` is well denoted at every universe instance. -/
def WellDenotedTerms (constants : Assignment β V) (σ : ConstRef β → Option (AExpr β)) : Prop :=
  ∀ r w, σ r = some w → ∀ levels env, WellDenoted constants levels env w

theorem wellDenoted_revalue {σ : ConstRef β → Option (AExpr β)} (hσ : ClosedTerms σ)
    {constants : Assignment β V} (hw : WellDenotedTerms constants σ) (levels : List Nat)
    (e : AExpr β) (env : Nat → V) :
    WellDenoted (constants.revalue σ) levels env e ↔
      WellDenoted constants levels env (e.substConsts σ) := by
  induction e generalizing env with
  | const r ls =>
    simp only [WellDenoted, AExpr.substConsts]
    cases hr : σ r with
    | none => simp [WellDenoted]
    | some w =>
      simp only [wellDenoted_instL, true_iff]
      exact hw r w hr _ env
  | app f a hf ha =>
    simp only [WellDenoted, AExpr.substConsts, hf, ha, interp_revalue hσ]
  | lam p a b ha hb =>
    simp only [WellDenoted, AExpr.substConsts, ha, hb, interp_revalue hσ]
  | forallE p a b ha hb =>
    simp only [WellDenoted, AExpr.substConsts, ha, hb, interp_revalue hσ]
  | letE t w b ht hw' hb =>
    simp only [WellDenoted, AExpr.substConsts, ht, hw', hb, interp_revalue hσ]
  | proj r i x hx => simp only [WellDenoted, AExpr.substConsts, hx]
  | bvar _ | sort _ | natLit _ _ => simp [WellDenoted, AExpr.substConsts]

/-! ## Replacing a block by revalued entries -/

variable [DecidableEq β]

/-- A supplied entry, valued by a closed term over the environment it
replaces. -/
structure Revalued (β : Type u) where
  ref : ConstRef β
  entry : ConstantEntry β
  term : AExpr β

namespace Revalued

def find (block : List (Revalued β)) (r : ConstRef β) : Option (Revalued β) :=
  block.find? fun b => decide (b.ref = r)

/-- Each supplied constant's valuing term. -/
def valuation (block : List (Revalued β)) : ConstRef β → Option (AExpr β) := fun r =>
  (find block r).map (·.term)

/-- The environment with the supplied entries in place of the old ones. -/
def environment (block : List (Revalued β)) (before : Environment β) : Environment β := fun r =>
  match find block r with
  | some b => some b.entry
  | none => before r

theorem find_ref {block : List (Revalued β)} {r : ConstRef β} {b : Revalued β}
    (h : find block r = some b) : b ∈ block ∧ b.ref = r := by
  unfold find at h
  exact ⟨List.mem_of_find?_eq_some h,
    of_decide_eq_true (List.find?_some (p := fun b : Revalued β => decide (b.ref = r)) h)⟩

end Revalued

/-- A fact carrying only arities, whose meaning is trivial. -/
def ConstantFact.Arity : ConstantFact β → Prop
  | .recursor .. | .structure .. | .height _ => True
  | _ => False

instance {fact : ConstantFact β} : Decidable fact.Arity := by
  cases fact <;> unfold ConstantFact.Arity <;> infer_instance

omit [DecidableEq β] in
theorem ConstantFact.Arity.meaning {fact : ConstantFact β} (h : fact.Arity)
    (constants : Assignment β V) (owner : ConstRef β) (levels : List Nat) (env : Nat → V) :
    fact.Meaning constants owner levels env := by
  cases fact <;> first | trivial | exact h.elim

/-- Every constant an entry mentions. -/
def ConstantEntry.references (entry : ConstantEntry β) : List (ConstRef β) :=
  entry.type.references ++ (entry.body.map AExpr.references).getD [] ++
    entry.equations.flatMap (fun q => q.lhs.references ++ q.rhs.references) ++
    entry.facts.flatMap ConstantFact.references

/-- What the kernel establishes about a revalued entry over the environment it
replaces: its term is closed and typed at the supplied type with the supplied
constants substituted, and each supplied equation holds with them
substituted. -/
structure Revalued.Claims (before : Environment β) (σ : ConstRef β → Option (AExpr β))
    (b : Revalued β) : Prop where
  closed : b.term.Scope b.entry.universes 0
  body : b.entry.body = none
  typed : TypingClaim.{u,v} before [] b.term (b.entry.type.substConsts σ)
  equations : ∀ q ∈ b.entry.equations,
    ConvClaim.{u,v} before [] (q.lhs.substConsts σ) (q.rhs.substConsts σ) ∧
      FormedClaim.{u,v} before [] (q.lhs.substConsts σ) ∧
      FormedClaim.{u,v} before [] (q.rhs.substConsts σ)
  /-- Facts are arities, or typings the kernel checked with the supplied
  constants substituted. -/
  facts : ∀ fact ∈ b.entry.facts, fact.Arity ∨
    ∃ e T, fact = .typed e T ∧ TypingClaim.{u,v} before [] (e.substConsts σ) (T.substConsts σ)

/-- The old entries outside the block, as an environment. -/
def keepView (block : List (Revalued β)) (before : Environment β) : Environment β := fun r =>
  if Revalued.find block r = none then before r else none

theorem revalue_agrees (block : List (Revalued β)) (before : Environment β)
    (constants : Assignment β V) :
    Assignment.AgreesOn (keepView block before) constants
      (constants.revalue (Revalued.valuation block)) := by
  intro r entry hr levels
  unfold keepView at hr
  split at hr
  · rename_i hn
    simp [Assignment.revalue, Revalued.valuation, hn]
  · cases hr

theorem Revalued.realizes {block : List (Revalued β)} {before : Environment β}
    {constants : Assignment β V} (hE : before.WF) (hM : Realizes constants before)
    (hkeep : ∀ q entry, before q = some entry → Revalued.find block q = none →
      ∀ r ∈ entry.references, Revalued.find block r = none)
    (hclaims : ∀ b ∈ block, Revalued.Claims.{u,v} before (Revalued.valuation block) b) :
    Realizes (constants.revalue (Revalued.valuation block)) (Revalued.environment block before) := by
  let σ := Revalued.valuation block
  have hclosed : ClosedTerms σ := by
    intro r w hw
    simp only [σ, Revalued.valuation, Option.map_eq_some_iff] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    exact ⟨_, (hclaims b (Revalued.find_ref hb).1).closed⟩
  have hwd : WellDenotedTerms constants σ := by
    intro r w hw levels env
    simp only [σ, Revalued.valuation, Option.map_eq_some_iff] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    exact ((hclaims b (Revalued.find_ref hb).1).typed V constants hM levels env
      (Context.valid_nil constants levels env)).1
  have hag := revalue_agrees block before constants
  -- An old entry's parts only mention installed constants outside the block.
  have hin : ∀ q entry, before q = some entry → Revalued.find block q = none →
      keepView block before q = some entry ∧
      ∀ e : AExpr β, (∀ r ∈ e.references, r ∈ entry.references) → e.ReferencesIn before →
        e.ReferencesIn (keepView block before) := by
    intro q entry hq hn
    refine ⟨by simp [keepView, hn, hq], fun e hsub he r hr => ?_⟩
    simp [keepView, hkeep q entry hq hn r (hsub r hr), he r hr]
  -- The value of a supplied constant is its term's denotation.
  have hvalue : ∀ b ∈ block, ∀ q, Revalued.find block q = some b → ∀ levels,
      constants.revalue σ q levels = interp constants levels (fun _ => empty) b.term := by
    intro b _ q hq levels
    simp [Assignment.revalue, σ, Revalued.valuation, hq]
  constructor
  · intro q entry hq levels hn env
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      have hc := hclaims b (Revalued.find_ref hb).1
      rw [wellDenoted_revalue hclosed hwd]
      exact (hc.typed V constants hM levels env (Context.valid_nil constants levels env)).2.1
    · rename_i hb
      obtain ⟨_, hsub⟩ := hin q entry hq hb
      rw [hag.wellDenoted (hsub _ (fun r hr => by simp [ConstantEntry.references, hr])
        (hE.typeReferences q entry hq)) levels env]
      exact hM.typeValid q entry hq levels hn env
  · intro q entry hq levels hn env
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      have hc := hclaims b (Revalued.find_ref hb).1
      rw [hvalue b (Revalued.find_ref hb).1 q hb levels, interp_revalue hclosed,
        interp_closed b.term constants levels hc.closed (fun _ => empty) env]
      exact (hc.typed V constants hM levels env (Context.valid_nil constants levels env)).2.2
    · rename_i hb
      obtain ⟨hk, hsub⟩ := hin q entry hq hb
      rw [hag q entry hk levels, hag.interp (hsub _ (fun r hr => by simp [ConstantEntry.references, hr])
        (hE.typeReferences q entry hq)) levels env]
      exact hM.member q entry hq levels hn env
  · intro q entry hq body hbody levels hn env
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      rw [(hclaims b (Revalued.find_ref hb).1).body] at hbody
      cases hbody
    · rename_i hb
      obtain ⟨_, hsub⟩ := hin q entry hq hb
      rw [hag.wellDenoted (hsub _ (fun r hr => by simp [ConstantEntry.references, hbody, hr])
        (hE.bodyReferences q entry hq body hbody)) levels env]
      exact hM.bodyValid q entry hq body hbody levels hn env
  · intro q entry hq body hbody levels hn env
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      rw [(hclaims b (Revalued.find_ref hb).1).body] at hbody
      cases hbody
    · rename_i hb
      obtain ⟨hk, hsub⟩ := hin q entry hq hb
      rw [hag q entry hk levels, hag.interp (hsub _ (fun r hr => by simp [ConstantEntry.references, hbody, hr])
        (hE.bodyReferences q entry hq body hbody)) levels env]
      exact hM.bodyValue q entry hq body hbody levels hn env
  · intro q entry hq law hl levels hn env
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      have hc := hclaims b (Revalued.find_ref hb).1
      obtain ⟨hconv, hlf, hrf⟩ := hc.equations law hl
      have hΓ := Context.valid_nil constants levels env
      rw [interp_revalue hclosed, interp_revalue hclosed]
      exact hconv V constants hM levels env hΓ (hlf V constants hM levels env hΓ)
        (hrf V constants hM levels env hΓ)
    · rename_i hb
      obtain ⟨_, hsub⟩ := hin q entry hq hb
      have hrefs := hE.equationReferences q entry hq law hl
      rw [hag.interp (hsub _ (fun r hr => by
          simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap]
          exact Or.inl (Or.inr ⟨law, hl, Or.inl hr⟩)) hrefs.1) levels env,
        hag.interp (hsub _ (fun r hr => by
          simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap]
          exact Or.inl (Or.inr ⟨law, hl, Or.inr hr⟩)) hrefs.2) levels env]
      exact hM.equationValue q entry hq law hl levels hn env
  · intro q entry hq fact hf levels hn env
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      rcases (hclaims b (Revalued.find_ref hb).1).facts fact hf with harity | ⟨e, T, rfl, htyped⟩
      · exact harity.meaning _ _ _ _
      · have ht := htyped V constants hM levels env (Context.valid_nil constants levels env)
        simp only [ConstantFact.Meaning]
        rw [wellDenoted_revalue hclosed hwd, wellDenoted_revalue hclosed hwd,
          interp_revalue hclosed, interp_revalue hclosed]
        exact ht
    · rename_i hb
      obtain ⟨hk, _⟩ := hin q entry hq hb
      have hrefs : fact.ReferencesIn (keepView block before) := by
        intro r hr
        have hmem : r ∈ entry.references := by
          simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨fact, hf, hr⟩
        simp [keepView, hkeep q entry hq hb r hmem, hE.factReferences q entry hq fact hf r hr]
      exact hag.factMeaning hk hrefs levels env (hM.factMeaning q entry hq fact hf levels hn env)

/-- A supplied entry is closed and mentions only installed constants. -/
structure Revalued.Formed (after : Environment β) (b : Revalued β) : Prop where
  typeScope : b.entry.type.Scope b.entry.universes 0
  typeReferences : b.entry.type.ReferencesIn after
  body : b.entry.body = none
  equationScope : ∀ q ∈ b.entry.equations,
    q.lhs.Scope b.entry.universes 0 ∧ q.rhs.Scope b.entry.universes 0
  equationReferences : ∀ q ∈ b.entry.equations, q.lhs.ReferencesIn after ∧ q.rhs.ReferencesIn after
  factScope : ∀ fact ∈ b.entry.facts, fact.Scope b.entry.universes
  factReferences : ∀ fact ∈ b.entry.facts, fact.ReferencesIn after

theorem Revalued.wf {block : List (Revalued β)} {before : Environment β} (hE : before.WF)
    (hkeep : ∀ q entry, before q = some entry → Revalued.find block q = none →
      ∀ r ∈ entry.references, Revalued.find block r = none)
    (hformed : ∀ b ∈ block, Revalued.Formed (Revalued.environment block before) b) :
    (Revalued.environment block before).WF := by
  -- An old entry's references are installed, outside the block, so still there.
  have hold : ∀ q entry, before q = some entry → Revalued.find block q = none →
      ∀ r ∈ entry.references, (Revalued.environment block before r).isSome = true := by
    intro q entry hq hn r hr
    have hrn := hkeep q entry hq hn r hr
    simp only [Revalued.environment, hrn]
    -- Every reference of an old entry is installed.
    simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap] at hr
    rcases hr with ((hr | hr) | ⟨law, hl, hr⟩) | ⟨fact, hf, hr⟩
    · exact hE.typeReferences q entry hq r hr
    · cases hb : entry.body with
      | none => simp [hb] at hr
      | some body =>
        simp only [hb, Option.map_some, Option.getD_some] at hr
        exact hE.bodyReferences q entry hq body hb r hr
    · rcases hr with hr | hr
      · exact (hE.equationReferences q entry hq law hl).1 r hr
      · exact (hE.equationReferences q entry hq law hl).2 r hr
    · exact hE.factReferences q entry hq fact hf r hr
  have hcases : ∀ q entry, Revalued.environment block before q = some entry →
      (∃ b ∈ block, b.entry = entry) ∨
        (before q = some entry ∧ Revalued.find block q = none) := by
    intro q entry hq
    unfold Revalued.environment at hq
    split at hq
    · rename_i b hb
      cases hq
      exact Or.inl ⟨b, (Revalued.find_ref hb).1, rfl⟩
    · rename_i hb
      exact Or.inr ⟨hq, hb⟩
  constructor
  · intro q entry hq
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, _⟩
    · exact (hformed b hb).typeScope
    · exact hE.typeScope q entry hq
  · intro q entry hq body hbody
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, _⟩
    · rw [(hformed b hb).body] at hbody; cases hbody
    · exact hE.bodyScope q entry hq body hbody
  · intro q entry hq
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, hn⟩
    · exact (hformed b hb).typeReferences
    · exact fun r hr => hold q entry hq hn r (by simp [ConstantEntry.references, hr])
  · intro q entry hq body hbody
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, hn⟩
    · rw [(hformed b hb).body] at hbody; cases hbody
    · exact fun r hr => hold q entry hq hn r (by simp [ConstantEntry.references, hbody, hr])
  · intro q entry hq law hl
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, _⟩
    · exact (hformed b hb).equationScope law hl
    · exact hE.equationScope q entry hq law hl
  · intro q entry hq law hl
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, hn⟩
    · exact (hformed b hb).equationReferences law hl
    · refine ⟨fun r hr => hold q entry hq hn r ?_, fun r hr => hold q entry hq hn r ?_⟩
      · simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨law, hl, Or.inl hr⟩)
      · simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨law, hl, Or.inr hr⟩)
  · intro q entry hq fact hf
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, _⟩
    · exact (hformed b hb).factScope fact hf
    · exact hE.factScope q entry hq fact hf
  · intro q entry hq fact hf
    rcases hcases q entry hq with ⟨b, hb, rfl⟩ | ⟨hq, hn⟩
    · exact (hformed b hb).factReferences fact hf
    · refine fun r hr => hold q entry hq hn r ?_
      simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨fact, hf, hr⟩

end Ix.Kernel.Model
