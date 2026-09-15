/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Inductive.Recursor
import Ix.Kernel.Verify.Consistency.SynthesisInference

/-!
# Formation facts for singleton shapes

The certified shape conditions are semantic typing facts about telescopes.
Every one of them is derived here from retained closed type checks of the
stored declarations: a retained product check splits into the retained checks
of its binder domains, each in the context of its predecessors. Facts stated
over the family-extended interface transfer to the preceding interface
through a trivial realization of the fresh family entry, because ordinary
fields never mention the family. The generated rule syntax shares its binders
with the stored rule, so its scope and references follow syntactically.
-/

namespace Ix.Kernel.Consistency.Inductive

open Theory Theory.Model Theory.Model.SetTheory Theory.Certified Theory.Certified.Ordinary
  Theory.Inductive

universe u v
variable {β : Type u}

/-! ### Telescope contexts -/

theorem context_append (Γ : Context β) (left right : List (AExpr β)) :
    Telescope.context Γ (left ++ right) = Telescope.context (Telescope.context Γ left) right := by
  induction left generalizing Γ with
  | nil => rfl
  | cons A rest ih => exact ih (Γ.push A)

theorem formed_append_inv {entries : Model.Environment β} :
    ∀ {Γ : Context β} {left right : List (AExpr β)},
      Telescope.Formed.{u,v} entries Γ (left ++ right) →
        Telescope.Formed.{u,v} entries Γ left ∧
          Telescope.Formed.{u,v} entries (Telescope.context Γ left) right
  | _, [], _, h => ⟨.nil, h⟩
  | _, A :: rest, right, h => by
      cases h with
      | cons l hA htail =>
          obtain ⟨hleft, hright⟩ := formed_append_inv htail
          exact ⟨.cons l hA hleft, hright⟩

theorem references_liftN (e : AExpr β) (n k : Nat) : (e.liftN n k).references = e.references := by
  induction e generalizing k <;> simp_all [AExpr.liftN, AExpr.references]

/-- Every context entry refers to the interface. -/
def ContextRefs (entries : Model.Environment β) (Γ : Context β) : Prop :=
  ∀ B ∈ Γ, B.ReferencesIn entries

theorem ContextRefs.nil (entries : Model.Environment β) : ContextRefs entries [] := by
  intro B hB
  simp at hB

theorem ContextRefs.push {entries : Model.Environment β} {Γ : Context β} {A : AExpr β}
    (hΓ : ContextRefs entries Γ) (hA : A.ReferencesIn entries) : ContextRefs entries (Γ.push A) := by
  intro B hB
  simp only [Context.push, List.mem_cons, List.mem_map] at hB
  rcases hB with rfl | ⟨C, hC, rfl⟩
  · intro r hr
    rw [references_liftN] at hr
    exact hA r hr
  · intro r hr
    rw [references_liftN] at hr
    exact hΓ C hC r hr

theorem ContextRefs.context {entries : Model.Environment β} :
    ∀ (domains : List (AExpr β)) {Γ : Context β}, ContextRefs entries Γ →
      (∀ A ∈ domains, A.ReferencesIn entries) → ContextRefs entries (Telescope.context Γ domains)
  | [], _, hΓ, _ => hΓ
  | A :: rest, Γ, hΓ, hd =>
      ContextRefs.context rest (Γ := Γ.push A) (hΓ.push (hd A (List.mem_cons_self ..)))
        (fun B hB => hd B (List.mem_cons_of_mem A hB))

/-! ### Retained checks of product telescopes -/

/-- The retained domain checks of a product telescope, each in the context of
its predecessors. -/
inductive CheckedTelescope (resolve : Address → Option (ConstRef β)) (incoming : Model.Environment β)
    (incomingContext : Context β) (incomingBounds : List VLevel) (entries : Model.Environment β) :
    Context β → List (AExpr β) → Type u
  | nil {Γ : Context β} : CheckedTelescope resolve incoming incomingContext incomingBounds entries Γ []
  | cons {Γ : Context β} {A : AExpr β} {rest : List (AExpr β)}
      (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries A)
      (context : check.context = Γ)
      (tail : CheckedTelescope resolve incoming incomingContext incomingBounds entries (Γ.push A) rest) :
      CheckedTelescope resolve incoming incomingContext incomingBounds entries Γ (A :: rest)

theorem CheckedTelescope.formed {resolve : Address → Option (ConstRef β)} {incoming entries : Model.Environment β}
    {incomingContext : Context β} {incomingBounds : List VLevel}
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ∀ {Γ : Context β} {domains : List (AExpr β)},
      CheckedTelescope resolve incoming incomingContext incomingBounds entries Γ domains →
        Telescope.Formed.{u,v} entries Γ domains
  | _, _, .nil => .nil
  | _, _, .cons check hctx tail =>
      .cons check.level (hctx ▸ check.sound formed) (CheckedTelescope.formed formed tail)

/-- The retained check at one telescope position. -/
theorem CheckedTelescope.get {resolve : Address → Option (ConstRef β)} {incoming entries : Model.Environment β}
    {incomingContext : Context β} {incomingBounds : List VLevel} :
    ∀ {Γ : Context β} {domains : List (AExpr β)},
      CheckedTelescope resolve incoming incomingContext incomingBounds entries Γ domains →
      ∀ (j : Nat) (A : AExpr β), domains[j]? = some A →
        ∃ check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries A,
          check.context = Telescope.context Γ (domains.take j)
  | _, _, .nil, j, A, h => by simp at h
  | _, _, .cons check hctx tail, 0, A, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨check, hctx⟩
  | _, _, .cons check hctx tail, j + 1, A, h => by
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨found, hfound⟩ := tail.get j A h
      exact ⟨found, hfound⟩

/-- Split a retained check of a product into the retained checks of its
domains and the retained check of its body. -/
def telescopeChecks {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Context β} {incomingBounds : List VLevel}
    {p : PropWhen} :
    ∀ (domains : List (AExpr β)) {B : AExpr β}
      (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries
        (AExpr.forallN p domains B)),
      CheckedTelescope resolve incoming incomingContext incomingBounds entries check.context domains ×
        { body : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries B //
          body.context = Telescope.context check.context domains }
  | [], _, check => (.nil, ⟨check, rfl⟩)
  | A :: rest, B, check =>
      let view := check.check.forallView (condition := p) (domain := A)
        (body := AExpr.forallN p rest B) rfl
      let domainCheck : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries A :=
        ⟨check.context, view.domainLevel, view.domainCheck⟩
      let bodyCheck : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries
          (AExpr.forallN p rest B) :=
        ⟨check.context.push A, view.bodyLevel, view.bodyCheck⟩
      let inner := telescopeChecks rest bodyCheck
      (.cons domainCheck rfl inner.1, ⟨inner.2.val, inner.2.property⟩)

/-- Transport a retained check along an equation between its terms. -/
def retypeCheck {resolve : Address → Option (ConstRef β)} {incoming entries : Model.Environment β}
    {incomingContext : Context β} {incomingBounds : List VLevel} {t t' : AExpr β} (h : t = t')
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries t) :
    SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries t' := h ▸ check

theorem retypeCheck_context {resolve : Address → Option (ConstRef β)} {incoming entries : Model.Environment β}
    {incomingContext : Context β} {incomingBounds : List VLevel} {t t' : AExpr β} (h : t = t')
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries t) :
    (retypeCheck h check).context = check.context := by
  subst h
  rfl

/-- A retained closed check viewed in the empty context. -/
def closedScoped {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {type : AExpr β} {level : VLevel} (check : SynthesisTypeCheck resolve entries type level) :
    SynthesisScopedTypeCheck resolve entries [] [] entries type :=
  check.scoped

/-! ### Transfer from the family-extended interface -/

/-- A fresh entry realizable in every model of the interface. -/
def FreshRealizable [DecidableEq β] (entries : Model.Environment β) (r : ConstRef β) (entry : ConstantEntry β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∃ value : List Nat → V, EntryRealization (constants.insert r value) r entry

theorem typing_of_insert [DecidableEq β] {entries : Model.Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} {Γ : Context β} {e A : AExpr β}
    (hE : entries.WF) (fresh : entries r = none) (realizable : FreshRealizable.{u,v} entries r entry)
    (claim : TypingClaim.{u,v} (entries.insert r entry) Γ e A)
    (hΓ : ContextRefs entries Γ) (he : e.ReferencesIn entries) (hA : A.ReferencesIn entries) :
    TypingClaim.{u,v} entries Γ e A := by
  intro V _ constants hM levels env hvalid
  obtain ⟨value, realization⟩ := realizable V constants hM
  have agrees := Assignment.insert_agrees fresh constants value
  have hM' : Realizes (constants.insert r value) (entries.insert r entry) :=
    (hM.of_agrees hE agrees).insert realization
  have hvalid' : Γ.Valid (constants.insert r value) levels env := by
    intro i B hB
    have hBr := hΓ B (List.mem_of_getElem? hB)
    obtain ⟨hw, hm⟩ := hvalid i B hB
    refine ⟨(agrees.wellDenoted hBr levels env).mpr hw, ?_⟩
    rw [agrees.interp hBr]
    exact hm
  obtain ⟨hew, hAw, hem⟩ := claim V (constants.insert r value) hM' levels env hvalid'
  refine ⟨(agrees.wellDenoted he levels env).mp hew, (agrees.wellDenoted hA levels env).mp hAw, ?_⟩
  rwa [agrees.interp he levels env, agrees.interp hA levels env] at hem

theorem formed_of_insert [DecidableEq β] {entries : Model.Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} (hE : entries.WF) (fresh : entries r = none)
    (realizable : FreshRealizable.{u,v} entries r entry) :
    ∀ {Γ : Context β} {domains : List (AExpr β)},
      Telescope.Formed.{u,v} (entries.insert r entry) Γ domains → ContextRefs entries Γ →
      (∀ A ∈ domains, A.ReferencesIn entries) → Telescope.Formed.{u,v} entries Γ domains
  | _, [], _, _, _ => .nil
  | _, A :: rest, h, hΓ, hd => by
      cases h with
      | cons l hA htail =>
          have hAr := hd A (List.mem_cons_self ..)
          refine .cons l (typing_of_insert hE fresh realizable hA hΓ hAr ?_)
            (formed_of_insert hE fresh realizable htail (hΓ.push hAr)
              (fun B hB => hd B (List.mem_cons_of_mem A hB)))
          intro q hq
          simp [AExpr.references] at hq

/-- The fresh family entry is realized by the constantly empty family. -/
theorem family_realizable [DecidableEq β] {entries : Model.Environment β} {shape : Shape β} {source : β}
    (hs : shape.indices = []) (hscope : shape.type.Scope shape.universes 0)
    (hrefs : shape.type.ReferencesIn entries) (fresh : entries (.member source 0) = none)
    (formed : Telescope.Formed.{u,v} entries [] shape.parameters) :
    FreshRealizable.{u,v} entries (.member source 0) shape.familyEntry := by
  intro V _ constants hM
  have formedAll : Telescope.Formed.{u,v} entries [] (shape.parameters ++ shape.indices) :=
    formed.append (by rw [hs]; exact .nil)
  obtain ⟨l, _, htype⟩ := formedAll.forallN (TypingClaim.sort shape.level)
  have htype' : TypingClaim.{u,v} entries [] shape.type (.sort l) := htype
  let value : List Nat → V := fun levels =>
    Telescope.curry 1 (Telescope.interpret constants levels (fun _ => empty)
      (shape.parameters ++ shape.indices)) (fun _ => empty)
  have agrees := Assignment.insert_agrees fresh constants value
  refine ⟨value, ?_⟩
  constructor
  · intro levels _ env
    exact (agrees.wellDenoted hrefs levels env).mpr
      (htype' V constants hM levels env (Context.valid_nil constants levels env)).1
  · intro levels _ env
    rw [Assignment.insert_same]
    change value levels ∈ˢ interp (constants.insert (.member source 0) value) levels env shape.type
    rw [agrees.interp hrefs levels env, interp_closed shape.type constants levels hscope env (fun _ => empty)]
    simp only [Shape.type, AExpr.interp_forallN, regime_never, interp, value]
    apply Telescope.curry_mem
    intro xs _
    exact empty_mem_univ _
  · intro body hb
    cases hb
  · intro body hb
    cases hb
  · intro law hl
    simp [Shape.familyEntry] at hl
  · intro fact hf
    simp [Shape.familyEntry] at hf

/-! ### Scope and references of generated syntax -/

/-- Binder domains scoped in sequence, each one level deeper. -/
def BindersScope (p : PropWhen) (universes : Nat) : Nat → List (AExpr β) → Prop
  | _, [] => True
  | depth, A :: rest => p.WF universes ∧ A.Scope universes depth ∧ BindersScope p universes (depth + 1) rest

theorem scope_lamN_iff {p : PropWhen} {universes : Nat} :
    ∀ {domains : List (AExpr β)} {body : AExpr β} {depth : Nat},
      (AExpr.lamN p domains body).Scope universes depth ↔
        BindersScope p universes depth domains ∧ body.Scope universes (depth + domains.length)
  | [], body, depth => by simp [AExpr.lamN, BindersScope]
  | A :: rest, body, depth => by
      simp only [AExpr.lamN, AExpr.Scope, BindersScope, List.length_cons]
      rw [scope_lamN_iff (domains := rest)]
      have : depth + 1 + rest.length = depth + (rest.length + 1) := by omega
      rw [this]
      constructor
      · rintro ⟨hp, hA, hrest, hbody⟩
        exact ⟨⟨hp, hA, hrest⟩, hbody⟩
      · rintro ⟨⟨hp, hA, hrest⟩, hbody⟩
        exact ⟨hp, hA, hrest, hbody⟩

theorem scope_forallN_iff {p : PropWhen} {universes : Nat} :
    ∀ {domains : List (AExpr β)} {body : AExpr β} {depth : Nat},
      (AExpr.forallN p domains body).Scope universes depth ↔
        BindersScope p universes depth domains ∧ body.Scope universes (depth + domains.length)
  | [], body, depth => by simp [AExpr.forallN, BindersScope]
  | A :: rest, body, depth => by
      simp only [AExpr.forallN, AExpr.Scope, BindersScope, List.length_cons]
      rw [scope_forallN_iff (domains := rest)]
      have : depth + 1 + rest.length = depth + (rest.length + 1) := by omega
      rw [this]
      constructor
      · rintro ⟨hp, hA, hrest, hbody⟩
        exact ⟨⟨hp, hA, hrest⟩, hbody⟩
      · rintro ⟨⟨hp, hA, hrest⟩, hbody⟩
        exact ⟨hp, hA, hrest, hbody⟩

theorem scope_appN_iff {universes depth : Nat} :
    ∀ {args : List (AExpr β)} {f : AExpr β},
      (AExpr.appN f args).Scope universes depth ↔
        f.Scope universes depth ∧ ∀ a ∈ args, a.Scope universes depth
  | [], f => by simp [AExpr.appN]
  | a :: args, f => by
      simp only [AExpr.appN, List.mem_cons, forall_eq_or_imp]
      rw [scope_appN_iff (args := args)]
      simp only [AExpr.Scope]
      constructor
      · rintro ⟨⟨hf, ha⟩, hargs⟩
        exact ⟨hf, ha, hargs⟩
      · rintro ⟨hf, ha, hargs⟩
        exact ⟨⟨hf, ha⟩, hargs⟩

theorem parameterVars_scope {universes depth offset : Nat} :
    ∀ {count : Nat}, offset + count ≤ depth →
      ∀ v ∈ (parameterVars offset count : List (AExpr β)), v.Scope universes depth
  | 0, _ => by simp [parameterVars]
  | count + 1, h => by
      intro v hv
      simp only [parameterVars, List.mem_cons] at hv
      rcases hv with rfl | hv
      · show offset + count < depth
        omega
      · exact parameterVars_scope (by omega) v hv

theorem referencesIn_lamN_iff {entries : Model.Environment β} {p : PropWhen} :
    ∀ {domains : List (AExpr β)} {body : AExpr β},
      (AExpr.lamN p domains body).ReferencesIn entries ↔
        (∀ A ∈ domains, A.ReferencesIn entries) ∧ body.ReferencesIn entries
  | [], body => by simp [AExpr.lamN]
  | A :: rest, body => by
      simp only [AExpr.lamN, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h
        have hA : A.ReferencesIn entries := fun r hr => h r (List.mem_append_left _ hr)
        have ht : (AExpr.lamN p rest body).ReferencesIn entries :=
          fun r hr => h r (List.mem_append_right _ hr)
        obtain ⟨hrest, hbody⟩ := referencesIn_lamN_iff.mp ht
        exact ⟨⟨hA, hrest⟩, hbody⟩
      · rintro ⟨⟨hA, hrest⟩, hbody⟩
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hA r hr
        · exact (referencesIn_lamN_iff.mpr ⟨hrest, hbody⟩) r hr

theorem referencesIn_appN_iff {entries : Model.Environment β} :
    ∀ {args : List (AExpr β)} {f : AExpr β},
      (AExpr.appN f args).ReferencesIn entries ↔
        f.ReferencesIn entries ∧ ∀ a ∈ args, a.ReferencesIn entries
  | [], f => by simp [AExpr.appN]
  | a :: args, f => by
      simp only [AExpr.appN, List.mem_cons, forall_eq_or_imp]
      rw [referencesIn_appN_iff (args := args)]
      constructor
      · rintro ⟨hfa, hargs⟩
        exact ⟨fun r hr => hfa r (List.mem_append_left _ hr),
          fun r hr => hfa r (List.mem_append_right _ hr), hargs⟩
      · rintro ⟨hf, ha, hargs⟩
        refine ⟨?_, hargs⟩
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hf r hr
        · exact ha r hr

theorem parameterVars_referencesIn {entries : Model.Environment β} {offset : Nat} :
    ∀ {count : Nat}, ∀ v ∈ (parameterVars offset count : List (AExpr β)), v.ReferencesIn entries
  | 0 => by simp [parameterVars]
  | count + 1 => by
      intro v hv
      simp only [parameterVars, List.mem_cons] at hv
      rcases hv with rfl | hv
      · intro r hr
        simp [AExpr.references] at hr
      · exact parameterVars_referencesIn v hv

theorem referencesIn_insert_inv [DecidableEq β] {entries : Model.Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} {e : AExpr β} (h : e.ReferencesIn (entries.insert r entry))
    (absent : r ∉ e.references) : e.ReferencesIn entries := by
  intro q hq
  have hne : q ≠ r := fun heq => absent (heq ▸ hq)
  have := h q hq
  simpa [Environment.insert, hne] using this

theorem length_independent : ∀ (l : List (AExpr β)) (offset : Nat),
    (Telescope.independent l offset).length = l.length
  | [], _ => rfl
  | _ :: rest, offset => by simp [Telescope.independent, length_independent rest]

theorem length_lift : ∀ (l : List (AExpr β)) (count cutoff : Nat),
    (Telescope.lift count l cutoff).length = l.length
  | [], _, _ => rfl
  | _ :: rest, count, cutoff => by simp [Telescope.lift, length_lift rest]

theorem length_recursiveTypes (ctor : Constructor β) (shape : Shape β) (source : β) :
    (ctor.recursiveTypes shape source).length = ctor.recursive.length := by
  simp [Constructor.recursiveTypes, Ordinary.recursiveTypesFrom]

theorem length_minorTypesSyntax (shape : Shape β) (source : β) (mode : ElimMode) :
    (shape.minorTypesSyntax source mode).length = shape.constructors.length := by
  simp [Shape.minorTypesSyntax, length_independent]

theorem length_ruleBinders (shape : Shape β) (source : β) (mode : ElimMode) (ctor : Constructor β) :
    (shape.ruleBinders source mode ctor).length =
      shape.parameters.length + 1 + shape.constructors.length +
        (ctor.fields.length + ctor.recursive.length) := by
  simp only [Shape.ruleBinders, List.length_append, List.length_map, List.length_singleton,
    length_minorTypesSyntax, length_lift, length_recursiveTypes]

theorem motiveLevel_wf (mode : ElimMode) (universes : Nat) :
    mode.motiveLevel.WF (mode.recUvars universes) := by
  cases mode <;> simp [ElimMode.motiveLevel, ElimMode.recUvars, ElimMode.offset, VLevel.WF]

/-- The generated left-hand side of a rule is scoped whenever the stored
right-hand side is: both bind the same telescope, and the left body applies
the recursor and the constructor to bound variables only. -/
theorem ruleLhs_scope {shape : Shape β} {source recursor : β} {mode : ElimMode} {i : Nat}
    {ctor : Constructor β} (hc : ctor.indices = [])
    (hrhs : (shape.ruleRhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0) :
    (shape.ruleLhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0 := by
  unfold Shape.ruleRhs at hrhs
  unfold Shape.ruleLhs
  obtain ⟨hbinders, _⟩ := scope_lamN_iff.mp hrhs
  refine scope_lamN_iff.mpr ⟨hbinders, ?_⟩
  rw [length_ruleBinders]
  unfold Shape.ruleLhsBody
  refine scope_appN_iff.mpr ⟨?_, ?_⟩
  · intro l hl
    exact VLevel.params_wf hl
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact parameterVars_scope (by omega) a ha
    · simp [Shape.ruleIndices, hc] at ha
    · unfold Shape.ruleConstructor
      refine scope_appN_iff.mpr ⟨?_, ?_⟩
      · intro l hl
        exact mode.sourceLevels_wf shape.universes l hl
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact parameterVars_scope (by omega) v hv
        · exact parameterVars_scope (by omega) v hv

/-- The generated left-hand side refers to the recursor, the constructor,
and the binders of the stored right-hand side. -/
theorem ruleLhs_referencesIn [DecidableEq β] {entries : Model.Environment β} {shape : Shape β}
    {source recursor : β} {mode : ElimMode} {i : Nat} {ctor : Constructor β}
    (hc : ctor.indices = []) (hi : shape.constructors[i]? = some ctor)
    (hrhs : (shape.ruleRhs source recursor mode i ctor).ReferencesIn
      (shape.recursorEnvironment entries source recursor mode)) :
    (shape.ruleLhs source recursor mode i ctor).ReferencesIn
      (shape.recursorEnvironment entries source recursor mode) := by
  unfold Shape.ruleRhs at hrhs
  unfold Shape.ruleLhs
  obtain ⟨hbinders, _⟩ := referencesIn_lamN_iff.mp hrhs
  refine referencesIn_lamN_iff.mpr ⟨hbinders, ?_⟩
  unfold Shape.ruleLhsBody
  refine referencesIn_appN_iff.mpr ⟨?_, ?_⟩
  · intro r hr
    simp only [AExpr.references, List.mem_singleton] at hr
    subst hr
    simp [Shape.recursorEnvironment, Environment.insert]
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact parameterVars_referencesIn a ha
    · simp [Shape.ruleIndices, hc] at ha
    · unfold Shape.ruleConstructor
      refine referencesIn_appN_iff.mpr ⟨?_, ?_⟩
      · intro r hr
        simp only [AExpr.references, List.mem_singleton] at hr
        subst hr
        simp [Shape.recursorEnvironment, Environment.insert, Shape.constructorEnvironment,
          Environment.overlay, Shape.constructorEntries, hi]
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact parameterVars_referencesIn v hv
        · exact parameterVars_referencesIn v hv

end Ix.Kernel.Consistency.Inductive
