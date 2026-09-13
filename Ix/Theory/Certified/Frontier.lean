/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Source

/-! Conditional interfaces contain formed, source-bound headers. They carry
no assumed bodies, equations or primitive facts, and no claim that a model
exists. Object axioms and quotient primitives must use their semantic
producers; they cannot be deferred and later erased by frontier subtraction. -/

namespace Ix.Theory.Certified

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

def deferredSource (store : Store β) (ref : ConstRef β) : Bool :=
  match store.lookup ref with
  | some (.defn _ _ _ _ .safe) | some (.induct _ _ _ _ _ .safe) |
      some (.recursor _ _ _ _ _ _ _ _ .safe) => true
  | some _ => false
  | none => match store.lookupCtor ref with
    | some ctor => ctor.safety == .safe
    | none => false

structure FrontierWitness (β : Type u) where
  ref : ConstRef β
  annotations : AnnotationTree
  level : VLevel
  typing : TypingWitness β

structure FrontierHeader (store : Store β) where
  header : Signature.Header β
  source : SourceHeader store header.ref header.entry
  allowed : deferredSource store header.ref = true

def readFrontierHeader? (store : Store β) (witness : FrontierWitness β) :
    Option (FrontierHeader store) :=
  if ha : deferredSource store witness.ref = true then
    match ht : store.type witness.ref with
    | none => none
    | some type => match hn : store.uvars witness.ref with
      | none => none
      | some universes => do
        let reading ← readAnnotations? universes 0 type witness.annotations
        return {
          header := ⟨witness.ref, universes, reading.val⟩
          source := ⟨ht.trans (congrArg some reading.property.1.symm), hn⟩
          allowed := ha
        }
  else none

omit [DecidableEq β] in
theorem readFrontierHeader?_ref {store : Store β} {witness : FrontierWitness β}
    {reading : FrontierHeader store} (h : readFrontierHeader? store witness = some reading) :
    reading.header.ref = witness.ref := by
  unfold readFrontierHeader? at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨value, _, h⟩ := h
        cases Option.some.inj h
        rfl
  · cases h

omit [DecidableEq β] in
theorem mapM_projection {α : Type _} {γ : Type _} {δ : Type _}
    (f : α → Option γ) (project : γ → δ) (source : α → δ)
    (step : ∀ a b, f a = some b → project b = source a)
    {inputs : List α} {outputs : List γ} (h : inputs.mapM f = some outputs) :
    outputs.map project = inputs.map source := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst outputs; rfl
  | cons a rest ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    simp only [List.map_cons, step a b hb, ih hbs]

structure CheckedFrontier (signature : PrimitiveSignature β) (store : Store β) where
  readings : List (FrontierHeader store)
  validated : signature.validate store = true
  formed : Signature.Formed.{u,v} signature.environment (readings.map (·.header))

def CheckedFrontier.headers {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) : List (Signature.Header β) :=
  frontier.readings.map (·.header)

def CheckedFrontier.refs {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) : List (ConstRef β) :=
  frontier.headers.map (·.ref)

def CheckedFrontier.interface {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) : CheckedInterface signature where
  entries := Signature.environment signature.environment frontier.headers
  wf := frontier.formed.wf signature.environment_wf
  present := ⟨frontier.formed.old signature.environment_false,
    frontier.formed.old signature.environment_falseElim⟩

def checkFrontier? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (witnesses : List (FrontierWitness β)) : Option (CheckedFrontier.{u,v} signature store) := do
  if hv : signature.validate store = true then
    if witnesses.length > fuel then none else do
      let readings ← witnesses.mapM (readFrontierHeader? store)
      let checked ← Signature.checkTypes.{u,v} fuel signature.environment
        (readings.map (·.header)) (witnesses.map fun witness => ⟨witness.level, witness.typing⟩)
      return ⟨readings, hv, checked.down⟩
  else none

theorem checkFrontier?_refs {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {witnesses : List (FrontierWitness β)} {result : CheckedFrontier.{u,v} signature store}
    (h : checkFrontier? fuel signature store witnesses = some result) :
    result.refs = witnesses.map (·.ref) := by
  unfold checkFrontier? at h
  split at h
  · split at h
    · cases h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨readings, hr, formed, _, h⟩ := h
      cases Option.some.inj h
      simpa only [CheckedFrontier.refs, CheckedFrontier.headers, List.map_map, Function.comp_def] using
        mapM_projection (readFrontierHeader? store) (fun r => r.header.ref) (·.ref)
          (fun _ _ h => readFrontierHeader?_ref h) hr
  · cases h

theorem CheckedFrontier.header_source {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) {header : Signature.Header β}
    (h : header ∈ frontier.headers) : SourceHeader store header.ref header.entry := by
  obtain ⟨reading, _, rfl⟩ := List.mem_map.mp h
  exact reading.source

/-- A provider may contain additional checked bodies and laws. Its entire
annotated type and universe arity must match the deferred header exactly. -/
def HeaderPresent (entries : Environment β) (header : Signature.Header β) : Prop :=
  match entries header.ref with
  | none => False
  | some entry => entry.universes = header.universes ∧ entry.type = header.type

instance (entries : Environment β) (header : Signature.Header β) :
    Decidable (HeaderPresent entries header) := by
  unfold HeaderPresent
  split <;> infer_instance

omit [DecidableEq β] in
theorem HeaderPresent.entry {entries : Environment β} {header : Signature.Header β}
    (h : HeaderPresent entries header) :
    ∃ entry, entries header.ref = some entry ∧
      entry.universes = header.universes ∧ entry.type = header.type := by
  unfold HeaderPresent at h
  cases he : entries header.ref with
  | none => simp [he] at h
  | some entry => exact ⟨entry, rfl, by simpa only [he] using h⟩

/-- The compatible interpretation of every provider gives one interpretation
of the complete deferred view, including shared references and primitive pins. -/
theorem CheckedFrontier.compatible {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) (provider : CheckedInterface signature)
    (headers : ∀ header ∈ frontier.headers, HeaderPresent provider.entries header)
    (V : Type v) [SetTheory V] (constants : Assignment β V)
    (hM : signature.Compatible provider.entries constants) :
    signature.Compatible frontier.interface.entries constants := by
  have old : ∀ r entry, signature.environment r = some entry →
      provider.entries r = some entry := by
    intro r entry he
    unfold PrimitiveSignature.environment at he
    split at he
    · subst r; cases Option.some.inj he; exact provider.present.1
    · split at he
      · subst r; cases Option.some.inj he; exact provider.present.2
      · cases he
  have he : ∀ r entry, frontier.interface.entries r = some entry →
      ∃ actual, provider.entries r = some actual ∧
        actual.universes = entry.universes ∧ actual.type = entry.type ∧
        entry.body = none ∧ entry.equations = [] ∧ entry.facts = [] := by
    intro r entry hr
    rcases Signature.environment_source hr with hbase | ⟨header, hh, rfl, rfl⟩
    · refine ⟨entry, old r entry hbase, rfl, rfl, ?_⟩
      unfold PrimitiveSignature.environment at hbase
      split at hbase
      · cases Option.some.inj hbase; exact ⟨rfl, rfl, rfl⟩
      · split at hbase
        · cases Option.some.inj hbase; exact ⟨rfl, rfl, rfl⟩
        · cases hbase
    · obtain ⟨actual, ha, hu, ht⟩ := (headers header hh).entry
      exact ⟨actual, ha, hu, ht, rfl, rfl, rfl⟩
  refine ⟨?_, hM.falseValue, hM.falseElimValue⟩
  constructor
  · intro r entry hr levels hn env
    obtain ⟨actual, ha, hu, ht, _⟩ := he r entry hr
    rw [← ht]
    exact hM.realizes.typeValid r actual ha levels (hn.trans hu.symm) env
  · intro r entry hr levels hn env
    obtain ⟨actual, ha, hu, ht, _⟩ := he r entry hr
    rw [← ht]
    exact hM.realizes.member r actual ha levels (hn.trans hu.symm) env
  · intro r entry hr body hb
    rw [(he r entry hr).choose_spec.2.2.2.1] at hb
    cases hb
  · intro r entry hr body hb
    rw [(he r entry hr).choose_spec.2.2.2.1] at hb
    cases hb
  · intro r entry hr law hl
    rw [(he r entry hr).choose_spec.2.2.2.2.1] at hl
    cases hl
  · intro r entry hr fact hf
    rw [(he r entry hr).choose_spec.2.2.2.2.2] at hf
    cases hf

structure ConditionalStore (signature : PrimitiveSignature β) (store : Store β)
    (subjects : List (ConstRef β)) where
  frontier : CheckedFrontier.{u,v} signature store
  checked : CheckedExtension.{u,v} signature store frontier.interface
  fresh : ∀ r ∈ subjects, frontier.interface.entries r = none
  present : ∀ r ∈ subjects, (checked.result.entries r).isSome = true

def checkConditionalStore? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (frontier : List (FrontierWitness β)) (subjects : List (ConstRef β))
    (witness : List (DeclarationWitness β)) : Option (ConditionalStore.{u,v} signature store subjects) := do
  let dependencies ← checkFrontier?.{u,v} fuel signature store frontier
  if fresh : subjects.all (fun r => (dependencies.interface.entries r).isNone) = true then
    let checked ← checkDeclarationExtensions?.{u,v} fuel (store := store) dependencies.interface witness
    if present : subjects.all (fun r => (checked.result.entries r).isSome) = true then
      return ⟨dependencies, checked, fun r hr => Option.isNone_iff_eq_none.mp
        (List.all_eq_true.mp fresh r hr), List.all_eq_true.mp present⟩
    else none
  else none

theorem checkConditionalStore?_frontier {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {frontier : List (FrontierWitness β)} {subjects : List (ConstRef β)}
    {witness : List (DeclarationWitness β)} {result : ConditionalStore.{u,v} signature store subjects}
    (h : checkConditionalStore? fuel signature store frontier subjects witness = some result) :
    checkFrontier? fuel signature store frontier = some result.frontier := by
  unfold checkConditionalStore? at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨dependencies, hd, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨checked, _, h⟩ := h
    split at h
    · cases Option.some.inj h; exact hd
    · cases h
  · cases h

/-- No realization of the frontier is fabricated. Every realization supplied
by checked dependencies extends compatibly to all the exact subject types. -/
theorem ConditionalStore.subject_sound {signature : PrimitiveSignature β} {store : Store β}
    {subjects : List (ConstRef β)} (receipt : ConditionalStore.{u,v} signature store subjects)
    (V : Type v) [SetTheory V] (constants : Assignment β V)
    (hM : signature.Compatible receipt.frontier.interface.entries constants) :
    ∃ constants' : Assignment β V,
      signature.Compatible receipt.checked.result.entries constants' ∧
      Assignment.AgreesOn receipt.frontier.interface.entries constants constants' ∧
      ∀ ref ∈ subjects, ∃ entry, receipt.checked.result.entries ref = some entry ∧
        EntrySource signature store ref entry ∧ SourceHeader store ref entry ∧
        ∀ levels, levels.length = entry.universes → ∀ env,
          WellDenoted constants' levels env entry.type ∧
          constants' ref levels ∈ˢ interp constants' levels env entry.type := by
  obtain ⟨constants', hM', ha⟩ := receipt.checked.extension.models V constants hM
  refine ⟨constants', hM', ha, ?_⟩
  intro ref hr
  have hp := receipt.present ref hr
  cases he : receipt.checked.result.entries ref with
  | none => simp [he] at hp
  | some entry =>
    have hs : EntrySource signature store ref entry := by
      rcases receipt.checked.source ref entry he with old | new
      · rw [receipt.fresh ref hr] at old; cases old
      · exact new
    refine ⟨entry, rfl, hs, hs.header, ?_⟩
    intro levels hl env
    exact ⟨hM'.realizes.typeValid ref entry he levels hl env,
      hM'.realizes.member ref entry he levels hl env⟩

end Ix.Theory.Certified
