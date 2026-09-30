/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Environment
import Ix.Kernel.Model.Extension
import Std.Data.TreeMap.Lemmas

/-! # The checked environment and its models

`Env β` is the environment the kernel builds: installed entries in
installation order, keyed by `ConstRef β`. The semantic model reads it through
`Env.toEnvironment`, the `Model.Environment β` view (a partial function from
references to entries). `β` is the reference type; the public API fixes it to
`Address`, where an address is an opaque key: the kernel never hashes content.

Lookups go through an index: entries are bucketed by a 64-bit hash of their
reference in a persistent ordered map, newest first within a bucket, and a
lookup scans only its bucket. The hash of a block key is fixed when the
environment is created (`emptyWith`). It selects a bucket and nothing else:
`toEnvironment_push` and `toEnvironment_pushList` characterize lookups without
it, so no statement depends on the hash or on its collisions. `Env.empty` puts
every entry in one bucket, the generic reference behaviour; the addressed entry
point `checkAddressed` (`checkIndexed`) hashes addresses by their leading bytes.

Installation order is the host-supplied dependency order. The checker rejects
a reference to an entry that is not yet installed and rejects a duplicate
reference, so acceptance needs neither an acyclicity proof nor a collision
assumption about addresses.

A `Model V env` is an assignment realizing every installed entry together
with the syntactic well-formedness of the environment (`Environment.WF`),
which the checker's decidable scope and reference checks establish and the
model extension of a definition consumes. -/

namespace Ix.Kernel

open Model Model.SetTheory

universe u v

/-- The checked environment: entries in installation order, newest first, and
their index. -/
structure Env (β : Type u) where
  entries : List (ConstRef β × Model.ConstantEntry β)
  /-- Hash of a block key; it only selects an index bucket. -/
  keyHash : β → UInt64
  /-- Installed entries by `refHash keyHash` of their reference, newest first
  within a bucket. -/
  index : Std.TreeMap UInt64 (List (ConstRef β × Model.ConstantEntry β)) compare
  /-- References whose installed bodies conversion does not unfold (theorems
  and opaques), bucketed like `index`. Lookups never read it. -/
  noUnfold : Std.TreeMap UInt64 (List (ConstRef β)) compare := ∅
  /-- The numeric operations certified so far (`ConstantFact.natOp`), newest
  first. Lookups never read it; the equations of a new operation name a
  certified one found here, and its fact is checked again at use. -/
  natOps : List (Model.NatOp × ConstRef β) := []

namespace Env

variable {β : Type u} [DecidableEq β]

/-- The bucket hash of a reference. -/
def refHash (keyHash : β → UInt64) : ConstRef β → UInt64
  | .member b i => mixHash (keyHash b) (hash i)
  | .ctor b i c => mixHash (mixHash (keyHash b) (hash i)) (hash (c + 1))

/-- The empty environment with the given key hash. -/
def emptyWith (keyHash : β → UInt64) : Env β := ⟨[], keyHash, ∅, ∅, []⟩

/-- The empty environment, the starting point of the closed check: one bucket. -/
def empty : Env β := emptyWith fun _ => 0

/-- The index bucket a reference belongs to. -/
def bucket (env : Env β) (r : ConstRef β) : List (ConstRef β × Model.ConstantEntry β) :=
  env.index.getD (refHash env.keyHash r) []

/-- Look up an installed entry. Installation rejects duplicate references, so
the first match is the only match. -/
def lookup (env : Env β) (r : ConstRef β) : Option (Model.ConstantEntry β) :=
  ((env.bucket r).find? fun e => e.1 == r).map (·.2)

/-- The first installed reference satisfying `valid`. Used to find an admitted
eliminator by its checked interface: Ixon stores a recursor as its own record,
so its reference is found rather than assumed to follow its family. -/
def findRef (env : Env β) (valid : ConstRef β → Bool) : Option (ConstRef β) :=
  (env.entries.find? fun e => valid e.1).map (·.1)

/-- The semantic view of the environment read by the model. -/
def toEnvironment (env : Env β) : Model.Environment β := env.lookup

/-- Install an entry. -/
def push (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) : Env β :=
  let h := refHash env.keyHash r
  { env with
    entries := (r, entry) :: env.entries
    index := env.index.insert h ((r, entry) :: env.index.getD h []) }

@[simp] theorem lookup_emptyWith (keyHash : β → UInt64) (r : ConstRef β) :
    (emptyWith keyHash).lookup r = none := by
  simp [lookup, bucket, emptyWith, Std.TreeMap.getD_emptyc]

@[simp] theorem toEnvironment_emptyWith (keyHash : β → UInt64) (r : ConstRef β) :
    (emptyWith keyHash).toEnvironment r = none := lookup_emptyWith keyHash r

@[simp] theorem lookup_empty (r : ConstRef β) : (empty : Env β).lookup r = none :=
  lookup_emptyWith _ r

@[simp] theorem toEnvironment_empty (r : ConstRef β) :
    (empty : Env β).toEnvironment r = none := lookup_empty r

theorem lookup_push (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β)
    (q : ConstRef β) :
    (env.push r entry).lookup q = if q = r then some entry else env.lookup q := by
  simp only [lookup, bucket, push, Std.TreeMap.getD_insert]
  by_cases hq : q = r
  · subst hq; simp
  · have hne : (r == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
    rw [ite_eq_right hq]
    split
    · rename_i hh
      have hh : refHash env.keyHash r = refHash env.keyHash q := Std.LawfulEqCmp.eq_of_compare hh
      simp [hne, hh]
    · rfl

theorem toEnvironment_push (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) :
    (env.push r entry).toEnvironment = env.toEnvironment.insert r entry := by
  funext q
  simp only [toEnvironment, lookup_push, Environment.insert]

/-! ### Bodies that conversion does not unfold

A theorem's or an opaque's body is installed, so the reading of the supplied
declaration is exact (`Block.Installed`), but conversion does not unfold it,
as in the official kernel and con-leche. `reductionView` is the environment
with those bodies hidden; it only drops bodies, so every realization of the
environment realizes it (`realizes_reductionView`), and claims established
against it hold against the environment (`TypingClaim.ofReductionView`). -/

/-- Install an entry whose body conversion does not unfold. -/
def pushOpaque (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) : Env β :=
  let pushed := env.push r entry
  let h := refHash env.keyHash r
  { pushed with noUnfold := env.noUnfold.insert h (r :: env.noUnfold.getD h []) }

theorem toEnvironment_pushOpaque (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) :
    (env.pushOpaque r entry).toEnvironment = (env.push r entry).toEnvironment := rfl

/-- Install an entry, hiding its body from conversion when `hidden`. -/
def pushWith (hidden : Bool) (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) : Env β :=
  if hidden then env.pushOpaque r entry else env.push r entry

theorem toEnvironment_pushWith (hidden : Bool) (env : Env β) (r : ConstRef β)
    (entry : Model.ConstantEntry β) :
    (env.pushWith hidden r entry).toEnvironment = (env.push r entry).toEnvironment := by
  cases hidden <;> rfl

omit [DecidableEq β] in
theorem entries_pushOpaque (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) :
    (env.pushOpaque r entry).entries = (env.push r entry).entries := rfl

/-- Whether conversion must not unfold this reference's body. -/
def isOpaque (env : Env β) (r : ConstRef β) : Bool :=
  (env.noUnfold.getD (refHash env.keyHash r) []).any (· = r)

/-- The environment conversion reads: theorem and opaque bodies hidden. -/
def reductionView (env : Env β) : Model.Environment β := fun r =>
  (env.lookup r).map fun entry => if env.isOpaque r then { entry with body := none } else entry

theorem realizes_reductionView {V : Type v} [Model.SetTheory V] {constants : Assignment β V}
    (env : Env β) (h : Realizes constants env.toEnvironment) :
    Realizes constants env.reductionView := by
  have lift : ∀ r e, env.reductionView r = some e → ∃ e₀, env.toEnvironment r = some e₀ ∧
      e.universes = e₀.universes ∧ e.type = e₀.type ∧ e.equations = e₀.equations ∧
        e.facts = e₀.facts ∧ (e.body = none ∨ e.body = e₀.body) := by
    intro r e he
    simp only [reductionView, Option.map_eq_some_iff] at he
    obtain ⟨e₀, h₀, rfl⟩ := he
    refine ⟨e₀, h₀, ?_⟩
    split <;> simp
  constructor
  · intro r e he levels hl env'
    obtain ⟨e₀, h₀, hu, ht, -, -, -⟩ := lift r e he
    rw [ht]; exact h.typeValid r e₀ h₀ levels (hu ▸ hl) env'
  · intro r e he levels hl env'
    obtain ⟨e₀, h₀, hu, ht, -, -, -⟩ := lift r e he
    rw [ht]; exact h.member r e₀ h₀ levels (hu ▸ hl) env'
  · intro r e he body hb levels hl env'
    obtain ⟨e₀, h₀, hu, -, -, -, hbody⟩ := lift r e he
    rcases hbody with hn | hs
    · rw [hn] at hb; cases hb
    · exact h.bodyValid r e₀ h₀ body (hs ▸ hb) levels (hu ▸ hl) env'
  · intro r e he body hb levels hl env'
    obtain ⟨e₀, h₀, hu, -, -, -, hbody⟩ := lift r e he
    rcases hbody with hn | hs
    · rw [hn] at hb; cases hb
    · exact h.bodyValue r e₀ h₀ body (hs ▸ hb) levels (hu ▸ hl) env'
  · intro r e he law hlaw levels hl env'
    obtain ⟨e₀, h₀, hu, -, heq, -, -⟩ := lift r e he
    exact h.equationValue r e₀ h₀ law (heq ▸ hlaw) levels (hu ▸ hl) env'
  · intro r e he fact hf levels hl env'
    obtain ⟨e₀, h₀, hu, -, -, hfacts, -⟩ := lift r e he
    exact h.factMeaning r e₀ h₀ fact (hfacts ▸ hf) levels (hu ▸ hl) env'

/-- Existing entries, including bodies, equations, and facts, are unchanged. -/
def Preserves (before after : Env β) : Prop :=
  ∀ r entry, before.toEnvironment r = some entry → after.toEnvironment r = some entry

theorem Preserves.refl (env : Env β) : Preserves env env := fun _ _ h => h

theorem Preserves.trans {a b c : Env β} (h₁ : Preserves a b) (h₂ : Preserves b c) :
    Preserves a c := fun r e h => h₂ r e (h₁ r e h)

theorem preserves_push (env : Env β) (r : ConstRef β) (entry : ConstantEntry β)
    (fresh : env.toEnvironment r = none) : env.Preserves (env.push r entry) := by
  intro q old hq
  rw [toEnvironment_push]
  exact Environment.insert_old fresh hq

@[simp] theorem lookup_push_same (env : Env β) (r : ConstRef β) (entry : ConstantEntry β) :
    (env.push r entry).toEnvironment r = some entry := by
  rw [toEnvironment_push]
  exact Environment.insert_same ..

end Env

variable {β : Type u} [DecidableEq β]

/-- A model of a checked environment in the set theory `V`: one assignment of
a set to every reference at every universe instance under which every
installed entry is realized (`Model.Realizes`): its type is well denoted, the
constant is a member of what its type denotes, its body if any denotes the
constant, and its published equations and facts hold. The environment is
also syntactically well formed. -/
structure Model (V : Type v) [SetTheory V] (env : Env β) where
  constants : Assignment β V
  realizes : Realizes constants env.toEnvironment
  wf : env.toEnvironment.WF

/-- An empty environment has a model in every set theory. -/
noncomputable def Model.emptyEnvWith (V : Type v) [SetTheory V] (keyHash : β → UInt64) :
    Model V (Env.emptyWith keyHash) where
  constants := fun _ _ => SetTheory.empty
  realizes :=
    { typeValid := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      member := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      bodyValid := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      bodyValue := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      equationValue := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      factMeaning := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h }
  wf :=
    { typeScope := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      bodyScope := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      typeReferences := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      bodyReferences := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      equationScope := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      equationReferences := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      factScope := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h
      factReferences := fun _ _ h => by rw [Env.toEnvironment_emptyWith] at h; cases h }

/-- The empty environment has a model in every set theory. -/
noncomputable def Model.emptyEnv (V : Type v) [SetTheory V] : Model V (Env.empty : Env β) :=
  Model.emptyEnvWith V _

/-- One accepted step extends every model of the input environment. -/
def StepClaim (env env' : Env β) : Prop :=
  ∀ (V : Type v) [SetTheory V], Model.{u,v} V env → Nonempty (Model.{u,v} V env')

theorem StepClaim.refl (env : Env β) : StepClaim.{u,v} env env := fun _ _ m => ⟨m⟩

theorem StepClaim.trans {a b c : Env β} (h₁ : StepClaim.{u,v} a b) (h₂ : StepClaim.{u,v} b c) :
    StepClaim.{u,v} a c := fun V _ m => (h₁ V m).elim fun m' => h₂ V m'

/-- Admission supplies both model extension and exact old-lookup preservation.
Model existence alone does not establish the latter. Both fields are erased. -/
structure AdmissionClaim (before after : Env β) : Prop where
  step : StepClaim.{u,v} before after
  preserves : before.Preserves after

theorem AdmissionClaim.refl (env : Env β) : AdmissionClaim.{u,v} env env :=
  ⟨StepClaim.refl env, Env.Preserves.refl env⟩

theorem AdmissionClaim.trans {a b c : Env β}
    (h₁ : AdmissionClaim.{u,v} a b) (h₂ : AdmissionClaim.{u,v} b c) :
    AdmissionClaim.{u,v} a c := ⟨h₁.step.trans h₂.step, h₁.preserves.trans h₂.preserves⟩

end Ix.Kernel

namespace Ix.Kernel.Env

variable {β : Type u} [DecidableEq β]

/-- Install several entries at once; the list is newest first. -/
def pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β)) : Env β :=
  rs.foldr (fun e acc => acc.push e.1 e.2) env

omit [DecidableEq β] in
theorem entries_pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β)) :
    (env.pushList rs).entries = rs ++ env.entries := by
  induction rs with
  | nil => rfl
  | cons e rs ih =>
    simp only [pushList, List.foldr_cons] at *
    show (e.1, e.2) :: _ = _
    rw [ih]; rfl

theorem lookup_pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β))
    (q : ConstRef β) :
    (env.pushList rs).lookup q =
      match rs.find? (fun e => e.1 == q) with
      | some e => some e.2
      | none => env.lookup q := by
  induction rs with
  | nil => rfl
  | cons e rs ih =>
    simp only [pushList, List.foldr_cons] at *
    rw [lookup_push, ih, List.find?_cons]
    by_cases hq : q = e.1
    · subst hq; simp
    · have : (e.1 == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
      simp [hq, this]

theorem toEnvironment_pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β))
    (q : ConstRef β) :
    (env.pushList rs).toEnvironment q =
      match rs.find? (fun e => e.1 == q) with
      | some e => some e.2
      | none => env.toEnvironment q := lookup_pushList env rs q

end Ix.Kernel.Env

namespace Ix.Kernel.Env

variable {β : Type u} [DecidableEq β]
