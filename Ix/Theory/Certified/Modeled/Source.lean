/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Modeled.Transport

/-! Exact source readings for model companions. The rule reader constructs
the whole left endpoint from the stored recursor type, specializes the actual
constructor at the major's universe and parameter arguments, and retains the
stored right endpoint. It grants no equation until `checkCompanions?` checks
the corresponding complete equation in the earlier model environment.

Mutual recursors use the store's global constructor offsets. Only rules for
the recursor's actual major family are published on that recursor. Copies of
other families' rules in a shared table do not enable a reduction. Restored
nested auxiliary recursors use their target block's native constructor slots.
-/

namespace Ix.Theory.Certified.Modeled

open Model

universe u v
variable {β : Type u} [DecidableEq β]

structure FamilySource (β : Type u) where
  universes : Nat
  parameters : Nat
  indices : Nat
  type : VExpr β
  constructors : List (Ctor β)

def familySource? (store : Store β) (ref : ConstRef β) : Option (FamilySource β) := do
  let .induct universes parameters indices type constructors .safe ← store.lookup ref | none
  return ⟨universes, parameters, indices, type, constructors⟩

structure RecursorSource (β : Type u) where
  universes : Nat
  parameters : Nat
  indices : Nat
  motives : Nat
  minors : Nat
  type : VExpr β
  rules : List (RecRule β)

/-- K is deliberately unavailable on this admission route. It requires its
own semantic law; a model equation does not grant proof replacement. -/
def recursorSource? (store : Store β) (ref : ConstRef β) : Option (RecursorSource β) := do
  let .recursor universes parameters indices motives minors type rules false .safe ← store.lookup ref | none
  return ⟨universes, parameters, indices, motives, minors, type, rules⟩

def RecursorSource.prefix (source : RecursorSource β) : Nat :=
  source.parameters + source.motives + source.minors

/-- Unlike `telN`/`dropN`, a short telescope positively declines. -/
def splitPi? : Nat → VExpr β → Option (List (VExpr β) × VExpr β)
  | 0, type => some ([], type)
  | n + 1, .forallE domain body => do
    let (domains, result) ← splitPi? n body
    return (domain :: domains, result)
  | _ + 1, _ => none

def splitLam? : Nat → VExpr β → Option (List (VExpr β) × VExpr β)
  | 0, expression => some ([], expression)
  | n + 1, .lam domain body => do
    let (domains, result) ← splitLam? n body
    return (domain :: domains, result)
  | _ + 1, _ => none

def applyPi? : VExpr β → List (VExpr β) → Option (VExpr β)
  | type, [] => some type
  | .forallE _ body, argument :: rest => applyPi? (body.inst argument) rest
  | _, _ :: _ => none

/-- Inspect a constant-headed application through explicit beta redexes.
Restoration may leave a parameter abstraction applied to its arguments. No
definition, equation, projection or other conversion is used by this reader.
The original type and complete equation are still checked without rewriting
their source erasures. Fuel exhaustion is a positive decline. -/
def betaHead? : Nat → VExpr β → Option (VExpr β)
  | 0, _ => none
  | fuel + 1, .app function argument => do
    let function ← betaHead? fuel function
    match function with
    | .lam _ body => betaHead? fuel (body.inst argument)
    | _ => some (.app function argument)
  | _ + 1, expression => some expression

structure MajorSource (β : Type u) where
  family : ConstRef β
  levels : List VLevel
  parameters : List (VExpr β)
  prefixDomains : List (VExpr β)

/-- Read the actual major, including nested parameter expressions. Removing
the index frame must round-trip exactly, so parameters cannot secretly depend
on the fresh result indices. The index arguments themselves are pinned. -/
def majorSource? (store : Store β) (source : RecursorSource β) : Option (MajorSource β) := do
  let (prefixDomains, tail) ← splitPi? source.prefix source.type
  let (_, .forallE major _) ← splitPi? source.indices tail | none
  let major ← betaHead? 512 major
  let .const family levels := major.appHead | none
  let info ← familySource? store family
  if info.indices != source.indices || levels.length != info.universes then none else do
    let arguments := major.appArgs []
    if arguments.length != info.parameters + source.indices then none else do
      if arguments.drop info.parameters != VExpr.bvarRevRange 0 source.indices then none else do
        let actual := arguments.take info.parameters
        let parameters := actual.map (fun p => p.unliftN source.indices 0)
        if parameters.map (·.liftN source.indices) != actual then none else
          return ⟨family, levels, parameters, prefixDomains⟩

structure RawRule (β : Type u) where
  universes : Nat
  type : VExpr β
  lhs : VExpr β
  rhs : VExpr β
  deriving DecidableEq

def eraseRule (rule : Signature.Rule β) : RawRule β :=
  ⟨rule.universes, rule.type.erase, rule.lhs.erase, rule.rhs.erase⟩

/-- Construct the exact source rule at a constructor's native flattened slot.
The specialized field telescope, result family, levels, parameters and indices
determine its whole common type. The complete stored lambda telescope is
retained on the right, and `checkEquation?` checks it against that type; beta
redexes left by restoration need not have identical domain spellings. -/
def ruleSource? (store : Store β) (recursor : ConstRef β) (source : RecursorSource β)
    (major : MajorSource β) (constructor : ConstRef β) : Option (RawRule β) := do
  let .ctor block member _ := constructor | none
  if major.family != .member block member then none else do
    let family ← familySource? store major.family
    let ctor ← store.lookupCtor constructor
    if ctor.safety != .safe || ctor.uvars != family.universes ||
        ctor.nparams != family.parameters then none else do
      let some slot := store.ctorRuleIndex? constructor | none
      let stored ← source.rules[slot]?
      if stored.nfields != ctor.nfields then none else do
        let specialized ← applyPi? ((ctor.type.instL major.levels).liftN source.prefix) major.parameters
        let (fields, result) ← splitPi? ctor.nfields specialized
        if result.appHead != .const major.family major.levels then none else do
          let args := result.appArgs []
          let parameters := major.parameters.map (·.liftN ctor.nfields)
          if args.length != ctor.nparams + source.indices || args.take ctor.nparams != parameters then none else do
            let constructorValue := VExpr.appN (.const constructor major.levels)
              (parameters ++ VExpr.bvarRevRange 0 ctor.nfields)
            let callArgs := VExpr.bvarRevRange ctor.nfields source.prefix ++
              args.drop ctor.nparams ++ [constructorValue]
            let resultType ← applyPi? (source.type.liftN (source.prefix + ctor.nfields)) callArgs
            let telescope := major.prefixDomains ++ fields
            let _ ← splitLam? telescope.length stored.rhs
            return ⟨source.universes, VExpr.forallN telescope resultType,
              VExpr.lamN telescope (VExpr.appN (.const recursor ((List.range source.universes).map VLevel.param))
                callArgs), stored.rhs⟩

def familyConstructors? (store : Store β) (ref : ConstRef β) : Option (List (ConstRef β)) := do
  let .member block member := ref | none
  let source ← familySource? store ref
  return (List.range source.constructors.length).map (.ctor block member ·)

def recursorRules? (store : Store β) (ref : ConstRef β) : Option (List (RawRule β)) := do
  let source ← recursorSource? store ref
  let major ← majorSource? store source
  let constructors ← familyConstructors? store major.family
  constructors.mapM (ruleSource? store ref source major)

/-- A family or constructor gains no computation, projection, eta or K fact
from this route. A recursor gains exactly its checked source equations. -/
def sourceRules? (store : Store β) (ref : ConstRef β) : Option (List (RawRule β)) :=
  match ref with
  | .ctor block member _ => do
    let _ ← familySource? store (.member block member)
    let ctor ← store.lookupCtor ref
    if ctor.safety = .safe then some [] else none
  | .member .. =>
    match store.lookup ref with
    | some (.induct _ _ _ _ _ .safe) => some []
    | some (.recursor ..) => recursorRules? store ref
    | _ => none

def SourceMatches (store : Store β) (companion : Companion β) : Prop :=
  store.type companion.header.ref = some companion.header.type.erase ∧
  store.uvars companion.header.ref = some companion.header.universes ∧
  sourceRules? store companion.header.ref = some (companion.rules.map eraseRule)

instance (store : Store β) (companion : Companion β) : Decidable (SourceMatches store companion) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def sourceFamilies? (store : Store β) (source : β) : Option (List (ConstRef β)) := do
  let contents ← store.blocks source
  if contents.members.isEmpty then none else do
    contents.members.zipIdx.mapM fun (constant, index) =>
      match constant with
      | .induct _ _ _ _ _ .safe => some (.member source index)
      | _ => none

/-- Public family and constructor order is the actual block/member/constructor
order. Original recursors come first, in family order; checked auxiliary
recursors may follow. Each auxiliary's own major and native slots are read
independently, so a proposed permutation cannot change a rule's owner. -/
def sourceRefs? (store : Store β) (source : β) (recursors : List (ConstRef β)) :
    Option (List (ConstRef β)) := do
  let families ← sourceFamilies? store source
  if recursors.length < families.length then none else do
    let majors ← recursors.mapM fun ref => do
      let info ← recursorSource? store ref
      let major ← majorSource? store info
      return major.family
    if majors.take families.length != families then none else do
      let members ← families.mapM fun family => do
        let ctors ← familyConstructors? store family
        return family :: ctors
      return members.flatten ++ recursors

structure Witness (β : Type u) where
  source : β
  recursors : List (ConstRef β)
  companions : List (Companion β)
  equations : List (List (EquationWitness β))

structure Checked (entries : Environment β) (store : Store β) (witness : Witness β) : Prop where
  layout : sourceRefs? store witness.source witness.recursors = some (witness.companions.map (·.header.ref))
  source : ∀ companion ∈ witness.companions, SourceMatches store companion
  models : CheckedCompanions.{u,v} entries witness.companions

def check? (fuel : Nat) (entries : Environment β) (store : Store β) (witness : Witness β) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries store witness)) :=
  if hl : sourceRefs? store witness.source witness.recursors = some (witness.companions.map (·.header.ref)) then
    if hs : ∀ companion ∈ witness.companions, SourceMatches store companion then do
      let checked ← checkCompanions?.{u,v} fuel entries witness.companions witness.equations
      return ⟨hl, hs, checked.down⟩
    else none
  else none

theorem check?_sound {fuel : Nat} {entries : Environment β} {store : Store β} {witness : Witness β} {result}
    (_ : check?.{u,v} fuel entries store witness = some result) : Checked.{u,v} entries store witness := result.down

/-- Data-only provenance, kept in each published source entry. -/
def EntrySource (store : Store β) (ref : ConstRef β) (entry : ConstantEntry β) : Prop :=
  ∃ decision : DecidableEq β, ∃ companion : Companion β,
    @SourceMatches β decision store companion ∧ ref = companion.header.ref ∧ entry = companion.entry

omit [DecidableEq β] in
theorem EntrySource.not_axiom {store : Store β} {ref : ConstRef β} {entry : ConstantEntry β}
    (source : EntrySource store ref entry) {n : Nat} {type : VExpr β} {safety : Safety}
    (h : store.lookup ref = some (.axiom n type safety)) : False := by
  obtain ⟨decision, companion, hm, hr, _⟩ := source
  letI := decision
  have hh := hm.2.2
  rw [← hr] at hh
  cases ref with
  | ctor => cases h
  | member => simp [sourceRules?, h] at hh

theorem publishedEntry_source {entries : Environment β} {store : Store β} {witness : Witness β}
    (checked : Checked.{u,v} entries store witness) {ref : ConstRef β} {entry : ConstantEntry β}
    (h : environment entries witness.companions ref = some entry) :
    entries ref = some entry ∨ EntrySource store ref entry := by
  unfold environment Environment.overlay additions at h
  cases hc : lookupCompanion witness.companions ref with
  | none => simp only [hc, Option.map_none] at h; exact Or.inl h
  | some companion =>
    have he : companion.entry = entry := by simpa [hc] using h
    obtain ⟨hm, hr⟩ := lookupCompanion_sound hc
    exact Or.inr ⟨inferInstance, companion, checked.source companion hm, hr.symm, he.symm⟩

end Ix.Theory.Certified.Modeled
