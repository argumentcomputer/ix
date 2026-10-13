import Ix.CompileCert.FamilyFields

/-! Lift source-related recursor actions through the actual motive-ordered
family loop. Inputs expose index/publication/family facts for later driver
discharge rather than assuming successful whole-family reading. -/

namespace Ix.CompileCert.FamilyRecursors

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

structure Input where
  source : RecursorVal
  owner : Address
  position : Nat
  constant : Ixon.Constant
  entry : RecEntry
  target : Ixon.Recursor
  majorOwner : Address
  majorIndex : Nat
  major : Ixon.Inductive

def Input.ref (input : Input) : ConstRef Address := .member input.owner input.position

def Input.params (input : Input) (reader : Ctx) (blockParams : List Kernel.Name) : List Kernel.Name :=
  reader.recLps input.ref input.entry.large input.target.lvls.toNat blockParams

structure Valid (reader : Ctx) (blockParams : List Kernel.Name)
    (names : Name → Kernel.Name → Prop) (input : Input) : Prop where
  indexed : reader.index.recs[input.ref]? = some input.entry
  stored : reader.store input.owner = some input.constant
  member : (recursorMembers input.constant).find? (·.1 == input.position) = some (input.position, input.target)
  majorRef : input.entry.major = .member input.majorOwner input.majorIndex
  majorFound : inductiveAt reader.store input.entry.major = some input.major
  count : input.major.ctors.size = input.source.rules.size
  safe : input.source.isUnsafe = false
  fields : RecursorEmission.Related
    (FamilyFields.recursorReader reader blockParams input.owner input.position input.constant input.entry input.target)
    names input.source.cnst.levelParams.toList (input.params reader blockParams) input.source input.target

structure RowMeaning (reader : Ctx) (blockParams : List Kernel.Name)
    (names : Name → Kernel.Name → Prop) (input : Input) (row : FamilyReader.RecRow) : Prop where
  name : row.1.name = input.entry.name
  params : row.1.levelParams = input.params reader blockParams
  payload : row.2.1 = input.target
  header : RecursorEmission.Related
    (FamilyFields.recursorReader reader blockParams input.owner input.position input.constant input.entry input.target)
    names input.source.cnst.levelParams.toList (input.params reader blockParams) input.source input.target
  type : ExpressionState.Related names input.source.cnst.levelParams.toList row.1.levelParams input.source.cnst.type row.1.type
  rules : List.Forall₂ (FamilyFields.RuleMeaning names input.source.cnst.levelParams.toList row.1.levelParams)
    input.source.rules.toList row.2.2
  constructors : row.2.2.map (·.ctor) = (List.range' 0 input.source.rules.size).map
    (fun position => reader.nameOf (.ctor input.majorOwner input.majorIndex position))

theorem row_action (reader : Ctx) (blockParams : List Kernel.Name)
    (names : Name → Kernel.Name → Prop) (input : Input) (valid : Valid reader blockParams names input)
    (next : FamilyReader.RecRow → ReadM α) :
    ∃ row, FamilyReader.recursorAction reader blockParams input.ref next = next row ∧
      RowMeaning reader blockParams names input row := by
  obtain ⟨type, rules, action, typeMeaning, ruleMeanings, constructors⟩ := FamilyFields.recursor_action
    reader blockParams input.owner input.position input.constant input.entry input.source input.target
    input.majorOwner input.majorIndex input.major names input.source.cnst.levelParams.toList
    valid.indexed valid.stored valid.member valid.majorRef valid.majorFound valid.count valid.safe valid.fields next
  exact ⟨(⟨input.entry.name, input.params reader blockParams, type⟩, input.target, rules), action,
    ⟨rfl, rfl, rfl, valid.fields, typeMeaning, ruleMeanings, constructors⟩⟩

private theorem push_join (initial : Array α) (head : α) (tail : List α) :
    initial.push head ++ tail.toArray = initial ++ (head :: tail).toArray := by
  rw [Array.push_eq_append, Array.append_assoc]
  exact congrArg (initial ++ ·) (List.toArray_cons head tail).symm

theorem recursors_loop (reader : Ctx) (blockParams : List Kernel.Name)
    (names : Name → Kernel.Name → Prop) (inputs : List Input)
    (valid : ∀ input ∈ inputs, Valid reader blockParams names input) (initial : Array FamilyReader.RecRow) :
    ∃ rows,
      (forIn (inputs.map Input.ref) initial fun ref rows =>
        FamilyReader.recursorAction reader blockParams ref fun row => pure (.yield (rows.push row))) =
          .ok (initial ++ rows.toArray) ∧
      List.Forall₂ (RowMeaning reader blockParams names) inputs rows := by
  induction inputs generalizing initial with
  | nil => exact ⟨[], by simp; rfl, .nil⟩
  | cons input inputs ih =>
    obtain ⟨row, action, meaning⟩ := row_action reader blockParams names input (valid input (by simp))
      (fun row => pure (ForInStep.yield (initial.push row)))
    obtain ⟨rows, tailRun, meanings⟩ := ih (fun input present => valid input (by simp [present])) (initial.push row)
    refine ⟨row :: rows, ?_, .cons meaning meanings⟩
    rw [List.map_cons, List.forIn_cons, action]
    simpa only [pure, Except.pure, bind, Except.bind, push_join] using tailRun

/-- Every actual reference in the supplied motive order is consumed exactly
once, with source-related type/rule rows and retained header correspondence. -/
theorem recursors_read (reader : Ctx) (blockParams : List Kernel.Name)
    (names : Name → Kernel.Name → Prop) (inputs : Array Input) (refs : Array (ConstRef Address))
    (order : refs = inputs.map Input.ref)
    (valid : ∀ input ∈ inputs, Valid reader blockParams names input) :
    ∃ rows, FamilyReader.readRecursors reader blockParams refs = .ok rows ∧
      List.Forall₂ (RowMeaning reader blockParams names) inputs.toList rows.toList := by
  obtain ⟨rows, ran, meanings⟩ := recursors_loop reader blockParams names inputs.toList
    (fun input present => valid input (by simpa using present)) #[]
  refine ⟨rows.toArray, ?_, meanings⟩
  rw [FamilyReader.readRecursors, order, ← Array.forIn_toList]
  simpa using ran

end Ix.CompileCert.FamilyRecursors
