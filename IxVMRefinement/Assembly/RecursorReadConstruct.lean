import IxVMRefinement.Assembly.RecursorReadInputs

/-! # Constructing a recursor reading from its concrete inputs

The input certificate is sufficient as well as necessary: its actual key/type/rule reads
reconstruct the reader computation. This keeps future context transport local to those
reads, without requiring equality of recursor indexes or whole reader environments.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

private theorem ruleLoop_of_frames {md : Mode} {cx : Ctx md} {reader : MemberReader md}
    {majorOwner : _root_.Address} {majorSlot : Nat}
    {sources : List (Ixon.RecursorRule × Nat)} {rules : List (RecRule md)}
    (frames : List.Forall₂ (RecursorRuleReadFrame cx reader majorOwner majorSlot) sources rules) :
    ∀ acc : List (RecRule md),
      forIn sources acc (fun (source : Ixon.RecursorRule × Nat) (current : List (RecRule md)) => do
        let ctor ← cx.memberKey (.ctor majorOwner majorSlot source.2)
        let rhs ← reader.read source.1.rhs
        pure (.yield (current ++
          [RecRule.mk ctor source.1.fields.toNat 0 .inert rhs false false false]))) =
        .ok (acc ++ rules) := by
  induction frames with
  | nil => intro acc; simp
  | @cons source rule sources rules frame rest ih =>
    intro acc
    rw [List.forIn_cons]
    simp only [frame.1, frame.2.1, bind, Except.bind, pure, Except.pure]
    rw [← frame.2.2]
    simpa only [bind, Except.bind, pure, Except.pure, List.append_assoc, List.singleton_append]
      using ih (acc ++ [rule])

/-- Concrete payload inputs reconstruct the same successful reader result. -/
theorem RecursorReadInputs.run {md : Mode} {cx : Ctx md} {blockLps : List LevelParam}
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    {row : CVal md × RecCounts × List (RecRule md)}
    (inputs : RecursorReadInputs cx blockLps ref entry row) :
    readRecursor cx blockLps ref entry = .ok row := by
  rcases inputs with ⟨owner, slot, record, recursor, majorOwner, majorSlot, major,
    reference, stored, selected, safe, named, levels, typeRead, majorReference,
    majorStored, ruleCount, counts, frames⟩
  subst ref
  unfold readRecursor
  dsimp only
  simp only [stored, selected, safe, Bool.false_eq_true, ↓reduceIte]
  rw [named]
  simp only [bind, Except.bind]
  change (do
    let type ← (MemberReader.mk' cx record (recParam (recLps entry.large blockLps))
      (recursorReaderSelf cx record owner row.1.name)).read recursor.typ
    let some major := inductiveAt cx.store entry.major
      | declined s!"recursor {row.1.name}: its major premise is not an inductive"
    unless major.ctors.size == recursor.rules.size do
      malformed s!"recursor {row.1.name} has {recursor.rules.size} rules for {major.ctors.size} constructors"
    let .member majorOwner majorSlot := entry.major | malformed "recursor major is a constructor"
    let rules ← forIn recursor.rules.zipIdx ([] : List (RecRule md))
        (fun (source : Ixon.RecursorRule × Nat) (current : List (RecRule md)) => do
      let ctor ← cx.memberKey (.ctor majorOwner majorSlot source.2)
      let rhs ← (MemberReader.mk' cx record (recParam (recLps entry.large blockLps))
        (recursorReaderSelf cx record owner row.1.name)).read source.1.rhs
      pure (.yield (current ++
        [RecRule.mk ctor source.1.fields.toNat 0 .inert rhs false false false])))
    pure ((⟨row.1.name, recLps entry.large blockLps, type⟩ : CVal md),
      (⟨recursor.params.toNat, recursor.motives.toNat, recursor.minors.toNat,
        recursor.indices.toNat, recursor.k, some entry.motive⟩ : RecCounts), rules)) = .ok row
  rw [typeRead]
  simp only [bind, Except.bind]
  rw [majorStored]
  simp only [ruleCount, beq_self_eq_true, ↓reduceIte, majorReference]
  rw [← Array.forIn_toList, ruleLoop_of_frames frames]
  simp only [List.nil_append, bind, Except.bind, pure, Except.pure]
  rw [← levels, ← counts]
  cases row with
  | mk value rest => cases value; cases rest; rfl

end IxVM.Refinement.Assembly
