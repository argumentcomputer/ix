import Compilatrix.X86.PhysicalHeapPrimitiveEval
import Compilatrix.IxIR2.LowerSim

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (RVal Credit Frame)

inductive ValueVector (layout : HeapArena.Layout) (offset used : Nat) :
    List Kind → List RVal → List Word → Prop where
  | nil : ValueVector layout offset used [] [] []
  | cons {kind value word kinds values words}
      (head : ValueAt layout offset used kind value word)
      (tail : ValueVector layout offset used kinds values words) :
      ValueVector layout offset used (kind :: kinds) (value :: values) (word :: words)

theorem ValueVector.lengths {layout offset used kinds values words}
    (related : ValueVector layout offset used kinds values words) :
    kinds.length = values.length ∧ words.length = values.length := by
  induction related with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => simp only [List.length_cons, ih.1, ih.2, and_self]

theorem ValueVector.at {layout offset used kinds values words}
    (related : ValueVector layout offset used kinds values words) {index : Nat} {kind : Kind}
    (found : kinds[index]? = some kind) :
    ∃ value word, values[index]? = some value ∧ words[index]? = some word ∧ ValueAt layout offset used kind value word := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst kind
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, word, atValue, atWord, represented⟩ := ih (by simpa using found)
          exact ⟨value, word, by simpa using atValue, by simpa using atWord, represented⟩

theorem ValueVector.append {layout offset used kinds values words otherKinds otherValues otherWords}
    (left : ValueVector layout offset used kinds values words)
    (right : ValueVector layout offset used otherKinds otherValues otherWords) :
    ValueVector layout offset used (kinds ++ otherKinds) (values ++ otherValues) (words ++ otherWords) := by
  induction left with
  | nil => exact right
  | cons head _ ih => exact .cons head ih

inductive CreditVector (layout : HeapArena.Layout) (offset used : Nat) :
    List IxIR2.LayoutId → List Credit → List Word → Prop where
  | nil : CreditVector layout offset used [] [] []
  | cons {id credit word ids credits words}
      (head : CreditAt layout offset used id credit word)
      (tail : CreditVector layout offset used ids credits words) :
      CreditVector layout offset used (id :: ids) (credit :: credits) (word :: words)

theorem CreditVector.lengths {layout offset used ids credits words}
    (related : CreditVector layout offset used ids credits words) :
    ids.length = credits.length ∧ words.length = credits.length := by
  induction related with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => simp only [List.length_cons, ih.1, ih.2, and_self]

theorem CreditVector.at {layout offset used ids credits words}
    (related : CreditVector layout offset used ids credits words) {index : Nat} {id : IxIR2.LayoutId}
    (found : ids[index]? = some id) :
    ∃ credit word, credits[index]? = some credit ∧ words[index]? = some word ∧ CreditAt layout offset used id credit word := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst id
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨credit, word, atCredit, atWord, represented⟩ := ih (by simpa using found)
          exact ⟨credit, word, by simpa using atCredit, by simpa using atWord, represented⟩

theorem TakeValues.related {layout offset used frame scope rawValues rawCredits state sources kinds operands next values}
    (selected : TakeValues scope sources kinds operands next)
    (resolved : IxIR2.Lower.Sim.ResolvedAtomsList rawValues sources values)
    (locals : ScopeAt layout offset used frame scope rawValues rawCredits state) :
    ValueVector layout offset used kinds values (operands.map (HeapCopies.atomValue frame state)) ∧
      ScopeAt layout offset used frame next rawValues rawCredits state := by
  induction selected generalizing values with
  | nil => cases resolved; exact ⟨.nil, locals⟩
  | cons head tail ih =>
      cases resolved with
      | cons atHead atTail =>
          obtain ⟨peeked, remaining⟩ := locals.take head
          obtain ⟨rest, finalLocals⟩ := ih atTail remaining
          exact ⟨.cons (locals.resolved peeked atHead) rest, finalLocals⟩

theorem ArgumentsCode.related {layout offset used frame scope rawValues rawCredits state arguments kinds operands next values}
    (selected : ArgumentsCode scope arguments kinds operands next)
    (resolved : IxIR2.Eval.resolveAtoms rawValues arguments = .ok values)
    (locals : ScopeAt layout offset used frame scope rawValues rawCredits state) :
    ValueVector layout offset used kinds.toList values.toList (operands.map (HeapCopies.atomValue frame state)).toList ∧
      ScopeAt layout offset used frame next rawValues rawCredits state := by
  simpa only [Array.toList_map] using TakeValues.related selected (IxIR2.Lower.Sim.resolvedAtoms_of_resolveAtoms resolved) locals

theorem creditSequence_shape {raw output : Frame} {sources : List IxIR2.CreditId} {credits : List Credit}
    (taken : IxIR2.Eval.CreditTakeSequence raw sources output credits) :
    output = { raw with credits := output.credits } := by
  induction taken with
  | nil => rfl
  | cons head tail ih =>
      conv => lhs; rw [ih]
      rw [head.target_eq.1]

theorem TakeCredits.related {layout offset used frame scope state sources ids next raw output credits}
    (selected : TakeCredits scope sources ids next)
    (taken : IxIR2.Eval.CreditTakeSequence raw sources output credits)
    (locals : ScopeAt layout offset used frame scope raw.values raw.credits state) :
    CreditVector layout offset used ids credits (sources.map (fun source => state.words (frame.localIndex (creditBase + source)))) ∧
      ScopeAt layout offset used frame next output.values output.credits state := by
  induction selected generalizing raw output credits with
  | nil => cases taken; exact ⟨.nil, locals⟩
  | cons head tail ih =>
      cases taken with
      | cons physicalHead physicalTail =>
          obtain ⟨actual, actualAt, represented, remaining⟩ := locals.takeCredit head
          obtain ⟨targetEq, found⟩ := physicalHead.target_eq
          cases Option.some.inj (Option.some.inj (actualAt.symm.trans found))
          subst_vars
          obtain ⟨rest, finalLocals⟩ := ih physicalTail remaining
          exact ⟨.cons represented rest, finalLocals⟩

theorem ScopeAt.ofVectors {layout offset used frame state kinds values words ids credits creditWords}
    (valueVector : ValueVector layout offset used kinds values words)
    (creditVector : CreditVector layout offset used ids credits creditWords)
    (bounded : (Scope.mk (kinds.map some).toArray (ids.map some).toArray).bounded = true)
    (valueWords : ∀ index word, words[index]? = some word → state.words (frame.localIndex index) = word)
    (creditWordsAt : ∀ index word, creditWords[index]? = some word → state.words (frame.localIndex (creditBase + index)) = word) :
    ScopeAt layout offset used frame ⟨(kinds.map some).toArray, (ids.map some).toArray⟩
      values.toArray (credits.map some).toArray state := by
  refine ⟨bounded, by simpa using valueVector.lengths.1, by simpa using creditVector.lengths.1, ?_, ?_⟩
  · intro index kind active
    have found : kinds[index]? = some kind := by simpa using active
    obtain ⟨value, word, atValue, atWord, represented⟩ := valueVector.at found
    exact ⟨value, by simpa using atValue, valueWords index word atWord ▸ represented⟩
  · intro index id active
    have found : ids[index]? = some id := by simpa using active
    obtain ⟨credit, word, atCredit, atWord, represented⟩ := creditVector.at found
    exact ⟨credit, by simp [atCredit], creditWordsAt index word atWord ▸ represented⟩

end Compilatrix.X86.PhysicalHeap
