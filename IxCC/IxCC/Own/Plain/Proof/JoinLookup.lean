import IxCC.Own.Plain.Proof.Captures

/-! Lookup and charged re-entry preserve the exact paired stack/body relation.
Ownership filtering uses the separate lexical identity invariant. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

theorem StackDen.lookup {H : Heap} {owned : List RVal} {joins : Joins}
    {jf : List Fir.JEntry} {jo : List JEntry} (h : StackDen H owned joins jf jo)
    {j : Fir.JoinId} {ef : Fir.JEntry} {restf : List Fir.JEntry}
    (hf : Fir.lookupJ j jf = some (ef, restf)) :
    ∃ captured older eo resto,
      lookupJ j jo = some (eo, resto) ∧ joins.lookup j = some captured ∧
      EntryDen H owned captured older ef eo ∧ StackDen H owned older restf resto := by
  induction h with
  | nil => simp [Fir.lookupJ] at hf
  | @cons captured older ef₀ eo₀ jf jo he ht ih =>
    by_cases hid : ef₀.id = j
    · have hh : ef₀ = ef ∧ jf = restf := by simpa [Fir.lookupJ, hid] using hf
      rcases hh with ⟨rfl, rfl⟩
      refine ⟨captured, older, eo₀, jo, ?_, ?_, he, ht⟩
      · simp [lookupJ, he.id, hid]
      · simp [List.lookup, hid]
    · have hf' : Fir.lookupJ j jf = some (ef, restf) := by simpa [Fir.lookupJ, hid] using hf
      obtain ⟨captured', older', eo, resto, ho, hm, he', ht'⟩ := ih hf'
      refine ⟨captured', older', eo, resto, ?_, ?_, he', ht'⟩
      · simpa [lookupJ, he.id, hid] using ho
      · have hb : (j == ef₀.id) = false := beq_eq_false_iff_ne.mpr (Ne.symm hid)
        simpa only [List.lookup, hb] using hm

theorem StackDen.after {H : Heap} {owned : List RVal} {captured : List Fir.Var}
    {older : Joins} {ef : Fir.JEntry} {eo : JEntry}
    {restf : List Fir.JEntry} {resto : List JEntry}
    (he : EntryDen H owned captured older ef eo) (ht : StackDen H owned older restf resto) :
    StackDen H owned (if ef.isRec then (ef.id, captured) :: older else older)
      (ef.after restf) (eo.after resto) := by
  cases hr : ef.isRec with
  | false => simpa [Fir.JEntry.after, JEntry.after, he.isRec, hr] using ht
  | true =>
    have hs := StackDen.cons he.charge ht
    simpa [Fir.JEntry.after, JEntry.after, he.isRec, hr] using hs


end IxCC.Own.Plain
