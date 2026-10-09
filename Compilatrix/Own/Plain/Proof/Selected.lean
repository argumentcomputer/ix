import Compilatrix.Own.Plain.Proof.State
import Compilatrix.Own.Plain.Proof.StackRetain

/-! Joint lookup selects one shared capture list and older suffix across all
three stack invariants, preventing independently chosen metadata witnesses. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem StackScope.head {functions : Signatures} {live : List Fir.Var}
    {joins : Joins} {J : List Fir.JEntry} (h : StackScope functions live joins J) :
    match J, joins with
    | e :: rest, (_, captured) :: older =>
      captured.Sublist live ∧ EntryScope functions captured rest e ∧
        StackScope functions captured older rest
    | _, _ => True := by
  cases h with
  | nil => trivial
  | cons ho he ht => exact ⟨ho, he, ht⟩

theorem lookup_ready {functions : Signatures} {H : Heap} {owned : List RVal} {joins : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (hd : StackDen H owned joins Jf Jo)
    {ρ : Own.Env} {live : List Fir.Var}
    (hv : StackViews ρ live joins Jo) (hs : StackScope functions live joins Jf)
    {j : Fir.JoinId} {ef : Fir.JEntry} {restf : List Fir.JEntry}
    (hl : Fir.lookupJ j Jf = some (ef, restf)) :
    ∃ captured older eo resto,
      lookupJ j Jo = some (eo, resto) ∧ joins.lookup j = some captured ∧
      EntryDen H owned captured older ef eo ∧ CaptureView eo.env ρ captured live ∧
      EntryScope functions captured restf ef ∧ StackDen H owned older restf resto ∧
      StackViews eo.env captured older resto ∧ StackScope functions captured older restf := by
  induction hd generalizing ρ live with
  | nil => simp [Fir.lookupJ] at hl
  | @cons captured older ef₀ eo₀ jf jo he ht ih =>
    have hv' : StackViews ρ live ((eo₀.id, captured) :: older) (eo₀ :: jo) := by
      simpa only [he.id] using hv
    obtain ⟨hview, hviews⟩ := StackViews.head hv'
    obtain ⟨horder, hentry, hscope⟩ := StackScope.head hs
    by_cases hij : ef₀.id = j
    · have hh : ef₀ = ef ∧ jf = restf := by simpa [Fir.lookupJ, hij] using hl
      rcases hh with ⟨rfl, rfl⟩
      exact ⟨captured, older, eo₀, jo, by simp [lookupJ, he.id, hij],
        by simp [List.lookup, hij], he, hview, hentry, ht, hviews, hscope⟩
    · have hl' : Fir.lookupJ j jf = some (ef, restf) := by simpa [Fir.lookupJ, hij] using hl
      obtain ⟨captured', older', eo, resto, hlookup, hmeta, hden, hsaved, hscoped, hdt, hvt, hst⟩ :=
        ih hviews hscope hl'
      have hb : (j == ef₀.id) = false := beq_eq_false_iff_ne.mpr (Ne.symm hij)
      exact ⟨captured', older', eo, resto, by simpa [lookupJ, he.id, hij] using hlookup,
        by simpa only [List.lookup, hb] using hmeta,
        hden, hsaved.trans hview, hscoped, hdt, hvt, hst⟩


end Compilatrix.Own.Plain
