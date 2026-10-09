import Compilatrix.Own.Plain.Proof.Captures

/-! Source checker scope carried by saved join bodies. This is static syntax
data derived at declaration, separately from heap/environment preservation. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

def stackArities (J : List Fir.JEntry) : JoinArities := J.map fun e => (e.id, e.params.length)

def EntryScope (functions : Signatures) (captured : List Fir.Var)
    (older : List Fir.JEntry) (e : Fir.JEntry) : Prop :=
  fresh captured e.params = true ∧
    scopeOk functions (captured ++ e.params)
      (if e.isRec then (e.id, e.params.length) :: stackArities older else stackArities older) e.body = true

inductive StackScope (functions : Signatures) : List Fir.Var → Joins → List Fir.JEntry → Prop
  | nil (live : List Fir.Var) : StackScope functions live [] []
  | cons {live captured : List Fir.Var} {older : Joins} {e : Fir.JEntry} {rest : List Fir.JEntry}
      (order : captured.Sublist live)
      (entry : EntryScope functions captured rest e)
      (tail : StackScope functions captured older rest) :
      StackScope functions live ((e.id, captured) :: older) (e :: rest)

theorem StackScope.bind {functions : Signatures} {live : List Fir.Var}
    {joins : Joins} {J : List Fir.JEntry} (h : StackScope functions live joins J) (x : Fir.Var) :
    StackScope functions (live ++ [x]) joins J := by
  cases h with
  | nil => exact .nil _
  | cons ho he ht => exact .cons (List.sublist_append_of_sublist_left ho) he ht

theorem StackScope.rebind {functions : Signatures} {live : List Fir.Var}
    {joins : Joins} {J : List Fir.JEntry} (h : StackScope functions live joins J) (params : List Fir.Var) :
    StackScope functions (live ++ params) joins J := by
  cases h with
  | nil => exact .nil _
  | cons ho he ht => exact .cons (List.sublist_append_of_sublist_left ho) he ht

theorem StackScope.lookup {functions : Signatures} {live : List Fir.Var}
    {joins : Joins} {J : List Fir.JEntry} (h : StackScope functions live joins J)
    {j : Fir.JoinId} {e : Fir.JEntry} {rest : List Fir.JEntry}
    (hl : Fir.lookupJ j J = some (e, rest)) :
    ∃ captured older, joins.lookup j = some captured ∧ captured.Sublist live ∧
      EntryScope functions captured rest e ∧ StackScope functions captured older rest := by
  induction h with
  | nil => simp [Fir.lookupJ] at hl
  | @cons live captured older e₀ rest₀ ho he ht ih =>
    by_cases hid : e₀.id = j
    · have hh : e₀ = e ∧ rest₀ = rest := by simpa [Fir.lookupJ, hid] using hl
      rcases hh with ⟨rfl, rfl⟩
      exact ⟨captured, older, by simp [List.lookup, hid], ho, he, ht⟩
    · have hl' : Fir.lookupJ j rest₀ = some (e, rest) := by simpa [Fir.lookupJ, hid] using hl
      obtain ⟨captured', older', hm, ho', he', ht'⟩ := ih hl'
      have hb : (j == e₀.id) = false := beq_eq_false_iff_ne.mpr (Ne.symm hid)
      exact ⟨captured', older', by simpa only [List.lookup, hb] using hm,
        ho'.trans ho, he', ht'⟩

theorem StackScope.after {functions : Signatures} {captured : List Fir.Var}
    {older : Joins} {e : Fir.JEntry} {rest : List Fir.JEntry}
    (he : EntryScope functions captured rest e) (ht : StackScope functions captured older rest) :
    StackScope functions (captured ++ e.params)
      (if e.isRec then (e.id, captured) :: older else older) (e.after rest) := by
  cases hr : e.isRec with
  | false => simpa [Fir.JEntry.after, hr] using ht.rebind e.params
  | true =>
    have he' : EntryScope functions captured rest { e with charged := true } := he
    have hs := StackScope.cons (List.sublist_append_left captured e.params) he' ht
    simpa [Fir.JEntry.after, hr] using hs

theorem stackArities_after (e : Fir.JEntry) (rest : List Fir.JEntry) :
    stackArities (e.after rest) =
      if e.isRec then (e.id, e.params.length) :: stackArities rest else stackArities rest := by
  cases hr : e.isRec <;> simp [Fir.JEntry.after, hr, stackArities]


end Compilatrix.Own.Plain
