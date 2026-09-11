import Ix.Compiler.Ixon.Address
import Std.Data.HashMap.Lemmas

/-!
# Indexed address environments

Proof-facing IR environments are functions whose list constructor uses
`List.find?`.  That definition is intentionally transparent and convenient in
the kernel, but repeated global lookup is linear in the size of a corpus.

This module supplies an extensionally equal two-stage implementation: build a
hash index once, preserving `List.find?`'s first-binding-wins behavior, and
then close over its lookup function.  Keeping those stages explicit matters:
a curried `List → Address → Option α` implementation can otherwise rebuild the
index at every saturated call after compiler arity analysis.
-/

namespace Ix.Compiler.AddressEnv

open Ixon (Address)

abbrev Index (α : Type) := Std.HashMap Address α

/-- Build from right to left so an earlier duplicate overwrites a later one,
exactly matching `List.find?`.  Lean's proved `List.foldr` compiler rewrite
uses its stack-safe implementation in generated code. -/
def build (entries : List (Address × α)) : Index α :=
  entries.foldr (fun entry index => index.insert entry.1 entry.2) {}

/-- Turn an already-built index into the proof model's function type. Partial
application captures the index; it never rebuilds it during lookup. -/
def lookup (index : Index α) : Address → Option α :=
  fun address => index.get? address

theorem get?_build (entries : List (Address × α)) (address : Address) :
    (build entries).get? address =
      (entries.find? (fun entry => entry.1 == address)).map (·.2) := by
  induction entries with
  | nil => simp [build]
  | cons entry rest ih =>
    rw [show build (entry :: rest) = (build rest).insert entry.1 entry.2 by
      rfl]
    rw [Std.HashMap.get?_insert, ih]
    by_cases h : entry.1 = address <;> simp [h]

/-- Lookup equivalence, including duplicate-key precedence and misses. -/
theorem lookup_build_apply (entries : List (Address × α)) (address : Address) :
    lookup (build entries) address =
      (entries.find? (fun entry => entry.1 == address)).map (·.2) := by
  exact get?_build entries address

theorem lookup_build (entries : List (Address × α)) :
    lookup (build entries) = fun address =>
      (entries.find? (fun entry => entry.1 == address)).map (·.2) := by
  funext address
  exact lookup_build_apply entries address

end Ix.Compiler.AddressEnv
