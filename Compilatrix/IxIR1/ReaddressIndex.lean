import Compilatrix.IxIR1.Readdress
import Std.Data.HashSet.Lemmas

/-!
# Indexed address-image checks

The transparent renaming and environment models keep their first-binding-wins
list definitions. These explicitly staged indexes implement those definitions
exactly, including misses and duplicate bindings.
-/

namespace Compilatrix.IxIR1.Readdress

open Ixon (Address)

namespace Renaming

abbrev Index := AddressEnv.Index Address

def Index.ofList (mapping : Renaming) : Index := AddressEnv.build mapping

def Index.apply (index : Index) : Address → Address :=
  fun address => (AddressEnv.lookup index address).getD address

def Index.contains (index : Index) : Address → Bool :=
  fun address => (AddressEnv.lookup index address).isSome

@[simp] theorem Index.apply_ofList (mapping : Renaming) :
    (Index.ofList mapping).apply = Renaming.apply mapping := by
  funext address
  simp only [Index.apply, Index.ofList, AddressEnv.lookup_build_apply,
    Renaming.apply, Renaming.lookup]

@[simp] theorem Index.contains_ofList (mapping : Renaming) :
    (Index.ofList mapping).contains = Renaming.contains mapping := by
  funext address
  simp [Index.contains, Index.ofList, AddressEnv.lookup_build_apply,
    Renaming.contains, List.isSome_find?]

/-- Reverse lookup also retains the first producer when content is deduplicated. -/
def reverseIndex (mapping : Renaming) : Index :=
  Index.ofList (mapping.map fun entry => (entry.2, entry.1))

@[simp] theorem lookup_reverseIndex (mapping : Renaming) (address : Address) :
    AddressEnv.lookup (reverseIndex mapping) address =
      (mapping.find? fun entry => entry.2 == address).map (·.1) := by
  simp [reverseIndex, Index.ofList, AddressEnv.lookup_build_apply, List.find?_map,
    Option.map_map, Function.comp_def]

end Renaming

/-- Fold from the right to retain the same first duplicate as a suffix scan.
The library compiles `foldr` with its proved stack-safe implementation. -/
def duplicateIndex (addresses : List Address) : Std.HashSet Address × Option Address :=
  addresses.foldr (fun address state =>
    (state.1.insert address,
      if state.1.contains address then some address else state.2)) ({}, none)

theorem duplicateIndex_contains (addresses : List Address) (address : Address) :
    (duplicateIndex addresses).1.contains address = addresses.contains address := by
  induction addresses with
  | nil => simp [duplicateIndex]
  | cons found rest ih =>
      change ((duplicateIndex rest).1.insert found).contains address =
        (found :: rest).contains address
      rw [Std.HashSet.contains_insert, ih, List.contains_cons]
      rw [BEq.comm]

def uniqueIndexed (addresses : List Address) : Bool :=
  (duplicateIndex addresses).2.isNone

theorem uniqueIndexed_cons (address : Address) (rest : List Address) :
    uniqueIndexed (address :: rest) = (!rest.contains address && uniqueIndexed rest) := by
  change (if (duplicateIndex rest).1.contains address then some address
    else (duplicateIndex rest).2).isNone = _
  rw [duplicateIndex_contains]
  cases rest.contains address <;> simp [uniqueIndexed]

theorem setContains_ofList (addresses : List Address) :
    (Std.HashSet.ofList addresses).contains = addresses.contains := by
  funext address
  exact Std.HashSet.contains_ofList

theorem contains_map_snd (mapping : Renaming) (address : Address) :
    (mapping.map (·.2)).contains address = mapping.any (fun entry => entry.2 == address) := by
  simp only [List.contains_map]
  congr 1
  funext entry
  exact BEq.comm

/-- Shared environment and renaming indexes for one exact declaration image. -/
structure ImageIndex where
  original : Env.Index
  emitted : Env.Index
  forward : Renaming.Index
  backward : Renaming.Index

def ImageIndex.build (raw declarations : List (Address × Decl))
    (mapping : Renaming) : ImageIndex :=
  { original := Env.Index.ofList raw
    emitted := Env.Index.ofList declarations
    forward := Renaming.Index.ofList mapping
    backward := Renaming.reverseIndex mapping }

def ImageIndex.semanticAudit (index : ImageIndex)
    (raw declarations : List (Address × Decl)) (main rawMain : Code) : Bool :=
  let rename := index.forward.apply
  let original := index.original.toEnv
  let emitted := index.emitted.toEnv
  Code.structurallyEq main (Code.mapAddresses rename rawMain) &&
    raw.all (fun entry =>
      match original entry.1, emitted (rename entry.1) with
      | some before, some after =>
          Decl.structurallyEq after (Decl.mapAddresses rename before)
      | _, _ => false) &&
    declarations.all (fun entry =>
      match emitted entry.1 with
      | some declaration =>
          Decl.structurallyEq (Decl.mapAddresses rename declaration) declaration
      | none => false)

theorem ImageIndex.semanticAudit_build (result : Result)
    (raw : List (Address × Decl)) (rawMain : Code) :
    (ImageIndex.build raw result.declarations result.addressMap).semanticAudit
      raw result.declarations result.main rawMain = result.semanticAudit raw rawMain := by
  simp only [ImageIndex.semanticAudit, ImageIndex.build, Env.Index.toEnv_ofList,
    Renaming.Index.apply_ofList, Result.semanticAudit]
  rfl

end Compilatrix.IxIR1.Readdress
