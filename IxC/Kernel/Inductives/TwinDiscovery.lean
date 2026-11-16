module

public import IxC.Kernel.Inductives.TwinInstall

@[expose] public section

/-! # Native twin discovery in installation order

The general twin checker remains separate. These selectors consider only stored
recursors without model companions and search the oldest installed entries first.
-/

namespace Ix.Kernel.NativeTwin

def nativeCandidate (find? : Key md → Option (ConstantInfo md))
    (raw annotated : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)) (key : Key md) :
    Option (Part md) := do
  let part ← candidate find? raw annotated mI rP rules key
  if part.model?.isNone then some part else none

def findNativeCanonical (find? : Key md → Option (ConstantInfo md))
    (raw annotated : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)) :
    List (ConstantInfo md) → Option (Part md)
  | [] => none
  | .recInfo cv _ _ _ :: rest =>
    nativeCandidate find? raw annotated mI rP rules cv.name <|>
      findNativeCanonical find? raw annotated mI rP rules rest
  | _ :: rest => findNativeCanonical find? raw annotated mI rP rules rest

def findOldestNative (find? : Key md → Option (ConstantInfo md))
    (raw annotated : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (entries : List (ConstantInfo md)) : Option (Part md) :=
  findNativeCanonical find? raw annotated mI rP rules entries.reverse

theorem nativeCandidate_spec {find? : Key md → Option (ConstantInfo md)}
    {raw annotated : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {key : Key md} {part : Part md}
    (h : nativeCandidate find? raw annotated mI rP rules key = some part) :
    candidate find? raw annotated mI rP rules key = some part ∧ part.model? = none := by
  unfold nativeCandidate at h
  cases hc : candidate find? raw annotated mI rP rules key with
  | none => simp [hc, bind, Option.bind] at h
  | some found =>
    cases hm : found.model? with
    | none =>
      simp only [hc, bind, Option.bind, hm, Option.isNone_none, ↓reduceIte, Option.some.injEq] at h
      subst part
      exact ⟨rfl, hm⟩
    | some value => simp [hc, hm, bind, Option.bind] at h

theorem findNativeCanonical_append (find? : Key md → Option (ConstantInfo md))
    (raw annotated : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)) :
    ∀ entries later,
      findNativeCanonical find? raw annotated mI rP rules (entries ++ later) =
        (findNativeCanonical find? raw annotated mI rP rules entries <|>
          findNativeCanonical find? raw annotated mI rP rules later)
  | [], _ => rfl
  | ci :: entries, later => by
    cases ci with
    | recInfo cv _ _ _ =>
      simp only [List.cons_append, findNativeCanonical, findNativeCanonical_append]
      cases nativeCandidate find? raw annotated mI rP rules cv.name <;> rfl
    | _ => exact findNativeCanonical_append find? raw annotated mI rP rules entries later

/-- Prepending newly installed records preserves an already successful oldest choice
when the inspected lookups are the same. The actual frame clients must separately
establish that lookup agreement and the required installation-order relation. -/
theorem findOldestNative_prepend {find? : Key md → Option (ConstantInfo md)}
    {raw annotated : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {entries : List (ConstantInfo md)} {part : Part md}
    (h : findOldestNative find? raw annotated mI rP rules entries = some part)
    (added : List (ConstantInfo md)) :
    findOldestNative find? raw annotated mI rP rules (added ++ entries) = some part := by
  simp only [findOldestNative, List.reverse_append, findNativeCanonical_append]
  change findNativeCanonical find? raw annotated mI rP rules entries.reverse = some part at h
  rw [h]
  rfl

end Ix.Kernel.NativeTwin
