import IxVMRefinement.Core.Specs.Common

/-! # Registry specs: the `KernelLevels` functions the core calls besides the level layer's

The level layer (`IxVMRefinement/Levels/Spec.lean`) states the comparisons, the zero test,
the smart constructors and the parameter substitution (`level_leq`, `level_equal`,
`level_is_not_zero`, `level_struct_eq`, `level_max`, `level_imax`, `level_reduce`,
`level_inst_params`, `level_list_inst`). This family holds the other `KernelLevels` functions
the core calls: the binder-datum comparison `pw_eq` and the literal comparisons `literal_eq`,
`klimbs_eq`, `bytestream_eq`. In the level layer's style, levels are `RepKLevel` (exact) and
every answer the code decides is stated exactly. (`expr_inst_levels` is in `Specs/Subst.lean`.) -/

namespace IxVM.Refinement.Core.Specs.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- **A literal's data** as IxVM holds it: a limb list, or a byte stream. -/
inductive LitData where
  | nat (limbs : List UInt64)
  | str (bytes : List UInt8)
  deriving DecidableEq

/-- The kernel literal a literal's data reads as (the term seam's reading of `Lit`): a limb
list's value; the string whose UTF-8 encoding the bytes are (`StrBytes`). -/
def LitData.Reads : LitData → Ix.Kernel.Literal → Prop
  | .nat limbs, l => l = .natVal (limbsVal limbs)
  | .str bytes, l => ∃ s, StrBytes s bytes ∧ l = .strVal s

/-- **A literal** (`KernelTypes::KLiteral`, held by value) holding the data `ld`. -/
def LitRep (h : Heap F) (ld : LitData) (v : SourceValue F) : Prop :=
  match ld with
  | .nat limbs => ∃ lp, v = .construct klitEnum "Nat" [lp] ∧ RepList limbListEnum RepU64 h limbs lp
  | .str bytes => ∃ bp, v = .construct klitEnum "Str" [bp] ∧ RepBytes h bytes bp

/-- `KernelLevels::pw_eq(a, b)`: **whether the two levels have the same zero-ness datum**
(`bmeta`: the binder data agree, as `DefEq.lam`/`forallE`/`eta` and inference's datum checks
require). Exact: IxVM's zero sets are sorted without repetition, as the datum's canonical form. -/
def pw_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls → ∀ la lb, RepKLevel h la a → RepKLevel h lb b →
    r = .field (if la.zeronessOf = lb.zeronessOf then 1 else 0) ∧ Heap.Extends h h'

/-- `KernelLevels::literal_eq(a, b)`: **whether the two literals hold the same data** (a limb
list is compared limb by limb, so two limb lists of one value with different lengths answer
`0`; equal data read as the same kernel literal, `DefEq.refl`). Reads only. -/
def literal_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls → ∀ la lb, LitRep h la a → LitRep h lb b →
    r = .field (if la = lb then 1 else 0) ∧ h' = h

/-- `KernelLevels::klimbs_eq(a, b)`: **whether the two limb lists are equal** (so their values
are). Reads only. -/
def klimbs_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls → ∀ la lb, RepList limbListEnum RepU64 h la a →
    RepList limbListEnum RepU64 h lb b → r = .field (if la = lb then 1 else 0) ∧ h' = h

/-- `KernelLevels::bytestream_eq(a, b)`: **whether the two byte strings are equal**. Reads
only. -/
def bytestream_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls → ∀ xs ys, RepBytes h xs a → RepBytes h ys b →
    r = .field (if xs = ys then 1 else 0) ∧ h' = h

/-! ## The family -/

/-- The functions of the family. -/
inductive Fn where
  | pw_eq | literal_eq | klimbs_eq | bytestream_eq
  deriving DecidableEq, Repr

/-- The symbol `ObsFn` names each function by. -/
def Fn.name : Fn → String
  | .pw_eq => "KernelLevels::pw_eq"
  | .literal_eq => "KernelLevels::literal_eq"
  | .klimbs_eq => "KernelLevels::klimbs_eq"
  | .bytestream_eq => "KernelLevels::bytestream_eq"

/-- Each function's spec. -/
def Fn.spec : Fn → SpecFn
  | .pw_eq => Specs.Levels.pw_eq
  | .literal_eq => Specs.Levels.literal_eq
  | .klimbs_eq => Specs.Levels.klimbs_eq
  | .bytestream_eq => Specs.Levels.bytestream_eq

end IxVM.Refinement.Core.Specs.Levels
