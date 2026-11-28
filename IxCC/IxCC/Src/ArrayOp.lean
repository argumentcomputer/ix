import IxCC.Src.ArraySpec
import IxCC.Sem.Result

/-!
# The array primitives: the operation set and its meaning (`IxCC.Src.ArrOp`)

Design note: `plans/ONE-PIPELINE.md`, section 1.

**One value.** An `Array`, a `ByteArray` and a `String` have one mathematical value at every level
of the pipeline: a list of values. The twelve operations below are primitives of every evaluator,
bound to Lean constants by family at the source (`Array`, `ByteArray`, `String` differ only in
which tower the source evaluator reads) and one from erasure on.

**One definition.** `ArrOp.eval` gives every operation's meaning over an abstract *value model*
(`Sem.ValModel`: how a value is read as a `Nat`, as an array, as a `List`, and how each is
built). Every evaluator supplies its model and calls this one function, so the levels agree by
definition, as they do for `Nat` (`Src.PrimOp.eval2`) and for words (`Src.WordOp.eval`). Elements
are opaque to every operation, which is why one parametricity theorem (`Sem.ValModel`,
`ArrOp.parametric`) serves every pass.

**Failure.** A wrong kind or count of arguments is `stuck`, as for every primitive. An index out
of range in `get` or `set` is a `trap`, at every level (decision D2): the reference bodies of the
proof-carrying accessors end in an absurdity eliminator, which the source evaluator's rule F4
already makes a trap, so the primitive agrees with the body on a false proof too, and the safety
clause needs no fact about erased proofs. A consequence for the middle end: `get` and `set` are
observable when their result is unused, so they are not dead-code eliminable (`ArrOp.mayTrap`).
No operation fails for a resource or times out (`ArrOp.eval_ne_timeout`, `eval_ne_resource`).

**Bulk operations.** `append`, `extract` and `copySlice` are definable from the others; they are
primitives because their reference bodies cost a push per element.

This module is distinct from `Src.ArrayOp`/`ByteArrayOp`/`StringOp` (`Src/ArraySpec.lean`), the
inventories of pinned source constants of the three families.
-/

set_option autoImplicit false

namespace IxCC.Sem

/-- **A value model**: what an evaluator's values must provide for the list-model primitives.
`arr`/`asArr` build and read an array value, `list`/`asList` a `List` value (the spine of the
pinned `List` constructors), `nat`/`asNat` a `Nat` literal. -/
structure ValModel (V : Type) where
  nat : Nat → V
  asNat : V → Option Nat
  arr : List V → V
  asArr : V → Option (List V)
  list : List V → V
  asList : V → Option (List V)

/-- The laws a model keeps: what it builds, it reads back. -/
structure ValModel.Lawful {V : Type} (M : ValModel V) : Prop where
  asNat_nat : ∀ n, M.asNat (M.nat n) = some n
  asArr_arr : ∀ xs, M.asArr (M.arr xs) = some xs
  asList_list : ∀ xs, M.asList (M.list xs) = some xs

end IxCC.Sem

namespace IxCC.Src

open IxCC.Sem (Result ValModel)

/-- **The array operations that are primitives of every evaluator.** `Array`, `ByteArray` and
`String` constants are bound to them by family at the source. -/
inductive ArrOp where
  /-- `[capacity] ↦ #[]`; the capacity is a hint and has no meaning. -/
  | empty
  /-- `[n, v] ↦` `n` copies of `v`. -/
  | replicate
  /-- `[a] ↦ |a|`. -/
  | size
  /-- `[a, i] ↦ a[i]`; a trap when `i ≥ |a|`. -/
  | get
  /-- `[a, i, v] ↦ a` with element `i` replaced; a trap when `i ≥ |a|`. -/
  | set
  /-- `[a, v] ↦ a ++ [v]`. -/
  | push
  /-- `[a] ↦ a` without its last element (`#[]` stays `#[]`). -/
  | pop
  /-- `[a, b] ↦ a ++ b`. -/
  | append
  /-- `[a, start, stop] ↦` `Src.ArraySpec.extractList`. -/
  | extract
  /-- `[src, srcOff, dest, destOff, len] ↦` `Src.ArraySpec.copySliceList`. -/
  | copySlice
  /-- `[l] ↦` the array of a `List` value (`Array.mk`, from erasure on). -/
  | ofList
  /-- `[a] ↦` the `List` value of an array (`Array.toList`, from erasure on). -/
  | toList
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace ArrOp

def all : List ArrOp :=
  [.empty, .replicate, .size, .get, .set, .push, .pop, .append, .extract, .copySlice, .ofList,
   .toList]

/-- The number of value arguments (types and proofs are not arguments below the source
evaluator). -/
def arity : ArrOp → Nat
  | .empty | .size | .pop | .ofList | .toList => 1
  | .replicate | .get | .push | .append => 2
  | .set | .extract => 3
  | .copySlice => 5

/-- Whether the operation can trap. A trapping operation is observable when its result is not
used, so the middle end may not delete it. -/
def mayTrap : ArrOp → Bool
  | .get | .set => true
  | _ => false

/-- A stable name, for printing and serialisation. -/
def name : ArrOp → String
  | .empty => "arrEmpty" | .replicate => "arrReplicate" | .size => "arrSize" | .get => "arrGet"
  | .set => "arrSet" | .push => "arrPush" | .pop => "arrPop" | .append => "arrAppend"
  | .extract => "arrExtract" | .copySlice => "arrCopySlice" | .ofList => "arrOfList"
  | .toList => "arrToList"

/-- **The meaning of every array primitive**, in any value model. -/
def eval {V : Type} (M : ValModel V) (op : ArrOp) (args : List V) : Result V :=
  match op, args with
  | .empty, [c] =>
    match M.asNat c with
    | some _ => .ok (M.arr [])
    | none => .stuck
  | .replicate, [n, v] =>
    match M.asNat n with
    | some n => .ok (M.arr (List.replicate n v))
    | none => .stuck
  | .size, [a] =>
    match M.asArr a with
    | some xs => .ok (M.nat xs.length)
    | none => .stuck
  | .get, [a, i] =>
    match M.asArr a, M.asNat i with
    | some xs, some i =>
      match xs[i]? with
      | some x => .ok x
      | none => .trap
    | _, _ => .stuck
  | .set, [a, i, v] =>
    match M.asArr a, M.asNat i with
    | some xs, some i => if i < xs.length then .ok (M.arr (xs.set i v)) else .trap
    | _, _ => .stuck
  | .push, [a, v] =>
    match M.asArr a with
    | some xs => .ok (M.arr (xs ++ [v]))
    | none => .stuck
  | .pop, [a] =>
    match M.asArr a with
    | some xs => .ok (M.arr xs.dropLast)
    | none => .stuck
  | .append, [a, b] =>
    match M.asArr a, M.asArr b with
    | some xs, some ys => .ok (M.arr (xs ++ ys))
    | _, _ => .stuck
  | .extract, [a, start, stop] =>
    match M.asArr a, M.asNat start, M.asNat stop with
    | some xs, some start, some stop => .ok (M.arr (ArraySpec.extractList xs start stop))
    | _, _, _ => .stuck
  | .copySlice, [src, srcOff, dest, destOff, len] =>
    match M.asArr src, M.asNat srcOff, M.asArr dest, M.asNat destOff, M.asNat len with
    | some xs, some srcOff, some ys, some destOff, some len =>
      .ok (M.arr (ArraySpec.copySliceList xs srcOff ys destOff len))
    | _, _, _, _, _ => .stuck
  | .ofList, [l] =>
    match M.asList l with
    | some xs => .ok (M.arr xs)
    | none => .stuck
  | .toList, [a] =>
    match M.asArr a with
    | some xs => .ok (M.list xs)
    | none => .stuck
  | _, _ => .stuck

end ArrOp

end IxCC.Src
