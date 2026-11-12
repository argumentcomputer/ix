import IxVMRefinement.Core.Specs.Common

/-! # Registry specs: the level and literal functions the core calls (`KernelLevels`)

The `KernelLevels` entry points the core reaches: the comparisons (`level_equal`, `level_leq`),
the zero tests (`level_is_not_zero`, `pw_eq`), the level constructors and instantiation
(`level_max`, `level_imax`, `level_reduce`, `level_inst_params`, `level_list_inst`) and the
literal comparisons (`literal_eq`, `klimbs_eq`, `bytestream_eq`). Levels are read up to semantic
equality (`LvRep`, `LvListRep`), as the statement's `Levels` reads them (`RepKLevel`,
`Level.eval`); a comparison claims something for the answer `1` only. `expr_inst_levels` is in
`Specs/Subst.lean`. -/

namespace IxVM.Refinement.Core.Specs.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-- **A literal** (`KernelTypes::KLiteral`, held by value): a limb list read as its value, or a
byte stream read as the string it is the UTF-8 encoding of (as the term seam reads `Lit`). -/
def LitRep (h : Heap F) (l : Ix.Kernel.Literal) (v : SourceValue F) : Prop :=
  (∃ lp n, v = .construct klitEnum "Nat" [lp] ∧ RepLimbs h n lp ∧ l = .natVal n) ∨
  (∃ bp bytes s, v = .construct klitEnum "Str" [bp] ∧ RepBytes h bytes bp ∧ StrBytes s bytes ∧
    l = .strVal s)

/-- `KernelLevels::level_equal(a, b)`: **`1` claims equal values at every assignment**
(`DefEq.sort`, `DefEq.const` read `LvEq`); `0` claims nothing. -/
def level_equal : SpecFn := fun c args h r h' calls =>
  ∀ a b u v, args = [a, b] → Good c calls → LvRep h u a → LvRep h v b →
    r = .field 1 → LvEq u v

/-- `KernelLevels::level_leq(a, b)`: **`1` claims `a ≤ b` at every assignment**; `0` claims
nothing. -/
def level_leq : SpecFn := fun c args h r h' calls =>
  ∀ a b u v, args = [a, b] → Good c calls → LvRep h u a → LvRep h v b →
    r = .field 1 → ∀ φ, Ix.Kernel.Level.eval φ u ≤ Ix.Kernel.Level.eval φ v

/-- `KernelLevels::level_is_not_zero(l)`: **exactly whether the level is never zero**, its
zero-ness datum being `never` (the test is the datum's syntactic computation, `zeronessOf`,
which is semantic). Allocates nothing. The β gate reads `1` (`Red.betaGate`); the certified
branches read `0` and claim nothing from it. -/
def level_is_not_zero : SpecFn := fun c args h r h' calls =>
  ∀ l u, args = [l] → Good c calls → LvRep h u l →
    h' = h ∧ r = .field (if u.zeronessOf.isNever then 1 else 0)

/-- `KernelLevels::pw_eq(a, b)`: **`1` claims the two levels have the same zero-ness datum**
(`bmeta`: binder data agree, as `DefEq.lam`/`forallE`/`eta` and the datum checks of inference
require); `0` claims nothing. -/
def pw_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b u v, args = [a, b] → Good c calls → LvRep h u a → LvRep h v b →
    r = .field 1 → u.zeronessOf = v.zeronessOf

/-- `KernelLevels::level_max(a, b)`: a level whose value is the maximum. -/
def level_max : SpecFn := fun c args h r h' calls =>
  ∀ a b u v, args = [a, b] → Good c calls → LvRep h u a → LvRep h v b →
    LvRep h' (.max u v) r

/-- `KernelLevels::level_imax(a, b)`: a level whose value is `imax`'s. -/
def level_imax : SpecFn := fun c args h r h' calls =>
  ∀ a b u v, args = [a, b] → Good c calls → LvRep h u a → LvRep h v b →
    LvRep h' (.imax u v) r

/-- `KernelLevels::level_reduce(l)`: a level of the same value. -/
def level_reduce : SpecFn := fun c args h r h' calls =>
  ∀ l u, args = [l] → Good c calls → LvRep h u l → LvRep h' u r

/-- `KernelLevels::level_inst_params(l, params)`: **the kernel's level substitution at the
positional parameters** (`Level.subst (List.range n) us`, `n = |us|`), up to value. A parameter
beyond the list has no derivation (`Lists::lookup` fails). -/
def level_inst_params : SpecFn := fun c args h r h' calls =>
  ∀ l params u us, args = [l, params] → Good c calls → LvRep h u l → LvListRep h us params →
    LvRep h' (Ix.Kernel.Level.subst (List.range us.length) us u) r

/-- `KernelLevels::level_list_inst(lvls, params)`: `level_inst_params` on every level of the
list. -/
def level_list_inst : SpecFn := fun c args h r h' calls =>
  ∀ lvls params vs us, args = [lvls, params] → Good c calls → LvListRep h vs lvls →
    LvListRep h us params →
      LvListRep h' (vs.map (Ix.Kernel.Level.subst (List.range us.length) us)) r

/-- `KernelLevels::literal_eq(a, b)`: **`1` claims equal literals** (`DefEq.refl` on two
literals); `0` claims nothing (a limb list is compared limb by limb, so equal values with
different limb lists answer `0`). Allocates nothing. -/
def literal_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b la lb, args = [a, b] → Good c calls → LitRep h la a → LitRep h lb b →
    h' = h ∧ (r = .field 1 → la = lb)

/-- `KernelLevels::klimbs_eq(a, b)`: **`1` claims equal values**; `0` claims nothing.
Allocates nothing. -/
def klimbs_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b n m, args = [a, b] → Good c calls → RepLimbs h n a → RepLimbs h m b →
    h' = h ∧ (r = .field 1 → n = m)

/-- `KernelLevels::bytestream_eq(a, b)`: **`1` claims equal byte strings**; `0` claims nothing.
Allocates nothing. -/
def bytestream_eq : SpecFn := fun c args h r h' calls =>
  ∀ a b xs ys, args = [a, b] → Good c calls → RepBytes h xs a → RepBytes h ys b →
    h' = h ∧ (r = .field 1 → xs = ys)

/-! ## The family -/

/-- The functions of the family. -/
inductive Fn where
  | level_equal | level_leq | level_is_not_zero | pw_eq
  | level_max | level_imax | level_reduce | level_inst_params | level_list_inst
  | literal_eq | klimbs_eq | bytestream_eq
  deriving DecidableEq, Repr

/-- The symbol `ObsFn` names each function by. -/
def Fn.name : Fn → String
  | .level_equal => "KernelLevels::level_equal"
  | .level_leq => "KernelLevels::level_leq"
  | .level_is_not_zero => "KernelLevels::level_is_not_zero"
  | .pw_eq => "KernelLevels::pw_eq"
  | .level_max => "KernelLevels::level_max"
  | .level_imax => "KernelLevels::level_imax"
  | .level_reduce => "KernelLevels::level_reduce"
  | .level_inst_params => "KernelLevels::level_inst_params"
  | .level_list_inst => "KernelLevels::level_list_inst"
  | .literal_eq => "KernelLevels::literal_eq"
  | .klimbs_eq => "KernelLevels::klimbs_eq"
  | .bytestream_eq => "KernelLevels::bytestream_eq"

/-- Each function's spec. -/
def Fn.spec : Fn → SpecFn
  | .level_equal => Specs.Levels.level_equal
  | .level_leq => Specs.Levels.level_leq
  | .level_is_not_zero => Specs.Levels.level_is_not_zero
  | .pw_eq => Specs.Levels.pw_eq
  | .level_max => Specs.Levels.level_max
  | .level_imax => Specs.Levels.level_imax
  | .level_reduce => Specs.Levels.level_reduce
  | .level_inst_params => Specs.Levels.level_inst_params
  | .level_list_inst => Specs.Levels.level_list_inst
  | .literal_eq => Specs.Levels.literal_eq
  | .klimbs_eq => Specs.Levels.klimbs_eq
  | .bytestream_eq => Specs.Levels.bytestream_eq

end IxVM.Refinement.Core.Specs.Levels
