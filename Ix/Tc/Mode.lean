module

public import Ix.Environment

/-!
Mirror: crates/kernel/src/mode.rs

Kernel mode metadata parameterization.

All kernel types are parameterized by `m : Mode`, which controls the presence
of metadata via the type-level function `Mode.F`:

- **`.«meta»`**: metadata fields stored as `α`.
- **`.anon`**: metadata fields erased to `Unit`.

Semantic expression and universe hashes deliberately never include metadata
in either mode, so anon and meta terms of the same underlying structure carry
identical Blake3 addresses.

Rust's `MetaHash` trait is not ported: its only load-bearing uses are the
`Ord` on `KId` (ported directly in `Ix.Tc.Id` via stored name hashes) and
duplicate-level-param detection (`Mode.F.hasDups` below).
-/

public section
@[expose] section

namespace Ix.Tc

/-- Kernel mode. `anon` erases metadata fields to `Unit`; `«meta»` keeps them.
    Mirrors Rust `ZMode<META>` (`Anon = ZMode<false>`, `Meta = ZMode<true>`). -/
inductive Mode where
  | anon
  | «meta»
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Mode

/-- A metadata field: stores `α` in meta mode, erased to `Unit` in anon mode.
    Mirrors `KernelMode::MField<T>`. -/
@[reducible] def F : Mode → Type → Type
  | .anon, _ => Unit
  | .«meta», α => α

/-- `true` iff this mode carries metadata. Mirrors `KernelMode::HAS_META`.
    Use to guard metadata lookups so they don't execute in anon mode. -/
def hasMeta : Mode → Bool
  | .anon => false
  | .«meta» => true

/-- Wrap a value into a metadata field. In anon mode the value is discarded.
    Mirrors `meta_field`. -/
@[inline] def field : {m : Mode} → α → m.F α
  | .anon, _ => ()
  | .«meta», a => a

/-- Build a metadata field from a thunk. Meta runs the thunk; anon discards it
    unevaluated — metadata-extraction work (arena walks, name resolution) is
    entirely skipped. Mirrors `meta_field_with`. -/
@[inline] def fieldWith : {m : Mode} → (Unit → α) → m.F α
  | .anon, _ => ()
  | .«meta», f => f ()

/-- Monadic variant of `fieldWith`. Meta runs the action (which may throw);
    anon discards it and returns `pure ()`. Mirrors `meta_field_try`. -/
@[inline] def fieldWithM {n : Type → Type} [Monad n] :
    {m : Mode} → (Unit → n α) → n (m.F α)
  | .anon, _ => pure ()
  | .«meta», f => f ()

/-- Extract the value from a metadata field when running in meta mode.
    Mirrors `meta_name` (generalized over the field type). -/
@[inline] def get? : {m : Mode} → m.F α → Option α
  | .anon, _ => none
  | .«meta», a => some a

namespace F

/-- `BEq` eliminator for metadata fields: anon units always compare equal;
    meta compares the payloads. (Instance search cannot case on `m`; a
    match-defined function can.) -/
def beq [BEq α] : {m : Mode} → m.F α → m.F α → Bool
  | .anon, _, _ => true
  | .«meta», a, b => a == b

instance {m : Mode} [BEq α] : BEq (m.F α) := ⟨beq⟩

/-- `Repr` eliminator for metadata fields. -/
def reprF [Repr α] : {m : Mode} → m.F α → Nat → Std.Format
  | .anon, _, _ => .text "()"
  | .«meta», a, p => reprPrec a p

instance {m : Mode} [Repr α] : Repr (m.F α) := ⟨reprF⟩

/-- `Inhabited` eliminator for metadata fields. (Not named `default`: a
    branch-defined helper named `default` would capture itself.) -/
def mkDefault [Inhabited α] : {m : Mode} → m.F α
  | .anon => ()
  | .«meta» => default

instance {m : Mode} [Inhabited α] : Inhabited (m.F α) := ⟨mkDefault⟩

/-- Compare two metadata fields with `cmp`; anon fields always compare equal.
    Replaces Rust's `meta_cmp` (which compared `MetaHash` digests). -/
def cmpBy : {m : Mode} → (α → α → Ordering) → m.F α → m.F α → Ordering
  | .anon, _, _, _ => .eq
  | .«meta», cmp, a, b => cmp a b

/-- Duplicate detection on a metadata list field. Anon (erased) is always
    `false`; meta performs the real check. Mirrors `CheckDupLevelParams`. -/
def hasDups [BEq α] : {m : Mode} → m.F (Array α) → Bool
  | .anon, _ => false
  | .«meta», xs => Id.run do
    let mut i := 0
    for x in xs do
      i := i + 1
      for y in xs.toSubarray i do
        if x == y then return true
    return false

end F

end Mode

/-- Display metadata conditionally across kernel modes. In meta mode, concrete
    types display their content; in anon mode `Unit` signals no content via
    `hasMeta = false` and callers provide a positional or hash fallback.
    Mirrors Rust `MetaDisplay`. -/
class MetaDisplay (α : Type) where
  /-- Whether this field carries displayable metadata. -/
  hasMeta : α → Bool
  /-- Format the metadata value. Check `hasMeta` first and provide a fallback
      (e.g. positional index) when `false`. -/
  metaFmt : α → String

instance : MetaDisplay Unit where
  hasMeta _ := false
  metaFmt _ := ""

instance : MetaDisplay Ix.Name where
  hasMeta n := match n with
    | .anonymous _ => false
    | _ => true
  metaFmt n := toString n

instance : MetaDisplay Lean.BinderInfo where
  hasMeta _ := true
  metaFmt bi := match bi with
    | .default => ""
    | .implicit => "{}"
    | .strictImplicit => "⦃⦄"
    | .instImplicit => "[]"

instance : MetaDisplay Bool where
  hasMeta _ := true
  metaFmt b := toString b

namespace Mode.F

/-- `MetaDisplay.hasMeta` eliminator for metadata fields. -/
def hasMetaF [MetaDisplay α] : {m : Mode} → m.F α → Bool
  | .anon, _ => false
  | .«meta», a => MetaDisplay.hasMeta a

/-- `MetaDisplay.metaFmt` eliminator for metadata fields. -/
def metaFmtF [MetaDisplay α] : {m : Mode} → m.F α → String
  | .anon, _ => ""
  | .«meta», a => MetaDisplay.metaFmt a

instance {m : Mode} [MetaDisplay α] : MetaDisplay (m.F α) where
  hasMeta := hasMetaF
  metaFmt := metaFmtF

end Mode.F

end Ix.Tc

/-- Saturating decrement: `0 - 1 = 0`. Lean `UInt64` subtraction wraps where
    Rust's `saturating_sub` saturates; loose-bound-range (`lbr`) computations
    must use this. -/
@[inline] def UInt64.sat1 (x : UInt64) : UInt64 :=
  if x == 0 then 0 else x - 1

end
end
