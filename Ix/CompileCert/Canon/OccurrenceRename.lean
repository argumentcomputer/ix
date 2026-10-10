import Ix.Compile.Canon.OccurrenceKey

namespace Ix.Compile.Canon.OccurrenceRef

def rename (f : Lean.Name → Lean.Name) : OccurrenceRef → OccurrenceRef
  | .named n => .named (f n)
  | .external a => .external a

theorem rename_eq_iff {f : Lean.Name → Lean.Name} (hf : Function.Injective f)
    (a b : OccurrenceRef) : rename f a = rename f b ↔ a = b := by
  cases a <;> cases b <;> simp [rename, hf.eq_iff]

/-- The previous encoding, used only to compare old and typed key equality.
This is never used for a production lookup. -/
def legacy : OccurrenceRef → OccurrenceRef
  | .named n => .named n
  | .external a => .named (.str .anonymous s!"#{a}")

end Ix.Compile.Canon.OccurrenceRef

namespace Ix.Compile.Canon.OccurrenceKey

/-- Constant/projection reference renaming. External addresses, universes
and source binder names are not renamed. -/
def rename (f : Lean.Name → Lean.Name) : OccurrenceKey → OccurrenceKey
  | .bvar i => .bvar i
  | .fvar n => .fvar n
  | .mvar n => .mvar n
  | .sort u => .sort u
  | .const n us => .const (n.rename f) us
  | .app a b => .app (rename f a) (rename f b)
  | .lam n a b bi => .lam n (rename f a) (rename f b) bi
  | .forallE n a b bi => .forallE n (rename f a) (rename f b) bi
  | .letE n a v b nd => .letE n (rename f a) (rename f v) (rename f b) nd
  | .natLit n => .natLit n
  | .strLit s => .strLit s
  | .mdata md b => .mdata md (rename f b)
  | .proj n i b => .proj (n.rename f) i (rename f b)

theorem rename_injective {f : Lean.Name → Lean.Name} (hf : Function.Injective f) :
    Function.Injective (rename f) := by
  intro a b h
  induction a generalizing b <;> cases b <;>
    simp [rename, OccurrenceRef.rename_eq_iff hf] at h <;> grind

theorem rename_eq_iff {f : Lean.Name → Lean.Name} (hf : Function.Injective f)
    (a b : OccurrenceKey) : rename f a = rename f b ↔ a = b :=
  ⟨fun eq => rename_injective hf eq, congrArg (rename f)⟩

/-- Project typed keys to the former address-as-name encoding. All other
fields are identical. The impact census compares this projection, never
advisory cache hints, to distinguish old false matches from real equality. -/
def legacy : OccurrenceKey → OccurrenceKey
  | .const n us => .const n.legacy us
  | .app a b => .app a.legacy b.legacy
  | .lam n a b bi => .lam n a.legacy b.legacy bi
  | .forallE n a b bi => .forallE n a.legacy b.legacy bi
  | .letE n a v b nd => .letE n a.legacy v.legacy b.legacy nd
  | .mdata md b => .mdata md b.legacy
  | .proj n i b => .proj n.legacy i b.legacy
  | e => e

/-- Typed equality refines the former equality: tags can split a false
match but never merge keys distinguished by the previous representation. -/
theorem legacy_congr {a b : OccurrenceKey} (h : a = b) : a.legacy = b.legacy :=
  congrArg legacy h

end Ix.Compile.Canon.OccurrenceKey

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon

/-- Structural occurrence lookup commutes with an injective renaming of
constant-reference names and any corresponding auxiliary-value map. There
is no condition on expression/name digests or on cache buckets. -/
theorem occurrenceLookup_rename (f : Lean.Name → Lean.Name)
    (hf : Function.Injective f) (values : Ix.Name → Ix.Name)
    (entries : List (OccurrenceKey × Ix.Name)) (key : OccurrenceKey) :
    occurrenceLookup (entries.map fun (k,v) => (k.rename f, values v)) (key.rename f) =
      (occurrenceLookup entries key).map values := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k,v⟩ := entry
    simp only [List.map_cons, occurrenceLookup, OccurrenceKey.rename_eq_iff hf]
    split <;> simp_all

end Ix.CompileCert.Canon
