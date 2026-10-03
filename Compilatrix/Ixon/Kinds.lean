/-!
# Ixon declaration kinds

The definition kind, definition safety and quotient kind tags of Ixon
constants (`Ix.DefKind`, `Ix.DefinitionSafety`, `Ix.QuotKind` in ix), with
their byte codes. Moved unchanged from the retired Ixon v2 constant module.
-/

namespace Compilatrix.Ixon

/-! ## Kind enums -/

/-- Distinguish kinds of definitions. -/
inductive DefKind where
  | defn
  | opaq
  | thm
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace DefKind

def toBits : DefKind → UInt8
  | .defn => 0
  | .opaq => 1
  | .thm => 2

def ofBits? : UInt8 → Option DefKind
  | 0 => some .defn
  | 1 => some .opaq
  | 2 => some .thm
  | _ => none

protected theorem ofBits?_toBits (k : DefKind) : ofBits? k.toBits = some k := by
  cases k <;> rfl

end DefKind

inductive DefinitionSafety where
  | unsaf
  | safe
  | part
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace DefinitionSafety

def toBits : DefinitionSafety → UInt8
  | .unsaf => 0
  | .safe => 1
  | .part => 2

def ofBits? : UInt8 → Option DefinitionSafety
  | 0 => some .unsaf
  | 1 => some .safe
  | 2 => some .part
  | _ => none

protected theorem ofBits?_toBits (s : DefinitionSafety) :
    ofBits? s.toBits = some s := by
  cases s <;> rfl

end DefinitionSafety

/-- Mirrors `Lean.QuotKind`. -/
inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace QuotKind

def toBits : QuotKind → UInt8
  | .type => 0
  | .ctor => 1
  | .lift => 2
  | .ind => 3

def ofBits? : UInt8 → Option QuotKind
  | 0 => some .type
  | 1 => some .ctor
  | 2 => some .lift
  | 3 => some .ind
  | _ => none

protected theorem ofBits?_toBits (q : QuotKind) : ofBits? q.toBits = some q := by
  cases q <;> rfl

end QuotKind

end Compilatrix.Ixon
