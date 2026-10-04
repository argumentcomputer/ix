import Ix.CompileCert.Source
import Ix.Kernel.Ixon.Reader

/-! # Explicit proposed source maps

Targets may repeat. Uniqueness is a condition on source keys, never target
addresses. Every fiber member must later pass its own direct translation
comparison against the actual reader output. This module does not treat a
producer alias flag or `Named.original` as evidence.
-/

namespace Ix.CompileCert

structure MapEntry where
  source : Lean.Name
  /-- The supplied record, which must resolve to the proposed member. -/
  record : Address
  target : Kernel.ConstRef Address

abbrev SourceMap := List MapEntry

def SourceMap.find (m : SourceMap) (n : Lean.Name) : Option (Kernel.ConstRef Address) :=
  (m.find? (fun e => e.source == n)).map MapEntry.target

/-- Exactly one map entry per source declaration; legitimate content aliases
are allowed. Record/member validity is discharged against reader output. -/
def MapComplete (s : Source) (m : SourceMap) : Prop :=
  (m.map MapEntry.source).Nodup ∧
    (∀ n ∈ s.names, n ∈ m.map MapEntry.source) ∧
    (∀ e ∈ m, e.source ∈ s.names) ∧
    (∀ e ∈ m, e.record.hash.size = 32 ∧ e.target.block.hash.size = 32)

instance (s : Source) (m : SourceMap) : Decidable (MapComplete s m) :=
  inferInstanceAs (Decidable ((m.map MapEntry.source).Nodup ∧
    (∀ n ∈ s.names, n ∈ m.map MapEntry.source) ∧
    (∀ e ∈ m, e.source ∈ s.names) ∧
    (∀ e ∈ m, e.record.hash.size = 32 ∧ e.target.block.hash.size = 32)))

def checkMap (s : Source) (m : SourceMap) : Bool := decide (MapComplete s m)

theorem checkMap_sound {s : Source} {m : SourceMap}
    (h : checkMap s m = true) : MapComplete s m := of_decide_eq_true h

end Ix.CompileCert
