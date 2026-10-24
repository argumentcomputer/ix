import Ix.Cert.SourceReverse

/-! Finite graph/budget controls, not admission or reachability certificates. -/
namespace Tests.Ix.Cert.SourceReverse

open _root_.Ix.Cert
open _root_.Ix.Cert.SourceReverse

private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
private def name (n : Nat) : _root_.Ix.Name := .str (.anonymous (addr 0)) s!"n{n}" (addr n)
private def alias (n : Nat) : _root_.Ix.Name := .str (.anonymous (addr 0)) s!"alias{n}" (addr n)
private def sort : _root_.Ix.Expr := .sort (.zero (addr 0)) (addr 0)
private def atom (n : _root_.Ix.Name) (ty := sort) : _root_.Ix.ConstantInfo :=
  .axiomInfo ⟨⟨n, #[], ty⟩, false⟩
private def edge (n d : _root_.Ix.Name) : _root_.Ix.ConstantInfo := atom n (.const d #[] (addr 0))
private def input : _root_.Ix.Environment :=
  { consts := .ofList [(name 2, edge (name 2) (name 1)),
      (name 3, edge (name 3) (name 2)), (name 9, atom (name 9))] }
private def index := build input

-- Direction, missing final endpoints, and hash-equivalent caller/dependency queries.
#guard !(input.consts.contains (name 1))
#guard (index.getD (name 1) #[]).contains (name 2)
#guard (index.getD (name 2) #[]).contains (name 3)
#guard !((index.getD (name 2) #[]).contains (name 1))
#guard (index.getD (alias 1) #[]).contains (alias 2)
#guard !((index.getD (name 9) #[]).contains (name 3))

-- Owned updates preserve the exact payload array, including order and duplicates.
private def repeated := appendAt (appendAt (appendAt ({} : Index) (name 1) (name 2))
  (alias 1) (name 3)) (name 1) (name 2)
#guard decide (repeated.getD (alias 1) #[] = #[name 2, name 3, name 2])
#guard edgeCount repeated == 3

private def litInput : _root_.Ix.Environment :=
  { consts := .ofList [(name 4, atom (name 4) (.lit (.natVal 1) (addr 0)))] }
#guard ((build litInput).getD (_root_.Ix.Name.fromLeanName `Nat) #[]).contains (name 4)
private def ind (all : Array _root_.Ix.Name) : _root_.Ix.ConstantInfo :=
  .inductInfo ⟨⟨name 4, #[], sort⟩, 0, 0, all, #[], 0, false, false, false⟩
private def recursor (first : _root_.Ix.Name) : _root_.Ix.ConstantInfo :=
  .recInfo ⟨⟨name 5, #[], sort⟩, #[first], 0, 0, 1, 0, #[], false, false⟩
private def family (first : _root_.Ix.Name) : _root_.Ix.Environment :=
  { consts := .ofList [(name 4, ind #[name 4]), (name 5, recursor first)] }
private def grouped : _root_.Ix.Environment :=
  { consts := .ofList [(name 4, ind #[name 4, name 6]) ] }
#guard ((build grouped).getD (name 6) #[]).contains (name 4)
#guard ((build (family (name 4))).getD (name 5) #[]).contains (name 4)
#guard ((build (family (name 4))).getD (name 4) #[]).contains (name 5)
-- Recursor buckets use hash lookup, but first-member filtering stays structural.
#guard decide ((recursors (family (alias 4))).getD (name 4) #[] = #[(alias 4, name 5)])
#guard !((build (family (alias 4))).getD (name 5) #[]).contains (name 4)

private def seed (n : Nat) : Std.HashSet _root_.Ix.Name := {name n}
private def finished := walk index (seed 1)
#guard finished.pending.isEmpty
#guard (#[name 1, name 2, name 3, alias 1]).all finished.seen.contains
#guard !(finished.seen.contains (name 9))
#guard (walk index (seed 8)).seen.contains (name 8)
#guard (walk ({} : Index) (seed 8)).pending.isEmpty
#guard (walk index {}).seen.isEmpty
#guard budget ({} : Index) (seed 8) == 1

private def start : State := ⟨{}, [name 1]⟩
private def self : Index := appendAt {} (name 1) (name 1)
private def cycle : Index := appendAt (appendAt {} (name 1) (name 2)) (name 2) (alias 1)
#guard decide ((walkFuel self 0 start).pending = [name 1])
#guard (walkFuel self 0 start).seen.isEmpty
#guard !(walkFuel self 1 start).pending.isEmpty
#guard (walkFuel self (budget self (seed 1)) start).pending.isEmpty
#guard budget self (seed 1) == 2
#guard (walk cycle (seed 1)).pending.isEmpty
#guard (walk cycle (seed 1)).seen.size == 2
#guard (walk repeated (seed 1)).pending.isEmpty
#guard (walk repeated (seed 1)).seen.size == 3
#guard !(walkFuel repeated 3 start).pending.isEmpty
#guard (walkFuel repeated 4 start).pending.isEmpty
-- A pre-marked name is popped without expanding its otherwise present bucket.
#guard (step cycle ⟨seed 1, [alias 1]⟩).pending.isEmpty

/-- info: 'Ix.Cert.SourceReverse.appendAt_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceReverse.appendAt_lookup
/-- info: 'Ix.Cert.SourceReverse.recursors_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceReverse.recursors_lookup
/-- info: 'Ix.Cert.SourceReverse.dependencies_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceReverse.dependencies_eq
/-- info: 'Ix.Cert.SourceReverse.build_contains_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceReverse.build_contains_iff
/-- info: 'Ix.Cert.SourceReverse.walk_pending_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceReverse.walk_pending_empty

end Tests.Ix.Cert.SourceReverse
