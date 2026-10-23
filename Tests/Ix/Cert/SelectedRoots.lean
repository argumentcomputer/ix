import Ix.Cert.SelectedRoots

/-! Pure coverage controls. Synthetic records exercise graph/publication shape;
they do not claim checker acceptance. Run with the strict module build. -/
namespace Tests.Ix.Cert.SelectedRoots

open _root_.Ix.Cert
open _root_.Ix.Cert.SelectedRoots
open _root_.Ix.Compile.ChangedSet

private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
private def name (n : Nat) : _root_.Ix.Name := .str (.anonymous (addr 0)) s!"n{n}" (addr n)
private def sort : _root_.Ix.Expr := .sort (.zero (addr 0)) (addr 0)
private def atom (n : _root_.Ix.Name) (ty := sort) : _root_.Ix.ConstantInfo :=
  .axiomInfo ⟨⟨n, #[], ty⟩, false⟩
private def edge (n d : _root_.Ix.Name) : _root_.Ix.ConstantInfo :=
  atom n (.const d #[] (addr 0))
private def changes (es : Array Entry) : ChangedSet :=
  { entries := es, names := es.foldl (fun s e => s.insert e.name) {} }
private def causes : List Cause := [.member, .imageHead, .caller, .regenerated, .clique]
private def env : _root_.Ix.Environment :=
  { consts := .ofList [(name 1, atom (name 1)), (name 2, edge (name 2) (name 1)),
      (name 3, atom (name 3))] }
private def cs : ChangedSet := changes (causes.toArray.map fun c => ⟨name 1, c, none⟩)
private def ixe : Ixon.Env :=
  { named := .ofList [(name 1, { addr := addr 100 }), (name 2, { addr := addr 100 }),
      (name 3, { addr := addr 101 }),
      (_root_.Ix.Compile.Pass.Clique.rowName (name 1), { addr := addr 200 })] }
private def roots := select env cs env ixe

-- Every cause survives at one address; cascade aliases it; the row is extra.
#guard roots.length == 7
#guard causes.all fun c => roots.any fun r => r.reason == .direct c && r.address == addr 100
#guard roots.any fun r => r.reason == .cascade && r.source == name 2 && r.address == addr 100
#guard roots.any fun r => r.reason == .row && r.address == addr 200
#guard !(roots.any fun r => r.source == name 3)
-- A classified clique without a published row supplies no invented row.
#guard (rowRoots cs env { named := ixe.named.erase (_root_.Ix.Compile.Pass.Clique.rowName (name 1)) }).isEmpty
-- Publication is required; a missing direct publication does not erase its cascade.
#guard (select env cs env { named := .ofList [(name 2, { addr := addr 100 })] }).length == 1
#guard (select env cs { consts := {} } ixe).isEmpty

-- A missing changed endpoint is outside closure.consts but inside Reaches.
private def missing : _root_.Ix.Environment :=
  { consts := .ofList [(name 2, edge (name 2) (name 1))] }
#guard !(closure missing [name 2]).consts.contains (name 1)
#guard affected missing cs (name 2)
#guard (select missing cs missing ixe).length == 1
#guard !(affected missing cs (name 3))
-- Hash-equivalent roots/entries do not need a hash-injectivity premise.
private def alias : _root_.Ix.Name := .str (.anonymous (addr 0)) "alias" (addr 1)
#guard affected env cs alias
#guard (directRoots (changes #[⟨alias, .caller, none⟩]) env ixe).length == 1

-- Literal support contributes an edge even though graphConst has no reference.
private def litEnv : _root_.Ix.Environment :=
  { consts := .ofList [(name 4, atom (name 4) (.lit (.natVal 1) (addr 0)))] }
#guard affected litEnv (changes #[⟨_root_.Ix.Name.fromLeanName `Nat, .member, none⟩]) (name 4)

private def ind (all : Array _root_.Ix.Name) : _root_.Ix.ConstantInfo :=
  .inductInfo ⟨⟨name 4, #[], sort⟩, 0, 0, all, #[], 0, false, false, false⟩
private def recursor : _root_.Ix.ConstantInfo :=
  .recInfo ⟨⟨name 5, #[], sort⟩, #[name 4], 0, 0, 1, 0, #[], false, false⟩
private def family : _root_.Ix.Environment :=
  { consts := .ofList [(name 4, ind #[name 4, name 5]), (name 5, atom (name 5))] }
private def recFamily : _root_.Ix.Environment :=
  { consts := .ofList [(name 4, ind #[name 4]), (name 5, recursor)] }
private def familyChange := changes #[⟨name 5, .regenerated, none⟩]
#guard affected family familyChange (name 4)
#guard affected recFamily familyChange (name 4)

/-- info: 'Ix.Cert.SelectedRoots.affected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SelectedRoots.affected_iff
/-- info: 'Ix.Cert.SelectedRoots.select_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SelectedRoots.select_sound
/-- info: 'Ix.Cert.SelectedRoots.select_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SelectedRoots.select_complete
/-- info: 'Ix.Cert.SelectedRoots.contains_iff_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SelectedRoots.contains_iff_entry
/-- info: 'Ix.Cert.SelectedRoots.required_covered_ofCompile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SelectedRoots.required_covered_ofCompile
/-- info: 'Ix.Cert.SelectedRoots.selected_input_required_ofCompile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SelectedRoots.selected_input_required_ofCompile

end Tests.Ix.Cert.SelectedRoots
