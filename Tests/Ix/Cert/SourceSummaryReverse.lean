import Ix.Cert.SourceSummaryReverse
import Tests.Ix.Cert.SourceReverse

namespace Tests.Ix.Cert.SourceSummaryReverse
open _root_.Ix (Name ConstantInfo)
open _root_.Ix.Compile.SourceGraph
open _root_.Ix.Cert

private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
private def name (n : Nat) : Name := .str (.anonymous (addr 0)) s!"n{n}" (addr n)
private def aliasKey (n : Nat) : Name := .str (.anonymous (addr 0)) s!"alias{n}" (addr n)
private def sort := _root_.Ix.Expr.mkSort _root_.Ix.Level.mkZero
private def header (n : Name) : _root_.Ix.ConstantVal := ⟨n, #[], sort⟩
private def edge (n d : Name) : ConstantInfo := .axiomInfo ⟨{ header n with type := .mkConst d #[] }, false⟩
private def ind : ConstantInfo := .inductInfo ⟨header (name 4), 0, 0, #[name 4, name 6], #[], 0, false, false, false⟩
private def recursor (all : Array Name) : ConstantInfo := .recInfo ⟨header (name 5), all, 0, 0, 1, 0, #[], false, false⟩
private def code : ConstantInfo := .defnInfo ⟨header (name 1), .mkConst (name 2) #[], .abbrev, .safe, #[name 1]⟩
private def opaqueBody (body : _root_.Ix.Expr) : ConstantInfo := .opaqueInfo ⟨header (aliasKey 1), body, false, #[aliasKey 1]⟩
private def nodes (rows : List (Name × ConstantInfo)) := (collect (rows.map fun (n, ci) => rowOfCanonical n ci)).nodes
private def changes (seeds : List Name) : _root_.Ix.Compile.ChangedSet.ChangedSet :=
  let es := seeds.toArray.flatMap fun n => #[⟨n, .member, none⟩, ⟨n, .caller, none⟩, ⟨n, .clique, none⟩]
  { entries := es, names := es.foldl (fun s e => s.insert e.name) {} }
private def sameRoots (xs ys : List SelectedRoots.Root) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (x, y) =>
    Name.beqRaw x.source y.source && x.address == y.address && x.reason == y.reason
private def agrees (ns : _root_.Ix.Map Name Node) (env : _root_.Ix.Environment) (cs : _root_.Ix.Compile.ChangedSet.ChangedSet) : Bool := Id.run do
  let a := Reverse.build ns
  let b := SourceReverse.build env
  let qs := cs.names.toList ++ (a.toList ++ b.toList).flatMap fun (n, ds) => n :: ds.toList
  let wa := SourceReverse.walk a cs.names
  let wb := SourceReverse.walk b cs.names
  let ixe : Ixon.Env := { named := .ofList ((env.consts.toList.map fun (n, _) => (n, { addr := addr 90 })) ++
    cs.entries.toList.map fun e => (_root_.Ix.Compile.Pass.Clique.rowName e.name, { addr := addr 91 })) }
  let roots := [env, { consts := {} }].all fun sub => [ixe, {}].all fun published =>
    sameRoots (SourceSummaryReverse.select ns cs sub published) (SelectedRoots.select env cs sub published)
  return roots && wa.pending.isEmpty && wb.pending.isEmpty && qs.all (fun d =>
    wa.seen.contains d == wb.seen.contains d && qs.all fun n =>
      (a.getD d #[]).contains n == (b.getD d #[]).contains n)
private def cases : List (List (Name × ConstantInfo)) :=
  [[], [(name 2, edge (name 2) (name 1)), (name 3, edge (name 3) (name 2))],
   [(name 1, edge (name 1) (name 1))], [(name 1, edge (name 1) (name 2)), (name 2, edge (name 2) (aliasKey 1))],
   [(name 4, ind), (name 5, recursor #[name 4])], [(name 4, ind), (name 5, recursor #[aliasKey 4])],
   [(name 4, ind), (name 5, recursor #[])], [(name 1, code), (aliasKey 1, opaqueBody (.mkConst (name 3) #[]))],
   [(name 5, recursor #[name 4]), (aliasKey 5, edge (aliasKey 5) (name 9)), (name 4, ind)],
   [(name 1, opaqueBody (.mkLit (.natVal 7)))],
   [(name 1, opaqueBody (.mkApp (.mkLit (.natVal 7)) (.mkLit (.strVal "summary"))))]]
private def raw : Array (Lean.Name × Lean.ConstantInfo) :=
  let a : Lean.ConstantInfo := .axiomInfo { name := `Summary.a, levelParams := [], type := .const `Summary.absent [], isUnsafe := false }
  let o : Lean.ConstantInfo := .opaqueInfo
    { name := `Summary.o, levelParams := [], type := .const `Nat [],
      value := .lit (.natVal 7), isUnsafe := false, all := [`Summary.o] }
  #[(a.name, a), (o.name, o)]
def checks : Array Bool := Id.run do
  let mut out := #[]
  for rows in cases do
    for seeds in [[], [name 1], [aliasKey 1, name 8], [name 4, name 5]] do
      out := out.push (agrees (nodes rows) (SourceGraph.full rows) (changes seeds))
  for w in [0, 1, 2, 8] do
    let p := Prepass.produce (fun _ => false) raw w
    out := out.push (agrees p.2.facts.nodes (SourceGraph.full (SourceStream.canonical raw))
      (changes [Name.fromLeanName `Summary.absent, Name.fromLeanName `Summary.o]))
  let family := nodes [(name 4, ind), (name 5, recursor #[aliasKey 4])]
  out := out.push (decide ((Reverse.recursors family).getD (name 4) #[] = #[(aliasKey 4, name 5)]))
  out := out.push (!((Reverse.build family).getD (name 5) #[]).contains (name 4))
  let winners := nodes [(name 5, recursor #[name 4]), (aliasKey 5, recursor #[name 4])]
  out := out.push (decide ((Reverse.recursors winners).getD (name 4) #[] = #[(name 4, aliasKey 5)]))
  let repeated := Reverse.appendAt (Reverse.appendAt ({} : Reverse.Index) (name 1) (name 2)) (aliasKey 1) (name 2)
  out := out.push (SourceReverse.edgeCount repeated == 2 && (SourceReverse.walk repeated {(name 1)}).pending.isEmpty)
  return out
#guard checks.all id
def run : IO Unit := do
  let results ← IO.lazyPure fun _ => checks
  unless results.all id do throw (IO.userError "summary reverse finite control failed")
  IO.println s!"summary reverse: {results.size} finite controls; exact edges/reached names and ordered fixed-sub roots"

/-- info: 'Ix.Cert.SourceSummaryReverse.collected_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceSummaryReverse.collected_edges
/-- info: 'Ix.Cert.SourceSummaryReverse.produced_recursors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceSummaryReverse.produced_recursors
/-- info: 'Ix.Cert.SourceSummaryReverse.produced_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceSummaryReverse.produced_edges
/-- info: 'Ix.Cert.SourceSummaryReverse.produced_affected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceSummaryReverse.produced_affected
/-- info: 'Ix.Cert.SourceSummaryReverse.produced_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceSummaryReverse.produced_select
end Tests.Ix.Cert.SourceSummaryReverse
