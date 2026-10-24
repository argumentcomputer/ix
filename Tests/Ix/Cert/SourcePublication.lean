import Ix.Cert.SourcePublication

namespace Tests.Ix.Cert.SourcePublication
open _root_.Ix (Name ConstantInfo)
open _root_.Ix.Compile.SourceGraph
open _root_.Ix.Cert

private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
-- Distinct addresses with the same hash-table bucket hash.
private def key (i : Nat) : Name := .str (.anonymous (addr 0)) s!"k{i}"
  ⟨⟨(Array.replicate 32 (0 : UInt8)).set! 31 i.toUInt8⟩⟩
private def aliasKey (i : Nat) : Name := .str (.anonymous (addr 0)) s!"alias{i}" (key i).getHash
private def ci (k : Name) (kind : Nat) (body : _root_.Ix.Expr) : ConstantInfo :=
  let cv : _root_.Ix.ConstantVal := ⟨k, #[], .mkSort .mkZero⟩
  match kind % 3 with
  | 0 => .defnInfo ⟨cv, body, .abbrev, .safe, #[k]⟩
  | 1 => .thmInfo ⟨cv, body, #[k]⟩
  | _ => .opaqueInfo ⟨cv, body, false, #[k]⟩
private def input (count : Nat) := (List.range count).map fun i => (key i, ci (key i) i (.mkSort .mkZero))
private def nodes (xs : List (Name × ConstantInfo)) := (collect (xs.map fun (k, c) => rowOfCanonical k c)).nodes
private def ordered (xs : List (Name × ConstantInfo)) :=
  decide ((nodes xs).toList.map (·.1) = (SourceGraph.full xs).consts.toList.map (·.1))
private def mapReverses : Bool :=
  letI : Hashable Bool := ⟨fun _ => 0⟩
  let m := (({} : Std.HashMap Bool Nat).insert false 10).insert true 20
  decide (m.toList.map (·.1) = [true, false]) &&
    decide ((m.map (fun _ v => v)).toList.map (·.1) = [false, true])
private def causes : Array _root_.Ix.Compile.ChangedSet.Cause := #[.member, .imageHead, .caller, .regenerated, .clique]
private def changed : _root_.Ix.Compile.ChangedSet.ChangedSet :=
  let es := (causes.map fun c => ⟨key 1, c, none⟩) ++
    #[⟨aliasKey 1, .caller, none⟩, ⟨aliasKey 1, .clique, none⟩, ⟨key 1, .caller, some (key 8)⟩]
  { entries := es, names := es.foldl (fun s e => s.insert e.name) {} }
private def source : List (Name × ConstantInfo) :=
  [(key 1, ci (key 1) 0 (.mkSort .mkZero)), (key 2, ci (key 2) 1 (.mkConst (key 1) #[])),
    (key 3, ci (key 3) 2 (.mkConst (key 2) #[])), (key 9, ci (key 9) 0 (.mkSort .mkZero))]
private def ixe : Ixon.Env :=
  { named := .ofList [(key 1, { addr := addr 50 }), (key 2, { addr := addr 50 }), (key 3, { addr := addr 51 }),
    (key 9, { addr := addr 59 }), (_root_.Ix.Compile.Pass.Clique.rowName (key 1), { addr := addr 90 })] }
private def sameRoots (xs ys : List SelectedRoots.Root) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (x, y) =>
    Name.beqRaw x.source y.source && x.address == y.address && x.reason == y.reason
private def agrees (xs : List (Name × ConstantInfo)) (cs : _root_.Ix.Compile.ChangedSet.ChangedSet) (artifact : Ixon.Env) :=
  let e := SourceGraph.full xs
  sameRoots (SourcePublication.selectOriginal (nodes xs) cs artifact) (SelectedRoots.select e cs e artifact)
private def raw : Array (Lean.Name × Lean.ConstantInfo) :=
  (List.range 20).toArray.map fun i =>
    let name := Lean.Name.num `Publication i
    let c : Lean.ConstantInfo := .opaqueInfo
      { name, levelParams := [], type := .sort (.succ .zero), value := .sort .zero, isUnsafe := false, all := [name] }
    (name, c)
def checks : Array Bool := Id.run do
  let mut out := #[mapReverses]
  for count in [0, 1, 2, 8, 12, 13, 24, 25, 48, 49, 96] do
    let xs := input count
    let suffix := [(aliasKey 2, ci (aliasKey 2) 2 (.mkSort .mkZero)), (key 2, ci (key 2) 1 (.mkSort .mkZero))]
    out := out.push (ordered xs && ordered (xs ++ suffix) && ordered (xs ++ suffix.reverse))
    out := out.push (Std.HashMap.Internal.numBuckets (nodes xs) == Std.HashMap.Internal.numBuckets (SourceGraph.full xs).consts)
  for threshold in [12, 24, 48] do
    out := out.push (Std.HashMap.Internal.numBuckets (nodes (input (threshold + 1))) >
      Std.HashMap.Internal.numBuckets (nodes (input threshold)))
  let noRows := { ixe with named := ixe.named.erase (_root_.Ix.Compile.Pass.Clique.rowName (key 1)) }
  let onlyLast : Ixon.Env := { named := .ofList [(key 3, { addr := addr 51 })] }
  let overwritten := source ++ [(aliasKey 1, ci (aliasKey 1) 2 (.mkSort .mkZero))]
  for xs in [source, source.tail, overwritten, []] do
    for artifact in [ixe, noRows, onlyLast, {}] do
      out := out.push (agrees xs changed artifact && agrees xs {} artifact)
  let selected := SourcePublication.selectOriginal (nodes overwritten) changed ixe
  out := out.push (selected.length == 12 && (selected.filter (·.reason == .cascade)).length == 2 &&
    (selected.filter (·.reason == .direct .caller)).length == 3 &&
    (selected.filter (·.reason == .row)).length == 2 &&
    causes.all (fun c => selected.any (fun r => r.reason == .direct c && Name.beqRaw r.source (key 1))) &&
    selected.any (fun r => r.reason == .row && Name.beqRaw r.source (aliasKey 1)))
  out := out.push ((SourcePublication.selectOriginal (nodes source.tail) changed ixe).length == 2 &&
    (SourcePublication.selectOriginal (nodes source) changed onlyLast).length == 1 &&
    (SourcePublication.selectOriginal (nodes source) changed noRows).length == 10)
  -- Ordinary map equivalence/identity-value mapping cannot supply this order.
  let m := (SourceGraph.full (input 3)).consts
  out := out.push (!decide (m.toList.map (·.1) = (m.map fun _ v => v).toList.map (·.1)))
  for w in [0, 1, 2, 8] do
    let p := Prepass.produce (fun _ => false) raw w
    let e := SourceGraph.full (SourceStream.canonical raw)
    let h := Hybrid.hybridEnv p.2.facts.code (Prepass.run raw).leanByIx
    let names := e.consts.toList.map (·.1)
    let artifact : Ixon.Env := { named := .ofList (names.map fun k => (k, { addr := addr 70, original := some (addr 71, .empty) })) }
    let cs := _root_.Ix.Compile.ChangedSet.ofCompile h default {} artifact
    out := out.push (decide (p.2.facts.nodes.toList.map (·.1) = names) &&
      sameRoots (SourcePublication.selectOriginal p.2.facts.nodes cs artifact)
        (SelectedRoots.selectCompile e default {} e artifact))
  return out
#guard checks.all id
def run : IO Unit := do
  let results ← IO.lazyPure fun _ => checks
  for i in [:results.size] do
    unless results[i]! do throw (IO.userError s!"publication/order control {i} failed")
  IO.println s!"source publication: {results.size} controls; exact structural key/root order, resize growth, aliases and reasons"

/-- info: 'Ix.Cert.SourceOrder.Map.inserted_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceOrder.Map.inserted_keys
/-- info: 'Ix.Cert.SourceOrder.collected_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceOrder.collected_keys
/-- info: 'Ix.Cert.SourceOrder.produced_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceOrder.produced_keys
/-- info: 'Ix.Cert.SourcePublication.selectOriginal_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourcePublication.selectOriginal_produced
/-- info: 'Ix.Cert.SourcePublication.selectCompile_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourcePublication.selectCompile_produced
end Tests.Ix.Cert.SourcePublication
