import Ix.Cert.SourceClassifier

namespace Tests.Ix.Cert.SourceClassifier
open _root_.Ix (Name ConstantInfo)
open _root_.Ix.Compile.ChangedSet
open _root_.Ix.Compile.SourceGraph
open _root_.Ix.Cert

private def addr (i : Nat) : Address := ⟨⟨Array.replicate 32 i.toUInt8⟩⟩
private def n (s : String) : Name := Name.fromLeanName (`Classifier ++ s.toName)
private def aliasKey (k : Name) : Name := .str .mkAnon "alias" k.getHash
private def header (k : Name) : _root_.Ix.ConstantVal := ⟨k, #[], .mkSort .mkZero⟩
private def ind (k : Name) (all : Array Name) (ctors : Array Name := #[]) : ConstantInfo :=
  .inductInfo ⟨header k, 0, 0, all, ctors, 0, true, false, false⟩
private def defn (k : Name) (all : Array Name) : ConstantInfo :=
  .defnInfo ⟨header k, .mkSort .mkZero, .abbrev, .safe, all⟩
private def opaq (k : Name) : ConstantInfo := .opaqueInfo ⟨header k, .mkSort .mkZero, false, #[k]⟩
private def inputs : List (Name × ConstantInfo) :=
  [(n "A", ind (n "A") #[n "A", n "B"] #[n "A.mk"]), (n "B", ind (n "B") #[n "A", n "B"]),
   (n "A.rec", .recInfo ⟨header (n "A.rec"), #[n "A", n "B"], 0, 0, 0, 0, #[], false, false⟩),
   (n "A.mk", .ctorInfo ⟨header (n "A.mk"), n "A", 0, 0, 0, false⟩),
   (n "D", defn (n "D") #[n "D", n "F"]), (n "F", defn (n "F") #[n "D", n "F"]),
   (n "C", defn (n "C") #[n "C"]), (n "O", opaq (n "O")),
   (n "T", .thmInfo ⟨header (n "T"), .mkSort .mkZero, #[n "T"]⟩)]
private def hybrid (xs : List (Name × ConstantInfo)) : _root_.Ix.Environment :=
  { consts := (collect (xs.map fun (k, ci) => rowOfCanonical k ci)).code,
    fallback? := some (SourceGraph.full xs).get? }
private def blocks : _root_.Ix.CondensedBlocks :=
  { lowLinks := .ofList (inputs.map fun (k, _) => (k, k)),
    blocks := .ofList (inputs.map fun (k, _) => (k, ({k} : _root_.Ix.Set Name))),
    blockRefs := .ofList [(n "D", {n "D._f"}), (n "C", {n "A.rec", n "D._f"})] }
private def layout : Ixon.AuxLayout := { perm := #[1, 0], sourceCtorCounts := #[1, 0], evaporated := #[0, 1] }
private def artifact (original : Bool) (lay : Option Ixon.AuxLayout) : Ixon.Env :=
  { named := .ofList [(n "A", { addr := addr 50, constMeta := { info := .muts #[#[ (n "B").getHash ], #[ (n "A").getHash ]] lay } }),
    (n "B", { addr := addr 50 }),
    (n "D", { addr := addr 60, constMeta := { info := .muts #[#[ (n "D").getHash, (n "F").getHash ]] none } }),
    (n "F", { addr := addr 60 }), (n "T", { addr := addr 70 }),
    (n "O",
      { addr := addr 70, original := if original then some (addr 79, .empty) else none,
        constMeta := { info := .defn (n "O").getHash #[] #[] #[ (n "O").getHash, (n "T").getHash ] {} 0 0 } })] }
private def table (verdict : _root_.Ix.AuxGen.AuxVerdict) : _root_.Ix.AuxGen.AuxTable :=
  { rows := #[{ name := n "O", kind := .other, verdict, addr := some (addr 70) }] }
private def sameBlock (a b : Block) : Bool :=
  a.kind == b.kind && decide (a.all = b.all) && decide (a.classes = b.classes) &&
    a.layout? == b.layout? && a.causes == b.causes
private def entryObs (e : Entry) := (e.name, e.cause, e.ref)
private def same (a b : ChangedSet) : Bool :=
  a.blocks.size == b.blocks.size && (a.blocks.zip b.blocks).all (fun (x, y) => sameBlock x y) &&
    decide (a.entries.map entryObs = b.entries.map entryObs) &&
    (a.names.toList ++ b.names.toList).all (fun k => a.contains k == b.contains k)
private def agrees (h e : _root_.Ix.Environment) : Bool :=
  [false, true].all fun original => [none, some layout].all fun lay =>
    ([{}, table .identical, table .accepted] : List _root_.Ix.AuxGen.AuxTable).all fun t =>
      same (ofCompile h blocks t (artifact original lay)) (ofCompile e blocks t (artifact original lay))
private def has (cs : ChangedSet) (k : Name) (cause : Cause) := cs.entries.any (fun e => e.name == k && e.cause == cause)
private def raw : Array (Lean.Name × Lean.ConstantInfo) :=
  let a : Lean.ConstantInfo := .inductInfo
    { name := `Classifier.A, levelParams := [], type := .sort .zero, numParams := 0, numIndices := 0,
      all := [`Classifier.A], ctors := [], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  let o : Lean.ConstantInfo := .opaqueInfo
    { name := `Classifier.O, levelParams := [], type := .sort (.succ .zero), value := .sort .zero,
      isUnsafe := false, all := [`Classifier.O] }
  let t : Lean.ConstantInfo := .thmInfo
    { name := `Classifier.T, levelParams := [], type := .const `True [], value := .const `True.intro [], all := [`Classifier.T] }
  #[(a.name, a), (o.name, o), (t.name, t)]
def checks : Array Bool := Id.run do
  let mut results := #[]
  for xs in [[], inputs.filter (fun p => !(p.2 matches .inductInfo _)), inputs, inputs.reverse,
      inputs ++ [(aliasKey (n "A"), ind (aliasKey (n "A")) #[aliasKey (n "A"), n "B"])],
      inputs ++ [(aliasKey (n "A"), opaq (aliasKey (n "A")))]] do
    let h := hybrid xs
    let e := SourceGraph.full xs
    results := results.push (agrees h e)
    results := results.push ((n "missing" :: xs.map (·.1)).all fun k =>
      decide ((leanBlocks h).get? k.getHash = (leanBlocks e).get? k.getHash))
  let emptyAll := SourceGraph.full [(n "empty", ind (n "empty") #[])]
  results := results.push (decide ((leanBlocks emptyAll).get? (n "empty").getHash = some #[]) &&
    ((leanBlocks emptyAll).get? (n "missing").getHash).isNone)
  -- Equal hash-table buckets force different iteration, without equal keys.
  let ks := (List.range 3).map fun i => Name.str .mkAnon s!"K{i}"
    ⟨⟨(Array.replicate 32 (0 : UInt8)).set! 31 i.toUInt8⟩⟩
  let xs := ks.map fun k => (k, ind k ks.toArray)
  let a := SourceGraph.full xs
  let b := SourceGraph.full xs.reverse
  results := results.push (!decide (a.consts.toList.map (·.1) = b.consts.toList.map (·.1)) &&
    ks.all (fun k => decide ((leanBlocks a).get? k.getHash = (leanBlocks b).get? k.getHash)) && agrees a b)
  for w in [0, 1, 2, 8] do
    let p := Prepass.produce (fun _ => false) raw w
    let h := Hybrid.hybridEnv p.2.facts.code (Prepass.run raw).leanByIx
    results := results.push (agrees h (SourceGraph.full (SourceStream.canonical raw)) &&
      !h.consts.contains (n "O") && !h.consts.contains (n "T") &&
      sourceDefinition h (artifact false none) (n "O") && sourceDefinition h (artifact false none) (n "T"))
  let h := hybrid inputs
  let plain := ofCompile h blocks {} (artifact false (some layout))
  results := results.push (has plain (n "A.mk") .member && has plain (n "A.rec") .imageHead &&
    has plain (n "C") .caller && has plain (n "D") .clique &&
    plain.blocks.any (fun b => b.kind == .definitions && b.classes.any (·.contains (n "O"))))
  results := results.push (has (ofCompile h blocks {} (artifact true none)) (n "O") .regenerated &&
    !has (ofCompile h blocks (table .identical) (artifact true none)) (n "O") .regenerated &&
    has (ofCompile h blocks (table .accepted) (artifact true none)) (n "O") .regenerated &&
    !sourceDefinition h (artifact true none) (n "O"))
  let wrongNames := { plain with entries := plain.entries.modify 0 fun e => { e with name := aliasKey e.name } }
  let wrongLayout := { plain with blocks := plain.blocks.map fun b =>
    if b.kind == .inductiveBlock then { b with layout? := some { layout with sourceCtorCounts := #[99] } } else b }
  results := results.push (plain.entries.size > 0 && !same plain wrongNames && !same plain wrongLayout)
  return results
#guard checks.all id
def run : IO Unit := do
  let results ← IO.lazyPure fun _ => checks
  for i in [:results.size] do
    unless results[i]! do throw (IO.userError s!"classifier control {i} failed")
  IO.println s!"source classifier: {results.size} finite controls; complete ordered entries, structural names, layouts and all causes"

/-- info: 'Ix.Cert.SourceClassifier.leanBlocks_get_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceClassifier.leanBlocks_get_iff
/-- info: 'Ix.Cert.SourceClassifier.leanBlocks_inductives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceClassifier.leanBlocks_inductives
/-- info: 'Ix.Cert.SourceClassifier.ofCompile_lookups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceClassifier.ofCompile_lookups
/-- info: 'Ix.Cert.SourceClassifier.produced_leanBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceClassifier.produced_leanBlocks
/-- info: 'Ix.Cert.SourceClassifier.produced_ofCompile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceClassifier.produced_ofCompile
end Tests.Ix.Cert.SourceClassifier
