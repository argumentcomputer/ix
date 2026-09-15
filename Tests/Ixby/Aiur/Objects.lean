module
import Tests.Ixby.Aiur.Common
import Ix.Ixby.Aiur.Objects.Refinement

namespace Tests.Ixby.Aiur.Objects

open Ix.Ixby Ix.Ixby.AiurBackend

private def w (n : Nat) : Value := .scalar (.word32 n.toUInt32)
private def g (n : Nat) : Value := .scalar (.field (Goldilocks.reduce n))
private def ext (a b : Nat) : Value :=
  .scalar (.extField ⟨Goldilocks.reduce a, Goldilocks.reduce b⟩)
private def id (n : Nat) (member := 0) (tag := 0) : CtorId :=
  ⟨⟨n % (2 ^ 256), Nat.mod_lt _ (by decide)⟩, member, tag⟩
private def ctors : Array CtorDecl :=
  #[⟨id 37 0 0, 0⟩, ⟨id 37 0 1, 2⟩, ⟨id 83, 2⟩, ⟨id 91, 1⟩, ⟨id 101, 16⟩]
private def obj (index : Nat) (fields : Array Value) : Value := .ctor ctors[index]!.id fields
private def nil : Value := obj 0 #[]
private def listValue (values : List Nat) : Value := values.foldr (fun n tail => obj 1 #[w n, tail]) nil
private def chain : Nat → Value → Value
  | 0, value => value
  | n + 1, value => obj 3 #[chain n value]
private def dag : Nat → Value → Value
  | 0, value => value
  | n + 1, value => let child := dag n value; obj 2 #[child, child]

private def linear (ops : List Op) (arity := 1) : Function := {
  arity, blocks := (ops.toArray.mapIdx fun i op => ⟨arity + i, .letOp op (i + 1)⟩).push
    ⟨arity + ops.length, .ret (.local (arity + ops.length - 1))⟩ }
private def program (function : Function) : Program := { constructors := ctors, functions := #[function] }
private def identity : Program := program (linear [])
private def projection (field : Nat) : Program := program (linear [.project (.local 0) field])
private def wrap : Program := program (linear [.construct 3 [.local 0]])
private def mapList : Program := program {
  arity := 1, blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 3⟩]⟩,
    ⟨1, .letOp (.construct 0 []) 2⟩,
    ⟨2, .ret (.local 1)⟩,
    ⟨3, .letOp (.primitive .word32Add [.local 1, .literal (.word32 1)]) 4⟩,
    ⟨4, .letOp (.callSelf [.local 2]) 5⟩,
    ⟨5, .letOp (.construct 1 [.local 3, .local 4]) 6⟩,
    ⟨6, .ret (.local 5)⟩] }
private def foldList : Program := program {
  arity := 2, blocks := #[
    ⟨2, .caseCtor (.local 0) [⟨1, 2⟩, ⟨0, 1⟩]⟩,
    ⟨2, .ret (.local 1)⟩,
    ⟨4, .letOp (.primitive .word32Add [.local 1, .local 2]) 3⟩,
    ⟨5, .tailCallSelf [.local 3, .local 4]⟩] }
private def casePair : Program := program {
  arity := 2, blocks := #[
    ⟨2, .caseCtor (.local 0) [⟨2, 1⟩]⟩,
    ⟨4, .letOp (.construct 2 [.local 3, .local 1]) 2⟩,
    ⟨5, .ret (.local 4)⟩] }
private def shared (levels : Nat) (extra : List Op := []) : Program :=
  program (linear ((List.range levels).map (fun i => .construct 2 [.local i, .local i]) ++ extra))
private def forest (first := 7) : Array Value :=
  (Array.range 16).map fun i => chain (if i == 0 then first else 7) (w i)
private def forestIdentity : Program := program (linear [] 16)
private def callObjects : Program := { constructors := ctors, functions := #[
  linear [.call 1 [.local 1, .local 0], .project (.local 2) 1] 2,
  linear [.construct 2 [.local 0, .local 1]] 2] }
private def ctorCapacity (n : Nat) : Program := {
  constructors := (Array.range n).map fun i => ⟨id i, 0⟩,
  functions := #[linear [.construct (n - 1) []] 0] }

private def argsFor : Primitive → Array Value
  | .word32ToField => #[w 0xffffffff]
  | .word32Add | .word32And | .word32Or | .word32Xor | .word32Eq | .word32Lt =>
    #[w 0xfffffff0, w 0x21]
  | .fieldInverse => #[g 7]
  | .extInverse | .extFst | .extSnd => #[ext 7 11]
  | .extAdd | .extSub | .extMul | .extEq => #[ext 7 11, ext 13 17]
  | _ => #[g (goldilocksModulus - 1), g 2]

private def branchObjects : Program := program {
  arity := 3, blocks := #[⟨3, .branch (.local 0) 2 1⟩,
    ⟨3, .ret (.local 1)⟩, ⟨3, .ret (.local 2)⟩] }

private def tailObjects : Program := { constructors := ctors, functions := #[
  linear [.call 1 [.local 0, .local 1], .construct 2 [.local 0, .local 2]] 2,
  { arity := 2, blocks := #[⟨2, .tailCall 2 [.local 1, .local 0]⟩] },
  linear [.construct 2 [.local 0, .local 1]] 2] }

private def deepTemporary : Program := program {
  arity := 1, blocks := ((Array.range 63).map fun i =>
    ⟨1 + i, .letOp (.construct 3 [.local i]) (i + 1)⟩).push ⟨64, .ret (.local 0)⟩ }

private def caseCapacity (copies : Nat) : Program := program {
  arity := 16, blocks := ((Array.range copies).map fun i =>
    ⟨16 + i, .letOp (.copy .erased) (i + 1)⟩) ++ #[
      ⟨16 + copies, .caseCtor (.local 0) [⟨4, copies + 1⟩]⟩,
      ⟨32 + copies, .ret (.local (31 + copies))⟩] }

private def caseCapacityInput : Array Value :=
  #[obj 4 ((Array.range 16).map w)] ++ (Array.range 15).map w

private def reorderedMap : Program :=
  let original := mapList.functions[0]!
  let blocks := (original.blocks.set! 0 ⟨1, .caseCtor (.local 0) [⟨4, 1⟩, ⟨1, 3⟩]⟩)
    |>.set! 1 ⟨1, .letOp (.construct 4 []) 2⟩
  { mapList with
    constructors := #[ctors[4]!, ctors[1]!, ctors[2]!, ctors[3]!, ctors[0]!]
    functions := #[{ original with blocks := blocks }] }

private def fixture (p : Program) (input : Array Value) (expected : Value) : Except String Fixture := do
  validateObjectsFragment p
  let actual ← objectsProfile.execute p input objectsProfile.maxSteps |>.mapError (fun e => s!"eval: {repr e}")
  unless actual == expected do throw s!"wrong reference result: {repr actual}, expected {repr expected}"
  Fixture.encode objectsProfile p input

private def rawFixture := Fixture.raw objectsProfile
private def rawProgram := encodeRawProgram objectsProfile
private def rawInput (values : Array Value) : Except String Codec.Bytes :=
  (Codec.Internal.encode 65536 65536 do
    Codec.Internal.writeHeader "IXBI"
    Codec.Internal.writeVector (Codec.Internal.writeValue objectsProfile 1024) values)
  |>.mapError (fun e => s!"raw input: {repr e}")
private def rawOutput (value : Value) : Except String Codec.Bytes :=
  (Codec.Internal.encode 65536 65536 do
    Codec.Internal.writeHeader "IXBO"
    Codec.Internal.writeValue objectsProfile 1024 value)
  |>.mapError (fun e => s!"raw output: {repr e}")
private def successes : List (String × Program × Array Value × Value) :=
  [("scalar without constructors", { identity with constructors := #[] }, #[w 7], w 7),
   ("nullary constructor", identity, #[nil], nil),
   ("erased identity", identity, #[.erased], .erased),
   ("asymmetric nested fields", identity, #[obj 2 #[w 7, obj 3 #[w 19]]], obj 2 #[w 7, obj 3 #[w 19]]),
   ("first projection", projection 0, #[obj 2 #[w 7, w 19]], w 7),
   ("last projection", projection 1, #[obj 2 #[w 7, w 19]], w 19),
   ("nested projection", projection 1, #[obj 2 #[w 7, obj 3 #[w 19]]], obj 3 #[w 19]),
   ("erased projection u32 maximum", projection 0xffffffff, #[.erased], .erased),
   ("constructor case binding preserves caller and field order", casePair, #[obj 2 #[w 7, w 19], w 31], obj 2 #[w 19, w 31]),
   ("object call and return order", callObjects, #[w 7, obj 3 #[w 19]], w 7),
   ("input/output depth exactly 32", identity, #[chain 31 (w 7)], chain 31 (w 7)),
   ("constructed output depth exactly 32", wrap, #[chain 30 (w 7)], chain 31 (w 7)),
   ("intermediate depth 33 projected back to 32", program (linear [.construct 3 [.local 0], .project (.local 1) 0]),
      #[chain 31 (w 7)], chain 31 (w 7)),
   ("input forest exactly 128 nodes", forestIdentity, forest, chain 7 (w 15)),
   ("shared output exactly 128 unfolded nodes", shared 6 [.construct 3 [.local 6]], #[w 7], chain 1 (dag 6 (w 7))),
   ("intermediate 255-node DAG projected to 127", shared 7 [.project (.local 7) 0], #[w 7], dag 6 (w 7)),
   ("constructor capacity exactly 16", ctorCapacity 16, #[], .ctor (id 15) #[]),
   ("maximum width constructor", program (linear [.construct 4 ((List.range 16).map Operand.local)] 16),
      (Array.range 16).map w, obj 4 ((Array.range 16).map w)),
   ("maximum constructor name", { identity with constructors := #[⟨id (2 ^ 256 - 1) 0xffffffff 0xffffffff, 0⟩] },
      #[.ctor (id (2 ^ 256 - 1) 0xffffffff 0xffffffff) #[]], .ctor (id (2 ^ 256 - 1) 0xffffffff 0xffffffff) #[]),
   ("false branch returns object", branchObjects, #[.scalar (.bool false), nil, obj 3 #[w 7]], nil),
   ("true branch returns object", branchObjects, #[.scalar (.bool true), nil, obj 3 #[w 7]], obj 3 #[w 7]),
   ("tail call preserves saved object frame", tailObjects, #[obj 3 #[w 7], nil],
      obj 2 #[obj 3 #[w 7], obj 2 #[nil, obj 3 #[w 7]]]),
   ("unexecuted projection type error allowed", program { arity := 1, blocks := #[
      ⟨1, .ret (.local 0)⟩, ⟨1, .letOp (.project (.literal (.word32 7)) 0) 2⟩, ⟨2, .ret .erased⟩] }, #[nil], nil),
   ("unexecuted case type error allowed", program { arity := 1, blocks := #[
      ⟨1, .ret (.local 0)⟩, ⟨1, .caseCtor (.literal (.word32 7)) [⟨0, 0⟩]⟩] }, #[nil], nil),
   ("intermediate rank 95 with 64 locals", deepTemporary, #[chain 31 (w 7)], chain 31 (w 7)),
   ("case field binding reaches exactly 64 locals", caseCapacity 32, caseCapacityInput, w 15),
   ("nonzero function and block entry", { identity with entry := 1, functions := #[linear [],
      { arity := 1, entry := 1, blocks := #[⟨1, .ret .erased⟩, ⟨1, .ret (.local 0)⟩] }] }, #[nil], nil),
   ("reordered constructor table", reorderedMap, #[listValue [7, 19]], listValue [8, 20])] ++
  ((cryptoPrimitives.filter primitiveSupported).toList.map fun op =>
    let args := argsFor op
    let result := (op.eval objectsProfile.limits args.toList).toOption.getD .erased
    (s!"primitive in object {repr op}", program (linear [
      .primitive op ((List.range op.arity).map Operand.local), .construct 2 [.local op.arity, .local 0]] op.arity),
      args, obj 2 #[result, args[0]!])) ++
  ([0, 1, 3, 16].map fun n =>
    (s!"recursive list map length {n}", mapList, #[listValue (List.range n)], listValue ((List.range n).map (· + 1)))) ++
  ([0, 1, 30, 31].map fun n =>
    (s!"tail-recursive list fold length {n}", foldList, #[listValue (List.range n), w 13], w (13 + n * (n - 1) / 2))) ++
  ((List.range 10).map fun limb =>
    let other := if limb < 8 then id (2 ^ (32 * limb)) else if limb == 8 then id 0 1 else id 0 0 1
    let p : Program := { constructors := #[⟨id 0, 0⟩, ⟨other, 0⟩], functions := #[{
      arity := 1, blocks := #[⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩]⟩,
        ⟨1, .ret (.literal (.word32 7))⟩, ⟨1, .ret (.literal (.word32 19))⟩] }] }
    (s!"constructor identity limb {limb}", p, #[.ctor other #[]], w 19))

private def negatives (base : Fixture) : List (String × Except String Fixture) := Id.run do
  let run (p : Program) (input : Array Value) : Except String Fixture := do
    rawFixture (← rawProgram p) (← rawInput input) base.output
  -- Unused malformed code must preserve the valid entry's input/output: a
  -- rejected *different* output would not demonstrate whole-image admission.
  let code (p : Program) := run p #[obj 2 #[w 7, w 19]]
  let input (values : Array Value) : Except String Fixture := do
    -- Ignore the input and return a tiny valid result, so output admission
    -- cannot mask missing input constructor, type, or depth checks.
    let ignored := program { arity := 1, blocks := #[⟨1, .ret .erased⟩] }
    rawFixture (← rawProgram ignored) (← rawInput values) (← rawOutput .erased)
  let dead (instr : Instr) (locals := 1) : Program :=
    { identity with functions := #[{ identity.functions[0]! with
      blocks := #[⟨1, .ret (.local 0)⟩, ⟨locals, instr⟩, ⟨locals + 1, .ret .erased⟩] }] }
  return [
    ("constructor count 17", run (ctorCapacity 17) #[]),
    ("duplicate unused constructor IDs", code { identity with constructors := ctors.push ctors[0]! }),
    ("duplicate IDs with different arity", code { identity with constructors := ctors.push ⟨ctors[0]!.id, 1⟩ }),
    ("constructor arity 17", code { identity with constructors := ctors.push ⟨id 99, 17⟩ }),
    ("unknown input constructor", input #[.ctor (id 999) #[]]),
    ("input field arity too short", input #[obj 2 #[w 7]]),
    ("input field arity too long", input #[obj 2 #[w 7, w 8, w 9]]),
    ("projection out of bounds", run (projection 2) #[obj 2 #[w 7, w 8]]),
    ("projection u32 maximum", run (projection 0xffffffff) #[obj 2 #[w 7, w 8]]),
    ("projection scalar", run (projection 0) #[w 7]),
    ("projection nullary", run (projection 0) #[nil]),
    ("case scalar", run mapList #[w 7]),
    ("case erased", run mapList #[.erased]),
    ("missing case", run mapList #[obj 3 #[w 7]]),
    ("empty case", run (program { arity := 1, blocks := #[⟨1, .caseCtor (.local 0) []⟩] }) #[nil]),
    ("case binding exceeds 64 locals", run (caseCapacity 33) caseCapacityInput),
    ("primitive object argument", run (program (linear [.primitive .word32ToField [.local 0]])) #[nil]),
    ("input depth 33", input #[chain 32 (w 7)]),
    ("output depth 33", run wrap #[chain 31 (w 7)]),
    ("input forest 129 nodes", run forestIdentity (forest 8)),
    ("output shared DAG 255 nodes", run (shared 7) #[w 7]),
    ("output shared DAG exactly 129 nodes", run (shared 6 [.construct 3 [.local 6], .construct 3 [.local 7]]) #[w 7]),
    ("recursive map stack overflow", run mapList #[listValue (List.range 17)]),
    ("nonterminating tail call", run (program { arity := 1, blocks := #[⟨1, .tailCallSelf [.local 0]⟩] }) #[nil]),
    ("dead construct bad index", code (dead (.letOp (.construct 999 []) 2))),
    ("dead construct wrong arity", code (dead (.letOp (.construct 2 [.local 0]) 2))),
    ("dead projection bad local", code (dead (.letOp (.project (.local 1) 0) 2))),
    ("dead duplicate alternatives", code (dead (.caseCtor (.local 0) [⟨0, 0⟩, ⟨0, 0⟩]))),
    ("case alternative capacity 17", code (dead (.caseCtor (.local 0) (List.replicate 17 ⟨0, 0⟩)))),
    ("dead case bad constructor", code (dead (.caseCtor (.local 0) [⟨99, 0⟩]))),
    ("dead case bad target", code (dead (.caseCtor (.local 0) [⟨0, 99⟩]))),
    ("unselected case wrong frame", run { mapList with functions := #[{ mapList.functions[0]! with
      blocks := mapList.functions[0]!.blocks.set! 3 ⟨2, .ret .erased⟩ }] } #[nil]),
    ("dead closure excluded", code (dead (.letOp (.closure 0 []) 2))),
    ("dead apply excluded", code (dead (.letOp (.apply (.local 0) []) 2))),
    ("dead tailApply excluded", code (dead (.tailApply (.local 0) []))),
    ("dead unsupported primitive", code (dead (.letOp (.primitive .word32Mul [.local 0, .local 0]) 2))),
    ("PAP input excluded", input #[.pap 0 #[]]),
    ("byte scalar excluded", input #[.scalar (.bytes #[])]),
    ("trailing program", rawFixture (base.code.push 0) base.input base.output),
    ("trailing input", rawFixture base.code (base.input.push 0) base.output),
    ("oversized program advice", rawFixture (base.code ++ Array.replicate objectsProfile.programBytes 0) base.input base.output),
    ("oversized input advice", rawFixture base.code (base.input ++ Array.replicate objectsProfile.valueBytes 0) base.output),
    ("wire version", rawFixture (replaceU32 base.code 4 1) base.input base.output),
    ("constructor count u32 maximum", rawFixture (replaceU32 base.code 12 0xffffffff) base.input base.output),
    ("input count u32 maximum", rawFixture base.code (replaceU32 base.input 8 0xffffffff) base.output),
    ("wrong output", rawFixture base.code base.input (base.output.set! (base.output.size - 1) 55)),
    ("swapped constructor output fields", do
      let f ← fixture identity #[obj 2 #[w 7, w 19]] (obj 2 #[w 7, w 19])
      let other ← fixture identity #[obj 2 #[w 19, w 7]] (obj 2 #[w 19, w 7])
      rawFixture f.code f.input other.output)]

private def buildBackend : IO (Except String System) := buildFresh System.buildObjects

public def suite (withProofs := true) (withStats := false) : IO UInt32 :=
    runChecks "ixby-objects" do
  IO.println "ixby-objects (experimental constrained immutable objects)"
  let built ← buildBackend
  let .ok backend := built
    | return [succeeds "interpreter build" built]
  IO.println s!"{backend.compiled.bytecode.circuits.size} function circuits; one system for all guest programs"
  let programs := successes.foldl (init := (#[] : Array Program)) fun acc (_, p, _, _) =>
    if acc.contains p then acc else acc.push p
  IO.println s!"{successes.length} success cases over {programs.size} distinct guest programs"
  let mut checks : List Check := []
  for (label, p, input, expected) in successes do
    checks := checks ++ [succeeds label (fixture p input expected >>= executeFixture backend)]
  let .ok base := fixture identity #[obj 2 #[w 7, w 19]] (obj 2 #[w 7, w 19])
    | return checks ++ [("base fixture failed", false)]
  for (label, p, input, expected) in [
      ("source recursive map", mapList, #[listValue [3, 7]], listValue [4, 8]),
      ("source case field binding", casePair, #[obj 2 #[w 7, w 19], w 31], obj 2 #[w 19, w 31]),
      ("source object return", callObjects, #[w 7, obj 3 #[w 19]], w 7)] do
    checks := checks ++ [succeeds label (fixture p input expected >>= interpretFixture backend objectsToplevel `ixby_objects_exec)]
  for byte in [0, 1, 255] do
    let .ok f := rawFixture (base.code.push byte) base.input base.output
      | return checks ++ [(s!"trailing program byte {byte} fixture failed", false)]
    checks := checks ++ [(s!"source/native trailing program byte {byte} rejected",
      !(interpretFixture backend objectsToplevel `ixby_objects_exec f).isOk &&
      !(backend.execute f.statement f.code f.input).isOk)]
  let bad := negatives base ++
    ((List.range base.code.size).map fun n =>
      (s!"program prefix {n}", rawFixture (base.code.extract 0 n) base.input base.output)) ++
    ((List.range base.input.size).map fun n =>
      (s!"input prefix {n}", rawFixture base.code (base.input.extract 0 n) base.output))
  for (label, result) in bad do
    match result with
    | .error e => checks := checks ++ [(s!"negative fixture {label}: {e}", false)]
    | .ok f =>
      match backend.execute f.statement f.code f.input with
      | .error error =>
        -- Except for the two deliberate output mutations, admission/runtime
        -- negatives must fail BEFORE the terminal output-commitment check.
        let outputMismatch := decide ((error.splitOn "IxBy output commitment").length > 1)
        let deliberateOutput := label == "wrong output" || label == "swapped constructor output fields"
        checks := checks ++ [(s!"rejects {label} at expected stage: {error}",
          outputMismatch == deliberateOutput)]
      | .ok _ => checks := checks ++ [(s!"rejects {label}", false)]
  IO.println s!"  tested {bad.length} malformed/excluded/nonterminal artifacts with matching commitments"
  checks := checks ++ preflightChecks backend base
  if withStats then
    for (label, p, input, expected) in [
        ("recursive map length 16", mapList, #[listValue (List.range 16)], listValue ((List.range 16).map (· + 1))),
        ("tail fold length 31", foldList, #[listValue (List.range 31), w 13], w 478),
        ("shared output 128 nodes", shared 6 [.construct 3 [.local 6]], #[w 7], chain 1 (dag 6 (w 7)))] do
      match fixture p input expected with
      | .ok f => printStats backend label f
      | .error e => IO.eprintln e
  if withProofs then
    checks := checks ++ (← proofChecks backend buildBackend
      (successes.map (fun (label, p, input, expected) => (label, fixture p input expected))) (.ok base))
  return checks

end Tests.Ixby.Aiur.Objects
