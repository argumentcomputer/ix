/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Corpus
import Ix.Certified.Packet
import Ix.IxVM.Certified.Accept
import Ix.Aiur.Interpret
import Ix.Aiur.Semantics.SourceEval

namespace Ix.Certified.VmTests

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model

structure Input where
  prepared : PreparedInput
  witness : ProofWitness Address
  words : Array Nat
  args : Array Aiur.G

def fromCase (c : Corpus.Case) : Except String Input := do
  let some prepared := prepare? 300 Fixtures.profile c.target c.blobs
    | throw "serialized preparation declined"
  let some witness := Ix.Theory.Certificate.proofWitness? 300 prepared.signature prepared.input
    | throw "witness construction declined"
  return ⟨prepared, witness, ← Packet.words prepared.signature prepared.input witness,
    ← Packet.args prepared.signature⟩

def asValues (args : Array Aiur.G) : List Aiur.Value :=
  [.array (args.extract 0 32 |>.map .field), .field (args[32]?.getD 0),
   .array (args.extract 33 65 |>.map .field), .field (args[65]?.getD 0)]

def emitWords (emit : Packet.Emit Unit) : Except String (Array Nat) := do
  return (← emit #[]).2

def prelude (i : Input) : Packet.Emit Unit := do
  Packet.nat 1
  Packet.source (← Packet.lookup i.prepared.input i.prepared.signature.falseType)
  Packet.source (← Packet.lookup i.prepared.input i.prepared.signature.falseElim)

def changes (i : Input) : Except String (List (String × Array Nat)) := do
  let some (.definition definition) := i.witness.declarations.head?
    | throw "test requires one admitted definition"
  let source ← match i.prepared.input.store.lookup definition.ref with
    | some s => pure s | none => throw "source missing"
  let .defn n kind typ body _ := source | throw "test requires a definition"
  let sourcePrefix ← emitWords do
    prelude i
    Packet.nat i.witness.declarations.length
    Packet.ref definition.ref
  let original ← emitWords (Packet.source source)
  let replaceSource := fun (source : Const Address) => do
    let replacement ← emitWords (Packet.source source)
    return sourcePrefix ++ replacement ++ i.words.extract (sourcePrefix.size + original.size) i.words.size
  let prefixPrelude ← emitWords (prelude i)
  let wrongAnnotations := { definition with bodyAnnotations :=
    match definition.bodyAnnotations with
    | .lam _ domain body => .lam none domain body
    | other => other }
  let badAnnotationWitness := { i.witness with declarations := [.definition wrongAnnotations] }
  let badRuleWitness := { i.witness with declarations :=
    [.definition { definition with bodyWitness := .sort }] }
  let changedStatement : ProofInput Address := { i.prepared.input with proposition :=
    (VExpr.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.bvar 1))) }
  return [
    ("trailing-word", i.words.push 0),
    ("truncated-packet", i.words.extract 0 (i.words.size - 1)),
    ("unknown-packet-version", i.words.set! 0 2),
    ("out-of-range-scalar", i.words.set! 0 65536),
    ("primitive-universe-arity", i.words.set! 2 1),
    ("primitive-K-flag", i.words.set! (prefixPrelude.size - 2) 1),
    ("axiom-in-admission", ← replaceSource (Const.axiom n typ .safe)),
    ("unsafe-in-admission", ← replaceSource (.defn n kind typ body .«unsafe»)),
    ("partial-in-admission", ← replaceSource (.defn n kind typ body .«partial»)),
    ("changed-source-body", ← replaceSource (.defn n kind typ (.sort .zero) .safe)),
    ("wrong-annotation", ← Packet.words i.prepared.signature i.prepared.input badAnnotationWitness),
    ("wrong-typing-rule", ← Packet.words i.prepared.signature i.prepared.input badRuleWitness),
    ("missing-declaration", ← Packet.words i.prepared.signature i.prepared.input
      { i.witness with declarations := [] }),
    ("duplicate-declaration", ← Packet.words i.prepared.signature i.prepared.input
      { i.witness with declarations := i.witness.declarations ++ i.witness.declarations }),
    ("changed-original-statement", ← Packet.words i.prepared.signature changedStatement i.witness)
  ]

def run : IO Unit := do
  let compiled ← IO.ofExcept IxVM.Certified.compiled
  let some function := compiled.getFuncIdx `c_accept | throw (IO.userError "entrypoint missing")
  let vm ← IO.ofExcept (IxVM.Certified.toplevel.mapError toString)
  let decls ← IO.ofExcept (vm.mkDecls.mapError toString)
  for c in Corpus.positive do
    let input ← IO.ofExcept (fromCase c)
    let io := Packet.ioBuffer input.words
    let (output, _, _) ← IO.ofExcept (compiled.bytecode.execute function input.args io)
    unless output == #[1] do throw (IO.userError s!"native declined {c.name}")
    let (result, state) := Aiur.runFunction decls ⟨`c_accept⟩ (asValues input.args) io
    match result with
    | .ok (.field value) =>
      unless value == 1 do throw (IO.userError s!"interpreter declined {c.name}")
    | .ok _ => throw (IO.userError s!"interpreter result shape changed for {c.name}")
    | .error error => throw (IO.userError (error.ppDeref state.store 4 3))
    -- A source-evaluator check on each conversion-using case keeps a
    -- second executable semantics in the differential corpus.
    if c.name == "identity" || c.name == "beta-statement" || c.name == "eta-statement" then
      match Aiur.Source.Eval.runFunction decls ⟨`c_accept⟩ (asValues input.args) io 5000 with
      | .ok (.field value, _) =>
        unless value == 1 do throw (IO.userError s!"source evaluator declined {c.name}")
      | .ok _ => throw (IO.userError s!"source result shape changed for {c.name}")
      | .error error => throw (IO.userError s!"source evaluator: {repr error}")
    IO.println s!"PASS {c.name}: native/interpreter agreement"
  let input ← IO.ofExcept (fromCase (Corpus.one "identity" Fixtures.identity))
  let negative ← IO.ofExcept (changes input)
  for (name, words) in negative do
    match compiled.bytecode.execute function input.args (Packet.ioBuffer words) with
    | .error _ => IO.println s!"PASS {name}: native rejection"
    | .ok _ => throw (IO.userError s!"native accepted malformed certificate: {name}")
  -- Public address coordinates must be bytes, even before any private
  -- source/certificate data is used.
  match compiled.bytecode.execute function (input.args.set! 0 256) (Packet.ioBuffer input.words) with
  | .error _ => IO.println "PASS public-address-range: native rejection"
  | .ok _ => throw (IO.userError "native accepted a non-byte public address coordinate")
  for c in Corpus.declined do
    if acceptsSerialized.{0} 300 Fixtures.profile c.target c.blobs input.witness then
      throw (IO.userError s!"serialized boundary accepted excluded syntax: {c.name}")
    unless (prepare? 300 Fixtures.profile c.target c.blobs).isNone do
      throw (IO.userError s!"profile exclusion changed: {c.name}")
    IO.println s!"DECLINE {c.name}: serialized profile exclusion"
  IO.println <| (Lean.Json.mkObj [
    ("accepted", Lean.toJson Corpus.positive.length),
    ("declined", Lean.toJson Corpus.declined.length),
    ("vmRejected", Lean.toJson (negative.length + 1)),
    ("unexpectedErrors", Lean.toJson (0 : Nat))]).compress

end Ix.Certified.VmTests

def main : IO Unit := Ix.Certified.VmTests.run
