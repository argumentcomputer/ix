/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Corpus
import Tests.Theory.OrdinaryAcceptance

/-! Actual canonical Ixon bytes for ordinary source blocks and closed proofs.
The serializer is test infrastructure. Witness generation receives only the
decoded store and original target, and the serialized acceptance gate reruns
all independent checks. -/

namespace Tests.Certified.Ordinary

open Ix.Theory Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certified.Ordinary
open Ix.Certified Ix.Certified.Fixtures
open Tests.Theory.OrdinaryAcceptance
open Lean (toJson)

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

local instance : DecidableEq Address := Ix.Certified.addressDecidableEq

structure Tables where
  refs : Array Address := #[]
  univs : Array Ixon.Univ := #[]

abbrev Write := StateT Tables Option

def univ : VLevel → Ixon.Univ
  | .zero => .zero
  | .succ u => .succ (univ u)
  | .max u v => .max (univ u) (univ v)
  | .imax u v => .imax (univ u) (univ v)
  | .param i => .var i.toUInt64

def level (u : VLevel) : Write UInt64 := do
  let s ← get
  set { s with univs := s.univs.push (univ u) }
  return s.univs.size.toUInt64

def address (a : Address) : Write UInt64 := do
  let s ← get
  set { s with refs := s.refs.push a }
  return s.refs.size.toUInt64

def expression (self : Nat) (resolve : ConstRef Nat → Option Address) :
    VExpr Nat → Write Ixon.Expr
  | .sort u => return .sort (← level u)
  | .bvar i => return .var i.toUInt64
  | .const r us => do
    let us ← us.mapM level
    match r with
    | .member block member =>
      if block = self then return .recur member.toUInt64 us.toArray
      else return .ref (← address (← resolve r)) us.toArray
    | .ctor .. => return .ref (← address (← resolve r)) us.toArray
  | .app f a => return .app (← expression self resolve f) (← expression self resolve a)
  | .lam A b => return .leanLam (← expression self resolve A) (← expression self resolve b)
  | .forallE A B => return .leanAll (← expression self resolve A) (← expression self resolve B)
  | .proj .. | .natLit .. => failure

def constructor (self : Nat) (resolve : ConstRef Nat → Option Address)
    (ctor : Ctor Nat) (index : Nat) : Write Ixon.Constructor := do
  return {
    isUnsafe := ctor.safety != .safe, lvls := ctor.uvars.toUInt64,
    cidx := index.toUInt64, params := ctor.nparams.toUInt64, fields := ctor.nfields.toUInt64,
    typ := ← expression self resolve ctor.type }

def constantInfo (self : Nat) (resolve : ConstRef Nat → Option Address) :
    Const Nat → Write Ixon.ConstantInfo
  | .induct n p i type ctors safety => do
    let typ ← expression self resolve type
    let ctors ← ctors.zipIdx.mapM fun (ctor, index) => constructor self resolve ctor index
    return .muts #[.indc {
      isUnsafe := safety != .safe,
      lvls := n.toUInt64, params := p.toUInt64, indices := i.toUInt64, typ, ctors := ctors.toArray }]
  | .recursor n p i m b type rules k safety => do
    let typ ← expression self resolve type
    let rules ← rules.mapM fun rule => do
      return ({
        fields := rule.nfields.toUInt64,
        rhs := ← expression self resolve rule.rhs } : Ixon.RecursorRule)
    return .recr {
      k, isUnsafe := safety != .safe, lvls := n.toUInt64,
      params := p.toUInt64, indices := i.toUInt64, motives := m.toUInt64,
      minors := b.toUInt64, typ, rules := rules.toArray }
  | .defn n _ type body .safe => do
    return .defn {
      kind := .thm, safety := .safe, lvls := n.toUInt64,
      typ := ← expression self resolve type, value := ← expression self resolve body }
  | _ => failure

def constant (self : Nat) (resolve : ConstRef Nat → Option Address) (source : Const Nat) :
    Option Ixon.Constant := do
  let (info, tables) ← constantInfo self resolve source {}
  return ⟨info, #[], tables.refs, tables.univs⟩

structure Case extends Corpus.Case where
  source : Address
  recursor : Address
  mode : Inductive.ElimMode

def make? (name : String) (shape : Shape Nat) (mode : Inductive.ElimMode)
    (body proposition : AExpr Nat) (mutateRec : Const Nat → Const Nat := id)
    (mutateFamily : Ixon.Constant → Ixon.Constant := id) : Option Case := do
  let family := mutateFamily (← constant 100 (fun _ => none) (shape.source 100))
  let source := encode family
  let projection := encode ⟨.iPrj ⟨0, source.1⟩, #[], #[], #[]⟩
  let ctors := (List.range shape.constructors.length).map fun index =>
    encode ⟨.cPrj ⟨0, index.toUInt64, source.1⟩, #[], #[], #[]⟩
  let resolve := fun r => match r with
    | .member 100 0 => some projection.1
    | .ctor 100 0 index => (ctors[index]?).map Prod.fst
    | _ => none
  let recursor ← constant 101 resolve (mutateRec (shape.recursorSource 100 101 mode))
  let recursor := encode recursor
  let resolve := fun r => if r = .member 101 0 then some recursor.1 else resolve r
  let target ← constant 200 resolve (.defn 0 .theorem proposition.erase body.erase .safe)
  let target := encode target
  return {
    name, target := target.1,
    blobs := prelude ++ [source, projection] ++ ctors ++ [recursor, target],
    source := source.1, recursor := recursor.1, mode }

def acceptedCase (c : Case) : Bool :=
  match prepare? 2000 profile c.target c.blobs with
  | none => false
  | some prepared => (Ix.Theory.Certificate.proofWitness? 2000 prepared.signature prepared.input).any
      (acceptsSerialized.{0} 2000 profile c.target c.blobs)

def positive : List (Option Case) := [
  make? "Nat-iota" Tests.Theory.Ordinary.natShape .large identity (proposition natComputed),
  make? "List-distinct-universes" Tests.Theory.Ordinary.listShape .large identity (proposition listComputed),
  make? "indexed-iota" Tests.Theory.Ordinary.indexedShape .large identity (proposition indexedComputed),
  make? "function-field-iota" functionalShape .large identity (proposition functionalComputed),
  make? "multiple-Prop-small" Tests.Theory.Ordinary.manyProp .small smallProof identityType
]

#guard positive.length = 5
#guard positive.all (fun c => c.any acceptedCase)

def corruptRule : Const Nat → Const Nat
  | .recursor n p i m b type (_ :: rules) k safety =>
    .recursor n p i m b type (⟨0, .sort .zero⟩ :: rules) k safety
  | other => other

def unsafeRecursor : Const Nat → Const Nat
  | .recursor n p i m b type rules k _ => .recursor n p i m b type rules k .unsafe
  | other => other

def enableK : Const Nat → Const Nat
  | .recursor n p i m b type rules _ safety => .recursor n p i m b type rules true safety
  | other => other

def replaceBlock (store : Store Address) (address : Address) (block : Block Address) : Store Address where
  dom := store.dom
  nodup := store.nodup
  blocks a := (store.blocks a).map fun old => if a = address then block else old
  mem_dom a := by simp [store.mem_dom]

/-- Construct a valid certificate with the original canonical recursor at the
new address, then submit it against the authenticated altered source. This
tests the acceptance boundary independently of producer refusal. -/
def rejectsWithValidWitness (c : Case) : Bool := Id.run do
  let some prepared := prepare? 2000 profile c.target c.blobs | return false
  let some raw := prepared.input.store.lookup (.member c.source 0) | return false
  let some shape := Ix.Theory.Certificate.Ordinary.description? 2000
    prepared.signature.environment c.source raw | return false
  let repaired := replaceBlock prepared.input.store c.recursor
    ⟨[shape.recursorSource c.source c.recursor c.mode]⟩
  let input := { prepared.input with store := repaired }
  let some witness := Ix.Theory.Certificate.proofWitness? 2000 prepared.signature input | return false
  return acceptsCertified.{0,0} 2000 prepared.signature input witness &&
    !acceptsSerialized.{0} 2000 profile c.target c.blobs witness

#guard [corruptRule, unsafeRecursor, enableK].all fun mutation =>
  (make? "forged-recursor" Tests.Theory.Ordinary.natShape .large identity
    (proposition natComputed) mutation).any rejectsWithValidWitness

def wrongPosition (source : Ixon.Constant) : Ixon.Constant :=
  match source.info with
  | .muts #[.indc family] => { source with info := .muts #[.indc
      { family with ctors := family.ctors.map fun ctor => { ctor with cidx := ctor.cidx + 1 } }] }
  | _ => source

#guard (make? "wrong-constructor-position" Tests.Theory.Ordinary.natShape .large identity
  (proposition natComputed) id wrongPosition).any fun c =>
    (prepare? 2000 profile c.target c.blobs).isNone

def writeCase (directory : System.FilePath) (c : Case) : IO Unit := do
  let directory := directory / c.name
  IO.FS.createDirAll directory
  for (address, bytes) in c.blobs do
    IO.FS.writeBinFile (directory / s!"{hexOfBytes address.hash}.ixon") bytes
  let metadata := Lean.Json.mkObj [
    ("target", toJson (hexOfBytes c.target.hash)),
    ("falseType", toJson (hexOfBytes profile.falseType.hash)),
    ("falseElim", toJson (hexOfBytes profile.falseElim.hash))]
  IO.FS.writeFile (directory / "target.json") (metadata.pretty ++ "\n")

def run (directory : Option System.FilePath) : IO Unit := do
  let mut accepted := 0
  for candidate in positive do
    let some c := candidate | throw (IO.userError "serialized fixture construction failed")
    unless acceptedCase c do throw (IO.userError s!"serialized acceptance failed: {c.name}")
    accepted := accepted + 1
    if let some directory := directory then writeCase directory c
  let mut rejected := 0
  for (name, mutation) in [("changed-rule", corruptRule), ("unsafe-recursor", unsafeRecursor),
      ("unsupported-K", enableK)] do
    let some c := make? name Tests.Theory.Ordinary.natShape .large identity
      (proposition natComputed) mutation | throw (IO.userError "malformed fixture construction failed")
    unless rejectsWithValidWitness c do throw (IO.userError s!"malformed source accepted: {name}")
    rejected := rejected + 1
    if let some directory := directory then writeCase directory c
  let some wrong := make? "wrong-constructor-position" Tests.Theory.Ordinary.natShape .large identity
    (proposition natComputed) id wrongPosition | throw (IO.userError "position fixture construction failed")
  unless (prepare? 2000 profile wrong.target wrong.blobs).isNone do
    throw (IO.userError "wrong constructor position accepted")
  if let some directory := directory then writeCase directory wrong
  IO.println <| (Lean.Json.mkObj [
    ("serializedAccepted", toJson accepted), ("serializedRejected", toJson rejected),
    ("ingressRejected", toJson (1 : Nat)),
    ("unexpectedErrors", toJson (0 : Nat))]).compress

end Tests.Certified.Ordinary

def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "usage: certified-ordinary-tests [OUTPUT_DIRECTORY]"
    return 2
  Tests.Certified.Ordinary.run (args.head?.map System.FilePath.mk)
  return 0
