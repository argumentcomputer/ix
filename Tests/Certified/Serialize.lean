/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Fixtures

/-! Test-only serializer for singleton source stores. It preserves every
source kind and field, emits real content-addressed projection wrappers, and
places natural literal bytes in their separate authenticated blob domain. -/

namespace Tests.Certified.Serialize

open Ix.Theory Ix.Theory.Certified Ix.Certified Ix.Certified.Fixtures

structure Tables where
  refs : Array Address := #[]
  univs : Array Ixon.Univ := #[]
  literals : ConstantBlobs := []

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
  | .proj r i s => return .prj (← address (← resolve r)) i.toUInt64 (← expression self resolve s)
  | .natLit n => do
    let bytes := ByteArray.mk n.toBytesLE
    let a := Address.blake3 bytes
    modify fun s => { s with literals := s.literals ++ [(a, bytes)] }
    return .nat (← address a)

def safety : Safety → Ix.DefinitionSafety
  | .safe => .safe
  | .unsafe => .unsaf
  | .partial => .part

def kind : Ix.Theory.DefKind → Ix.DefKind
  | .definition => .defn
  | .theorem => .thm
  | .opaque => .opaq

def quotKind : Ix.Theory.QuotKind → Ix.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def constantInfo (self : Nat) (resolve : ConstRef Nat → Option Address) :
    Const Nat → Write Ixon.ConstantInfo
  | .induct n p i type ctors s => do
    let typ ← expression self resolve type
    let ctors ← ctors.zipIdx.mapM fun (ctor, index) => do
      return ({
        isUnsafe := ctor.safety != .safe, lvls := ctor.uvars.toUInt64,
        cidx := index.toUInt64, params := ctor.nparams.toUInt64, fields := ctor.nfields.toUInt64,
        typ := ← expression self resolve ctor.type } : Ixon.Constructor)
    return .muts #[.indc {
      isUnsafe := s != .safe, lvls := n.toUInt64,
      params := p.toUInt64, indices := i.toUInt64, typ, ctors := ctors.toArray }]
  | .recursor n p i m b type rules k s => do
    let typ ← expression self resolve type
    let rules ← rules.mapM fun rule => do
      return ({
        fields := rule.nfields.toUInt64,
        rhs := ← expression self resolve rule.rhs } : Ixon.RecursorRule)
    return .recr {
      k, isUnsafe := s != .safe, lvls := n.toUInt64,
      params := p.toUInt64, indices := i.toUInt64, motives := m.toUInt64,
      minors := b.toUInt64, typ, rules := rules.toArray }
  | .defn n k type body s => do
    return .defn {
      kind := kind k, safety := safety s, lvls := n.toUInt64,
      typ := ← expression self resolve type, value := ← expression self resolve body }
  | .axiom n type s => do
    return .axio { isUnsafe := s != .safe, lvls := n.toUInt64, typ := ← expression self resolve type }
  | .quot k n type => do
    return .quot { kind := quotKind k, lvls := n.toUInt64, typ := ← expression self resolve type }

def constant (self : Nat) (resolve : ConstRef Nat → Option Address) (source : Const Nat) :
    Option (Ixon.Constant × ConstantBlobs) := do
  let (info, tables) ← constantInfo self resolve source {}
  return (⟨info, #[], tables.refs, tables.univs⟩, tables.literals)

structure Case where
  name : String
  profile : Profile
  target : Address
  blobs : ConstantBlobs
  literals : ConstantBlobs
  references : List (ConstRef Nat × Address)
  blocks : List (Nat × Address)

def reference (references : List (ConstRef Nat × Address)) (r : ConstRef Nat) : Option Address :=
  (references.find? fun (key, _) => key = r).map Prod.snd

def uniqueBlobs (blobs : ConstantBlobs) : ConstantBlobs :=
  blobs.foldl (fun acc entry => if (lookup acc entry.1).isSome then acc else acc ++ [entry]) []

/-- Source domains are supplied in dependency order. Each fixture must provide
all declarations; witness construction receives only the decoded result. -/
def make? (name : String) (signature : PrimitiveSignature Nat) (input : ProofInput Nat) :
    Option Case := do
  if signature.falseType != .member 10 0 || signature.falseElim != .member 11 0 || 900 ∈ input.store.dom then
    none
  else do
    let mut blobs := prelude
    let mut literals := []
    let mut references := [(.member 10 0, falseObject.1), (.member 11 0, falseElimObject.1)]
    let mut blocks := [(10, falseBlockObject.1), (11, falseElimObject.1)]
    for b in input.store.dom.filter (fun b => b != 10 && b != 11) do
      let source ← input.store.lookup (.member b 0)
      let (raw, extra) ← constant b (reference references) source
      let encoded := encode raw
      blobs := blobs ++ [encoded]
      literals := literals ++ extra
      blocks := blocks ++ [(b, encoded.1)]
      match source with
      | .induct _ _ _ _ ctors _ =>
        let projection := encode ⟨.iPrj ⟨0, encoded.1⟩, #[], #[], #[]⟩
        blobs := blobs ++ [projection]
        references := references ++ [(.member b 0, projection.1)]
        for i in List.range ctors.length do
          let ctor := encode ⟨.cPrj ⟨0, i.toUInt64, encoded.1⟩, #[], #[], #[]⟩
          blobs := blobs ++ [ctor]
          references := references ++ [(.ctor b 0 i, ctor.1)]
      | _ => references := references ++ [(.member b 0, encoded.1)]
    let (raw, extra) ← constant 900 (reference references)
      (.defn input.universes .theorem input.proposition input.proof .safe)
    let target := encode raw
    let natType ← match signature.natType with
      | none => some none
      | some r => (reference references r).map some
    return {
      name, profile := { profile with natType }, target := target.1,
      blobs := blobs ++ [target], literals := uniqueBlobs (literals ++ extra),
      references := references ++ [(.member 900 0, target.1)], blocks := blocks ++ [(900, target.1)] }

def renameConstant (mapping : Nat → Address) : Const Nat → Const Address
  | .axiom n type s => .axiom n (type.rename mapping) s
  | .defn n k type body s => .defn n k (type.rename mapping) (body.rename mapping) s
  | .quot k n type => .quot k n (type.rename mapping)
  | .induct n p i type ctors s => .induct n p i (type.rename mapping)
      (ctors.map fun c => ⟨c.uvars, c.nparams, c.nfields, c.type.rename mapping, c.safety⟩) s
  | .recursor n p i m b type rules k s => .recursor n p i m b (type.rename mapping)
      (rules.map fun r => ⟨r.nfields, r.rhs.rename mapping⟩) k s

/-- A control input with original declarations under the altered source's
addresses. It intentionally bypasses authentication only to obtain an
independently valid certificate to attack the real serialized gate. -/
def repaired? (c : Case) (original : ProofInput Nat) : Option PreparedInput := do
  let prepared ← prepare? 6400 c.profile c.target c.blobs c.literals
  let mapping := fun b => ((c.blocks.find? fun (key, _) => key = b).map Prod.snd).getD c.target
  let originals := c.blocks.map fun (b, a) => (a, (if b = 900 then
    some (Const.defn original.universes .theorem original.proposition original.proof .safe)
    else original.store.lookup (.member b 0)).map (fun source =>
      (⟨[renameConstant mapping source]⟩ : Block Address)))
  let old := prepared.input.store
  let store : Store Address := {
    dom := old.dom, nodup := old.nodup,
    blocks := fun a => (old.blocks a).map fun block => ((lookup originals a).join).getD block,
    mem_dom := by intro a; simp [old.mem_dom] }
  let target ← store.lookup (.member c.target 0)
  return { prepared with input := { prepared.input with store, proposition := target.type } }

end Tests.Certified.Serialize

namespace Tests.Certified.Serialize

open Ix.Theory Ix.Theory.Certified Ix.Certified Ix.Certified.Fixtures

/-- Rehash an entire fixture after changing one raw blob or constant. Every
reference and projection wrapper is updated in dependency order, so tests of
canonical encoding and field ownership do not merely fail at an old hash. -/
def rehash? (c : Case) (alterLiteral : ByteArray → ByteArray := id)
    (alterConstant : Address → Ixon.Constant → Ixon.Constant := fun _ source => source) : Option Case := do
  let mut changed : List (Address × Address) := []
  let mut literals := []
  for (a, bytes) in c.literals do
    let bytes := alterLiteral bytes
    let a' := Address.blake3 bytes
    changed := changed ++ [(a, a')]
    literals := literals ++ [(a', bytes)]
  let mut blobs := []
  for (a, bytes) in c.blobs do
    let source ← decodeObject? a bytes
    let rewrite := fun a => (lookup changed a).getD a
    let info := match source.val.info with
      | .iPrj p => .iPrj { p with block := rewrite p.block }
      | .rPrj p => .rPrj { p with block := rewrite p.block }
      | .dPrj p => .dPrj { p with block := rewrite p.block }
      | .cPrj p => .cPrj { p with block := rewrite p.block }
      | info => info
    let source := alterConstant a { source.val with info, refs := source.val.refs.map rewrite }
    let encoded := encode source
    changed := changed ++ [(a, encoded.1)]
    blobs := blobs ++ [encoded]
  let rewrite := fun a => (lookup changed a).getD a
  return { c with
    profile := {
      falseType := rewrite c.profile.falseType, falseElim := rewrite c.profile.falseElim,
      natType := c.profile.natType.map rewrite },
    target := rewrite c.target, blobs, literals,
    references := c.references.map fun (r, a) => (r, rewrite a),
    blocks := c.blocks.map fun (b, a) => (b, rewrite a) }

def mapLiterals (index : UInt64) : Ixon.Expr → Ixon.Expr
  | .nat _ => .nat index
  | .app f a => .app (mapLiterals index f) (mapLiterals index a)
  | .lam u A b => .lam u (mapLiterals index A) (mapLiterals index b)
  | .all u c A B => .all u c (mapLiterals index A) (mapLiterals index B)
  | .prj owner field value => .prj owner field (mapLiterals index value)
  | other => other

end Tests.Certified.Serialize
