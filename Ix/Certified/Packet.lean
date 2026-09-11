/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Bytes
import Ix.Aiur.Semantics.BytecodeFfi

/-!
Untrusted certificate packet producer for the C2 Aiur pilot. It reads source
declarations from the decoded input store and transports the exact proposed
rule witnesses. It does not run the semantic checker. All words are checked
before field conversion, and the VM independently checks the same bounds.
-/

namespace Ix.Certified.Packet

open Ix.Theory Ix.Theory.Certified Model

abbrev Emit := StateT (Array Nat) (Except String)

def nat (n : Nat) : Emit Unit := do
  if n ≥ 65536 then throw "certificate scalar exceeds the pilot bound"
  modify (·.push n)

def bool (b : Bool) : Emit Unit := nat (if b then 1 else 0)

def address (a : Address) : Emit Unit := do
  if a.hash.size != 32 then throw "certificate address is not 32 bytes"
  for byte in a.hash.data do nat byte.toNat

def ref : ConstRef Address → Emit Unit
  | .member a i => nat 0 *> address a *> nat i
  | .ctor a i j => nat 1 *> address a *> nat i *> nat j

def list (emit : α → Emit Unit) (xs : List α) : Emit Unit := do
  nat xs.length
  xs.forM emit

def condition : PropWhen → Emit Unit
  | .never => nat 0
  | .allZero xs _ => nat 1 *> list nat xs

def level : VLevel → Emit Unit
  | .zero => nat 0
  | .succ l => nat 1 *> level l
  | .max a b => nat 2 *> level a *> level b
  | .imax a b => nat 3 *> level a *> level b
  | .param i => nat 4 *> nat i

def expr : AExpr Address → Emit Unit
  | .sort l => nat 0 *> level l
  | .bvar i => nat 1 *> nat i
  | .const r ls => nat 2 *> ref r *> list level ls
  | .app f a => nat 3 *> expr f *> expr a
  | .lam p a b => nat 4 *> condition p *> expr a *> expr b
  | .forallE p a b => nat 5 *> condition p *> expr a *> expr b
  | .proj .. | .natLit .. => throw "unsupported expression in the C2 pilot"

def sourceExpr : VExpr Address → Emit Unit
  | .sort l => nat 0 *> level l
  | .bvar i => nat 1 *> nat i
  | .const r ls => nat 2 *> ref r *> list level ls
  | .app f a => nat 3 *> sourceExpr f *> sourceExpr a
  | .lam a b => nat 4 *> nat 0 *> sourceExpr a *> sourceExpr b
  | .forallE a b => nat 5 *> nat 0 *> sourceExpr a *> sourceExpr b
  | .proj .. | .natLit .. => throw "unsupported source expression in the C2 pilot"

mutual
def typing : TypingWitness Address → Emit Unit
  | .sort => nat 0
  | .bvar => nat 1
  | .const => nat 2
  | .app p d b wf wa =>
    nat 3 *> condition p *> expr d *> expr b *> typing wf *> typing wa
  | .lam ld lb b wd wb wt =>
    nat 4 *> level ld *> level lb *> expr b *> typing wd *> typing wb *> typing wt
  | .forallE ld lb wd wb => nat 5 *> level ld *> level lb *> typing wd *> typing wb
  | .fact .. | .natLit .. | .betaResult .. => throw "semantic facts require the expanded VM profile"
  | .conv b la we wa wc => nat 6 *> expr b *> level la *> typing we *> typing wa *> conversion wc

def conversion : ConversionWitness Address → Emit Unit
  | .refl => nat 0
  | .symm w => nat 1 *> conversion w
  | .trans c wl wr => nat 2 *> expr c *> conversion wl *> conversion wr
  | .app wf wa => nat 3 *> conversion wf *> conversion wa
  | .lam ld wd wa wb => nat 4 *> level ld *> typing wd *> conversion wa *> conversion wb
  | .forallE ld wd wa wb => nat 5 *> level ld *> typing wd *> conversion wa *> conversion wb
  | .beta t wl wa => nat 6 *> expr t *> typing wl *> typing wa
  | .eta b wf => nat 7 *> expr b *> typing wf
  | .proofIrrel a wt wa wb => nat 8 *> expr a *> typing wt *> typing wa *> typing wb
  | .delta => nat 9
  | .sort => nat 10
  | .proj .. | .natLiteral .. => throw "projection and literal conversions require the expanded VM profile"
  | .equation .. => throw "ordinary equations require the expanded VM profile"
end

def safety : Safety → Emit Unit
  | .safe => nat 0
  | .unsafe => nat 1
  | .partial => nat 2

def kind : Ix.Theory.DefKind → Emit Unit
  | .definition => nat 0
  | .theorem => nat 1
  | .opaque => nat 2

def source : Const Address → Emit Unit
  | .axiom n t s => nat 0 *> nat n *> sourceExpr t *> safety s
  | .defn n k t b s => nat 1 *> nat n *> kind k *> sourceExpr t *> sourceExpr b *> safety s
  | .induct n p i t cs s =>
    nat 2 *> nat n *> nat p *> nat i *> sourceExpr t *> nat cs.length *> safety s
  | .recursor n p i m b t rs k s =>
    nat 3 *> nat n *> nat p *> nat i *> nat m *> nat b *> sourceExpr t *>
      nat rs.length *> bool k *> safety s
  | .quot .. => nat 4

def lookup (input : ProofInput Address) (r : ConstRef Address) : Emit (Const Address) := do
  match input.store.lookup r with
  | none => throw "missing source declaration"
  | some declaration => pure declaration

def definition (input : ProofInput Address) (w : DefinitionWitness Address) : Emit Unit := do
  ref w.ref
  let declaration ← lookup input w.ref
  source declaration
  -- Reading only connects occurrence annotations to source syntax. All
  -- semantic rule checks still run in Aiur, including unsafe/kind rejection.
  let .defn n _ t b _ := declaration
    | throw "a definition packet requires a source body"
  let some t ← pure (readAnnotations? n 0 t w.typeAnnotations)
    | throw "cannot read the proposed type annotations"
  let some b ← pure (readAnnotations? n 0 b w.bodyAnnotations)
    | throw "cannot read the proposed body annotations"
  expr t.val
  expr b.val
  level w.typeLevel
  typing w.typeWitness
  typing w.bodyWitness

def emit (signature : PrimitiveSignature Address) (input : ProofInput Address)
    (w : ProofWitness Address) : Emit Unit := do
  if signature.natType.isSome then throw "natural primitives require the expanded VM profile"
  nat 1
  source (← lookup input signature.falseType)
  source (← lookup input signature.falseElim)
  list (fun declaration => match declaration with
    | .definition witness => definition input witness
    | .ordinary _ => throw "ordinary blocks require the expanded VM profile"
    | .standard _ => throw "standard axioms require the expanded VM profile"
    | .quotient _ => throw "quotients require the expanded VM profile"
    | .structure _ => throw "structures require the expanded VM profile"
    | .natural _ => throw "natural primitives require the expanded VM profile"
    | .modeled _ => throw "modeled blocks require the expanded VM profile") w.declarations
  nat input.universes
  sourceExpr input.proof
  sourceExpr input.proposition
  let some e ← pure (readAnnotations? input.universes 0 input.proof w.proofAnnotations)
    | throw "cannot read the proposed proof annotations"
  let some p ← pure (readAnnotations? input.universes 0 input.proposition w.propositionAnnotations)
    | throw "cannot read the proposed proposition annotations"
  expr e.val
  expr p.val
  typing w.proofWitness
  typing w.propositionWitness

def words (signature : PrimitiveSignature Address) (input : ProofInput Address)
    (w : ProofWitness Address) : Except String (Array Nat) := do
  let (_, result) ← emit signature input w #[]
  if result.size ≥ 65536 then throw "certificate packet exceeds the pilot bound"
  return result

def args (signature : PrimitiveSignature Address) : Except String (Array Aiur.G) := do
  if signature.natType.isSome then throw "natural primitives require the expanded VM profile"
  let .member f i := signature.falseType | throw "False must be a block member"
  let .member e j := signature.falseElim | throw "False.elim must be a block member"
  if f.hash.size != 32 || e.hash.size != 32 || i ≥ 65536 || j ≥ 65536 then
    throw "primitive signature exceeds the pilot bounds"
  return (f.hash.data.map (.ofNat ∘ UInt8.toNat)).push (.ofNat i) ++
    (e.hash.data.map (.ofNat ∘ UInt8.toNat)).push (.ofNat j)

def ioBuffer (words : Array Nat) : Aiur.IOBuffer :=
  (default : Aiur.IOBuffer).extend 17 #[0] (words.map Aiur.G.ofNat)

end Ix.Certified.Packet
