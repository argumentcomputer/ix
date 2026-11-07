import IxCK.Ixon.Codec
import IxCC.Ixon.V3.Const

/-!
# Ix's Ixon data and ours

Ixon v4 changed the wire (TagN integers, canonical sharing) and kept the
data model that Ixon v3 introduced: the same universes, expressions,
contracts and constants. The bytes are read and written by ix's pure codec
(`IxCK.Ixon.Codec`, ix's `IxCK` package at the pinned revision);
everything downstream of ingress (`V3.Tc`, `Src.Ingress`, the resource
checker) keeps our own copy of the data types, so no ix type reaches `Src`
or the recheck path.

This module is the total structural correspondence between the two copies.
`ofIx` direction: the only partiality is an address whose byte string is not
32 bytes long (ix's `Address` carries no length invariant; its decoder always
reads 32 bytes). `toIx` is total. Ix's names are written with `_root_` because
`Ixon.*` inside our namespace means `IxCC.Ixon.*`.
-/

namespace IxCC.Ixon.V4

open IxCC.Ixon

abbrev IxAddress := _root_.Address
abbrev IxUniv := _root_.Ixon.Univ
abbrev IxExpr := _root_.Ixon.Expr
abbrev IxConstant := _root_.Ixon.Constant

/-! ## Addresses -/

def addressOfIx (a : IxAddress) : Except String Address :=
  match Address.ofBytes? a.hash with
  | some address => .ok address
  | none => .error s!"ixon-v4: address of {a.hash.size} bytes"

def addressToIx (a : Address) : IxAddress := ⟨a.hash⟩

/-! ## Declaration tags and contracts -/

def defKindOfIx : _root_.Ix.DefKind → DefKind
  | .defn => .defn
  | .opaq => .opaq
  | .thm => .thm

def defKindToIx : DefKind → _root_.Ix.DefKind
  | .defn => .defn
  | .opaq => .opaq
  | .thm => .thm

def safetyOfIx : _root_.Ix.DefinitionSafety → DefinitionSafety
  | .unsaf => .unsaf
  | .safe => .safe
  | .part => .part

def safetyToIx : DefinitionSafety → _root_.Ix.DefinitionSafety
  | .unsaf => .unsaf
  | .safe => .safe
  | .part => .part

def quotKindOfIx : _root_.Ix.QuotKind → QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def quotKindToIx : QuotKind → _root_.Ix.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def usesOfIx : _root_.Ixon.Uses → Uses
  | .erased => .erased
  | .linear => .linear
  | .affine => .affine
  | .many => .many

def usesToIx : Uses → _root_.Ixon.Uses
  | .erased => .erased
  | .linear => .linear
  | .affine => .affine
  | .many => .many

def ownedOfIx : _root_.Ixon.Owned → Owned
  | .unique => .unique
  | .shared => .shared

def ownedToIx : Owned → _root_.Ixon.Owned
  | .unique => .unique
  | .shared => .shared

def localityOfIx : _root_.Ixon.Locality → V3.Locality
  | .unrestricted => .unrestricted
  | .local => .local

def localityToIx : V3.Locality → _root_.Ixon.Locality
  | .unrestricted => .unrestricted
  | .local => .local

def valueOfIx (v : _root_.Ixon.ValueContract) : V3.ValueContract :=
  ⟨ownedOfIx v.owned, localityOfIx v.locality⟩

def valueToIx (v : V3.ValueContract) : _root_.Ixon.ValueContract :=
  ⟨ownedToIx v.owned, localityToIx v.locality⟩

def binderOfIx (b : _root_.Ixon.BinderContract) : V3.BinderContract :=
  ⟨usesOfIx b.uses, valueOfIx b.value⟩

def binderToIx (b : V3.BinderContract) : _root_.Ixon.BinderContract :=
  ⟨usesToIx b.uses, valueToIx b.value⟩

def letKindOfIx : _root_.Ixon.LetKind → V3.LetKind
  | .value => .value
  | .borrowShared => .borrowShared

def letKindToIx : V3.LetKind → _root_.Ixon.LetKind
  | .value => .value
  | .borrowShared => .borrowShared

def letOfIx (c : _root_.Ixon.LetContract) : V3.LetContract :=
  ⟨c.nonDep, letKindOfIx c.kind, binderOfIx c.binder⟩

def letToIx (c : V3.LetContract) : _root_.Ixon.LetContract :=
  ⟨c.nonDep, letKindToIx c.kind, binderToIx c.binder⟩

/-! ## Universes and expressions -/

def univOfIx : IxUniv → Univ
  | .zero => .zero
  | .succ u => .succ (univOfIx u)
  | .max u v => .max (univOfIx u) (univOfIx v)
  | .imax u v => .imax (univOfIx u) (univOfIx v)
  | .var i => .var i

def univToIx : Univ → IxUniv
  | .zero => .zero
  | .succ u => .succ (univToIx u)
  | .max u v => .max (univToIx u) (univToIx v)
  | .imax u v => .imax (univToIx u) (univToIx v)
  | .var i => .var i

def exprOfIx : IxExpr → V3.Expr
  | .sort i => .sort i
  | .var i => .var i
  | .ref i levels => .ref i levels
  | .recur i levels => .recur i levels
  | .prj i field value => .prj i field (exprOfIx value)
  | .str i => .str i
  | .nat i => .nat i
  | .app f a => .app (exprOfIx f) (exprOfIx a)
  | .lam c t b => .lam (binderOfIx c) (exprOfIx t) (exprOfIx b)
  | .all c r t b => .all (binderOfIx c) (valueOfIx r) (exprOfIx t) (exprOfIx b)
  | .letE c t v b => .letE (letOfIx c) (exprOfIx t) (exprOfIx v) (exprOfIx b)
  | .share i => .share i

def exprToIx : V3.Expr → IxExpr
  | .sort i => .sort i
  | .var i => .var i
  | .ref i levels => .ref i levels
  | .recur i levels => .recur i levels
  | .prj i field value => .prj i field (exprToIx value)
  | .str i => .str i
  | .nat i => .nat i
  | .app f a => .app (exprToIx f) (exprToIx a)
  | .lam c t b => .lam (binderToIx c) (exprToIx t) (exprToIx b)
  | .all c r t b => .all (binderToIx c) (valueToIx r) (exprToIx t) (exprToIx b)
  | .letE c t v b => .letE (letToIx c) (exprToIx t) (exprToIx v) (exprToIx b)
  | .share i => .share i

/-! ## Constants -/

def definitionOfIx (d : _root_.Ixon.Definition) : V3.Definition :=
  ⟨defKindOfIx d.kind, safetyOfIx d.safety, d.lvls, exprOfIx d.typ, exprOfIx d.value⟩

def definitionToIx (d : V3.Definition) : _root_.Ixon.Definition :=
  ⟨defKindToIx d.kind, safetyToIx d.safety, d.lvls, exprToIx d.typ, exprToIx d.value⟩

def recursorOfIx (r : _root_.Ixon.Recursor) : V3.Recursor :=
  ⟨r.k, r.isUnsafe, r.lvls, r.params, r.indices, r.motives, r.minors, exprOfIx r.typ,
    r.rules.map fun rule => ⟨rule.fields, exprOfIx rule.rhs⟩⟩

def recursorToIx (r : V3.Recursor) : _root_.Ixon.Recursor :=
  ⟨r.k, r.isUnsafe, r.lvls, r.params, r.indices, r.motives, r.minors, exprToIx r.typ,
    r.rules.map fun rule => ⟨rule.fields, exprToIx rule.rhs⟩⟩

def constructorOfIx (c : _root_.Ixon.Constructor) : V3.Constructor :=
  ⟨c.isUnsafe, c.lvls, c.cidx, c.params, c.fields, exprOfIx c.typ⟩

def constructorToIx (c : V3.Constructor) : _root_.Ixon.Constructor :=
  ⟨c.isUnsafe, c.lvls, c.cidx, c.params, c.fields, exprToIx c.typ⟩

def inductiveOfIx (i : _root_.Ixon.Inductive) : V3.Inductive :=
  ⟨i.isUnsafe, i.lvls, i.params, i.indices, exprOfIx i.typ, i.ctors.map constructorOfIx⟩

def inductiveToIx (i : V3.Inductive) : _root_.Ixon.Inductive :=
  ⟨i.isUnsafe, i.lvls, i.params, i.indices, exprToIx i.typ, i.ctors.map constructorToIx⟩

def mutOfIx : _root_.Ixon.MutConst → V3.MutConst
  | .defn d => .defn (definitionOfIx d)
  | .indc i => .indc (inductiveOfIx i)
  | .recr r => .recr (recursorOfIx r)

def mutToIx : V3.MutConst → _root_.Ixon.MutConst
  | .defn d => .defn (definitionToIx d)
  | .indc i => .indc (inductiveToIx i)
  | .recr r => .recr (recursorToIx r)

def infoOfIx : _root_.Ixon.ConstantInfo → Except String V3.ConstantInfo
  | .defn d => .ok (.defn (definitionOfIx d))
  | .recr r => .ok (.recr (recursorOfIx r))
  | .axio a => .ok (.axio ⟨a.isUnsafe, a.lvls, exprOfIx a.typ⟩)
  | .quot q => .ok (.quot ⟨quotKindOfIx q.kind, q.lvls, exprOfIx q.typ⟩)
  | .cPrj p => return .cPrj ⟨p.idx, p.cidx, ← addressOfIx p.block⟩
  | .rPrj p => return .rPrj ⟨p.idx, ← addressOfIx p.block⟩
  | .iPrj p => return .iPrj ⟨p.idx, ← addressOfIx p.block⟩
  | .dPrj p => return .dPrj ⟨p.idx, ← addressOfIx p.block⟩
  | .muts ms => .ok (.muts (ms.map mutOfIx))

def infoToIx : V3.ConstantInfo → _root_.Ixon.ConstantInfo
  | .defn d => .defn (definitionToIx d)
  | .recr r => .recr (recursorToIx r)
  | .axio a => .axio ⟨a.isUnsafe, a.lvls, exprToIx a.typ⟩
  | .quot q => .quot ⟨quotKindToIx q.kind, q.lvls, exprToIx q.typ⟩
  | .cPrj p => .cPrj ⟨p.idx, p.cidx, addressToIx p.block⟩
  | .rPrj p => .rPrj ⟨p.idx, addressToIx p.block⟩
  | .iPrj p => .iPrj ⟨p.idx, addressToIx p.block⟩
  | .dPrj p => .dPrj ⟨p.idx, addressToIx p.block⟩
  | .muts ms => .muts (ms.map mutToIx)

def constantOfIx (c : IxConstant) : Except String V3.Constant := do
  return ⟨← infoOfIx c.info, c.sharing.map exprOfIx, ← c.refs.mapM addressOfIx,
    c.univs.map univOfIx⟩

def constantToIx (c : V3.Constant) : IxConstant :=
  ⟨infoToIx c.info, c.sharing.map exprToIx, c.refs.map addressToIx, c.univs.map univToIx⟩

end IxCC.Ixon.V4
