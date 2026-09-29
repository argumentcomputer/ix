/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Egress
import Tests.Ix.Kernel.Ingress

open Ix.Kernel Ix.Kernel.Egress
open Tests.Ix.Kernel.Ingress

namespace Tests.Ix.Kernel.Egress

/-- Serialization fixtures need not be well typed: admission is a separate
operation. Compare the complete constants, including unused layout slots. -/
def roundtrips (inputs : Ingress.Constants) (blobs : Ingress.Blobs := [])
    (family : Option (ConstRef Address) := none) : Bool :=
  match readRecords inputs blobs family 100 inputs with
  | .error _ => false
  | .ok records => match writeRecords inputs blobs family 100 records with
    | .error _ => false
    | .ok output => output == inputs

def exprRoundtrips (context : Ingress.Context) (source : Ixon.Expr) : Bool :=
  match Ingress.readExpr context 100 source with
  | .error _ => false
  | .ok raw => match writeExpr context 100 (.ofExpr source) raw with
    | .error _ => false
    | .ok output => output == source

def isMalformed : Search α → Bool
  | .error (.malformed _) => true
  | _ => false

#guard roundtrips []
#guard roundtrips [(address 1, identity), (address 2, aliasIdentity)]
#guard roundtrips [(address 1, sharedIdentity)]
#guard roundtrips falseStore
#guard roundtrips separatedFalse
#guard roundtrips separatedFalse.reverse

def variedBlock : Ixon.Constant :=
  ⟨.muts #[
    .defn ⟨.opaq, .part, 2, .sort 2,
      .letE (.lean true) (.sort 0) (.ref 1 #[2, 1]) (.var 0)⟩,
    .indc ⟨true, 3, 4, 5, .sort 0, #[⟨true, 6, 0, 7, 8, .recur 1 #[]⟩]⟩,
    .recr ⟨true, true, 9, 10, 11, 12, 13, .sort 1,
      #[⟨14, .share 1⟩, ⟨15, .var 0⟩]⟩],
    #[.var 2, .share 0, .var 99], #[address 1, address 1, address 99],
    #[.zero, .var 0, .zero, .max (.var 0) (.var 1)]⟩

def variants : Ingress.Constants :=
  [(address 1, identity), (address 12, variedBlock),
   (address 13, ⟨.dPrj ⟨0, address 12⟩, #[], #[], #[]⟩),
   (address 14, ⟨.iPrj ⟨1, address 12⟩, #[], #[], #[]⟩),
   (address 15, ⟨.cPrj ⟨1, 0, address 12⟩, #[], #[], #[]⟩),
   (address 16, ⟨.rPrj ⟨2, address 12⟩, #[], #[], #[]⟩),
   (address 17, ⟨.axio ⟨true, 18446744073709551615, .sort 0⟩, #[], #[], #[.zero]⟩)]

#guard roundtrips variants
#guard [Ix.DefKind.defn, .opaq, .thm].all fun kind =>
  [Ix.DefinitionSafety.safe, .unsaf, .part].all fun safety =>
    roundtrips [(address 1, { identity with info := .defn ⟨kind, safety, 1, idType, idBody⟩ })]
#guard [Ix.QuotKind.type, .ctor, .lift, .ind].all fun kind =>
  roundtrips [(address 1, ⟨.quot ⟨kind, 2, .sort 0⟩, #[], #[], #[.var 1]⟩)]

#guard exprRoundtrips (ctx) (.var 18446744073709551615)
#guard exprRoundtrips (ctx) (.letE (.lean false) (.sort 0) (.var 0) (.var 1))
#guard exprRoundtrips (ctx) (.letE (.lean true) (.sort 0) (.var 0) (.var 1))
-- Ixon v3 let contracts are erased by the reading and retained by the layout.
#guard exprRoundtrips (ctx) (.letE (.borrow true .linear) (.sort 0) (.var 0) (.var 1))
#guard exprRoundtrips (ctx) (.letE { nonDep := false, binder := .affine } (.sort 0) (.var 0) (.var 1))
#guard exprRoundtrips (ctx sharedIdentity) (.share 2)
#guard exprRoundtrips (ctx aliasIdentity) (.prj 0 18446744073709551615 (.var 0))
#guard exprRoundtrips literalContext (.nat 0)
#guard exprRoundtrips { literalContext with blobs := [(address 9, ⟨#[0, 0]⟩)] } (.nat 0)

-- A retained table slot or sharing node must not hide changed raw payloads.
#guard isMalformed (writeExpr (ctx) 100 (.sort 0) (.sort .zero))
#guard isMalformed (writeExpr (ctx aliasIdentity) 100 (.ref 0 #[0])
  (.const (.member (address 2) 0) [.param 0]))
#guard isMalformed (writeExpr (ctx falseBlock) 100 (.recur 0 #[])
  (.const (.member (address 1) 1) []))
#guard isMalformed (writeExpr (ctx sharedIdentity) 100 (.share 2) (.bvar 0))
#guard isMalformed (writeExpr literalContext 100 (.nat 0)
  (.natLit (.member (address 3) 0) 66052))
#guard isMalformed (writeExpr literalContext 100 (.nat 0)
  (.natLit (.member (address 4) 0) 66051))
#guard isMalformed (writeExpr (ctx aliasIdentity) 100 (.prj 0 .var)
  (.proj (.member (address 2) 0) 0 (.bvar 0)))

-- Index/metadata narrowing and shape/count mismatches fail explicitly.
#guard word 18446744073709551615 == some 18446744073709551615
#guard word 18446744073709551616 == none
#guard isMalformed (writeExpr (ctx) 100 .var (.bvar 18446744073709551616))
#guard isMalformed (writeExpr (ctx aliasIdentity) 100 (.prj 0 .var)
  (.proj (.member (address 1) 0) 18446744073709551616 (.bvar 0)))
#guard isMalformed (writeBlock (ctx) 100 (.ofConstant identity)
  ⟨[.defn 18446744073709551616 .definition (.bvar 0) (.bvar 0) .safe]⟩)
#guard isMalformed (writeBlock (ctx) 100 (.ofConstant identity) ⟨[]⟩)
#guard isMalformed (writeBlock (ctx variedBlock) 100 (.ofConstant variedBlock) ⟨[]⟩)
#guard isMalformed (writeBlock (ctx falseBlock) 100 (.ofConstant falseBlock)
  ⟨[.induct 0 0 0 (.sort .zero) [⟨0, 0, 0, .sort .zero, .safe⟩] .safe,
    .recursor 0 0 0 0 0 (.sort .zero) [] false .safe]⟩)
#guard isMalformed (writeBlock (ctx falseBlock) 100 (.ofConstant falseBlock)
  ⟨[.induct 0 0 0 (.sort .zero) [] .safe,
    .recursor 0 0 0 0 0 (.sort .zero) [⟨0, .bvar 0⟩] false .safe]⟩)
#guard isMalformed (writeProjection .constructor (.member (address 3) 0))
#guard isMalformed (writeProjection .definition (.member (address 3) 18446744073709551616))
#guard isMalformed (writeProjection .constructor (.ctor (address 3) 0 18446744073709551616))

-- Projections must have empty tables and identify a matching stored member.
#guard isMalformed (readProjection { falseProjection with refs := #[address 3] })
#guard isMalformed (readRecord ⟨falseStore, [], address 4,
  { falseProjection with info := .rPrj ⟨0, address 3⟩ }, none⟩ 100)
#guard isMalformed (readRecord ⟨[], [], address 4, falseProjection, none⟩ 100)
#guard isMalformed (Ingress.readDeclarationsC falseStore [] none 100
  [(address 4, { falseProjection with info := .rPrj ⟨0, address 3⟩ })])
#guard isMalformed (writeRecord ⟨falseStore, [], address 5, identity, none⟩ 100
  (.projection .recursor (.member (address 3) 0)))

-- The proof applies to the actual public list operations, at the same fuel.
example {inputs : Ingress.Constants} {records : List (Address × Record)}
    (h : readRecords inputs [] none 100 inputs = .ok records) :
    writeRecords inputs [] none 100 records = .ok inputs := records_roundtrip h

end Tests.Ix.Kernel.Egress
