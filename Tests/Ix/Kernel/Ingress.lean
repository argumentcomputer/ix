/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress

open Ix.Kernel
open Ix.Kernel.Ingress

namespace Tests.Ix.Kernel.Ingress

def address (tag : UInt8) : Address := ⟨⟨Array.replicate 32 tag⟩⟩

def idType : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
def idBody : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))

def identity : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 1, idType, idBody⟩, #[], #[], #[.var 0]⟩

def sharedIdentity : Ixon.Constant :=
  { identity with
    info := .defn ⟨.defn, .safe, 1, .share 0, .share 2⟩
    sharing := #[idType, idBody, .share 1] }

def aliasIdentity : Ixon.Constant :=
  { identity with
    info := .defn ⟨.defn, .safe, 1, idType, .ref 0 #[0]⟩
    refs := #[address 1] }

def accepts (constants : Constants) (blobs : Blobs := []) : Bool :=
  (checkEnv.{1} {} constants blobs).isOk

def rejected (constants : Constants) (blobs : Blobs := []) : Bool :=
  match checkEnv.{1} {} constants blobs with
  | .error (.rejected _) => true
  | _ => false

def declined (constants : Constants) : Bool :=
  match checkEnv.{1} {} constants [] with
  | .error (.declined _) => true
  | _ => false

def ctx (source : Ixon.Constant := identity) : Context :=
  context [(address 1, identity)] [] none none (address 1, source)

def malformed (context : Context) (input : Ixon.Expr) : Bool :=
  match readExpr context 100 input with
  | .error (.malformed _) => true
  | _ => false

def unsupported (input : Ixon.Expr) : Bool :=
  match readExpr (ctx) 100 input with
  | .error (.unsupported _) => true
  | _ => false

#guard accepts [(address 1, identity), (address 2, aliasIdentity)]
#guard accepts [(address 1, sharedIdentity)]
#guard rejected [(address 2, aliasIdentity), (address 1, identity)]
#guard rejected [(address 2, aliasIdentity)]
#guard rejected [(address 1, identity), (address 1, identity)]
#guard rejected [(address 1, identity)] [(address 9, ⟨#[]⟩), (address 9, ⟨#[1]⟩)]
#guard match readExpr (ctx) 0 idBody with | .error .exhausted => true | _ => false
#guard malformed (ctx) (.sort 1)
#guard malformed (ctx) (.sort 18446744073709551615)
#guard malformed (ctx) (.ref 0 #[])
#guard malformed (ctx aliasIdentity) (.ref 0 #[1])
#guard malformed (ctx) (.recur 1 #[])
#guard malformed (ctx) (.share 0)
#guard malformed (ctx { identity with sharing := #[.share 0] }) (.share 0)
#guard malformed (ctx { identity with sharing := #[.share 1, .var 0] }) (.share 0)
#guard match readExpr (ctx) 10 (.var 18446744073709551615) with
  | .ok value => value == .bvar 18446744073709551615
  | _ => false

#guard unsupported (.str 0)
-- Ixon v3 contracts are erased by the reading: every binder, result, and let
-- contract reads as the same kernel term.
def binderContracts : List Ixon.BinderContract :=
  (List.range 16).filterMap fun bits => Ixon.BinderContract.ofBits? bits.toUInt8
def valueContracts : List Ixon.ValueContract :=
  (List.range 4).filterMap fun bits => Ixon.ValueContract.ofBits? bits.toUInt8
#guard binderContracts.length == 16 && valueContracts.length == 4
def readsLike (input default : Ixon.Expr) : Bool :=
  match readExpr (ctx) 100 input, readExpr (ctx) 100 default with
  | .ok value, .ok expected => value == expected
  | _, _ => false
#guard binderContracts.all fun binder =>
  readsLike (.lam binder (.sort 0) (.var 0)) (.leanLam (.sort 0) (.var 0)) &&
  valueContracts.all fun result =>
    readsLike (.all binder result (.sort 0) (.var 0)) (.leanAll (.sort 0) (.var 0))
#guard (List.range 4).all fun flags => binderContracts.all fun binder =>
  match Ixon.LetContract.ofFlags? flags.toUInt64 binder with
  | none => false
  | some contract =>
    readsLike (.letE contract (.sort 0) (.sort 0) (.var 0))
      (.leanLet false (.sort 0) (.sort 0) (.var 0))
-- A definition whose body binds with a linear, unique, local contract is
-- checked by its erased typing, as upstream `Ix.Tc` does.
#guard accepts [(address 1, { identity with info := .defn ⟨.defn, .safe, 1, idType,
  .lam ⟨.linear, .localUnique⟩ (.sort 0) (.leanLam (.var 0) (.var 0))⟩ })]

/-- A no-constructor inductive and its large eliminator, encoded independently
of the kernel's shape generator. -/
def falseBlock : Ixon.Constant :=
  let falseType : Ixon.Expr := .recur 0 #[]
  let motive := Ixon.Expr.leanAll falseType (.sort 1)
  let recType := Ixon.Expr.leanAll motive
    (.leanAll falseType (.app (.var 1) (.var 0)))
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[]⟩,
    .recr ⟨false, false, 1, 0, 0, 1, 0, recType, #[]⟩], #[], #[], #[.zero, .var 0]⟩

def falseProjection : Ixon.Constant := ⟨.iPrj ⟨0, address 3⟩, #[], #[], #[]⟩
def recProjection : Ixon.Constant := ⟨.rPrj ⟨1, address 3⟩, #[], #[], #[]⟩
def falseStore : Constants :=
  [(address 3, falseBlock), (address 4, falseProjection), (address 5, recProjection)]

#guard accepts falseStore
#guard reference falseStore (address 4) == some (.member (address 3) 0)
#guard reference falseStore (address 5) == some (.member (address 3) 1)
#guard reference falseStore (address 3) == none

/-- Physical Ixon layout: the family and recursor have independent owners. -/
def falseFamily : Ixon.Constant :=
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[]⟩], #[], #[], #[.zero]⟩

def falseRecursor : Ixon.Recursor :=
  let falseType := Ixon.Expr.ref 0 #[]
  let motive := Ixon.Expr.leanAll falseType (.sort 1)
  ⟨false, false, 1, 0, 0, 1, 0,
    .leanAll motive (.leanAll falseType (.app (.var 1) (.var 0))), #[]⟩

def falseRecursorRecord (recursor : Ixon.Recursor := falseRecursor) : Ixon.Constant :=
  ⟨.recr recursor, #[], #[address 4], #[.zero, .var 0]⟩

def separatedFalse (recursor : Ixon.Recursor := falseRecursor) : Constants :=
  [(address 3, falseFamily), (address 6, falseRecursorRecord recursor), (address 4, falseProjection)]

#guard accepts separatedFalse
-- `checkEnv_ok_iff`: the entry point agrees with reading then the closed check.
#guard match readDeclarations separatedFalse [] none none ({} : Config).fuel separatedFalse with
  | .ok decls => (check.{0,1} {} decls).isOk && decls.length == 2
  | .error _ => false
-- Production layout: the separately stored eliminator at its own record
-- satisfies the `EmptyType` interface; a family admitted without its
-- recursor does not, since its emptiness is not constrained.
#guard match checkEnv.{1} {} separatedFalse [] with
  | .ok env => decide (Certified.Basis.Empty.Interface env.toEnvironment (address 3) (.member (address 6) 0))
  | .error _ => false
#guard match checkEnv.{1} {} [(address 3, falseFamily), (address 4, falseProjection)] [] with
  | .ok env => (env.entries.map (·.1)).all fun r =>
      !decide (Certified.Basis.Empty.Interface env.toEnvironment (address 3) r)
  | .error _ => false
#guard accepts [(address 3, falseFamily), (address 4, falseProjection)]
#guard match checkEnv.{1} {} separatedFalse [] with
  | .ok env => (env.lookup (.member (address 3) 0)).isSome &&
      (env.lookup (.member (address 6) 0)).isSome &&
      (env.lookup (.member (address 3) 1)).isNone
  | _ => false
#guard accepts [(address 3, falseFamily),
  (address 6, { falseRecursorRecord with info := .muts #[.recr falseRecursor] }),
  (address 4, falseProjection), (address 7, ⟨.rPrj ⟨0, address 6⟩, #[], #[], #[]⟩)]

-- Candidate discovery alone cannot admit a changed type or metadata.
#guard declined (separatedFalse { falseRecursor with
  typ := .leanAll (.leanAll (.ref 0 #[]) (.sort 1)) (.leanAll (.ref 0 #[]) (.sort 0)) })
#guard declined (separatedFalse { falseRecursor with params := 18446744073709551615 })
#guard rejected (separatedFalse { falseRecursor with k := true })

-- A record between the family and recursor must still be checked.
def interveningFalseId : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, .leanAll (.ref 0 #[]) (.ref 0 #[]),
    .leanLam (.ref 0 #[]) (.var 0)⟩, #[], #[address 4], #[]⟩
#guard accepts [(address 3, falseFamily), (address 8, interveningFalseId),
  (address 6, falseRecursorRecord), (address 4, falseProjection)]
#guard rejected [(address 3, falseFamily),
  (address 8, { interveningFalseId with refs := #[address 99] }),
  (address 6, falseRecursorRecord), (address 4, falseProjection)]
#guard rejected [(address 4, falseProjection)]
#guard rejected [(address 3, falseBlock), (address 4, { falseProjection with
  info := .rPrj ⟨0, address 3⟩ })]
#guard rejected [(address 3, falseBlock), (address 4, { falseProjection with
  info := .iPrj ⟨2, address 3⟩ })]
#guard rejected [(address 3, falseBlock), (address 4, { falseProjection with refs := #[address 3] })]
#guard rejected [(address 3, falseBlock), (address 4, { falseProjection with
  info := .cPrj ⟨0, 0, address 3⟩ })]

def literalContext : Context :=
  let base := ctx { identity with refs := #[address 9] }
  Context.ofStores base.constants [(address 9, ⟨#[3, 2, 1]⟩)] base.owner base.source
    (some (.member (address 3) 0))

#guard match readExpr literalContext 10 (.nat 0) with
  | .ok value => value == .natLit (.member (address 3) 0) 66051
  | _ => false
#guard malformed literalContext (.nat 1)
#guard malformed (literalContext.withBlobs []) (.nat 0)
#guard natural ⟨#[]⟩ == 0

/-- String literals read as their constructor expansion once the string
constants are configured; without them they are unsupported. -/
def stringRefs : StringRefs Address :=
  ⟨.member (address 20) 0, .member (address 21) 0, .member (address 3) 0,
   .member (address 22) 0, .ctor (address 23) 0 0, .ctor (address 23) 0 1⟩

def stringContext : Context :=
  let base := ctx { identity with refs := #[address 9] }
  Context.ofStores base.constants [(address 9, "hé".toUTF8)] base.owner base.source
    (some (.member (address 3) 0)) (some stringRefs)

#guard match readExpr stringContext 10 (.str 0) with
  | .ok value => value == stringRefs.stringLiteral "hé"
  | _ => false
#guard unsupported (Ixon.Expr.str 0)
#guard malformed (stringContext.withBlobs [(address 9, ⟨#[0xff]⟩)]) (.str 0)
#guard natural ⟨#[0, 0]⟩ == 0
#guard levelTree (.max (.var 0) (.imax .zero (.var 1))) ==
  VLevel.max (.param 0) (.imax .zero (.param 1))

example (V : Type 1) [Model.SetTheory V] {env : Env Address}
    (h : checkEnv.{1} {} falseStore [] = .ok env) : Nonempty (Model V env) :=
  checkEnv_has_model V h

example {env : Env Address} (h : checkEnv.{1} {} falseStore [] = .ok env) :
    _root_.Ix.Kernel.Ingress.Installed falseStore [] none none env := checkEnv_reading h

end Tests.Ix.Kernel.Ingress
