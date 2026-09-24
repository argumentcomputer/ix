/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Const
import Ix.Kernel.Annotate
import Ix.Kernel.Inductive.Ordinary
import Ix.Kernel.Inductive.Structure
import Ix.Kernel.Inductive.Natural
import Ix.Kernel.Certified.Quotient.Install
import Ix.Kernel.Certified.Standard.Install
import Ix.Kernel.Certified.Basis.EqualityChecked

/-! # The declaration checker

The executable entry points of the kernel. `checkDecl` checks one declaration
against the environment; `checkDecls` folds it over a list in the supplied
order; `check` starts from the empty environment. Every accepting run has the
model constructed in `Ix.Kernel.Consistency`.

Outcomes are accept (`.ok`), reject (`Error.rejected`: the input is wrong),
and decline (`Error.declined`: the kernel does not support the input and says
why). Only accept carries the theorems.

Milestone K1 supports single-member blocks holding one safe definition,
theorem, or opaque: the declared type is annotated and checked to be a type,
the body is annotated and checked to have the declared type (a theorem's
type must be a proposition), and the constant is installed with its body. The
proof-carrying `checkDeclC` returns the environment together with the model
extension (`StepClaim`); the public `checkDecl` erases it. -/

namespace Ix.Kernel

open Model Model.SetTheory Certified Certified.Ordinary Certified.Structure Inductive

universe u v

/-- Kernel configuration. -/
structure Config where
  /-- Fuel for reduction, inference, and conversion; exhaustion declines. -/
  fuel : Nat := 100000
  deriving Repr

/-- Non-accepting outcomes. -/
inductive Error where
  /-- The input is wrong. -/
  | rejected (reason : String)
  /-- The kernel does not support the input. -/
  | declined (reason : String)
  deriving Repr, DecidableEq

/-- An input declaration: a block of constants at its address. -/
structure Decl (β : Type u) where
  address : β
  block : Block β

variable {β : Type u} [DecidableEq β]

/-- Install one checked definition. -/
private def installDefinition (env : Env β) (r : ConstRef β) (universes : Nat)
    (type body : AExpr β) (fresh : env.toEnvironment r = none)
    (hTs : type.Scope universes 0) (hBs : body.Scope universes 0)
    (hTr : type.ReferencesIn env.toEnvironment) (hBr : body.ReferencesIn env.toEnvironment)
    {level : VLevel} (hT : TypingClaim.{u,v} env.toEnvironment [] type (.sort level))
    (hB : TypingClaim.{u,v} env.toEnvironment [] body type) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  let entry : ConstantEntry β := ⟨universes, type, some body, [], []⟩
  ⟨env.push r entry, fun V _ m => by
    obtain ⟨constants', hM', -⟩ := extend_definition (entry := entry) m.wf fresh rfl rfl rfl hBs hTr hBr
      hT hB m.constants m.realizes
    refine ⟨⟨constants', ?_, ?_⟩⟩
    · rw [Env.toEnvironment_push]; exact hM'
    · rw [Env.toEnvironment_push]
      exact m.wf.insert hTs (fun b hb => by cases hb; exact hBs) hTr
        (fun b hb => by cases hb; exact hBr) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ h => nomatch h)⟩

/-- Check one declaration, returning the model extension with the environment. -/
def checkDeclC (cfg : Config) (env : Env β) (d : Decl β) :
    Except Error { env' : Env β // StepClaim.{u,v} env env' } :=
  match d.block.members with
  | [.defn universes kind type body .safe] =>
    let r : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries r = none then
      if !(type.refs ++ body.refs).all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match annotate.{u,v} cfg.fuel entries [] type, annotate.{u,v} cfg.fuel entries [] body with
      | .ok type', .ok body' =>
        if hTs : type'.Scope universes 0 then
          if hBs : body'.Scope universes 0 then
            if hTr : type'.ReferencesIn entries then
              if hBr : body'.ReferencesIn entries then
                match inferA.{u,v} cfg.fuel entries [] type' with
                | some ⟨S, hS⟩ =>
                  match sortOf (whnf.{u,v} cfg.fuel entries [] S) hS with
                  | some ⟨l, hT⟩ =>
                    if kind = .theorem && !levelIsZero l then
                      .error (.rejected "the type of a theorem must be a proposition")
                    else
                      match inferA.{u,v} cfg.fuel entries [] body' with
                      | some ⟨B, hb⟩ =>
                        match isDefEq.{u,v} cfg.fuel entries [] B type' with
                        | some ⟨hc⟩ =>
                          .ok (installDefinition env r universes type' body' fresh hTs hBs hTr hBr hT
                            (hb.convF hT.formed hc))
                        | none => .error (.rejected "the body does not have the declared type")
                      | none => .error (.rejected "the body is ill-typed")
                  | none => .error (.rejected "the declared type is not a type")
                | none => .error (.rejected "the declared type is ill-typed")
              else .error (.rejected "the body references a constant that is not installed")
            else .error (.rejected "the declared type references a constant that is not installed")
          else .error (.rejected "the body is not closed in its universe parameters and variables")
        else .error (.rejected "the declared type is not closed in its universe parameters and variables")
      | .error .fuel, _ | _, .error .fuel => .error (.declined "out of fuel")
      | .error .illTyped, _ => .error (.rejected "the declared type is ill-typed")
      | _, .error .illTyped => .error (.rejected "the body is ill-typed")
    else .error (.rejected "duplicate declaration address")
  | [.induct _ _ _ _ _ .safe, .recursor _ _ _ _ _ _ _ _ .safe] =>
    let source := d.address
    let entries := env.toEnvironment
    if (entries (.member source 0)).isSome || (entries (.member source 1)).isSome then
      .error (.rejected "duplicate declaration address")
    else if !d.block.refs.all (fun q => q.block == source || (entries q).isSome) then
      .error (.rejected "the declaration references a constant that is not installed")
    else
      match readBlock.{u,v} cfg.fuel entries source d.block with
      | none => .error (.declined "the inductive block is not in the ordinary shape class")
      | some reading =>
        let shape := reading.shape
        let mode := reading.mode
        let k := reading.k
        if d.block = ⟨[shape.source source, shape.recursorSource source mode k]⟩ then
          if k && !decide shape.SupportsK then
            .error (.rejected "K-like reduction is declared for an inductive that does not support it")
          else
            match checkBlock.{u,v} cfg.fuel entries source shape mode with
            | some ⟨hb⟩ =>
              if hnat : shape = Natural.shape then
                match Natural.check.{u,v} entries source mode (hnat ▸ hb) with
                | some ⟨hn⟩ => .ok (installNatural env source mode hn)
                | none => .ok (installOrdinary env source shape mode hb)
              else
              match readDescription.{u,v} cfg.fuel entries reading with
              | some d =>
                if hd : d.ordinary = shape then
                  match Structure.check.{u,v} cfg.fuel entries d source mode (hd ▸ hb) with
                  | some ⟨hs⟩ => .ok (installStructure env source d mode hs)
                  | none => .ok (installOrdinary env source shape mode hb)
                else .ok (installOrdinary env source shape mode hb)
              | none => .ok (installOrdinary env source shape mode hb)
            | none => .error (.rejected "the inductive block is ill-formed")
        else .error (.declined "the block is not the generated ordinary block of its inductive")
  | [.induct _ _ _ _ _ _, .recursor _ _ _ _ _ _ _ _ _] =>
    .error (.declined "unsafe inductive blocks are not supported")
  | [.defn _ _ _ _ _] => .error (.declined "unsafe and partial definitions are not supported")
  | [.quot kind uvars t] =>
    let self : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries self = none then
      if !t.refs.all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match kind, uvars, Quotient.occurrences t with
      | .type, 1, [] =>
        if d.block = ⟨[Quotient.Refs.source (⟨self, self, self, self, self⟩ : Quotient.Refs β) .type]⟩ then
          if hTs : (Quotient.typeType : AExpr β).Scope 1 0 then
            match checkSort.{u,v} cfg.fuel entries [] Quotient.typeType with
            | some ⟨_, ht⟩ => .ok (Quotient.installType env self fresh hTs ht)
            | none => .error (.rejected "the quotient former's type is ill-typed")
          else .error (.rejected "the quotient former's type is not closed")
        else .error (.declined "the quotient former is not the primitive one")
      | .ctor, 1, [q] =>
        let refs : Quotient.Refs β := ⟨q, q, self, self, self⟩
        if d.block = ⟨[Quotient.Refs.source refs .ctor]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hTs : (Quotient.ctorType refs).Scope 1 0 then
              if hTr : (Quotient.ctorType refs).ReferencesIn entries then
                match checkSort.{u,v} cfg.fuel entries [] (Quotient.ctorType refs) with
                | some ⟨_, ht⟩ => .ok (Quotient.installCtor env refs fresh hTs hq hTr ht)
                | none => .error (.rejected "the quotient constructor's type is ill-typed")
              else .error (.rejected "the quotient constructor references a constant that is not installed")
            else .error (.rejected "the quotient constructor's type is not closed")
          else .error (.rejected "the quotient constructor does not follow the admitted former")
        else .error (.declined "the quotient constructor is not the primitive one")
      | .lift, 2, [eq, q] =>
        let refs : Quotient.Refs β := ⟨eq, q, self, self, self⟩
        if d.block = ⟨[Quotient.Refs.source refs .lift]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hTs : (Quotient.liftType refs).Scope 2 0 then
              if hTr : (Quotient.liftType refs).ReferencesIn entries then
                match checkSort.{u,v} cfg.fuel entries [] (Quotient.liftType refs) with
                | some ⟨_, ht⟩ => .ok (Quotient.installLift env refs fresh hTs hq hTr ht)
                | none => .error (.rejected "the quotient lift's type is ill-typed")
              else .error (.rejected "the quotient lift references a constant that is not installed")
            else .error (.rejected "the quotient lift's type is not closed")
          else .error (.rejected "the quotient lift does not follow the admitted former")
        else .error (.declined "the quotient lift is not the primitive one")
      | .ind, 1, [q, c] =>
        let refs : Quotient.Refs β := ⟨q, q, c, self, self⟩
        if d.block = ⟨[Quotient.Refs.source refs .ind]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hc : Quotient.HasCtor entries refs then
              if hTs : (Quotient.indType refs).Scope 1 0 then
                if hTr : (Quotient.indType refs).ReferencesIn entries then
                  match checkSort.{u,v} cfg.fuel entries [] (Quotient.indType refs) with
                  | some ⟨_, ht⟩ => .ok (Quotient.installInd env refs fresh hTs hq hc hTr ht)
                  | none => .error (.rejected "the quotient eliminator's type is ill-typed")
                else .error (.rejected "the quotient eliminator references a constant that is not installed")
              else .error (.rejected "the quotient eliminator's type is not closed")
            else .error (.rejected "the quotient eliminator does not follow the admitted constructor")
          else .error (.rejected "the quotient eliminator does not follow the admitted former")
        else .error (.declined "the quotient eliminator is not the primitive one")
      | _, _, _ => .error (.declined "the quotient declaration is not one of the primitive ones")
    else .error (.rejected "duplicate declaration address")
  | [.axiom 0 t .safe] =>
    let self : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries self = none then
      if !t.refs.all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match Standard.occurrences t with
      | [iff, eq] =>
        match Standard.propextSpec eq iff with
        | some spec =>
          if d.block = ⟨[spec.source]⟩ then
            if hp : spec.Prerequisites entries then
              if hTs : spec.type.Scope spec.universes 0 then
                if hTr : spec.type.ReferencesIn entries then
                  match checkSort.{u,v} cfg.fuel entries [] spec.type with
                  | some ⟨level, ht⟩ => .ok (Standard.install env self spec ⟨fresh, hp, hTs, hTr, ⟨level, ht⟩⟩)
                  | none => .error (.rejected "the axiom's type is ill-typed")
                else .error (.rejected "the axiom references a constant that is not installed")
              else .error (.rejected "the axiom's type is not closed")
            else .error (.rejected "the axiom's prerequisites are not the admitted interfaces")
          else .error (.declined "only the standard axioms and quotient soundness are supported")
        | none => .error (.declined "only the standard axioms and quotient soundness are supported")
      | _ => .error (.declined "only the standard axioms and quotient soundness are supported")
    else .error (.rejected "duplicate declaration address")
  | [.axiom 1 t .safe] =>
    let self : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries self = none then
      if !t.refs.all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match Quotient.occurrences t with
      | [eq, q, c] =>
        let refs : Quotient.Refs β := ⟨eq, q, c, self, self⟩
        if d.block = ⟨[Quotient.Refs.soundSource refs]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hc : Quotient.HasCtor entries refs then
              if hE : Quotient.EqInterface entries eq then
                if hTs : (Quotient.soundType refs).Scope 1 0 then
                  if hTr : (Quotient.soundType refs).ReferencesIn entries then
                    match checkSort.{u,v} cfg.fuel entries [] (Quotient.soundType refs) with
                    | some ⟨_, ht⟩ => .ok (Quotient.installSound env refs self fresh hTs hq hc hE hTr ht)
                    | none => .error (.rejected "the quotient soundness axiom's type is ill-typed")
                  else .error (.rejected "the quotient soundness axiom references a constant that is not installed")
                else .error (.rejected "the quotient soundness axiom's type is not closed")
              else .error (.rejected "the quotient soundness axiom's equality is not the admitted one")
            else .error (.rejected "the quotient soundness axiom does not follow the admitted constructor")
          else .error (.rejected "the quotient soundness axiom does not follow the admitted former")
        else .error (.declined "only the standard axioms and quotient soundness are supported")
      | [nonempty] =>
        match Standard.choiceSpec nonempty with
        | some spec =>
          if d.block = ⟨[spec.source]⟩ then
            if hp : spec.Prerequisites entries then
              if hTs : spec.type.Scope spec.universes 0 then
                if hTr : spec.type.ReferencesIn entries then
                  match checkSort.{u,v} cfg.fuel entries [] spec.type with
                  | some ⟨level, ht⟩ => .ok (Standard.install env self spec ⟨fresh, hp, hTs, hTr, ⟨level, ht⟩⟩)
                  | none => .error (.rejected "the axiom's type is ill-typed")
                else .error (.rejected "the axiom references a constant that is not installed")
              else .error (.rejected "the axiom's type is not closed")
            else .error (.rejected "the axiom's prerequisites are not the admitted interfaces")
          else .error (.declined "only the standard axioms and quotient soundness are supported")
        | none => .error (.declined "only the standard axioms and quotient soundness are supported")
      | _ => .error (.declined "only the standard axioms and quotient soundness are supported")
    else .error (.rejected "duplicate declaration address")
  | [.axiom _ _ _] => .error (.declined "only the standard axioms and quotient soundness are supported")
  | [_] => .error (.declined "only definitions, inductive blocks, quotient primitives, and the standard axioms are supported")
  | _ => .error (.declined "multi-member blocks are not supported")

/-- Check one declaration against the environment. -/
def checkDecl (cfg : Config) (env : Env β) (d : Decl β) : Except Error (Env β) :=
  (checkDeclC.{u,v} cfg env d).map Subtype.val

/-- The proof-carrying fold. -/
def checkDeclsC (cfg : Config) (env : Env β) :
    List (Decl β) → Except Error { env' : Env β // StepClaim.{u,v} env env' }
  | [] => .ok ⟨env, StepClaim.refl env⟩
  | d :: ds => do
    let ⟨env₁, h₁⟩ ← checkDeclC.{u,v} cfg env d
    let ⟨env₂, h₂⟩ ← checkDeclsC cfg env₁ ds
    return ⟨env₂, h₁.trans h₂⟩

/-- The closed fold: check declarations in the supplied order, each against the
environment the earlier ones built. -/
def checkDecls (cfg : Config) (env : Env β) (decls : List (Decl β)) : Except Error (Env β) :=
  (checkDeclsC.{u,v} cfg env decls).map Subtype.val

/-- The closed entry point: check declarations from the empty environment. -/
def check (cfg : Config) (decls : List (Decl β)) : Except Error (Env β) :=
  checkDecls.{u,v} cfg Env.empty decls

end Ix.Kernel
