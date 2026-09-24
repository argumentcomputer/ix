/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Kernel fixtures

Executable checks of `Ix.Kernel.check` on small declarations: accepted
definitions and theorems exercising application, beta and delta reduction,
`let`, universe instantiation, and level equivalence; and one input for each
rejection and decline of milestone K1. `#guard` runs the compiled checker. -/

open Ix.Kernel

namespace Tests.Ix.Kernel.Fixtures

abbrev E := VExpr String

def sortU : E := .sort (.param 0)
def type0 : E := .sort (.succ .zero)
def type1 : E := .sort (.succ (.succ .zero))
def prop : E := .sort .zero

def defn (address : String) (universes : Nat) (kind : DefKind) (type body : E)
    (safety : Safety := .safe) : Decl String :=
  ⟨address, ⟨[.defn universes kind type body safety]⟩⟩

/-- `∀ (α : Sort u), α → α` -/
def idType : E := .forallE sortU (.forallE (.bvar 0) (.bvar 1))
/-- `fun (α : Sort u) (x : α) => x` -/
def idBody : E := .lam sortU (.lam (.bvar 0) (.bvar 0))
def idDecl : Decl String := defn "id" 1 .definition idType idBody

/-- `theorem idProp : ∀ (P : Prop), P → P` -/
def idPropType : E := .forallE prop (.forallE (.bvar 0) (.bvar 1))
def idPropDecl : Decl String :=
  defn "idProp" 0 .theorem idPropType (.lam prop (.lam (.bvar 0) (.bvar 0)))

/-- `∀ (α : Type), α → α` -/
def idTType : E := .forallE type0 (.forallE (.bvar 0) (.bvar 1))

/-- `id.{2} (∀ (α : Type), α → α) id.{1}`: applications, universe instantiation,
and the level equivalence `imax 2 (imax 1 1) = 2`. -/
def idIdBody : E :=
  .app (.app (.const (.member "id" 0) [.succ (.succ .zero)]) idTType)
    (.const (.member "id" 0) [.succ .zero])
def idIdDecl : Decl String := defn "idId" 0 .definition idTType idIdBody

/-- `fun (α : Type) (x : α) => let y : α := x; y` -/
def letBody : E := .lam type0 (.lam (.bvar 0) (.letE (.bvar 1) (.bvar 0) (.bvar 0)))
def letDecl : Decl String := defn "useLet" 0 .definition idTType letBody

/-- `twice : ∀ (α : Type), (α → α) → α → α := fun α f x => f (f x)` -/
def twiceType : E :=
  .forallE type0 (.forallE (.forallE (.bvar 0) (.bvar 1)) (.forallE (.bvar 1) (.bvar 2)))
def twiceBody : E :=
  .lam type0 (.lam (.forallE (.bvar 0) (.bvar 1))
    (.lam (.bvar 1) (.app (.bvar 1) (.app (.bvar 1) (.bvar 0)))))
def twiceDecl : Decl String := defn "twice" 0 .definition twiceType twiceBody

/-- `fun (α : Type) => twice α (id.{1} α)`: beta reduction of the applied type. -/
def twiceIdBody : E :=
  .lam type0 (.app (.app (.const (.member "twice" 0) []) (.bvar 0))
    (.app (.const (.member "id" 0) [.succ .zero]) (.bvar 0)))
def twiceIdDecl : Decl String := defn "twiceId" 0 .definition idTType twiceIdBody

/-- `Fn : Type 1 := ∀ (α : Type), α → α` and `idFn : Fn := fun α x => x`: delta
reduction of the declared type during conversion. -/
def fnDecl : Decl String := defn "Fn" 0 .definition type1 idTType
def idFnDecl : Decl String :=
  defn "idFn" 0 .definition (.const (.member "Fn" 0) []) (.lam type0 (.lam (.bvar 0) (.bvar 0)))

/-- `opaque idOpaque : ∀ (α : Type), α → α := fun α x => x` -/
def opaqueDecl : Decl String :=
  defn "idOpaque" 0 .opaque idTType (.lam type0 (.lam (.bvar 0) (.bvar 0)))

def accepted : List (Decl String) :=
  [idDecl, idPropDecl, idIdDecl, letDecl, twiceDecl, twiceIdDecl, fnDecl, idFnDecl, opaqueDecl]

/-! ## Harness -/

def run (decls : List (Decl String)) : Except Error (Env String) := check.{0,1} {} decls

def accepts (decls : List (Decl String)) : Bool :=
  match run decls with | .ok _ => true | .error _ => false

def installs (decls : List (Decl String)) (n : Nat) : Bool :=
  match run decls with | .ok env => env.entries.length == n | .error _ => false

def rejects (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.rejected r) => r == reason | _ => false

def declines (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.declined r) => r == reason | _ => false

/-- The public theorem applies to the fixture runs at the model universe of
`Models/SetTheory` (`ZFSet.{0} : Type 1`). -/
example (V : Type 1) [Ix.Kernel.Model.SetTheory V] {env : Env String}
    (h : run accepted = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  check_has_model V h

/-! ## Accepted -/

#guard accepts [idDecl]
#guard accepts [idPropDecl]
#guard installs accepted accepted.length
#guard accepts [fnDecl, idFnDecl]

/-! ## Rejected -/

#guard rejects [defn "badThm" 0 .theorem idTType (.lam type0 (.lam (.bvar 0) (.bvar 0)))]
  "the type of a theorem must be a proposition"
#guard rejects [defn "badBody" 1 .definition idType (.lam sortU (.lam (.bvar 0) (.bvar 1)))]
  "the body does not have the declared type"
#guard rejects [defn "ill" 0 .definition type0 (.app prop prop)]
  "the body is ill-typed"
#guard rejects [defn "illType" 0 .definition (.app prop prop) prop]
  "the declared type is ill-typed"
#guard rejects [defn "notType" 0 .definition idTType idTType]
  "the body does not have the declared type"
#guard rejects [defn "useMissing" 0 .definition idTType
    (.lam type0 (.app (.const (.member "nope" 0) []) (.bvar 0)))]
  "the declaration references a constant that is not installed"
#guard rejects [idDecl, idDecl] "duplicate declaration address"
#guard rejects [defn "openUniverse" 0 .definition idType idBody]
  "the declared type is not closed in its universe parameters and variables"
#guard rejects [defn "openVariable" 0 .definition type0 (.bvar 0)]
  "the body is not closed in its universe parameters and variables"
#guard rejects [idDecl, defn "wrongLevels" 0 .definition idTType (.const (.member "id" 0) [])]
  "the body is ill-typed"

/-! ## Declined -/

#guard declines [defn "unsafeId" 1 .definition idType idBody .unsafe]
  "unsafe and partial definitions are not supported"
#guard declines [⟨"ax", ⟨[.axiom 0 prop .safe]⟩⟩] "only the standard axioms and quotient soundness are supported"
#guard declines [⟨"pair", ⟨[.defn 1 .definition idType idBody .safe, .defn 1 .definition idType idBody .safe]⟩⟩]
  "multi-member blocks are not supported"
#guard rejects [defn "lit" 0 .definition type0 (.natLit (.member "Nat" 0) 0)]
  "the declaration references a constant that is not installed"
#guard match check.{0,1} { fuel := 0 } [idDecl] with
  | .error (.declined _) => true
  | _ => false

end Tests.Ix.Kernel.Fixtures
