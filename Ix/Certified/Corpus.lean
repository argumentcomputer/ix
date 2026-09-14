/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Fixtures

namespace Ix.Certified.Corpus

open Fixtures

def idType (level : UInt64) : Ixon.Expr :=
  .leanAll (.sort level) (.leanAll (.var 0) (.var 1))

def idBody (level : UInt64) : Ixon.Expr :=
  .leanLam (.sort level) (.leanLam (.var 0) (.var 0))

def polyId (kind : Ix.DefKind) : Ixon.Constant := {
  info := .defn {
    kind, safety := .safe, lvls := 1, typ := idType 0, value := idBody 0 }
  sharing := #[], refs := #[], univs := #[.var 0]
}

def polyUse (kind : Ix.DefKind) (large : Bool) : Ixon.Constant := {
  info := .defn {
    kind := .thm, safety := .safe, lvls := 0, typ := idType 0,
    value := if large then
      .app (.leanLam (idType 1) (idBody 0)) (.ref 0 #[1])
      else .ref 0 #[0] }
  sharing := #[], refs := #[(encode (polyId kind)).1],
  univs := #[.zero, .succ .zero]
}

def dependent (n : UInt64) (u : Ixon.Univ) : Ixon.Constant := {
  info := .defn {
    kind := .thm, safety := .safe, lvls := n,
    typ := .leanAll (.sort 0)
      (.leanAll (.leanAll (.var 0) (.sort 1))
        (.leanAll (.leanAll (.var 1) (.app (.var 1) (.var 0)))
          (.leanAll (.var 2) (.app (.var 2) (.var 0))))),
    value := .leanLam (.sort 0)
      (.leanLam (.leanAll (.var 0) (.sort 1))
        (.leanLam (.leanAll (.var 1) (.app (.var 1) (.var 0)))
          (.leanLam (.var 2) (.app (.var 1) (.var 0))))) }
  sharing := #[], refs := #[], univs := #[u, .zero]
}

-- The declared proposition contains a beta redex. The body is checked
-- against that original proposition through a beta conversion certificate.
def betaStatement : Ixon.Constant := {
  info := .defn {
    kind := .thm, safety := .safe, lvls := 0,
    typ := .app (.leanLam (.sort 0) (.var 0)) (idType 0),
    value := idBody 0 }
  sharing := #[], refs := #[], univs := #[.zero]
}

-- ∀ A : Prop, ∀ F : (A → A) → Prop, ∀ f, F f → F (fun x => f x).
-- The supplied proof returns its last argument, so admission needs eta
-- beneath a dependent application and a telescope of products.
def etaStatement : Ixon.Constant := {
  info := .defn {
    kind := .thm, safety := .safe, lvls := 0,
    typ := .leanAll (.sort 0)
      (.leanAll (.leanAll (.leanAll (.var 0) (.var 1)) (.sort 0))
        (.leanAll (.leanAll (.var 1) (.var 2))
          (.leanAll (.app (.var 1) (.var 0))
            (.app (.var 2) (.leanLam (.var 3) (.app (.var 2) (.var 0))))))),
    value := .leanLam (.sort 0)
      (.leanLam (.leanAll (.leanAll (.var 0) (.var 1)) (.sort 0))
        (.leanLam (.leanAll (.var 1) (.var 2))
          (.leanLam (.app (.var 1) (.var 0)) (.var 0)))) }
  sharing := #[], refs := #[], univs := #[.zero]
}

def eliminatorStatement : Ixon.Constant := {
  info := .defn {
    kind := .thm, safety := .safe, lvls := 0,
    typ := .leanAll (.leanAll (.ref 0 #[]) (.sort 0))
      (.leanAll (.ref 0 #[]) (.app (.var 1) (.var 0))),
    value := .ref 1 #[0] }
  sharing := #[], refs := #[falseObject.1, falseElimObject.1], univs := #[.zero]
}

structure Case where
  name : String
  target : Address
  blobs : ConstantBlobs

def one (name : String) (source : Ixon.Constant)
    (dependencies : List Ixon.Constant := []) : Case :=
  let object := encode source
  ⟨name, object.1, prelude ++ dependencies.map encode ++ [object]⟩

def positive : List Case := [
  one "identity" identity,
  one "dependent-polymorphic" (dependent 1 (.var 0)),
  one "dependent-Prop" (dependent 0 .zero),
  one "dependent-Type" (dependent 0 (.succ .zero)),
  one "dependent-Type1" (dependent 0 (.succ (.succ .zero))),
  one "definition-at-Prop" (polyUse .defn false) [polyId .defn],
  one "definition-at-Type" (polyUse .defn true) [polyId .defn],
  one "theorem-at-Prop" (polyUse .thm false) [polyId .thm],
  one "opaque-at-Type" (polyUse .opaq true) [polyId .opaq],
  one "beta-statement" betaStatement,
  one "eta-statement" etaStatement,
  one "False-eliminator" eliminatorStatement
]

#guard positive.all fun c => accepted c.blobs c.target

/-- Syntactic exclusions measured separately from failed witness generation.
The selected profile never enables literals or linear binder flags. -/
def declined : List Case := [
  one "linear-binder-profile" linearIdentity,
  one "literal-profile" { identity with info := .defn {
    kind := .thm, safety := .safe, lvls := 0,
    typ := idType 0, value := .nat 0 } }
]

#guard declined.all fun c => (prepare? 300 profile c.target c.blobs).isNone

end Ix.Certified.Corpus
