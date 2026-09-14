/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Bytes
import Ix.Theory.Certificate.Build

namespace Ix.Certified.Fixtures

open Ix.Theory Ix.Theory.Certified

def encode (source : Ixon.Constant) : Address × ByteArray :=
  let bytes := Ixon.serConstant source
  (Address.blake3 bytes, bytes)

def falseBlock : Ixon.Constant := {
  info := .muts #[.indc {
    isUnsafe := false, lvls := 0, params := 0, indices := 0,
    typ := .sort 0, ctors := #[]
  }]
  sharing := #[]
  refs := #[]
  univs := #[.zero]
}

def falseBlockObject := encode falseBlock

def falseProjection : Ixon.Constant :=
  ⟨.iPrj ⟨0, falseBlockObject.1⟩, #[], #[], #[]⟩

def falseObject := encode falseProjection

def falseElim : Ixon.Constant := {
  info := .recr {
    k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
    motives := 1, minors := 0,
    typ := .leanAll (.leanAll (.ref 0 #[]) (.sort 0))
      (.leanAll (.ref 0 #[]) (.app (.var 1) (.var 0))),
    rules := #[]
  }
  sharing := #[]
  refs := #[falseObject.1]
  univs := #[.var 0]
}

def falseElimObject := encode falseElim

def profile : Profile := ⟨falseObject.1, falseElimObject.1, none⟩
def prelude : ConstantBlobs := [falseBlockObject, falseObject, falseElimObject]

def identity : Ixon.Constant := {
  info := .defn {
    kind := .thm, safety := .safe, lvls := 0,
    typ := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
    value := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  }
  sharing := #[]
  refs := #[]
  univs := #[.zero]
}

def identityObject := encode identity
def identityBlobs : ConstantBlobs := prelude ++ [identityObject]

def witness? (blobs : ConstantBlobs) (target : Address) : Option (ProofWitness Address) := do
  let prepared ← prepare? 300 profile target blobs
  Ix.Theory.Certificate.proofWitness? 300 prepared.signature prepared.input

def accepted (blobs : ConstantBlobs) (target : Address) : Bool :=
  (witness? blobs target).any (acceptsSerialized.{0} 300 profile target blobs)

#guard accepted identityBlobs identityObject.1

-- A new valid hash cannot license trailing data outside the constant grammar.
def trailingIdentity : Address × ByteArray :=
  let bytes := identityObject.2.push 0
  (Address.blake3 bytes, bytes)
#guard (prepare? 300 profile trailingIdentity.1 (prelude ++ [trailingIdentity])).isNone

-- Changed bytes under an old address fail authentication.
#guard (prepare? 300 profile identityObject.1
  (prelude ++ [(identityObject.1, identityObject.2.push 0)])).isNone

-- Duplicate object addresses are not silently overwritten.
#guard (prepare? 300 profile identityObject.1 (identityBlobs ++ [identityObject])).isNone

def linearIdentity : Ixon.Constant :=
  { identity with info := .defn {
      kind := .thm, safety := .safe, lvls := 0,
      typ := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)),
      value := .lam .linear (.sort 0) (.leanLam (.var 0) (.var 0))
    } }

def linearIdentityObject := encode linearIdentity
#guard (prepare? 300 profile linearIdentityObject.1
  (prelude ++ [linearIdentityObject])).isNone

def wrongTable : Ixon.Constant := { identity with univs := #[] }
def wrongTableObject := encode wrongTable
#guard (prepare? 300 profile wrongTableObject.1 (prelude ++ [wrongTableObject])).isNone

def cyclicSharing : Ixon.Constant := {
  identity with
  info := .defn {
    kind := .thm, safety := .safe, lvls := 0,
    typ := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)), value := .share 0 }
  sharing := #[.share 0]
}
def cyclicSharingObject := encode cyclicSharing
#guard (prepare? 30 profile cyclicSharingObject.1 (prelude ++ [cyclicSharingObject])).isNone

def axiomIdentity : Ixon.Constant := {
  identity with
  info := .axio {
    isUnsafe := false, lvls := 0,
    typ := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1)) }
}
def axiomIdentityObject := encode axiomIdentity

-- Force an untrusted proof witness through the actual acceptance gate. This
-- is a policy rejection, not merely a failure of the suggestion producer.
def axiomRejected : Bool :=
  match witness? identityBlobs identityObject.1 with
  | none => false
  | some witness =>
    let forged := { witness with declarations := witness.declarations.map fun declaration =>
      match declaration with
      | .definition definition => .definition { definition with ref := .member axiomIdentityObject.1 0 }
      | .ordinary block => .ordinary block
      | .standard witness => .standard witness
      | .quotient witness => .quotient witness
      | .structure witness => .structure witness
      | .natural witness => .natural witness
      | .modeled witness => .modeled witness }
    !acceptsSerialized.{0} 300 profile axiomIdentityObject.1
      (prelude ++ [axiomIdentityObject]) forged

#guard axiomRejected

end Ix.Certified.Fixtures
