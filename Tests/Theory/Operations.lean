/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Operations
import Tests.Theory.Acceptance

open Ix.Theory

namespace Tests.Theory.Operations

open Ix.Theory.Certified Ix.Theory.Model
open Tests.Theory.Checker
open Tests.Theory.Acceptance (identityAnnotations)

def betaType : AExpr Nat := .forallE .never (.sort .zero) (.sort .zero)

def betaInference : InferenceWitness Nat := {
  annotations := .app (identityAnnotations (.succ .zero)) .leaf
  type := betaType
  typing := .app .never (.sort (.succ .zero)) (.forallE .never (.bvar 0) (.bvar 1))
    (identityWitness (.succ .zero)) .sort
}

def betaWhnf : WhnfWitness Nat := {
  source := betaInference
  result := betaResult
  resultTyping := .lam (.succ .zero) (.succ .zero) (.sort .zero) .sort .sort .bvar
  conversion := betaWitness
}

#guard inferCertified.{0,0} 50 0 emptyEnvironment [] betaSource.erase betaInference |>.isSome
#guard whnfCertified.{0,0} 50 0 emptyEnvironment [] betaSource.erase betaWhnf |>.isSome

-- Valid typing plus reflexive conversion does not certify a remaining redex.
#guard whnfCertified.{0,0} 50 0 emptyEnvironment [] betaSource.erase
  { betaWhnf with
    result := betaSource
    resultTyping := betaInference.typing
    conversion := .refl } |>.isNone

-- Neither the input reading nor the proposed normal form can change unchecked.
#guard whnfCertified.{0,0} 50 0 emptyEnvironment []
  (.app (identity .zero).erase (.sort .zero)) betaWhnf |>.isNone
#guard whnfCertified.{0,0} 50 0 emptyEnvironment [] betaSource.erase
  { betaWhnf with result := .sort .zero, resultTyping := .sort } |>.isNone

end Tests.Theory.Operations
