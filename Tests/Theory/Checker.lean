/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Checker

open Ix.Theory

namespace Tests.Theory.Checker

open Ix.Theory.Certified Ix.Theory.Model

def emptyEnvironment : Environment Nat := fun _ => none

def identity (l : VLevel) : AExpr Nat :=
  .lam (zeroCondition l) (.sort l) (.lam (zeroCondition l) (.bvar 0) (.bvar 0))

def identityType (l : VLevel) : AExpr Nat :=
  .forallE (zeroCondition l) (.sort l) (.forallE (zeroCondition l) (.bvar 0) (.bvar 1))

def identityWitness (l : VLevel) : TypingWitness Nat :=
  .lam (.succ l) (.imax l l) (.forallE (zeroCondition l) (.bvar 0) (.bvar 1))
    .sort (.forallE l l .bvar .bvar)
    (.lam l l (.bvar 1) .bvar .bvar .bvar)

#guard checkTypeCertified.{0,0} 30 1 emptyEnvironment [] (identity (.param 0))
  (identityType (.param 0)) (identityWitness (.param 0))
#guard checkTypeCertified.{0,0} 30 0 emptyEnvironment [] (identity .zero)
  (identityType .zero) (identityWitness .zero)
#guard checkTypeCertified.{0,0} 30 0 emptyEnvironment [] (identity (.succ .zero))
  (identityType (.succ .zero)) (identityWitness (.succ .zero))

-- The same parameterized expression is rejected with a missing universe slot.
#guard !checkTypeCertified.{0,0} 30 0 emptyEnvironment [] (identity (.param 0))
  (identityType (.param 0)) (identityWitness (.param 0))

-- Structural erasure alone would permit this false annotation.
def wrongIdentity : AExpr Nat := .lam .never (.sort .zero) (.lam .never (.bvar 0) (.bvar 0))
def wrongIdentityType : AExpr Nat :=
  .forallE .never (.sort .zero) (.forallE .never (.bvar 0) (.bvar 1))
#guard !checkTypeCertified.{0,0} 30 0 emptyEnvironment [] wrongIdentity wrongIdentityType
  (identityWitness .zero)

def betaSource : AExpr Nat := .app (identity (.succ .zero)) (.sort .zero)
def betaResult : AExpr Nat := .lam .never (.sort .zero) (.bvar 0)
def betaWitness : ConversionWitness Nat :=
  .beta (identityType (.succ .zero)) (identityWitness (.succ .zero)) .sort
#guard defeqCertified.{0,0} 30 0 emptyEnvironment [] betaSource betaResult betaWitness

-- A proposed beta step cannot substitute an argument outside the lambda domain.
#guard !defeqCertified.{0,0} 30 0 emptyEnvironment []
  (.app (identity (.succ .zero)) (.sort (.succ .zero)))
  (.lam .never (.sort (.succ .zero)) (.bvar 0)) betaWitness
-- This check is required in the proof-point regime too.
#guard !defeqCertified.{0,0} 30 0 emptyEnvironment []
  (.app (identity .zero) (.sort .zero))
  (.lam .always (.sort .zero) (.bvar 0))
  (.beta (identityType .zero) (identityWitness .zero) .sort)

def etaSource : AExpr Nat :=
  .lam .never (.sort (.succ .zero))
    (.app ((identity (.succ .zero)).liftN 1) (.bvar 0))
#guard defeqCertified.{0,0} 30 0 emptyEnvironment [] etaSource (identity (.succ .zero))
  (.eta (.forallE .never (.bvar 0) (.bvar 1)) (identityWitness (.succ .zero)))

def proofContext : Context Nat :=
  Context.push (.bvar 1) (Context.push (.bvar 0) (Context.push (.sort .zero) []))
#guard defeqCertified.{0,0} 30 0 emptyEnvironment proofContext (.bvar 0) (.bvar 1)
  (.proofIrrel (.bvar 2) .bvar .bvar .bvar)

#guard LevelEq.check 1 (.imax (.param 0) (.param 0)) (.param 0)
#guard LevelEq.check 0 (.imax (.succ .zero) .zero) .zero
#guard !LevelEq.check 0 (.succ .zero) (.succ (.succ .zero))
#guard !LevelEq.check 0 (.imax (.param 0) .zero) .zero
#guard defeqCertified.{0,0} 10 1 emptyEnvironment []
  (.sort (.imax (.param 0) (.param 0))) (.sort (.param 0)) .sort
#guard !defeqCertified.{0,0} 10 0 emptyEnvironment []
  (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) .sort

#guard !checkTypeCertified.{0,0} 0 1 emptyEnvironment [] (identity (.param 0))
  (identityType (.param 0)) (identityWitness (.param 0))
#guard !checkTypeCertified.{0,0} 30 0 emptyEnvironment [] (.natLit 0) (.sort .zero) .const
#guard !checkTypeCertified.{0,0} 30 0 emptyEnvironment [] (.const (.member 42 0) []) (.sort .zero) .const

end Tests.Theory.Checker
