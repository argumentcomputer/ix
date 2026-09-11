/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Build
import Tests.Theory.Acceptance

open Ix.Theory

namespace Tests.Theory.Suggestions

open Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Certificate
open Tests.Theory.Acceptance
open Tests.Theory.Certified (primitives)

/-- Search success is deliberately insufficient: every test runs the public
acceptance validator on the produced ordinary witness data. -/
def autoAccept (input : ProofInput Nat) : Bool :=
  (proofWitness? 300 primitives input).any (acceptsCertified.{0,0} 300 primitives input)

#guard autoAccept identityInput
#guard autoAccept (idDefinitionInput .definition)
#guard autoAccept (idDefinitionInput .theorem)
#guard autoAccept (idDefinitionInput .opaque)
#guard autoAccept { idDefinitionInput with proof := largeIdentityUse.erase }
#guard autoAccept eliminatorInput
#guard !autoAccept { identityInput with proposition := primitives.falseExpr }

-- Dependent application with a nonempty-domain possibility:
-- λ A B f x => f x, where B : A → Prop and f : (x : A) → B x.
def dependentApplication (u : VLevel) : VExpr Nat :=
  .lam (.sort u)
    (.lam (.forallE (.bvar 0) (.sort .zero))
      (.lam (.forallE (.bvar 1) (.app (.bvar 1) (.bvar 0)))
        (.lam (.bvar 2) (.app (.bvar 1) (.bvar 0)))))

def dependentApplicationType (u : VLevel) : VExpr Nat :=
  .forallE (.sort u)
    (.forallE (.forallE (.bvar 0) (.sort .zero))
      (.forallE (.forallE (.bvar 1) (.app (.bvar 1) (.bvar 0)))
        (.forallE (.bvar 2) (.app (.bvar 2) (.bvar 0)))))

def dependentInput (n : Nat) (u : VLevel) : ProofInput Nat :=
  ⟨prelude, n, dependentApplication u, dependentApplicationType u⟩

#guard autoAccept (dependentInput 1 (.param 0))
#guard autoAccept (dependentInput 0 .zero)
#guard autoAccept (dependentInput 0 (.succ .zero))
#guard autoAccept (dependentInput 0 (.succ (.succ .zero)))

-- An out-of-scope universe is still rejected by the producer and validator.
#guard !autoAccept (dependentInput 0 (.param 0))

end Tests.Theory.Suggestions
