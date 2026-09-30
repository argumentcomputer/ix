/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Annotate

/-! # Annotation with delayed context shifts

These cases distinguish propositions from types through dependent local
variables, exercise inference fallback with a nonempty initial context, and
retain the transparent-let fallback and bounded-search outcomes. -/

open Ix.Kernel Ix.Kernel.Model

namespace Tests.Ix.Kernel.AnnotationContexts

def prop : VExpr Nat := .sort .zero
def type0 : VExpr Nat := .sort (.succ .zero)
def type1 : VExpr Nat := .sort (.succ (.succ .zero))

def read (Γ : Context Nat) (raw : VExpr Nat) : Option (AExpr Nat) :=
  (annotate.{0,1} 64 (fun _ => none) Γ raw).toOption

-- Both binder conditions are inherited from the sort of the dependent type.
#guard read [] (.lam prop (.lam (.bvar 0) (.bvar 0))) =
  some (.lam .always (.sort .zero) (.lam .always (.bvar 0) (.bvar 0)))
#guard read [] (.lam type0 (.lam (.bvar 0) (.bvar 0))) =
  some (.lam .never (.sort (.succ .zero)) (.lam .never (.bvar 0) (.bvar 0)))

-- P : Prop, A : Type, x : P. Reading x must find P beyond both later binders.
#guard read [] (.lam prop (.lam type0 (.lam (.bvar 1) (.bvar 0)))) =
  some (.lam .always (.sort .zero)
    (.lam .always (.sort (.succ .zero)) (.lam .always (.bvar 1) (.bvar 0))))

-- The same dependency begins outside annotation, in a full model context.
#guard read [.sort (.succ .zero), .sort .zero] (.lam (.bvar 1) (.bvar 0)) =
  some (.lam .always (.bvar 1) (.bvar 0))

-- A : Type, f : A → A. A local function application forces inference to
-- materialize the deferred context, including shifts in f's dependent type.
def functionContext : Context Nat :=
  [.forallE .never (.bvar 1) (.bvar 2), .sort (.succ .zero)]

#guard read functionContext (.lam (.bvar 1) (.app (.bvar 1) (.bvar 0))) =
  some (.lam .never (.bvar 1) (.app (.bvar 1) (.bvar 0)))

-- A local type family application forces the Pi annotation fallback as well.
#guard read [.forallE .never (.sort (.succ .zero)) (.sort (.succ .zero))]
    (.forallE prop (.app (.bvar 1) prop)) =
  some (.forallE .never (.sort .zero) (.app (.bvar 1) (.sort .zero)))

-- The opaque local F does not expose a Pi to inference. Annotation retries
-- with F's value substituted, then transfers annotations onto the raw let.
def transparentLet : VExpr Nat :=
  .letE type1 (.forallE type0 type0) (.lam (.bvar 0) (.app (.bvar 0) prop))

#guard read [] transparentLet =
  some (.letE (.sort (.succ (.succ .zero)))
    (.forallE .never (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.lam .never (.bvar 0) (.app (.bvar 0) (.sort .zero))))

#guard match annotate.{0,1} 0 (β := Nat) (fun _ => none) [] prop with
  | .error .exhausted => true
  | _ => false
#guard match annotate.{0,1} 2 (β := Nat) (fun _ => none) []
    (.lam prop (.lam (.bvar 0) (.bvar 0))) with
  | .error .exhausted => true
  | _ => false

-- A missing local type remains a failed search; delayed lookup must not
-- manufacture an entry at or beyond the end of either context segment.
#guard (read [] (.lam prop (.bvar 4))).isNone
#guard (read functionContext (.lam (.bvar 1) (.app (.bvar 4) (.bvar 0)))).isNone

-- A polymorphic identity has a dependent result type: after both arguments,
-- the raw telescope ends in bvar 1. Its last Pi still records the result sort.
def identityType : AExpr Nat :=
  let p := Certified.zeroCondition (.param 0)
  .forallE p (.sort (.param 0)) (.forallE p (.bvar 0) (.bvar 1))

def applicationEntries : Environment Nat := fun
  | .member 0 0 => some ⟨1, identityType, none, [], []⟩
  | .member 1 0 => some ⟨0, .sort (.succ (.succ .zero)),
      some (.forallE .never (.sort (.succ .zero)) (.sort (.succ .zero))), [], []⟩
  | .member 2 0 => some ⟨0, .const (.member 1 0) [],
      some (.lam .never (.sort (.succ .zero)) (.bvar 0)), [], []⟩
  | _ => none

def identityUse (level : VLevel) : VExpr Nat :=
  .lam (.sort level) (.lam (.bvar 0)
    (.app (.app (.const (.member 0 0) [level]) (.bvar 1)) (.bvar 0)))

def annotatedIdentityUse (level : VLevel) : AExpr Nat :=
  let p := Certified.zeroCondition level
  .lam p (.sort level) (.lam p (.bvar 0)
    (.app (.app (.const (.member 0 0) [level]) (.bvar 1)) (.bvar 0)))

-- Five units suffice for the syntax depth, without inferring the application
-- to discover either lambda annotation. Ordinary inference validates them.
#guard ([.zero, .succ .zero, .param 0] : List VLevel).all fun level =>
  decide ((annotate.{0,1} 5 applicationEntries [] (identityUse level)).toOption =
    some (annotatedIdentityUse level))
#guard ([.zero, .succ .zero, .param 0] : List VLevel).all fun level =>
  (inferA.{0,1} 128 applicationEntries [] (annotatedIdentityUse level)).isOk

-- Conditions remain proposals: reading one does not certify the constant's
-- universe arity, which full inference must still reject when it is wrong.
def wrongArityUse : VExpr Nat :=
  .lam prop (.lam (.bvar 0)
    (.app (.app (.const (.member 0 0) []) (.bvar 1)) (.bvar 0)))
#guard match annotate.{0,1} 5 applicationEntries [] wrongArityUse with
  | .ok term => !(inferA.{0,1} 128 applicationEntries [] term).isOk
  | .error _ => false

-- Zero, partial, and complete application all retain the appropriate sort
-- condition. Reading past the explicit telescope or an absent entry declines.
#guard termCondition applicationEntries [] (.const (.member 0 0) [.zero]) = some .always
#guard termCondition applicationEntries []
  (.app (.const (.member 0 0) [.succ .zero]) (.sort .zero)) = some .never
#guard termCondition applicationEntries []
  (.app (.app (.const (.member 0 0) [.param 0]) (.bvar 1)) (.bvar 0)) =
    some (Certified.PropWhen.param 0)
#guard termCondition applicationEntries []
  (.app (.app (.app (.const (.member 0 0) [.zero]) (.bvar 2)) (.bvar 1)) (.bvar 0)) = none
#guard termCondition applicationEntries [] (.const (.member 3 0) []) = none
#guard termCondition applicationEntries []
  (.app (.const (.member 3 0) []) (.sort .zero)) = none

-- A hidden Pi is still found by inference when the constant's type is an
-- alias. Likewise, a dependent result may become a function after substitution
-- even though the explicit stored telescope has no further binder.
def aliasApplication : VExpr Nat := .lam prop (.app (.const (.member 2 0) []) prop)
#guard termCondition applicationEntries []
  (.app (.const (.member 2 0) []) (.sort .zero)) = none
#guard (annotate.{0,1} 64 applicationEntries [] aliasApplication).toOption =
  some (.lam .never (.sort .zero) (.app (.const (.member 2 0) []) (.sort .zero)))

def extraApplication : VExpr Nat :=
  .lam prop (.app (.app (.app (.const (.member 0 0) [.succ (.succ .zero)])
    (.forallE type0 type0)) (.lam type0 (.bvar 0))) prop)
#guard (annotate.{0,1} 128 applicationEntries [] extraApplication).isOk

end Tests.Ix.Kernel.AnnotationContexts
