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

end Tests.Ix.Kernel.AnnotationContexts
