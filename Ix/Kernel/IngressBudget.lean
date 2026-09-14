/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module

public import Ix.Ixon

/-!
# Finite work bounds for anonymous ingress

These tail-recursive counters visit the serialized source trees without
expanding sharing references. The expression bound reserves one expansion
and completion frame for every sharing-table entry. Conversion maintains an
active-sharing set and a completed-entry cache, so a cyclic expansion is
rejected and an entry need only be expanded once.

The counters and the production range loops are total Lean definitions.
Their numeric bounds are computed from input syntax, not supplied by a
caller or justified by a termination axiom.
-/

public section
@[expose] section

namespace Ix.Kernel

/-- Logical work-list measure; it is erased from the executable counter. -/
noncomputable def ingressExprPendingSize : List Ixon.Expr → Nat
  | [] => 0
  | e :: rest => sizeOf e + ingressExprPendingSize rest

/-- Count the explicit conversion frames for the source trees without
expanding share references. The counter walk itself uses a tail-recursive
work list, so input depth does not consume the native call stack. -/
def ingressExprWork (pending : List Ixon.Expr) (total : Nat := 0) : Nat :=
  match pending with
  | [] => total
  | e :: rest => match e with
    | .app f a => ingressExprWork (f :: a :: rest) (total + 2)
    | .lam _ ty body | .all _ _ ty body => ingressExprWork (ty :: body :: rest) (total + 2)
    | .letE _ ty value body => ingressExprWork (ty :: value :: body :: rest) (total + 2)
    | .prj _ _ value => ingressExprWork (value :: rest) (total + 2)
    | _ => ingressExprWork rest (total + 1)
termination_by ingressExprPendingSize pending
decreasing_by
  all_goals simp [ingressExprPendingSize]
  all_goals first | omega | skip
  all_goals rename_i expr; cases expr <;> simp <;> omega

/-- All sharing-table expansions, each with its cache-completion frame. -/
def ingressSharingWork (sharing : Array Ixon.Expr) : Nat :=
  sharing.foldl (fun total expr => ingressExprWork [expr] (total + 1)) 0

def ingressExprWorkBudget (root : Ixon.Expr) (sharing : Array Ixon.Expr) : Nat :=
  ingressExprWork [root] (ingressSharingWork sharing)

/-- Logical universe work-list measure, also erased from the runtime walk. -/
noncomputable def ingressUnivPendingSize : List Ixon.Univ → Nat
  | [] => 0
  | u :: rest => sizeOf u + ingressUnivPendingSize rest

def ingressUnivWork (pending : List Ixon.Univ) (total : Nat := 0) : Nat :=
  match pending with
  | [] => total
  | u :: rest => match u with
    | .succ inner => ingressUnivWork (inner :: rest) (total + 2)
    | .max a b | .imax a b => ingressUnivWork (a :: b :: rest) (total + 2)
    | _ => ingressUnivWork rest (total + 1)
termination_by ingressUnivPendingSize pending
decreasing_by
  all_goals simp [ingressUnivPendingSize]
  all_goals first | omega | skip
  all_goals rename_i level; cases level <;> simp <;> omega

end Ix.Kernel

end
end
