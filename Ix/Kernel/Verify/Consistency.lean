/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Level
import Ix.Kernel.Verify.Consistency.Expr
import Ix.Kernel.Verify.Consistency.Judgment
import Ix.Kernel.Verify.Consistency.Infer
import Ix.Kernel.Verify.Consistency.InstUniv
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.Atomic
import Ix.Kernel.Verify.Consistency.ScopedExpr
import Ix.Kernel.Verify.Consistency.Context
import Ix.Kernel.Verify.Consistency.BinderOpening
import Ix.Kernel.Verify.Consistency.Application
import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Kernel.Verify.Consistency.Production
import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.Audit

/-!
# Refinement into the set-theoretic consistency model

This library connects production kernel operations to `Ix.Theory`. Each
transport keeps its representation, arithmetic, and dependency assumptions
explicit. A production `checkEnvAnon` fragment preserves models of its
axiom set for monomorphic aliases, closed sorts, monomorphic specializations of
polymorphic constants, and closed function bodies built from sorts, locals,
monomorphic references, applications, dependent functions, and full-mode lambdas
under the stated execution resources.
Constant inference supports arbitrary readable entry types, using the actual
universe-instantiation walker and explicit lookup and finite-support resources.
The returned type's scope and references justify declaration admission.
The binder case also requires explicit syntactic scope and references to the
preceding interface. Its separate declared-type inference turns semantic checking
into typing. Local cache hits agree with the actual declaration type; other
inference nodes retain cache-miss boundaries.
Applications use syntactic Pi exposure, full argument checking, hash conversion,
and the ordinary eager-marker path. Constant- and local-headed spines derive
type validity from the admitted model or local context; their arguments may be lambdas.
General checker soundness remains outside this fragment.
-/
