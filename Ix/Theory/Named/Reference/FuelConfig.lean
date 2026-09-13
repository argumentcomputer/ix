/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Lean.Data.Json.FromToJson

namespace Ix.Theory.Named

/--
Bounds for the various fixed-fuel loops inside the kernel.

Every field is a positive `Nat`; on exhaustion the corresponding loop throws
`.deterministicTimeout` (whnf-family) or `.deepRecursion` (structural /
mutual-recursion loops).

Defaults are set so mathlib passes. Since lean4#13956 the native kernel bounds
its mutually recursive type-checker entry points using `maxRecDepth`.
The named reference implementation instead keeps separate, explicit fuel for those calls and for loops
that need structural termination witnesses; these counters also provide a
deterministic defensive check against runaway reductions.
-/
structure FuelConfig where
  /-- `whnf'` unfold-loop, non-eager path (`TypeChecker.lean` whnf'). -/
  whnf        : Nat := 100000
  /-- `whnf'` unfold-loop, `eagerReduce` path. -/
  whnfEager   : Nat := 1000000
  /-- `lazyDeltaReduction.loop`. -/
  lazyDelta   : Nat := 1000
  /-- `etaExpand.loop.loop2`. -/
  etaExpand   : Nat := 1000
  /-- Starting fuel for `Methods.withFuel` (bounds mutual whnf/isDefEq depth). -/
  recDepth    : Nat := 10000
  /-- Shared fuel for the structural loops in `Inductive/Add.lean`. -/
  inductiveFuel : Nat := 1000
  /-- Upper bound, in bytes, on the `Nat` numerals the kernel will accept or compute while
  reducing `Nat` literals. Bounds the memory and time a single reduction can consume. The
  native kernel spells this bound `LEAN_NAT_MAX_SIZE` and defaults it to the same 128 MB. -/
  natMaxSize : Nat := 134217728 -- 128 MB; a literal so `simp` cannot renormalize it
  deriving Repr, Inhabited, Lean.FromJson, Lean.ToJson
