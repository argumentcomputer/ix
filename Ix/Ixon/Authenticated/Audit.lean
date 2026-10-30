import Ix.Ixon.Authenticated.Theorems
import Ix.Ixon.Projection.Audit

/-! # The authenticated entries' boundary

The instantiation at BLAKE3 adds exactly one thing to the generic entries'
compiled closures: the admission hash's substitution, `Address.admissionHash`
executed as `Address.blake3`, with the Rust backend's foreign primitives it
reaches. The runtime audit admits it only as the ruled assumption
`Ix.Kernel.Audit.assumedSubstitutions`, and fails without it; the
instantiated entries are the generic ones applied to the admission hash
(their definitions are frozen below), so the hash argument is the only way
the foreign primitives enter. The import closure is the root library's
(`Ix.Address` brings `Lean`); the generic entries keep their hash-free
import fence (`Ixon.Projection.Audit`). -/

namespace Ixon.Authenticated.Audit

/-- The authenticated entries, and the admission hash itself (whose
`implemented_by` the closure reports). -/
def operations : Array Lean.Name :=
  #[``Ixon.Authenticated.checkBytes, ``Ixon.Authenticated.checkBytesProjection,
    ``Address.admissionHash]

/-- The kernel's rulings and exactly the one assumed substitution. -/
def rulings : Ix.Kernel.Audit.RuntimeRulings :=
  { Ix.Kernel.Audit.runtimeRulings with assumed := Ix.Kernel.Audit.assumedSubstitutions }

/-- The generic entries the instantiation applies. -/
def generic : Array Lean.Name :=
  Ix.Kernel.Admission.Audit.operations ++ Ixon.Projection.Audit.operations

end Ixon.Authenticated.Audit

-- Step 5a (typed keys) moved the count from 5839 by the generic entries' change
-- (`IxC/Kernel/Audit/Roots.lean`); step 5b's `LetMeta` from 5630, by the let
-- contract's equality, hash and `Repr`; step 5b's walk change from 5657, by the
-- sources of the arity-reduced `f._redArg` the walk reaches (no extern, `unsafe`,
-- `csimp` or `partial` constant among them); step 5b's mode index from 5752, by
-- the generic entries' change; its address keys from 5764 and 115 inherited
-- externs, by the generic entries' change; the IxC performance series (PERF
-- P16, P14, P3, P2) from 5727 and 117 inherited externs, by the generic
-- entries' change (`IxC/Kernel/Audit/Roots.lean`); step 6's structured errors
-- from 5745 and 119 inherited externs, by the generic entries' change; the
-- validation of the four install anchors from 5963, by the generic entries' change;
-- step 6b's display annotations from 5974, by the generic entries' change (8
-- more, one more ruled csimp), and its failure display from 5982 (30 more, one
-- more ruled csimp); the reader's conversion to Lean `module`s from 6012, by the
-- generic entries' change (29 more, the block-order entry's); the block
-- order's `let` key (a `let`'s nondependency bit,
-- `Ixon.BlockOrder.compareExpr_letE`) from 6041, by `compareExpr`'s own
-- compiler-generated lambdas (`Ix/Ixon/BlockOrder/Audit.lean`); CQX.8's field test in
-- the in-model generator from 6043, by the generic entries' change (4 of
-- `genNested`'s specialisations gone, `IxC/Kernel/Audit/Roots.lean`); (A)
-- (`ALPHA-COLLAPSE.md` §8.2) from 6039, by the generic entries' change (122 out:
-- the compiler-trust roles and their checks, `IxC/Kernel/Audit/Roots.lean`); the
-- `.indDecl` shape guard from 5917, by the generic entries' change (44 in: the guard,
-- its memoized walk and their specialisations; one more csimp, ruled,
-- `IxC/Kernel/Audit/Roots.lean`); the mutual modeller's reading of Lean's recursive
-- fields from 5961, likewise (9 more); the rest-only hoist and the decided units
-- check (S1) from 5970, by the generic entries' change (117 in,
-- `IxC/Kernel/Audit/Roots.lean`); the prelude's
-- shape check (S1, fact (ii)) from 6087, likewise (12 in); the hoist guard
-- (S1) from 6099, likewise (4 in); the in-model generator's totality (S1)
-- from 6103, likewise (15 more; its nine ruled `partial` definitions are total,
-- and the ruling is gone); the prelude-copy check ((b), `State.keepsPrelude` in
-- `readStream`) from 6118, likewise (38 in: the check, the state's keys and the derived
-- `DecidableEq` it compares with; externs, `unsafe` and csimp unchanged).
-- The committed fallback recursor guard (2026-10-22) adds seven compiled
-- functions to each entry closure. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Module visibility compiles one additional specialization,
-- Option.instBEq.beq._at_.Ixon.BlockOrder.checkMotives.spec_0,
-- instead of reusing Reader.buildIndex's Option Nat equality helper.
-- Its IR is identical after symbol renaming. Measured +1 against the
-- archived pre-header modules; extern/unsafe/opaque/substitution and
-- csimp sets and every ruling count are unchanged (2026-10-22).
-- Keeping the fallback's recursors off the input's blocks (`fallbackIndexed`, `indexedRecords`,
-- through `contextOf`) adds four compiled functions. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Declining an inductive read whose declarations repeat a name (`lowerInductive` over
-- `lowerInductiveDecls`) adds 11 compiled functions, the entry's
-- (`IxC/Kernel/Audit/Roots.lean`). Measured against a walk that stops at the guard; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Removing the block-order entry (`checkBytesBlockOrder`: every block is stored in its
-- source's order, so the structural order check is gone) removes 141 compiled functions
-- (6179 to 6038) and the one extern only it reached, `String.compare` (117 to 116);
-- implemented_by, unsafe, csimp and all ruling counts are unchanged. Measured before
-- refreezing.
-- Leaving out of the index an input recursor filed under a block only the fallback supplies
-- (`inputIndexed`) adds 32 compiled functions, the reader's (`IxC/Kernel/Audit/Roots.lean`):
-- the predicate and the derived equality of `Ixon.Constant` that compares a record with the
-- fallback's. Measured before refreezing; externs, implemented_by, unsafe, csimp and all
-- ruling counts are unchanged.
-- The role-shape validation merge adds the entry's four compiled functions
-- (`IxC/Kernel/Audit/Roots.lean`), measured with the fallback-record guard.
-- Execution allowances are unchanged.
-- The expanded role and evidence catalog adds 811 compiled functions and removes
-- eight specializations in both authenticated closures: 495 role helpers, 208
-- key helpers and 108 fixture helpers are added. Every extern, unsafe, direct
-- and reached implementation, csimp, replacement and opaque entry is unchanged.
-- Auditing `@[csimp]` replacements whose target was inlined into its caller
-- records one more proved `csimp` in `Ix.Kernel.Cached` (26 -> 27; see
-- `IxC/Kernel/Audit/Roots.lean`).
/-- info: runtime closure of [Ixon.Authenticated.checkBytes,
 Ixon.Authenticated.checkBytesProjection,
 Address.admissionHash]: 6877 compiled functions; inherited externs 116, implemented_by 1, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 27 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.Authenticated.Audit.operations #[`Init, `Std] Ixon.Authenticated.Audit.rulings

-- Without the assumption the closure fails on the substitution and its primitives.
/-- error: project-level execution replacements reached from [Ixon.Authenticated.checkBytes,
 Ixon.Authenticated.checkBytesProjection,
 Address.admissionHash]:
[Address.admissionHash, Blake3.Rust.hasherFinalize, Blake3.Rust.hasherInit, Blake3.Rust.hasherUpdate] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.Authenticated.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

/-- info: Additional authenticated-entry externs: [Blake3.Rust.hasherFinalize, Blake3.Rust.hasherUpdate, Blake3.Rust.hasherInit]
---
info: Additional authenticated-entry implemented_by: [(Address.admissionHash, Address.blake3)]
---
info: Additional authenticated-entry unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ixon.Authenticated.Audit.generic
  let after := Ix.Kernel.Audit.runtimeClosure env Ixon.Authenticated.Audit.operations
  Lean.logInfo m!"Additional authenticated-entry externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional authenticated-entry implemented_by: {after.implementedBy}"
  Lean.logInfo m!"Additional authenticated-entry unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"

/-! ## The instantiation -/

/-- info: def Address.admissionHash : ByteArray → Address :=
fun x => Address.blake3Pure x -/
#guard_msgs (whitespace := lax) in
#print Address.admissionHash

/-- info: def Ixon.Authenticated.checkBytes : Ix.Kernel.Admission.Binding →
  Ix.Kernel.Admission.Limits →
    Ix.Kernel.Admission.Records →
      Ix.Kernel.Ingress.Blobs →
        (optParam (Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) fun x => none) →
          Except Ix.Kernel.Admission.Error (Ix.Kernel.Env Ix.Kernel.Mode.anon) :=
fun binding limits records blobs hint =>
  Ix.Kernel.Admission.checkBytes Address.admissionHash binding limits records blobs hint -/
#guard_msgs (whitespace := lax) in
#print Ixon.Authenticated.checkBytes

/-- info: def Ixon.Authenticated.checkBytesProjection : Ix.Kernel.Admission.Binding →
  Nat →
    Ix.Kernel.Admission.Limits →
      Ix.Kernel.Admission.Records →
        Ix.Kernel.Ingress.Blobs →
          (optParam (Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) fun x => none) →
            Except Ixon.Projection.CheckError (Ix.Kernel.Env Ix.Kernel.Mode.anon) :=
fun binding maxProjections limits records blobs hint =>
  Ixon.Projection.checkBytes Address.admissionHash binding maxProjections limits records blobs hint -/
#guard_msgs (whitespace := lax) in
#print Ixon.Authenticated.checkBytesProjection

#guard_kernel_axioms Address.admissionHash_eq [propext, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.admissionHash_width [propext, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_no_proof_of_False [propext, Classical.choice, Quot.sound]

/-! ## The statements at BLAKE3 -/

/-- info: @Ixon.Authenticated.checkBytes_authentic : ∀ {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.Authenticated.checkBytes binding limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic Address.blake3Pure records blobs ∧ Address.blake3Pure binding.bytes = binding.address -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytes_authentic

/-- info: Ixon.Authenticated.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.Authenticated.checkBytes binding limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytes_has_model

/-- info: Ixon.Authenticated.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.Authenticated.checkBytes binding limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const (Ix.Kernel.roleKey Ix.Kernel.Role.false) [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytes_no_proof_of_False

/-- info: @Ixon.Authenticated.checkBytesProjection_authentic : ∀ {binding : Ix.Kernel.Admission.Binding} {maxProjections : Nat}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.Authenticated.checkBytesProjection binding maxProjections limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output,
        Ix.Kernel.Admission.Hashed Address.blake3Pure output ∧
          Ix.Kernel.Admission.checkConstantsAt Address.blake3Pure binding output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytesProjection_authentic

/-! ## The tiered entry at BLAKE3 (the typing tier)

The tiered entry's closure is frozen apart, so the entries' above is
unchanged: the generic tiered entries' (`Ix.Kernel.Audit.tierOperations`)
and the same one assumed substitution: 5878 and 10 more, the Rust BLAKE3
backend's three externs among them (ruled assumed 4). Step 6b's display
annotations moved it from 5888 by the generic tiered entries' change (8 more,
one more ruled csimp), and its failure display from 5896, likewise (33 more,
one more ruled csimp). The reader's conversion to Lean `module`s moved it from 5929,
likewise (28 more), and the tier fold's unsafe stage (U1) from 5957, likewise (10
more: the fold's split by kind and the staging; `IxC/Kernel/Audit/Roots.lean`), and the
tiered Ixon entry's routing of unsafe records (U1) from 5967, likewise (12 more: the
partition's safety and the tier reader's unsafe opaque and axiom branches), and CQX.8's
field test in the in-model generator from 5979, likewise (4 of `genNested`'s
specialisations gone), and (A) (`ALPHA-COLLAPSE.md` §8.2) from 5975, likewise (122
out: the compiler-trust roles and their checks), and the `.indDecl` shape guard from
5853, likewise (44 in: the guard, its memoized walk and their specialisations; one more csimp, ruled),
and the mutual modeller's reading of Lean's recursive fields from 5897, likewise (9 more),
and the rest-only hoist and the decided units check (S1) from 5906, likewise (117 in),
and the prelude's shape check (S1, fact (ii)) from 6023, likewise (12 in),
and the hoist guard (S1) from 6035, likewise (4 in),
and the in-model generator's totality (S1) from 6039, likewise (15 more; its nine ruled
`partial` definitions are total, and the ruling is gone),
and the admission chain's conversion to Lean `module`s (step 10c) from 6054, likewise
(codegen only: the partition's `HashSet` specialisations, 7 in and 1 out, and `wordC`
under its public name; externs, `unsafe` and csimp unchanged),
and the prelude-copy check ((b), `State.keepsPrelude` in `readStream`) from 6060, likewise
(38 in: the check, the state's keys and the derived `DecidableEq` it compares with). -/

-- Keeping the fallback's recursors off the input's blocks (`fallbackIndexed`, `indexedRecords`,
-- through `contextOf`) adds four compiled functions. Measured before refreezing; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Declining an inductive read whose declarations repeat a name (`lowerInductive` over
-- `lowerInductiveDecls`) adds 11 compiled functions, the entry's
-- (`IxC/Kernel/Audit/Roots.lean`). Measured against a walk that stops at the guard; externs,
-- implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- Leaving out of the index an input recursor filed under a block only the fallback supplies
-- (`inputIndexed`) adds 32 compiled functions, the reader's, as above. Measured before
-- refreezing; externs, implemented_by, unsafe, csimp and all ruling counts are unchanged.
-- The role-shape validation merge adds the same four compiled functions,
-- measured with the fallback-record guard. Execution allowances are unchanged.
/-- info: runtime closure of [Ixon.Authenticated.checkBytesTiered]: 6959 compiled functions; inherited externs 116, implemented_by 0, unsafe 26, csimp 7; ruled assumed 4, computed_field 21, csimp 27 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ixon.Authenticated.checkBytesTiered] #[`Init, `Std] Ixon.Authenticated.Audit.rulings

#guard_kernel_axioms Ixon.Authenticated.checkBytesTiered [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesTiered_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesTiered_typed [propext, Classical.choice, Quot.sound]
