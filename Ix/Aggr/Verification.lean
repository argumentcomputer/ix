module
public import Ix.Aggr.Host
public import Ix.Ixon

/-! Content-addressed aggregate wrappers and their environment interpretation. -/

public section
namespace Aggr

/-- Decode a proof wrapper only after checking that its bytes reproduce the
content address supplied by the caller. `Store.read` selects a path by address
but deliberately does not re-hash ordinary store objects. -/
def decodeAggregateWrapperAt (proofAddr : Address) (bytes : ByteArray) :
    Except String Ixon.Proof := do
  let actual := Address.blake3 bytes
  if actual != proofAddr then
    throw s!"aggregate proof store object {proofAddr} hashes to {actual}"
  Ixon.Proof.de bytes

/-- Establish the per-constant interpretation of an aggregate root. A valid
proof of `CheckEnv(subjects.root, none)` certifies every subject leaf, so this
single linear audit checks that those leaves are exactly the constants in the
supplied environment: no omissions, foreign leaves, or duplicates.

With `base := some R`, the root is instead conditional: its assumptions must be
exactly `some R`, as a rebase (shape 13) onto the subjects root `R` outputs,
and the audit certifies the subjects only provided every leaf under `R` is
well-typed. The default rejects any assumption.

For an extension environment, `baseConstants` are the base constants it holds:
they are excluded from the constants the subjects must cover, and a subject
that is one of them counts as foreign. -/
def auditAggregateConstants (env : Ixon.Env) (statement : Aggr.CheckEnvTrees)
    (base : Option Address := none) (baseConstants : Std.HashSet Address := {}) :
    Except String Nat := do
  match base, statement.assumptions with
  | none, none => pure ()
  | none, some assumptions =>
    throw s!"aggregate root retains undischarged assumptions {assumptions.root}"
  | some base, none =>
    throw s!"aggregate root has no assumptions, but base {base} was declared"
  | some base, some assumptions =>
    if assumptions.root != base then
      throw s!"aggregate root assumes {assumptions.root}, not the declared \
        base {base}"
  let leaves := statement.subjects.leaves
  let mut seen : Std.HashSet Address := {}
  let mut duplicates := 0
  let mut foreign := 0
  let mut firstDuplicate : Option Address := none
  let mut firstForeign : Option Address := none
  for address in leaves do
    if seen.contains address then
      duplicates := duplicates + 1
      if firstDuplicate.isNone then firstDuplicate := some address
    else
      seen := seen.insert address
    if !env.consts.contains address || baseConstants.contains address then
      foreign := foreign + 1
      if firstForeign.isNone then firstForeign := some address
  let mut missing := 0
  let mut firstMissing : Option Address := none
  let mut owned := 0
  for (address, _) in env.consts do
    if baseConstants.contains address then continue
    owned := owned + 1
    if !seen.contains address then
      missing := missing + 1
      if firstMissing.isNone then firstMissing := some address
  if duplicates != 0 || foreign != 0 || missing != 0 then
    let sample (address : Option Address) := address.map toString |>.getD "none"
    throw s!"aggregate constant audit failed: {missing} missing \
      (first {sample firstMissing}), {foreign} foreign \
      (first {sample firstForeign}), {duplicates} duplicate occurrence(s) \
      (first {sample firstDuplicate}); environment has {owned} constants, \
      subject tree has {leaves.size} leaves"
  if leaves.size != owned then
    throw s!"aggregate constant audit cardinality mismatch: environment has \
      {owned} constants, subject tree has {leaves.size} leaves"
  pure owned


end Aggr
end
