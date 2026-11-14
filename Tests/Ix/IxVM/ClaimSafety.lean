import Ix.Meta
import Ix.Check
import Ix.Shard.Environment
import Ix.IxVM.ClaimHarness
import Tests.Ix.IxVM.Harness

/-!
# Typing claims on constants outside Lean's logic

A typing claim certifies its seeds, a `check` target or a `checkEnv` claim's
owned leaves, only in Lean's logic. IxVM refuses a seed whose record, or the
block it projects from, is unsafe or partial (`KernelClaim::assert_claimable`):
Lean's kernel accepts an unsafe constant of any type, `False` included, and a
`partial` block (Lean's `_unsafe_rec` companions) may refer to itself. The face
of a `partial def` is a safe opaque and stays claimable. The claim builders
leave the others out of seed and owned lists (`IxVM.ClaimHarness.claimableOwned`,
`Ix.Shard.ownedConstsPer`, `Ix.Check.outsideLogicError?`).

The fixtures are compiled from Lean: `Tests.Ix.Kernel.EntryCaseDefs` (its own
library, `EntryCaseFixtures`, loaded at run time), `IxVMInd.UnsafeSquash`
(`Tests.Ix.IxVMFixtures`) and `Init`'s partial `Lean.extractMainModule`.

- **Refused** (`check`): an unsafe definition, and one of `False`; an unsafe
  opaque; an unsafe axiom of `False`; a partial definition (`loop._unsafe_rec`);
  a member of a mutual partial block (`ping._unsafe_rec`), and the block itself;
  the self-referential partial definition `badFalse : False := badFalse`; an
  unsafe inductive, its constructor and its recursor; and
  `Lean.extractMainModule._unsafe_rec`. Each is refused at the seed, before the
  walk, with `claim seed is unsafe or partial`.
- **Refused** (`checkEnv`): a shard whose owned tree holds `loop._unsafe_rec`
  beside the safe `loop`.
- **Refused**: the inert axiom `Lean.trustCompiler` as a `check` target and
  among a `checkEnv` claim's owned leaves, with `claim seed is an inert axiom`:
  an inert axiom installs nothing and may have no model.
- **Accepted**: the safe opaques `loop` and `ping`, and the shard claims the
  builder makes from the same owned lists, which leave `loop._unsafe_rec` and
  `Lean.trustCompiler` out.

Beside the circuit cases, the host side is checked without running the
program: `Ixon.Env.outsideLogicAt` agrees with Lean's own flags on every
fixture, the shard owner and the claim builder leave out the refused seeds and
the inert axioms with the constants that use one (`inertUsers`), and every
walk edge from a constant in Lean's logic lands on one (so the owned sets
stay closed). `corpus` checks the last on a compiled corpus.
-/

namespace Tests.Ix.IxVM.ClaimSafety

open IxVM.ClaimHarness

/-- A name from its dotted form, numeric components as numbers. -/
private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none => .mkStr acc s

private def defs (n : String) : Lean.Name := `Tests.Ix.Kernel.EntryCaseDefs ++ n.toName

/-- The seeds IxVM must refuse. -/
def refused : List (String × Lean.Name) := [
  ("an unsafe definition", defs "unsafeSucc"),
  ("an unsafe definition of False", defs "unsafeFalse"),
  ("an unsafe opaque", defs "unsafeOpq"),
  ("an unsafe axiom of False", defs "unsafeAx"),
  ("a partial definition", defs "loop._unsafe_rec"),
  ("a member of a mutual partial block", defs "ping._unsafe_rec"),
  ("a self-referential partial definition of False", defs "badFalse"),
  ("an unsafe inductive", `IxVMInd.UnsafeSquash),
  ("an unsafe inductive's constructor", `IxVMInd.UnsafeSquash.mk),
  ("an unsafe inductive's recursor", `IxVMInd.UnsafeSquash.rec),
  ("Init's partial companion",
    nameOfString "_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec")]

/-- The seeds IxVM must accept: the safe opaques of `partial def`s. -/
def accepted : List (String × Lean.Name) := [
  ("the safe opaque of a partial definition", defs "loop"),
  ("the safe opaque of a mutual partial definition", defs "ping")]

/-- The message `KernelClaim::assert_claimable` refuses a seed with. -/
def seedMessage : String := "claim seed is unsafe or partial"

/-- The inert axioms of the environment's binding and the constants that use one
(`inertUsers`): no claim names them. -/
def inertNames : List Lean.Name :=
  [``sorryAx, ``Lean.trustCompiler, ``Lean.reduceBool, ``Lean.reduceNat, ``Lean.ofReduceBool,
    ``Lean.ofReduceNat]

/-- The message `KernelClaim::assert_claimable` refuses an inert axiom with. -/
def inertSeedMessage : String := "claim seed is an inert axiom"

/-- The walk edges of `env` from a constant in Lean's logic to one outside it,
with the number of constants outside it. None means that an owned set without
the constants outside Lean's logic loses nothing its claim walk reaches. -/
def logicEdgeViolations (env : Ixon.Env) : Array (Address × Address) × Nat := Id.run do
  let aside := env.outsideLogicRecords
  let outside (a : Address) (c : Ixon.Constant) : Bool := aside.contains (c.ownerAt a)
  let mut bad : Array (Address × Address) := #[]
  let mut count := 0
  for (a, lc) in env.consts do
    let some c := lc.get? | continue
    if outside a c then
      count := count + 1
      continue
    for e in walkEdges c do
      if let some ce := env.getConst? e then
        if outside e ce then bad := bad.push (a, e)
  return (bad, count)

/-- The host side: the predicate against Lean's flags, the owner, the claim
builder, `ix check`'s refusal and the closure of what stays owned. -/
def hostChecks (leanEnv : Lean.Environment) (env : Ixon.Env)
    (addrOf : Lean.Name → Except String Address) : Except String Unit := do
  let flagged (n : Lean.Name) : Bool := (leanEnv.find? n).any fun ci => ci.isUnsafe || ci.isPartial
  for (label, n) in refused do
    let a ← addrOf n
    unless flagged n do throw s!"{n} ({label}) is not unsafe or partial in Lean"
    unless env.outsideLogicAt a do throw s!"{n} ({label}) is not outside Lean's logic"
    if (Ix.Check.outsideLogicError? env label a).isNone then
      throw s!"ix check would not refuse {n} ({label})"
  for (label, n) in accepted do
    let a ← addrOf n
    if flagged n then throw s!"{n} ({label}) is unsafe or partial in Lean"
    if env.outsideLogicAt a then throw s!"{n} ({label}) is outside Lean's logic"
    if (Ix.Check.outsideLogicError? env label a).isSome then
      throw s!"ix check would refuse {n} ({label})"
  -- one shard owning every block: the refused seeds are owned by nobody, the
  -- accepted ones are owned
  let blocks : Array Address := env.consts.fold (init := #[]) fun acc a lc =>
    match lc.get? with
    | some c => if c.ownerAt a == a then acc.push a else acc
    | none => acc
  let owned := (Ix.Shard.ownedConstsPer env #[blocks])[0]!
  for (label, n) in refused do
    if owned.contains (← addrOf n) then throw s!"the shard owner kept {n} ({label})"
  for (label, n) in accepted do
    unless owned.contains (← addrOf n) do throw s!"the shard owner dropped {n} ({label})"
  -- the inert axioms and the constants that use one: owned by nobody and refused by
  -- `ix check`; the accepted seeds use none
  let inert := inertUsers env
  for n in inertNames do
    let a ← addrOf n
    unless inert.contains a do throw s!"{n} is not among the constants that use an inert axiom"
    if owned.contains a then throw s!"the shard owner kept {n}"
    if (Ix.Check.seedError? env inert (toString n) a).isNone then
      throw s!"ix check would not refuse {n}"
  for (label, n) in accepted do
    if inert.contains (← addrOf n) then throw s!"{n} ({label}) uses an inert axiom"
  unless owned.size == (claimableConsts env).size do
    throw s!"the shard owns {owned.size} constants, {(claimableConsts env).size} are claimable"
  -- the claim builder: an owned list of refused seeds alone has no claim, and
  -- the loop pair's claim is the safe face's alone
  let loopA ← addrOf (defs "loop")
  let loopRecA ← addrOf (defs "loop._unsafe_rec")
  if (claimableOwned env #[loopRecA]).toOption.isSome then
    throw "the claim builder made a claim over loop._unsafe_rec alone"
  let (pair, _) ← shardCheckEnvClaimTrees env #[loopA, loopRecA] true
  let (face, _) ← shardCheckEnvClaimTrees env #[loopA] true
  unless pair == face do throw "the claim builder kept loop._unsafe_rec"
  -- the canonical whole-environment tree has no refused seed
  let some tree := envCanonicalTree env | throw "the environment has no tree"
  for (label, n) in refused do
    if tree.leaves.contains (← addrOf n) then throw s!"envCanonicalTree kept {n} ({label})"
  for n in inertNames do
    if tree.leaves.contains (← addrOf n) then throw s!"envCanonicalTree kept {n}"
  -- the claim builder leaves an inert axiom out of an owned list
  let trustA ← addrOf ``Lean.trustCompiler
  if (claimableOwned env #[trustA]).toOption.isSome then
    throw "the claim builder made a claim over Lean.trustCompiler alone"
  let (bad, _) := logicEdgeViolations env
  unless bad.isEmpty do
    throw s!"{bad.size} walk edge(s) from a constant in Lean's logic reach one outside it \
      (first {(bad[0]!).1} → {(bad[0]!).2})"

def run : IO UInt32 := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs, `Tests.Ix.IxVMFixtures]
  let names := (refused ++ accepted).map (·.2)
  let missing := names.filter (!leanEnv.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-claim-safety] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names.toArray leanEnv
  let addrOf (n : Lean.Name) : Except String Address :=
    match env.getAddr? (Ix.Name.fromLeanName n) with
    | some a => pure a
    | none => throw s!"{n} is not in the Ixon environment"
  match hostChecks leanEnv env addrOf with
  | .ok () => IO.println "[ixvm-claim-safety] host checks passed"
  | .error e =>
    IO.eprintln s!"[ixvm-claim-safety] host check failed: {e}"
    return 1
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let check (label : String) (a : Address) (accept : Bool) : Builder := fun _ =>
    Case.ofClaim label env (.check ctx a none) {} accept
      (if accept then none else some seedMessage)
  let mut cases : Array Builder := #[]
  for (label, n) in refused do
    let a ← IO.ofExcept (addrOf n)
    cases := cases.push (check s!"refuse {label} ({n})" a false)
  -- the partial block itself, through its member's projection record
  let pingRec ← IO.ofExcept (addrOf (defs "ping._unsafe_rec"))
  match env.getConst? pingRec with
  | some c =>
    if c.ownerAt pingRec == pingRec then
      IO.eprintln "[ixvm-claim-safety] ping._unsafe_rec is not a block member"
      return 1
    cases := cases.push (check "refuse a mutual partial block" (c.ownerAt pingRec) false)
  | none =>
    IO.eprintln "[ixvm-claim-safety] ping._unsafe_rec has no record"
    return 1
  for (label, n) in accepted do
    let a ← IO.ofExcept (addrOf n)
    cases := cases.push (check s!"accept {label} ({n})" a true)
  -- a shard whose owned tree holds a partial companion beside its face
  let loopA ← IO.ofExcept (addrOf (defs "loop"))
  let loopRecA ← IO.ofExcept (addrOf (defs "loop._unsafe_rec"))
  let some ownedTree := Ix.AssumptionTree.canonical #[loopA, loopRecA]
    | IO.eprintln "[ixvm-claim-safety] no owned tree"; return 1
  let trees := ({} : Std.HashMap Address Ix.AssumptionTree).insert ownedTree.root ownedTree
  cases := cases.push fun _ =>
    Case.ofClaim "refuse a checkEnv shard owning loop._unsafe_rec" env
      (.checkEnv ctx ownedTree.root none) trees false (some seedMessage)
  -- the builder's claim over the same owned list leaves the companion out
  cases := cases.push fun _ => do
    let (_, witness) ← buildShardCheckEnvWitness env #[loopA, loopRecA] (assumeBinding := true)
    return { label := "accept the builder's shard over loop and loop._unsafe_rec", accept := true,
             witness }
  -- an inert axiom among a checkEnv claim's owned leaves, and among a check target
  let trustA ← IO.ofExcept (addrOf ``Lean.trustCompiler)
  let some inertTree := Ix.AssumptionTree.canonical #[loopA, trustA]
    | IO.eprintln "[ixvm-claim-safety] no owned tree"; return 1
  let inertTrees := ({} : Std.HashMap Address Ix.AssumptionTree).insert inertTree.root inertTree
  cases := cases.push fun _ =>
    Case.ofClaim "refuse a checkEnv shard owning Lean.trustCompiler" env
      (.checkEnv ctx inertTree.root none) inertTrees false (some inertSeedMessage)
  cases := cases.push fun _ =>
    Case.ofClaim "refuse a check of Lean.trustCompiler" env (.check ctx trustA none) {} false
      (some inertSeedMessage)
  -- the builder's claim over the same owned list leaves the inert axiom out
  cases := cases.push fun _ => do
    let (_, witness) ← buildShardCheckEnvWitness env #[loopA, trustA] (assumeBinding := true)
    return { label := "accept the builder's shard over loop and Lean.trustCompiler", accept := true,
             witness }
  Tests.Ix.IxVM.runCases "ixvm-claim-safety" cases

/-- The closure of what stays owned on a compiled corpus (`IX_SAFETY_IXE`, an
`.ixe`): every walk edge from a constant in Lean's logic lands on one, so a
shard that leaves out the constants outside it loses nothing its walk reaches.
With `IX_SAFETY_IXES` (a manifest of that environment), each shard's owned
count before and after. -/
def corpus : IO UInt32 := do
  let some path ← IO.getEnv "IX_SAFETY_IXE"
    | IO.eprintln "[ixvm-claim-safety-corpus] set IX_SAFETY_IXE to a .ixe"; return 1
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  let started ← IO.monoMsNow
  let (bad, aside) := logicEdgeViolations env
  IO.println s!"[ixvm-claim-safety-corpus] {path}: {env.consts.size} constants, {aside} outside \
    Lean's logic (unsafe or partial, or projected from such a block), {bad.size} walk edge(s) \
    from a constant in Lean's logic to one outside it, {(← IO.monoMsNow) - started} ms"
  for (a, e) in bad.extract 0 20 do
    IO.println s!"  {a} → {e}"
  if let some ixes ← IO.getEnv "IX_SAFETY_IXES" then
    let shards ← IO.ofExcept (Ix.Shard.parseIxesAllShards (← IO.FS.readBinFile ixes))
    let owned := Ix.Shard.ownedConstsPer env shards
    let records := env.consts.fold (init := (({} : Std.HashMap Address Nat))) fun m a lc =>
      match lc.get? with
      | some c => m.insert (c.ownerAt a) (m.getD (c.ownerAt a) 0 + 1)
      | none => m
    for (blocks, k) in shards.mapIdx fun k b => (b, k) do
      let all := blocks.foldl (fun n b => n + records.getD b 0) 0
      IO.println s!"  shard {k}: {all} constants, {(owned[k]?.map (·.size)).getD 0} owned"
  return if bad.isEmpty then 0 else 1

end Tests.Ix.IxVM.ClaimSafety
