module

public import Ix.CompileDriver

/-! # The compiler as a pure function

`compile` is the function the certification statements (`Ix.Cert.Statement`)
are about. It is the compile pipeline after canonicalization, as
`Ix.CompileM.compileDecoratedConsts` runs it, with the same stages:

1. the reference graph (`Ix.GraphM`);
2. the ground filter: the immediately ungrounded constants
   (`Ix.groundConstCheck`), spread through the reverse graph
   (`Ix.proliferateUngrounded`), are removed from the graph together with
   every edge into them (`Ix.groundConsts` composes the two);
3. the condensation (`Ix.CondenseM.run`), which `blocksOf` names because the
   Source-mode statements group by it too;
4. the aux-aware driver, `Ix.CompileM.compileEnvAux`.

Its input is `Ix.Environment`, `Ix.CanonM`'s output, which is also Source
mode's input (`Ix.LeanIngress`). Only `env.consts` is read: the streaming
fallback (`Ix.Environment.fallback?`) is dropped.

Every content address it computes (each record, projection and blob) is
`Address.admissionHash`, the hash the authenticated entries check: pure
BLAKE3 (`Address.blake3Pure`) in the logic, executed as the Rust BLAKE3
(`Address.blake3`). The structural hashes of `Ix.Name`, `Ix.Level` and
`Ix.Expr`, which are map keys and never authenticated, stay the Rust
BLAKE3's.

What the IO pipeline does that this function does not:
* it starts from Lean's constants: it resolves source contracts
  (`Ix.Compile.CompileInput.prepare`), refuses unresolved binder contracts,
  inspects semantic contracts and canonicalizes (`Ix.CanonM`) itself;
* it compiles against a hybrid environment, in which theorem and opaque
  bodies are canonicalized again on demand (`fallback?`) instead of
  materialized, and passes the name-hash index (`CompileEnv.nameByHash`)
  that such an environment needs;
* it schedules the driver in parallel waves (`compileEnvParallelAux`) and
  takes the sharing limits from its options (`DriverOptions`);
* it serializes (`Ixon.serEnv`).

**Failures.** The compile records what it leaves out instead of dropping it:
`compileReport` returns, with the environment, every constant the ground
filter removed, with its named refusal (`Ix.GroundError.refusal`, the text
the IO pipeline and the Rust compiler record), and every constant of a block
that failed to compile, with the driver's error (`CompileEnv.ungrounded`: the
block's own failure, including a refused claim or payload and a failed
promotion or cross-SCC subset, which withdraws the whole block, or a
dependent's `MissingConstant`). `compile` is its first component, so a
failure leaves the result defined; `compileComplete` (the policy
`requireComplete`) makes any failure an error instead.

**Checks** (CQ2.27). `compileReport` ends by checking its own result
(`checkReport`): every input constant is published or reported as failed,
exactly one of the two, and every stored record and blob is at the admission
hash of its bytes. An inconsistency is an error, with no artifact. The
statements' coverage and authenticity (`CompileCovers`, `CompileAuthentic`)
therefore hold by construction, without an invariant of the driver's loop.

`Tests.Ix.Cert.Statement` compares the serialized output of the two on the
Source-mode fixtures (`cert-statement`) and on `Init`
(`cert-compile-parity-init`, ignored by default). -/

public section

namespace Ix.Cert

/-- The reference graph of `env` without its ungrounded constants and
without the edges into them, and the ungrounded constants themselves
(`Ix.groundConsts`: the immediately ungrounded ones, spread through the
reverse graph). -/
@[expose] def groundSplit (env : Ix.Environment) :
    Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.GroundError :=
  let outRefs := Ix.GraphM.envSerial env
  let inRefs : Ix.Map Ix.Name (Ix.Set Ix.Name) := outRefs.fold (init := {}) fun m n refs =>
    refs.fold (init := m) fun m r =>
      m.alter r fun
        | some s => some (s.insert n)
        | none => some (({} : Ix.Set Ix.Name).insert n)
  let ungrounded := Ix.groundConsts env inRefs
  if ungrounded.isEmpty then (outRefs, ungrounded)
  else (outRefs.fold (init := {}) fun m n refs =>
    if ungrounded.contains n then m
    else m.insert n (refs.fold (init := {}) fun s r =>
      if ungrounded.contains r then s else s.insert r), ungrounded)

/-- The reference graph of `env` without its ungrounded constants, and
without the edges into them. -/
@[expose] def groundedRefs (env : Ix.Environment) : Ix.Map Ix.Name (Ix.Set Ix.Name) :=
  (groundSplit env).1

/-- The compiler's declaration groups: the strongly connected components of
the grounded reference graph. -/
@[expose] def blocksOf (env : Ix.Environment) : Ix.CondensedBlocks :=
  Ix.CondenseM.run (groundedRefs env)

/-- What a compile left out, by name, with the reason. A name is in at most
one of the two maps: the ground filter removes its constants before any
block is compiled. -/
structure Failures where
  /-- The constants the ground filter removed, with their named refusals
  (`Ix.GroundError.refusal`). -/
  ungrounded : Std.HashMap Ix.Name String := {}
  /-- The constants of the blocks that failed to compile, with the driver's
  error (`Ix.CompileM.CompileEnv.ungrounded`). -/
  blocks : Std.HashMap Ix.Name String := {}

/-- Every failure in one map, as the IO pipeline records them
(`Ix.CompileM.LeanPipelineOut.cenv`'s `ungrounded`). -/
@[expose] def Failures.toMap (f : Failures) : Std.HashMap Ix.Name String :=
  f.blocks.fold (init := f.ungrounded) fun m n e => if m.contains n then m else m.insert n e

/-- Nothing failed. -/
@[expose] def Failures.isEmpty (f : Failures) : Bool :=
  f.ungrounded.isEmpty && f.blocks.isEmpty

/-- The compile and its failures, before `compileReport`'s checks. A block
that fails to compile is recorded, with its dependents, and left out of the
environment; the result is an error only when the driver itself fails (a
refused input, or a condensation it cannot schedule). -/
@[expose] def compileUnchecked (env : Ix.Environment) : Except String (Ixon.Env × Failures) := do
  let env : Ix.Environment := { consts := env.consts }
  let split := groundSplit env
  let (ixe, _, cenv) ← Ix.CompileM.compileEnvAux env (Ix.CondenseM.run split.1)
  let ungrounded := split.2.fold (init := {}) fun m n e =>
    m.insert n (e.refusal split.2.contains)
  pure (ixe, { ungrounded, blocks := cenv.ungrounded })

/-- The compile reports `n` as failed: the ground filter removed it, or its
block failed to compile. -/
@[expose] def Failures.failed (failures : Failures) (n : Ix.Name) : Bool :=
  failures.ungrounded.contains n || failures.blocks.contains n

/-- The input constants that a compile's result accounts for wrongly: those
both published (`Ixon.Env.named`) and listed as failed, and those neither. -/
@[expose] def uncovered (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) :
    List Ix.Name :=
  env.consts.keys.filter fun n => ixe.named.contains n == failures.failed n

/-- The records and blobs of `ixe` not stored at the admission hash of their
stored bytes (`Address.admissionHash`: pure BLAKE3 in the logic, the Rust
BLAKE3 at run time). -/
@[expose] def unauthentic (ixe : Ixon.Env) : List Address :=
  (ixe.consts.toList.filter fun (a, lc) => a != Address.admissionHash lc.rawBytes).map (·.1) ++
    (ixe.blobs.toList.filter fun (a, bytes) => a != Address.admissionHash bytes).map (·.1)

/-- `compileReport`'s two checks on a compile's result, each an error on any
inconsistency. **Coverage:** every input constant is published or listed as
failed, exactly one of the two. **Authenticity:** every record and blob is
stored at the admission hash of its bytes. -/
@[expose] def checkReport (env : Ix.Environment) (out : Ixon.Env × Failures) :
    Except String Unit :=
  match uncovered env out.1 out.2, unauthentic out.1 with
  | [], [] => .ok ()
  | n :: rest, _ =>
    .error s!"compileReport: coverage check failed: {rest.length + 1} input constant(s) are \
      published and listed as failed, or neither; first: {n.pretty} \
      ({if out.2.failed n then "published and failed" else "neither published nor failed"})"
  | [], a :: rest =>
    .error s!"compileReport: authenticity check failed: {rest.length + 1} record(s) or \
      blob(s) are not stored at the admission hash of their bytes; first: {a}"

/-- **The pure compiler, with its failures.** A block that fails to compile
is recorded, with its dependents, and left out of the environment; the
result is an error when the driver itself fails (a refused input, or a
condensation it cannot schedule). It ends with two checks (`checkReport`):
every input constant is published or reported as failed, exactly one of the
two, and every record and blob is stored at the admission hash of its
bytes. Any inconsistency is an error, and no artifact is returned. So
coverage and authenticity hold by construction (`Ix.Cert.compileCovers`,
`Ix.Cert.compileAuthentic`); on a consistent run the result is
`compileUnchecked`'s, byte for byte. -/
@[expose] def compileReport (env : Ix.Environment) : Except String (Ixon.Env × Failures) := do
  let out ← compileUnchecked env
  checkReport env out
  pure out

/-- **The pure compiler.** `compileReport`'s environment: a block that fails
to compile is left out of it, with its dependents (`compileReport` names
them). -/
@[expose] def compile (env : Ix.Environment) : Except String Ixon.Env :=
  Prod.fst <$> compileReport env

/-- The failure policy that makes every failure an error: the environment
when nothing failed, otherwise an error naming the least failing constant
(`Ix.nameCompare`), its reason, and the number of failures. -/
@[expose] def requireComplete (out : Ixon.Env × Failures) : Except String Ixon.Env :=
  let all := out.2.toMap
  match (all.toArray.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt)[0]? with
  | none => .ok out.1
  | some (n, why) => .error s!"{all.size} constant(s) failed to compile; {n.pretty}: {why}"

/-- `compileReport` under `requireComplete`: the compile fails if any
constant fails. -/
@[expose] def compileComplete (env : Ix.Environment) : Except String Ixon.Env :=
  compileReport env >>= requireComplete

end Ix.Cert

end
