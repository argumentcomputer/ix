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
4. the driver, `Ix.CompileM.compileEnvFold`: a fold over waves of ready
   blocks, their outcomes applied in block-key order. The IO pipeline runs
   the same function.

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
  materialized, and passes the count of constants it leaves to the fallback
  (`compileEnvFold`'s `unmaterialized`);
* it splits each wave of the driver into four tasks per `--workers` (the
  value does not depend on the split) and
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
  let (ixe, _, cenv) ← Ix.CompileM.compileEnvFold env (Ix.CondenseM.run split.1)
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

/-- The record stored at `a`, decoded (`Ix.Cert.recordAt`). -/
@[expose] def storedRecord (ixe : Ixon.Env) (a : Address) : Option Ixon.Constant :=
  (ixe.consts.get? a).bind (·.get?)

/-- The record a reference to the record `c` at `a` resolves to: a
projection's block, otherwise `a` itself (`Ix.Cert.ownerOf`). -/
@[expose] def refOwner (a : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => a

/-! ### A record's references, read without its expressions

The reference check needs, of each stored record, only its `refs` table and,
for a projection, its block. `RecordRefs.getRefs` reads exactly that. It walks
the record's bytes by `Ixon.getConstant`'s grammar, step for step and with the
same checks and messages, but keeps no expression or universe: of an
expression only its outermost constructor, where the reader's canonicity
checks look at it (`Head`). So it succeeds exactly when `Ixon.getConstant`
does, at the same position, with the decoded record's `refs` and projection
block (`Ix.Cert.RefsRead.getRefs_eq`). -/

namespace RecordRefs
open Ixon

/-- The outermost constructor of an expression, as far as
`Ixon.getExprFromTag`'s canonicity checks look at it. -/
inductive Head where
  | app | lam | all | other
  deriving DecidableEq, Inhabited

/-- An expression's `Head`. -/
@[expose] def head : Ixon.Expr → Head
  | .app .. => .app
  | .lam .. => .lam
  | .all .. => .all
  | _ => .other

/-- `count` decodings by `m`, keeping nothing (`Ixon.getArray`). -/
@[expose] def skipMany (m : GetM Unit) : Nat → GetM Unit
  | 0 => pure ()
  | count + 1 => do
    m
    skipMany m count

/-- `Ixon.getTagN0Values`, keeping nothing. -/
@[expose] def skipTagN0Values : Nat → GetM Unit
  | 0 => pure ()
  | count + 1 => do
    let _ ← getTagN 0
    skipTagN0Values count

/-- `Ixon.getExprAppArgs`, keeping the result's head. -/
@[expose] def skipAppArgs (recur : GetM Head) : Nat → Head → GetM Head
  | 0, result => pure result
  | count + 1, _ => do
    let _ ← recur
    skipAppArgs recur count .app

/-- `Ixon.getExprLamBinders`, keeping whether the telescope is empty. -/
@[expose] def skipLamBinders (recur : GetM Head) : Nat → GetM Bool
  | 0 => pure true
  | count + 1 => do
    let _ ← getBinderContract
    let _ ← recur
    let _ ← skipLamBinders recur count
    pure false

/-- `Ixon.getExprAllBinders`, keeping whether the telescope is empty. -/
@[expose] def skipAllBinders (recur : GetM Head) : Nat → GetM Bool
  | 0 => pure true
  | count + 1 => do
    let bits ← getU8
    match unpackAllContract? bits with
    | some _ =>
      let _ ← recur
      let _ ← skipAllBinders recur count
      pure false
    | none => throw s!"getExpr: invalid forall contract {bits}"

/-- `Ixon.getExprFromTag`, keeping the head. -/
@[expose] def skipExprFromTag (recur : GetM Head) (tag : TagN) : GetM Head := do
  match tag.flag with
  | 0x0 => return .other
  | 0x1 => return .other
  | 0x2 => do
    let _ ← getTagN 0
    checkCount tag.value
    skipTagN0Values tag.value.toNat
    return .other
  | 0x3 => do
    let _ ← getTagN 0
    checkCount tag.value
    skipTagN0Values tag.value.toNat
    return .other
  | 0x4 => do
    let _ ← getTagN 0
    let _ ← recur
    return .other
  | 0x5 => return .other
  | 0x6 => return .other
  | 0x7 => do
    if tag.value == 0 then
      throw "getExpr: empty app spine"
    checkCount tag.value
    let base ← recur
    match base with
    | .app => throw "getExpr: non-canonical app base"
    | _ => pure ()
    skipAppArgs recur tag.value.toNat base
  | 0x8 => do
    if tag.value == 0 then
      throw "getExpr: Lam with zero binders"
    checkCount tag.value 2
    let empty ← skipLamBinders recur tag.value.toNat
    let body ← recur
    match body with
    | .lam => throw "getExpr: non-canonical lam telescope"
    | _ => pure ()
    return if empty then body else .lam
  | 0x9 => do
    if tag.value == 0 then
      throw "getExpr: All with zero binders"
    checkCount tag.value 2
    let empty ← skipAllBinders recur tag.value.toNat
    let body ← recur
    match body with
    | .all => throw "getExpr: non-canonical all telescope"
    | _ => pure ()
    return if empty then body else .all
  | 0xA => do
    if tag.value > 3 then
      throw s!"getExpr: invalid let flags {tag.value}"
    let binder ← getBinderContract
    match LetContract.ofFlags? tag.value binder with
    | some _ =>
      let _ ← recur
      let _ ← recur
      let _ ← recur
      return .other
    | none => throw "getExpr: invalid let flags"
  | 0xB => return .other
  | f => throw s!"getExpr: invalid flag {f}"

/-- `Ixon.getExprFuel`, keeping the head. -/
@[expose] def skipExprFuel : Nat → GetM Head
  | 0 => throw "getExpr: recursion budget exhausted"
  | fuel + 1 => getTagN 4 >>= skipExprFromTag (skipExprFuel fuel)

/-- `Ixon.getExpr`, keeping nothing. -/
@[expose] def skipExpr : GetM Unit := do
  let state ← get
  let _ ← skipExprFuel (state.bytes.size - state.idx + 1)
  pure ()

/-- `Ixon.getUnivFromTag`, keeping nothing. -/
@[expose] def skipUnivFromTag (recur : GetM Unit) (tag : TagN) : GetM Unit := do
  match tag.flag with
  | 0 => if tag.value == 0 then pure () else recur
  | 1 => do
    recur
    recur
  | 2 => do
    recur
    recur
  | 3 => pure ()
  | f => throw s!"getUniv: invalid flag {f}"

/-- `Ixon.getUnivFuel`, keeping nothing. -/
@[expose] def skipUnivFuel : Nat → GetM Unit
  | 0 => throw "getUniv: recursion budget exhausted"
  | fuel + 1 => getTagN 2 >>= skipUnivFromTag (skipUnivFuel fuel)

/-- `Ixon.getUniv`, keeping nothing. -/
@[expose] def skipUniv : GetM Unit := do
  let state ← get
  skipUnivFuel (state.bytes.size - state.idx + 1)

/-- `Ixon.getDefinition`, keeping nothing. -/
@[expose] def skipDefinition : GetM Unit := do
  let flags ← getU8
  if flags >>> 2 > 2 || (flags &&& 3) > 2 then
    throw "invalid definition kind/safety"
  let _ ← getTagN 0
  skipExpr
  skipExpr

/-- `Ixon.getRecursorRule`, keeping nothing. -/
@[expose] def skipRecursorRule : GetM Unit := do
  let _ ← getTagN 0
  skipExpr

/-- `Ixon.getRecursor`, keeping nothing. -/
@[expose] def skipRecursor : GetM Unit := do
  let flags ← getU8
  if flags > 3 then throw "invalid recursor flags"
  let _ ← getTagN 0
  let _ ← getTagN 0
  let _ ← getTagN 0
  let _ ← getTagN 0
  let _ ← getTagN 0
  skipExpr
  let numRules := (← getTagN 0).value.toNat
  checkCount numRules.toUInt64 2
  skipMany skipRecursorRule numRules

/-- `Ixon.getAxiom`, keeping nothing. -/
@[expose] def skipAxiom : GetM Unit := do
  let _ ← (Serialize.get : GetM Bool)
  let _ ← getTagN 0
  skipExpr

/-- `Ixon.getQuotient`, keeping nothing. -/
@[expose] def skipQuotient : GetM Unit := do
  let v ← getU8
  match v with
  | 0 | 1 | 2 | 3 =>
    let _ ← getTagN 0
    skipExpr
  | _ => throw s!"invalid QuotKind tag {v}"

/-- `Ixon.getConstructor`, keeping nothing. -/
@[expose] def skipConstructor : GetM Unit := do
  let _ ← (Serialize.get : GetM Bool)
  let _ ← getTagN 0
  let _ ← getTagN 0
  let _ ← getTagN 0
  let _ ← getTagN 0
  skipExpr

/-- `Ixon.getInductive`, keeping nothing. -/
@[expose] def skipInductive : GetM Unit := do
  let _ ← (Serialize.get : GetM Bool)
  let _ ← getTagN 0
  let _ ← getTagN 0
  let _ ← getTagN 0
  skipExpr
  let numCtors := (← getTagN 0).value.toNat
  checkCount numCtors.toUInt64 6
  skipMany skipConstructor numCtors

/-- `Ixon.getMutConst`, keeping nothing. -/
@[expose] def skipMutConst : GetM Unit := do
  match ← getU8 with
  | 0 => skipDefinition
  | 1 => skipInductive
  | 2 => skipRecursor
  | t => throw s!"getMutConst: invalid tag {t}"

/-- `Ixon.getConstantInfo`, keeping only a projection's block. -/
@[expose] def skipInfo : GetM (Option Address) := do
  let tag ← getTagN 4
  if tag.flag == Constant.FLAG_MUTS then
    skipMany skipMutConst tag.value.toNat
    return none
  else if tag.flag == Constant.FLAG then
    match tag.value with
    | 0 => do skipDefinition; return none
    | 1 => do skipRecursor; return none
    | 2 => do skipAxiom; return none
    | 3 => do skipQuotient; return none
    | 4 => do let p ← getConstructorProj; return some p.block
    | 5 => do let p ← getRecursorProj; return some p.block
    | 6 => do let p ← getInductiveProj; return some p.block
    | 7 => do let p ← getDefinitionProj; return some p.block
    | v => throw s!"getConstantInfo: invalid variant {v}"
  else
    throw s!"getConstantInfo: invalid flag {tag.flag}"

/-- **A record's `refs` table and its projection block**, read by
`Ixon.getConstant`'s grammar without keeping its expressions or universes. -/
@[expose] def getRefs : GetM (Array Address × Option Address) := do
  let block ← skipInfo
  let numSharing := (← getTagN 0).value.toNat
  skipMany skipExpr numSharing
  let numRefs := (← getTagN 0).value.toNat
  let refs ← getArray Serialize.get numRefs
  let numUnivs := (← getTagN 0).value.toNat
  skipMany skipUniv numUnivs
  return (refs, block)

/-- `getRefs` at offset `off` of `buf` (`Ixon.deConstantAt`). -/
@[expose] def refsAt (buf : ByteArray) (off : Nat) : Option (Array Address × Option Address) :=
  match getRefs.run { idx := off, bytes := buf } with
  | .ok r _ => some r
  | .error _ _ => none

/-- The references and the owner (`Ix.Cert.refOwner`) of the record `lc`
stored at `a`, read without its expressions; `none` exactly when `lc.get?`
is (`Ix.Cert.RefsRead.lazyRefs_eq`). -/
@[expose] def lazyRefs (a : Address) (lc : Ixon.LazyConstant) : Option (Array Address × Address) :=
  match lc.cache with
  | some c => some (c.refs, refOwner a c)
  | none => (refsAt lc.buf lc.off).map fun (refs, block) => (refs, block.getD a)

end RecordRefs

/-- The references and the owner of the record stored at `a`: those of
`storedRecord ixe a`, read without its expressions (`RecordRefs.lazyRefs`). -/
@[expose] def storedRefs (ixe : Ixon.Env) (a : Address) : Option (Array Address × Address) :=
  (ixe.consts.get? a).bind (RecordRefs.lazyRefs a)

/-- How many tasks `parMap` runs on, at most. -/
@[expose] def recordTasks : Nat := 256

/-- `xs.map f`, computed on at most `recordTasks` tasks over contiguous chunks
of `xs` (`Task.spawn`, the task pool); the tasks see only `xs` and `f`. The
value is `xs.map f`: `(Task.spawn g).get = g ()` by definition, and the
chunks, flattened, are `xs` (`Ix.Cert.Order.parMap_eq`). -/
@[expose] def parMap {α β : Type} (f : α → β) (xs : Array α) : Array β :=
  let n := xs.size
  let size := (n + recordTasks - 1) / recordTasks
  let chunks := if size == 0 then 0 else (n + size - 1) / size
  (((Array.range chunks).map fun c => Task.spawn fun _ =>
    (xs.extract (c * size) ((c + 1) * size)).map f).map Task.get).flatten

/-- The references and owner of each record of `recs` (an address and what is
stored there), in order, read without the records' expressions
(`RecordRefs.lazyRefs`) on tasks (`parMap`) that see only `recs`, not the
artifact. -/
@[expose] def recordRefs (recs : Array (Address × Option Ixon.LazyConstant)) :
    Array (Option (Array Address × Address)) :=
  parMap (fun (a, lc) => lc.bind (RecordRefs.lazyRefs a)) recs

/-- The stored records' reference graph: the records (`ixe.consts`' keys) as
nodes `0 … n-1`, and an edge from a record to the record each of its
references resolves to (`refOwner`), when that is a stored record: the
edges of `Ix.Cert.RecordRef`, and a record's edges to itself. Each record is
read once, without its expressions (`recordRefs`), and the edges are resolved
on tasks (`parMap`). -/
@[expose] def recordGraph (ixe : Ixon.Env) : Array Address × Array (Array Nat) :=
  let addrs := ixe.consts.keys.toArray
  let index : Std.HashMap Address Nat := Std.HashMap.ofList addrs.toList.zipIdx
  let info := recordRefs (addrs.map fun a => (a, ixe.consts.get? a))
  let ownerAt : Address → Option Address := fun r => do
    let j ← index.get? r
    let (_, o) ← (info[j]?).join
    pure o
  let adj := parMap (fun
    | none => #[]
    | some (refs, _) => refs.filterMap fun r => ownerAt r >>= index.get?) info
  (addrs, adj)

/-- The stored records of a reference cycle, if any: a component of the
records' reference graph (`Ix.Compile.Canon.condensation`, Tarjan's
strongly connected components, proved) with more than one record, or one
record that references itself. `none` when there is no such component, so
the references are acyclic. (`condensation` always returns,
`Ix.CompileCert.Canon.condensation_isSome`; were it not to, the check fails.) -/
@[expose] def referenceCycle (ixe : Ixon.Env) : Option (List Address) :=
  let (addrs, adj) := recordGraph ixe
  let cyclic (c : Array Nat) : Bool :=
    c.size != 1 || c.any fun i => (adj[i]?.getD #[]).contains i
  match Ix.Compile.Canon.condensation adj with
  | none => some []
  | some C => (C.comps.toList.find? cyclic).map fun c => c.toList.filterMap (addrs[·]?)

/-- `compileReport`'s three checks on a compile's result, each an error on
any inconsistency. **Coverage:** every input constant is published or listed
as failed, exactly one of the two. **Authenticity:** every record and blob is
stored at the admission hash of its bytes. **Acyclic references:** no stored
record is on a reference cycle (`referenceCycle`), so the records have an
order in which none precedes a record it references. -/
@[expose] def checkReport (env : Ix.Environment) (out : Ixon.Env × Failures) :
    Except String Unit :=
  match uncovered env out.1 out.2, unauthentic out.1 with
  | [], [] =>
    match referenceCycle out.1 with
    | none => .ok ()
    | some cycle =>
      .error s!"compileReport: reference check failed: {cycle.length} stored record(s) on a \
        reference cycle; first: {cycle.take 5}"
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
condensation it cannot schedule). It ends with three checks (`checkReport`):
every input constant is published or reported as failed, exactly one of the
two; every record and blob is stored at the admission hash of its bytes; and
no stored record is on a reference cycle. Any inconsistency is an
error, and no artifact is returned. So coverage, authenticity and an order of
the records in which none precedes a record it references hold by
construction (`Ix.Cert.compileCovers`, `Ix.Cert.compileAuthentic`,
`Ix.Cert.ClosureOrder`'s existence); on a consistent run the result is
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
