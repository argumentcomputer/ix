module

public import Ix.CompileDriver
public import IxC.Kernel.Ixon.Reader
public import IxC.Kernel.Ixon.Prelude
public import Ix.LeanIngress

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
  materialized;
* it splits each wave of the driver into four tasks per `--workers` (the
  value does not depend on the split) and
  takes the sharing limits from its options (`DriverOptions`);
* it serializes (`Ixon.serEnv`).

**Failures.** The compile records what it leaves out instead of dropping it:
`compileReport` returns, with the environment, every constant the ground
filter removed, with its named refusal (`Ix.GroundError.refusal`, the text
the IO pipeline and the Rust compiler record), and every constant of a block
that failed to compile, with the driver's error (`CompileEnv.ungrounded`: the
block's own failure, including a refused claim or payload, or a
dependent's `MissingConstant`). `compile` is its first component, so a
failure leaves the result defined; `compileComplete` (the policy
`requireComplete`) makes any failure an error instead.

**Checks** (CQ2.27). `compileReport` ends by checking its own result
(`checkReport`): every input constant is published or reported as failed,
exactly one of the two, and every stored record and blob is at the admission
hash of its bytes; the later checks are listed at `checkReport`. An
inconsistency is an error, with no artifact. The
statements' coverage and authenticity (`CompileCovers`, `CompileAuthentic`)
therefore hold by construction, without an invariant of the driver's loop.

`Tests.Ix.Cert.Statement` compares the serialized output of the two on the
Source-mode fixtures (`cert-statement`) and on Init+Std
(`cert-compile-parity-initstd`, in the merge queue). -/

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

/-- The compile and its failures, before `compileReport`'s checks, with the
driver's compile environment at the end of the fold, whose maps the checks
read: the resolution map (`CompileEnv.nameToAddr`: the address each name the
compile registered resolves to) and the recorded failures
(`CompileEnv.ungrounded`). A block that fails to compile is recorded, with its
dependents, and left out of the environment; the result is an error only when
the driver itself fails (a refused input, or a condensation it cannot
schedule). -/
@[expose] def compileUnchecked (env : Ix.Environment) :
    Except String (Ixon.Env × Failures × Ix.CompileM.CompileEnv) := do
  let env : Ix.Environment := { consts := env.consts }
  let split := groundSplit env
  let blocks := Ix.CondenseM.run split.1
  let (ixe, _, cenv) ← Ix.CompileM.compileEnvFold env blocks
  let ungrounded := split.2.fold (init := {}) fun m n e =>
    m.insert n (e.refusal split.2.contains)
  pure (ixe, { ungrounded, blocks := cenv.ungrounded }, cenv)

/-- **The compile's condensation**: the declaration groups the driver
compiles, and their references (the strongly connected components of the
grounded reference graph of the input's map). `compileUnchecked` compiles
exactly these blocks (its `blocks`, by `rfl`; it computes the ground split
once, for its failures too). -/
@[expose] def compileBlocks (env : Ix.Environment) : Ix.CondensedBlocks :=
  Ix.CondenseM.run (groundSplit { consts := env.consts }).1

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
the record's bytes by `Ixon.Bounded.getConstant`'s grammar, step for step and with the
same checks and messages, but keeps no expression or universe: of an
expression only its outermost constructor, where the reader's canonicity
checks look at it (`Head`). Universe entries share the loader's node budget.
So it succeeds exactly when `Ixon.Bounded.getConstant`
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

/-- `Ixon.Bounded.getUnivFromTag`, keeping only the unspent node budget. -/
@[expose] def skipUnivFromTag (recur : Nat → GetM Nat) (budget : Nat)
    (tag : TagN) : GetM Nat := do
  let charge := Bounded.univTagCharge tag
  if charge ≤ budget then
    let remaining := budget - charge
    match tag.flag with
    | 0 => if tag.value == 0 then pure remaining else recur remaining
    | 1 => do
      let remaining ← recur remaining
      recur remaining
    | 2 => do
      let remaining ← recur remaining
      recur remaining
    | 3 => pure remaining
    | f => throw s!"getUniv: invalid flag {f}"
  else
    throw "getUnivBounded: expanded-node budget exhausted"

/-- `Ixon.Bounded.getUnivFuel`, keeping only the unspent node budget. -/
@[expose] def skipUnivFuel : Nat → Nat → GetM Nat
  | 0, _ => throw "getUniv: recursion budget exhausted"
  | fuel + 1, budget => getTagN 2 >>= skipUnivFromTag (skipUnivFuel fuel) budget

/-- `Ixon.Bounded.getUniv`, without allocating the expanded universe. -/
@[expose] def skipUniv (budget : Nat) : GetM Nat := do
  let state ← get
  skipUnivFuel (state.bytes.size - state.idx + 1) budget

/-- Skip a universe table with one budget shared by all its entries. -/
@[expose] def skipUnivArray : Nat → Nat → GetM Nat
  | 0, budget => pure budget
  | count + 1, budget => do
    let remaining ← skipUniv budget
    skipUnivArray count remaining

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
`Ixon.Bounded.getConstant`'s grammar without keeping its expressions or universes. -/
@[expose] def getRefs (maxUnivNodes : Nat := loadMaxUnivNodes) :
    GetM (Array Address × Option Address) := do
  let block ← skipInfo
  let numSharing := (← getTagN 0).value.toNat
  skipMany skipExpr numSharing
  let numRefs := (← getTagN 0).value.toNat
  let refs ← getArray Serialize.get numRefs
  let numUnivs := (← getTagN 0).value.toNat
  let _ ← skipUnivArray numUnivs maxUnivNodes
  return (refs, block)

/-- `getRefs` over exactly the window `buf[off, off + len)`, as
`Ixon.deConstantAt` decodes it: the window inside `buf`, and the read ending at
`off + len`. -/
@[expose] def refsAt (buf : ByteArray) (off len : Nat)
    (maxUnivNodes : Nat := loadMaxUnivNodes) : Option (Array Address × Option Address) :=
  if off + len ≤ buf.size then
    match (getRefs maxUnivNodes).run { idx := off, bytes := buf } with
    | .ok r s => if s.idx = off + len then some r else none
    | .error _ _ => none
  else none

/-- The references and the owner (`Ix.Cert.refOwner`) of the record `lc`
stored at `a`, read without its expressions; `none` exactly when `lc.get?`
is (`Ix.Cert.RefsRead.lazyRefs_eq`). -/
@[expose] def lazyRefs (a : Address) (lc : Ixon.LazyConstant) : Option (Array Address × Address) :=
  match lc.cache with
  | some c => some (c.refs, refOwner a c)
  | none => (refsAt lc.buf lc.off lc.len).map fun (refs, block) => (refs, block.getD a)

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

/-- Two different names with one stored hash among the input's constants and
the artifact's published names, the first such pair met, if any.
`Ix.Name`'s `==` compares stored hashes, so every map keyed by name (the
input's, the artifact's, the changed set's) identifies two such names; the
statements read names structurally (`Ix.nameCompareExact`). -/
@[expose] def nameHashCollision (env : Ix.Environment) (ixe : Ixon.Env) : Option (Ix.Name × Ix.Name) :=
  ((env.consts.keys ++ ixe.named.keys).foldl
    (init := ((∅ : Std.HashMap Address Ix.Name), (none : Option (Ix.Name × Ix.Name))))
    fun acc n =>
      match acc.2 with
      | some _ => acc
      | none =>
        match acc.1.get? n.getHash with
        | some m => if Ix.nameCompareExact m n == .eq then acc else (acc.1, some (m, n))
        | none => (acc.1.insert n.getHash n, none)).2

/-- The block and member index of a stored member projection record (a
definition's, an inductive's or a recursor's). -/
@[expose] def memberProjection (c : Ixon.Constant) : Option (Address × Nat) :=
  match c.info with
  | .dPrj p => some (p.block, p.idx.toNat)
  | .iPrj p => some (p.block, p.idx.toNat)
  | .rPrj p => some (p.block, p.idx.toNat)
  | _ => none

/-- Whether the name with hash `h` is published at the projection of member
`i` of the block at `block` (`byHash`: the published names by hash). -/
@[expose] def publishedAtMember (ixe : Ixon.Env) (byHash : Std.HashMap Address Ix.Name)
    (block : Address) (i : Nat) (h : Address) : Bool :=
  match byHash.get? h with
  | none => false
  | some n => match ixe.named.get? n with
    | none => false
    | some m => match storedRecord ixe m.addr with
      | none => false
      | some c => memberProjection c == some (block, i)

/-- A `Muts` entry whose class `i` lists a name hash not published at member
`i`'s projection of the entry's block, if any: the entry's name, `i` and the
hash. The changed set reads a compiled component's classes off these entries;
with no mismatch they are the block's own, as its projections publish them. -/
@[expose] def mutsMismatch (ixe : Ixon.Env) : Option (Ix.Name × Nat × Address) :=
  let byHash : Std.HashMap Address Ix.Name := ixe.named.fold (init := {}) fun m n _ => m.insert n.getHash n
  ixe.named.toList.findSome? fun (entry, named) =>
    match named.constMeta.info with
    | .muts all _ =>
      all.toList.zipIdx.findSome? fun (cls, i) =>
        (cls.toList.find? fun h => !publishedAtMember ixe byHash named.addr i h).map fun h => (entry, i, h)
    | _ => none

/-- A name the driver resolves that the artifact does not publish at that
address, the first met, if any: the name, the address it resolves to
(`resolved`, the driver's resolution map at the end of the fold,
`CompileEnv.nameToAddr`), and the address `ixe.named` publishes it at, if
any. A block's merge registers its names in both tables at one address, and
later merges (another block's names, or its `Muts` entry) write `ixe.named`
without the resolution map's single-ownership check, so a name could end
published at another address than the one the compile resolved it to. With no
mismatch, every name the compile resolves is published at that address. -/
@[expose] def resolutionMismatch (resolved : Std.HashMap Ix.Compile.ExactKey.ExactName Address)
    (ixe : Ixon.Env) : Option (Ix.Name × Address × Option Address) :=
  resolved.toList.findSome? fun (n, a) =>
    let published := (ixe.named.get? n).map (·.addr)
    if published = some a then none else some (n, a, published)

/-- The first input name published in `ixe` that is not in the driver's final
resolution map (`resolved`), if any. A `Named` entry can come from a block's
`Muts` entry (`BlockState.mutsNamed`), so publication alone says nothing of
where a name's record came from. With no such name, every published input
name is a primary claim of a block compiled during the fold
(`Ix.Cert.Resolution.compileReport_claim`). -/
@[expose] def unresolvedPublished (env : Ix.Environment)
    (resolved : Std.HashMap Ix.Compile.ExactKey.ExactName Address) (ixe : Ixon.Env) :
    Option Ix.Name :=
  ixe.named.toList.findSome? fun (n, _) =>
    if env.consts.contains n && !resolved.contains n then some n else none

/-- The first input constant whose own name (`ConstantVal.name`) is not the
name it is stored under, spelled exactly (`Ix.nameCompareExact`, stored hashes
included), if any. The block compile names its projections by its members' own
names (`MutConst`), while the condensation and the driver group and look them
up by the names they are stored under. With no such constant, every name a
block's compile claims is a member's or a member's constructor's, and a
constant is published under one spelling whichever path compiles it. `Ix.Name`'s
`==` compares stored hashes only, so it would let an own name be a respelling
of the stored name that shares its hash. -/
@[expose] def misnamedInput (env : Ix.Environment) : Option Ix.Name :=
  env.consts.toList.findSome? fun (n, ci) =>
    if Ix.nameCompareExact ci.getCnst.name n == .eq then none else some n

/-- The first constructor name (`InductiveVal.ctors`) of an input inductive
that the input does not store as a constructor of that inductive
(`ConstructorVal.induct` hashing like the name the inductive is stored under),
if any. A block's compile claims its inductives' constructors, looked up by
those names; with no such name, each claimed constructor references its
inductive (`Ix.graphConst`), so it is in the inductive's component and in
every closure that holds it. -/
@[expose] def strayConstructor (env : Ix.Environment) : Option Ix.Name :=
  env.consts.toList.findSome? fun (n, ci) =>
    match ci with
    | .inductInfo iv => iv.ctors.toList.find? fun c =>
        match env.consts.get? c with
        | some (.ctorInfo cv) => !(cv.induct == n)
        | _ => true
    | _ => none

/-- The first address that holds both a stored blob and a stored record, if
any. Blobs (literal bytes) and records share one address space,
`Address.admissionHash` with no domain separation, and a record's reference
table lists its literals' blob addresses beside the records it references: a
literal whose bytes are another record's serialization would make that record
look referenced. With none, no blob address is a record's. -/
@[expose] def blobRecordCollision (ixe : Ixon.Env) : Option Address :=
  ixe.blobs.toList.findSome? fun (a, _) => if ixe.consts.contains a then some a else none

/-- The stored records with a recursor member
(`Ix.Kernel.Reader.recursorMembers`), in `ixe.consts`' order: each record
decoded once, on tasks (`parMap`). The recursor index
(`Ix.Kernel.Reader.buildIndex`) reads nothing of the other records in its scan,
so over these it is the artifact's index (`Ix.Cert.recursorIndex_eq`). -/
@[expose] def storedRecursorRecords (ixe : Ixon.Env) : Array (Address × Ixon.Constant) :=
  (parMap (fun (e : Address × Ixon.LazyConstant) =>
    match e.2.get? with
    | some c => if (Ix.Kernel.Reader.recursorMembers c).isEmpty then none else some (e.1, c)
    | none => none) ixe.consts.toArray).filterMap id

/-- The block of the record stored at `a`: a projection's block, otherwise
`a` itself (`Ix.Cert.ClosureLayout.blockAt`), read without the record's
expressions (`storedRefs`). -/
@[expose] def recordBlock (ixe : Ixon.Env) (a : Address) : Address :=
  match storedRefs ixe a with
  | some (_, owner) => owner
  | none => a

/-- A name's published record and that record's block
(`Ix.Cert.ClosureLayout.nameRecords`). -/
@[expose] def publishedRecords (ixe : Ixon.Env) (n : Ix.Name) : List Address :=
  match ixe.named.get? n with
  | some named => [named.addr, recordBlock ixe named.addr]
  | none => []

/-- The first inductive of the family of an input inductive, constructor or
recursor: its `all[0]`, its inductive's, or its `all[0]`'s; `none` for any other
name. -/
@[expose] def familyFirst? (env : Ix.Environment) (x : Ix.Name) : Option Ix.Name :=
  match env.consts.get? x with
  | some (.inductInfo iv) => iv.all[0]?
  | some (.ctorInfo cv) =>
    match env.consts.get? cv.induct with
    | some (.inductInfo iv) => iv.all[0]?
    | _ => none
  | some (.recInfo rv) =>
    match rv.all[0]? with
    | some i =>
      match env.consts.get? i with
      | some (.inductInfo iv) => iv.all[0]?
      | _ => none
    | none => none
  | _ => none

/-- Whether the input name `rn` is a recursor of the family whose first
inductive is `first`, published at the record `blk` or at a projection of it. -/
@[expose] def familyRecursorAt (env : Ix.Environment) (ixe : Ixon.Env) (first rn : Ix.Name)
    (blk : Address) : Bool :=
  match env.consts.get? rn with
  | some (.recInfo rv) => decide (rv.all[0]? = some first) && decide (blk ∈ publishedRecords ixe rn)
  | _ => false

/-- `familyRecursors`' step at the input constant `n`: a recursor is filed under
its family's first inductive's name hash. -/
@[expose] def familyRecursorsStep (m : Std.HashMap Address (Array Ix.Name)) (n : Ix.Name)
    (ci : Ix.ConstantInfo) : Std.HashMap Address (Array Ix.Name) :=
  match ci with
  | .recInfo rv =>
    match rv.all[0]? with
    | some first => m.insert first.getHash ((m.getD first.getHash #[]).push n)
    | none => m
  | _ => m

/-- The input recursors, by the name hash of their family's first inductive:
the candidates `unownedRecursor` tries for a family. Each candidate is checked
in full (`familyRecursorAt`), so the table only narrows the search. -/
@[expose] def familyRecursors (env : Ix.Environment) : Std.HashMap Address (Array Ix.Name) :=
  env.consts.fold (init := {}) familyRecursorsStep

/-- Whether a recursor of the family whose first inductive is `first` is published
at the record `blk` or at a projection of it (`cands`, `familyRecursors`, gives the
candidates). -/
@[expose] def familyOwns (env : Ix.Environment) (ixe : Ixon.Env)
    (cands : Std.HashMap Address (Array Ix.Name)) (first : Ix.Name) (blk : Address) : Bool :=
  (cands.getD first.getHash #[]).any fun rn => familyRecursorAt env ixe first rn blk

/-- For the published name `x` (its entry `named`), if it is an input name and
its record's block has recursors in the index `idx`: the block and `x`, with no
recursor if `x` has no family (`familyFirst?`), otherwise with the first of the
block's recursors that is not a published recursor of `x`'s family
(`familyOwns`), if any. -/
@[expose] def unownedRecursorOf (env : Ix.Environment) (ixe : Ixon.Env)
    (idx : Ix.Kernel.Reader.RecIndex) (cands : Std.HashMap Address (Array Ix.Name))
    (x : Ix.Name) (named : Ixon.Named) :
    Option (Address × Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  if env.consts.contains x then
    match idx.blocks[recordBlock ixe named.addr]? with
    | some shape =>
      match familyFirst? env x with
      | some first =>
        (shape.recs.find? fun r => !familyOwns env ixe cands first r.block).map fun r =>
          (recordBlock ixe named.addr, x, some r)
      | none => some (recordBlock ixe named.addr, x, none)
    | none => none
  else none

/-- An inductive block the recursor index (`Ix.Kernel.Reader.buildIndex`) attaches
recursors to and an input name published in that block (at the block or a
projection of it) that has no family, or with a recursor attached there that is
not a published recursor of the name's family: the first met, if any. The index files a recursor under the
block its type's first motive carrier names and keeps the first per motive in
store order, so a recursor record of another family whose type eliminates a
block's motive could take the place of the block's own. Published input names
are read on tasks (`parMap`). With none, every input name published in a block
the index attaches recursors to has a family (it is an inductive, constructor or
recursor), and every recursor the index attaches there is a published recursor
of that family (`Ix.Cert.RecursorsOwned`). -/
@[expose] def unownedRecursor (env : Ix.Environment) (ixe : Ixon.Env) :
    Option (Address × Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  let idx := Ix.Kernel.Reader.buildIndex (storedRecord ixe) (storedRecursorRecords ixe)
  let cands := familyRecursors env
  (parMap (fun (e : Ix.Name × Ixon.Named) => unownedRecursorOf env ixe idx cands e.1 e.2)
    ixe.named.toList.toArray).findSome? id

/-- The kind of the specification of the role `r` (`(Ix.Kernel.Role.spec r).kind`,
`Ix.Cert.roleKind_eq`), without building the specification's expressions. -/
@[expose] def roleKind : Ix.Kernel.Role → Ix.Kernel.SpecKind
  | .nat | .natZero | .natSucc | .natRec | .eq | .eqRefl | .eqRec | .punit | .punitUnit | .punitRec
  | .empty | .emptyRec | .false | .falseRec | .quot | .quotMk | .quotLift | .quotInd | .quotSound
  | .iff | .iffIntro | .iffRec | .nonempty | .nonemptyIntro | .nonemptyRec => .block
  | .natPred | .natAdd | .natSub | .natMul | .natPow | .natBeq | .natBle | .natDiv | .natMod
  | .natGcd | .natLand | .natLor | .natXor | .natShiftLeft | .natShiftRight => .ops
  | .propext | .choice | .sorryAx => .axiom
  | _ => .anchor

/-- Whether the record `c` has the kind the specification of the role `r` asks
of the record stored at its bound address: a standalone definition for a `Nat`
operation (an `ops` specification), an axiom for an axiom role (`propext`,
`Classical.choice`, `sorryAx`); any kind for every other role. -/
@[expose] def roleRecordKindOk (r : Ix.Kernel.Role) (c : Ixon.Constant) : Bool :=
  match roleKind r, c.info with
  | .ops, .defn d => decide (d.kind = .defn)
  | .ops, _ => false
  | .axiom, .axio _ => true
  | .axiom, _ => false
  | _, _ => true

/-- The bound entries of the default role table's binding section, decoded
canonically (`Ix.Kernel.Reader.defaultTable`'s decoding, without its
well-formedness check, which builds the roles' specifications); none if it
does not decode. -/
@[expose] def roleTableBound : Array (Ix.Kernel.Role × Address) :=
  ((Ix.Kernel.Reader.defaultTableBytes.toOption.bind Ix.Kernel.RoleTable.ofBytes).map
    (·.bound)).getD #[]

/-- The addresses of the bound entries `bound`. -/
@[expose] def roleAddrs (bound : Array (Ix.Kernel.Role × Address)) : Std.HashSet Address :=
  Std.HashSet.ofList (bound.toList.map (·.2))

/-- The first role of the bound entries `bound` bound to the address `p` whose
specification asks another kind of record than `c` (`roleRecordKindOk`), if any.
Every entry is read, so whichever entry a lookup of the role finds is covered. -/
@[expose] def roleRecordKindAt (bound : Array (Ix.Kernel.Role × Address)) (p : Address)
    (c : Ixon.Constant) : Option Ix.Kernel.Role :=
  (bound.toList.find? fun e => e.2 == p && !roleRecordKindOk e.1 c).map (·.1)

/-- A stored record at an address the default role table binds
(`roleTableBound`) whose kind is not the one a role bound there asks
(`roleRecordKindAt`), with that role, the first met, if any. Only records at
bound addresses are decoded. An address the artifact stores nothing at, and a
table that does not decode, are unconstrained. With none, the stored record at
a bound `Nat` operation's address is a standalone definition and at a bound
axiom role's address an axiom (`Ix.Cert.RoleRecordKinds`). -/
@[expose] def roleRecordKind (ixe : Ixon.Env) : Option (Ix.Kernel.Role × Address) :=
  let bound := roleTableBound
  let addrs := roleAddrs bound
  ixe.consts.toList.findSome? fun (p, lc) =>
    if addrs.contains p then
      match lc.get? with
      | some c => (roleRecordKindAt bound p c).map fun r => (r, p)
      | none => none
    else none

/-- The roles a literal is checked against: the `Nat` basis and the string support
(the roles of `Ix.Kernel.Reader.strLitSupportNames`). -/
@[expose] def literalSupportRoles : List Ix.Kernel.Role :=
  [.nat, .natZero, .natSucc, .string, .stringOfList, .list, .listNil, .listCons, .char, .charOfNat]

/-- The Lean name of a literal-support role, as `Ix.RoleEvidence.toLeanName` spells the
role's key (`Ix.Cert.literalRoleName_eq`), written out so that the check does not evaluate
the kernel's name keys. -/
@[expose] def literalLeanName : Ix.Kernel.Role → Lean.Name
  | .nat => `Nat
  | .natZero => `Nat.zero
  | .natSucc => `Nat.succ
  | .string => `String
  | .stringOfList => `String.ofList
  | .list => `List
  | .listNil => `List.nil
  | .listCons => `List.cons
  | .char => `Char
  | .charOfNat => `Char.ofNat
  | _ => .anonymous

/-- The input name of a literal-support role. -/
@[expose] def literalRoleIxName (s : Ix.Kernel.Role) : Ix.Name :=
  Ix.Name.fromLeanName (literalLeanName s)

/-- The roles a `Nat` literal is checked against: the `Nat` basis (the roles of
`Ix.Kernel.Reader.natLitSupportNames`). -/
@[expose] def natLiteralRoles : List Ix.Kernel.Role :=
  [.nat, .natZero, .natSucc]

/-- Whether some stored record holds a `Nat` literal, and whether some holds a `String`
literal (`Ix.Kernel.Reader.literalKinds` of each stored record, decoded on tasks). -/
@[expose] def storedLiteralKinds (ixe : Ixon.Env) : Bool × Bool :=
  let kinds := parMap (fun (e : Address × Ixon.LazyConstant) =>
    match e.2.get? with
    | some c => Ix.Kernel.Reader.literalKinds c
    | none => (false, false)) ixe.consts.toArray
  (kinds.any (·.1), kinds.any (·.2))

/-- The roles the stored records' literals are checked against: the string support when
some stored record holds a `String` literal, otherwise the `Nat` basis when some holds a
`Nat` literal, otherwise none. -/
@[expose] def storedLiteralRoles (ixe : Ixon.Env) : List Ix.Kernel.Role :=
  let kinds := storedLiteralKinds ixe
  if kinds.2 then literalSupportRoles else if kinds.1 then natLiteralRoles else []

/-- A literal-support role of the default role table (`roleTableBound`) that a stored
record's literal is checked against (`storedLiteralRoles`), at whose address the artifact
stores a record while the role's name (`literalRoleIxName`) is not an input constant
published at that address, with that address, the first met, if any. The stored records'
literals are read only when some bound literal-support role is stored unnamed. With none,
a literal's support role stored in the artifact is its name's
(`Ix.Cert.LiteralRolesNamed`). -/
@[expose] def literalRoleUnnamed (env : Ix.Environment) (ixe : Ixon.Env) :
    Option (Ix.Kernel.Role × Address) :=
  let unnamed := roleTableBound.toList.filter fun (s, b) =>
    literalSupportRoles.contains s && ixe.consts.contains b &&
      !(env.consts.contains (literalRoleIxName s) &&
        (ixe.named.get? (literalRoleIxName s)).map (·.addr) == some b)
  if unnamed.isEmpty then none
  else
    let roles := storedLiteralRoles ixe
    unnamed.find? fun (s, _) => roles.contains s

/-! ## Inductive input shapes

The compiler copies an inductive family's declarations as Lean gives them, and
reads only some of what it copies. The certified reading of a family
(quotient Source) and the reading of its compiled records (the Ixon reader)
agree only on inputs of the shapes Lean produces; these checks refuse every
other input. Real inputs pass all of them, and none changes a compiled byte. -/

/-- The first constructor name of an input inductive that is stored as a constructor declaring
another index than its position in the inductive's list, if any. The compiler stores the
declared index in the block and addresses the constructor by its position, so they must agree
for its projection to resolve. -/
@[expose] def misplacedConstructor (env : Ix.Environment) : Option Ix.Name :=
  env.consts.toList.findSome? fun (_, ci) =>
    match ci with
    | .inductInfo iv =>
      (iv.ctors.toList.zipIdx.find? fun (c, j) =>
        match env.consts.get? c with
        | some (.ctorInfo cv) => cv.cidx != j
        | _ => false).map (·.1)
    | _ => none

/-- Whether two arrays of names are equal, name by name structurally
(`Ix.Name.beqRaw`, through `Ix.LeanIngress.TableName`'s lawful `==`). -/
@[expose] def namesEq (a b : Array Ix.Name) : Bool :=
  @BEq.beq (Array Ix.LeanIngress.TableName) _ a b

/-- The level parameters of the first input recursor met for each family's first inductive
(its `all[0]`, compared structurally). -/
@[expose] def recursorLevelParams (env : Ix.Environment) :
    Std.HashMap Ix.LeanIngress.TableName (Array Ix.Name) :=
  env.consts.fold (init := {}) fun m _ ci =>
    match ci with
    | .recInfo rv =>
      match rv.all[0]? with
      | some first => if m.contains first then m else m.insert first rv.cnst.levelParams
      | none => m
    | _ => m

/-- Whether the recursor `rv` has as many level parameters as its family's first inductive
`first`, or one more (a large eliminator's); any count when `first` is not an input
inductive. -/
@[expose] def recursorLevelCountOk (env : Ix.Environment) (first : Ix.Name) (rv : Ix.RecursorVal) : Bool :=
  match env.consts.get? first with
  | some (.inductInfo iv) =>
    rv.cnst.levelParams.size == iv.cnst.levelParams.size ||
      rv.cnst.levelParams.size == iv.cnst.levelParams.size + 1
  | _ => true

/-- The first input name whose level parameters are not its family's, if any: a member an
input inductive lists, or a constructor it lists, without the inductive's names, or a
recursor without the names of the first recursor met with its `all[0]`
(`recursorLevelParams`), or with neither its family's count nor one more
(`recursorLevelCountOk`). The compiler compiles a constructor's type under its inductive's
level parameters, while quotient Source numbers each constant by its own. -/
@[expose] def strayLevelParams (env : Ix.Environment) : Option Ix.Name :=
  let recLps := recursorLevelParams env
  env.consts.toList.findSome? fun (n, ci) =>
    match ci with
    | .inductInfo iv =>
      match iv.all.find? (fun m =>
          match env.consts.get? m with
          | some (.inductInfo iv') => !namesEq iv'.cnst.levelParams iv.cnst.levelParams
          | _ => false) with
      | some m => some m
      | none =>
        iv.ctors.find? fun c =>
          match env.consts.get? c with
          | some (.ctorInfo cv) => !namesEq cv.cnst.levelParams iv.cnst.levelParams
          | _ => false
    | .recInfo rv =>
      match rv.all[0]? with
      | some first =>
        if (recLps[(first : Ix.LeanIngress.TableName)]?).any (namesEq · rv.cnst.levelParams) &&
            recursorLevelCountOk env first rv then none
        else some n
      | none => none
    | _ => none

/-- The names an input constant lists as members of its family: an inductive's `all` and
constructors, a constructor's inductive, a recursor's `all` and its rules' constructors. -/
@[expose] def familyNamesOf : Ix.ConstantInfo → List Ix.Name
  | .inductInfo v => v.all.toList ++ v.ctors.toList
  | .ctorInfo c => [c.induct]
  | .recInfo r => r.all.toList ++ r.rules.toList.map (·.ctor)
  | _ => []

/-- An input name and a name its family lists (`familyNamesOf`) that is not an input
constant's own name, spelled exactly, the first met, if any. `Ix.Name`'s `==` compares
stored hashes only, so a name stored nowhere that carries another's hash would otherwise be
looked up as that other name; with none, every family name is an input key exactly
(`Ix.Cert.FamilyNamesStored`, with `misnamedInput`). -/
@[expose] def unstoredFamilyName (env : Ix.Environment) : Option (Ix.Name × Ix.Name) :=
  env.consts.toList.findSome? fun (n, ci) =>
    ((familyNamesOf ci).find? fun a =>
      !(env.consts.get? a).any fun ci' => Ix.nameCompareExact ci'.getCnst.name a == .eq).map (n, ·)

/-- The names of the family whose Lean block is `block`: the names it lists, then the
constructors of each inductive it lists. -/
@[expose] def familyNames (env : Ix.Environment) (block : Array Ix.Name) : Array Ix.Name :=
  block ++ block.flatMap fun n =>
    match env.consts.get? n with
    | some (.inductInfo iv) => iv.ctors
    | _ => #[]

/-- Whether the compile block `all` holds exactly the names `names` (by `==`). -/
@[expose] def sameNames (all : Ix.Set Ix.Name) (names : Array Ix.Name) : Bool :=
  let set : Ix.Set Ix.Name := Std.HashSet.ofList names.toList
  all.toList.all set.contains && names.all all.contains

/-- Whether an inductive family's motive positions fit the compiled records' 64-bit
fields: its members and auxiliary motives number fewer than `2 ^ 63`. -/
@[expose] def familySized (iv : Ix.InductiveVal) : Bool :=
  decide (iv.all.size + iv.numNested < 2 ^ 63)

/-- Whether the compile block `all` is the family of its member `y`: exactly the types and
constructors of `y`'s family when `y` is an inductive or a constructor of an input inductive;
exactly the input recursors with `y`'s `all[0]` (`recs`, `familyRecursors`, by the name's
hash) when `y` is a recursor whose `all[0]` is an input inductive with `y`'s `all`, of a
family that is `familySized`. Any other member passes. -/
@[expose] def familyBlockOk (env : Ix.Environment) (recs : Std.HashMap Address (Array Ix.Name))
    (all : Ix.Set Ix.Name) (y : Ix.Name) : Bool :=
  match env.consts.get? y with
  | some (.inductInfo iv) => sameNames all (familyNames env iv.all)
  | some (.ctorInfo cv) =>
    match env.consts.get? cv.induct with
    | some (.inductInfo iv) => sameNames all (familyNames env iv.all)
    | _ => false
  | some (.recInfo rv) =>
    match rv.all[0]? with
    | some first =>
      match env.consts.get? first with
      | some (.inductInfo iv) =>
        namesEq rv.all iv.all && familySized iv &&
        (all.toList.all fun x =>
          match env.consts.get? x with
          | some (.recInfo rx) => rx.all[0]?.any (Ix.Name.beqRaw · first)
          | _ => false) &&
        (recs.getD first.getHash #[]).all all.contains
      | _ => false
    | none => false
  | _ => true

/-- A block of the condensation `blocks` (its representative) and a member of it whose family
it is not exactly (`familyBlockOk`), the first met, if any. The compile compiles each block
of its condensation as one unit; with none, a block holding a family member holds exactly
that family's types and constructors, or exactly its recursors
(`Ix.Cert.FamilyBlocks`). -/
@[expose] def strayFamilyMember (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Option (Ix.Name × Ix.Name) :=
  let recs := familyRecursors env
  blocks.blocks.toList.findSome? fun (rep, all) =>
    (all.toList.find? fun y => !familyBlockOk env recs all y).map (rep, ·)

/-- The inductive members of a block's members, with their positions
(`Ix.CompileCert.ReaderIndex.inductives`). -/
@[expose] def inductiveMembers (members : Array Ixon.MutConst) : Array (Nat × Ixon.Inductive) :=
  members.zipIdx.filterMap fun | (.indc ind, index) => some (index, ind) | _ => none

/-- The positions of `owner`'s members among the first `count` carriers
(`Ix.CompileCert.ReaderIndex.orderFor`). -/
@[expose] def motiveOrder (carriers : Array (Ix.Kernel.ConstRef Address)) (owner : Address) (count : Nat) :
    Array Nat :=
  (carriers.extract 0 count).filterMap fun
    | .member block index => if block == owner then some index else none
    | .ctor .. => none

/-- Whether `order` orders the block's inductive members, starting at `firstIndex`
(`Ix.CompileCert.ReaderIndex.orderValid`). -/
@[expose] def motiveOrderValid (firstIndex : Nat) (indcs : Array (Nat × Ixon.Inductive)) (order : Array Nat) :
    Bool :=
  order.size == indcs.size && order[0]? == some firstIndex &&
    order.all (fun index => indcs.any (·.1 == index)) && order.toList.eraseDups.length == indcs.size

/-- **The analysis the recursor index files a recursor member by**, when it files it
(`Ix.CompileCert.ReaderIndex.candidate`, before its one-recursor-per-motive test): its block
and motive, its motives' carriers, its major premise's carrier. -/
@[expose] def recursorAnalysis? (store : Ix.Kernel.Reader.Store) (owner : Address) (c : Ixon.Constant)
    (r : Ixon.Recursor) :
    Option (Address × Nat × Array (Ix.Kernel.ConstRef Address) × Ix.Kernel.ConstRef Address) := do
  let (motive, carriers, major) ← Ix.Kernel.Reader.analyseRecursor store owner c r
  let .member block firstIndex ← carriers[0]? | none
  let blockRecord ← store block
  let .muts members := blockRecord.info | none
  let indcs := inductiveMembers members
  let _ ← indcs[0]?
  guard (motiveOrderValid firstIndex indcs (motiveOrder carriers block indcs.size))
  pure (block, motive, carriers, major)

/-- The slot a recursor member is filed at: its block and motive. -/
@[expose] def recursorSlot? (store : Ix.Kernel.Reader.Store) (owner : Address) (c : Ixon.Constant)
    (r : Ixon.Recursor) : Option (Address × Nat) :=
  (recursorAnalysis? store owner c r).map fun (b, m, _, _) => (b, m)

/-- The motive an input recursor's name gives it in its family's block, in
`Ix.LeanIngress.blockRecursors`' order: `T.rec` for the `i`-th member `T` of `first.all`;
`first.rec_{j+1}` for `j < first.numNested` at `first.all.size + j`. -/
@[expose] def namedMotive? (first : Ix.InductiveVal) (n : Ix.Name) : Option Nat :=
  (first.all.toList.findIdx? fun T => Ix.LeanIngress.isStrName T "rec" n).orElse fun _ =>
    ((List.range first.numNested).find? fun j =>
      Ix.LeanIngress.isStrName first.cnst.name s!"rec_{j + 1}" n).map (first.all.size + ·)

/-- The record member a published name sits at: a recursor projection's block member, or a
lone recursor's member 0. -/
@[expose] def publishedRecursor? (ixe : Ixon.Env) (n : Ix.Name) : Option (Address × Nat) := do
  let named ← ixe.named.get? n
  let c ← storedRecord ixe named.addr
  match c.info with
  | .rPrj q => pure (q.block, q.idx.toNat)
  | .recr _ => pure (named.addr, 0)
  | _ => none

/-- What the recursor shape check found. -/
inductive RecursorShapeError where
  /-- a stored recursor member the recursor index would not file -/
  | unanalysed (owner : Address) (member : Nat)
  /-- two stored recursor members on one slot -/
  | clash (block : Address) (motive : Nat)
  /-- a published input recursor whose name gives no motive in its family -/
  | unnamed (n : Ix.Name)
  /-- a published input recursor not filed at its family's block and named motive, with
  the block's members as its first carriers -/
  | misfiled (n : Ix.Name)
  /-- a published input recursor whose major premise's constructors are not its rules' -/
  | major (n : Ix.Name)

/-- The text of a recursor shape refusal. -/
@[expose] def RecursorShapeError.message : RecursorShapeError → String
  | .unanalysed o j => s!"the recursor at member {j} of the record {o} does not have the shape \
      the recursor index files by"
  | .clash b m => s!"two stored recursor records fall on motive {m} of the inductive block at {b}"
  | .unnamed n => s!"the input recursor {n.pretty} is named neither T.rec for a member T of its \
      family nor rec_j for an auxiliary motive j of it"
  | .misfiled n => s!"the input recursor {n.pretty} is not filed at its family's block and the \
      motive its name gives it, with the block's members as its first carriers"
  | .major n => s!"the major premise of the input recursor {n.pretty} is not an inductive whose \
      constructors, in order, are its rules' constructors"

/-- Each stored recursor member, by its record and position, with its slot
(`recursorSlot?`), analysed on tasks (`parMap`). -/
@[expose] def recursorSlots (ixe : Ixon.Env) : List ((Address × Nat) × Option (Address × Nat)) :=
  (parMap (fun (e : Address × Ixon.Constant) =>
    (Ix.Kernel.Reader.recursorMembers e.2).toList.map fun (j, r) =>
      ((e.1, j), recursorSlot? (storedRecord ixe) e.1 e.2 r))
    (storedRecursorRecords ixe)).toList.flatten

/-- A stored recursor member that is not filed, or a slot two stored recursor members are
filed at, the first met, if any. Every filed member's first slot is recorded, then each
member is compared with its slot's. -/
@[expose] def recursorSlotError (ixe : Ixon.Env) : Option RecursorShapeError :=
  let slots := recursorSlots ixe
  match slots.find? (·.2.isNone) with
  | some ((o, j), _) => some (.unanalysed o j)
  | none =>
    let filed := slots.filterMap fun (k, s) => s.map (·, k)
    let first : Std.HashMap (Address × Nat) (Address × Nat) := filed.foldl (init := {}) fun m (s, k) =>
      if m.contains s then m else m.insert s k
    filed.findSome? fun (s, k) => if decide (first[s]? = some k) then none else some (.clash s.1 s.2)

/-- Whether the recursor's rules' constructors are, in order, the constructors of the
inductive at member `mi` of the block `mb`: each published where it resolves to its
position. -/
@[expose] def rulesAt (ixe : Ixon.Env) (rv : Ix.RecursorVal) (mb : Address) (mi : Nat) : Bool :=
  (List.finRange rv.rules.size).all fun k =>
    match ixe.named.get? rv.rules[k].ctor with
    | some cn => Ix.Kernel.Reader.resolve (storedRecord ixe) cn.addr == some (.ctor mb mi k.val)
    | none => false

/-- The published input recursor `n` (`rv`), when it is not filed by its name: at its
family's block, at the motive its name gives it (`namedMotive?`), its first carriers the
block's members in order, its major premise an inductive whose constructors, in order, are
where its rules' constructors are published. An unpublished name passes. -/
@[expose] def recursorNameError (env : Ix.Environment) (ixe : Ixon.Env) (n : Ix.Name)
    (rv : Ix.RecursorVal) : Option RecursorShapeError :=
  if (ixe.named.get? n).isNone then none else
  match rv.all[0]? with
  | none => some (.unnamed n)
  | some first =>
    match env.consts.get? first with
    | some (.inductInfo fv) =>
      match namedMotive? fv n with
      | none => some (.unnamed n)
      | some m =>
        match ixe.named.get? first, publishedRecursor? ixe n with
        | some fnamed, some (owner, j) =>
          match storedRecord ixe owner with
          | none => some (.misfiled n)
          | some c =>
            match (Ix.Kernel.Reader.recursorMembers c).find? (·.1 == j) with
            | none => some (.misfiled n)
            | some (_, r) =>
              match recursorAnalysis? (storedRecord ixe) owner c r with
              | none => some (.unanalysed owner j)
              | some (b, m', carriers, major) =>
                if b == recordBlock ixe fnamed.addr && m' == m &&
                    (List.range fv.all.size).all (fun i => carriers[i]? == some (.member b i)) then
                  match major with
                  | .ctor .. => some (.major n)
                  | .member mb mi =>
                    match Ix.Kernel.Reader.inductiveAt (storedRecord ixe) (.member mb mi) with
                    | none => some (.major n)
                    | some ind =>
                      if ind.ctors.size == rv.rules.size && rulesAt ixe rv mb mi then none
                      else some (.major n)
                else some (.misfiled n)
        | _, _ => some (.misfiled n)
    | _ => some (.unnamed n)

/-- **Recursors have the shapes Lean gives them**: a stored recursor member that the
recursor index would not file, or two filed at one slot (`recursorSlotError`); otherwise a
published input recursor not filed by its name (`recursorNameError`, input constants read on
tasks), the first met, if any. With none, every stored recursor member is filed at a slot of
its own (`Ix.Cert.RecursorSlotsUnique`) and every published input family recursor at its
family's block and named motive, with its rules' constructors its major premise's
(`Ix.Cert.RecursorShapes`). The index files a recursor by its type, which the compiler
copies; quotient Source reads it by its name. -/
@[expose] def recursorShapeError (env : Ix.Environment) (ixe : Ixon.Env) : Option RecursorShapeError :=
  match recursorSlotError ixe with
  | some e => some e
  | none =>
    (parMap (fun (e : Ix.Name × Ix.ConstantInfo) =>
      match e.2 with
      | .recInfo rv => recursorNameError env ixe e.1 rv
      | _ => none) env.consts.toArray).findSome? id

/-- A stored record's definition projection: the member it projects (its block's
address and its index) and the record's address. -/
@[expose] def definitionProjection (e : Address × Ixon.LazyConstant) : Option ((Address × Nat) × Address) :=
  match e.2.get? with
  | some c =>
    match c.info with
    | .dPrj p => some ((p.block, p.idx.toNat), e.1)
    | _ => none
  | none => none

/-- Whether the uncached decoder's first TagN can introduce a definition
projection. This reads the same buffer and offset as `LazyConstant.get?`,
without imposing a window-length check that the decoder itself does not run. -/
@[expose] def definitionProjectionHeader (buf : ByteArray) (off : Nat) : Bool :=
  match (Ixon.getTagN 4).run { idx := off, bytes := buf } with
  | .ok tag _ => tag.flag == Ixon.Constant.FLAG && tag.value == Ixon.ConstantInfo.CONST_DPRJ
  | .error _ _ => false

/-- The same projection as `definitionProjection`, with a header filter before
decoding an uncached record (`ProjectionRead.fast_eq`, on every input). A
cached constant takes precedence over its bytes, as in `LazyConstant.get?`.
Only a possible definition projection needs its complete payload decoded. -/
@[expose] def definitionProjectionFast (e : Address × Ixon.LazyConstant) :
    Option ((Address × Nat) × Address) :=
  match e.2.cache with
  | some _ => definitionProjection e
  | none =>
    if definitionProjectionHeader e.2.buf e.2.off then definitionProjection e else none

/-- A member two stored definition projection records project, if any: its
block's address and its index. The reader takes a definition block member's
hint at its projection record (`Ix.Cert.hintsOf`), so with none the record it
reads the hint at is the member's one projection record
(`Ix.Cert.CtxAgree.hintsOf_projection`'s premise). Every record's first
projection of a member is filed, then each record is compared with its member's
filed one. The cheap header filter skips non-projections, and each candidate
is decoded once before the two passes over projection pairs. -/
@[expose] def projectionCollision (ixe : Ixon.Env) : Option (Address × Nat) :=
  let entries := ixe.consts.toList.filterMap definitionProjectionFast
  let first : Std.HashMap (Address × Nat) Address := entries.foldl (init := {}) fun m (r, a) =>
    if m.contains r then m else m.insert r a
  entries.findSome? fun (r, a) => if decide (first[r]? = some a) then none else some r

/-- Whether stored bytes open with the TagN header of a block record
(`Ixon.Constant.FLAG_MUTS`). Only the first TagN is read. -/
@[expose] def blockHeader (bytes : ByteArray) : Bool :=
  match (Ixon.getTagN 4).run { idx := 0, bytes } with
  | .ok tag _ => tag.flag == Ixon.Constant.FLAG_MUTS
  | .error _ _ => false

/-- The first published input name whose address holds no stored record, or a
block record (`blockHeader`), if any. The reader keys an address only through a
record that resolves to a reference, a singleton or a projection
(`Ix.Kernel.Reader.resolveSource`), never through a block, so a published input
name at such an address would read as no constant. A `Muts` entry's name is not
an input name. -/
@[expose] def unreadablePublished (env : Ix.Environment) (ixe : Ixon.Env) : Option Ix.Name :=
  ixe.named.toList.findSome? fun (n, named) =>
    if env.consts.contains n then
      match ixe.consts.get? named.addr with
      | some lc => if blockHeader lc.rawBytes then some n else none
      | none => some n
    else none

/-- The first published input definition, theorem or opaque whose address has no reducibility
hint in the artifact (`Ixon.Env.anonHints`), if any. The reader takes a definition's hint from
`anonHints` at its address (`Ix.Cert.hintsOf`), as quotient Source does (`fiberHintsMap`), so a
definition without one would be read at no hint. The compile records every definition's hint,
so a real artifact has one at every published definition's address. -/
@[expose] def unhintedDefinition (env : Ix.Environment) (ixe : Ixon.Env) : Option Ix.Name :=
  ixe.named.toList.findSome? fun (n, named) =>
    match env.consts.get? n with
    | some (.defnInfo _) | some (.thmInfo _) | some (.opaqueInfo _) =>
      if ixe.anonHints.contains named.addr then none else some n
    | _ => none

/-- `compileReport`'s twenty-one checks on a compile's result, each an error on
any inconsistency. **Coverage:** every input constant is published or listed
as failed, exactly one of the two. **Authenticity:** every record and blob is
stored at the admission hash of its bytes. **Acyclic references:** no stored
record is on a reference cycle (`referenceCycle`), so the records have an
order in which none precedes a record it references. **Distinct name
hashes:** no two different names among the input's constants and the
published names share a stored hash (`nameHashCollision`). **`Muts` entries
agree with the blocks:** each name a `Muts` entry lists in class `i` is
published at member `i`'s projection of its block (`mutsMismatch`).
**Resolved names are published where they resolve:** each name of the
driver's final resolution map (`cenv.nameToAddr`) is published at the address it resolves
to (`resolutionMismatch`). **Published input names are resolved:** each
published input name is in the resolution map (`unresolvedPublished`). **Input constants carry their names:** each input
constant's own name is spelled as the name it is stored under
(`misnamedInput`). **Input constructors belong to their inductive:** each
constructor an input inductive lists is stored as a constructor of it
(`strayConstructor`). **One projection record per definition member:**
no two stored definition projection records project one member
(`projectionCollision`). **Published input names are readable:** each
published input name's address holds a stored record that is not a block
(`unreadablePublished`). **Blobs and records apart:** no address holds both a
stored blob and a stored record (`blobRecordCollision`). **Indexed recursors
belong to their block's family:** every input name published in an inductive
block the recursor index attaches recursors to has a family, and each of those
recursors is a published recursor of it (`unownedRecursor`). **Bound roles'
records have their kinds:** under the default role table, the stored record at a
bound `Nat` operation's address is a standalone definition, and at a bound axiom
role's address an axiom (`roleRecordKind`). **Literal-support roles are named:**
under the default role table, a role a stored record's literal is checked against
(the `Nat` basis, and the string support for a `String` literal) whose address the
artifact stores a record at is an input constant published at that address
(`literalRoleUnnamed`). **Inductive inputs have Lean's shapes:** every name an
input family lists is an input constant's own name (`unstoredFamilyName`); every input
inductive's `j`-th constructor declares index `j` (`misplacedConstructor`); a
family's members, constructors and recursors share its level-parameter names, a
recursor's of its family's count or one more (`strayLevelParams`); every block of the condensation `blocks` (by default the
compile's, `compileBlocks`) that holds a family member is exactly one family's
types and constructors, or exactly its recursors (`strayFamilyMember`); and every
stored recursor member is filed by the recursor index at a slot of its own, every
published input recursor at the slot its name gives it (`recursorShapeError`). **Published
definitions have hints:** every published input definition, theorem or opaque has a reducibility
hint at its address (`unhintedDefinition`). -/
@[expose] def checkReport (env : Ix.Environment)
    (cenv : Ix.CompileM.CompileEnv) (out : Ixon.Env × Failures)
    (blocks : Ix.CondensedBlocks := compileBlocks env) : Except String Unit :=
  match uncovered env out.1 out.2, unauthentic out.1 with
  | [], [] =>
    match referenceCycle out.1 with
    | none =>
      match nameHashCollision env out.1 with
      | none =>
        match mutsMismatch out.1 with
        | none =>
          match resolutionMismatch cenv.nameToAddr out.1 with
          | none =>
            match unresolvedPublished env cenv.nameToAddr out.1 with
            | none =>
              match misnamedInput env with
              | none =>
                match strayConstructor env with
                | none =>
                  match projectionCollision out.1 with
                  | none =>
                    match unreadablePublished env out.1 with
                    | none =>
                      match blobRecordCollision out.1 with
                      | none =>
                        match unownedRecursor env out.1, roleRecordKind out.1,
                            literalRoleUnnamed env out.1 with
                        | none, none, none =>
                          match unstoredFamilyName env, misplacedConstructor env, strayLevelParams env,
                              strayFamilyMember env blocks, recursorShapeError env out.1 with
                          | none, none, none, none, none =>
                            match unhintedDefinition env out.1 with
                            | none => .ok ()
                            | some n =>
                              .error s!"compileReport: hint check failed: the published definition \
                                {n.pretty} has no reducibility hint at its address"
                          | some (n, a), _, _, _, _ =>
                            .error s!"compileReport: inductive input check failed: the input constant \
                              {n.pretty} lists {a.pretty} in its family, which is not an input \
                              constant's own name"
                          | none, some c, _, _, _ =>
                            .error s!"compileReport: inductive input check failed: the constructor \
                              {c.pretty} of an input inductive declares another index than its position \
                              in the inductive's constructors"
                          | none, none, some x, _, _ =>
                            .error s!"compileReport: inductive input check failed: {x.pretty} does not \
                              have the level parameters of its family (for a recursor: its family's \
                              recursors' list, of its family's count or one more)"
                          | none, none, none, some (_, y), _ =>
                            .error s!"compileReport: inductive input check failed: the compile block of \
                              {y.pretty} is not exactly its family's types and constructors, or its \
                              family's recursors, or the family has 2^63 members and auxiliary motives \
                              or more"
                          | none, none, none, none, some e =>
                            .error s!"compileReport: inductive input check failed: {e.message}"
                        | none, none, some (s, b) =>
                          .error s!"compileReport: literal-role check failed: the artifact stores \
                            a record at {b}, the default role table's address of the literal-support \
                            role {repr s}, which a stored record's literal is checked against, but \
                            {(literalRoleIxName s).pretty} is not an input constant published there"
                        | none, some (r, p), _ =>
                          .error s!"compileReport: role check failed: the record stored at {p}, \
                            the default role table's address of the role {repr r}, is not of its \
                            specification's kind (a standalone definition for a Nat operation, \
                            an axiom for an axiom role)"
                        | some (b, x, none), _, _ =>
                          .error s!"compileReport: recursor check failed: the input name \
                            {x.pretty}, published in the inductive block at {b} that the recursor \
                            index attaches recursors to, is not an inductive, constructor or \
                            recursor of a family"
                        | some (b, x, some r), _, _ =>
                          let pos := match r with
                            | .member _ j => j
                            | .ctor _ i _ => i
                          .error s!"compileReport: recursor check failed: the recursor at member \
                            {pos} of the record {r.block}, indexed under the inductive block at {b}, \
                            is not a published recursor of the family of {x.pretty}, published in \
                            that block"
                      | some a =>
                        .error s!"compileReport: blob check failed: the address {a} holds both \
                          a stored blob and a stored record"
                    | some n =>
                      .error s!"compileReport: readability check failed: the input name \
                        {n.pretty} is published at an address that holds no stored record, \
                        or a block record"
                  | some (b, i) =>
                    .error s!"compileReport: projection check failed: member {i} of the block at \
                      {b} has more than one stored definition projection record"
                | some c =>
                  .error s!"compileReport: constructor check failed: the name {c.pretty}, a \
                    constructor of an input inductive, is not stored as a constructor of it"
              | some n =>
                .error s!"compileReport: name invariant failed: the input constant stored \
                  under {n.pretty} carries another name"
            | some n =>
              .error s!"compileReport: publication check failed: the input name {n.pretty} \
                is published but not resolved"
          | some (n, a, published) =>
            let found := match published with
              | some b => s!"published at {b}"
              | none => "not published"
            .error s!"compileReport: resolution check failed: {n.pretty} resolves to {a} but is {found}"
        | some (entry, i, h) =>
          .error s!"compileReport: Muts check failed: the entry {entry.pretty} lists the name \
            hash {h} in class {i}, which is not published at that member's projection of its block"
      | some (a, b) =>
        .error s!"compileReport: name check failed: {a.pretty} and {b.pretty} are different \
          names with one name hash"
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

/-! ### `checkReport` on tasks

`checkReport`'s checks are independent. The compiled code of `checkReport` is
`checkReportPar` (`checkReport_eq_par`, a `csimp` lemma proved by `rfl`): every
check is started as a task first, and the results are then read in
`checkReport`'s order, so a refusal is the first failing check's, as before.
The checks are passed to `checkReportOf`, which is not inlined, so that all of
them are started before the first result is read. -/

/-- `checkReport`'s checks, each a task. -/
structure CheckTasks where
  uncovered : Task (List Ix.Name)
  unauthentic : Task (List Address)
  referenceCycle : Task (Option (List Address))
  nameHashCollision : Task (Option (Ix.Name × Ix.Name))
  mutsMismatch : Task (Option (Ix.Name × Nat × Address))
  resolutionMismatch : Task (Option (Ix.Name × Address × Option Address))
  unresolvedPublished : Task (Option Ix.Name)
  misnamedInput : Task (Option Ix.Name)
  strayConstructor : Task (Option Ix.Name)
  projectionCollision : Task (Option (Address × Nat))
  unreadablePublished : Task (Option Ix.Name)
  blobRecordCollision : Task (Option Address)
  unownedRecursor : Task (Option (Address × Ix.Name × Option (Ix.Kernel.ConstRef Address)))
  roleRecordKind : Task (Option (Ix.Kernel.Role × Address))
  literalRoleUnnamed : Task (Option (Ix.Kernel.Role × Address))
  unstoredFamilyName : Task (Option (Ix.Name × Ix.Name))
  misplacedConstructor : Task (Option Ix.Name)
  strayLevelParams : Task (Option Ix.Name)
  strayFamilyMember : Task (Option (Ix.Name × Ix.Name))
  recursorShapeError : Task (Option RecursorShapeError)
  unhintedDefinition : Task (Option Ix.Name)

/-- `checkReport`'s verdict, read from its checks' tasks in `checkReport`'s order. -/
@[noinline, expose] def checkReportOf (out : Ixon.Env × Failures) (ts : CheckTasks) :
    Except String Unit :=
  match ts.uncovered.get, ts.unauthentic.get with
  | [], [] =>
    match ts.referenceCycle.get with
    | none =>
      match ts.nameHashCollision.get with
      | none =>
        match ts.mutsMismatch.get with
        | none =>
          match ts.resolutionMismatch.get with
          | none =>
            match ts.unresolvedPublished.get with
            | none =>
              match ts.misnamedInput.get with
              | none =>
                match ts.strayConstructor.get with
                | none =>
                  match ts.projectionCollision.get with
                  | none =>
                    match ts.unreadablePublished.get with
                    | none =>
                      match ts.blobRecordCollision.get with
                      | none =>
                        match ts.unownedRecursor.get, ts.roleRecordKind.get,
                            ts.literalRoleUnnamed.get with
                        | none, none, none =>
                          match ts.unstoredFamilyName.get, ts.misplacedConstructor.get, ts.strayLevelParams.get,
                              ts.strayFamilyMember.get, ts.recursorShapeError.get with
                          | none, none, none, none, none =>
                            match ts.unhintedDefinition.get with
                            | none => .ok ()
                            | some n =>
                              .error s!"compileReport: hint check failed: the published definition \
                                {n.pretty} has no reducibility hint at its address"
                          | some (n, a), _, _, _, _ =>
                            .error s!"compileReport: inductive input check failed: the input constant \
                              {n.pretty} lists {a.pretty} in its family, which is not an input \
                              constant's own name"
                          | none, some c, _, _, _ =>
                            .error s!"compileReport: inductive input check failed: the constructor \
                              {c.pretty} of an input inductive declares another index than its position \
                              in the inductive's constructors"
                          | none, none, some x, _, _ =>
                            .error s!"compileReport: inductive input check failed: {x.pretty} does not \
                              have the level parameters of its family (for a recursor: its family's \
                              recursors' list, of its family's count or one more)"
                          | none, none, none, some (_, y), _ =>
                            .error s!"compileReport: inductive input check failed: the compile block of \
                              {y.pretty} is not exactly its family's types and constructors, or its \
                              family's recursors, or the family has 2^63 members and auxiliary motives \
                              or more"
                          | none, none, none, none, some e =>
                            .error s!"compileReport: inductive input check failed: {e.message}"
                        | none, none, some (s, b) =>
                          .error s!"compileReport: literal-role check failed: the artifact stores \
                            a record at {b}, the default role table's address of the literal-support \
                            role {repr s}, which a stored record's literal is checked against, but \
                            {(literalRoleIxName s).pretty} is not an input constant published there"
                        | none, some (r, p), _ =>
                          .error s!"compileReport: role check failed: the record stored at {p}, \
                            the default role table's address of the role {repr r}, is not of its \
                            specification's kind (a standalone definition for a Nat operation, \
                            an axiom for an axiom role)"
                        | some (b, x, none), _, _ =>
                          .error s!"compileReport: recursor check failed: the input name \
                            {x.pretty}, published in the inductive block at {b} that the recursor \
                            index attaches recursors to, is not an inductive, constructor or \
                            recursor of a family"
                        | some (b, x, some r), _, _ =>
                          let pos := match r with
                            | .member _ j => j
                            | .ctor _ i _ => i
                          .error s!"compileReport: recursor check failed: the recursor at member \
                            {pos} of the record {r.block}, indexed under the inductive block at {b}, \
                            is not a published recursor of the family of {x.pretty}, published in \
                            that block"
                      | some a =>
                        .error s!"compileReport: blob check failed: the address {a} holds both \
                          a stored blob and a stored record"
                    | some n =>
                      .error s!"compileReport: readability check failed: the input name \
                        {n.pretty} is published at an address that holds no stored record, \
                        or a block record"
                  | some (b, i) =>
                    .error s!"compileReport: projection check failed: member {i} of the block at \
                      {b} has more than one stored definition projection record"
                | some c =>
                  .error s!"compileReport: constructor check failed: the name {c.pretty}, a \
                    constructor of an input inductive, is not stored as a constructor of it"
              | some n =>
                .error s!"compileReport: name invariant failed: the input constant stored \
                  under {n.pretty} carries another name"
            | some n =>
              .error s!"compileReport: publication check failed: the input name {n.pretty} \
                is published but not resolved"
          | some (n, a, published) =>
            let found := match published with
              | some b => s!"published at {b}"
              | none => "not published"
            .error s!"compileReport: resolution check failed: {n.pretty} resolves to {a} but is {found}"
        | some (entry, i, h) =>
          .error s!"compileReport: Muts check failed: the entry {entry.pretty} lists the name \
            hash {h} in class {i}, which is not published at that member's projection of its block"
      | some (a, b) =>
        .error s!"compileReport: name check failed: {a.pretty} and {b.pretty} are different \
          names with one name hash"
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


/-- `checkReport` with every check started as a task before any result is read. -/
@[expose] def checkReportPar (env : Ix.Environment)
    (cenv : Ix.CompileM.CompileEnv) (out : Ixon.Env × Failures)
    (blocks : Ix.CondensedBlocks := compileBlocks env) : Except String Unit :=
  checkReportOf out {
    uncovered := Task.spawn fun _ => uncovered env out.1 out.2
    unauthentic := Task.spawn fun _ => unauthentic out.1
    referenceCycle := Task.spawn fun _ => referenceCycle out.1
    nameHashCollision := Task.spawn fun _ => nameHashCollision env out.1
    mutsMismatch := Task.spawn fun _ => mutsMismatch out.1
    resolutionMismatch := Task.spawn fun _ => resolutionMismatch cenv.nameToAddr out.1
    unresolvedPublished := Task.spawn fun _ => unresolvedPublished env cenv.nameToAddr out.1
    misnamedInput := Task.spawn fun _ => misnamedInput env
    strayConstructor := Task.spawn fun _ => strayConstructor env
    projectionCollision := Task.spawn fun _ => projectionCollision out.1
    unreadablePublished := Task.spawn fun _ => unreadablePublished env out.1
    blobRecordCollision := Task.spawn fun _ => blobRecordCollision out.1
    unownedRecursor := Task.spawn fun _ => unownedRecursor env out.1
    roleRecordKind := Task.spawn fun _ => roleRecordKind out.1
    literalRoleUnnamed := Task.spawn fun _ => literalRoleUnnamed env out.1
    unstoredFamilyName := Task.spawn fun _ => unstoredFamilyName env
    misplacedConstructor := Task.spawn fun _ => misplacedConstructor env
    strayLevelParams := Task.spawn fun _ => strayLevelParams env
    strayFamilyMember := Task.spawn fun _ => strayFamilyMember env blocks
    recursorShapeError := Task.spawn fun _ => recursorShapeError env out.1
    unhintedDefinition := Task.spawn fun _ => unhintedDefinition env out.1 }

/-- **`checkReport` runs as `checkReportPar`**: a spawned task's value is its
function's (`Task.spawn`), so the two are the same function. -/
@[csimp] theorem checkReport_eq_par : @checkReport = @checkReportPar := rfl

/-- **The pure compiler, with its failures.** A block that fails to compile
is recorded, with its dependents, and left out of the environment; the
result is an error when the driver itself fails (a refused input, or a
condensation it cannot schedule). It ends with twenty-one checks (`checkReport`):
every input constant is published or reported as failed, exactly one of the
two; every record and blob is stored at the admission hash of its bytes; no
stored record is on a reference cycle; no two different input or
published names share a name hash; every `Muts` entry lists in class `i`
only names published at member `i`'s projection of its block; every name
the driver resolves is published at the address it resolves to; every
published input name is resolved; every input constant carries the name it
is stored under; every constructor an input inductive lists is stored as a
constructor of it; no two stored definition projection records project one
member; every published input name's address holds a stored
record that is not a block; no address holds both a stored blob and a stored
record; every input name published in an inductive block the recursor index
attaches recursors to has a family, and each of those recursors is a published
recursor of it;
under the default role table, the stored record at a bound `Nat` operation's
address is a standalone definition and at a bound axiom role's address an
axiom, and a role a stored record's literal is checked against whose address holds
a stored record is an input constant published there; and inductive inputs have
Lean's shapes: family names are input keys, constructor indices are positions, a
family shares its level-parameter names, each compile block holding a family member is exactly
that family's types and constructors or its recursors, and recursors are filed
by the recursor index at slots of their own, each published input recursor at
the one its name gives it; and every published input definition has a reducibility
hint at its address. Any inconsistency is an error, and no artifact is
returned. So coverage, authenticity, an order of the records in which none
precedes a record it references, distinct name hashes, `Muts` entries that agree
with their blocks, resolved names published where they resolve, resolved
published input names, readable published records, blobs apart from records, indexed recursors of their blocks' families, bound roles'
records of their kinds, named literal-support roles and Lean's inductive shapes
hold by construction (`Ix.Cert.compileCovers`, `Ix.Cert.compileAuthentic`,
`Ix.Cert.ClosureOrder`'s existence, `Ix.Cert.nameHashes_distinct`,
`Ix.Cert.mutsMismatch_none`, `Ix.Cert.resolvedPublished`, `Ix.Cert.publishedResolved`,
`Ix.Cert.publishedReadable`, `Ix.Cert.blobsApart`, `Ix.Cert.recursorsOwned`,
`Ix.Cert.roleRecordKinds`, `Ix.Cert.literalRolesNamed`,
`Ix.Cert.familyNamesStored`, `Ix.Cert.constructorIndices`, `Ix.Cert.familyLevelParams`,
`Ix.Cert.familyBlocks`, `Ix.Cert.recursorSlotsUnique`,
`Ix.Cert.recursorShapes`); on a consistent run the result is
`compileUnchecked`'s environment and failures, byte for byte. -/
@[expose] def compileReport (env : Ix.Environment) : Except String (Ixon.Env × Failures) := do
  let (ixe, failures, cenv) ← compileUnchecked env
  checkReport env cenv (ixe, failures)
  pure (ixe, failures)

/-- `compileUnchecked` on a ground split and a condensation the caller has
computed: `compileUnchecked env` is this at `groundSplit` of `env`'s map and
that split's condensation (`compileBlocks env`). -/
@[expose] def compileUncheckedWith (env : Ix.Environment)
    (split : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.GroundError)
    (blocks : Ix.CondensedBlocks) :
    Except String (Ixon.Env × Failures × Ix.CompileM.CompileEnv) := do
  let env : Ix.Environment := { consts := env.consts }
  let (ixe, _, cenv) ← Ix.CompileM.compileEnvFold env blocks
  let ungrounded := split.2.fold (init := {}) fun m n e =>
    m.insert n (e.refusal split.2.contains)
  pure (ixe, { ungrounded, blocks := cenv.ungrounded }, cenv)

/-- `compileReport` with the ground split and the condensation computed once:
its checks read the compile's condensation (`compileBlocks env`, the default
of `checkReport`), which the compile has computed already. -/
@[expose] def compileReportShared (env : Ix.Environment) :
    Except String (Ixon.Env × Failures) := do
  let split := groundSplit { consts := env.consts }
  let blocks := Ix.CondenseM.run split.1
  let (ixe, failures, cenv) ← compileUncheckedWith env split blocks
  checkReport env cenv (ixe, failures) blocks
  pure (ixe, failures)

/-- **`compileReport` runs as `compileReportShared`**: the two are the same
function, the condensation `compileReport`'s checks recompute being the one its
compile computed. -/
@[csimp] theorem compileReport_eq_shared : @compileReport = @compileReportShared := rfl

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
