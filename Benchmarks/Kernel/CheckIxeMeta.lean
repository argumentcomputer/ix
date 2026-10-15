import Benchmarks.Kernel.CheckIxeStep

/-! # `.meta`: the display table, the meta reader and the erasure run (untrusted harness)

IXC-PLAN §11 (step 6). `.meta` is the Ixon reading with display: its keys are
the `.anon` keys (record addresses, role keys, derived keys), and the reader's
output carries what the `.ixe`'s metadata says of the keys a record declares
(`Reader.Read.display`). It explains failures with names; it never decides.

* `displayTable`: what the metadata says of each key (`Reader.Display`): every
  Lean name the environment maps to the key's record address (an alias fiber
  has several), and, when the metadata is loaded in full (`Ixon.deEnv`), the
  level parameters' names. The key is the one a reading gives the address
  (`Reader.keyOfAddress`: a bound role's, else the address's own).
* `withDisplay`: the meta reader's last step, a `.meta` reading with the
  display of the keys it declares.
* `run` (`kernel-check-ixe --meta <input.ixe> <output.jsonl> [limit]`): **the
  erasure test.** Every record of the check order is read and checked twice,
  at `.anon` (as `kernel-check-ixe` does) and at `.meta` (the meta reader and
  the checker at `md = .meta`, under the same table, prelude, evidence and
  hints), and the two runs are compared record by record: the readings
  (declared keys exactly, terms by their cached hashes, display aside), the
  outcome, the fold position and the failure itself, whose keys are mapped
  from `.anon` to `.meta` by `Key.map id` (the same addresses). The rows are
  the `.anon` run's, with a failure's reason rendered by `.meta`
  (`Reader.spellWith`). Any difference is printed and fails the run (exit 1).
-/

namespace Benchmarks.Kernel.CheckIxeMeta

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-! ## The display table -/

/-- Lean's name (Ix's copy) as the kernel's, component by component. -/
def kernelName : Ix.Name → Ix.Kernel.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (kernelName p) s
  | .num p n _ => .num (kernelName p) n

/-- The level parameters' names the metadata gives a constant (none when the
metadata is not loaded, as in the streaming load). -/
def levelNamesOf (env : Ixon.Env) (m : Ixon.ConstantMeta) : List Ix.Kernel.Name :=
  let lvls : Array Address := match m.info with
    | .defn _ l .. | .axio _ l .. | .quot _ l .. | .indc _ l .. | .ctor _ l .. | .recr _ l .. => l
    | _ => #[]
  lvls.toList.filterMap fun a => (env.names[a]?).map kernelName

/-- **The display table** of an environment, keyed by the keys a reading with
the context `cx` gives the addresses the environment's names map to. -/
def displayTable (env : Ixon.Env) (cx : Ctx md) : DisplayTable md := Id.run do
  let mut t : DisplayTable md := {}
  for (name, named) in env.named.toList do
    let some k := cx.keys.byAddress[named.addr]? <|> keyOfAddress cx.store cx.roles named.addr
      | continue
    let (d, _) := t.getD k ({}, named.addr)
    let lvls := if d.levelNames.isEmpty then levelNamesOf env named.constMeta else d.levelNames
    t := t.insert k ({ d with names := d.names ++ [kernelName name], levelNames := lvls }, named.addr)
  -- an alias fiber's names in a fixed order
  return t.map fun _ (d, a) =>
    ({ d with names := (d.names.toArray.qsort (toString · < toString ·)).toList }, a)

/-! ## The meta reader -/

/-- The keys a declaration declares. -/
def declaredKeys : Ix.Kernel.Declaration md → List (CName md)
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv => [cv.name]
  | .indDecl block _ => block.map (·.name)
  | .basisDecl _ => []

/-- **The meta reader's last step**: the display of the keys the reading
declares, from the table. -/
def withDisplay (t : DisplayTable .meta) (rd : Read .meta) : Read .meta :=
  { rd with display := (rd.decls.toList.flatMap declaredKeys).filterMap fun k =>
      (t[k]?).map fun (d, _) => (k, d) }

/-- The reader context and the table's evidence at `.meta`, over a setup's
store and with its hints: what `CheckIxeStep.setup` builds at `.anon`. -/
def metaContext (s : Setup) (blobs : Address → Option ByteArray) (t : Ix.Kernel.RoleTable)
    (pre : Prelude .meta) (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Ctx .meta × Ix.Kernel.Evidences .meta :=
  let blobs' : Address → Option ByteArray := fun a =>
    blobs a <|> (pre.blobs.find? (·.1 == a)).map (·.2)
  let evidence : Std.HashMap Address Ixon.Constant := pre.evidence.foldl
    (fun m (a, c) => if s.store.contains a then m else m.insert a c) {}
  let look : Address → Option Ixon.Constant := fun a => s.store[a]? <|> evidence[a]?
  let cx : Ctx .meta := contextWith look blobs' t s.store.toArray hint
    (Ix.Kernel.Admission.projectionAddress Address.blake3 look)
  (cx, evidenceOf cx pre.state t)

/-! ## The erasure run -/

/-- An `.anon` key as a `.meta` key: the same address, role or shape. -/
def toMeta : Ix.Kernel.Key .anon → Ix.Kernel.Key .meta := Ix.Kernel.Key.map (fun a => a)

/-- A declaration's fingerprint up to its keys' mode: its kind, its declared
keys' and its terms' cached hashes (a term's hash is a function of its
structure and its keys' ids, the same in both modes), its level parameters
and counts. Terms are compared by hash: a structural comparison of two
readings would walk shared terms unshared. -/
def fingerprint : Ix.Kernel.Declaration md → List UInt64
  | .axiomDecl cv => [0] ++ cvPrint cv
  | .defnDecl cv v _ => [1] ++ cvPrint cv ++ [hash v]
  | .thmDecl cv v => [2] ++ cvPrint cv ++ [hash v]
  | .opaqueDecl cv v => [3] ++ cvPrint cv ++ [hash v]
  | .basisDecl _ => [4]
  | .indDecl block nP => [5, nP.toUInt64] ++ block.flatMap infoPrint
  | .quotDecl _ cv => [6] ++ cvPrint cv
where
  cvPrint (cv : Ix.Kernel.ConstantVal md) : List UInt64 :=
    [hash cv.name, cv.levelParams.length.toUInt64, hash cv.type]
  infoPrint (ci : Ix.Kernel.ConstantInfo md) : List UInt64 :=
    match ci with
    | .recInfo cv mI rP rules =>
      cvPrint cv ++ [mI.toUInt64, rP.toUInt64] ++
        rules.flatMap fun r => [hash r.ctor, r.nfields.toUInt64, hash r.rhs]
    | .ctorInfo cv nP nF => cvPrint cv ++ [nP.toUInt64, nF.toUInt64]
    | ci => cvPrint ci.toConstantVal

/-- Two failures are the same: the verdict and the message, keys included. -/
def sameError (a b : Ix.Kernel.CheckError .meta) : Bool :=
  a.verdictPrefix == b.verdictPrefix && a.msg == b.msg

structure Options where
  input : System.FilePath
  output : System.FilePath
  limit : Option Nat := none

def usage : String := "usage: kernel-check-ixe --meta <input.ixe> <output.jsonl> [limit]"

def parseArgs : List String → Option Options
  | [input, output] => some { input, output }
  | [input, output, limit] => do some { input, output, limit := some (← limit.toNat?) }
  | _ => none

/-- `kernel-check-ixe --meta`: the erasure test (module docstring). -/
def run (args : List String) : IO UInt32 := do
  let some o := parseArgs args | IO.eprintln usage; return 2
  let started ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile o.input
  let env ← IO.ofExcept (Ixon.deEnv bytes)
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let table ← IO.ofExcept defaultTable
  let preA : Prelude .anon ← IO.ofExcept (preludeFor table)
  let preM : Prelude .meta ← IO.ofExcept (preludeFor table)
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) table preA hints.lookup
  let (cxM, evM) := metaContext s (env.blobs[·]?) table preM hints.lookup
  let display := displayTable env cxM
  let names := reportNames env s.store
  let addresses := match o.limit with
    | some n => s.ordered.extract 0 (min n s.ordered.size)
    | none => s.ordered
  IO.eprintln s!"check-ixe --meta: {s.store.size} records, {addresses.size} in order, \
    {display.size} keys with display; loaded in {(← IO.monoMsNow) - started} ms"
  let handle ← IO.FS.Handle.mk o.output .write
  let counts ← IO.mkRef ({} : Std.HashMap String Nat)
  let failed ← IO.mkRef ({} : Std.HashMap Address Address)
  let diffs ← IO.mkRef (#[] : Array String)
  -- a record's rows (its own and its recursor records'), one outcome
  let note (address : Address) (v : RecordView) (outcome reason : String) (root : Address) :
      IO Unit := do
    let rows := #[(⟨address, names.getD address #[], v.kind, outcome, reason, 0, 0⟩ : Row)] ++
      v.recs.map fun r => (⟨r, names.getD r #[], "recursor", outcome, reason, 0, 0⟩ : Row)
    for row in rows do
      counts.modify fun c => c.insert outcome (c.getD outcome 0 + 1)
      if outcome != "accept" then failed.modify (·.insert row.address root)
      handle.putStrLn row.json.compress
  let mut stA : State .anon := {}
  let mut stM : State .meta := {}
  let mut ca : Checker .anon := {}
  let mut cm : Checker .meta := {}
  let mut consumed : Std.HashSet Address := {}
  let mut displayed := 0
  let mut index := 0
  for address in addresses do
    index := index + 1
    if index % 10000 == 0 then
      IO.eprintln s!"check-ixe --meta: {index}/{addresses.size} after {(← IO.monoMsNow) - started} ms; \
        {(← counts.get).toList}; {(← diffs.get).size} differences"
    if consumed.contains address then continue
    let some v := s.view address | continue
    let some source := s.store[address]? | continue
    for r in v.recs do consumed := consumed.insert r
    let readA := readRecord s.cx stA address source
    let readM := (readRecord cxM stM address source).map (withDisplay display)
    match readA, readM with
    | .error eA, .error eM =>
      unless toString eA == toString eM do
        diffs.modify (·.push s!"{address}: read errors differ: {eA} / {eM}")
      let (outcome, reason) := readOutcome eA
      note address v outcome reason address
    | .ok rA, .ok rM =>
      let keysA := (rA.decls.toList.flatMap declaredKeys).map toMeta
      let keysM := rM.decls.toList.flatMap declaredKeys
      unless keysA == keysM && rA.decls.toList.map fingerprint == rM.decls.toList.map fingerprint &&
          rA.generated == rM.generated do
        diffs.modify (·.push s!"{address}: readings differ")
      displayed := displayed + rM.display.length
      stA := stA.commit rA
      stM := stM.commit rM
      let f ← failed.get
      match (v.deps ()).find? f.contains with
      | some blocker =>
        let root := f.getD blocker blocker
        note address v "blocked" (toString root) root
      | none =>
        let (ca', eA) := ca.steps s.evidence rA.decls
        let (cm', eM) := cm.steps evM rM.decls
        ca := ca'
        cm := cm'
        let same := ca'.pos == cm'.pos && match eA, eM with
          | none, none => true
          | some a, some m => sameError (a.mapKeys toMeta) m
          | _, _ => false
        unless same do
          diffs.modify (·.push s!"{address}: verdicts differ: .anon {eA.map toString} at {ca'.pos}, \
            .meta {eM.map toString} at {cm'.pos}")
        match eM with
        | none => note address v "accept" "" address
        | some e =>
          let (outcome, reason) := checkOutcome e (spellWith display)
          note address v outcome reason address
    | .ok _, .error eM =>
      diffs.modify (·.push s!"{address}: .anon reads, .meta does not: {eM}")
      note address v "decline" s!"check-ixe --meta: .meta does not read: {eM}" address
    | .error eA, .ok _ =>
      diffs.modify (·.push s!"{address}: .meta reads, .anon does not: {eA}")
      let (outcome, reason) := readOutcome eA
      note address v outcome reason address
  handle.flush
  let diffs ← diffs.get
  IO.eprintln s!"check-ixe --meta: done in {(← IO.monoMsNow) - started} ms; {(← counts.get).toList}; \
    {displayed} declared keys with display; fold positions .anon {ca.pos}, .meta {cm.pos}"
  if diffs.isEmpty then
    IO.eprintln s!"check-ixe --meta: erasure: {addresses.size} records, .meta equals .anon on every \
      reading, outcome, position and failure"
    return 0
  IO.eprintln s!"check-ixe --meta: erasure FAILED: {diffs.size} records differ"
  for d in diffs.extract 0 50 do IO.eprintln s!"  {d}"
  return 1

end Benchmarks.Kernel.CheckIxeMeta
