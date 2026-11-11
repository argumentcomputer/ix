import Ix.IxVM.PwCheck
import Ix.IxVM.ClaimHarness
import Ix.Shard.Environment
import Ix.KernelCheck.Step
import Tests.Ix.IxVM.Harness
import IxVM.Fixture

/-!
# The binder-data annotator

`IxVM.PwHints.annotate` writes, for every record a witness carries, the datum
of every `Lam` and `All` node and the variant of every `Share` site, keyed as
the conversion's interface (`IxVM/IxVM/Source/Convert.lean`, "Binder data") says.

`ixvm-pw-hints` holds the annotator to hand-made records whose data are known:
* a sharing entry `x → x` with `x` loose, used under `A : Prop` and under
  `B : Type`: the binder is `ifAllZero []` at the first, `never` at the
  second, so the entry gets two variants;
* a `let` (the kernel annotates its body as the ζ-reduct, its value on its own);
* a datum with a level parameter, `(α : Sort u) → α → α`.
Each is checked by value, by the host-side check (`IxVM.PwHints.check`:
coverage, and every aligned binder against the kernel's own annotation pass),
and by tampering: a wrong datum is a mismatch, a dropped block a missing key.
The stream encoding round-trips.

`ixvm-pw-corpus` (manual) measures the annotator on a compiled corpus:
`IX_PW_IXE` (an `.ixe`), and with `IX_PW_IXES` (its shard manifest) each
shard's claim closure as `ix check` builds it, one line per shard.
-/

namespace Tests.Ix.IxVM.PwHints

open _root_.IxVM.PwHints

private def all := Ixon.Expr.leanAll
private def lam := Ixon.Expr.leanLam

/-- `x → x` with `x` loose: sharing entry 0 of `twoSorts`. -/
def arrowEntry : Ixon.Expr := all (.var 0) (.var 1)

/-- `(A : Prop) → (A → A) → (B : Type) → (B → B) → Prop`, both `_ → _` the
sharing entry 0. -/
def twoSortsType : Ixon.Expr :=
  all (.sort 0) (all (.share 0) (all (.sort 1) (all (.share 0) (.sort 0))))

def twoSorts : Ixon.Constant where
  info := .axio { isUnsafe := false, lvls := 0, typ := twoSortsType }
  sharing := #[arrowEntry]
  refs := #[]
  univs := #[.zero, .succ .zero]

/-- `fun p => let q : Prop := p → p; q → q`. -/
def letValue : Ixon.Expr :=
  lam (.sort 0) (Ixon.Expr.leanLet false (.sort 0) arrowEntry arrowEntry)

/-- `def _ : Prop → Prop := fun p => let q : Prop := p → p; q → q`. -/
def letBody : Ixon.Constant where
  info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := all (.sort 0) (.sort 0), value := letValue }
  sharing := #[]
  refs := #[]
  univs := #[.zero]

/-- `(α : Sort u) → α → α`. -/
def polyId : Ixon.Constant where
  info := .axio { isUnsafe := false, lvls := 1, typ := all (.sort 0) arrowEntry }
  sharing := #[]
  refs := #[]
  univs := #[.var 0]

private def never : Node := .binder none
private def always : Node := .binder (some #[])

/-- The expected blocks of each record. -/
def expected : List (Ixon.Constant × Array Block) := [
  (twoSorts, #[⟨0, 0, 0, #[never, never, .share 0, never, never, .share 1]⟩,
               ⟨1, 0, 0, #[always]⟩, ⟨1, 0, 1, #[never]⟩]),
  (letBody, #[⟨0, 0, 0, #[never]⟩, ⟨0, 1, 0, #[never, always, always]⟩]),
  (polyId, #[⟨0, 0, 0, #[.binder (some #[0]), .binder (some #[0])]⟩])]

/-- An environment of `cs` bound to the default role table, without the
table's support records (the records name no role). -/
def envOf (cs : List Ixon.Constant) : Except String Ixon.Env := do
  let bytes ← _root_.Ix.Kernel.Reader.defaultTableBytes
  let env : Ixon.Env := { roleBinding := some { address := Address.blake3 bytes, bytes } }
  return cs.foldl (fun env c => env.storeConst (Address.blake3 (Ixon.ser c)) c) env

/-- A witness's IO with every record of `env`, without binder data. -/
def bufferOf (env : Ixon.Env) : Aiur.IOBuffer :=
  _root_.IxVM.ClaimHarness.addEntries env (fun _ => true) (_root_.IxVM.ClaimHarness.seedBinding env default)

private def ensure (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def units : IO Unit := do
  let env ← IO.ofExcept (envOf (expected.map (·.1)))
  let io := bufferOf env
  let (io', stats) ← IO.ofExcept (annotate io env)
  IO.println s!"[ixvm-pw-hints] {stats.render}"
  ensure (stats.fallbacks == 0) "the kernel's pass failed at a binder"
  ensure (stats.extraVariants == 1) s!"expected one variant beyond 0, got {stats.extraVariants}"
  let table ← IO.ofExcept (tableOf io')
  for (c, blocks) in expected do
    let a := Address.blake3 (Ixon.ser c)
    for b in blocks do
      let got := table[(a, b.ekind, b.eidx, b.variant)]?
      ensure (got == some b.nodes)
        s!"{a} ({b.ekind}, {b.eidx}) variant {b.variant}: {repr got}, expected {repr b.nodes}"
  ensure (table.size == (expected.map (·.2.size)).sum) s!"{table.size} blocks, expected more or fewer"
  -- the encoding round-trips
  for (_, blocks) in expected do
    let back := match decode (encode blocks) with
      | .ok bs => bs == blocks
      | .error _ => false
    ensure back "the stream encoding does not round-trip"
  -- the host-side check: complete, and the kernel's
  let rep ← IO.ofExcept (check io' env)
  IO.println s!"[ixvm-pw-hints] check: {rep.render}"
  for s in rep.samples do IO.println s!"  {s}"
  ensure rep.ok "the annotated witness fails the check"
  ensure (rep.compared ≥ 10 && rep.unaligned == 1) s!"unexpected comparison counts: {rep.render}"
  -- tampering: a wrong datum is a mismatch, a missing block a missing key
  let k ← IO.ofExcept (KernelEnv.ofView (View.ofBuffer io env))
  let (tables, _) := annotateKernel k
  let polyAddr := Address.blake3 (Ixon.ser polyId)
  let twoAddr := Address.blake3 (Ixon.ser twoSorts)
  let wrong := tables.map fun (a, bs) =>
    if a == polyAddr then (a, bs.map fun b => { b with nodes := b.nodes.set! 0 never }) else (a, bs)
  let rep ← IO.ofExcept (check (seed io wrong).1 env)
  ensure (rep.mismatches ≥ 1 && rep.missing == 0) s!"a wrong datum was not caught: {rep.render}"
  let dropped := tables.map fun (a, bs) =>
    if a == twoAddr then (a, bs.filter (·.variant == 0)) else (a, bs)
  let rep ← IO.ofExcept (check (seed io dropped).1 env)
  ensure (rep.missing ≥ 1) s!"a missing block was not caught: {rep.render}"
  -- a witness without data is caught, and `withHints` leaves one with data alone
  let rep ← IO.ofExcept (check io env)
  ensure (rep.missing ≥ 1) "a witness without binder data passed the check"
  ensure (hasHints io' && !hasHints io) "hasHints"

def run : IO UInt32 := do
  try
    units
    IO.println "[ixvm-pw-hints] passed"
    return 0
  catch e =>
    IO.eprintln s!"[ixvm-pw-hints] FAILED: {e}"
    return 1

/-! ## Through the circuit

`ixvm-pw-circuit` runs a check claim of `def idPoly.{u} : (α : Sort u) → α → α
:= fun α a => a` through the program with its honest data (accepted), with a
wrong datum at the type's outer binder and at the value's inner binder (each
rejected where the circuit validates it), and with the value's block dropped
(a host error naming the missing key). It runs once the program reads the
binder data (its source names `ixvm.pw`); before that it reports a skip. -/

def idPolyType : Ixon.Expr := all (.sort 0) arrowEntry
def idPolyValue : Ixon.Expr := lam (.sort 0) (lam (.var 0) (.var 0))

def idPoly : Ixon.Constant where
  info := .defn { kind := .defn, safety := .safe, lvls := 1, typ := idPolyType, value := idPolyValue }
  sharing := #[]
  refs := #[]
  univs := #[.var 0]

/-- Every record's blocks, from a witness's channel-8 streams. -/
def blocksOf (io : Aiur.IOBuffer) : Except String (Array (Address × Array Block)) := do
  let mut out := #[]
  for ((ch, key), info) in io.map do
    unless ch.n == channel && key.size == 32 do continue
    let a : Address := ⟨⟨key.map (·.val.toUInt8)⟩⟩
    out := out.push (a, ← decode ((io.data.getD ch #[]).extract info.idx (info.idx + info.len)))
  return out

/-- `c` with the blocks of the record at `a` changed by `f`. -/
def tamper (c : Tests.Ix.IxVM.Case) (a : Address) (f : Array Block → Array Block) :
    Except String Tests.Ix.IxVM.Case := do
  let io := c.witness.inputIOBuffer
  let tables := (← blocksOf io).map fun (b, bs) => if b == a then (b, f bs) else (b, bs)
  let io := (seed (stripHints io) tables).1
  return { c with witness := { c.witness with inputIOBuffer := io } }

/-- `nodes` with the node at `i` replaced, in the block `(ekind, eidx)`. -/
def setNodeAt (ekind eidx i : Nat) (n : Node) (bs : Array Block) : Array Block :=
  bs.map fun b => if b.ekind == ekind && b.eidx == eidx then { b with nodes := b.nodes.set! i n } else b

def circuitCases : Except String (Array Tests.Ix.IxVM.Builder) := do
  let ctx ← _root_.Ix.ClaimContext.ofDefaultTable
  let addr := Address.blake3 (Ixon.ser idPoly)
  let env := ({} : Ixon.Env).storeConst addr idPoly
  let env := { env with anonHints := env.anonHints.insert addr (.regular 0) }
  let honest ← Tests.Ix.IxVM.Case.ofClaim "pw: idPoly with the kernel's data" env (.check ctx addr none)
  let wrongType ← tamper honest addr (setNodeAt 0 0 0 never)
  let wrongValue ← tamper honest addr (setNodeAt 0 1 1 always)
  let dropped ← tamper honest addr (·.filter fun b => !(b.ekind == 0 && b.eidx == 1))
  return #[
    fun _ => pure honest,
    fun _ => pure { wrongType with label := "pw: idPoly, type's outer binder never", accept := false },
    fun _ => pure { wrongValue with label := "pw: idPoly, value's inner binder always zero", accept := false },
    fun _ => pure { dropped with label := "pw: idPoly, the value's data missing", accept := false,
                                 rejectsWith := some "missing hint data: ixvm.pw at record" }]

def circuit : IO UInt32 := do
  let sources ← Tests.Ix.IxVM.programSources
  unless sources.any (fun (_, text) => (text.splitOn "\"ixvm.pw\"").length > 1) do
    IO.println "[ixvm-pw-circuit] skipped: the program does not read the binder data yet"
    return 0
  Tests.Ix.IxVM.runCases "ixvm-pw-circuit" (← IO.ofExcept circuitCases)

/-! ## Diagnosis

`ixvm-pw-diag` (manual) builds one check claim of the test binary's
environment as the pins build it (`IX_PW_NAME`, default `Nat.add_comm`) and
prints, with names: the records the kernel does not install and why (counted by
reason), the records with binders whose datum the kernel's pass could not
compute, and why the kernel's pass refuses roots. -/

private def histogram (xs : Array String) : Array (String × Nat) :=
  let m : Std.HashMap String Nat := xs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) {}
  m.toArray.qsort (fun a b => a.2 > b.2)

def diag (env : Lean.Environment) : IO UInt32 := do
  let name := (← IO.getEnv "IX_PW_NAME").getD "Nat.add_comm"
  -- `@idPoly`: the hand-made record of `ixvm-pw-circuit` over the default
  -- table's support records alone, as the hand-made suites build their claims
  let (ixon, w) ← if name == "@idPoly" then do
      let addr := Address.blake3 (Ixon.ser idPoly)
      let e := ({} : Ixon.Env).storeConst addr idPoly
      let e := { e with anonHints := e.anonHints.insert addr (.regular 0) }
      let ctx ← IO.ofExcept _root_.Ix.ClaimContext.ofDefaultTable
      let w ← IO.ofExcept (_root_.IxVM.ClaimHarness.buildClaimWitness e (.check ctx addr none))
      pure (← IO.ofExcept (_root_.IxVM.ClaimHarness.withDefaultRoleBinding e), w)
    else do
      let leanName := name.toName
      let ixon ← _root_.IxVM.ClaimHarness.loadIxonEnv leanName env
      let addr ← _root_.IxVM.ClaimHarness.lookupAddr ixon leanName
      let ctx ← IO.ofExcept (_root_.Ix.ClaimContext.ofEnv ixon true)
      pure (ixon, ← IO.ofExcept (_root_.IxVM.ClaimHarness.buildClaimWitness ixon (.check ctx addr none)))
  let io := stripHints w.inputIOBuffer
  let mut names : Std.HashMap Address String := {}
  for (n, named) in ixon.named do
    names := names.insert named.addr (toString n)
    if let some c := ixon.getConst? named.addr then
      let block := match c.info with
        | .iPrj p => some p.block | .cPrj p => some p.block
        | .rPrj p => some p.block | .dPrj p => some p.block
        | _ => none
      if let some b := block then
        unless names.contains b do names := names.insert b s!"block of {n}"
  let nameOf (a : Address) : String := (names[a]?).getD (toString a)
  let v := View.ofBuffer io ixon
  let k ← IO.ofExcept (KernelEnv.ofView v)
  IO.println s!"[ixvm-pw-diag] {name}: {v.records.size} records, {k.owners.size} owners, \
    {k.installed} declarations installed, {k.failures.size} records refused"
  let cut (s : String) : String := String.ofList (s.toList.take 140)
  for (why, n) in histogram (k.failures.map (cut ·.2)) do
    IO.println s!"  refused {n}: {why}"
  for (a, why) in k.failures.extract 0 40 do
    IO.println s!"  refused {nameOf a}: {cut why}"
  -- the keys the reasons name, by their address prefix
  let hexes := names.toArray.map fun (a, n) => (toString a, n)
  let nameKeys (reasons : Array String) : IO Unit := do
    let mut tokens : Std.HashSet String := {}
    for (why, _) in (histogram reasons).extract 0 15 do
      for part in (why.splitOn "#").drop 1 do
        tokens := tokens.insert (String.ofList (part.toList.take 12))
    for t in tokens do
      let hits := (hexes.filter fun (h, _) => h.startsWith t).map (·.2)
      IO.println s!"  #{t} = {hits.toList.take 3}"
  nameKeys (k.failures.map (cut ·.2))
  let core := Ix.Kernel.Cached.coreKnotI .verified k.fe Ix.Kernel.checkFuel
  let mut rootErrors : Array String := #[]
  let mut fallbackRecords : Array (String × Nat) := #[]
  let mut inheritedRecords : Array (String × Nat) := #[]
  for a in k.owners do
    let some c := k.setup.store[a]? | continue
    let (_, fb, inh) := annotateRecord k core a c
    if fb > 0 then fallbackRecords := fallbackRecords.push (nameOf a, fb)
    if inh > 0 then inheritedRecords := inheritedRecords.push (nameOf a, inh)
    let n := memberCount c
    let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) := fun i =>
      if i < n then some (k.setup.cx.memberKey (.member a i)) else none
    let mr := Ix.Kernel.Reader.MemberReader.mk' k.setup.cx c id self
    for e in roots c do
      match mr.read e with
      | .error _ => rootErrors := rootErrors.push "reader"
      | .ok raw =>
        match (core.annotate 0 raw).run {} with
        | .ok _ => pure ()
        | .error err =>
          rootErrors := rootErrors.push (cut (Benchmarks.Kernel.CheckIxeStep.checkOutcome err).2)
  IO.println s!"[ixvm-pw-diag] records with fallbacks: {fallbackRecords.size}"
  for (n, fb) in (fallbackRecords.qsort (fun a b => a.2 > b.2)).extract 0 40 do
    IO.println s!"  fallbacks {fb}: {n}"
  IO.println s!"[ixvm-pw-diag] records with data from their declared types: {inheritedRecords.size}"
  for (n, k) in inheritedRecords.extract 0 20 do
    IO.println s!"  inherited {k}: {n}"
  IO.println s!"[ixvm-pw-diag] roots the kernel's pass refuses: {rootErrors.size}"
  for (why, n) in (histogram rootErrors).extract 0 30 do
    IO.println s!"  root {n}: {why}"
  nameKeys rootErrors
  return 0

/-! ## The corpus measurement -/

private def rssKb : IO Nat := Benchmarks.Kernel.CheckIxeStep.statusKb "VmHWM:"

/-- Annotate `io` and report the time, the counts and the peak memory so far. -/
def measure (label : String) (env : Ixon.Env) (io : Aiur.IOBuffer) : IO Stats := do
  let t0 ← IO.monoMsNow
  let (_, stats) ← IO.ofExcept (annotate io env)
  let ms := (← IO.monoMsNow) - t0
  IO.println s!"PWCORPUS {label}: ms={ms} {stats.render} hwm_kb={← rssKb}"
  return stats

def corpus : IO UInt32 := do
  let some ixe ← IO.getEnv "IX_PW_IXE" | do IO.eprintln "IX_PW_IXE is not set"; return 1
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
  let env ← IO.ofExcept (_root_.IxVM.ClaimHarness.withDefaultRoleBinding env)
  IO.println s!"PWCORPUS loaded {ixe}: {env.consts.size} records, hwm_kb={← rssKb}"
  match ← IO.getEnv "IX_PW_IXES" with
  | some ixes =>
    let shards ← match ← _root_.Ix.Shard.loadEnvAndShards ixes ixe with
      | .ok (_, shards) => pure shards
      | .error e => throw (IO.userError e)
    let mut total : Stats := {}
    let t0 ← IO.monoMsNow
    for (blocks, k) in shards.zipIdx do
      let owned := _root_.Ix.Shard.ownedConstsForBlocks env blocks
      let (_, closure, _) ← IO.ofExcept (_root_.IxVM.ClaimHarness.shardCheckEnvClaim env owned true)
      let io := _root_.IxVM.ClaimHarness.addEntries env closure.contains
        (_root_.IxVM.ClaimHarness.seedBinding env default)
      total := total.add (← measure s!"shard {k} ({owned.size} owned, {closure.size} in closure)" env io)
    IO.println s!"PWCORPUS shards total: ms={(← IO.monoMsNow) - t0} {total.render} hwm_kb={← rssKb}"
  | none => pure ()
  if (← IO.getEnv "IX_PW_WHOLE") != some "0" then
    let _ ← measure "whole environment" env (bufferOf env)
  return 0

end Tests.Ix.IxVM.PwHints

namespace Tests.Ix.IxVM.PwHints

open _root_.IxVM.PwHints

/-- `ixvm-pw-fixture` (manual): the dev fixture (`IX_PW_FIXTURE`, default
`IxVM/IxVM/fixtures/nat-add-comm.ixf`) rewritten at version 2 with the binder
data of its records (`IX_PW_FIXTURE_OUT`, default in place): the witness its
constants (the invalid proof included), tags, blobs and role table make, as
`IxVM.Cli.fixtureHints` serves them, annotated. -/
def fixture : IO UInt32 := do
  let path := (← IO.getEnv "IX_PW_FIXTURE").getD "IxVM/IxVM/fixtures/nat-add-comm.ixf"
  let outPath := (← IO.getEnv "IX_PW_FIXTURE_OUT").getD path
  let f ← IO.ofExcept (_root_.IxVM.Fixture.decode (← IO.FS.readBinFile path))
  let key (s : _root_.IxVM.Serialized) : Array Aiur.G := s.address.map (Aiur.G.ofNat ·)
  let vals (s : _root_.IxVM.Serialized) : Array Aiur.G := s.bytes.map (Aiur.G.ofNat ·)
  let mut io : Aiur.IOBuffer := default
  for s in f.constants.push f.invalidProof do
    io := io.extend 2 (key s) (vals s)
    io := io.extend 3 (key s) #[.ofNat s.hint]
  for s in f.blobs do io := io.extend 4 (key s) (vals s)
  for s in f.roles do io := io.extend 6 (key s) (vals s)
  let (annotated, stats) ← IO.ofExcept (annotate io)
  let blocks := (← IO.ofExcept (blocksOf annotated)).qsort fun x y => x.1.cmpBytes y.1 == .lt
  let binderData := blocks.map fun (a, bs) => (a.hash.data.map (·.toNat), (encode bs).map (·.n))
  IO.FS.writeBinFile outPath (← IO.ofExcept ({ f with binderData }).encode)
  IO.println s!"[ixvm-pw-fixture] {outPath}: {stats.render}"
  return 0

end Tests.Ix.IxVM.PwHints
