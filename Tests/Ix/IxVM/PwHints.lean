import Ix.Compile.BinderData
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

`ixvm-pw-circuit` runs check claims of `def idPoly.{u} : (α : Sort u) → α → α :=
fun α a => a` through the program, the record carrying its binder-data section:
* the honest section (every binder `ifAllZero [u]`): accepted;
* a wrong datum at the type's outer binder, and at the value's inner binder:
  rejected where the circuit validates them;
* the value's block missing, the undecided sentinel at a binder, a block with a
  node left over, a share node at a binder: rejected at the conversion;
* sections that are not in canonical form (blocks out of order, a root block at
  variant 1, an empty block, an empty, unsorted or out-of-range parameter list):
  rejected when the record is read.
Each tampered record is its own record, at the address of its bytes. -/

def idPolyType : Ixon.Expr := all (.sort 0) arrowEntry
def idPolyValue : Ixon.Expr := lam (.sort 0) (lam (.var 0) (.var 0))

def idPoly : Ixon.Constant where
  info := .defn { kind := .defn, safety := .safe, lvls := 1, typ := idPolyType, value := idPolyValue }
  sharing := #[]
  refs := #[]
  univs := #[.var 0]

/-- The honest section: both roots, both binders `ifAllZero [u]`. -/
def idPolySection : Array Ixon.BinderBlock :=
  let u : Ixon.BinderNode := .ifAllZero #[0]
  #[⟨false, 0, 0, #[u, u]⟩, ⟨false, 1, 0, #[u, u]⟩]

/-- The check case of `idPoly` with `binders`. -/
def idPolyCase (ctx : _root_.Ix.ClaimContext) (label : String) (binders : Array Ixon.BinderBlock)
    (accept : Bool := false) (rejectsWith : Option String := none) : Tests.Ix.IxVM.Builder := fun _ => do
  let c := { idPoly with binders }
  let addr := Address.blake3 (Ixon.ser c)
  let env := ({} : Ixon.Env).storeConst addr c
  let env := { env with anonHints := env.anonHints.insert addr (.regular 0) }
  Tests.Ix.IxVM.Case.ofClaim s!"binder data: idPoly, {label}" env (.check ctx addr none) {} accept rejectsWith

/-- `sec` with node `i` of block `b` replaced by `n`. -/
def setNode (sec : Array Ixon.BinderBlock) (b i : Nat) (n : Ixon.BinderNode) : Array Ixon.BinderBlock :=
  sec.modify b fun blk => { blk with nodes := blk.nodes.set! i n }

def circuitCases : Except String (Array Tests.Ix.IxVM.Builder) := do
  let ctx ← _root_.Ix.ClaimContext.ofDefaultTable
  let s := idPolySection
  return #[
    idPolyCase ctx "the compiler's data" s (accept := true),
    idPolyCase ctx "type's outer binder never" (setNode s 0 0 .never),
    idPolyCase ctx "value's inner binder always zero" (setNode s 1 1 .zero),
    idPolyCase ctx "the value's block missing" (s.extract 0 1)
      (rejectsWith := some "binder data: no block for an expression with a binder"),
    idPolyCase ctx "the undecided sentinel at the type's inner binder" (setNode s 0 1 .undecided)
      (rejectsWith := some "binder data: an undecided binder"),
    idPolyCase ctx "a share node at the value's outer binder" (setNode s 1 0 (.share 0))
      (rejectsWith := some "binder data: a share node at a binder"),
    idPolyCase ctx "a node left over in the type's block"
      (s.modify 0 fun b => { b with nodes := b.nodes.push .never }),
    idPolyCase ctx "the blocks out of order" #[s[1]!, s[0]!]
      (rejectsWith := some "binder data: blocks are not strictly ascending"),
    idPolyCase ctx "a root block at variant 1" (s.modify 1 fun b => { b with variant := 1 })
      (rejectsWith := some "binder data: a root block at a variant other than 0"),
    idPolyCase ctx "an empty block" (s.push ⟨true, 0, 0, #[]⟩)
      (rejectsWith := some "binder data: an empty block"),
    idPolyCase ctx "an empty parameter list" (setNode s 0 0 (.ifAllZero #[]))
      (rejectsWith := some "binder data: an empty parameter list"),
    idPolyCase ctx "a parameter at the level count" (setNode s 0 0 (.ifAllZero #[1]))
      (rejectsWith := some "binder data: a parameter is not below the level count"),
    idPolyCase ctx "a repeated parameter" (setNode s 0 0 (.ifAllZero #[0, 0]))
      (rejectsWith := some "binder data: parameters are not strictly ascending")]

def circuit : IO UInt32 :=
  do Tests.Ix.IxVM.runCases "ixvm-pw-circuit" (← IO.ofExcept circuitCases)

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

/-- The refusals and fallbacks of one witness, with the names `env` gives (`IX_PW_SHARD`). -/
def diagnose (env : Ixon.Env) (io : Aiur.IOBuffer) : IO Unit := do
  let mut names : Std.HashMap Address String := {}
  for (n, named) in env.named do names := names.insert named.addr (toString n)
  let nameOf (a : Address) : String := (names[a]?).getD (toString a)
  let k ← IO.ofExcept (KernelEnv.ofView (View.ofBuffer io env))
  let cut (s : String) : String := String.ofList (s.toList.take 160)
  for (why, n) in (histogram (k.failures.map (cut ·.2))).extract 0 12 do
    IO.println s!"PWDIAG refused {n}: {why}"
  for (a, why) in k.failures.extract 0 25 do
    IO.println s!"PWDIAG refused {nameOf a}: {cut why}"
  let core := Ix.Kernel.Cached.coreKnotI .verified k.fe Ix.Kernel.checkFuel
  for a in k.owners do
    let some c := k.setup.store[a]? | continue
    let (_, fb, _) := annotateRecord k core a c
    if fb > 0 then IO.println s!"PWDIAG fallbacks {fb}: {nameOf a}"

private def pre (n : Nat) (s : String) : String := String.ofList (s.toList.take n)

/-- The extended diagnosis of one witness (`IX_PW_DIAG2=1`): the store's
recursor-index conflicts (records filed under one block's motive), the role
bindings of the `Bool` roles, the install order at each refusal, and IxC's own
record check (`checkLoop`, phase B included, no lenient install) over the same
records in the same order. -/
def diagnose2 (env : Ixon.Env) (io : Aiur.IOBuffer) : IO Unit := do
  let mut allNames : Std.HashMap Address (Array String) := {}
  for (n, named) in env.named do
    let cur := allNames.getD named.addr #[]
    if cur.size < 3 then allNames := allNames.insert named.addr (cur.push (toString n))
  let nameOf (a : Address) : String :=
    match allNames[a]? with
    | some ns => s!"{ns.toList}@{pre 12 (toString a)}"
    | none => pre 16 (toString a)
  let cut (s : String) : String := pre 200 s
  let v := View.ofBuffer io env
  let k ← IO.ofExcept (KernelEnv.ofView v)
  let s := k.setup
  -- the recursor index: every record a recursor analysis files under a block's motive
  let mut groups : Std.HashMap (Address × Nat) (Array Address) := {}
  for (a, c) in s.store.toArray do
    for (_, r) in Ix.Kernel.Reader.recursorMembers c do
      if let some (m, carriers, _) := Ix.Kernel.Reader.analyseRecursor s.cx.store a c r then
        if let some (Ix.Kernel.ConstRef.member b _) := carriers[0]? then
          let cur := groups.getD (b, m) #[]
          unless cur.contains a do groups := groups.insert (b, m) (cur.push a)
  let indexed (a : Address) : Bool :=
    match s.store[a]? with
    | some c => (Ix.Kernel.Reader.recursorMembers c).any fun (j, _) =>
        s.cx.index.recs.contains (.member a j)
    | none => false
  let mut conflicts := 0
  for ((b, m), rs) in groups.toList do
    if rs.size > 1 then
      conflicts := conflicts + 1
      if conflicts ≤ 20 then
        let shown := rs.toList.map fun r => s!"{nameOf r} indexed={indexed r}"
        IO.println s!"PWDIAG2 index conflict: block {nameOf b} motive {m}: {shown}"
  IO.println s!"PWDIAG2 index conflicts: {conflicts} (of {groups.size} block motives)"
  for (r, key) in s.cx.roles.names.toList do
    let ks := toString key
    if ks.startsWith "Bool" then
      let a := match r with
        | .member a _ => a
        | .ctor a _ _ => a
      IO.println s!"PWDIAG2 role {ks} -> {nameOf a} indexed={indexed a}"
  -- the install order, and the refusals in it
  let preRead ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude (md := .anon))
  let first := preRead.records.map (·.1)
  let addresses := Ixon.CheckOrder.closure s.store s.extra (first ++ k.owners)
  let pos : Std.HashMap Address Nat := addresses.zipIdx.foldl (fun m (a, i) => m.insert a i) {}
  IO.println s!"PWDIAG2 install order: {addresses.size} records"
  for (a, why) in k.failures.extract 0 30 do
    IO.println s!"PWDIAG2 refused at {(pos[a]?).getD 0}: {nameOf a}: {cut why}"
  -- IxC's own record check over the same records, in the same order
  let rows ← IO.mkRef (#[] : Array Benchmarks.Kernel.CheckIxeStep.Row)
  let out ← Benchmarks.Kernel.CheckIxeStep.checkLoop s (fun a => #[nameOf a]) addresses {}
    (fun row => if row.outcome == "accept" || row.outcome == "typed" then pure ()
      else rows.modify (·.push row)) (tier := true)
  IO.println s!"PWDIAG2 strict IxC over the same records: {out.counts.toList}"
  for (why, n) in (histogram ((← rows.get).map (cut ·.reason))).extract 0 12 do
    IO.println s!"PWDIAG2 strict reason {n}: {why}"
  for row in (← rows.get).extract 0 40 do
    IO.println s!"PWDIAG2 strict {row.outcome} at {(pos[row.address]?).getD 0}: \
      {nameOf row.address}: {cut row.reason}"

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
      let chosen := (← IO.getEnv "IX_PW_SHARD").map (·.splitOn ",")
      if let some ks := chosen then
        unless ks.contains (toString k) do continue
      let owned := _root_.Ix.Shard.ownedConstsForBlocks env blocks
      let (_, closure, _) ← IO.ofExcept (_root_.IxVM.ClaimHarness.shardCheckEnvClaim env owned true)
      let io := _root_.IxVM.ClaimHarness.addEntries env closure.contains
        (_root_.IxVM.ClaimHarness.seedBinding env default)
      total := total.add (← measure s!"shard {k} ({owned.size} owned, {closure.size} in closure)" env io)
      if chosen.isSome then
        IO.println s!"PWDIAG shard {k}"
        diagnose env io
        if (← IO.getEnv "IX_PW_DIAG2") == some "1" then diagnose2 env io
    IO.println s!"PWCORPUS shards total: ms={(← IO.monoMsNow) - t0} {total.render} hwm_kb={← rssKb}"
  | none => pure ()
  if (← IO.getEnv "IX_PW_WHOLE") != some "0" then
    let _ ← measure "whole environment" env (bufferOf env)
  return 0

end Tests.Ix.IxVM.PwHints

namespace Tests.Ix.IxVM.PwHints

open _root_.IxVM.PwHints

/-- `ixvm-fixture` (manual): the dev fixture `IxVM/IxVM/fixtures/nat-add-comm.ixf`
(version 3, Ixon v5; `IX_FIXTURE_OUT` to write elsewhere), built from the test
binary's environment: `Nat.add_comm`'s own closure (`IxVM.ClaimHarness.closureFromRoots`
from the target alone), compiled with each record's binder data, the blobs those
records name, the default role table, each definition's channel-3 tag, and an
invalid proof: `Nat.add_comm`'s record with its proof replaced by `Sort 0`,
correctly hashed, which the verifier must reject. The entries that read the
fixture (`verify_constant`, `verify_transitive`) run with the binding assumed, so
they read neither the evidence nor the bound roles outside that closure, which a
claim's witness carries (`IxVM.ClaimHarness.closureFrom`). -/
def fixture (env : Lean.Environment) : IO UInt32 := do
  let outPath := (← IO.getEnv "IX_FIXTURE_OUT").getD "IxVM/IxVM/fixtures/nat-add-comm.ixf"
  let name := ``Nat.add_comm
  let ixon ← _root_.IxVM.ClaimHarness.loadIxonEnv name env
  let target ← _root_.IxVM.ClaimHarness.lookupAddr ixon name
  let some binding := ixon.roleBinding | throw (IO.userError "the environment has no role binding")
  let closure := _root_.IxVM.ClaimHarness.closureFromRoots ixon #[target]
  let words (a : Address) : Array Nat := a.hash.data.map (·.toNat)
  -- the harness's channel-3 encoding (`Ingress::load_constant_hint`)
  let tag (a : Address) : Nat := match ixon.anonHints[a]? with
    | some .opaque => 0
    | some .abbrev => 0xFFFFFFFF
    | some (.regular n) => min (1 + n.toNat) 0xFFFFFFFE
    | none => 0
  let mut constants : Array _root_.IxVM.Serialized := #[]
  let mut named : Std.HashSet Address := {}
  for a in (closure.toArray.qsort fun x y => x.cmpBytes y == .lt) do
    let some lc := ixon.consts[a]? | continue
    constants := constants.push { address := words a, bytes := lc.rawBytes.data.map (·.toNat), hint := tag a }
    if let some c := lc.get? then
      for r in c.refs do named := named.insert r
  let blobs := (ixon.blobs.toArray.filter (named.contains ·.1)).qsort (fun x y => x.1.cmpBytes y.1 == .lt)
    |>.map fun (a, b) => ({ address := words a, bytes := b.data.map (·.toNat), hint := 0 } : _root_.IxVM.Serialized)
  -- the invalid proof: the theorem's statement with `Sort 0` as its proof
  let some c := ixon.getConst? target | throw (IO.userError s!"{name}'s record is missing")
  let .defn d := c.info | throw (IO.userError s!"{name}'s record is not a definition")
  let invalidC : Ixon.Constant := { c with
    info := .defn { d with value := .sort c.univs.size.toUInt64 }
    univs := c.univs.push .zero
    -- the proof's block goes with the proof (root 1)
    binders := c.binders.filter fun b => b.shared || b.index != 1 }
  let invalidBytes := Ixon.ser invalidC
  let invalid : _root_.IxVM.Serialized :=
    { address := words (Address.blake3 invalidBytes), bytes := invalidBytes.data.map (·.toNat), hint := 0 }
  let f : _root_.IxVM.Fixture := {
    format := Ixon.wireFormatId, name := name.toString, address := words target,
    invalidProof := invalid, constants, blobs,
    roles := #[{ address := words binding.address, bytes := binding.bytes.data.map (·.toNat), hint := 0 }] }
  IO.FS.writeBinFile outPath (← IO.ofExcept f.encode)
  IO.println s!"[ixvm-fixture] {outPath}: {constants.size} constants, {blobs.size} blobs, \
    target {target}, binding {binding.address}"
  return 0

end Tests.Ix.IxVM.PwHints

/-! ## The compiler's sections (`Ix.Compile.BinderData`)

`ixvm-binder-data` runs the compile side on the hand-made records above,
bound to the default table with its support records, all without their
sections, as the compiler emits them before it writes the sections (the
committed support records carry theirs, so they are stripped first): each
record's section is the annotator's data in the section's spelling (binder-free
share nodes and blocks dropped, "always zero" written `.zero`), canonical, with
no undecided binder; the environment is re-addressed (each record under the hash
of its new bytes, the binding rewritten), which gives back every committed
support record and the default table; a second run on the result changes
nothing (the data do not depend on addresses, and the run is deterministic); and
stripping the result gives back the environment without sections.

`binder-data-corpus` (manual) checks a compiled `.ixe` (`IX_BD_IXE`): every
record's section canonical, projections' empty, the undecided binders counted
and named, and the sections recomputed from the artifact itself equal to the
stored ones. -/

namespace Tests.Ix.IxVM.BinderData

open _root_.IxVM.PwHints
open _root_.Ix.Compile.BinderData

private def ensure (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

/-- The expected sections of the hand-made records. -/
def expectedSections : List (Ixon.Constant × Array Ixon.BinderBlock) := [
  (Tests.Ix.IxVM.PwHints.twoSorts,
    #[⟨false, 0, 0, #[.never, .never, .share 0, .never, .never, .share 1]⟩,
      ⟨true, 0, 0, #[.zero]⟩, ⟨true, 0, 1, #[.never]⟩]),
  (Tests.Ix.IxVM.PwHints.letBody,
    #[⟨false, 0, 0, #[.never]⟩, ⟨false, 1, 0, #[.never, .zero, .zero]⟩]),
  (Tests.Ix.IxVM.PwHints.polyId, #[⟨false, 0, 0, #[.ifAllZero #[0], .ifAllZero #[0]]⟩])]

/-- The serialized environment, for comparisons. -/
private def bytesOf (env : Ixon.Env) : Except String ByteArray := Ixon.serEnv env

def units : IO Unit := do
  let base := expectedSections.foldl
    (fun (env : Ixon.Env) (c, _) => env.storeConst (Address.blake3 (Ixon.ser c)) c) {}
  let supported ← IO.ofExcept (_root_.IxVM.ClaimHarness.withRoleTable base
    (← IO.ofExcept _root_.Ix.Kernel.Reader.defaultTableBytes))
  -- the compiler's environment: every record without its section (the committed
  -- support records carry theirs)
  let env ← IO.ofExcept (_root_.Ix.Compile.BinderData.strip supported)
  let (env', report) ← IO.ofExcept (_root_.Ix.Compile.BinderData.apply env)
  IO.println s!"[ixvm-binder-data] {report.summary}"
  ensure report.undecided.isEmpty "an undecided binder"
  ensure (env'.consts.size == env.consts.size) "the record count changed"
  -- every record under the hash of its bytes, its section canonical
  for (a, lc) in env'.consts do
    ensure (Address.blake3 lc.rawBytes == a) s!"{a} is not the hash of its record"
    let c ← IO.ofExcept lc.get
    ensure c.bindersCanonical s!"{a}: the section is not canonical"
  -- the hand-made records' sections, under their new addresses
  for (c, sec) in expectedSections do
    let a' := Address.blake3 (Ixon.ser { c with binders := sec })
    ensure (env'.consts.contains a') s!"no record with the expected section {repr sec}"
    ensure (!env.consts.contains a') "the record kept its old address"
  -- the binding names the new addresses
  let some b := env'.roleBinding | throw (IO.userError "the binding is gone")
  ensure (Address.blake3 b.bytes == b.address) "the binding is not under the hash of its bytes"
  let some t := _root_.Ix.Kernel.RoleTable.ofBytes b.bytes | throw (IO.userError "binding decode")
  for (_, a) in t.bound do
    ensure (env'.consts.contains a) s!"the binding names {a}, not a record"
  -- the support records come back as committed, and so does the default table
  let handMade : Std.HashSet Address := expectedSections.foldl
    (fun s (c, _) => s.insert (Address.blake3 (Ixon.ser c))) {}
  let mut missing := 0
  for (a, _) in supported.consts do
    unless handMade.contains a || env'.consts.contains a do
      missing := missing + 1
      if missing ≤ 10 then IO.eprintln s!"[ixvm-binder-data] support record {a} not given back"
  ensure (missing == 0) s!"{missing} committed support records are not given back"
  ensure (some b.address == supported.roleBinding.map (·.address))
    "the binding is not the default table"
  -- a second run changes nothing; a run is deterministic
  let (env'', _) ← IO.ofExcept (_root_.Ix.Compile.BinderData.apply env')
  ensure ((← IO.ofExcept (bytesOf env'')) == (← IO.ofExcept (bytesOf env')))
    "a second run changed the environment"
  let (again, _) ← IO.ofExcept (_root_.Ix.Compile.BinderData.apply env)
  ensure ((← IO.ofExcept (bytesOf again)) == (← IO.ofExcept (bytesOf env')))
    "two runs differ"
  -- stripping the sections gives back the compiler's environment, and an
  -- environment mixing both is annotated as one
  let stripped ← IO.ofExcept (_root_.Ix.Compile.BinderData.strip env')
  ensure ((← IO.ofExcept (bytesOf stripped)) == (← IO.ofExcept (bytesOf env)))
    "strip does not give back the compiler's environment"
  let mixed := env'.consts.fold (fun (e : Ixon.Env) a lc => { e with consts := e.consts.insert a lc }) env
  let (whole, _) ← IO.ofExcept (_root_.Ix.Compile.BinderData.withBinderData mixed)
  ensure ((← IO.ofExcept (bytesOf whole)) == (← IO.ofExcept (bytesOf env')))
    "a mixed environment is not annotated as one"

def run : IO UInt32 := do
  try
    units
    IO.println "[ixvm-binder-data] passed"
    return 0
  catch e =>
    IO.eprintln s!"[ixvm-binder-data] FAILED: {e}"
    return 1

private def rssKb : IO Nat := Benchmarks.Kernel.CheckIxeStep.statusKb "VmHWM:"

/-- `binder-data-corpus` (manual): a compiled `.ixe`'s sections (`IX_BD_IXE`). -/
def corpus : IO UInt32 := do
  let some ixe ← IO.getEnv "IX_BD_IXE" | do IO.eprintln "IX_BD_IXE is not set"; return 1
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
  IO.println s!"BDCORPUS loaded {ixe}: {env.consts.size} records, hwm_kb={← rssKb}"
  let records ← IO.ofExcept (recordsOf env)
  let mut stored : Std.HashMap Address (Array Ixon.BinderBlock) := {}
  let mut nonCanonical := 0
  let mut projections := 0
  let mut undecided := 0
  let mut nodes := 0
  for (a, c) in records do
    unless c.bindersCanonical do
      nonCanonical := nonCanonical + 1
      if nonCanonical ≤ 10 then IO.println s!"BDCORPUS not canonical: {a}"
    if (roots c).isEmpty && !c.binders.isEmpty then projections := projections + 1
    unless c.binders.isEmpty do stored := stored.insert a c.binders
    for b in c.binders do
      nodes := nodes + b.nodes.size
      undecided := undecided + (b.nodes.filter (·.isUndecided)).size
  IO.println s!"BDCORPUS stored: {stored.size} records with a section, {nodes} nodes, \
    {undecided} undecided, {nonCanonical} not canonical, {projections} projections with data"
  let t0 ← IO.monoMsNow
  let (sections, report) ← IO.ofExcept (_root_.Ix.Compile.BinderData.annotate env records)
  IO.println s!"BDCORPUS recomputed in {(← IO.monoMsNow) - t0}ms: {report.summary}, \
    hwm_kb={← rssKb}"
  let mut differ := 0
  for (a, _) in records do
    unless sections.getD a #[] == stored.getD a #[] do
      differ := differ + 1
      if differ ≤ 10 then IO.println s!"BDCORPUS differs: {a}"
  IO.println s!"BDCORPUS sections recomputed from the artifact that differ from the stored: {differ}"
  report.print env "BDCORPUS" (limit := 30)
  return (if nonCanonical == 0 && differ == 0 && projections == 0 then 0 else 1)

end Tests.Ix.IxVM.BinderData
