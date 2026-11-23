import IxCC.Recheck.Produce
import IxCC.Src.Table.Cert

/-! # `KF-4` + `SP-0`: Seed-Closure Kernel Verification & `KernelAccepted` Witness

Ports the seed-closure walk `S = {target} ∪ theorems(table)` into `CompileClaim`
verification:

1. **Seed set (`tableTheoremAddrs`)**: extracts every theorem constant named by
   `.eqn`, `.csimp`, and `.word` entries of the certificate's `TableCert`, paired
   with the claim's `target` address.
2. **Committed default role table (`tableRestrictsDefault`)**: verifies that the
   artifact's role table is an exact restriction of the committed default role
   table (`Ix.Kernel.Admission.defaultBinding` / `Ix.Kernel.Reader.defaultTable`),
   so role identities and certificate evidence cannot be spoofed per-artifact.
3. **Pure logical seed-closure check (`checkSeedClosure`)**: computes the
   dependency-ordered closure of `S` (following table `refs`, recursor records
   and their dependencies, `groundEdges`, `literalEdges`, and certificate
   `evidenceEdges`, plus reached block projections and referenced blobs) and
   submits it to the **pure logical** certified kernel entry
   `Ix.Kernel.Admission.checkBytes` (which uses the committed `preludeFor` and
   committed `defaultBinding`, with no typing tier / no `partial` or `unsafe`
   constants in the seed closure).
4. **N5 resource mode check (`checkClosureModes`)**: runs `IxCK.Resource.recordWellFormed`
   and `IxCK.Resource.allDefault` / `IxCK.Resource.check` against the logical
   environment installed for the seed closure.

All loops are total (explicit fuel or `for` over finite collections); no
`partial`, `unsafe`, `implemented_by`, or `extern` definitions appear here. -/

set_option autoImplicit false

namespace IxCC.CompileClaim

open IxCC.Src.KernelFront
open Ix.Kernel.Reader

/-- Theorem constant referenced by a `Src.Table.Entry`, if any. -/
def entryTheorem? : Src.Table.Entry → Option Src.CId
  | .eqn thm => some thm
  | .csimp _ thm => some thm
  | .word _ _ thm => some thm
  | .prim _ | .case => none

/-- The kernel addresses of all theorem constants named by a `TableCert`,
failing closed if any referenced `CId` is absent from `P`. -/
def tableTheoremAddrs (P : Src.Program) (tc : Src.Table.TableCert) :
    Except String (Array KAddr) := do
  let mut out : Array KAddr := #[]
  for (_, e) in tc.resolve do
    if let some thm := entryTheorem? e then
      let some entry := P.entry? thm
        | throw s!"KF-4: table theorem CId {thm} missing from program"
      let a := kaddr entry.addr
      if !out.contains a then
        out := out.push a
  pure out

/-- Structural equality on kernel role-table `Evidence` entries. -/
def evidenceEq : Ix.Kernel.Evidence KAddr → Ix.Kernel.Evidence KAddr → Bool
  | .defeq, .defeq => true
  | .proof a, .proof b => a == b
  | _, _ => false

/-- Check that `artTable` is an exact restriction of the committed default
`RoleTable` `defTable`: same specification version, every bound role maps to the
identical committed address, and every evidence entry matches `defTable`. -/
def tableRestrictsDefault (artTable defTable : Ix.Kernel.RoleTable) : Bool :=
  artTable.version == defTable.version &&
  artTable.bound.all (fun (r, a) => defTable.addressOf? r == some a) &&
  artTable.evidence.all (fun (r, es) =>
    match defTable.evidence.find? (·.1 == r) with
    | some (_, des) =>
      es.size == des.size &&
        (es.toList.zip des.toList).all (fun (e1, e2) => evidenceEq e1 e2)
    | none => false)

/-- Extra edges from each bound operation block to the constants cited by its
certificate proof records in `defTable.evidence`, so every proof dependency is
ordered before the operation in a partial seed closure. -/
def evidenceEdges (defTable : Ix.Kernel.RoleTable) (look : Store) :
    Std.HashMap KAddr (Array KAddr) := Id.run do
  let mut out : Std.HashMap KAddr (Array KAddr) := {}
  for (r, es) in defTable.evidence do
    let some rAddr := defTable.addressOf? r | continue
    let some rRec := look rAddr | continue
    let rBlock := Order.owner rAddr rRec
    let mut deps : Array KAddr := out.getD rBlock #[]
    for e in es do
      if let .proof pa := e then
        if let some pc := look pa then
          for ref in pc.refs do
            if !deps.contains ref then
              deps := deps.push ref
    if !deps.isEmpty then
      out := out.insert rBlock deps
  return out

/-- Map each standalone recursor record address back to its owning inductive block. -/
def buildRecOwner (store : RecordStore) (index : RecIndex) : Std.HashMap KAddr KAddr := Id.run do
  let mut m : Std.HashMap KAddr KAddr := {}
  for (b, _) in store do
    for r in Order.recursorRecords index b do
      if r != b && !m.contains r then
        m := m.insert r b
  return m

/-- Primary block owner of `a`: projection records map to their block, and
standalone recursor records map to their inductive block. -/
def primaryOwner (recOwner : Std.HashMap KAddr KAddr) (a : KAddr) (c : KConstant) : KAddr :=
  let o := Order.owner a c
  recOwner.getD o o

/-- Total fuel-bounded DFS postorder step for `seedPostorder`. -/
def seedDfsStep (store : RecordStore) (index : RecIndex)
    (recOwner : Std.HashMap KAddr KAddr) (extra : Std.HashMap KAddr (Array KAddr)) :
    Nat → Array (KAddr × Bool) → Std.HashSet KAddr → Std.HashSet KAddr → Array KAddr →
    (Bool × Std.HashSet KAddr × Std.HashSet KAddr × Array KAddr)
  | 0, stack, done, active, out => (stack.isEmpty, done, active, out)
  | fuel + 1, stack, done, active, out =>
    match stack.back? with
    | none => (true, done, active, out)
    | some (node, expanded) =>
      let stack := stack.pop
      if expanded then
        let active := active.erase node
        if done.contains node then
          seedDfsStep store index recOwner extra fuel stack done active out
        else
          seedDfsStep store index recOwner extra fuel stack (done.insert node) active (out.push node)
      else if done.contains node || active.contains node then
        seedDfsStep store index recOwner extra fuel stack done active out
      else
        let active := active.insert node
        let stack := stack.push (node, true)
        let pushDep (stk : Array (KAddr × Bool)) (ref : KAddr) : Array (KAddr × Bool) :=
          match store[ref]? with
          | some target =>
            let dep := primaryOwner recOwner ref target
            if dep == node || done.contains dep || active.contains dep then stk
            else stk.push (dep, false)
          | none => stk
        let refs := (store[node]?.map (·.refs)).getD #[]
        let stack := refs.foldl pushDep stack
        let stack := match extra[node]? with
          | some ex => ex.foldl pushDep stack
          | none => stack
        let recs := Order.recursorRecords index node
        let stack := recs.foldl (fun stk r =>
          let rRefs := (store[r]?.map (·.refs)).getD #[]
          let stk := rRefs.foldl pushDep stk
          match extra[r]? with
          | some ex => ex.foldl pushDep stk
          | none => stk) stack
        seedDfsStep store index recOwner extra fuel stack done active out

/-- Compute the dependency-ordered seed closure of `seeds` within `inputConstants`,
backed by `pre` under `defTable`. Returns `none` only if a seed is absent from
`inputConstants` or the DFS fuel bound is exhausted. -/
def seedClosureOrder (defTable : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (inputConstants : List (KAddr × KConstant)) (seeds : Array KAddr) :
    Except String (Array KAddr) := do
  let input : RecordStore := inputConstants.foldl (fun m (a, c) => m.insert a c) {}
  for s in seeds do
    unless input.contains s do
      throw s!"KF-4: seed record {s} missing from environment"
  let mut store := input
  for (a, c) in pre.records do
    unless store.contains a do
      store := store.insert a c
  let evidence : RecordStore := pre.evidence.foldl
    (fun m (a, c) => if store.contains a then m else m.insert a c) {}
  let storeRecords := store.toArray
  let look : Store := fun a => store[a]? <|> evidence[a]?
  let roles : Bindings .anon := bindingsOf look defTable
  let index := buildIndex look storeRecords
  let recOwner := buildRecOwner store index
  let extra :=
    Order.mergeEdges
      (Order.mergeEdges (Order.groundEdges roles.names) (literalEdges roles.names storeRecords))
      (evidenceEdges defTable look)
  let edgeBudget : Nat := storeRecords.foldl (fun acc (a, c) =>
    acc + c.refs.size + (extra.getD a #[]).size) 0
  let fuel : Nat := seeds.size + 4 * store.size + 2 * edgeBudget + 64
  let mut done : Std.HashSet KAddr := Std.HashSet.emptyWithCapacity store.size
  let mut active : Std.HashSet KAddr := Std.HashSet.emptyWithCapacity 64
  let mut primaryOut : Array KAddr := Array.mkEmpty store.size
  for s in seeds do
    let some source := store[s]? | throw s!"KF-4: seed record {s} missing from store"
    let root := primaryOwner recOwner s source
    if done.contains root then continue
    let (ok, done', active', out') :=
      seedDfsStep store index recOwner extra fuel #[(root, false)] done active primaryOut
    unless ok do
      throw "KF-4: seed closure DFS exceeded budget"
    done := done'
    active := active'
    primaryOut := out'
  let mut seen : Std.HashSet KAddr := {}
  let mut out : Array KAddr := #[]
  for address in primaryOut do
    if seen.contains address then continue
    seen := seen.insert address
    out := out.push address
    for r in Order.recursorRecords index address do
      unless seen.contains r || !store.contains r do
        seen := seen.insert r
        out := out.push r
  let mut projections : Array KAddr := #[]
  for (a, c) in inputConstants do
    let o := Order.owner a c
    if o != a && seen.contains o && !seen.contains a then
      projections := projections.push a
  projections := projections.qsort (fun x y => x.cmpBytes y == .lt)
  pure ((out ++ projections).filter input.contains)

/-- Filter `allBlobs` to the blobs referenced by `closureConstants` (preserving order). -/
def closureBlobsOf (allBlobs : Ix.Kernel.Ingress.Blobs)
    (closureConstants : List (KAddr × KConstant)) : Ix.Kernel.Ingress.Blobs :=
  let needed : Std.HashSet KAddr := closureConstants.foldl (fun s (_, c) =>
    c.refs.foldl (fun s' ref => s'.insert ref) s) {}
  allBlobs.filter (fun (a, _) => needed.contains a)

/-- Run the `N5` resource mode check (`IxCK.Resource.recordWellFormed` + `allDefault`
/ `IxCK.Resource.check`) on the seed closure's decoded constants against the
logical environment installed by `Ix.Kernel.Admission.checkBytes`. -/
def checkClosureModes (defTable : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (closureEnv : Ix.Kernel.Env .anon) (constants : List (KAddr × KConstant))
    (blobs : Ix.Kernel.Ingress.Blobs) : Except String Unit := do
  for (a, c) in constants do
    (IxCK.Resource.recordWellFormed a c).mapError fun e =>
      s!"KF-4 mode-check: malformed modes at {a}: {e}"
  let mut constMap : Std.HashMap KAddr KConstant :=
    constants.foldl (fun m (a, c) => m.insert a c) {}
  for (a, c) in pre.records do
    unless constMap.contains a do
      constMap := constMap.insert a c
  let mut blobMap : Std.HashMap KAddr ByteArray :=
    blobs.foldl (fun m (a, b) => m.insert a b) {}
  for (a, b) in pre.blobs do
    unless blobMap.contains a do
      blobMap := blobMap.insert a b
  let subject : IxCK.Resource.Subject := {
    table := defTable
    store := (constMap[·]?)
    blob := (blobMap[·]?)
    seeds := constants.map (·.1)
  }
  match IxCK.Resource.allDefault subject with
  | .error e => throw s!"KF-4 mode-check: malformed modes: {e}"
  | .ok true => pure ()
  | .ok false =>
    match IxCK.Resource.check {} closureEnv subject with
    | .accept _ _ => pure ()
    | .refuse at_ w => throw s!"KF-4 mode-check: {at_}: {w}"
    | .decline r => throw s!"KF-4 mode-check (declined): {r}"

/-- Witness that the seed closure `S = {target} ∪ theorems(table)` was accepted by
the **pure logical** certified kernel entry `Ix.Kernel.Admission.checkBytes`
under the committed default role table (`defaultBinding`) and committed prelude
(`preludeFor`), with `N5` resource-mode checking (`checkClosureModes`) passing on
the resulting logical environment. -/
structure ClosureAccepted (inp : Recheck.Input) (target : Ixon.Address)
    (tc : Src.Table.TableCert) (limits : Ix.Kernel.Admission.Limits) where
  defBinding : Ix.Kernel.Admission.Binding
  defTable : Ix.Kernel.RoleTable
  pre : Prelude .anon
  seeds : Array KAddr
  records : Ix.Kernel.Admission.Records
  blobs : Ix.Kernel.Ingress.Blobs
  constants : List (KAddr × KConstant)
  hints : HintTable
  env : Ix.Kernel.Env .anon
  defaultBind : Ix.Kernel.Admission.defaultBinding = .ok defBinding
  admittedDefTable : Ix.Kernel.Admission.admitBinding hash defBinding = .ok defTable
  preludeOk : preludeFor defTable = .ok pre
  tableRestricted : tableRestrictsDefault inp.kernel.acc.table defTable = true
  seedsOk : tableTheoremAddrs inp.program tc = .ok (seeds.extract 1 seeds.size)
  seedTarget : seeds[0]? = some (kaddr target)
  decoded : Ix.Kernel.Admission.decodeWithin limits records = .ok constants
  hintsEq : hints = HintTable.of inp.env.hints constants
  /-- Pure logical kernel acceptance under committed `preludeFor` + committed `defaultBinding`. -/
  accepted : Ix.Kernel.Admission.checkBytes hash defBinding limits records blobs hints.lookup = .ok env
  /-- `N5` resource-mode check over the seed closure's logical environment. -/
  modesOk : checkClosureModes defTable pre env constants blobs = .ok ()

/-- Verify the seed closure `S = {target} ∪ theorems(tc)` via the pure logical
certified kernel entry `Ix.Kernel.Admission.checkBytes` (committed `preludeFor`
+ committed `defaultBinding`) and `N5` `checkClosureModes`. -/
def checkSeedClosure (inp : Recheck.Input) (target : Ixon.Address)
    (tc : Src.Table.TableCert) (limits : Ix.Kernel.Admission.Limits := defaultLimits) :
    Except String (ClosureAccepted inp target tc limits) :=
  match hdb : Ix.Kernel.Admission.defaultBinding with
  | .error e => .error s!"KF-4: committed default binding failed: {e}"
  | .ok defBinding =>
    match hadm : Ix.Kernel.Admission.admitBinding hash defBinding with
    | .error e => .error s!"KF-4: committed default table rejected: {Ix.Kernel.Admission.Error.binding e}"
    | .ok defTable =>
      match hpre : preludeFor defTable with
      | .error e => .error s!"KF-4: committed prelude failed: {e}"
      | .ok pre =>
        if hrest : tableRestrictsDefault inp.kernel.acc.table defTable = true then
          match hthms : tableTheoremAddrs inp.program tc with
          | .error e => .error e
          | .ok thms =>
            let seeds := #[kaddr target] ++ thms
            match seedClosureOrder defTable pre inp.kernel.acc.constants seeds with
            | .error e => .error e
            | .ok order =>
              let bytesAt : Std.HashMap KAddr ByteArray :=
                inp.kernel.acc.records.foldl (fun m (a, x) => m.insert a x) {}
              let buildRecs : Except String Ix.Kernel.Admission.Records := do
                let mut acc : Array (KAddr × ByteArray) := Array.mkEmpty order.size
                for a in order do
                  let some x := bytesAt[a]?
                    | throw s!"KF-4: missing bytes for seed-closure record {a}"
                  acc := acc.push (a, x)
                pure acc.toList
              match buildRecs with
              | .error e => .error e
              | .ok records =>
                match hdec : Ix.Kernel.Admission.decodeWithin limits records with
                | .error e => .error s!"KF-4: decode failed: {Ix.Kernel.Admission.Error.ofBytes e}"
                | .ok constants =>
                  let blobs := closureBlobsOf inp.kernel.acc.blobs constants
                  let hints := HintTable.of inp.env.hints constants
                  match hchk : Ix.Kernel.Admission.checkBytes hash defBinding limits
                      records blobs hints.lookup with
                  | .error e => .error s!"KF-4: logical kernel declined seed closure: {e}"
                  | .ok env =>
                    match hmod : checkClosureModes defTable pre env constants blobs with
                    | .error e => .error e
                    | .ok () =>
                      have htarget : seeds[0]? = some (kaddr target) := by
                        show (#[kaddr target] ++ thms)[0]? = some (kaddr target)
                        rw [Array.getElem?_append_left (by simp)]
                        rfl
                      have hextract : seeds.extract 1 seeds.size = thms := by
                        show (#[kaddr target] ++ thms).extract 1 (#[kaddr target] ++ thms).size = thms
                        apply Array.ext
                        · simp
                        · intro i h1 h2
                          simp only [Array.getElem_extract]
                          rw [Array.getElem_append_right (by simp)]
                          simp
                      .ok {
                        defBinding, defTable, pre, seeds, records, blobs, constants, hints, env
                        defaultBind := hdb
                        admittedDefTable := hadm
                        preludeOk := hpre
                        tableRestricted := hrest
                        seedsOk := by rw [hextract]; exact hthms
                        seedTarget := htarget
                        decoded := hdec
                        hintsEq := rfl
                        accepted := hchk
                        modesOk := hmod
                      }
        else
          .error "KF-4: artifact role table is not a restriction of the committed default role table"

end IxCC.CompileClaim
