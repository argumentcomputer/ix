import Benchmarks.Kernel.CheckIxeStep
import Ix.RoleEvidence
import Ix.RoleBinding.Publication
import Ix.RoleBinding.Evidence
import Ix.Address.Admission
import Ix.Meta
import Ix.CanonM
import Ix.GraphM
import Ix.CondenseM
import Ix.LeanIngress
import Ix.Cert.RoleClosurePrepare
import IxC.Kernel.Verify.Rename.Basic

/-! # The default role table, its evidence and the Ixon prelude, from Ixon (untrusted)

Generates `IxC/Kernel/Ixon/RoleData.lean`: the role table of a compiled
Init (`Ix.Kernel.RoleTable`, its binding section and the section's address),
the theorem records its proof evidence names, the blobs their literals use,
and the checker's prelude records. The inputs are two compiled `.ixe` files:
the compiled Init (`.lake/envs/initstd.ixe`) and
`IxC/Kernel/PinGen/Certs.lean` compiled by the Ix compiler (`regenerate`
below gives the commands). A toolchain bump reruns this and changes nothing
in IxC: the specifications (`Role.spec`), `specVersion` and their digest stay.

1. **The bindings.** Every role's Lean name (`Role.leanName`) is looked up in
   the environment's `named` metadata (this host tool is the only place
   metadata is read), and its address resolved to a reference exactly as the
   reader resolves references. Two roles on one constant fail the run (the
   table is injective).
2. **The prelude** records are taken by their roles' addresses and read under
   the bindings; every recursor role must be the reader's own name for its
   recursor.
3. **The evidence.** The structural operations get one `defeq` entry per
   recurrence equation. For each well-founded operation, the theorems of
   `IxC/Kernel/PinGen/Certs.lean` (`Ix.RoleEvidence.certTheorems`), compiled
   by the Ix compiler and read by the same reader over the Init's records,
   are closed over the operation's dependency closure
   (`Ix.RoleEvidence.closedProofs`: every constant outside it inlined, with
   beta, `let` and projection-of-constructor reduction, to a fixpoint) and
   written as theorem records (`theoremRecord`: the theorem's statement and
   the closed proof, with a sharing table over the proof's DAG). The
   evidence names each record by its address, BLAKE3 of its bytes. The two
   compiles must agree: each operation's address in the certificates' `.ixe`
   is its address in the Init `.ixe`.
4. **Verification by the verified fold.** The evidence records are read back
   (`Reader.evidenceOf`) and must give the closed proofs; then the dependency
   closure of every bound constant is checked record by record
   (`CheckIxeStep.checkLoop`, the environment check's own step) under the
   generated table and its evidence. The run fails unless every bound
   constant's record is accepted (a basis block matches its specification up
   to `canon`, the literal support has its exact types, the structural `Nat`
   operations are certified by their recurrences and the well-founded ones by
   the evidence) and both literal capabilities hold in the final
   environment.
5. **Output.** `RoleData.lean`: the table's binding section (canonical, well
   formed, checked by decoding it back) and its address, the evidence
   records and blobs, and the prelude's records, each as canonical bytes;
   and Source mode's evidence (`Ix.RoleEvidence.bundleEvidence`, for an
   input without the certificate theorems): the theorems closed in Source
   mode over the certificate module's own environment (`sourceEvidenceOf`;
   the module's `.olean`, which `lake -d IxC build` builds), written as
   theorem records whose references are names (`nameAddress`), with the
   names, and read back. Not the `.anon` records renamed: an Ixon address
   is an alias fiber's, several Lean names, and plain Source keeps them apart.
   And quotient Source's names (`Ix.RoleEvidence.quotientEvidence`): the table's
   own evidence records, read by name, with a name for each address they cite
   (`quotientNamesOf`): a role's constant by its role, any other by a Lean name the
   compiled Init publishes there, in the Lean dependency closure of the operations
   citing it. Quotient Source collapses each alias fiber onto one representative,
   so one name per address serves it: read back, the names sent to their addresses
   give the reader's proofs (`checkQuotientBundle`).

Usage: `kernel-pin-gen <init.ixe> <certs.ixe> <RoleData.lean> [closure.jsonl]`, or
`kernel-pin-gen --quotient-names <init.ixe> <RoleData.lean>`: quotient Source's names
only, from the committed table's evidence (`quotientOnly`), every other line left as it
is. -/

namespace Benchmarks.Kernel.PinGen

open Ix.Kernel (ConstRef LevelParam Role)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-- The prelude's declarations, in upstream con-leche's prelude order (its
`pins/<toolchain>.prelude.ndjson`): each group's roles. -/
def preludeGroups : List (List Role) :=
  [[.eq, .eqRefl, .eqRec], [.nat, .natZero, .natSucc, .natRec], [.punit, .punitUnit, .punitRec],
   [.empty, .emptyRec], [.false, .falseRec],
   [.quot], [.quotMk], [.quotLift], [.quotInd], [.quotSound],
   [.and, .andIntro, .andRec], [.bool, .boolFalse, .boolTrue, .boolRec]]

/-- The commands that regenerate `RoleData.lean`, written into its header.
`--no-build`: the files import only `Init`, and `IxC/`'s lakefile does not
know `IxC/Kernel/PinGen/Certs.lean` as a target of the root's. The
generator loads that module's `.olean` for Source mode's evidence, which
`lake -d IxC build` builds. -/
def regenerate : List String :=
  ["lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --no-build --out .lake/envs/initstd.ixe",
   "lake -d IxC build IxC.Kernel.PinGen.Certs",
   s!"lake exe ix compile IxC/Kernel/PinGen/Certs.lean --no-build --out .lake/envs/certs.ixe --consts \\\n      \
    {",".intercalate (Ix.RoleEvidence.certTheorems.flatMap (·.2) |>.map toString)}",
   "lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \\\n      \
    IxC/Kernel/Ixon/RoleData.lean",
   "lake exe IxTests cert-statement   # then: RoleEvidenceChecks on the committed file"]

def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  return (out.stdout.splitOn " ").headD ""

/-- An `.ixe`'s records, decoded. -/
def loadStore (path : System.FilePath) : IO (Ixon.Env × RecordStore) := do
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  return (env, store)

/-- The content hash of the generated records and section (BLAKE3). -/
def hash (bytes : ByteArray) : Address := Address.admissionHash bytes

/-! ## Reading declarations -/

/-- Read `addresses` in order, threading the reader state as the environment check does,
and return each record's declarations, with the records that do not read. -/
def readOrdered (s : Setup) (addresses : Array Address) :
    Std.HashMap Address (Array (CDecl .anon)) × Array (Address × ReadError) := Id.run do
  let mut st : State .anon := {}
  let mut out : Std.HashMap Address (Array (CDecl .anon)) := {}
  let mut errors : Array (Address × ReadError) := #[]
  for a in addresses do
    let some c := s.store[a]? | continue
    match readRecord s.cx st a c with
    | .ok r =>
      st := st.commit r
      out := out.insert a r.decls
    | .error e => errors := errors.push (a, e)
  return (out, errors)

/-! ## Theorem records from closed proofs -/

/-! ## Source mode's evidence -/

/-- The module of the certificate theorems. -/
def certsModule : Lean.Name := `IxC.Kernel.PinGen.Certs

/-- A Lean name's bytes for its address: each component tagged and
length-delimited, so distinct names have distinct bytes. -/
def nameBytes (n : Lean.Name) : ByteArray :=
  let rec go : Lean.Name → String
    | .anonymous => ""
    | .str p s => go p ++ s!"s{s.utf8ByteSize}:{s}"
    | .num p k => go p ++ s!"n{k};"
  ("ix.source-name:" ++ go n).toUTF8

/-- **A name's address**, by which a Source evidence record references the
constant of that name (`RoleData.sourceNames` names it back). -/
def nameAddress (n : Lean.Name) : Address := hash (nameBytes n)

/-- **Source mode's closed certificate proofs**, over the Lean environment
of the certificate module (Init and `IxC/Kernel/PinGen/Certs.lean`), as the
Source ingress takes it: canonicalized (`Ix.CanonM`, on `workers` tasks) and
condensed, every declaration group lowered in the Source order behind the
prelude `pre` (a group that does not lower, a `partial` or `unsafe` one, is
left out, as the step drivers leave it), then
`Ix.LeanIngress.sourceEvidenceReport`. Also the prepared declarations. -/
def sourceEvidenceOf (pre : Prelude .source) (leanEnv : Lean.Environment) (workers : Nat) :
    (Ix.Kernel.Evidences .source × List String) × Array (CDecl .source) := Id.run do
  let consts := leanEnv.constants.toList.toArray
  let size := (consts.size + workers - 1) / max workers 1
  let tasks := (Ix.CanonM.chunks consts (max size 1)).map fun chunk =>
    Task.spawn fun _ => Ix.CanonM.canonChunk chunk
  let env : Ix.Environment :=
    { consts := tasks.foldl (init := {}) fun m t => t.get.foldl (fun m (n, c) => m.insert n c) m }
  let blocks := Ix.CondenseM.run (Ix.GraphM.envParallel env)
  let groups := Ix.LeanIngress.groupsOf env blocks
  let g := Ix.LeanIngress.graphOf blocks groups (groups.map Ix.LeanIngress.convert)
  let mut st := pre.state
  let mut lowered : Array (CDecl .source) := #[]
  for (_, c) in Ix.LeanIngress.scheduleOf g do
    match c >>= Ix.LeanIngress.lower st with
    | .ok r =>
      st := st.commit r
      lowered := lowered ++ r.decls
    | .error _ => pure ()
  let decls := Ix.Kernel.Frontend.preparePrelude pre.ix lowered
  return (Ix.LeanIngress.sourceEvidenceReport decls, decls)

/-- A Lean name as a term of the generated file, constructor by constructor
(exact for every component: numbers, and strings no identifier spells). -/
def nameTerm : Lean.Name → String
  | .anonymous => ".anonymous"
  | .str p s => s!"(.str {nameTerm p} {s.quote})"
  | .num p k => s!"(.num {nameTerm p} {k})"

/-- **The theorem of an evidence record**, read as the reader reads evidence
(`Ix.Kernel.Reader.evidenceValue?`, the same steps): its key, its statement and its proof. -/
def evidenceTheorem? (cx : Ctx .anon) (st : State .anon) (a : Address) :
    Option (CName .anon × CExpr .anon × CExpr .anon) := do
  let ref ← resolve cx.store a
  let .member owner i := ref | none
  let c ← cx.store owner
  let (d, self) ← match c.info with
    | .defn d =>
      if i == 0 then
        some (d, fun j => if j == 0 then some (cx.memberKey (.member owner 0)) else none)
      else none
    | .muts ms =>
      match ms[i]? with
      | some (.defn d) => some (d, fun j => if j < ms.size then some (cx.memberKey (.member owner j)) else none)
      | _ => none
    | _ => none
  unless d.kind == .thm do none
  match readDefinition cx st (st.heights.getD · 0) ref (List.range d.lvls.toNat)
      (.mk' cx c id self) d with
  | .ok (.thmDecl cv value, _) => some (cv.name, cv.type, value)
  | _ => none

/-- The Lean names `roots` reach in `env`: each constant's type's and value's constants,
an inductive's constructors and recursor, a constructor's inductive; transitively. -/
def leanReach (env : Lean.Environment) (roots : List Lean.Name) : Lean.NameSet := Id.run do
  let mut seen : Lean.NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let mut next := ci.getUsedConstantsAsSet.toList
      match ci with
      | .inductInfo v => next := next ++ v.ctors ++ [Lean.mkRecName n]
      | .ctorInfo v => next := next ++ [v.induct]
      | _ => pure ()
      todo := next ++ todo
  return seen

/-- **The names of quotient Source's bundle, from the role table's evidence**. The
bundle's records are the table's own evidence records (`records`, the proofs the table
binds to the well-founded operations, `t.evidence`), and quotient Source reads each
reference by the name this gives its address: a record's own address its theorem's name (`certTheorems`); a
reference the reader keys by a role (`Ctx.keyAt` in `cx`) that role's name; any other a
Lean name the compiled Init publishes at that address (`namesAt`) that the Lean
dependency closure (`leanReach` in `leanEnv`, from the operation and the blocks of the
roles its evidence check reads) of every operation citing it holds (of one citing it,
failing that), the least by spelling. A reference no record reads as a constant (a
literal's blob) gets no name. With the names, each choice among several (the address, the
name chosen, the others). -/
def quotientNamesOf (cx : Ctx .anon) (t : Ix.Kernel.RoleTable) (records : Array (Address × Ixon.Constant))
    (namesAt : Address → Array Lean.Name) (leanEnv : Lean.Environment) :
    Except String (Array (Address × Lean.Name) × Array (Address × Lean.Name × List Lean.Name)) := do
  let recordAt : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let leanOf (s : Role) : Lean.Name := Ix.RoleEvidence.toLeanName (Ix.Kernel.roleKey (md := .anon) s)
  let mut names : Std.HashMap Address Lean.Name := {}
  -- the operations citing each reference that is no role's
  let mut citers : Std.HashMap Address (Array Role) := {}
  for (r, thms) in Ix.RoleEvidence.certTheorems do
    let some (_, es) := t.evidence.toList.find? (·.1 == r) | throw s!"{repr r}: no evidence in the table"
    let addrs := es.toList.filterMap fun
      | .proof a => some a
      | .defeq => none
    unless addrs.length == thms.length do
      throw s!"{repr r}: the table has {addrs.length} proofs for {thms.length} theorems"
    for (a, thm) in addrs.zip thms do
      if names.contains a then throw s!"{thm}: its record {a} is another theorem's"
      names := names.insert a thm
      let some c := recordAt[a]? | throw s!"{thm}: the table's record {a} is not among the evidence"
      for x in c.refs do
        match cx.keyAt x with
        | .ok (.role s) => names := names.insert x (leanOf s)
        | .ok (.id _) => citers := citers.insert x (((citers.getD x #[]).push r))
        | .ok k => throw s!"{thm}: the reference {x} reads as the derived key {k}"
        | .error _ =>
          unless cx.blob x |>.isSome do throw s!"{thm}: the reference {x} is neither a constant nor a blob"
  let mut reach : Std.HashMap Role Lean.NameSet := {}
  for (r, _) in Ix.RoleEvidence.certTheorems do
    reach := reach.insert r (leanReach leanEnv (leanOf r :: (r.deps.flatMap Role.block).map leanOf))
  let mut choices := #[]
  for (x, rs) in citers.toList do
    if names.contains x then throw s!"the reference {x} is also a record or a role's"
    let all := namesAt x
    let inAll := all.filter fun n => rs.all fun r => (reach.getD r {}).contains n
    let inSome := all.filter fun n => rs.any fun r => (reach.getD r {}).contains n
    let cands := (if inAll.isEmpty then inSome else inAll).qsort fun m n => m.toString < n.toString
    let some n := cands[0]?
      | throw s!"no Lean name of {x} ({all.toList}) is in the closure of {rs.toList.map repr}"
    if let .role _ := Ix.RoleEvidence.ofLeanName n then
      throw s!"{n} names a role but sits at {x}, which the table does not bind"
    if cands.size > 1 then choices := choices.push (x, n, (cands.extract 1 cands.size).toList)
    names := names.insert x n
  let rows := names.toArray.qsort fun (a, _) (b, _) => toString a < toString b
  return (rows, choices)

/-- **Quotient Source's bundle, read back**: the table's evidence records (`records`) with
the names (`quotientNamesOf`) and the blobs, read as quotient Source reads the committed
bundle (`Bundle.ofRows`, `evidenceReport`); required to give every well-founded operation its
proofs, and each proof, its names sent to the addresses they name, to be the reader's
reading of the record (`evidenceTheorem?` in `cx` at `st`). -/
def checkQuotientBundle (cx : Ctx .anon) (st : State .anon) (t : Ix.Kernel.RoleTable)
    (records : Array (Address × Ixon.Constant)) (names : Array (Address × Lean.Name))
    (blobs : Array (Address × ByteArray)) : Except String Unit := do
  let hexRows (xs : Array (Address × ByteArray)) : Array (String × String) :=
    xs.map fun (a, b) => (toString a, hexOfBytes b)
  let bundle ← (Ix.RoleEvidence.Bundle.ofRows (hexRows (records.map fun (a, c) => (a, Ixon.serConstant c)))
    (names.map fun (a, n) => (toString a, n)) (hexRows blobs)).mapError (s!"the quotient bundle: " ++ ·)
  let (ev, why) := bundle.evidenceReport
  unless why.isEmpty do throw s!"the quotient bundle does not read: {why}"
  let addrOf : Std.HashMap Ix.Kernel.Name Address :=
    names.foldl (fun m (a, n) => m.insert (Ix.Kernel.Name.ofLeanName n) a) {}
  for (r, thms) in Ix.RoleEvidence.certTheorems do
    let some (_, es) := t.evidence.toList.find? (·.1 == r) | throw s!"{repr r}: no evidence in the table"
    let addrs := es.toList.filterMap fun
      | .proof a => some a
      | .defeq => none
    let srcs := (ev.find? (·.1 == r)).map (·.2) |>.getD []
    unless srcs.length == thms.length && addrs.length == thms.length do
      throw s!"{repr r}: {srcs.length} Source proofs, {addrs.length} records, {thms.length} theorems"
    for ((a, e), thm) in (addrs.zip srcs).zip thms do
      let .proof (_, p) := e | throw s!"{thm}: not a proof in the quotient bundle"
      let some (_, _, v) := evidenceTheorem? cx st a | throw s!"{thm}: the table's record {a} does not read"
      unless Ix.Kernel.Expr.mapKeys (fun n => addrOf.getD n default) p == v do
        throw s!"{thm}: the quotient bundle's proof, at the addresses of its names, is not the record's reading"


/-- A compiled environment's name as a Lean name. -/
def ixToLean : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToLean p) s
  | .num p k _ => .num (ixToLean p) k

/-- The Lean names a compiled environment publishes at each address. -/
def initNames (env : Ixon.Env) : Std.HashMap Address (Array Lean.Name) :=
  env.named.fold (init := {}) fun m n d => m.insert d.addr ((m.getD d.addr #[]).push (ixToLean n))

/-- The table's evidence records for the well-founded operations, in `certTheorems`
order. -/
def proofRecords (t : Ix.Kernel.RoleTable) (records : Array (Address × Ixon.Constant)) :
    Except String (Array (Address × Ixon.Constant)) := do
  let recordAt : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let mut out := #[]
  for (r, _) in Ix.RoleEvidence.certTheorems do
    let some (_, es) := t.evidence.toList.find? (·.1 == r) | throw s!"{repr r}: no evidence in the table"
    for e in es do
      if let .proof a := e then
        let some c := recordAt[a]? | throw s!"{repr r}: the record {a} is not among the evidence"
        out := out.push (a, c)
  return out

/-- The generated file's account of quotient Source's names. -/
def quotientParagraph : String :=
  "`quotientNames`: quotient Source's evidence (`Ix.RoleEvidence.quotientEvidence`): the
table's own evidence records (`evidence`, with `blobs`), read by name. Each record is named
by its theorem, and each address the records cite as a constant by its role's name where
the table binds a role there, otherwise by a Lean name the compiled Init publishes there,
in the dependency closure of the operations citing it. Collapsed onto the fiber
representatives and sent back to their addresses, the names give the reader's proofs:
checked when this file was generated."

/-- The generated rows of a names array: (address, name term). -/
def nameRows (xs : Array (Address × Lean.Name)) : String :=
  ",\n".intercalate (xs.toList.map fun (a, n) => s!"  ({(toString a).quote},\n   {nameTerm n})")

/-- Put `block` (lines) in place of the block of `lines` that starts at the line `first`
and runs to the next blank line, or, where no line is `first`, before the line `before`
followed by a blank line. -/
def putBlock (lines : Array String) (first before : String) (block : Array String) :
    Except String (Array String) := do
  match lines.findIdx? (· == first) with
  | some i =>
    let mut j := i
    while j < lines.size && lines[j]! != "" do
      j := j + 1
    return lines.extract 0 i ++ block ++ lines.extract j lines.size
  | none =>
    let some i := lines.findIdx? (· == before) | throw s!"no line `{before}`"
    return lines.extract 0 i ++ block ++ #[""] ++ lines.extract i lines.size

/-- **Quotient Source's names only** (`--quotient-names`): over the compiled Init `input`,
under the committed table and prelude (`defaultTable`, `preludeFor`), the names of the
table's own evidence records (`quotientNamesOf`), read back (`checkQuotientBundle`) and
written into `output` (the committed `RoleData.lean`) as its `quotientNames` section and
paragraph, in place or before the closure's; every other line is left as it is. -/
def quotientOnly (input output : String) : IO UInt32 := do
  let started ← IO.monoMsNow
  let (env, store) ← loadStore input
  let t ← IO.ofExcept defaultTable
  let pre : Prelude .anon ← IO.ofExcept (preludeFor t)
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) t pre hints.lookup
  let leanEnv ← getCompileEnv #[certsModule]
  let records ← IO.ofExcept ((proofRecords t pre.evidence).mapError (s!"pin-gen: " ++ ·))
  let (names, choices) ← IO.ofExcept ((quotientNamesOf s.cx t records ((initNames env).getD · #[])
    leanEnv).mapError (s!"pin-gen: quotient names: " ++ ·))
  for (x, n, others) in choices do
    IO.eprintln s!"pin-gen: {x} named {n}, not {others}"
  IO.ofExcept ((checkQuotientBundle s.cx pre.state t pre.evidence names pre.blobs.toArray).mapError
    (s!"pin-gen: " ++ ·))
  let lines := ((← IO.FS.readFile output).splitOn "\n").toArray
  let lines ← IO.ofExcept (putBlock lines (quotientParagraph.splitOn "\n").head!
    "`closure`: the well-founded `Nat` operations' dependency closure in the"
    (quotientParagraph.splitOn "\n").toArray)
  let header := "def quotientNames : Array (String × Lean.Name) := #["
  let lines ← IO.ofExcept (putBlock lines header "def closure : Array (String × String) := #["
    (#[header] ++ ((nameRows names ++ "]").splitOn "\n").toArray))
  IO.FS.writeFile output ("\n".intercalate lines.toList)
  IO.eprintln s!"pin-gen: quotient names: {names.size} names of {records.size} records' addresses; \
    reads back as the reader's proofs; written to {output} in {(← IO.monoMsNow) - started} ms"
  return 0

/-! ## The run -/

def run (args : List String) : IO UInt32 := do
  if let ["--quotient-names", i, o] := args then return ← quotientOnly i o
  let parsed : Option (String × String × String × Option String) := match args with
    | [i, c, o] => some (i, c, o, none)
    | [i, c, o, r] => some (i, c, o, some r)
    | _ => none
  let some (input, certInput, output, rowsOut) := parsed
    | IO.eprintln "usage: kernel-pin-gen <init.ixe> <certs.ixe> <RoleData.lean> [closure.jsonl] | \
        --quotient-names <init.ixe> <RoleData.lean>"
      return 2
  let fail {α : Type} (msg : String) : IO α := throw (IO.userError s!"pin-gen: {msg}")
  let started ← IO.monoMsNow
  let (env, store) ← loadStore input
  IO.eprintln s!"pin-gen: {store.size} records loaded in {(← IO.monoMsNow) - started} ms"
  let lookup : Store := (store[·]?)
  -- 1: the bindings
  let publication ← IO.ofExcept (Ix.RoleBinding.publication env lookup Role.all)
  let bound := publication.bound
  let refOfRole := publication.refs
  let boundOnly := Ix.Kernel.RoleTable.ofEntries Ix.Kernel.specVersion bound.toList []
  IO.eprintln s!"pin-gen: {bound.size} roles bound"
  -- 2: the prelude records, in prelude order
  let preRecords ← IO.ofExcept (Ix.RoleBinding.preludeRecords boundOnly lookup preludeGroups)
  for (a, c) in preRecords do
    let bytes := Ixon.serConstant c
    match Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
    | .ok c' => unless c' == c do fail s!"prelude record {a} does not round-trip"
    | .error e => fail s!"prelude record {a}: {e}"
  let pre0 ← IO.ofExcept (readPrelude boundOnly preRecords)
  IO.eprintln s!"pin-gen: prelude: {preRecords.size} records, {pre0.ix.decls.size} declarations"
  let hints := Hints.ofStore store env.anonHints
  let s0 := setup store (env.blobs[·]?) boundOnly pre0 hints.lookup
  for r in Role.all do
    let some ref := refOfRole[r]? | continue
    unless (s0.cx.memberKey ref).toOption == some (Ix.Kernel.roleKey r) do
      fail s!"{repr r} is not read as its role"
  -- 3: the evidence
  let (certEnv, certRecords) ← loadStore certInput
  let mut certStore := s0.store
  let mut added := 0
  for (a, c) in certRecords.toList do
    unless certStore.contains a do
      certStore := certStore.insert a c
      added := added + 1
  for (r, _) in Ix.RoleEvidence.certTheorems do
    let lean := Ix.Name.fromLeanName (Ix.RoleEvidence.toLeanName (Ix.Kernel.roleKey (md := .anon) r))
    let some named := certEnv.named[lean]? | fail s!"{certInput} has no {repr r}"
    let some initNamed := env.named[lean]? | fail s!"the Init has no {repr r}"
    unless named.addr == initNamed.addr do
      fail s!"{repr r} is {named.addr} in {certInput} but {initNamed.addr} in the Init: \
        the two compiles disagree"
  let cs := setup certStore (fun a => certEnv.blobs[a]? <|> env.blobs[a]?) boundOnly pre0
    (Hints.ofStore certStore certEnv.anonHints).lookup
  -- the readings: the prelude, the operations' closures and the theorems' closures
  let mut certAt : Std.HashMap Lean.Name Address := {}
  let mut roots : Array Address := preRecords.map (·.1)
  for (r, thms) in Ix.RoleEvidence.certTheorems do
    if let some ref := refOfRole[r]? then roots := roots.push ref.block
    for t in thms do
      let some named := certEnv.named[Ix.Name.fromLeanName t]? | fail s!"{certInput} has no {t}"
      certAt := certAt.insert t named.addr
      roots := roots.push named.addr
  let order := closure cs.store cs.extra roots
  let (decls, readErrors) := readOrdered cs order
  unless readErrors.isEmpty do
    fail s!"records that do not read: {readErrors.toList.map fun (a, e) => (toString a, toString e)}"
  let allDecls : Array (CDecl .anon) := order.foldl (fun acc a => acc ++ decls.getD a #[]) #[]
  let uni : Ix.RoleEvidence.Universe .anon := allDecls.foldl Ix.RoleEvidence.Universe.add {}
  let lookMap := Ix.RoleEvidence.lookupOf allDecls
  let look : CName .anon → Option (Ix.Kernel.ConstantInfo .anon) := (lookMap[·]?)
  IO.eprintln s!"pin-gen: evidence: the certificates' compile adds {added} records; {order.size} \
    records read, {uni.values.size} values"
  -- every record's address by the reader's name for it
  let mut addrOfName : Std.HashMap (CName .anon) Address := {}
  for (a, _) in cs.store.toList do
    if let .ok n := cs.cx.keyAt a then
      unless addrOfName.contains n do addrOfName := addrOfName.insert n a
  for (r, a) in bound do addrOfName := addrOfName.insert (Ix.Kernel.roleKey r) a
  let keyOf (t : Lean.Name) : CName .anon :=
    match certAt[t]? with
    -- a name that is not a certificate theorem keys `sorryAx`, which no proof is
    | some a => (cs.cx.keyAt a).toOption.getD (Ix.Kernel.roleKey .sorryAx)
    | none => Ix.Kernel.roleKey .sorryAx
  let mut evidence : Array (Role × Array (Ix.Kernel.Evidence Address)) :=
    Ix.RoleEvidence.defeqRoles.toArray.map fun r => (r, (Ix.RoleEvidence.defeqEvidence r).toArray)
  let mut evRecords : Array (Address × Ixon.Constant) := #[]
  let mut evBlobs : Array (Address × ByteArray) := #[]
  let mut closed : Std.HashMap Address (CExpr .anon) := {}
  for (r, thms) in Ix.RoleEvidence.certTheorems do
    let proofs ← match Ix.RoleEvidence.closedProofs allDecls uni look keyOf r with
      | .ok ps => pure ps
      | .error e => fail s!"{repr r}: {e}"
    let mut entries : Array (Ix.Kernel.Evidence Address) := #[]
    for ((k, p), t) in proofs.zip thms do
      let some type := allDecls.findSome? (fun
          | .thmDecl cv _ => if cv.name == k then some cv.type else none
          | _ => none)
        | fail s!"{t}: no statement"
      let (c, blobs) ← match Ix.RoleBinding.Evidence.theoremRecord (addrOfName[·]?) type p with
        | .ok x => pure x
        | .error e => fail s!"{t}: {e}"
      let bytes := Ixon.serConstant c
      match Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
      | .ok c' => unless c' == c do fail s!"{t}: its record does not round-trip"
      | .error e => fail s!"{t}: its record does not decode: {e}"
      let a := hash bytes
      evRecords := evRecords.push (a, c)
      for b in blobs do
        unless evBlobs.any (·.1 == b.1) do evBlobs := evBlobs.push b
      closed := closed.insert a p
      entries := entries.push (.proof a)
    IO.eprintln s!"pin-gen: {repr r}: {entries.size} certificates closed and written"
    evidence := evidence.push (r, entries)
  let table := Ix.Kernel.RoleTable.ofEntries Ix.Kernel.specVersion bound.toList evidence.toList
  IO.ofExcept (table.check.mapError (s!"pin-gen: the table is not well formed: " ++ ·))
  let tableBytes := table.toBytes
  unless table.wireWF do fail "the table is outside the binding section's domain"
  match Ix.Kernel.RoleTable.ofBytes tableBytes with
  | some t' => unless t'.toBytes == tableBytes do fail "the section does not decode back"
  | none => fail "the section does not decode"
  let tableAddress := hash tableBytes
  IO.eprintln s!"pin-gen: table: {tableBytes.size} bytes at {tableAddress}"
  -- 4: verification: the evidence reads back, and the fold accepts every
  -- bound constant's closure under the table
  let pre ← IO.ofExcept (readPrelude table preRecords evRecords evBlobs.toList)
  let s := setup store (env.blobs[·]?) table pre hints.lookup
  for (r, es) in s.evidence do
    for e in es do
      match e with
      | .defeq => pure ()
      | .proof (k, v) =>
        let some a := (table.evidence.toList.find? (·.1 == r)).bind fun (_, xs) =>
          xs.toList.findSome? fun | .proof a => if closed[a]? == some v then some a else none
                                  | .defeq => none
          | fail s!"{repr r}: the evidence {k} does not read back as its closed proof"
        IO.eprintln s!"pin-gen: {repr r}: {k} reads back at {a}"
  let evRoles := table.evidence.toList.filter (fun (_, es) => es.any fun
    | .proof _ => true | .defeq => false)
  for (r, _) in evRoles do
    unless (s.evidence.find? (·.1 == r)).any (fun (_, es) => !es.isEmpty) do
      fail s!"{repr r}: its evidence does not resolve"
  let checkRoots := (preRecords.map (·.1)) ++ (bound.filterMap fun (r, _) =>
    (refOfRole[r]?).map (·.block))
  let ordered := closure s.store s.extra checkRoots
  IO.eprintln s!"pin-gen: checking the closure, {ordered.size} records"
  let rows ← IO.mkRef (#[] : Array Row)
  let names := reportNames env s.store
  let out ← checkLoop s (names.getD · #[]) ordered {}
    (emit := fun row => rows.modify (·.push row))
  let rows ← rows.get
  if let some path := rowsOut then
    IO.FS.writeFile path (String.intercalate "\n" (rows.toList.map (·.json.compress)) ++ "\n")
  IO.eprintln s!"pin-gen: closure checked in {(← IO.monoMsNow) - started} ms: {out.counts.toList}"
  let outcomeOf : Std.HashMap Address (String × String) :=
    rows.foldl (fun m r => m.insert r.address (r.outcome, r.reason)) {}
  let mut bad := 0
  for (r, _) in bound do
    let some ref := refOfRole[r]? | continue
    let verdict := outcomeOf[ref.block]?
    match verdict with
    | some ("accept", _) => pure ()
    | _ =>
      let (o, reason) := verdict.getD ("unchecked", "")
      IO.eprintln s!"pin-gen: bound {repr r}: {o}: {reason}"
      bad := bad + 1
  let fe := out.checker.fe
  let nat := Ix.Kernel.natLitSupportedF fe
  let str := Ix.Kernel.strLitSupportedF fe
  IO.eprintln s!"pin-gen: Nat literals {nat}, String literals {str}"
  unless bad == 0 && nat && str do return 1
  for (r, _) in Ix.RoleEvidence.certTheorems do
    let a := ((refOfRole[r]?).map (·.block)).getD default
    let micros := ((rows.find? (·.address == a)).map (·.micros)).getD 0
    IO.eprintln s!"pin-gen: {repr r}: accepted with the generated evidence, {micros} µs"
  -- 4c: the well-founded operations' dependency closure, pinned for
  -- `Ix.Cert.RoleClosure.RoleEvidenceChecks` (with the blobs its literals
  -- reference and its definitions' hints), and checked as that statement
  -- reads it: the Ixon entry's reading behind the prelude, the verified fold
  let preludeSet : Std.HashSet Address := preRecords.foldl (fun m (a, _) => m.insert a) {}
  let wfRoots : Array Address := Ix.RoleEvidence.certTheorems.toArray.filterMap fun (r, _) =>
    (refOfRole[r]?).map (·.block)
  -- the reader needs every block's projection records (the entry reconstructs
  -- none) and every inductive block's recursors (their records, closed over in
  -- turn): `closure` keeps owners only, so both are added to a fixpoint
  let mut projectionsOf : Std.HashMap Address (Array Address) := {}
  for (a, c) in s.store.toList do
    let o := owner a c
    if o != a then projectionsOf := projectionsOf.insert o ((projectionsOf.getD o #[]).push a)
  let mut closureRoots := wfRoots
  let mut closureOrder : Array Address := #[]
  repeat
    closureOrder := closure s.store s.extra closureRoots
    let have_ : Std.HashSet Address := closureOrder.foldl (fun m a => m.insert a) {}
    let mut more : Array Address := #[]
    for a in closureOrder do
      if let some shape := s.cx.index.blocks[a]? then
        for r in shape.recs do
          unless have_.contains r.block || more.contains r.block do more := more.push r.block
    if more.isEmpty then break
    closureRoots := closureRoots ++ more
  let withProjections : Array Address := closureOrder.foldl (init := #[]) fun acc a =>
    (acc.push a) ++ ((projectionsOf.getD a #[]).qsort fun x y => toString x < toString y)
  let closureRecords : Array (Address × Ixon.Constant) :=
    (withProjections.filter (!preludeSet.contains ·)).filterMap fun a => (s.store[a]?).map (a, ·)
  for (a, c) in closureRecords do
    let bytes := Ixon.serConstant c
    match Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
    | .ok c' => unless c' == c do fail s!"closure record {a} does not round-trip"
    | .error e => fail s!"closure record {a}: {e}"
  let mut closureBlobs : Array (Address × ByteArray) := #[]
  for (_, c) in closureRecords do
    for x in c.refs do
      if let some b := env.blobs[x]? then
        unless closureBlobs.any (·.1 == x) do closureBlobs := closureBlobs.push (x, b)
  let closureHints : Array (Address × Ix.Kernel.ReducibilityHint) := closureRecords.filterMap fun (a, _) =>
    (env.anonHints[a]?).map fun
      | .opaque => (a, .opaque)
      | .abbrev => (a, .abbrev)
      | .regular h => (a, .regular h.toNat)
  let prepared := Ix.Cert.RoleClosure.prepareClosure table pre closureRecords closureBlobs.toList
    closureHints
  unless Ix.Cert.RoleClosure.closureCheck prepared do
    fail s!"the well-founded operations' closure does not check: \
      {match prepared with | .ok _ => "the fold refuses it or an operation is not defined" | .error e => e}"
  IO.eprintln s!"pin-gen: closure: {closureRecords.size} records (bytes \
    {closureRecords.foldl (fun n (_, c) => n + (Ixon.serConstant c).size) 0}), {closureBlobs.size} blobs, \
    {closureHints.size} hints; it defines every well-founded operation and the verified fold accepts it"
  -- 4b: Source mode's evidence (`Ix.RoleEvidence.bundleEvidence`): the
  -- certificate theorems closed in Source mode over the certificate module's
  -- own environment, written as theorem records whose references are names
  -- (an Ixon address is an alias fiber's, several names, so the `.anon`
  -- records cannot be read by name)
  let srcStarted ← IO.monoMsNow
  let leanEnv ← getCompileEnv #[certsModule]
  let preSrc ← IO.ofExcept (readPrelude (md := .source) table preRecords evRecords evBlobs.toList)
  let ((srcEv, srcWhy), srcDecls) := sourceEvidenceOf preSrc leanEnv 16
  unless srcWhy.isEmpty do fail s!"Source evidence: {srcWhy}"
  let mut srcRecords : Array (Address × Ixon.Constant) := #[]
  let mut srcBlobs : Array (Address × ByteArray) := #[]
  let mut srcNames : Std.HashMap Address Lean.Name := {}
  for (r, es) in srcEv do
    for e in es do
      let .proof (k, p) := e | continue
      let some type := srcDecls.findSome? (fun
          | .thmDecl cv _ => if cv.name == k then some cv.type else none
          | _ => none)
        | fail s!"{k}: no statement in Source mode"
      let mut named : Std.HashMap Address Lean.Name := {}
      for n in (type.constKeys.toList ++ p.constKeys.toList) do
        let ln := Ix.RoleEvidence.toLeanName n
        unless Ix.RoleEvidence.ofLeanName ln == n do
          fail s!"{k}: the key {n} is not its name's (a generated key)"
        let a := nameAddress ln
        if let some m := named[a]? then
          unless m == ln do fail s!"{k}: {m} and {ln} have one name address"
        named := named.insert a ln
      let (c, blobs) ← match Ix.RoleBinding.Evidence.theoremRecord (fun n => some (nameAddress (Ix.RoleEvidence.toLeanName n))) type p with
        | .ok x => pure x
        | .error e => fail s!"{k}: {e}"
      let bytes := Ixon.serConstant c
      match Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
      | .ok c' => unless c' == c do fail s!"{k}: its Source record does not round-trip"
      | .error e => fail s!"{k}: its Source record does not decode: {e}"
      let a := hash bytes
      srcRecords := srcRecords.push (a, c)
      srcNames := srcNames.insert a (Ix.RoleEvidence.toLeanName k)
      for (x, n) in named.toList do
        if let some m := srcNames[x]? then
          unless m == n do fail s!"{m} and {n} have one name address"
        srcNames := srcNames.insert x n
      for b in blobs do
        unless evBlobs.any (·.1 == b.1) || srcBlobs.any (·.1 == b.1) do srcBlobs := srcBlobs.push b
    if es.any (fun | .proof _ => true | .defeq => false) then
      IO.eprintln s!"pin-gen: {repr r}: Source evidence closed and written"
  let srcNameRows : Array (Address × Lean.Name) := srcNames.toArray.qsort fun (a, n) (b, m) =>
    toString a < toString b || (toString a == toString b && n.toString < m.toString)
  let hexRows (xs : Array (Address × ByteArray)) : Array (String × String) :=
    xs.map fun (a, b) => (toString a, hexOfBytes b)
  -- the bundle reads back as the closed proofs
  let bundle ← IO.ofExcept ((Ix.RoleEvidence.Bundle.ofRows
    (hexRows (srcRecords.map fun (a, c) => (a, Ixon.serConstant c)))
    (srcNameRows.map fun (a, n) => (toString a, n)) (hexRows (evBlobs ++ srcBlobs))).mapError
      (s!"pin-gen: the Source bundle: " ++ ·))
  let (readEv, readWhy) := bundle.evidenceReport
  unless readWhy.isEmpty && readEv == srcEv do
    fail s!"the Source bundle does not read back as the closed proofs: {readWhy}"
  IO.eprintln s!"pin-gen: Source evidence: {srcRecords.size} records, {srcNames.size} names, \
    {srcBlobs.size} more blobs; reads back; {(← IO.monoMsNow) - srcStarted} ms"
  -- 4c: quotient Source's evidence (`Ix.RoleEvidence.quotientEvidence`): the table's own
  -- evidence records, with a name for each address they cite (`quotientNamesOf`), read
  -- back as the reader's proofs (`checkQuotientBundle`)
  let qStarted ← IO.monoMsNow
  let qRecords ← IO.ofExcept ((proofRecords table evRecords).mapError (s!"pin-gen: " ++ ·))
  let (qNames, choices) ← IO.ofExcept ((quotientNamesOf s.cx table qRecords ((initNames env).getD · #[])
    leanEnv).mapError (s!"pin-gen: quotient names: " ++ ·))
  for (x, n, others) in choices do
    IO.eprintln s!"pin-gen: {x} named {n}, not {others}"
  IO.ofExcept ((checkQuotientBundle s.cx pre.state table evRecords qNames evBlobs).mapError (s!"pin-gen: " ++ ·))
  IO.eprintln s!"pin-gen: quotient names: {qNames.size} names; reads back as the reader's proofs; \
    {(← IO.monoMsNow) - qStarted} ms"
  -- 5: output
  let digest ← sha256 input
  let certDigest ← sha256 certInput
  let rowsOf (xs : Array (Address × ByteArray)) : String :=
    ",\n".intercalate (xs.toList.map fun (a, b) => s!"  ({(toString a).quote},\n   {(hexOfBytes b).quote})")
  let namesOf (xs : Array (Address × Lean.Name)) : String :=
    ",\n".intercalate (xs.toList.map fun (a, n) => s!"  ({(toString a).quote},\n   {nameTerm n})")
  let recipe := "\n".intercalate (regenerate.map ("    " ++ ·))
  let text := s!"module

/-! # The default role table, its evidence, and the Ixon prelude (generated)

GENERATED by `kernel-pin-gen` (`Benchmarks/Kernel/PinGen.lean`); do not edit.
To regenerate:

{recipe}

The default table binds every role (`Ix.Kernel.Role`) to the constant of the
compiled Init (sha256 {digest}) under the role's Lean name, with the
structural `Nat` operations' `defeq` evidence and, for each well-founded one,
the theorems of `IxC/Kernel/PinGen/Certs.lean` (compiled, sha256 {certDigest})
closed over the operation's dependency closure and written as theorem
records. Every bound constant's record, the evidence and both literal
capabilities were checked by the verified fold through the Ixon reader under
this table when this file was generated. The table is untrusted: every
theorem holds for every table (`Ix.Kernel.Admission.checkBytes`), and it is
for tests and the command line only.

`table`: the binding section (`Ix.Kernel.RoleTable.toBytes`), `tableAddress`
its BLAKE3 hash. `evidence`: the evidence's theorem records (address,
canonical bytes); `blobs`: the blobs their literals reference (address,
bytes). `prelude`: (record address, canonical record bytes), in the checker's
prelude order.

`sourceEvidence`: Source mode's evidence (`Ix.RoleEvidence.bundleEvidence`,
for an input without the certificate theorems): the same theorems closed in
Source mode over the certificate module's own environment, as theorem records
(address, canonical bytes) whose references are names: `sourceNames` names
each reference's address (the generator's `nameAddress`) and each record (its theorem), and
a literal's blob is in `blobs` or `sourceBlobs`. These were read back as the
closed proofs when this file was generated.

{quotientParagraph}

`closure`: the well-founded `Nat` operations' dependency closure in the
compiled Init, less the prelude (record address, canonical record bytes), in
check order; `closureBlobs`: the blobs its literals reference; `closureHints`:
its definitions' hints (record address, `opaque`, `abbrev` or a height). Read
by the Ixon entry's reader behind the prelude, it defines every well-founded
operation and the verified fold accepts it under this table's evidence
(`Ix.Cert.RoleClosure.RoleEvidenceChecks`): checked when this file was
generated, and by `lake exe IxTests cert-statement` (`roleEvidenceCheck`) after
every regeneration. -/

@[expose] public section

namespace Ix.Kernel.Reader.RoleData

def source : String := {s!"sha256:{digest} sha256:{certDigest}".quote}

def table : String := {(hexOfBytes tableBytes).quote}

def tableAddress : String := {(toString tableAddress).quote}

def evidence : Array (String × String) := #[
{rowsOf (evRecords.map fun (a, c) => (a, Ixon.serConstant c))}]

def blobs : Array (String × String) := #[
{rowsOf evBlobs}]

def prelude : Array (String × String) := #[
{rowsOf (preRecords.map fun (a, c) => (a, Ixon.serConstant c))}]

def sourceEvidence : Array (String × String) := #[
{rowsOf (srcRecords.map fun (a, c) => (a, Ixon.serConstant c))}]

def sourceNames : Array (String × Lean.Name) := #[
{namesOf srcNameRows}]

def sourceBlobs : Array (String × String) := #[
{rowsOf srcBlobs}]

def quotientNames : Array (String × Lean.Name) := #[
{nameRows qNames}]

def closure : Array (String × String) := #[
{rowsOf (closureRecords.map fun (a, c) => (a, Ixon.serConstant c))}]

def closureBlobs : Array (String × String) := #[
{rowsOf closureBlobs}]

def closureHints : Array (String × String) := #[
{",\n".intercalate (closureHints.toList.map fun (a, h) =>
    s!"  ({(toString a).quote}, {(Ix.Cert.RoleClosure.hintString h).quote})")}]

end Ix.Kernel.Reader.RoleData
"
  IO.FS.writeFile output text
  IO.eprintln s!"pin-gen: wrote {output}: {bound.size} roles, {evRecords.size} evidence records, \
    {evBlobs.size} blobs, {preRecords.size} prelude records, {srcRecords.size} Source \
    evidence records, {srcNameRows.size} names, {closureRecords.size} closure records"
  return 0

end Benchmarks.Kernel.PinGen

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.PinGen.run args
