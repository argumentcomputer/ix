import Benchmarks.Kernel.CheckIxeStep
import Ix.RoleEvidence
import Ix.Address.Admission

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
   records and blobs, and the prelude's records, each as canonical bytes.

Usage: `kernel-pin-gen <init.ixe> <certs.ixe> <RoleData.lean> [closure.jsonl]`. -/

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
know `IxC/Kernel/PinGen/Certs.lean` as a target of the root's. -/
def regenerate : List String :=
  ["lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --no-build --out .lake/envs/initstd.ixe",
   s!"lake exe ix compile IxC/Kernel/PinGen/Certs.lean --no-build --out .lake/envs/certs.ixe --consts \\\n      \
    {",".intercalate (Ix.RoleEvidence.certTheorems.flatMap (·.2) |>.map toString)}",
   "lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \\\n      \
    IxC/Kernel/Ixon/RoleData.lean"]

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

/-- The writer's state: the record's tables and the blobs its literals need. -/
structure Egress where
  refs : Array Address := #[]
  refIdx : Std.HashMap Address Nat := {}
  univs : Array Ixon.Univ := #[]
  univIdx : Std.HashMap Ixon.Univ Nat := {}
  sharing : Array Ixon.Expr := #[]
  shareIdx : Std.HashMap (CExpr .anon) Nat := {}
  blobs : Array (Address × ByteArray) := #[]

abbrev EgressM := StateT Egress (Except String)

def refOf (a : Address) : EgressM UInt64 := do
  if let some i := (← get).refIdx[a]? then return i.toUInt64
  let i := (← get).refs.size
  modify fun s => { s with refs := s.refs.push a, refIdx := s.refIdx.insert a i }
  return i.toUInt64

def convLevel : CLevel → Ixon.Univ
  | .zero => .zero
  | .succ u => .succ (convLevel u)
  | .max u v => .max (convLevel u) (convLevel v)
  | .imax u v => .imax (convLevel u) (convLevel v)
  | .param i => .var i.toUInt64

def univOf (l : CLevel) : EgressM UInt64 := do
  let u := convLevel l
  if let some i := (← get).univIdx[u]? then return i.toUInt64
  let i := (← get).univs.size
  modify fun s => { s with univs := s.univs.push u, univIdx := s.univIdx.insert u i }
  return i.toUInt64

/-- A natural number's blob: little-endian bytes, no trailing zero (the
reader's `natural`). -/
def natBytes (n : Nat) : ByteArray := Id.run do
  let mut out : ByteArray := .empty
  let mut k := n
  while k > 0 do
    out := out.push (k % 256).toUInt8
    k := k / 256
  return out

def blobOf (bytes : ByteArray) : EgressM UInt64 := do
  let a := hash bytes
  unless (← get).blobs.any (·.1 == a) do
    modify fun s => { s with blobs := s.blobs.push (a, bytes) }
  refOf a

/-- How often each node occurs in `e`'s DAG (each parent edge counted once
per distinct parent). -/
partial def countUses (e : CExpr .anon) : StateM (Std.HashMap (CExpr .anon) Nat) Unit := do
  let seen := (← get)[e]?
  modify fun m => m.insert e (seen.getD 0 + 1)
  if seen.isSome then return
  match e with
  | .app f a => countUses f; countUses a
  | .lam t b _ | .forallE t b _ => countUses t; countUses b
  | .letE t v b _ => countUses t; countUses v; countUses b
  | .proj _ _ x => countUses x
  | .fvar _ t => countUses t
  | _ => pure ()

/-- An expression as an Ixon expression under the writer's tables: every
node used more than once (and not a leaf) becomes a sharing entry, written
after the entries it uses. `addrOf` names a constant's record. -/
partial def egress (uses : Std.HashMap (CExpr .anon) Nat) (addrOf : CName .anon → Option Address)
    (e : CExpr .anon) : EgressM Ixon.Expr := do
  let leaf := match e with
    | .bvar _ | .sort _ | .const .. | .lit _ => true
    | _ => false
  if !leaf && uses.getD e 0 > 1 then
    if let some i := (← get).shareIdx[e]? then return .share i.toUInt64
    let x ← build
    let i := (← get).sharing.size
    modify fun s => { s with sharing := s.sharing.push x, shareIdx := s.shareIdx.insert e i }
    return .share i.toUInt64
  build
where
  build : EgressM Ixon.Expr := do
    match e with
    | .bvar i => pure (.var i.toUInt64)
    | .sort u => pure (.sort (← univOf u))
    | .const n us =>
      let some a := addrOf n | throw s!"no record for constant {n}"
      pure (.ref (← refOf a) (← us.toArray.mapM univOf))
    | .app f a => pure (.app (← egress uses addrOf f) (← egress uses addrOf a))
    | .lam t b m => pure (.lam m.contract (← egress uses addrOf t) (← egress uses addrOf b))
    | .forallE t b m =>
      pure (.all m.contract m.result (← egress uses addrOf t) (← egress uses addrOf b))
    | .letE t v b l =>
      pure (.letE l.contract (← egress uses addrOf t) (← egress uses addrOf v) (← egress uses addrOf b))
    | .lit (.natVal n) => pure (.nat (← blobOf (natBytes n)))
    | .lit (.strVal s) => pure (.str (← blobOf s.toUTF8))
    | .proj s i x =>
      let some a := addrOf s | throw s!"no record for structure {s}"
      pure (.prj (← refOf a) i.toUInt64 (← egress uses addrOf x))
    | .fvar .. => throw "a free variable in a proof"

/-- **A theorem record** with statement `type` and proof `value`: level
monomorphic, safe, its constants named through `addrOf`. -/
def theoremRecord (addrOf : CName .anon → Option Address) (type value : CExpr .anon) :
    Except String (Ixon.Constant × Array (Address × ByteArray)) := do
  let uses := ((countUses type *> countUses value).run {}).2
  let ((typ, val), eg) ← (do
      let t ← egress uses addrOf type
      let v ← egress uses addrOf value
      pure (t, v) : EgressM _).run {}
  let c : Ixon.Constant :=
    { info := .defn { kind := .thm, safety := .safe, lvls := 0, typ, value := val },
      sharing := eg.sharing, refs := eg.refs, univs := eg.univs }
  pure (c, eg.blobs)

/-! ## The run -/

def run (args : List String) : IO UInt32 := do
  let parsed : Option (String × String × String × Option String) := match args with
    | [i, c, o] => some (i, c, o, none)
    | [i, c, o, r] => some (i, c, o, some r)
    | _ => none
  let some (input, certInput, output, rowsOut) := parsed
    | IO.eprintln "usage: kernel-pin-gen <init.ixe> <certs.ixe> <RoleData.lean> [closure.jsonl]"
      return 2
  let fail {α : Type} (msg : String) : IO α := throw (IO.userError s!"pin-gen: {msg}")
  let started ← IO.monoMsNow
  let (env, store) ← loadStore input
  IO.eprintln s!"pin-gen: {store.size} records loaded in {(← IO.monoMsNow) - started} ms"
  let lookup : Store := (store[·]?)
  -- 1: the bindings
  let mut bound : Array (Role × Address) := #[]
  let mut refOfRole : Std.HashMap Role (ConstRef Address) := {}
  let mut roleOfRef : Std.HashMap (ConstRef Address) Role := {}
  for r in Role.all do
    let n := Ix.RoleEvidence.toLeanName (Ix.Kernel.roleKey (md := .anon) r)
    let some named := env.named[Ix.Name.fromLeanName n]? | fail s!"no constant named {n}"
    let some c := store[named.addr]? | fail s!"{n}: no record at {named.addr}"
    let some ref := resolveSource lookup named.addr c | fail s!"{n}: {named.addr} does not resolve"
    if let some other := roleOfRef[ref]? then
      fail s!"{repr r} and {repr other} are the same constant ({named.addr})"
    roleOfRef := roleOfRef.insert ref r
    refOfRole := refOfRole.insert r ref
    bound := bound.push (r, named.addr)
  let boundOnly := Ix.Kernel.RoleTable.ofEntries Ix.Kernel.specVersion bound.toList []
  IO.eprintln s!"pin-gen: {bound.size} roles bound"
  -- 2: the prelude records, in prelude order
  let mut preludeAddrs : Array Address := #[]
  for group in preludeGroups do
    for r in group do
      let a := (boundOnly.addressOf? r).getD default
      let some c := store[a]? | fail s!"no prelude record for {repr r}"
      for x in #[owner a c, a] do
        unless preludeAddrs.contains x do preludeAddrs := preludeAddrs.push x
  let preRecords : Array (Address × Ixon.Constant) := preludeAddrs.filterMap fun a =>
    (store[a]?).map (a, ·)
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
      let (c, blobs) ← match theoremRecord (addrOfName[·]?) type p with
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
  -- 5: output
  let digest ← sha256 input
  let certDigest ← sha256 certInput
  let rowsOf (xs : Array (Address × ByteArray)) : String :=
    ",\n".intercalate (xs.toList.map fun (a, b) => s!"  ({(toString a).quote},\n   {(hexOfBytes b).quote})")
  let recipe := "\n".intercalate (regenerate.map ("    " ++ ·))
  let text := s!"/-! # The default role table, its evidence, and the Ixon prelude (generated)

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
prelude order. -/

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

end Ix.Kernel.Reader.RoleData
"
  IO.FS.writeFile output text
  IO.eprintln s!"pin-gen: wrote {output}: {bound.size} roles, {evRecords.size} evidence records, \
    {evBlobs.size} blobs, {preRecords.size} prelude records"
  return 0

end Benchmarks.Kernel.PinGen

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.PinGen.run args
