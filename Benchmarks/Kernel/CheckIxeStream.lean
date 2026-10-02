import Benchmarks.Kernel.CheckIxeStep

/-! # The environment check's streaming load (untrusted harness)

`kernel-check-ixe` loads an `.ixe` this way unless `--load eager` is given.
The `.ixe` is loaded metadata-light and lazily (`Ixon.deEnvAnon`: names map
to addresses, records stay windows into the file's buffer). Every record is
decoded once for its **skeleton** (`skeleton`): what the order, the record
views and the reader read of a record other than the one being read. The
setup (`CheckIxeStep.setup`) is built over the skeletons, with the literal
edges computed from stand-ins that keep each record's literal kinds
(`literalStandIn`), so the order, the recursor index and the views are those
of the eager load.

Each record's serialized bytes are copied out of the file's buffer into the
reading state (`StreamState`), the buffer is released, and the check loop
(`CheckIxeStep.checkLoopWith`) decodes a record in full only when its turn
comes and drops its bytes once it is read. What stays resident is the
skeletons, the names, hints and blobs, the bytes of the records not yet read,
and what the checker installs.

The rows are the eager load's: the same records in the same order, read by
the same reader from the same decoded records. -/

namespace Benchmarks.Kernel.CheckIxeStream

open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep

/-! ## Skeletons -/

def stubExpr : Ixon.Expr := .sort 0

def stubDefn (d : Ixon.Definition) : Ixon.Definition := { d with typ := stubExpr, value := stubExpr }

def stubInd (i : Ixon.Inductive) : Ixon.Inductive :=
  { i with typ := stubExpr, ctors := i.ctors.map fun c => { c with typ := stubExpr } }

/-- What the order, the record views and the reader read of a record other
than the one being read: its info tag and kind (`owner`, `kindOf`,
`resolveSource`), its references (`order`, `dependencies`), an inductive's
constructor count and universe count (`inductiveAt`, `buildIndex`), and
recursor records in full (`buildIndex` reads their types; an inductive block
is read with its recursor records). Expressions, sharing and universe tables
are dropped from everything else. -/
def skeleton (c : Ixon.Constant) : Ixon.Constant :=
  match c.info with
  | .defn d => { c with info := .defn (stubDefn d), sharing := #[], univs := #[] }
  | .axio a => { c with info := .axio { a with typ := stubExpr }, sharing := #[], univs := #[] }
  | .quot q => { c with info := .quot { q with typ := stubExpr }, sharing := #[], univs := #[] }
  | .muts ms =>
    if ms.any (fun | .recr _ => true | _ => false) then c
    else
      { c with
        info := .muts (ms.map fun
          | .defn d => .defn (stubDefn d)
          | .indc i => .indc (stubInd i)
          | .recr r => .recr r)
        sharing := #[], univs := #[] }
  | _ => c

/-- A stand-in that `literalKinds` reads as a record with literals of the
given kinds. -/
def literalStandIn (nat str : Bool) : Ixon.Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := stubExpr }
    sharing := (if nat then #[Ixon.Expr.nat 0] else #[]) ++ (if str then #[Ixon.Expr.str 0] else #[])
    refs := #[], univs := #[] }

/-! ## The load -/

/-- A streaming load: the environment without its records, the setup over
the skeletons, the records' lazy windows (handed to the check loop's thread
in a reference, so that the loop takes the only reference to them), and the
prelude's records that the `.ixe` does not hold (read in full from the
setup's store). -/
structure Loaded where
  env : Ixon.Env
  setup : Setup
  windows : IO.Ref (Std.HashMap Address Ixon.LazyConstant)
  preludeOnly : Std.HashSet Address

/-- Load an `.ixe` for streaming: decode every record once for its skeleton
and its literal kinds, and build the setup over the skeletons. -/
def load (bytes : ByteArray) (pins : Pins) (pre : Prelude) : IO Loaded := do
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let consts := env.consts
  let env := { env with consts := {} }
  let mut store : RecordStore := {}
  let mut lits : Array (Address × Ixon.Constant) := #[]
  for (address, lazy) in consts.toList do
    let c ← IO.ofExcept lazy.get
    let (nat, str) := literalKinds c
    if nat || str then lits := lits.push (address, literalStandIn nat str)
    store := store.insert address (skeleton c)
  let preludeOnly := pre.records.foldl (init := {}) fun (acc : Std.HashSet Address) (a, _) =>
    if store.contains a then acc else acc.insert a
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) pins pre hints.lookup (literals := some lits)
  return { env, setup := s, windows := ← IO.mkRef consts, preludeOnly }

/-! ## Reading -/

/-- The reading state of a streaming run: the reader's state, and the
serialized bytes of every record of the `.ixe` not yet read. -/
structure StreamState where
  st : State := {}
  bytes : Std.HashMap Address ByteArray := {}

/-- The initial reading state: every record's bytes, copied out of the
file's buffer. Run on the check loop's thread, after taking the windows out
of their reference: the map is then that thread's own and the only one, so
dropping a record's bytes frees them, and the buffer is freed with the
windows. -/
def StreamState.take (windows : IO.Ref (Std.HashMap Address Ixon.LazyConstant)) : IO StreamState := do
  let consts ← windows.modifyGet fun m => (m, {})
  return { bytes := consts.fold (init := {}) fun m a lazy => m.insert a lazy.rawBytes }

/-- A record read in full: decoded from its bytes, or, for a prelude record
the `.ixe` does not hold, the setup's. -/
def StreamState.read (l : Loaded) (ss : StreamState) (address : Address) : Except ReadError Read :=
  match ss.bytes[address]? with
  | some b => match Ixon.deConstantAt b 0 with
    | .ok source => readRecord l.setup.cx ss.st address source
    | .error e => .error (.malformed s!"record does not decode: {e}")
  | none =>
    if l.preludeOnly.contains address then l.setup.read ss.st address
    else .error (.malformed "record is missing or was read already")

/-- The state after a record: the reader's state learns from it, and its
bytes are dropped. -/
def StreamState.commit (ss : StreamState) (address : Address) (rd : Read) : StreamState :=
  { st := ss.st.commit rd, bytes := ss.bytes.erase address }

/-- A streaming load as a loop source. -/
def Loaded.source (l : Loaded) : LoopSource StreamState :=
  { view := l.setup.view, read := StreamState.read l,
    commit := StreamState.commit, init := StreamState.take l.windows }

end Benchmarks.Kernel.CheckIxeStream
