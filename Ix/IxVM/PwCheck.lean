module

public import Ix.IxVM.PwHints

public section

/-!
# Checking a witness's binder data (host side)

Two checks of the data `IxVM.PwHints.annotate` writes on a witness's
channel 8, over every record the witness carries on channel 2:

* **Coverage.** The conversion of every root of every record, as IxVM
  converts it (`IxVM/IxVM/Source/Convert.lean`, "Binder data": roots at
  variant 0, each `Share n` read at its key and its entry converted at the
  variant read, each entry's `Lam`, `All` and `Share` nodes numbered in
  pre-order), finds a value of the right kind at every key it asks for, and
  each entry conversion's block has exactly the entry's nodes. This walk is
  written from the specification, independently of the annotator's.
* **The kernel's values.** Every root is read by IxC's reader (sharing
  expanded) and annotated by the kernel's own pass (`annotate` of the cached
  core, at depth 0, over the environment the kernel installed from the
  witness), and every binder of the converted tree is compared with the
  annotated term's binder at the same position. The annotated term is the
  ζ-reduct of a `let`, so a `let`'s body is compared with it and its type and
  value are not (they have no counterpart); a binder with no counterpart is
  counted as unaligned.
-/

namespace IxVM.PwHints

/-- What the checks found. -/
structure Report where
  records : Nat := 0
  roots : Nat := 0
  /-- keys the conversion asked for (each entry conversion once) -/
  keys : Nat := 0
  missing : Nat := 0
  /-- binder occurrences compared with the kernel's, mismatches among them,
  and those with no counterpart in the kernel's term -/
  compared : Nat := 0
  mismatches : Nat := 0
  unaligned : Nat := 0
  /-- roots the kernel's pass refuses (an ill-typed record) -/
  kernelRefused : Nat := 0
  samples : Array String := #[]
  deriving Inhabited

def Report.ok (r : Report) : Bool := r.missing == 0 && r.mismatches == 0

def Report.render (r : Report) : String :=
  s!"records={r.records} roots={r.roots} keys={r.keys} missing={r.missing} \
    compared={r.compared} mismatches={r.mismatches} unaligned={r.unaligned} \
    kernel-refused={r.kernelRefused}"

def Report.add (a b : Report) : Report :=
  { records := a.records + b.records, roots := a.roots + b.roots, keys := a.keys + b.keys,
    missing := a.missing + b.missing, compared := a.compared + b.compared,
    mismatches := a.mismatches + b.mismatches, unaligned := a.unaligned + b.unaligned,
    kernelRefused := a.kernelRefused + b.kernelRefused,
    samples := (a.samples ++ b.samples).extract 0 8 }

/-- The blocks a witness carries, by `(rec, ekind, eidx, variant)`. -/
abbrev Table := Std.HashMap (Address × Nat × Nat × Nat) (Array Node)

/-- The witness's channel-8 streams, decoded. -/
def tableOf (io : Aiur.IOBuffer) : Except String Table := do
  let mut t : Table := {}
  for ((ch, key), info) in io.map do
    unless ch.n == channel do continue
    unless key.size == 32 do throw "a binder-data stream is not keyed by an address"
    let a : Address := ⟨⟨key.map (·.val.toUInt8)⟩⟩
    let vs := (io.data.getD ch #[]).extract info.idx (info.idx + info.len)
    for b in ← decode vs do
      t := t.insert (a, b.ekind, b.eidx, b.variant) b.nodes
  return t

/-- A witness's binder-data stream values, its blocks, and the blocks at a
variant beyond 0. -/
def streamCounts (io : Aiur.IOBuffer) : Nat × Nat × Nat :=
  match tableOf io with
  | .error _ => (0, 0, 0)
  | .ok t =>
    let values := io.map.fold (init := 0) fun n (ch, _) info =>
      if ch.n == channel then n + info.len else n
    (values, t.size, t.fold (init := 0) fun n (_, _, _, v) _ => if v > 0 then n + 1 else n)

/-- `io` without binder data. -/
def stripHints (io : Aiur.IOBuffer) : Aiur.IOBuffer :=
  { data := io.data.erase (.ofNat channel)
    map := io.map.filter fun (ch, _) _ => ch.n != channel }

/-- The state of one record's check. -/
structure ChState where
  report : Report := {}
  /-- entry conversions already walked, with the kernel term they were
  compared with -/
  seen : Std.HashSet (Nat × Nat × Option KExpr) := {}
  /-- entry conversions whose node count was checked -/
  counted : Std.HashSet (Nat × Nat) := {}

abbrev ChM := StateM ChState

private def note (msg : String) : ChM Unit :=
  modify fun st => { st with report := { st.report with
    samples := if st.report.samples.size < 8 then st.report.samples.push msg else st.report.samples } }

private def missingKey (msg : String) : ChM Unit := do
  modify fun st => { st with report := { st.report with missing := st.report.missing + 1 } }
  note msg

/-- The binder at `ord`: a binder datum, compared with the kernel's `kpw`
(`none`: no counterpart). -/
private def binderAt (label : String) (nodes : Array Node) (ord : Nat)
    (kpw : Option Ix.Kernel.PropWhen) : ChM Unit := do
  modify fun st => { st with report := { st.report with keys := st.report.keys + 1 } }
  match nodes[ord]? with
  | some (.binder ps) =>
    match kpw with
    | some pw =>
      let ok := Node.binder ps == Node.ofPw pw
      modify fun st => { st with report := { st.report with
        compared := st.report.compared + 1
        mismatches := st.report.mismatches + (if ok then 0 else 1) } }
      unless ok do
        note s!"{label} ordinal {ord}: datum {repr ps}, the kernel's {repr pw.toList?}"
    | none =>
      modify fun st => { st with report := { st.report with unaligned := st.report.unaligned + 1 } }
  | some (.share _) => missingKey s!"{label} ordinal {ord}: a share datum at a binder"
  | some .undecided => missingKey s!"{label} ordinal {ord}: an undecided datum"
  | none => missingKey s!"{label} ordinal {ord}: no binder datum"

/-- The check of one entry conversion: `nodes` its block, `e` its tree, `k`
the kernel's term at the same position (`none`: no counterpart). `ord` is the
next ordinal; returns the one after the tree. A `Share n` site's entry is
checked at the variant it reads, once per kernel term it is compared with. -/
def checkTree (a : Address) (sharing : Array Ixon.Expr) (table : Table) (label : String)
    (nodes : Array Node) : Nat → Ixon.Expr → Option KExpr → Nat → ChM Nat
  | 0, _, _, ord => pure ord
  | fuel + 1, e, k, ord =>
    match e with
    | .app f x => do
      let (kf, kx) := match k with
        | some (.app kf kx) => (some kf, some kx)
        | _ => (none, none)
      let ord ← checkTree a sharing table label nodes fuel f kf ord
      checkTree a sharing table label nodes fuel x kx ord
    | .prj _ _ v => do
      let kv := match k with
        | some (.proj _ _ kv) => some kv
        | _ => none
      checkTree a sharing table label nodes fuel v kv ord
    | .letE _ _ t v b => do
      let ord ← checkTree a sharing table label nodes fuel t none ord
      let ord ← checkTree a sharing table label nodes fuel v none ord
      checkTree a sharing table label nodes fuel b k ord
    | .lam t b => do
      let (kt, kb, kpw) := match k with
        | some (.lam kt kb m) => (some kt, some kb, some m.pw)
        | _ => (none, none, none)
      binderAt label nodes ord kpw
      let ord ← checkTree a sharing table label nodes fuel t kt (ord + 1)
      checkTree a sharing table label nodes fuel b kb ord
    | .all t b => do
      let (kt, kb, kpw) := match k with
        | some (.forallE kt kb m) => (some kt, some kb, some m.pw)
        | _ => (none, none, none)
      binderAt label nodes ord kpw
      let ord ← checkTree a sharing table label nodes fuel t kt (ord + 1)
      checkTree a sharing table label nodes fuel b kb ord
    | .share n => do
      modify fun st => { st with report := { st.report with keys := st.report.keys + 1 } }
      match nodes[ord]? with
      | some (.share v) =>
        let n := n.toNat
        unless (← get).seen.contains (n, v, k) do
          modify fun st => { st with seen := st.seen.insert (n, v, k) }
          let label' := s!"{a} entry (1, {n}) variant {v}"
          match sharing[n]?, table[(a, 1, n, v)]? with
          | some tree, some nodes' =>
            let used ← checkTree a sharing table label' nodes' fuel tree k 0
            unless (← get).counted.contains (n, v) do
              modify fun st => { st with counted := st.counted.insert (n, v) }
              unless used == nodes'.size do
                missingKey s!"{label'}: {nodes'.size} data for {used} numbered nodes"
          | none, _ => missingKey s!"{label'}: no such sharing entry"
          | _, none => missingKey s!"{label'}: no block"
      | some (.binder _) | some .undecided =>
        missingKey s!"{label} ordinal {ord}: a binder datum at a share site"
      | none => missingKey s!"{label} ordinal {ord}: no share datum"
      pure (ord + 1)
    | _ => pure ord

/-- Check one record: every root, at variant 0, against the kernel's
annotation of the root. -/
def checkRecord (k : KernelEnv) (core : Ix.Kernel.Cached.CoreFnsI .anon) (table : Table)
    (addr : Address) (c : Ixon.Constant) : Report := Id.run do
  let n := memberCount c
  let cx := k.setup.cx
  let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) := fun i =>
    if i < n then some (cx.memberKey (.member addr i)) else none
  let mr := Ix.Kernel.Reader.MemberReader.mk' cx c id self
  let act : ChM Unit := do
    for (e, r) in (roots c).zipIdx do
      modify fun st => { st with report := { st.report with roots := st.report.roots + 1 } }
      let kernel : Option KExpr := match mr.read e with
        | .error _ => none
        | .ok raw =>
          match (core.annotate 0 raw).run {} with
          | .ok (ann, _) => some ann
          | .error _ => none
      if kernel.isNone then
        modify fun st => { st with report := { st.report with
          kernelRefused := st.report.kernelRefused + 1 } }
      let label := s!"{addr} root {r}"
      match table[(addr, 0, r, 0)]? with
      | none => missingKey s!"{label}: no block"
      | some nodes =>
        let used ← checkTree addr c.sharing table label nodes walkFuel e kernel 0
        unless used == nodes.size do
          missingKey s!"{label}: {nodes.size} data for {used} numbered nodes"
  let ((), st) := act.run {}
  return { st.report with records := 1 }

/-- **The host-side check** of a witness's binder data: coverage of every
conversion of every record on channel 2, and every aligned binder's datum
against the kernel's annotation pass. -/
def check (io : Aiur.IOBuffer) (env : Ixon.Env := {}) : Except String Report := do
  let table ← tableOf io
  let v := View.ofBuffer io env
  if v.records.isEmpty then return {}
  -- the reference is the strict kernel: what IxC installs itself, no record put in by the
  -- annotator's lenient path (whose data are the annotator's own)
  let k ← KernelEnv.ofView v (lenient := false)
  let core := Ix.Kernel.Cached.coreKnotI .verified k.fe Ix.Kernel.checkFuel
  let mut report : Report := {}
  for a in k.owners do
    let some c := k.setup.store[a]? | continue
    report := report.add (checkRecord k core table a c)
  return report

end IxVM.PwHints

end
