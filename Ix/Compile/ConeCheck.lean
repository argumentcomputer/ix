module
public import Ix.Ixon.Authenticated
public import Ix.Ixon.CheckOrder
public import IxC.Kernel.TypeChecker

/-! # The changed-cone check

The runtime half of the changed-cone validator (`Ix.Cert.ConeValidator`): given
what to check on a compiled artifact (a `Plan`, read off the compile's changed set
by the caller), it checks it with the certified Ixon entry and IxC's inference,
and refuses the artifact on the first failure. Nothing here is trusted to be
right about what it checks: `Ix.Cert.ConeValidator.sound` proves what its success
asserts.

* `Plan.seeds`: the published addresses of every record the changed set names,
  with its cone (the direct causes, the published clique rows, the cascade) and
  the image computation-rule rows. Their compiled closure is checked by the
  certified entry, in one run (`Mode.union`) or one run per seed
  (`Mode.perSeed`).
* `Plan.missingRows`: the image computation-rule rows the plan requires and the
  artifact does not publish. Any refuses.
* `Plan.rewritten`: the records whose terms the compiler rewrote. Each is checked
  with its own compiled closure, and in the environment that installs, the terms
  of its Source declaration renamed to the artifact's addresses (supplied by the
  caller, `none` when Source does not prepare the record's closure) must infer.

A check of seeds runs over their compiled closure: what they reach over the
reference tables, a projection's block, and the edges the certified entry needs
beyond the reference tables (`Extra`: the `Nat` operations' certificate ground, the
literal edges, and an inductive block's recursor records). It runs in an order that
the check decides is one (`closureOrderCheck`): each record once, every address the
seeds reach and nothing else, with a certificate of how each is reached, and no
record before one it references. The order itself comes from the environment
check's order (`Ixon.CheckOrder.wholeEnv`) and is not trusted. -/

@[expose] public section

namespace Ix.Compile.ConeCheck

open Ix.Kernel (Env ConstRef)
open Ix.Kernel.Admission (Binding Limits Records)

/-! ## The records of an artifact

These read the artifact as the final statement reads it (`Ix.Cert.recordAt`,
`ownerOf`, `recordsOf`, `blobsOf`, `hintsOf`), and are those definitions. -/

/-- The record stored at `a`, decoded. -/
def recordAt (ixe : Ixon.Env) (a : Address) : Option Ixon.Constant :=
  (ixe.consts.get? a).bind (·.get?)

/-- The record a reference to the record `c` at `a` resolves to: a projection's
block, otherwise `a` itself. -/
def ownerOf (a : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => a

/-- The records at `order`, each with its stored bytes. -/
def recordsOf (ixe : Ixon.Env) (order : List Address) : Records :=
  order.filterMap fun a => (ixe.consts.get? a).map fun lc => (a, lc.rawBytes)

/-- The blobs the records at `order` reference. -/
def blobsOf (ixe : Ixon.Env) (order : List Address) : Ix.Kernel.Ingress.Blobs :=
  let used : Std.HashSet Address := order.foldl (init := {}) fun s a =>
    match recordAt ixe a with
    | some c => c.refs.foldl (·.insert ·) s
    | none => s
  ixe.blobs.toList.filter fun b => used.contains b.1

def hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- The projection record of each definition block member. -/
def projAtOf (ixe : Ixon.Env) : Std.HashMap (ConstRef Address) Address :=
  ixe.consts.fold (init := {}) fun m a lc =>
    match lc.get? with
    | some c =>
      match c.info with
      | .dPrj p => m.insert (.member p.block p.idx.toNat) a
      | _ => m
    | none => m

/-- The hints, read through a computed projection map. -/
def hintsWith (projAt : Std.HashMap (ConstRef Address) Address)
    (anonHints : Std.HashMap Address Lean.ReducibilityHints) (r : ConstRef Address) :
    Option Ix.Kernel.ReducibilityHint :=
  hintOf <$> anonHints.get? ((projAt.get? r).getD r.block)

/-- The hints the artifact ships, read at the address the compiler registers them
under: a definition block member's projection record, otherwise the record. A
caller computes the projection map once (`hintsWith (projAtOf ixe)`): this
definition, applied to an artifact alone, is a function of two arguments to the
compiler and would rebuild the map at every lookup. -/
def hintsOf (ixe : Ixon.Env) : ConstRef Address → Option Ix.Kernel.ReducibilityHint :=
  let projAt : Std.HashMap (ConstRef Address) Address :=
    ixe.consts.fold (init := {}) fun m a lc =>
      match lc.get? with
      | some c =>
        match c.info with
        | .dPrj p => m.insert (.member p.block p.idx.toNat) a
        | _ => m
      | none => m
  fun r => hintOf <$> ixe.anonHints.get? ((projAt.get? r).getD r.block)

/-! ## The compiled closure of seeds, and its order -/

/-- **The edges the certified entry needs beyond the reference tables**, by source
address (`extraEdges`): a `Nat` operation's certificate ground, a literal's support,
and from an inductive block to its recursor records (the reader declines a block
whose recursors are not in its input, and no reference table names them). They
are the statement's `GroundEdge` and `RecursorEdge`, the edges
`Ixon.CheckOrder` follows besides the references. -/
abbrev Extra := Std.HashMap Address (Array Address)

/-- Whether the record at `a` needs `b`: `b` is its block, if `a` is a
projection, a stored record of its reference table, or a stored target of one of
its extra edges. -/
def edge (ixe : Ixon.Env) (extra : Extra) (a b : Address) : Bool :=
  (match recordAt ixe a with
    | some c => (ownerOf a c == b && b != a) || (c.refs.contains b && ixe.consts.contains b)
    | none => false) ||
  ((extra.getD a #[]).contains b && ixe.consts.contains b)

/-- The addresses the record `c` at `a` needs over its reference table and owner. -/
def needs (ixe : Ixon.Env) (a : Address) (c : Ixon.Constant) : Array Address :=
  let refs := c.refs.filter ixe.consts.contains
  let o := ownerOf a c
  if o != a then refs.push o else refs

/-- The compiled closure of the seeds, breadth first: every address in the order
found, the position of the address it was found from (none for a seed), and its
distance from the seeds. -/
structure Reach where
  found : Array Address := #[]
  parent : Array (Option Nat) := #[]
  depth : Array Nat := #[]
  index : Std.HashMap Address Nat := {}

/-- Add `b`, found from position `p` (none for a seed) at distance `d`, unless
already found. -/
def Reach.add (r : Reach) (b : Address) (p : Option Nat) (d : Nat) : Reach :=
  if r.index.contains b then r
  else
    let ⟨found, parent, depth, index⟩ := r
    ⟨found.push b, parent.push p, depth.push d, index.insert b found.size⟩

/-- Expand positions `i`, `i+1`, … of `r` (the queue is `r.found` itself), at most
`fuel` of them. -/
def Reach.expand (ixe : Ixon.Env) (extra : Extra) : Nat → Nat → Reach → Reach
  | 0, _, r => r
  | fuel + 1, i, r =>
    match r.found[i]? with
    | none => r
    | some a =>
      let d := r.depth.getD i 0
      let r := match recordAt ixe a with
        | some c => (needs ixe a c).foldl (fun r b => r.add b (some i) (d + 1)) r
        | none => r
      let r := ((extra.getD a #[]).filter ixe.consts.contains).foldl
        (fun r b => r.add b (some i) (d + 1)) r
      Reach.expand ixe extra fuel (i + 1) r

/-- The compiled closure of the stored seeds (an unstored seed is not reached). -/
def reach (ixe : Ixon.Env) (extra : Extra) (seeds : Array Address) : Reach :=
  let r := seeds.foldl (fun r s => if ixe.consts.contains s then r.add s none 0 else r) {}
  -- every address found is a stored record or the block of one
  Reach.expand ixe extra (2 * ixe.consts.size + seeds.size + 1) 0 r

/-- An order of the reached addresses for the certified entry: the unstored ones
first (a projection's block missing from the store references nothing), then the
stored records in the environment check's order (`Ixon.CheckOrder.wholeEnv`: the
prelude's records first, dependencies before dependents over the reference
tables, the `Nat` operations' certificate ground and the literal edges). -/
def orderOf (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (pre : Ix.Kernel.Reader.Prelude .anon)
    (r : Reach) : Array Address :=
  let stored := r.found.filterMap fun a => (recordAt ixe a).map (a, ·)
  let unstored := r.found.filter fun a => !ixe.consts.contains a
  unstored ++ Ixon.CheckOrder.wholeEnv t pre stored

/-- Whether `y` is at a position of `order` (the position map's answer, checked). -/
def mem (order : Array Address) (positions : Std.HashMap Address Nat) (y : Address) : Bool :=
  match positions.get? y with
  | some j => j < order.size && order.getD j default == y
  | none => false

/-- Whether `y` is at a position of `order` before `i`. -/
def memBefore (order : Array Address) (positions : Std.HashMap Address Nat) (i : Nat)
    (y : Address) : Bool :=
  match positions.get? y with
  | some j => j < i && order.getD j default == y
  | none => false

/-- The check at position `i` of `order`:
* `positions` maps the address there to `i` (so no address is listed twice);
* it is a stored seed, or it is needed by the address at position `parent[i]`,
  which is nearer the seeds (`depth`);
* everything it needs is listed;
* every record it references resolves to a record listed before it, or to
  itself. -/
def positionCheck (ixe : Ixon.Env) (extra : Extra) (isSeed : Address → Bool) (order : Array Address)
    (positions : Std.HashMap Address Nat) (parent : Array (Option Nat)) (depth : Array Nat)
    (i : Nat) : Bool :=
  let a := order.getD i default
  positions.get? a == some i &&
  (match parent.getD i none with
    | none => isSeed a && ixe.consts.contains a
    | some p => p < order.size && depth.getD p 0 < depth.getD i 0 && edge ixe extra (order.getD p default) a) &&
  (match recordAt ixe a with
    | some c =>
      (ownerOf a c == a || mem order positions (ownerOf a c)) &&
      c.refs.all (fun r => !ixe.consts.contains r || mem order positions r) &&
      c.refs.all fun r => match recordAt ixe r with
        | some cr => ownerOf r cr == a || memBefore order positions i (ownerOf r cr)
        | none => true
    | none => true) &&
  (extra.getD a #[]).all (fun r => !ixe.consts.contains r || mem order positions r)

/-- **Is `order` an order of the compiled closure of the seeds** (`seeds`, with
`isSeed` deciding membership): every position checks (`positionCheck`), and every
stored seed is listed. -/
def closureOrderCheck (ixe : Ixon.Env) (extra : Extra) (seeds : Array Address) (isSeed : Address → Bool)
    (order : Array Address) (positions : Std.HashMap Address Nat) (parent : Array (Option Nat))
    (depth : Array Nat) : Bool :=
  parent.size == order.size && depth.size == order.size &&
  (List.range order.size).all (positionCheck ixe extra isSeed order positions parent depth) &&
  seeds.all fun s => !ixe.consts.contains s || mem order positions s

/-- The positions of an order. -/
def positionsOf (order : Array Address) : Std.HashMap Address Nat :=
  order.foldl (init := ((0 : Nat), ({} : Std.HashMap Address Nat))) (fun (i, m) a => (i + 1, m.insert a i)) |>.2

/-- The reach certificate carried to the positions of `order`. -/
def certificateOf (r : Reach) (order : Array Address) (positions : Std.HashMap Address Nat) :
    Array (Option Nat) × Array Nat :=
  let parent := order.map fun a =>
    match r.index.get? a with
    | some k => (r.parent.getD k none).bind fun p => positions.get? (r.found.getD p default)
    | none => none
  let depth := order.map fun a => match r.index.get? a with
    | some k => r.depth.getD k 0
    | none => 0
  (parent, depth)

/-! ## The certified entry on a closure -/

/-- What the checks run under: the role table's binding, the admitted table and its
prelude (for the order only), the batch limits and the artifact's hints. -/
structure Setting where
  binding : Binding
  table : Ix.Kernel.RoleTable
  prelude : Ix.Kernel.Reader.Prelude .anon
  limits : Limits
  hints : ConstRef Address → Option Ix.Kernel.ReducibilityHint
  extra : Extra

/-- A checked closure: its order and the environment the entry installed. -/
structure Checked where
  order : Array Address
  env : Env .anon

/-- The certified entry over `order`, once the decider passes it as an order of the
compiled closure of the seeds, with the reach certificate `cert`. -/
def runOrdered (s : Setting) (ixe : Ixon.Env) (seeds : Array Address) (isSeed : Address → Bool)
    (order : Array Address) (cert : Array (Option Nat) × Array Nat) : Except String Checked :=
  if closureOrderCheck ixe s.extra seeds isSeed order (positionsOf order) cert.1 cert.2 then
    match Ixon.Authenticated.checkBytes s.binding s.limits (recordsOf ixe order.toList)
        (blobsOf ixe order.toList) s.hints with
    | .ok env => .ok ⟨order, env⟩
    | .error e => .error s!"the certified entry refused the compiled closure ({order.size} \
records): {e}"
  else
    .error s!"the computed order of the compiled closure ({order.size} records) is not one \
(an order bug, not a verdict on the artifact)"

/-- **The certified entry on the compiled closure of `seeds`**: the closure's order,
decided to be one (`closureOrderCheck`), and the entry's run over its records. -/
def checkSeeds (s : Setting) (ixe : Ixon.Env) (seeds : Array Address) (isSeed : Address → Bool) :
    Except String Checked :=
  match seeds.find? (!ixe.consts.contains ·) with
  | some a => .error s!"the record published at {a} is missing from the artifact's store"
  | none =>
    let r := reach ixe s.extra seeds
    let order := orderOf ixe s.table s.prelude r
    runOrdered s ixe seeds isSeed order (certificateOf r order (positionsOf order))

/-- The address set of seeds. -/
def seedSet (seeds : Array Address) : Std.HashSet Address :=
  seeds.foldl (·.insert ·) {}

/-- `f` on every element, each on a task of its own, in order. -/
def parMap {α β : Type} (f : α → β) (xs : List α) : List β :=
  (xs.map fun x => Task.spawn fun _ => f x).map Task.get

/-- The tasks change nothing: `parMap` is `List.map`. -/
theorem parMap_eq {α β : Type} (f : α → β) (xs : List α) : parMap f xs = xs.map f := by
  simp only [parMap, List.map_map]
  rfl

/-- The first failure of a list of checks. -/
def firstError : List (Except String Unit) → Except String Unit
  | [] => .ok ()
  | .error e :: _ => .error e
  | .ok () :: rest => firstError rest

/-- No failure: every check passed. -/
theorem firstError_ok : ∀ {xs : List (Except String Unit)}, firstError xs = .ok () →
    ∀ x ∈ xs, x = .ok ()
  | [], _, _, h => nomatch h
  | .error _ :: _, h, _, _ => nomatch h
  | .ok () :: rest, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact firstError_ok (xs := rest) h x hx

/-! ## The plan and the check -/

/-- **What to check** on an artifact (see the module docstring). -/
structure Plan where
  /-- every root's published address -/
  seeds : Array Address := #[]
  /-- the required image computation-rule rows the artifact does not publish:
  the imaged recursor and the rule's index -/
  missingRows : Array (Ix.Name × Nat) := #[]
  /-- the roots whose terms the compiler rewrote, with their published addresses -/
  rewritten : Array (Ix.Name × Address) := #[]

/-- How the roots' acceptance is checked: one run of the certified entry over the
compiled closure of all of them, or one run per root. -/
inductive Mode where
  | union
  | perSeed
  deriving DecidableEq, Repr, Inhabited

/-- What a check did. -/
structure Stats where
  seeds : Nat := 0
  /-- records checked by the acceptance runs, summed over runs -/
  acceptedRecords : Nat := 0
  rewritten : Nat := 0
  /-- rewritten roots whose closure Source does not prepare (nothing to infer) -/
  sourceDeclined : Nat := 0
  /-- records checked by the rewritten roots' own runs, summed -/
  rewrittenRecords : Nat := 0
  /-- Source terms inferred -/
  inferred : Nat := 0
  deriving Repr, Inhabited

/-- The image rule rows a refusal names. -/
def showRows (rows : Array (Ix.Name × Nat)) : String :=
  let shown := rows.toList.take 6 |>.map fun (r, i) => s!"{r.pretty}._ix.rule.{i}"
  ", ".intercalate shown ++ (if rows.size > 6 then s!", … ({rows.size} in all)" else "")

/-- The run of one seed's own closure. -/
def checkOne (s : Setting) (ixe : Ixon.Env) (a : Address) : Except String Checked :=
  checkSeeds s ixe #[a] (· == a)

/-- The acceptance of the seeds: the records checked. -/
def acceptance (s : Setting) (ixe : Ixon.Env) (mode : Mode) (seeds : Array Address) :
    Except String Nat :=
  match mode with
  | .union => (checkSeeds s ixe seeds (seedSet seeds).contains).map (·.order.size)
  | .perSeed =>
    let runs := parMap (checkOne s ixe) (seedSet seeds).toList
    (firstError (runs.map fun r => r.map fun _ => ())).map fun _ =>
      runs.foldl (fun n r => n + match r with | .ok c => c.order.size | .error _ => 0) 0

/-- Each pair once, in order of first occurrence. -/
def distinctPairs (xs : Array (Ix.Name × Address)) : Array (Ix.Name × Address) :=
  (xs.foldl (init := (({} : Std.HashSet (Ix.Name × Address)), (#[] : Array (Ix.Name × Address))))
    fun (seen, out) p => if seen.contains p then (seen, out) else (seen.insert p, out.push p)).2

/-- The Source terms of a rewritten root inferring, at full grade, in the
environment its own compiled closure installs (`closure`; none when that closure
was not checked). -/
def inferCheck (n : Ix.Name) (closure : Option (Except String Checked))
    (terms : List (Ix.Kernel.Expr .anon)) : Except String Unit := do
  let some c := closure | throw s!"rewritten record {n.pretty}: its closure was not checked"
  let c ← c.mapError fun e => s!"rewritten record {n.pretty}: {e}"
  firstError (terms.map fun e =>
    match Ix.Kernel.inferTypeCore .verified c.env Ix.Kernel.checkFuel 0 e with
    | .ok _ => .ok ()
    | .error err => .error s!"the Source form of the rewritten record {n.pretty} does not infer \
in its compiled closure: {err}")

/-- The Source terms read for the rewritten roots: a failure to read refuses. -/
def readTerms (reads : List (Ix.Name × Address × Except String (Option (List (Ix.Kernel.Expr .anon))))) :
    Except String Unit :=
  firstError (reads.map fun (n, _, r) => match r with
    | .error e => .error s!"the Source form of {n.pretty} could not be read: {e}"
    | .ok _ => .ok ())

/-- The rewritten roots with Source terms to infer. -/
def withTerms (reads : List (Ix.Name × Address × Except String (Option (List (Ix.Kernel.Expr .anon))))) :
    List (Ix.Name × Address × List (Ix.Kernel.Expr .anon)) :=
  reads.filterMap fun (n, a, r) => match r with
    | .ok (some ts) => some (n, a, ts)
    | _ => none

/-- **The changed-cone check** of `plan` on `ixe`, with the rewritten roots' Source
terms from `sourceTerms`, in four steps, each refusing the artifact on its first
failure:
1. every required image computation-rule row is published;
2. the seeds' compiled closure is accepted (`acceptance`);
3. the Source terms of each rewritten root are read (`none`: Source does not
   prepare its closure, nothing to infer);
4. each rewritten root with terms: its own compiled closure, checked once per
   address (`checkOne`), and its terms inferring in the environment that
   installs (`inferCheck`).
Steps 2 to 4 run their independent parts on tasks (`parMap`). -/
def runWithStats (s : Setting) (mode : Mode) (plan : Plan)
    (sourceTerms : Ix.Name → Except String (Option (List (Ix.Kernel.Expr .anon))))
    (ixe : Ixon.Env) : Except String Stats := do
  unless plan.missingRows.isEmpty do
    throw s!"changed-cone check refused: {plan.missingRows.size} computation-rule row(s) of \
recursors imaged by a changed inductive block are not published ({showRows plan.missingRows}). \
The rows `r._ix.rule.i` are required for every rule of an imaged recursor; the compiler does not \
emit them yet"
  let accepted ← (acceptance s ixe mode plan.seeds).mapError fun e =>
    s!"changed-cone check refused: the compiled closure of the changed records is not accepted: {e}"
  let pairs := (distinctPairs plan.rewritten).toList
  let reads := parMap (fun (p : Ix.Name × Address) => (p.1, p.2, sourceTerms p.1)) pairs
  (readTerms reads).mapError fun e => s!"changed-cone check refused: {e}"
  let todo := withTerms reads
  let addresses := (seedSet (todo.map (·.2.1)).toArray).toList
  let closures := addresses.zip (parMap (checkOne s ixe) addresses)
  (firstError (parMap (fun (x : Ix.Name × Address × List (Ix.Kernel.Expr .anon)) =>
      inferCheck x.1 (closures.lookup x.2.1) x.2.2) todo)).mapError
    fun e => s!"changed-cone check refused: {e}"
  let declined := reads.filter fun x => x.2.2 matches .ok none
  let checkedRecords := closures.foldl (fun n x => n + (x.2.toOption.map (·.order.size)).getD 0) 0
  pure {
    seeds := plan.seeds.size, acceptedRecords := accepted, rewritten := pairs.length,
    sourceDeclined := declined.length, rewrittenRecords := checkedRecords,
    inferred := todo.foldl (fun n x => n + x.2.2.length) 0 }

/-! ## The extra edges

These are the statement's (`Ix.Cert.GroundEdge`, `Ix.Cert.RecursorEdge`), read under the
default role table: the roles are the statement's (`groundRoles`, `literalRoles`), and the
recursor index is the artifact's (`artifactRecIndex`). -/

/-- The roles among the keys `ks`. -/
def keyRoles {md : Ix.Kernel.Mode} (ks : List (Ix.Kernel.Key md)) : List Ix.Kernel.Role :=
  ks.filterMap fun
    | .role r => some r
    | _ => none

/-- The roles the fold reads when it installs the role `r` (a `Nat` operation's
certificate ground). -/
def groundRoles (r : Ix.Kernel.Role) : List Ix.Kernel.Role :=
  let k : Ix.Kernel.Key .anon := Ix.Kernel.roleKey r
  if Ix.Kernel.natOpNames.contains k || Ix.Kernel.natDivModNames.contains k then
    keyRoles (Ix.Kernel.natOpDeps k)
  else []

/-- The roles a record's literals are checked against. -/
def literalRoles (c : Ixon.Constant) : List Ix.Kernel.Role :=
  let kinds := Ix.Kernel.Reader.literalKinds c
  keyRoles (if kinds.2 then (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon))
    else if kinds.1 then Ix.Kernel.Reader.natLitSupportNames else [])

/-- The artifact's stored records, decoded, in its store's order. -/
def storedRecords (ixe : Ixon.Env) : Array (Address × Ixon.Constant) :=
  ixe.consts.toArray.filterMap fun (a, lc) => lc.get?.map (a, ·)

/-- The artifact's recursor index (the reader's and the check order's own). -/
def artifactRecIndex (ixe : Ixon.Env) : Ix.Kernel.Reader.RecIndex :=
  Ix.Kernel.Reader.buildIndex (recordAt ixe) (storedRecords ixe)

/-- Add the edges from `a` to `bs`. -/
def addEdges (m : Extra) (a : Address) (bs : List Address) : Extra :=
  if bs.isEmpty then m else m.alter a fun old => some ((old.getD #[]) ++ bs.toArray)

/-- **The extra edges of an artifact** under the role table `t`, to stored records only:
* ground: from the address bound to a role `r`, and from the block holding it, to the
  address bound to each role of `groundRoles r`;
* literal: from a stored record to the address bound to each role of its
  `literalRoles`;
* recursor: from an inductive block to each of its recursors' records, other than
  itself. -/
def extraEdges (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) : Extra :=
  let stored (b : Address) : Bool := ixe.consts.contains b
  let ground := Ix.Kernel.Role.all.foldl (init := ({} : Extra)) fun m r =>
    match t.addressOf? r with
    | none => m
    | some p =>
      let targets := ((groundRoles r).filterMap t.addressOf?).filter stored
      let m := addEdges m p targets
      match recordAt ixe p with
      | some c => addEdges m (ownerOf p c) targets
      | none => m
  let literal := (storedRecords ixe).foldl (init := ground) fun m (a, c) =>
    addEdges m a (((literalRoles c).filterMap t.addressOf?).filter stored)
  (artifactRecIndex ixe).blocks.fold (init := literal) fun m a shape =>
    addEdges m a ((shape.recs.toList.map (·.block)).filter fun b => b != a && stored b)

/-- The setting under the default role table, at the given limits: the admitted
default binding, its table and prelude (for the order), the hints, and the extra
edges under the default table. -/
def defaultSetting (ixe : Ixon.Env) (limits : Limits) : Except String Setting := do
  let binding ← Ix.Kernel.Admission.defaultBinding
  let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash binding).mapError
    fun e => s!"the default role table is not admitted: {Ix.Kernel.Admission.Error.binding e}"
  let prelude ← Ix.Kernel.Reader.preludeFor table
  let roles ← Ix.Kernel.Reader.defaultTable
  let projAt := projAtOf ixe
  let extra := extraEdges roles ixe
  pure { binding, table, prelude, limits, hints := hintsWith projAt ixe.anonHints, extra }

end Ix.Compile.ConeCheck

end
