import IxCC.Anf.Defun.Dispatch

/-! # P8: closed-world defunctionalisation

`Anf.defun` (P8, `docs/closures-design.md`) turns every remaining local
function into a constructor and every unknown call into a call of a
generated dispatcher, so that its output is `Anf.FirstOrder`, which
`Fir.lower` accepts. The walk (`Defun.Lift`) rewrites each global; this
module checks the input, bounds the work, assembles the program and adds the
closure keys and the dispatchers (`Defun.Dispatch`):

* **ids**: the input's globals keep theirs; the dispatchers of arities
  `1 … M` (`M` the largest `app` arity) follow at `size + m - 1` (every arity
  below `M` is needed: an over-application by `r` arguments tail-calls the
  dispatcher of `m - r`); the lifted local functions follow, in global order
  and post-order within a global;
* **sources**: the escaping function globals by id, then the lifted local
  functions; each adds its closure keys to the constructor table with fresh
  tags from 0 (closure keys share no `case` with source constructors);
* **declines** (the closures design's): a closure cell with more fields than
  a constructor cell holds (`defun.captures`), more closure keys than tags
  (`defun.tags`);
* **input checks** (what P8's correctness needs and a well-scoped program
  meets, since the pipeline does not establish `WellScoped`): no global keyed
  as P8 keys them (`lam`, `dispatch`), no closure key in the table or among
  the pinned constructors, distinct keys for the globals whose closures the
  program builds, and the walk's own checks (`Lift.bind`);
* **budgets**: the walk's work (`Lift.programWork`, its nodes plus the depth
  of every local function) within `maxStepWork`, and the dispatchers' nodes
  (computed without building them) within `maxGlobalNodes` each and
  `maxProgramNodes` in all, before the work is done. The pipeline's size
  check after a step bounds the result as for every other step.

P8 reads no certificate data: it is deterministic (style P, D17).
Kernel-evaluable: lists, `Src.NatMap`, structural recursion. -/

namespace IxCC.Anf.Defun

/-- The most fields a constructor cell's header counts (`Rt.maxFields`). -/
def maxCellFields : Nat := 254

/-- The constructor tags (`Rt.maxTag + 1`): every closure key gets its own. -/
def maxClosureKeys : Nat := 0x7F00

/-- The keys P8 gives the globals it makes. -/
def reservedKey : Key.GKey → Bool
  | .lam .. | .dispatch _ => true
  | _ => false

def closureKey : Key.CtorKey → Bool
  | .clo .. => true
  | .src _ => false

/-- Whether a pinned constructor (`Nat`'s and `Bool`'s) has a closure key:
the closure keys P8 adds to the table would then give it their arity. -/
def knownClosure (K : Lam.Known) : Bool :=
  [K.natZero, K.natSucc, K.boolFalse, K.boolTrue].any fun c => c.any closureKey

/-- The first two of `ks` (keys with their globals) with equal keys, if any:
keys are bucketed by their source constant (`GKey.bucket`) and compared
within a bucket. The pass runs `firstEqualKeysT`, which finds the same pair
in time linear in the keys' sizes; this is its specification. -/
def firstEqualKeys : List (Key.GKey × GlobalId) → Src.NatMap (List (Key.GKey × GlobalId)) →
    Option (GlobalId × GlobalId)
  | [], _ => none
  | (k, g) :: ks, m =>
    let b := m.getD k.bucket []
    match b.find? (fun (k', _) => decide (k' = k)) with
    | some (_, h) => some (h, g)
    | none => firstEqualKeys ks (m.insert k.bucket ((k, g) :: b))

/-! ## The key check, linear

Each key is filed in a trie under its code, a prefix-free serialisation into
numbers (each constructor its tag, then its fields; each list its length, then
its elements), so that distinct keys have distinct codes. A key is compared
only with the keys already filed under its own code, which are equal to it,
so the check costs the keys' sizes (times the depth of a `Src.NatMap` step). -/

def bitCode (b : Bool) : Nat := if b then 1 else 0

/-- A universe profile's code: its length, then its bits. -/
def profileCode (p : Key.Profile) : List Nat := p.length :: p.map bitCode

def headCode : Src.Head → List Nat
  | .ctor c => [0, c]
  | .quotMk c => [1, c]
  | .quotLift c => [2, c]
  | .recr c => [3, c]
  | .cases c => [4, c]
  | .prim op => [5, Src.PrimOp.all.idxOf op]

mutual

/-- A global key's code. -/
def gkeyCode : Key.GKey → List Nat
  | .const c p => 0 :: c :: profileCode p
  | .byName c p => 1 :: c :: profileCode p
  | .recStar c p => 2 :: c :: profileCode p
  | .wrapper h p => 3 :: (headCode h ++ profileCode p)
  | .spec g as => 4 :: (gkeyCode g ++ (as.length :: argsCode as))
  | .worker g keep => 5 :: (gkeyCode g ++ (keep.length :: keep.map bitCode))
  | .lam g path => 6 :: (gkeyCode g ++ (path.length :: path))
  | .dispatch n => [7, n]
  termination_by structural k => k

def ctorKeyCode : Key.CtorKey → List Nat
  | .src c => [0, c]
  | .clo f n => 1 :: (gkeyCode f ++ [n])
  termination_by structural k => k

def argKeyCode : Key.ArgKey → List Nat
  | .glob g => 0 :: gkeyCode g
  | .con c as => 1 :: (ctorKeyCode c ++ (as.length :: argsCode as))
  | .lit n => [2, n]
  | .hole i => [3, i]
  termination_by structural k => k

/-- The codes of specialisation arguments, one after another. -/
def argsCode : List Key.ArgKey → List Nat
  | [] => []
  | a :: as => argKeyCode a ++ argsCode as
  termination_by structural as => as

end

/-- Keys filed by their codes: a node holds the keys (with their globals)
whose code ends there, newest first, and its children by the code's next
number. -/
inductive KeyTrie where
  | node (here : List (Key.GKey × GlobalId)) (kids : Src.NatMap KeyTrie)

namespace KeyTrie

def empty : KeyTrie := .node [] .leaf

/-- The keys filed under `code`. -/
def find : KeyTrie → List Nat → List (Key.GKey × GlobalId)
  | .node h _, [] => h
  | .node _ k, c :: cs =>
    match k.get? c with
    | some t => t.find cs
    | none => []
  termination_by structural _ code => code

/-- File `x` under `code`. -/
def add : KeyTrie → List Nat → Key.GKey × GlobalId → KeyTrie
  | .node h k, [], x => .node (x :: h) k
  | .node h k, c :: cs, x => .node h (k.insert c (((k.get? c).getD empty).add cs x))
  termination_by structural _ code => code

end KeyTrie

/-- The first two of `ks` (keys with their globals) with equal keys, if any:
each key is compared with the keys filed under its code, then filed. It finds
what `firstEqualKeys` finds (`Proof.firstEqualKeysT_eq`). -/
def firstEqualKeysT : List (Key.GKey × GlobalId) → KeyTrie → Option (GlobalId × GlobalId)
  | [], _ => none
  | (k, g) :: ks, t =>
    match (t.find (gkeyCode k)).find? (fun (k', _) => decide (k' = k)) with
    | some (_, h) => some (h, g)
    | none => firstEqualKeysT ks (t.add (gkeyCode k) (k, g))

/-- Rewrite the globals in order (a loop), and collect the globals that hold
local functions. -/
def globalsGo (P : Program) : List (GlobalId × GDef) → Acc → List GlobalId → List (GlobalId × GDef) →
    Except Error (List (GlobalId × GDef) × Acc × List GlobalId)
  | [], acc, parents, out => .ok (out.reverse, acc, parents)
  | (g, gd) :: rest, acc, parents, out =>
    match global P g gd acc with
    | .error e => .error e
    | .ok (gd', acc) => globalsGo P rest acc (if acc.next > 0 then g :: parents else parents) ((g, gd') :: out)

/-- The dispatchers' nodes, arity by arity, refused as soon as one passes
`maxGlobalNodes` or all pass `maxProgramNodes`. -/
def checkDispatchers (srcs : List Source) : List Nat → Nat → Except Error Unit
  | [], _ => .ok ()
  | m :: ms, used =>
    let n := dispNodesUpTo maxGlobalNodes m srcs 1
    if n > maxGlobalNodes then .error (.budget s!"the dispatcher of arity {m} exceeds the global node budget")
    else if used + n > maxProgramNodes then .error (.budget "the dispatchers exceed the program node budget")
    else checkDispatchers srcs ms (used + n)

/-- The input checks and the walk's work bound, before the walk. -/
def checkInput (P : Program) : Except Error Unit := do
  if let some (g, _) := P.globalList.find? (fun (_, gd) => reservedKey gd.key) then
    throw (.input g "a global already keyed as a lifted local function or a dispatcher")
  if P.ctors.any (fun r => closureKey r.key) || knownClosure P.known then throw .table
  if programWork maxStepWork P.globalList 0 > maxStepWork then
    throw (.budget "the walk's work exceeds the step work budget")

/-- The id of the first lifted function: after the input's globals and the
dispatchers. -/
def liftBase (P : Program) (acc : Acc) : GlobalId := P.size + acc.maxApp

/-- The escaping function globals as closure sources, by id. -/
def escapeSources (P : Program) (acc : Acc) : List Source :=
  (List.range P.size).filterMap fun h =>
    if acc.escapes.contains h then
      (P.global? h).map fun hd => { key := hd.key, id := h, caps := 0, arity := hd.ps.length }
    else none

/-- `xs` numbered from `k`. -/
def numbered {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: numbered (k + 1) xs

/-- The lifted functions at their ids, after the dispatchers. -/
def liftedAt (P : Program) (acc : Acc) : List (GlobalId × Lifted) :=
  numbered (liftBase P acc) acc.lifted.reverse

/-- The closure sources: the escaping globals, then the lifted functions in
id order. -/
def sources (P : Program) (acc : Acc) : List Source :=
  escapeSources P acc ++ (liftedAt P acc).map fun (i, l) =>
    { key := l.key, id := i, caps := l.ncaps, arity := l.ps.length }

/-- The back end's work on the dispatchers' switches (`Anf.backWork`'s `case`
term): `M` switches of `K` alternatives, each costing its square times the
grown table's length. With `maxBackWork = 2^28` and a table of about `K`
rows this admits `K` up to about 510 at `M = 1` and about 255 at `M = 8`. -/
def dispatchWork (P : Program) (M K : Nat) : Nat := M * (K * K) * (P.ctors.length + K + 1)

/-- The checks on the sources: distinct keys for the globals whose closures
the program builds (lifted keys then differ by their index, and from every
input key, which is never `lam`), the declines, and the dispatchers' size. -/
def checkSources (P : Program) (acc : Acc) (parents : List GlobalId) : Except Error Unit := do
  let srcs := sources P acc
  let owners := Src.NatSet.ofList ((escapeSources P acc).map (·.id) ++ parents)
  let ownerKeys := (List.range P.size).filterMap fun h =>
    if owners.contains h then (P.global? h).map fun hd => (hd.key, h) else none
  if let some (g, h) := firstEqualKeysT ownerKeys .empty then throw (.keys g h)
  if let some s := srcs.find? (fun s => s.caps + s.arity > maxCellFields + 1) then
    throw (.captures s.id (s.caps + s.arity - 1))
  let nkeys := srcs.foldl (fun n s => n + s.arity) 0
  if nkeys > maxClosureKeys then throw (.tags nkeys)
  -- each dispatcher is one `case` of `nkeys` alternatives: the back end's
  -- switch check and table searches cost its square times the table's length
  -- (`Anf.backWork`), so `dispatchWork` is capped before anything is built
  if dispatchWork P acc.maxApp nkeys > maxBackWork then
    throw (.budget s!"{acc.maxApp} dispatchers of {nkeys} alternatives exceed the back end's work budget")
  checkDispatchers srcs ((List.range acc.maxApp).map (· + 1)) 0

/-- The output: the rewritten globals at their ids, the dispatchers, the
lifted functions, and the closure keys appended to the table. -/
def assemble (P : Program) (gs : List (GlobalId × GDef)) (acc : Acc) : Program :=
  let srcs := sources P acc
  let disps := (List.range acc.maxApp).map fun i => (P.size + i, dispatcher P.size srcs (i + 1))
  let lifts := (liftedAt P acc).map fun (i, l) => (i, l.toGDef)
  { P with globals := Src.NatMap.ofList (gs ++ disps ++ lifts), size := liftBase P acc + acc.lifted.length
           ctors := P.ctors ++ rows srcs 0 }

/-- P8 on a program. -/
def run (P : Program) : Except Error Program := do
  checkInput P
  let (gs, acc, parents) ← globalsGo P P.globalList {} [] []
  checkSources P acc parents
  pure (assemble P gs acc)

end Defun

/-- **P8**: closed-world defunctionalisation (see `Anf.Defun`). -/
def defun (P : Program) : Except String Program := (Defun.run P).mapError Defun.Error.render

end IxCC.Anf
