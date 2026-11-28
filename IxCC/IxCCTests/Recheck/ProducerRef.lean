import IxCC.X86.Layout.Order
import IxCC.Anf.Pipeline

/-! # Reference copies of rewritten producer oracles

The producer is untrusted, so its oracles may be rewritten for speed; a
rewrite that is meant to change nothing must produce exactly what the code
it replaced produced. This module keeps that code, verbatim but for names,
as the oracle `tests-recheck` compares the rewrites against
(`IxCCTests.Recheck.Producer`). It is test code: nothing in production
imports it.

* `orderProduce`: the block-order oracle (`X86.Layout.Order.produce`) as it
  was when its cost was quadratic in a group's blocks (a path list searched at
  every edge of the depth-first search, a filter of the pending blocks and a
  scan of every loop at each chain start) and exponential in the two-way
  branches of a loop body (its loop search expanded a block once per path to
  it).
* `inlineProduce`, `specializeProduce` and `shrinkProduce`: the middle end's
  default oracles for P3, P4 and P2 (see their section). The producer now
  also cuts their choices to the certificate's caps and the re-run's
  budgets, so the comparison cuts the reference's the same way and, where the
  re-run refuses the reference's shrink certificate, asks only that the
  producer's be accepted. -/

namespace IxCCTests.Recheck.ProducerRef

open IxCC

abbrev NatMap := X86.Layout.NatMap
abbrev NatSet := X86.Layout.NatSet
abbrev Block := X86.Block
abbrev Group := X86.Layout.Group

/-- Successors in order of preference: a branch's false edge (which can
fall through), then its true edge; a jump's target. -/
def preferred (b : Block) : List Nat :=
  match b.terminator with
  | .branch _ _ _ yes no _ => [no.toNat, yes.toNat]
  | .jump t => [t.toNat]
  | _ => []

/-- A block's preferred successors among the blocks `ok` accepts. -/
def succsIn (m : NatMap Block) (ok : Nat → Bool) (b : Nat) : List Nat :=
  (((m.get? b).map preferred).getD []).filter ok

/-- Depth-first search from `b` (depth bounded by the fuel), adding the
blocks it visits to `seen` and each back edge `(u, h)` (`h` on the current
path) to the list. -/
def backEdges (m : NatMap Block) (ok : Nat → Bool) :
    Nat → List Nat → NatSet × List (Nat × Nat) → Nat → NatSet × List (Nat × Nat)
  | 0, _, acc, _ => acc
  | fuel + 1, path, (seen, backs), b =>
      let path := b :: path
      (succsIn m ok b).foldl (init := (seen.insert b, backs)) fun (seen, backs) t =>
        if path.contains t then (seen, (b, t) :: backs)
        else if seen.contains t then (seen, backs)
        else backEdges m ok fuel path (seen, backs) t

/-- Predecessors within the group, from each member's successors. -/
def predsIn (m : NatMap Block) (ok : Nat → Bool) (members : List Nat) : NatMap (List Nat) :=
  members.foldl (init := {}) fun acc b =>
    (succsIn m ok b).foldl (init := acc) fun acc t => acc.insert t (b :: acc.getD t [])

/-- The natural loop of a back edge into `h`: `body` starts as `{h}`, and
the search walks predecessors backwards from the edge's source, one
frontier per unit of fuel, never past `h`. -/
def loopBody (preds : NatMap (List Nat)) : Nat → NatSet → List Nat → NatSet
  | 0, body, _ => body
  | _, body, [] => body
  | fuel + 1, body, frontier =>
      let fresh := frontier.filter (!body.contains ·)
      let body := fresh.foldl (fun s b => s.insert b) body
      loopBody preds fuel body (fresh.flatMap (preds.getD · []))

/-- A loop per header: the union of the natural loops of its back edges. -/
def addLoop (loops : List (Nat × NatSet)) (h : Nat) (body : NatSet) : List (Nat × NatSet) :=
  if loops.any (·.1 == h) then
    loops.map fun (h', b) => if h' == h then (h', body.toList.foldl (fun s x => s.insert x) b) else (h', b)
  else (h, body) :: loops

/-- The size of the smallest loop containing both blocks, else `none'`. -/
def sharedLoop (loops : List (Nat × NatSet)) (none' a b : Nat) : Nat :=
  loops.foldl (init := none') fun best (_, body) =>
    if body.contains a && body.contains b then min best body.size else best

/-- The first candidate with the smallest score. -/
def pickBest (score : Nat → Nat) : List Nat → Option Nat
  | [] => none
  | c :: cs =>
      match pickBest score cs with
      | some d => if score d < score c then some d else some c
      | none => some c

/-- Place `b`, then keep following the unplaced successor that stays in the
smallest loop shared with the block just placed. The placed blocks are a
set and a list in reverse order. -/
def extendChain (m : NatMap Block) (ok : Nat → Bool) (loops : List (Nat × NatSet)) (none' : Nat) :
    Nat → NatSet × List Nat → Nat → NatSet × List Nat
  | 0, placed, _ => placed
  | fuel + 1, (done, order), b =>
      let done := done.insert b
      let order := b :: order
      match pickBest (sharedLoop loops none' b) ((succsIn m ok b).filter (!done.contains ·)) with
      | some t => extendChain m ok loops none' fuel (done, order) t
      | none => (done, order)

/-- Start a chain at the unplaced block sharing the smallest loop with the
last block placed (the first pending block when none does, or when nothing
is placed yet), until every pending block is placed. -/
def chains (m : NatMap Block) (ok : Nat → Bool) (loops : List (Nat × NatSet)) (none' bound : Nat) :
    Nat → NatSet × List Nat → List Nat → NatSet × List Nat
  | 0, placed, _ => placed
  | fuel + 1, (done, order), pending =>
      match pending.filter (!done.contains ·) with
      | [] => (done, order)
      | first :: rest =>
          let start := match order.head? with
            | some last => (pickBest (sharedLoop loops none' last) (first :: rest)).getD first
            | none => first
          chains m ok loops none' bound fuel (extendChain m ok loops none' bound (done, order) start)
            (first :: rest)

/-- One group's order: the entry, chains through hot blocks, then the cold
blocks in index order. -/
def groupOrder (m : NatMap Block) (seen : NatSet) (g : Group) : List Nat :=
  let members := ((List.range g.count).map (g.start + ·)).filter seen.contains
  let isCold (b : Nat) : Bool := g.cold.contains b && g.entry != some b
  let hot := members.filter (!isCold ·)
  let cold := members.filter isCold
  let ok (t : Nat) : Bool := g.contains t && seen.contains t && !isCold t
  let start := match g.entry with
    | some e => if seen.contains e then [e] else []
    | none => []
  let pending := start ++ hot
  let fuel := members.length + 1
  let (_, backs) := pending.foldl (init := (({} : NatSet), ([] : List (Nat × Nat)))) fun acc r =>
    if acc.1.contains r then acc else backEdges m ok fuel [] acc r
  let preds := predsIn m ok hot
  let loops := backs.foldl (init := []) fun loops (u, h) =>
    addLoop loops h (loopBody preds fuel (({} : NatSet).insert h) [u])
  (chains m ok loops fuel fuel fuel ({}, []) pending).2.reverse ++ cold

def orderProduce (p : X86.Program) (s : X86.Layout.Shape) : X86.Layout.Order :=
  let m := X86.Layout.blockMap p
  let seen := X86.Layout.reachable p s.roots
  s.groups.map (groupOrder m seen)


/-! ## The middle end's default oracles

`inlineProduce` (P3, with `inlineReachable` and `inlineRecursive`),
`specializeProduce` (P4) and `shrinkProduce` (P2) as they were when the
recursive set took a reachability walk from every global (quadratic in the
globals), each reference's callee was re-measured and its sites searched as
lists, the specialisation masks were an association list, and the shrink
certificate searched the results once per global id. -/

section Middle

open IxCC.Anf (GlobalId GDef Program)

/-- The globals reachable from `g` in one or more steps. -/
def inlineReachable (edges : Src.NatMap (List GlobalId)) (size g : Nat) : List GlobalId := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := edges.getD g []
  let mut out := #[]
  for _ in [0:size * size + size + 1] do
    match todo with
    | [] => break
    | h :: rest =>
      todo := rest
      if seen.contains h then continue
      seen := seen.insert h
      out := out.push h
      todo := edges.getD h [] ++ todo
  return out.toList

/-- Globals on a cycle of the reference graph. -/
def inlineRecursive (P : Program) : Std.HashSet GlobalId := Id.run do
  let edges : Src.NatMap (List GlobalId) :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) => (g, gd.body.refs.eraseDups))
  let mut out : Std.HashSet GlobalId := {}
  for (g, _) in P.globalList do
    if (inlineReachable edges P.size g).contains g then out := out.insert g
  return out

/-- The default oracle's next round: for each caller, the inlinable callees
it references (none if nothing remains). -/
def inlineProduce (B : Anf.Inline.Budgets) (P : Program) : Anf.Inline.Round :=
  let recs := inlineRecursive P
  P.globalList.filterMap fun (f, gd) =>
    let sites := gd.body.sites
    let cs := gd.body.refs.eraseDups.filter fun g =>
      g != f && (match P.global? g with
        | some gd' =>
          -- a function `glob` is a closure, not a site: only calls and CAFs
          Anf.Inline.inlinable B recs gd' g && (gd'.ps.isEmpty || sites.contains g)
        | none => false)
    if cs.isEmpty then none else some (f, cs)

def specializeProduce (_B : Anf.Specialize.Budgets) (inv : Nat) (P : Program) : Anf.Specialize.Cert :=
  let masks := P.globalList.map fun (g, gd) => (g, Anf.Specialize.fixedMask g gd)
  let ds := P.globalList.flatMap fun (f, gd) =>
    gd.body.sites.eraseDups.filterMap fun g =>
      match masks.lookup g with
      | some mask => if g != f && mask.any id then some { caller := f, callee := g, mask } else none
      | none => none
  { inv, decisions := ds }

/-- `produce`: each global to its fixpoint; the certificate, the program and
the rule counts. -/
def shrinkProduce (B : Anf.Shrink.Budgets) (P : Program) :
    Except String (Anf.Shrink.Cert × Program × Anf.Walk.Fires) := do
  let rs ← P.globalList.mapM fun (g, gd) => do
    let (gd', n, f) ← (Anf.Shrink.fixpoint P B.params gd B.rounds 0 {}).mapError (s!"shrink global {g}: " ++ ·)
    return (g, gd', n, f)
  let P' := { P with globals := Src.NatMap.ofList (rs.map fun (g, gd, _) => (g, gd)) }
  let cert := (List.range P.size).map fun g => ((rs.find? (·.1 == g)).map (·.2.2.1)).getD 0
  return (cert, P', rs.foldl (fun acc (_, _, _, f) => acc.add f) {})

end Middle

end IxCCTests.Recheck.ProducerRef
