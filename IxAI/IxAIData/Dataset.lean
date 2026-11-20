import IxAIData.Relevance
import IxAICommon.Merkle

/-!
# The premise-selection dataset on the host

Reads an extraction (`ix/premises/extract.sh`: `decls.tsv` and `names.tsv`), keys every
declaration by its Ixon address, applies the curation rules of `IxAIData.Rules`, builds training
pairs with hard negatives, and evaluates rankings. Names are metadata beside the addresses: they
label reports and feed the scorer's name features, and never enter an address.
-/

namespace IxAIData

open IxAI IxAICore

abbrev Addr := Digest

/-- The featurizer's bucket key: the first two address bytes. -/
def addrKey (d : Addr) : Nat := (d.bytes.get! 0).toNat * 256 + (d.bytes.get! 1).toNat

/-- Lean's `Name.toString` wraps some components in `«»`, Ix's display does not. -/
def normName (s : String) : String := String.ofList (s.toList.filter fun c => c ≠ '«' && c ≠ '»')

structure Module where
  name : String
  imports : List Nat
  deriving Inhabited

structure Extraction where
  modules : Array Module
  /-- Library theorems with their names. -/
  library : Array (Premise Addr × String)
  /-- Scope theorems with their names, in declaration order. -/
  items : Array (Item Addr × String)
  /-- Names that `names.tsv` does not address. -/
  unjoined : Nat
  names : Std.HashMap String Addr
  /-- Each address's first name in `names.tsv` order. -/
  addrNames : Std.HashMap Addr String

def splitTab (l : String) : List String := l.splitOn "\t"
def splitComma (s : String) : List String := if s.isEmpty then [] else s.splitOn ","

/-- `NAME → ADDRESS`, and each address's first name in file order. -/
def readNames (path : System.FilePath) : IO (Std.HashMap String Addr × Std.HashMap Addr String) := do
  let mut m : Std.HashMap String Addr := {}
  let mut inv : Std.HashMap Addr String := {}
  for l in (← IO.FS.lines path) do
    match splitTab l with
    | [n, a] =>
      if let some d := Digest.ofHex? a then
        m := m.insert (normName n) d
        if !inv.contains d then inv := inv.insert d (normName n)
    | _ => pure ()
  return (m, inv)

/-- `name*count` entries of a statement, as addresses. -/
def parseStatement (names : Std.HashMap String Addr) (consts kinds : String) :
    Statement Addr × Nat :=
  let cs := (splitComma consts).map fun e =>
    match e.splitOn "*" with
    | [n, k] => (names.get? (normName n), k.toNat!)
    | _ => (none, 0)
  ({ consts := cs.filterMap fun (a, k) => a.map (·, k)
     kinds := (splitComma kinds).map String.toNat! },
   (cs.filter (·.1.isNone)).length)

/-- Add the `HEAD,LHS,RHS` and `BINDERS,HYPS` fields of a `lib` record. -/
def withShape (names : Std.HashMap String Addr) (s : Statement Addr) (heads arity : String) :
    Statement Addr :=
  let hs := match heads.splitOn "," with
    | [h, l, r] => [h, l, r].map fun n => if n.isEmpty then none else names.get? (normName n)
    | _ => [none, none, none]
  match arity.splitOn "," with
  | [b, h] => { s with heads := hs, binders := b.toNat!, hyps := h.toNat! }
  | _ => { s with heads := hs }

/-- An `item` record's fields: the scope theorem, the constants its proof uses and its axioms.
A name that `names.tsv` does not address is counted in `unresolved` (and so refused by
`acceptance`), never silently dropped from the item's lists. -/
def itemOf (names : Std.HashMap String Addr) (thm : Premise Addr) (pcs axs nat : String) :
    Item Addr :=
  let look := fun (s : String) => (splitComma s).map fun c => names.get? (normName c)
  let uses := look pcs
  let axioms := look axs
  { thm, uses := uses.filterMap id, axioms := axioms.filterMap id, native := nat == "1"
    unresolved := (uses.filter (·.isNone)).length + (axioms.filter (·.isNone)).length }

def readExtraction (dir : System.FilePath) : IO Extraction := do
  let (names, addrNames) ← readNames (dir / "names.tsv")
  let mut modules : Array Module := #[]
  let mut library : Array (Premise Addr × String) := #[]
  let mut byName : Std.HashMap String (Premise Addr) := {}
  let mut items : Array (Item Addr × String) := #[]
  let mut unjoined := 0
  for l in (← IO.FS.lines (dir / "decls.tsv")) do
    match splitTab l with
    | ["mod", _, n, imps] => modules := modules.push ⟨n, (splitComma imps).map String.toNat!⟩
    | "lib" :: n :: m :: d :: tc :: ks :: shape =>
      let (stmt, miss) := parseStatement names tc ks
      let stmt := match shape with
        | [hs, ar] => withShape names stmt hs ar
        | _ => stmt
      unjoined := unjoined + miss
      match names.get? (normName n) with
      | some a =>
        let p : Premise Addr := ⟨a, m.toNat!, d.toNat!, stmt⟩
        library := library.push (p, n)
        byName := byName.insert n p
      | none => unjoined := unjoined + 1
    | ["item", n, pcs, axs, nat] =>
      match byName.get? n with
      | some p =>
        let it := itemOf names p pcs axs nat
        unjoined := unjoined + it.unresolved
        items := items.push (it, n)
      | none => pure ()
    | _ => pure ()
  return { modules, library, items, unjoined, names, addrNames }

/-! ## Accessibility -/

/-- For every module, which modules it imports transitively (itself included). -/
def reachability (modules : Array Module) : Array (Array Bool) := Id.run do
  let n := modules.size
  let mut reach : Array (Array Bool) := #[]
  -- Modules are listed after their imports, so one pass in order suffices.
  for i in [:n] do
    let mut r := (Array.replicate n false).set! i true
    for j in modules[i]!.imports do
      let rj := reach[j]!
      for k in [:n] do
        if rj[k]! then r := r.set! k true
    reach := reach.push r
  return reach

/-- A premise is accessible to a theorem when its module is imported, or it comes earlier in the
same module. -/
def accessible (reach : Array (Array Bool)) (p : Premise Addr) (t : Premise Addr) : Bool :=
  if p.module == t.module then p.decl < t.decl else reach[t.module]![p.module]!

/-! ## Curation -/

structure Curated where
  policy : Policy Addr
  accepted : List (Item Addr)
  refusals : List (Refusal × Nat)
  withPremises : List (Item Addr)
  deduped : List (Item Addr)
  nonempty : List (Item Addr)
  train : List (Item Addr)
  test : List (Item Addr)
  disjoint : Bool

def curate (ex : Extraction) (policy : Policy Addr) (isTest : Nat → Bool) : Curated :=
  let raw := ex.items.toList.map (·.1)
  let refused := raw.filterMap (acceptance policy)
  let refusals := [Refusal.unresolvedName, .usesSorry, .extraAxiom, .nativeRef].map fun r =>
    (r, (refused.filter (· == r)).length)
  let accepted := raw.filter (accepted policy)
  let libSet := setOf (ex.library.toList.map (·.1.addr))
  let withPremises := accepted.map (premiseRuleSet libSet)
  let deduped := dedupFast withPremises
  let nonempty := deduped.filter (!·.premises.isEmpty)
  let (train, test) := splitFast isTest nonempty
  { policy, accepted, refusals, withPremises, deduped, nonempty, train, test
    disjoint := disjointFast train test }

/-- `curate` computes the specifications: acceptance (every accepted item has all of its names
addressed and only allowed axioms), `premiseRule` over the library, `dedup`, `split` and
`disjoint`. -/
theorem curate_spec (ex : Extraction) (policy : Policy Addr) (isTest : Nat → Bool) :
    let c := curate ex policy isTest
    let lib := ex.library.toList.map (·.1.addr)
    (∀ it ∈ c.accepted, it.unresolved = 0 ∧ ∀ a ∈ it.axioms, a ∈ policy.allowedAxioms) ∧
      c.withPremises = c.accepted.map (premiseRule lib) ∧ c.deduped = dedup c.withPremises ∧
      (c.train, c.test) = split isTest c.nonempty ∧ c.disjoint = disjoint c.train c.test := by
  refine ⟨?_, ?_⟩
  · intro it hit
    simp only [curate, List.mem_filter] at hit
    exact ⟨accepted_resolved _ _ hit.2, accepted_axioms _ _ hit.2⟩
  · simp only [curate, dedupFast_eq, splitFast_eq, disjointFast_eq, and_true]
    apply List.map_congr_left
    intro it _
    exact premiseRuleSet_eq _ it

/-- The premise rule recomputed from the library list, through `premiseRuleSet`
(`premiseRuleSet_eq`), agrees with the curated items' premises. -/
def premiseRuleAgrees (ex : Extraction) (c : Curated) : Bool :=
  let lib := setOf (ex.library.toList.map (·.1.addr))
  c.withPremises.all fun it => (premiseRuleSet lib it).premises == it.premises

/-! ## Training pairs -/

structure PairConfig where
  features : Features
  seed : Nat
  /-- Negatives per item drawn from the modules of its premises. -/
  hard : Nat
  /-- Negatives per item drawn from all accessible premises. -/
  random : Nat

structure Library where
  premises : Array (Premise Addr)
  /-- The declaration name of each premise: metadata beside its address, not part of it. -/
  names : Array String
  /-- A name for each constant address, for the constants statements mention. -/
  constNames : Std.HashMap Addr String
  byAddr : Std.HashMap Addr (Premise Addr)
  byModule : Array (Array (Premise Addr))
  reach : Array (Array Bool)
  /-- Per module, the modules it imports transitively. -/
  ancestors : Array (Array Nat)
  /-- Per constant, how many library statements mention it. -/
  docFreq : Std.HashMap Addr Nat

def Library.of (ex : Extraction) : Library :=
  let reach := reachability ex.modules
  let n := ex.modules.size
  let byModule := ex.library.foldl (fun acc (p, _) => acc.modify p.module (·.push p))
    (Array.replicate n #[])
  { premises := ex.library.map (·.1)
    names := ex.library.map (·.2)
    constNames := ex.addrNames
    byAddr := ex.library.foldl (fun m (p, _) => if m.contains p.addr then m else m.insert p.addr p) {}
    byModule, reach
    ancestors := reach.map fun r => (List.range n).toArray.filter (r[·]!)
    docFreq := ex.library.foldl (fun m (p, _) =>
      p.stmt.consts.foldl (fun m (c, _) => m.insert c (m.getD c 0 + 1)) m) {} }

/-- Draw up to `count` premises from `pool` that pass `ok`, with `fuel` attempts. -/
def drawFrom (pool : Rng → Option (Premise Addr) × Rng) (ok : Premise Addr → Bool) :
    Nat → Nat → Rng → List (Premise Addr) → List (Premise Addr) × Rng
  | 0, _, r, acc => (acc.reverse, r)
  | _, 0, r, acc => (acc.reverse, r)
  | count + 1, fuel + 1, r, acc =>
    let (p?, r) := pool r
    match p? with
    | some p => if ok p && !acc.any (·.addr == p.addr) then drawFrom pool ok count (fuel + 1) r (p :: acc)
                else drawFrom pool ok (count + 1) fuel r acc
    | none => drawFrom pool ok (count + 1) fuel r acc

def pickIn {β : Type} (xs : Array β) (r : Rng) : Option β × Rng :=
  if xs.isEmpty then (none, r) else let (i, r) := r.below xs.size; (xs[i]?, r)

/-- Hard negatives in the ReProver style: accessible, unused premises, half from the modules the
proof draws on and half from all accessible modules. -/
def negatives (lib : Library) (pc : PairConfig) (it : Item Addr) (r : Rng) : List (Premise Addr) × Rng :=
  let ok := fun (p : Premise Addr) => p.addr != it.addr && !it.premises.contains p.addr &&
    accessible lib.reach p it.thm
  let mods := (it.premises.filterMap fun a => (lib.byAddr.get? a).map (·.module)).toArray
  let fromMods := fun (r : Rng) =>
    let (m?, r) := pickIn mods r
    match m? with
    | some m => pickIn lib.byModule[m]! r
    | none => (none, r)
  let fromAll := fun (r : Rng) =>
    let (m?, r) := pickIn lib.ancestors[it.module]! r
    match m? with
    | some m => pickIn lib.byModule[m]! r
    | none => (none, r)
  let (hard, r) := drawFrom fromMods ok pc.hard (8 * pc.hard) r []
  let (rnd, r) := drawFrom fromAll (fun p => ok p && !hard.any (·.addr == p.addr)) pc.random
    (8 * pc.random) r []
  (hard ++ rnd, r)

/-- How many training items use each premise. -/
abbrev Prior := Std.HashMap Addr Nat

def priorOf (train : List (Item Addr)) : Prior :=
  train.foldl (fun m it => it.premises.foldl (fun m a => m.insert a (m.getD a 0 + 1)) m) {}

def rareBound : Nat := 16

def contextOf (lib : Library) (prior : Prior) (t p : Premise Addr) : PairContext :=
  let tc := t.stmt.consts.map (·.1)
  let shared := p.stmt.consts.filter fun (c, _) => tc.contains c
  { prior := prior.getD p.addr 0
    shared := shared.length
    sharedRare := (shared.filter fun (c, _) => lib.docFreq.getD c 0 ≤ rareBound).length
    sameModule := p.module == t.module
    distance := t.decl - p.decl }

def pairOf (lib : Library) (pc : PairConfig) (prior : Prior) (t p : Premise Addr) (relevant : Bool) :
    Pair :=
  ⟨pairFeatures pc.features addrKey t.stmt p.stmt (contextOf lib prior t p), relevant⟩

def pairsOf (lib : Library) (pc : PairConfig) (prior : Prior) (items : List (Item Addr)) : List Pair :=
  let rec go : List (Item Addr) → Rng → List Pair
    | [], _ => []
    | it :: rest, r =>
      let pos := it.premises.filterMap fun a => (lib.byAddr.get? a).map fun p =>
        pairOf lib pc prior it.thm p true
      let (negs, r) := negatives lib pc it r
      let neg := negs.map fun p => pairOf lib pc prior it.thm p false
      pos ++ neg ++ go rest r
  go items (Rng.seeded pc.seed)

/-! ## Ranking -/

/-- `score` with the first layer split into a statement part, a premise part and a per-pair part
(bucket overlap and context). The first layer is linear in the integer features, so the parts add
up exactly to `Fx.dot` of the whole input; `fastScore_agrees` checks it on a sample. -/
structure Scorer where
  w1 : Array (Array Int)
  b1 : Array Int
  w2 : Array (Array Int)
  b2 : Array Int
  width : Nat
  buckets : Nat

def Scorer.of (m : Model) (f : Features) : Scorer :=
  { w1 := m.w1.toArray.map (·.toArray.map (·.raw)), b1 := m.b1.toArray.map (·.raw)
    w2 := m.w2.toArray.map (·.toArray.map (·.raw)), b2 := m.b2.toArray.map (·.raw)
    width := f.width, buckets := f.buckets }

/-- A statement's own features, if the featurizer includes them. -/
def stmtX (f : Features) (s : Statement Addr) : Array Int :=
  if f.statements then (stmtFeatures f.buckets addrKey s).toArray else #[]

def Scorer.part (s : Scorer) (offset : Nat) (x : Array Int) : Array Int :=
  s.w1.map fun row => Id.run do
    let mut acc : Int := 0
    for i in [:x.size] do acc := acc + row[offset + i]! * x[i]!
    return acc

/-- The margin for `true` from precomputed statement and premise parts and the pair's own
features. -/
def Scorer.margin (s : Scorer) (sp pp : Array Int) (px : Array Int) : Int := Id.run do
  let off := 2 * s.width
  let mut h : Array Int := #[]
  for j in [:s.w1.size] do
    let row := s.w1[j]!
    let mut z := sp[j]! + pp[j]! + s.b1[j]!
    for b in [:px.size] do
      let o := px[b]!
      if o != 0 then z := z + row[off + b]! * o
    h := h.push (if z > 0 then z else 0)
  let out := fun (k : Nat) => Id.run do
    let row := s.w2[k]!
    let mut acc : Int := 0
    for j in [:h.size] do acc := acc + row[j]! * h[j]!
    return (acc >>> 8) + s.b2[k]!
  return out 1 - out 0

def pairPart (a b : List Nat) (c : PairContext) : Array Int :=
  ((List.zipWith (fun x y => squash 1 (min x y)) a b) ++ contextFeatures c).toArray

structure Eval where
  /-- Per `k`: hits and gold premises summed over test items. -/
  recall : List (Nat × Nat × Nat)
  /-- Per `k`: the sum over test items of `hits / gold`, in units of `1/1000`. -/
  macroRecall : List (Nat × Nat)
  items : Nat
  candidates : Nat

def evaluate (ks : List Nat) (lib : Library) (items : List (Item Addr))
    (rank : Item Addr → List (Premise Addr) → List Addr) : Eval :=
  let maxK := ks.foldl max 0
  let rows := items.map fun it =>
    let cands := lib.premises.toList.filter fun p => p.addr != it.addr && accessible lib.reach p it.thm
    let ranked := (rank it cands).take maxK
    (ks.map fun k => recallAt k ranked it.premises, cands.length)
  { recall := ks.zipIdx.map fun (k, i) =>
      (k, (rows.map fun r => (getD r.1 i (0, 0)).1).foldl (· + ·) 0,
          (rows.map fun r => (getD r.1 i (0, 0)).2).foldl (· + ·) 0)
    macroRecall := ks.zipIdx.map fun (k, i) =>
      (k, (rows.map fun r => let (h, g) := getD r.1 i (0, 0); if g == 0 then 0 else h * 1000 / g).foldl (· + ·) 0)
    items := rows.length
    candidates := (rows.map (·.2)).foldl (· + ·) 0 }

/-- Rank by how many training items use each premise; ties keep library order. -/
def frequencyRank (prior : Prior) : Item Addr → List (Premise Addr) → List Addr :=
  fun _ cands => topK 10 (cands.map fun p => ((prior.getD p.addr 0 : Int), p.addr))

def modelRank (m : Model) (f : Features) (lib : Library) (prior : Prior) :
    Item Addr → List (Premise Addr) → List Addr :=
  let s := Scorer.of m f
  let cache : Std.HashMap Addr (Array Int × List Nat) := lib.premises.foldl (fun c p =>
    if c.contains p.addr then c else
    c.insert p.addr (s.part s.width (stmtX f p.stmt), constCounts f.buckets addrKey p.stmt)) {}
  fun it cands =>
    let sp := s.part 0 (stmtX f it.thm.stmt)
    let sc := constCounts f.buckets addrKey it.thm.stmt
    topK 10 (cands.map fun p =>
      let (pp, pc) := cache.getD p.addr (#[], [])
      (s.margin sp pp (pairPart sc pc (contextOf lib prior it.thm p)), p.addr))

/-- The split scorer equals `score` of the model on whole pair features. -/
def fastScore_agrees (m : Model) (f : Features) (lib : Library) (prior : Prior)
    (pairs : List (Premise Addr × Premise Addr)) : Bool :=
  let s := Scorer.of m f
  pairs.all fun (t, p) =>
    let c := contextOf lib prior t p
    let px := pairPart (constCounts f.buckets addrKey t.stmt) (constCounts f.buckets addrKey p.stmt) c
    s.margin (s.part 0 (stmtX f t.stmt)) (s.part s.width (stmtX f p.stmt)) px ==
      score m (pairFeatures f addrKey t.stmt p.stmt c)

end IxAIData
