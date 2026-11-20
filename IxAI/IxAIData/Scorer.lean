import IxAIData.Dataset
import IxAIData.Fx16

/-!
# A bilinear premise scorer trained with a pairwise ranking loss

A (statement, premise) pair is scored

  `s(x, p) = φ(x)ᵀ Eₛᵀ Eₚ ψ(p) + wᵀ c(x, p)`

where `φ` and `ψ` are sparse features of the two statements (`sparseFeatures`: alpha-invariant
shape and constant features from addresses, plus hashed tokens of the declaration name), `Eₛ` and
`Eₚ` embed them into `dim` dimensions (a rank-`dim` bilinear form), and `c` are integer features of
the pair (`pairContext`): IDF-weighted constant overlap, head-symbol matches, locality, the
training-set prior, and name-token overlap. All values are `Fx16` raw integers. Names are metadata
beside the content addresses, so the name features change no address.

Training minimises either the pairwise hinge loss `max 0 (margin − s(x, p⁺) + s(x, p⁻))` or the
listwise softmax loss `−log softmax(s)(p⁺)` over each gold premise `p⁺` and the theorem's hard
negatives `p⁻` (accessible premises the proof does not use: the highest by IDF overlap, from the
gold premises' modules, and from all accessible modules). With `residual`, the IDF score's weight
stays fixed and only a residual over it is learned. It is a pure,
deterministic function of the data and `ScorerConfig`: the schedule is fixed, every gradient
entry is an exact sum over the batch, and the learning rate and the batch average are folded into
one rounding (`Fx16.step`). Every value and accumulation is checked against `Bounds`; leaving
them is a `BoundError`.
-/

namespace IxAIData

open IxAI IxAICore

/-! ## Statement features -/

structure FeatureConfig where
  constBuckets : Nat := 512
  headBuckets : Nat := 128
  nameBuckets : Nat := 256
  deriving Repr, DecidableEq

def arityLevels : Nat := 8
def kindLevels : Nat := 3

def FeatureConfig.width (f : FeatureConfig) : Nat :=
  1 + f.constBuckets + 3 * f.headBuckets + 2 * arityLevels + 12 * kindLevels + f.nameBuckets

/-! ## Name tokens -/

/-- 64-bit FNV-1a of the UTF-8 bytes: the fixed hash of name tokens. -/
def fnv1a (s : String) : Nat :=
  s.toUTF8.foldl (fun h b => ((h ^^^ b.toNat) * 1099511628211) % 2 ^ 64) 14695981039346656037

/-- Mathlib names the lemmas about `hAdd`, `hMul`, … after `add`, `mul`, …: drop that `h`. -/
def stripH (s : String) : String :=
  match s.toList with
  | 'h' :: c :: rest => if c.isUpper then String.ofList (c :: rest) else s
  | _ => s

/-- A lowercased token without primes, hashed. -/
def tokenOf (s : String) : Nat := fnv1a (String.ofList ((stripH s).toLower.toList.filter (· ≠ '\'')))

def dedupNat (xs : List Nat) : Array Nat :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- The tokens of a declaration name such as `Mathlib.Order.le_antisymm_iff`. -/
structure NameToks where
  /-- Namespace components, outermost first. -/
  ns : Array Nat
  /-- The `_`-separated tokens of the last component. -/
  last : Array Nat
  /-- Both, without repeats. -/
  all : Array Nat
  deriving Inhabited

/-- Components that are numeric or start with `_` (private and auxiliary names) are skipped. -/
def nameToks (n : String) : NameToks :=
  let comps := (n.splitOn ".").filter fun c =>
    !c.isEmpty && !c.startsWith "_" && !c.all Char.isDigit
  let ns := comps.dropLast.map tokenOf
  let last := match comps.getLast? with
    | some c => ((stripH c).splitOn "_").filter (!·.isEmpty) |>.map tokenOf
    | none => []
  { ns := ns.toArray, last := dedupNat last, all := dedupNat (ns ++ last) }

/-- A sparse feature vector: `(index, value)` with distinct indices. -/
abbrev Sparse := Array (Nat × Int)

/-- Features of one statement, all from content addresses and shape: a bias; constant buckets
(capped at 2 per bucket); the head constants of the conclusion and of its two last arguments, each
in its own bucket space; one-hot binder and hypothesis counts; per node kind, one-hot
`⌊log₂ (n + 1)⌋` capped at 3; the hashed tokens of the declaration name. -/
def sparseFeatures (f : FeatureConfig) (key : Addr → Nat) (s : Statement Addr) (name : Array Nat) :
    Sparse := Id.run do
  let mut d : Array Int := Array.replicate f.width 0
  d := d.set! 0 1
  for (c, _) in s.consts do
    let i := 1 + key c % f.constBuckets
    d := d.set! i (min 2 (d[i]! + 1))
  let headOff := 1 + f.constBuckets
  for (h, slot) in s.heads.zipIdx do
    if let some a := h then
      if slot < 3 then d := d.set! (headOff + slot * f.headBuckets + key a % f.headBuckets) 1
  let arOff := headOff + 3 * f.headBuckets
  d := d.set! (arOff + min s.binders (arityLevels - 1)) 1
  d := d.set! (arOff + arityLevels + min s.hyps (arityLevels - 1)) 1
  let kOff := arOff + 2 * arityLevels
  for (n, k) in (s.kinds.take 12).zipIdx do
    let lvl := min (Nat.log2 (n + 1)) kindLevels
    if lvl > 0 then d := d.set! (kOff + k * kindLevels + (lvl - 1)) 1
  let nOff := kOff + 12 * kindLevels
  if f.nameBuckets > 0 then
    for h in name do d := d.set! (nOff + h % f.nameBuckets) 1
  let mut out : Sparse := #[]
  for i in [:d.size] do
    if d[i]! != 0 then out := out.push (i, d[i]!)
  return out

/-! ## Pair features -/

/-- Inverse document frequency in quarter bits: `⌊log₂ ((n/df)⁴)⌋ = ⌊4 log₂ (n/df)⌋`. -/
def idfQ (n df : Nat) : Nat := Nat.log2 (n ^ 4 / (max df 1) ^ 4)

/-- What the pair features need of a statement, computed once per library theorem. -/
structure Prepared where
  premise : Premise Addr
  x : Sparse
  /-- `x` without the name-token buckets. -/
  xAddr : Sparse
  consts : Array Addr
  idf : Array Nat
  /-- `Σ idf` over the statement's constants. -/
  mass : Nat
  constSet : Std.HashSet Addr
  heads : Array (Option Addr)
  name : NameToks
  nameSet : Std.HashSet Nat
  /-- The name's tokens and the tokens of the names of the statement's constants. -/
  ctxSet : Std.HashSet Nat
  /-- The IDF of each of `name.all` over library names, in quarter bits. -/
  nameIdf : Array Nat
  nameMass : Nat
  deriving Inhabited

/-- `tokDf`: per token, how many library names contain it. -/
def prepare (f : FeatureConfig) (lib : Library) (tokDf : Std.HashMap Nat Nat) (name : NameToks)
    (p : Premise Addr) (constToks : Addr → Option (Array Nat) := fun c => (lib.constNames.get? c).map fun n => (nameToks n).all) :
    Prepared :=
  let n := lib.premises.size
  let consts := (p.stmt.consts.map (·.1)).toArray
  let idf := consts.map fun c => idfQ n (lib.docFreq.getD c 0)
  let nameSet : Std.HashSet Nat := name.all.foldl (·.insert ·) {}
  let nameIdf := name.all.map fun h => idfQ n (tokDf.getD h 0)
  { premise := p, x := sparseFeatures f addrKey p.stmt name.all
    xAddr := sparseFeatures f addrKey p.stmt #[], consts, idf
    mass := idf.foldl (· + ·) 0
    constSet := consts.foldl (·.insert ·) {}
    heads := p.stmt.heads.toArray
    name, nameSet
    ctxSet := consts.foldl (fun s c => match constToks c with
      | some ts => ts.foldl (·.insert ·) s
      | none => s) nameSet
    nameIdf, nameMass := nameIdf.foldl (· + ·) 0 }

def numContext : Nat := 35

/-- The pair feature holding `idfScore / 64`. -/
def idfFeature : Nat := 16

/-- The pair feature holding `nameScore / 64`. -/
def nameFeature : Nat := 24

def capLog (cap n : Nat) : Int := Int.ofNat (min (Nat.log2 (n + 1)) cap)

/-- The IDF baseline: IDF-weighted overlap, as the share of the premise's IDF mass the theorem
covers plus the overlap itself, so specific premises fully covered by the theorem rank first. -/
def idfScore (t p : Prepared) : Int := Id.run do
  let mut overlap := 0
  for i in [:p.consts.size] do
    if t.constSet.contains p.consts[i]! then overlap := overlap + p.idf[i]!
  return Int.ofNat (1024 * overlap / (p.mass + 1) + overlap)

/-- The name analogue of `idfScore`: the IDF-weighted share of the premise's name tokens found
among the theorem's name tokens and the names of its statement's constants, plus that overlap. -/
def nameScore (t p : Prepared) : Int := Id.run do
  let mut overlap := 0
  for i in [:p.name.all.size] do
    if t.ctxSet.contains p.name.all[i]! then overlap := overlap + p.nameIdf[i]!
  return Int.ofNat (1024 * overlap / (p.nameMass + 1) + overlap)

/-- Name features of a pair: shared name tokens (log count, and Jaccard in sixteenths), the
length of the shared namespace prefix, the IDF-weighted overlap of the premise's name with the
theorem's name and constants (absolute, and as a share of the premise's name mass), whether the
premise's last component is covered by the theorem's name, or by its name and constants, and
`nameScore / 64`. -/
def nameContext (t p : Prepared) : Array Int := Id.run do
  let mut shared := 0
  for h in p.name.all do
    if t.nameSet.contains h then shared := shared + 1
  let union := t.name.all.size + p.name.all.size - shared
  let mut pfx := 0
  for i in [:min t.name.ns.size p.name.ns.size] do
    if pfx == i && t.name.ns[i]! == p.name.ns[i]! then pfx := pfx + 1
  let mut overlap := 0
  for i in [:p.name.all.size] do
    if t.ctxSet.contains p.name.all[i]! then overlap := overlap + p.nameIdf[i]!
  let lastIn := fun (s : Std.HashSet Nat) =>
    if !p.name.last.isEmpty && p.name.last.all s.contains then (1 : Int) else 0
  return #[capLog 3 shared, Int.ofNat (16 * shared / max union 1), Int.ofNat (min pfx 4),
    Int.ofNat (overlap / 16), Int.ofNat (16 * overlap / (p.nameMass + 1)),
    lastIn t.nameSet, lastIn t.ctxSet, nameScore t p / 64]

/-! ## Training-set statistics -/

/-- Which training proofs a training theorem's statistics (prior and neighbour votes) leave out,
so that training sees statistics like those of a held-out theorem. -/
inductive LeaveOut where
  /-- Its own proof only. -/
  | self
  /-- Every proof of its module: a held-out module has no training theorems. -/
  | module
  /-- Its own proof and those declared after it in its module: held-out theorems are the latest
  of their modules. -/
  | later
  deriving Repr, DecidableEq

/-- Does `r`'s proof count in the statistics of training theorem `t`? -/
def LeaveOut.keeps (lo : LeaveOut) (t r : Premise Addr) : Bool :=
  r.addr != t.addr && match lo with
    | .self => true
    | .module => r.module != t.module
    | .later => r.module != t.module || r.decl < t.decl

/-- One theorem's view of the training proofs. -/
structure ThmStats where
  /-- Per premise, uses by left-out training proofs, subtracted from the prior. -/
  sub : Std.HashMap Addr Nat := {}
  /-- Per premise, the summed similarity of the nearest training theorems whose proofs use it. -/
  votes : Std.HashMap Addr Nat := {}
  /-- Per premise, how many of those neighbours use it. -/
  count : Std.HashMap Addr Nat := {}
  /-- The largest vote. -/
  vmax : Nat := 0
  /-- Per premise, how often kept training proofs use it together with one of the theorem's
  context premises (its IDF top candidates), the premise itself not counted. -/
  co : Std.HashMap Addr Nat := {}
  deriving Inhabited

/-- The training-set prior and every theorem's view of it. -/
structure Stats where
  prior : Prior
  thm : Std.HashMap Addr ThmStats := {}
  deriving Inhabited

/-- Similarity of two statements in `1/1024`: the IDF-weighted Jaccard index of their constants
plus that of their name tokens. Symmetric, as each constant and token has one IDF. -/
def similarity (t r : Prepared) : Nat := Id.run do
  let mut ov := 0
  for i in [:r.consts.size] do
    if t.constSet.contains r.consts[i]! then ov := ov + r.idf[i]!
  let mut ovn := 0
  for i in [:r.name.all.size] do
    if t.nameSet.contains r.name.all[i]! then ovn := ovn + r.nameIdf[i]!
  return 1024 * ov / (t.mass + r.mass - ov + 1) + 1024 * ovn / (t.nameMass + r.nameMass - ovn + 1)

/-- Training proofs with the indices `thmStats` looks them up by, so that its cost grows with
the postings it touches rather than with the training set. -/
structure Refs where
  refs : Array (Prepared × List Addr)
  /-- Per module, its references. -/
  byModule : Std.HashMap Nat (Array Nat) := {}
  /-- Per constant and per name token, the references whose statements mention it. -/
  byConst : Std.HashMap Addr (Array Nat) := {}
  byToken : Std.HashMap Nat (Array Nat) := {}
  /-- Per premise, the references whose proofs use it. -/
  byPremise : Std.HashMap Addr (Array Nat) := {}

/-- Postings accumulate as lists in reverse, since pushing onto an array still held by the map
would copy it. -/
def pushAt {κ : Type} [BEq κ] [Hashable κ] (m : Std.HashMap κ (List Nat)) (k : κ) (i : Nat) :
    Std.HashMap κ (List Nat) :=
  m.insert k (i :: m.getD k [])

def postings {κ : Type} [BEq κ] [Hashable κ] (m : Std.HashMap κ (List Nat)) : Std.HashMap κ (Array Nat) :=
  m.map fun _ l => l.reverse.toArray

def Refs.of (refs : Array (Prepared × List Addr)) : Refs := Id.run do
  let mut byModule : Std.HashMap Nat (List Nat) := {}
  let mut byConst : Std.HashMap Addr (List Nat) := {}
  let mut byToken : Std.HashMap Nat (List Nat) := {}
  let mut byPremise : Std.HashMap Addr (List Nat) := {}
  for i in [:refs.size] do
    let (r, ps) := refs[i]!
    byModule := pushAt byModule r.premise.module i
    for c in r.consts do byConst := pushAt byConst c i
    for h in r.name.all do byToken := pushAt byToken h i
    for a in dedupNat' ps do byPremise := pushAt byPremise a i
  return { refs, byModule := postings byModule, byConst := postings byConst
           byToken := postings byToken, byPremise := postings byPremise }
where
  /-- The first occurrence of each address, in order. -/
  dedupNat' (xs : List Addr) : Array Addr :=
    (xs.foldl (fun (seen, acc) x => if seen.contains x then (seen, acc) else (seen.insert x, acc.push x))
      (({} : Std.HashSet Addr), (#[] : Array Addr))).2

/-- Constants and name tokens mentioned by more references than this do not propose neighbours. -/
def postingCap : Nat := 4096

/-- `t`'s view of the reference proofs, keeping those `keep` admits (`keep` drops at most `t`'s
own proof and proofs of `t`'s module): the prior's left-out uses; the votes of its `k` most similar
kept references among those sharing a constant or name token with it outside postings longer
than `cap` (ties by index; similarity 0 never votes); and co-usage with `ctx`. -/
def thmStats (k : Nat) (keep : Premise Addr → Bool) (t : Prepared) (R : Refs)
    (ctx : Array Addr := #[]) (cap : Nat := postingCap) : ThmStats := Id.run do
  let refs := R.refs
  let mut sub : Std.HashMap Addr Nat := {}
  let mut dropped : Std.HashSet Nat := {}
  for i in R.byModule.getD t.premise.module #[] do
    let (r, ps) := refs[i]!
    if !keep r.premise then
      dropped := dropped.insert i
      for a in ps do sub := sub.insert a (sub.getD a 0 + 1)
  let mut co : Std.HashMap Addr Nat := {}
  if !ctx.isEmpty then
    let mut n : Std.HashMap Nat Nat := {}
    for q in ctx do
      for i in R.byPremise.getD q #[] do
        if !dropped.contains i then n := n.insert i (n.getD i 0 + 1)
    for (i, c) in n.toArray.qsort (fun a b => a.1 < b.1) do
      for a in refs[i]!.2 do
        let d := c - (if ctx.contains a then 1 else 0)
        if d > 0 then co := co.insert a (co.getD a 0 + d)
  let mut sims : Array (Int × Nat) := #[]
  if k > 0 then
    let mut touched : Std.HashSet Nat := {}
    for c in t.consts do
      let ps := R.byConst.getD c #[]
      if ps.size ≤ cap then touched := ps.foldl (·.insert ·) touched
    for h in t.name.all do
      let ps := R.byToken.getD h #[]
      if ps.size ≤ cap then touched := ps.foldl (·.insert ·) touched
    for i in touched.toArray.qsort (· < ·) do
      let r := refs[i]!.1
      if !dropped.contains i && keep r.premise then
        let s := similarity t r
        if s > 0 then sims := sims.push (Int.ofNat s, i)
  let top := (sims.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)).extract 0 k
  let mut votes : Std.HashMap Addr Nat := {}
  let mut count : Std.HashMap Addr Nat := {}
  for (s, i) in top do
    for a in refs[i]!.2 do
      votes := votes.insert a (votes.getD a 0 + s.toNat)
      count := count.insert a (count.getD a 0 + 1)
  return { sub, votes, count, vmax := votes.fold (fun m _ v => max m v) 0, co }

/-! ## Pair context -/

/-- Integer features relating a theorem `t` to a candidate premise `p`, given `t`'s view of the
training proofs `ts`: for a training theorem, its left-out uses are subtracted from the prior (at
least its own proof, which uses every gold premise), so training sees the prior a held-out theorem
would. -/
def pairContext (st : Stats) (ts : ThmStats) (t p : Prepared) : Array Int := Id.run do
  let mut shared := 0
  let mut sharedRare := 0
  let mut overlap := 0
  for i in [:p.consts.size] do
    if t.constSet.contains p.consts[i]! then
      shared := shared + 1
      overlap := overlap + p.idf[i]!
      if p.idf[i]! ≥ 4 * 7 then sharedRare := sharedRare + 1
  let head := fun (s : Prepared) (k : Nat) => (s.heads[k]?).bind id
  let inT := fun (a? : Option Addr) => match a? with
    | some a => if t.constSet.contains a then (1 : Int) else 0
    | none => 0
  let same := p.premise.module == t.premise.module
  let dist := t.premise.decl - p.premise.decl
  let a := p.premise.addr
  let pr := st.prior.getD a 0 - ts.sub.getD a 0
  let votes := ts.votes.getD a 0
  let eqSome := fun (x y : Option Addr) => if x != none && x == y then (1 : Int) else 0
  let tHeadInP : Int := match head t 0 with
    | some h => if p.constSet.contains h then 1 else 0
    | none => 0
  return #[capLog 7 shared, capLog 7 sharedRare, Int.ofNat (overlap / 16),
    Int.ofNat (16 * overlap / (p.mass + 1)), Int.ofNat (16 * overlap / (t.mass + 1)),
    eqSome (head p 0) (head t 0),
    inT (head p 0), inT (head p 1), inT (head p 2),
    if same then 1 else 0, if same && dist ≤ 4 then 1 else 0, if same && dist ≤ 16 then 1 else 0,
    if same && dist ≤ 64 then 1 else 0, capLog 7 pr, if pr > 0 then 1 else 0,
    capLog 7 p.consts.size, idfScore t p / 64] ++ nameContext t p ++
    #[capLog 15 votes, Int.ofNat (16 * votes / (ts.vmax + 1)), capLog 4 (ts.count.getD a 0),
      if votes > 0 && votes == ts.vmax then 1 else 0,
      eqSome (head p 1) (head t 1) + eqSome (head p 2) (head t 2),
      max (eqSome (head p 0) (head t 1)) (eqSome (head p 0) (head t 2)),
      Int.ofNat (min p.premise.stmt.hyps 3), tHeadInP,
      capLog 7 (ts.co.getD a 0), if ts.co.getD a 0 > 0 then 1 else 0]

/-! ## The model -/

inductive Loss where
  /-- `max 0 (margin − s(x, p⁺) + s(x, p⁻))` per (gold, negative) pair. -/
  | hinge
  /-- `−log softmax(s)(p⁺)` over each gold premise and the theorem's negatives. -/
  | softmax
  deriving Repr, DecidableEq

structure ScorerConfig where
  features : FeatureConfig := {}
  seed : Nat := 1
  dim : Nat := 16
  /-- Learning rate `lrRaw / 2^16` per triple; the batch average is folded in by `Fx16.step`. -/
  lrRaw : Int := 4096
  epochs : Nat := 8
  /-- Training theorems per batch; a batch's gradient averages over all its triples. -/
  itemsPerBatch : Nat := 4
  marginRaw : Int := 65536
  /-- Initial embeddings are uniform in `[-initRaw, initRaw]`. -/
  initRaw : Nat := 4096
  /-- Hard negatives per theorem: highest IDF overlap, from the gold premises' modules, random. -/
  negIdf : Nat := 8
  negModule : Nat := 4
  negRandom : Nat := 8
  /-- Initial weight of the IDF pair feature, so training starts from the IDF ranking. -/
  idfInitRaw : Int := 65536
  /-- Initial weight of the `nameScore` pair feature. -/
  nameInitRaw : Int := 0
  /-- Keep the IDF feature's weight at `idfInitRaw` and learn only a residual over it. -/
  residual : Bool := false
  loss : Loss := .hinge
  /-- Include the name-token buckets in the statement features `φ` and `ψ`. -/
  nameTower : Bool := true
  /-- Neighbours that vote for their proofs' premises (0: no votes). -/
  knn : Nat := 0
  /-- Context premises for co-usage: the theorem's IDF top candidates (0: no co-usage). -/
  coUse : Nat := 0
  /-- What a training theorem's statistics leave out. -/
  leaveOut : LeaveOut := .self
  /-- Decay the learning rate linearly to 0 over the run. -/
  decay : Bool := false
  /-- Round each update to nearest rather than toward negative infinity. -/
  nearest : Bool := false
  /-- Models in the ensemble, trained with seeds `seed + 1000 i`; their scores are summed. -/
  ensemble : Nat := 1
  /-- Pair features held at 0. -/
  dropContext : List Nat := []
  /-- Postings longer than this propose no neighbours (`thmStats`). -/
  postingCap : Nat := postingCap
  bounds : Bounds := Bounds.standard
  deriving Repr

def Prepared.feats (c : ScorerConfig) (p : Prepared) : Sparse := if c.nameTower then p.x else p.xAddr

/-- `pairContext` with `dropContext` held at 0. -/
def ScorerConfig.context (c : ScorerConfig) (st : Stats) (ts : ThmStats) (t p : Prepared) : Array Int :=
  let cx := pairContext st ts t p
  c.dropContext.foldl (fun cx k => cx.set! k 0) cx

structure ScorerModel where
  dim : Nat
  width : Nat
  /-- `width × dim`, row-major: the statement embedding `Eₛ`. -/
  es : Array Int
  /-- `width × dim`: the premise embedding `Eₚ`. -/
  ep : Array Int
  /-- `numContext` weights of the pair features. -/
  wc : Array Int
  deriving Inhabited

def ScorerModel.init (c : ScorerConfig) : ScorerModel :=
  let w := c.features.width
  let n := w * c.dim
  let (vs, _) := (Rng.seeded (c.seed + 3)).draws (2 * c.initRaw + 1) (2 * n)
  let vs := vs.toArray.map fun v => Int.ofNat v - Int.ofNat c.initRaw
  { dim := c.dim, width := w, es := vs.extract 0 n, ep := vs.extract n (2 * n)
    wc := ((Array.replicate numContext 0).set! idfFeature c.idfInitRaw).set! nameFeature c.nameInitRaw }

/-- `Eᵀ x` for a sparse `x`: exact, with its accumulation checked. -/
def embed (b : Bounds) (dim : Nat) (e : Array Int) (x : Sparse) : Except BoundError (Array Int) := do
  let mut u := Array.replicate dim (0 : Int)
  let mut a := Array.replicate dim (0 : Nat)
  for (f, v) in x do
    for i in [:dim] do
      let t := v * e[f * dim + i]!
      u := u.set! i (u[i]! + t)
      a := a.set! i (a[i]! + t.natAbs)
  for i in [:dim] do
    b.checkAcc "embedding" a[i]!
    b.checkValue "embedding" u[i]!
  return u

/-- `s = uᵀv` (rounded once) `+ wᵀc`, raw. -/
def scoreRaw (b : Bounds) (m : ScorerModel) (u v : Array Int) (c : Array Int) :
    Except BoundError Int := do
  let mut d : Int := 0
  let mut a : Nat := 0
  for i in [:m.dim] do
    let t := u[i]! * v[i]!
    d := d + t
    a := a + t.natAbs
  b.checkAcc "score" a
  let mut s : Int := d >>> 16
  let mut a2 : Nat := s.natAbs
  for k in [:c.size] do
    let t := c[k]! * m.wc[k]!
    s := s + t
    a2 := a2 + t.natAbs
  b.checkAcc "score" a2
  b.checkValue "score" s
  return s

/-! ## Training -/

/-- One training theorem: its index, and the indices of its gold premises and hard negatives, all
into the prepared library. -/
structure Group where
  thm : Nat
  pos : Array Nat
  neg : Array Nat

/-- An exact gradient accumulator with the absolute sum of each entry's terms. -/
structure Grad where
  g : Array Int
  a : Array Nat

def Grad.zero (n : Nat) : Grad := ⟨Array.replicate n 0, Array.replicate n 0⟩

def Grad.add (gr : Grad) (i : Nat) (t : Int) : Grad :=
  ⟨gr.g.modify i (· + t), gr.a.modify i (· + t.natAbs)⟩

/-- Add `sign · x ⊗ y` to a `width × dim` gradient. -/
def Grad.outer (gr : Grad) (dim : Nat) (sign : Int) (x : Sparse) (y : Array Int) : Grad := Id.run do
  let mut gr := gr
  for (f, v) in x do
    for i in [:dim] do
      gr := gr.add (f * dim + i) (sign * v * y[i]!)
  return gr

/-- Apply `Fx16.step` to every weight, or with `nearest` the same update rounded to nearest (half
up), checking the accumulations and the new values. Rounding toward negative infinity moves every
updated weight up by half a unit on average. -/
def applyGrad (b : Bounds) (lrRaw : Int) (n : Nat) (what : String) (w : Array Int) (gr : Grad)
    (nearest : Bool := false) : Except BoundError (Array Int) := do
  let mut w := w
  let den : Int := 65536 * (max n 1 : Nat)
  for i in [:w.size] do
    let g := gr.g[i]!
    if g != 0 then
      b.checkAcc what gr.a[i]!
      b.checkAcc what ((if nearest then 2 else 1) * lrRaw * g).natAbs
      let nw := if nearest then w[i]! - (2 * lrRaw * g + den) / (2 * den)
        else (Fx16.step lrRaw n ⟨w[i]!⟩ ⟨g⟩).raw
      b.checkValue what nw
      w := w.set! i nw
  return w

/-- `2^(−y)` for `y = yRaw / 2^16`, in Fx16: a cubic on the fractional part (absolute error below
`1.5·10⁻⁴`), shifted by the integer part. -/
def exp2Neg (yRaw : Nat) : Int :=
  let k := yRaw / 65536
  if k ≥ 17 then 0 else
  let f : Int := Int.ofNat (yRaw % 65536)
  (65536 + ((-45340) * f >>> 16) + (15212 * f * f >>> 32) + ((-2647) * f * f * f >>> 48)) >>> k

/-- `softmax` of raw scores, in Fx16: `e^(s − max)` through `exp2Neg`, normalised by one
division each. The largest score's term is exactly 1, so the sum is at least 1. -/
def softmaxRaw (ss : Array Int) : Array Int :=
  let m := ss.foldl max (ss[0]?.getD 0)
  let es := ss.map fun s => exp2Neg ((m - s) * 94548 >>> 16).toNat
  let z := es.foldl (· + ·) 0
  es.map fun e => e * 65536 / max z 1

/-- One step over a batch of groups, averaged by the folded learning rate. Hinge: the gradient of
every violating (gold, negative) triple, averaged over the batch's triples. Softmax: per gold
premise, `Σⱼ (qⱼ − yⱼ) ∇sⱼ` over the gold premise and the theorem's negatives, each product of a
probability and an activation rounded once, averaged over the batch's gold premises. All sums are
exact. -/
def step (c : ScorerConfig) (prep : Array Prepared) (st : Stats) (lrRaw : Int) (m : ScorerModel)
    (batch : List Group) : Except BoundError ScorerModel := do
  let b := c.bounds
  let n := m.width * m.dim
  let mut ges := Grad.zero n
  let mut gep := Grad.zero n
  let mut gwc := Grad.zero numContext
  let mut triples := 0
  for grp in batch do
    let t := prep[grp.thm]!
    let ts := st.thm.getD t.premise.addr {}
    let u ← embed b m.dim m.es (t.feats c)
    let negs ← grp.neg.mapM fun j => do
      let p := prep[j]!
      let v ← embed b m.dim m.ep (p.feats c)
      let cx := c.context st ts t p
      return (p, v, cx, ← scoreRaw b m u v cx)
    for j in grp.pos do
      let p := prep[j]!
      let vp ← embed b m.dim m.ep (p.feats c)
      let cp := c.context st ts t p
      let sp ← scoreRaw b m u vp cp
      match c.loss with
      | .hinge =>
        for (q, vn, cn, sn) in negs do
          triples := triples + 1
          if c.marginRaw - sp + sn > 0 then
            ges := ges.outer m.dim 1 (t.feats c) (Array.zipWith (· - ·) vn vp)
            gep := gep.outer m.dim 1 (q.feats c) u
            gep := gep.outer m.dim (-1) (p.feats c) u
            for k in [:numContext] do
              gwc := gwc.add k ((cn[k]! - cp[k]!) * Fx16.scale)
      | .softmax =>
        if negs.isEmpty then continue
        triples := triples + 1
        let list := #[(p, vp, cp, sp)] ++ negs
        let q := softmaxRaw (list.map fun (_, _, _, s) => s)
        let mut vsum := Array.replicate m.dim (0 : Int)
        let mut vabs := Array.replicate m.dim (0 : Nat)
        for i in [:list.size] do
          let (r, v, cx, _) := list[i]!
          let w := q[i]! - (if i == 0 then Fx16.scale else 0)
          if w != 0 then
            for d in [:m.dim] do
              let y := (w * v[d]!) >>> 16
              vsum := vsum.set! d (vsum[d]! + y)
              vabs := vabs.set! d (vabs[d]! + y.natAbs)
            gep := gep.outer m.dim 1 (r.feats c) (u.map fun x => (w * x) >>> 16)
            for k in [:numContext] do
              gwc := gwc.add k (w * cx[k]!)
        for d in [:m.dim] do
          b.checkAcc "softmax gradient" vabs[d]!
          b.checkValue "softmax gradient" vsum[d]!
        ges := ges.outer m.dim 1 (t.feats c) vsum
  if triples == 0 then return m
  if c.residual then gwc := { gwc with g := gwc.g.set! idfFeature 0 }
  return { m with es := ← applyGrad b lrRaw triples "statement embedding" m.es ges c.nearest
                  ep := ← applyGrad b lrRaw triples "premise embedding" m.ep gep c.nearest
                  wc := ← applyGrad b lrRaw triples "pair weights" m.wc gwc c.nearest }

/-! `shuffle` (`IxAICore.Rng`) swaps list positions, quadratic in the length; `shuffleArr` makes
the same swaps in an array (`shuffleArr_eq`). -/

theorem setAt_eq_set {α : Type} (l : List α) (i : Nat) (v : α) : setAt l i v = l.set i v := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a as ih => cases i with
    | zero => rfl
    | succ i => simp [setAt, ih]

/-- `shuffleAux` on an array: the same swaps, each in place. -/
def shuffleArrAux {α : Type} [Inhabited α] : Nat → Array α → Rng → Array α × Rng
  | 0, a, r => (a, r)
  | i + 1, a, r =>
    let (j, r) := r.below (i + 2)
    let x := a[i + 1]?.getD default
    let y := a[j]?.getD default
    shuffleArrAux i ((a.setIfInBounds (i + 1) y).setIfInBounds j x) r

theorem shuffleArrAux_eq {α : Type} [Inhabited α] (i : Nat) :
    ∀ (a : Array α) (r : Rng),
      shuffleAux i a.toList r = ((shuffleArrAux i a r).1.toList, (shuffleArrAux i a r).2) := by
  induction i with
  | zero => intro a r; rfl
  | succ i ih =>
    intro a r
    simp only [shuffleArrAux, shuffleAux]
    generalize r.below (i + 2) = p
    obtain ⟨j, r'⟩ := p
    have key : setAt (setAt a.toList (i + 1) ((List.drop j a.toList).headD default)) j
        ((List.drop (i + 1) a.toList).headD default) =
        ((a.setIfInBounds (i + 1) (a[j]?.getD default)).setIfInBounds j (a[i + 1]?.getD default)).toList := by
      simp [setAt_eq_set, List.head?_drop, Array.toList_setIfInBounds, List.headD_eq_head?_getD]
    simp only [key, ih]

/-- `shuffle` through an array. -/
def shuffleArr {α : Type} [Inhabited α] (l : List α) (r : Rng) : List α × Rng :=
  let (a, r) := shuffleArrAux (l.length - 1) l.toArray r
  (a.toList, r)

theorem shuffleArr_eq {α : Type} [Inhabited α] (l : List α) (r : Rng) : shuffleArr l r = shuffle l r := by
  have h := shuffleArrAux_eq (l.length - 1) l.toArray r
  simp only [shuffleArr, shuffle, h]

/-- Every epoch is a fresh shuffle of the groups, cut into batches. -/
def schedule (c : ScorerConfig) (groups : Nat) : List (List Nat) :=
  let rec go : Nat → Rng → List (List Nat)
    | 0, _ => []
    | e + 1, r =>
      let (perm, r) := shuffleArr (List.range groups) r
      chunk (max c.itemsPerBatch 1) perm groups ++ go e r
  go c.epochs (Rng.seeded (c.seed + 7))

/-- The learning rate of step `s` of `total`: constant, or with `decay` falling linearly from
`lrRaw` to `lrRaw / total`. -/
def ScorerConfig.lrAt (c : ScorerConfig) (s total : Nat) : Int :=
  if c.decay then c.lrRaw * Int.ofNat (total - s) / Int.ofNat (max total 1) else c.lrRaw

/-- The specified result of training on the given groups. -/
def trainScorer (c : ScorerConfig) (prep : Array Prepared) (st : Stats) (groups : Array Group) :
    Except BoundError ScorerModel :=
  let sched := schedule c groups.size
  sched.zipIdx.foldlM (fun m (idx, s) => step c prep st (c.lrAt s sched.length) m
    (idx.filterMap (groups[·]?))) (ScorerModel.init c)

/-! ## Data: groups with hard negatives -/

/-- The prepared library with an index per address (the first theorem of that address). -/
structure PreparedLib where
  lib : Library
  prep : Array Prepared
  index : Std.HashMap Addr Nat
  /-- Every library index of each address. -/
  indices : Std.HashMap Addr (Array Nat) := {}
  /-- Whether the library lists each module's theorems contiguously, in module order; then module
  `m`'s theorems are the indices `[modLo[m], modHi[m])`. -/
  contiguous : Bool := false
  modLo : Array Nat := #[]
  modHi : Array Nat := #[]
  /-- Whether consecutive theorems of the same module have non-decreasing `decl`; then the
  theorems of a contiguous module declared before a given one form a prefix of its range. -/
  declSorted : Bool := false

def PreparedLib.of (f : FeatureConfig) (lib : Library) : PreparedLib :=
  let toks := lib.names.map nameToks
  let tokDf : Std.HashMap Nat Nat := toks.foldl (fun m t =>
    t.all.foldl (fun m h => m.insert h (m.getD h 0 + 1)) m) {}
  let n := lib.byModule.size
  let ps := lib.premises
  let sorted := (List.range (ps.size - 1)).all fun i => ps[i]!.module ≤ ps[i + 1]!.module
  let (lo, hi) := ps.zipIdx.foldl (fun (lo, hi) (p, i) =>
    (if lo[p.module]! > i then lo.set! p.module i else lo, hi.set! p.module (i + 1)))
    (Array.replicate n ps.size, Array.replicate n 0)
  let constToks : Std.HashMap Addr (Array Nat) := lib.docFreq.fold (fun m c _ =>
    match lib.constNames.get? c with
    | some cn => m.insert c (nameToks cn).all
    | none => m) {}
  { lib, prep := (lib.premises.zip toks).map fun (p, t) => prepare f lib tokDf t p constToks.get?
    index := lib.premises.zipIdx.foldl (fun m (p, i) => if m.contains p.addr then m else m.insert p.addr i) {}
    indices := postings (lib.premises.zipIdx.foldl (fun m (p, i) => pushAt m p.addr i) {})
    contiguous := sorted && ps.all (·.module < n), modLo := lo, modHi := hi
    declSorted := (List.range (ps.size - 1)).all fun i =>
      ps[i]!.module != ps[i + 1]!.module || ps[i]!.decl ≤ ps[i + 1]!.decl }

/-- Candidates for a theorem: accessible library theorems other than itself, in library order. -/
def candidates (pl : PreparedLib) (it : Item Addr) : Array Nat :=
  (Array.range pl.prep.size).filter fun j =>
    let p := pl.prep[j]!.premise
    p.addr != it.addr && accessible pl.lib.reach p it.thm

/-- Sort indices by descending score; ties keep the earlier index first. -/
def rankBy (scores : Array (Int × Nat)) : Array Nat :=
  (scores.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)).map (·.2)

/-! ## Candidate pools -/

/-- How many elements of the sorted array `xs` are below `x`. -/
def countBelow (xs : Array Nat) (x : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := xs.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if xs[mid]! < x then lo := mid + 1 else hi := mid
  return lo

/-- Whether the ascending array `xs` contains `x`. -/
def sortedContains (xs : Array Nat) (x : Nat) : Bool :=
  let k := countBelow xs x
  k < xs.size && xs[k]! == x

/-- An ascending array without repeated elements. -/
def dedupSorted (xs : Array Nat) : Array Nat :=
  xs.foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- The least `j` in `[lo, hi)` with `p j`, or `hi`; `p` must be monotone on that range. -/
def firstWith (lo hi : Nat) (p : Nat → Bool) : Nat := Id.run do
  let mut lo := lo
  let mut hi := hi
  while lo < hi do
    let mid := (lo + hi) / 2
    if p mid then hi := mid else lo := mid + 1
  return lo

/-- The candidates of a module's theorems from other modules: the index ranges `[lo[i], hi[i])`
of its imported modules, ascending, with `pre[i]` the number of indices in ranges before `i`. -/
structure ImportRanges where
  lo : Array Nat
  hi : Array Nat
  pre : Array Nat
  deriving Inhabited

def ImportRanges.of (pl : PreparedLib) (m : Nat) : ImportRanges := Id.run do
  let mut out : ImportRanges := { lo := #[], hi := #[], pre := #[0] }
  for k in pl.lib.ancestors[m]! do
    if k != m && pl.modLo[k]! < pl.modHi[k]! then
      out := { lo := out.lo.push pl.modLo[k]!, hi := out.hi.push pl.modHi[k]!
               pre := out.pre.push (out.pre.back! + pl.modHi[k]! - pl.modLo[k]!) }
  return out

/-- Indices of the ranges below `x`. -/
def ImportRanges.below (r : ImportRanges) (x : Nat) : Nat :=
  let k := countBelow r.lo x
  if k == 0 then 0 else r.pre[k - 1]! + min r.hi[k - 1]! x - r.lo[k - 1]!

def ImportRanges.contains (r : ImportRanges) (x : Nat) : Bool :=
  let k := countBelow r.lo (x + 1)
  k > 0 && x < r.hi[k - 1]!

/-- A theorem's candidates without materialising them: the import ranges, the earlier theorems
of its own module (`own`, ascending), less the excluded indices (`excl`, ascending, each among
the others). Element `i` in ascending order is `get i`. -/
structure Pool where
  ranges : ImportRanges
  own : Array Nat
  excl : Array Nat

def Pool.size (p : Pool) : Nat := p.ranges.pre.back! + p.own.size - p.excl.size

/-- Members below `x`. -/
def Pool.below (p : Pool) (x : Nat) : Nat :=
  p.ranges.below x + countBelow p.own x - countBelow p.excl x

/-- The `i`-th member: the least `x` with more than `i` members below `x + 1`. -/
def Pool.get (p : Pool) (n i : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := n
  while lo < hi do
    let mid := (lo + hi) / 2
    if p.below (mid + 1) > i then hi := mid else lo := mid + 1
  return lo

/-- `it`'s candidates (`candidates`) without the theorems whose address is in `drop`. Needs a
contiguous library; `ranges` are those of `it`'s module. -/
def Pool.of (pl : PreparedLib) (ranges : ImportRanges) (it : Item Addr) (drop : List Addr) : Pool :=
  let m := it.thm.module
  let lo := pl.modLo[m]!
  let hi := pl.modHi[m]!
  let own := if pl.declSorted then Array.range' lo (firstWith lo hi (fun j => pl.prep[j]!.premise.decl ≥ it.thm.decl) - lo)
    else (Array.range' lo (hi - lo)).filter fun j => pl.prep[j]!.premise.decl < it.thm.decl
  let excl := ((it.addr :: drop).flatMap fun a => (pl.indices.getD a #[]).toList).toArray.filter fun j =>
    ranges.contains j || sortedContains own j
  { ranges, own, excl := dedupSorted (excl.qsort (· < ·)) }

def Pool.toArray (p : Pool) (n : Nat) : Array Nat := (Array.range p.size).map (p.get n)

/-- The members in the given modules, ascending. -/
def Pool.inModules (pl : PreparedLib) (p : Pool) (thmModule : Nat) (mods : Array Nat) : Array Nat :=
  let ms := (dedupNat mods.toList).qsort (· < ·)
  (ms.flatMap fun m =>
    if m == thmModule then p.own
    else if p.ranges.contains pl.modLo[m]! then Array.range' pl.modLo[m]! (pl.modHi[m]! - pl.modLo[m]!)
    else #[]).filter fun j => !sortedContains p.excl j

/-- `f` on every element, in at most `chunks` chunks (and no more than there are elements) run as
parallel tasks; the result is `xs.map f`. -/
def parMap {α β : Type} [Inhabited β] (xs : Array α) (f : α → β) (chunks : Nat := 96) : Array β :=
  let chunks := max 1 (min chunks xs.size)
  let size := xs.size / chunks + 1
  let tasks := (List.range chunks).map fun c =>
    Task.spawn fun _ => (xs.extract (c * size) ((c + 1) * size)).map f
  tasks.foldl (fun acc t => acc ++ t.get) #[]

/-- The statistics of the training proofs `train`: the prior, and for every training theorem
(leaving out what `lo` says) and every `eval` theorem its prior corrections, the votes of its
`k` nearest training theorems, and co-usage with its `coUse` IDF top candidates. Theorems are
processed in parallel; the result does not depend on it. -/
def Stats.build (pl : PreparedLib) (lo : LeaveOut) (k coUse : Nat) (train eval : List (Item Addr))
    (cap : Nat := postingCap) : Stats :=
  let R := Refs.of (train.filterMap fun it => (pl.index.get? it.addr).map fun i => (pl.prep[i]!, it.premises)).toArray
  let jobs := (train.map (·, lo) ++ eval.map (·, LeaveOut.self)).toArray
  let views := parMap jobs fun (it, lo) => (pl.index.get? it.addr).map fun i =>
    let t := pl.prep[i]!
    let ctx := if coUse == 0 then #[] else
      let cs := candidates pl it
      ((rankBy (cs.map fun j => (idfScore t pl.prep[j]!, j))).extract 0 coUse).map (pl.prep[·]!.premise.addr)
    (it.addr, thmStats k (lo.keeps t.premise) t R ctx cap)
  { prior := priorOf train
    thm := views.foldl (fun m v => match v with
      | some (a, s) => m.insert a s
      | none => m) {} }

/-- Up to `k` of `xs` not already in `taken`, in order. -/
def takeNew (k : Nat) (taken : Array Nat) (xs : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  for x in xs do
    if out.size ≥ k then break
    if !taken.contains x && !out.contains x then out := out.push x
  return out

/-- Uniform draws from a pool of `size` values, the `i`-th being `get i`: `count` distinct values
with fuel `8·count`. -/
def drawIdxBy (size : Nat) (get : Nat → Nat) (count : Nat) (avoid : Array Nat) (r : Rng) :
    Array Nat × Rng := Id.run do
  let mut r := r
  let mut out := #[]
  if size == 0 then return (out, r)
  for _ in [:8 * count] do
    if out.size ≥ count then break
    let (i, r') := r.below size
    r := r'
    let x := get i
    if !avoid.contains x && !out.contains x then out := out.push x
  return (out, r)

def drawIdx (pool : Array Nat) (count : Nat) (avoid : Array Nat) (r : Rng) : Array Nat × Rng :=
  drawIdxBy pool.size (pool[·]!) count avoid r

/-- Each training theorem with its gold premises and negatives: the `negIdf` highest by IDF
among its candidates other than the gold premises, then `negModule` drawn from those in the gold
premises' modules, then `negRandom` from all of them. On a contiguous library the candidates are a
`Pool`, so a theorem costs its draws rather than a pass over the library (unless `negIdf > 0`). -/
def groupsOf (c : ScorerConfig) (pl : PreparedLib) (items : List (Item Addr)) : Array Group := Id.run do
  let mut r := Rng.seeded (c.seed + 11)
  let mut out := #[]
  let mut ranges : Option (Nat × ImportRanges) := none
  let n := pl.prep.size
  for it in items do
    let some ti := pl.index.get? it.addr | continue
    let pos := (it.premises.filterMap (pl.index.get? ·)).toArray
    if pos.isEmpty then continue
    let golds := it.premises
    let t := pl.prep[ti]!
    let mods := pos.map fun j => pl.prep[j]!.premise.module
    if pl.contiguous then
      let rs ← match ranges with
        | some (m, rs) => if m == it.thm.module then pure rs else pure (ImportRanges.of pl it.thm.module)
        | none => pure (ImportRanges.of pl it.thm.module)
      ranges := some (it.thm.module, rs)
      let pool := Pool.of pl rs it golds
      let hard := if c.negIdf == 0 then #[] else
        let cands := pool.toArray n
        takeNew c.negIdf #[] (rankBy (cands.map fun j => (idfScore t pl.prep[j]!, j)))
      let (fromMods, r1) := drawIdx (pool.inModules pl it.thm.module mods) c.negModule hard r
      let (rnd, r2) := drawIdxBy pool.size (pool.get n) c.negRandom (hard ++ fromMods) r1
      r := r2
      out := out.push { thm := ti, pos, neg := hard ++ fromMods ++ rnd }
    else
      let cands := (candidates pl it).filter fun j => !golds.contains pl.prep[j]!.premise.addr
      let hard := if c.negIdf == 0 then #[] else
        takeNew c.negIdf #[] (rankBy (cands.map fun j => (idfScore t pl.prep[j]!, j)))
      let modPool := cands.filter fun j => mods.contains pl.prep[j]!.premise.module
      let (fromMods, r1) := drawIdx modPool c.negModule hard r
      let (rnd, r2) := drawIdx cands c.negRandom (hard ++ fromMods) r1
      r := r2
      out := out.push { thm := ti, pos, neg := hard ++ fromMods ++ rnd }
  return out

/-- The `Pool` of every item equals its materialised candidates less its gold premises. -/
def poolsAgree (pl : PreparedLib) (items : List (Item Addr)) : Bool :=
  !pl.contiguous || items.all fun it =>
    let cands := (candidates pl it).filter fun j => !it.premises.contains pl.prep[j]!.premise.addr
    let pool := Pool.of pl (ImportRanges.of pl it.thm.module) it it.premises
    let mods := (it.premises.filterMap (pl.index.get? ·)).toArray.map fun j => pl.prep[j]!.premise.module
    pool.toArray pl.prep.size == cands &&
      pool.inModules pl it.thm.module mods == cands.filter fun j => mods.contains pl.prep[j]!.premise.module

/-! ## Evaluation -/

structure RankEval where
  ks : List Nat
  /-- Per `k`: gold premises in the top `k`, summed over theorems. -/
  hits : List Nat
  gold : Nat
  /-- Per `k`: `Σ hits/gold` over theorems, in units of `1/1000`. -/
  macroMilli : List Nat
  /-- `Σ 1/rank` of the first gold premise over theorems, in units of `1/10^6`. -/
  rrMicro : Nat
  items : Nat
  candidates : Nat

/-- One theorem's ranking measured against its gold premises. -/
structure ItemRank where
  /-- Per `k`: gold premises in the top `k`. -/
  hits : List Nat
  gold : Nat
  /-- `1/rank` of the first gold premise, in units of `1/10^6`; 0 if none is ranked. -/
  rrMicro : Nat
  candidates : Nat
  deriving Repr, Inhabited

/-- Measure a ranked list of addresses against the gold premises `g`. -/
def ItemRank.ofRanked (ks : List Nat) (g : List Addr) (ranked : Array Addr) (candidates : Nat) :
    ItemRank :=
  { hits := ks.map fun k => (g.filter fun a => (ranked.extract 0 k).contains a).length
    gold := g.length
    rrMicro := match ranked.findIdx? (g.contains ·) with
      | some i => 1000000 / (i + 1)
      | none => 0
    candidates }

/-- Rank the candidates `cs` (library indices) of one item with `score`. -/
def rankAmong (pl : PreparedLib) (it : Item Addr) (cs : Array Nat)
    (score : Item Addr → Array Nat → Array Int) : Array Addr :=
  let ss := score it cs
  (rankBy ((Array.range cs.size).map fun i => (ss[i]!, i))).map fun i => pl.prep[cs[i]!]!.premise.addr

/-- Rank every accessible candidate of one item with `score`. -/
def rankItem (ks : List Nat) (pl : PreparedLib) (score : Item Addr → Array Nat → Array Int)
    (it : Item Addr) : ItemRank :=
  let cs := candidates pl it
  ItemRank.ofRanked ks it.premises (rankAmong pl it cs score) cs.size

def RankEval.ofItems (ks : List Nat) (rs : List ItemRank) : RankEval :=
  rs.foldl (fun e r =>
    { e with hits := List.zipWith (· + ·) e.hits r.hits
             macroMilli := List.zipWith (fun acc h => acc + h * 1000 / max r.gold 1) e.macroMilli r.hits
             gold := e.gold + r.gold, rrMicro := e.rrMicro + r.rrMicro, items := e.items + 1
             candidates := e.candidates + r.candidates })
    { ks, hits := ks.map fun _ => 0, gold := 0, macroMilli := ks.map fun _ => 0, rrMicro := 0
      items := 0, candidates := 0 }

/-- Rank every accessible candidate of every item with `score` and measure recall and mean
reciprocal rank. -/
def evalRanking (ks : List Nat) (pl : PreparedLib) (items : List (Item Addr))
    (score : Item Addr → Array Nat → Array Int) : RankEval :=
  RankEval.ofItems ks (items.map (rankItem ks pl score))

/-- Neighbour votes (`thmStats`), ties broken by `idfScore`. -/
def knnRankScore (pl : PreparedLib) (st : Stats) : Item Addr → Array Nat → Array Int :=
  fun it cs => match pl.index.get? it.addr with
    | some ti => cs.map fun j =>
      let p := pl.prep[j]!
      Int.ofNat (((st.thm.getD it.addr {}).votes.getD p.premise.addr 0) * 4096) + idfScore pl.prep[ti]! p
    | none => cs.map fun _ => 0

def frequencyScore (pl : PreparedLib) (prior : Prior) : Item Addr → Array Nat → Array Int :=
  fun _ cs => cs.map fun j => Int.ofNat (prior.getD pl.prep[j]!.premise.addr 0)

def idfRankScore (pl : PreparedLib) : Item Addr → Array Nat → Array Int :=
  fun it cs => match pl.index.get? it.addr with
    | some ti => cs.map fun j => idfScore pl.prep[ti]! pl.prep[j]!
    | none => cs.map fun _ => 0

/-- IDF over name tokens alone (`nameScore`), ties broken by `idfScore`. -/
def nameRankScore (pl : PreparedLib) : Item Addr → Array Nat → Array Int :=
  fun it cs => match pl.index.get? it.addr with
    | some ti => cs.map fun j =>
      let t := pl.prep[ti]!
      let p := pl.prep[j]!
      nameScore t p * 4096 + idfScore t p
    | none => cs.map fun _ => 0

/-- The model's scores; premise embeddings are computed once. A bound error scores everything 0. -/
def modelScore (c : ScorerConfig) (pl : PreparedLib) (st : Stats) (m : ScorerModel) :
    Item Addr → Array Nat → Array Int :=
  let b := c.bounds
  let vs := pl.prep.map fun p => (embed b m.dim m.ep (p.feats c)).toOption.getD #[]
  fun it cs => match pl.index.get? it.addr with
    | none => cs.map fun _ => 0
    | some ti =>
      let t := pl.prep[ti]!
      let ts := st.thm.getD it.addr {}
      match embed b m.dim m.es (t.feats c) with
      | .error _ => cs.map fun _ => 0
      | .ok u => cs.map fun j =>
        let p := pl.prep[j]!
        (scoreRaw b m u vs[j]! (c.context st ts t p)).toOption.getD 0

/-- Each item's IDF top `n` candidates reordered by `score`, measured on its top 10: the reranking
task of the language-model baseline (`IxAIBench.Baseline`). -/
def rerankItems (ks : List Nat) (n : Nat) (pl : PreparedLib) (items : List (Item Addr))
    (score : Item Addr → Array Nat → Array Int) : Array ItemRank :=
  (items.map fun it =>
    let cs := candidates pl it
    let ss := idfRankScore pl it cs
    let top := ((rankBy ((Array.range cs.size).map fun k => (ss[k]!, k))).extract 0 n).map (cs[·]!)
    ItemRank.ofRanked ks it.premises ((rankAmong pl it top score).extract 0 10) top.size).toArray

/-- The members of `c`'s ensemble. -/
def ScorerConfig.members (c : ScorerConfig) : List ScorerConfig :=
  (List.range (max c.ensemble 1)).map fun i => { c with seed := c.seed + 1000 * i }

/-- Every member trained on `items`, each with the groups and negatives of its own seed. -/
def trainEnsemble (c : ScorerConfig) (pl : PreparedLib) (st : Stats) (items : List (Item Addr)) :
    Except BoundError (Array ScorerModel) :=
  List.toArray <$> c.members.mapM fun m => trainScorer m pl.prep st (groupsOf m pl items)

/-- The sum of the members' scores. -/
def ensembleScore (c : ScorerConfig) (pl : PreparedLib) (st : Stats) (ms : Array ScorerModel) :
    Item Addr → Array Nat → Array Int :=
  let fs := ms.toList.map (modelScore c pl st)
  fun it cs => fs.foldl (fun acc f => Array.zipWith (· + ·) acc (f it cs)) (cs.map fun _ => 0)

def pad3 (n : Nat) : String :=
  (if n < 100 then "0" else "") ++ (if n < 10 then "0" else "") ++ toString n

/-- Micro and macro recall at each `k` as percentages with one decimal, and MRR. -/
def RankEval.summary (e : RankEval) : List (String × String) :=
  let pct := fun (num den : Nat) =>
    if den == 0 then "n/a" else let t := num * 1000 / den; s!"{t / 10}.{t % 10}%"
  (e.ks.zip e.hits).map (fun (k, h) => (s!"R@{k}", pct h e.gold)) ++
    (e.ks.zip e.macroMilli).map (fun (k, m) => (s!"macro R@{k}", pct m (1000 * e.items))) ++
    [("MRR", if e.items == 0 then "n/a" else
        let t := e.rrMicro / e.items / 1000; s!"{t / 1000}.{pad3 (t % 1000)}")]

/-! ## Ranking without sorting -/

/-- `rankBy`'s order on positions: the higher score first, then the earlier position. -/
@[inline] def scoreBefore (ss : Array Int) (i j : Nat) : Bool :=
  ss[i]! > ss[j]! || (ss[i]! == ss[j]! && i < j)

/-- The first `k` of the positions `0 … n−1` under the strict total order `lt`, in order, by one
pass with an insertion buffer. -/
def topBy (k n : Nat) (lt : Nat → Nat → Bool) : Array Nat := Id.run do
  let mut top : Array Nat := #[]
  if k == 0 then return top
  for i in [:n] do
    if top.size < k || lt i top.back! then
      let mut buf := top.push i
      let mut q := buf.size - 1
      while q > 0 && lt buf[q]! buf[q - 1]! do
        buf := buf.swapIfInBounds q (q - 1)
        q := q - 1
      top := if buf.size > k then buf.pop else buf
  return top

/-- `ItemRank.ofRanked` of the candidates `cs` ranked by the strict total order `lt` on positions,
from the first `max ks` positions and the rank of the first gold premise, without sorting. -/
def ItemRank.ofOrder (ks : List Nat) (pl : PreparedLib) (it : Item Addr) (cs : Array Nat)
    (lt : Nat → Nat → Bool) : ItemRank :=
  let goldIdx : Std.HashSet Nat := it.premises.foldl (fun s a =>
    (pl.indices.getD a #[]).foldl (·.insert ·) s) {}
  let top := topBy (ks.foldl max 0) cs.size lt
  let ranked := top.map fun i => pl.prep[cs[i]!]!.premise.addr
  let golds := (Array.range cs.size).filter fun i => goldIdx.contains cs[i]!
  let first := golds.foldl (fun b i => match b with
    | some g => if lt i g then some i else some g
    | none => some i) none
  { hits := ks.map fun k => (it.premises.filter fun a => (ranked.extract 0 k).contains a).length
    gold := it.premises.length
    rrMicro := match first with
      | some g => 1000000 / ((Array.range cs.size).foldl (fun n i => if lt i g then n + 1 else n) 0 + 1)
      | none => 0
    candidates := cs.size }

/-- `rankItem` through `ItemRank.ofOrder`. -/
def rankItemFast (ks : List Nat) (pl : PreparedLib) (score : Item Addr → Array Nat → Array Int)
    (it : Item Addr) : ItemRank :=
  let cs := candidates pl it
  ItemRank.ofOrder ks pl it cs (scoreBefore (score it cs))

/-- One theorem ranked over all its candidates by IDF, name-IDF and a model, and its IDF top 30
reranked by each. The model scores only a prefilter pool, the union of the IDF and name-IDF top
`pool`; the candidates outside it follow in IDF order. -/
structure FullRank where
  model : ItemRank
  idf : ItemRank
  name : ItemRank
  modelRerank : ItemRank
  idfRerank : ItemRank
  nameRerank : ItemRank
  /-- Gold premises inside the prefilter pool. -/
  inPool : Nat
  poolSize : Nat
  deriving Inhabited

def rankFull (ks : List Nat) (pl : PreparedLib) (pool : Nat)
    (score : Item Addr → Array Nat → Array Int) (it : Item Addr) : FullRank :=
  let cs := candidates pl it
  let idf := idfRankScore pl it cs
  let nm := nameRankScore pl it cs
  let ps := (dedupNat ((topBy pool cs.size (scoreBefore idf)).toList ++
    (topBy pool cs.size (scoreBefore nm)).toList)).qsort (· < ·)
  let ms := score it (ps.map (cs[·]!))
  let inPool : Array (Option Int) := (Array.range ps.size).foldl (fun a k => a.set! ps[k]! (some ms[k]!))
    (Array.replicate cs.size none)
  let lt := fun (i j : Nat) => match inPool[i]!, inPool[j]! with
    | some a, some b => a > b || (a == b && i < j)
    | some _, none => true
    | none, some _ => false
    | none, none => scoreBefore idf i j
  let top30 := topBy 30 cs.size (scoreBefore idf)
  let goldIdx : Std.HashSet Nat := it.premises.foldl (fun s a => (pl.indices.getD a #[]).foldl (·.insert ·) s) {}
  let rerank := fun (ss : Array Int) =>
    let order := topBy 10 top30.size (fun a b => ss[top30[a]!]! > ss[top30[b]!]! || (ss[top30[a]!]! == ss[top30[b]!]! && a < b))
    ItemRank.ofRanked ks it.premises (order.map fun a => pl.prep[cs[top30[a]!]!]!.premise.addr) top30.size
  let msAll : Array Int := inPool.map (·.getD 0)
  { model := ItemRank.ofOrder ks pl it cs lt
    idf := ItemRank.ofOrder ks pl it cs (scoreBefore idf)
    name := ItemRank.ofOrder ks pl it cs (scoreBefore nm)
    modelRerank := rerank msAll, idfRerank := rerank idf, nameRerank := rerank nm
    inPool := (ps.filter fun i => goldIdx.contains cs[i]!).size, poolSize := ps.size }

end IxAIData
