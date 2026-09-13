import Compilatrix.Ixon.Sharing.Compress
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import Std.Data.DHashMap.Lemmas

/-! Exact indexed implementations of the frozen sharing analysis. Structural
equality remains the identity test; hashes only select lookup buckets or order
candidates. The equations below permit faster execution without changing the
reference canonicality predicate. -/

namespace Compilatrix.Ixon

instance Expr.instLawfulBEq : LawfulBEq Expr where
  eq_of_beq := by
    intro a b h
    induction a generalizing b <;> cases b <;>
      simp only [BEq.beq] at * <;>
      rw [instBEqExpr.beq.eq_1] at h <;>
      simp_all [Expr.ctorIdx, Nat.decEq] <;> grind
  rfl := by
    intro a
    induction a <;>
      simp only [BEq.beq] at * <;>
      rw [instBEqExpr.beq.eq_1] <;>
      simp_all [Expr.ctorIdx, Nat.decEq]

namespace Sharing.Indexed

def uniqueLoop : List Expr → Std.HashSet Expr → List Expr → List Expr
  | [], _, reversed => reversed.reverse
  | e :: es, seen, reversed =>
      if seen.contains e then uniqueLoop es seen reversed
      else uniqueLoop es (seen.insert e) (e :: reversed)

theorem uniqueLoop_eq (es : List Expr) (seen : Std.HashSet Expr) (reversed : List Expr)
    (exactSeen : ∀ e, seen.contains e = reversed.any (fun x => e == x)) :
    uniqueLoop es seen reversed = List.eraseDupsBy.loop (· == ·) es reversed := by
  induction es generalizing seen reversed with
  | nil => rfl
  | cons e es ih =>
      cases h : reversed.any (fun x => e == x) with
      | true => simpa only [uniqueLoop, List.eraseDupsBy.loop, exactSeen, h, ↓reduceIte]
          using ih seen reversed exactSeen
      | false =>
        simp only [uniqueLoop, List.eraseDupsBy.loop, exactSeen, h, Bool.false_eq_true, ↓reduceIte]
        apply ih
        intro x
        simp only [Std.HashSet.contains_insert, exactSeen, List.any_cons]
        by_cases same : e = x
        · simp [same]
        · simp only [beq_eq_false_iff_ne.mpr same, beq_eq_false_iff_ne.mpr (Ne.symm same)]

def unique (es : List Expr) : List Expr := uniqueLoop es {} []

theorem unique_eq (es : List Expr) : unique es = es.eraseDups := by
  exact uniqueLoop_eq es {} [] (by intro e; simp)

structure Entry (e : Expr) where
  digest : Address
  bytes : Nat
  digest_eq : digest = exprHash e
  bytes_eq : bytes = ixonV2EffectiveSize e

abbrev Cache := Std.DHashMap Expr Entry

def cached (cache : Cache) (e : Expr) : Entry e :=
  match cache.get? e with
  | some entry => entry
  | none => ⟨exprHash e, ixonV2EffectiveSize e, rfl, rfl⟩

/-- Build a node's metrics from already memoized children. The equalities are
erased in executable code, while still checking the cache at the type level. -/
def compute (cache : Cache) : (e : Expr) → Entry e
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) =>
      ⟨exprHash e, ixonV2EffectiveSize e, by subst e; rfl, by subst e; rfl⟩
  | e@(.prj _ _ v) =>
      let v := cached cache v
      ⟨Address.blake3 (nodeBytes e #[v.digest]), ixonV2NodeBaseSize e + v.bytes,
        by subst e; simp only [v.digest_eq, exprHash],
        by subst e; simp only [v.bytes_eq, ixonV2EffectiveSize]⟩
  | e@(.app f a) | e@(.lam _ f a) | e@(.all _ _ f a) =>
      let f := cached cache f
      let a := cached cache a
      ⟨Address.blake3 (nodeBytes e #[f.digest, a.digest]),
        ixonV2NodeBaseSize e + f.bytes + a.bytes,
        by subst e; simp only [f.digest_eq, a.digest_eq, exprHash],
        by subst e; simp only [f.bytes_eq, a.bytes_eq, ixonV2EffectiveSize]⟩
  | e@(.letE _ t v b) =>
      let t := cached cache t
      let v := cached cache v
      let b := cached cache b
      ⟨Address.blake3 (nodeBytes e #[t.digest, v.digest, b.digest]),
        ixonV2NodeBaseSize e + t.bytes + v.bytes + b.bytes,
        by subst e; simp only [t.digest_eq, v.digest_eq, b.digest_eq, exprHash],
        by subst e; simp only [t.bytes_eq, v.bytes_eq, b.bytes_eq, ixonV2EffectiveSize]⟩

def populate (e : Expr) (cache : Cache) : Cache :=
  if cache.contains e then cache
  else
    let cache := match e with
      | .prj _ _ v => populate v cache
      | .app f a | .lam _ f a | .all _ _ f a => populate a (populate f cache)
      | .letE _ t v b => populate b (populate v (populate t cache))
      | _ => cache
    cache.insert e (compute cache e)
termination_by e

def prepare (es : Array Expr) : Cache :=
  es.foldl (fun cache e => populate e cache) {}

def keyLT (cache : Cache) (a b : Expr) : Bool :=
  let ah := (cached cache a).digest
  let bh := (cached cache b).digest
  if ah == bh then (ser a).data < (ser b).data
  else ah.hash.data < bh.hash.data

theorem keyLT_eq (cache : Cache) : keyLT cache = exprKeyLT := by
  funext a b
  simp only [keyLT, exprKeyLT, (cached cache a).digest_eq, (cached cache b).digest_eq]

def countInto : List Occurrence → Std.HashMap Expr Nat → Std.HashMap Expr Nat
  | [], counts => counts
  | o :: os, counts => countInto os (counts.insert o.expr (counts.getD o.expr 0 + 1))

theorem countInto_eq (os : List Occurrence) (counts : Std.HashMap Expr Nat) (e : Expr) :
    (countInto os counts).getD e 0 = counts.getD e 0 + occurrenceCount e os := by
  induction os generalizing counts with
  | nil => simp [countInto, occurrenceCount]
  | cons o os ih =>
      rw [countInto, ih]
      by_cases same : o.expr = e
      · simp [same, occurrenceCount, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
      · simp [Std.HashMap.getD_insert, same, occurrenceCount]

def decide (exprs : Array Expr) : Array Expr :=
  let os := blockOccurrences exprs
  let representatives := unique (os.map (·.expr))
  let counts := countInto os {}
  let cache := prepare exprs
  let candidates := representatives.foldl (init := #[]) fun out e =>
    let n := counts.getD e 0
    let entry := cached cache e
    if n ≥ 2 && (n - 1) * entry.bytes > n then
      out.push (Candidate.mk e entry.bytes n entry.digest)
    else out
  let candidates := candidates.qsort candidateLT
  candidates.foldl (init := #[]) fun selected cand =>
    if (cand.usageCount - 1) * cand.termSize >
        cand.usageCount * shareRefSize selected.size then
      selected.push cand.expr
    else selected

theorem decide_eq (exprs : Array Expr) : decide exprs = decideIxonV2Sharing exprs := by
  have candidates :
      (fun (out : Array Candidate) (e : Expr) =>
        let n := (countInto (blockOccurrences exprs) {}).getD e 0
        let entry := cached (prepare exprs) e
        if n ≥ 2 && (n - 1) * entry.bytes > n then
          out.push (Candidate.mk e entry.bytes n entry.digest)
        else out) =
      (fun (out : Array Candidate) (e : Expr) =>
        let n := occurrenceCount e (blockOccurrences exprs)
        let size := ixonV2EffectiveSize e
        if n ≥ 2 && (n - 1) * size > n then
          out.push (Candidate.mk e size n (exprHash e))
        else out) := by
    funext out e
    dsimp only
    rw [countInto_eq]
    simp only [Std.HashMap.getD_empty, Nat.zero_add, Entry.bytes_eq, Entry.digest_eq]
  unfold decide decideIxonV2Sharing
  dsimp only
  rw [unique_eq, candidates]

def topological (exprs selected : Array Expr) : List Expr :=
  let all := (unique ((blockOccurrences exprs).map (·.expr))).toArray
  let cache := prepare exprs
  let sortedKeys := all.qsort (keyLT cache)
  let topo := unique (sortedKeys.toList.flatMap postorder)
  topo.filter fun e => selected.contains e

theorem topological_eq (exprs selected : Array Expr) :
    topological exprs selected = selectedTopological exprs selected := by
  unfold topological selectedTopological
  dsimp only
  rw [unique_eq ((blockOccurrences exprs).map (·.expr)), keyLT_eq, unique_eq]

def indexFrom : Nat → List Expr → Std.HashMap Expr Nat
  | _, [] => {}
  | next, e :: es => (indexFrom (next + 1) es).insert e next

theorem indexFrom_eq (es : List Expr) (next : Nat) (e : Expr) :
    (indexFrom next es).get? e = (findExprIndex? e es).map (next + ·) := by
  induction es generalizing next with
  | nil => simp [indexFrom, findExprIndex?]
  | cons head rest ih =>
      rw [indexFrom, Std.HashMap.get?_insert, ih]
      by_cases same : head = e
      · simp [findExprIndex?, same]
      · simp [findExprIndex?, same, Option.map_map,
          Function.comp_def, Nat.add_comm, Nat.add_left_comm]

def rewriteLookup (lookup : Expr → Option Nat) : Expr → Expr
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) =>
      match lookup e with
      | some i => .share i.toUInt64
      | none => e
  | e@(.prj r f v) =>
      match lookup e with
      | some i => .share i.toUInt64
      | none => .prj r f (rewriteLookup lookup v)
  | e@(.app f a) =>
      match lookup e with
      | some i => .share i.toUInt64
      | none => .app (rewriteLookup lookup f) (rewriteLookup lookup a)
  | e@(.lam u t b) =>
      match lookup e with
      | some i => .share i.toUInt64
      | none => .lam u (rewriteLookup lookup t) (rewriteLookup lookup b)
  | e@(.all u o d c) =>
      match lookup e with
      | some i => .share i.toUInt64
      | none => .all u o (rewriteLookup lookup d) (rewriteLookup lookup c)
  | e@(.letE nd t v b) =>
      match lookup e with
      | some i => .share i.toUInt64
      | none => .letE nd (rewriteLookup lookup t) (rewriteLookup lookup v)
          (rewriteLookup lookup b)

theorem rewriteLookup_eq (lookup : Expr → Option Nat) (shared : List Expr)
    (exactLookup : ∀ e, lookup e = findExprIndex? e shared) (e : Expr) :
    rewriteLookup lookup e = rewriteWith shared e := by
  induction e <;> simp_all only [rewriteLookup, rewriteWith] <;> rfl

def rewrite (shared : List Expr) : Expr → Expr :=
  let index := indexFrom 0 shared
  rewriteLookup (fun e => index.get? e)

theorem rewrite_eq (shared : List Expr) : rewrite shared = rewriteWith shared := by
  funext e
  apply rewriteLookup_eq
  intro x
  rw [indexFrom_eq]
  simp only [Nat.zero_add]
  cases findExprIndex? x shared <;> rfl

theorem findExprIndex?_append (shared : List Expr) (last needle : Expr) :
    findExprIndex? needle (shared ++ [last]) =
      match findExprIndex? needle shared with
      | some i => some i
      | none => if last = needle then some shared.length else none := by
  induction shared with
  | nil => simp [findExprIndex?]
  | cons head rest ih =>
      by_cases same : head = needle
      · simp [findExprIndex?, same]
      · simp only [List.cons_append, findExprIndex?, same, ↓reduceIte, ih]
        cases found : findExprIndex? needle rest <;>
          simp [List.length_cons]

def advance (index : Std.HashMap Expr Nat) (e : Expr) (next : Nat) : Std.HashMap Expr Nat :=
  if (index.get? e).isSome then index else index.insert e next

theorem advance_eq (index : Std.HashMap Expr Nat) (shared : List Expr)
    (exactLookup : ∀ e, index.get? e = findExprIndex? e shared) (last needle : Expr) :
    (advance index last shared.length).get? needle = findExprIndex? needle (shared ++ [last]) := by
  rw [findExprIndex?_append]
  unfold advance
  rw [exactLookup last]
  cases found : findExprIndex? last shared with
  | some i =>
      simp only [Option.isSome_some, ↓reduceIte, exactLookup]
      cases other : findExprIndex? needle shared with
      | some j => rfl
      | none =>
          by_cases same : last = needle
          · simp [same, other] at found
          · simp [same]
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Std.HashMap.get?_insert,
        exactLookup]
      by_cases same : last = needle
      · simp [same] at found ⊢
        simp [found]
      · simp only [beq_iff_eq, same, ↓reduceIte]
        cases findExprIndex? needle shared <;> rfl

def table (next : Nat) (index : Std.HashMap Expr Nat) : List Expr → List Expr
  | [] => []
  | e :: es => rewriteLookup (fun x => index.get? x) e ::
      table (next + 1) (advance index e next) es

theorem table_eq (es shared : List Expr) (index : Std.HashMap Expr Nat)
    (exactLookup : ∀ e, index.get? e = findExprIndex? e shared) :
    table shared.length index es = buildTable shared es := by
  induction es generalizing shared index with
  | nil => rfl
  | cons e es ih =>
      simp only [table, buildTable, rewriteLookup_eq _ _ exactLookup]
      have length : (shared ++ [e]).length = shared.length + 1 := by simp
      rw [← length]
      exact congrArg (List.cons (rewriteWith shared e))
        (ih (shared ++ [e]) (advance index e shared.length) (advance_eq index shared exactLookup e))

def build (exprs : Array Expr) : Compression :=
  let reps := (topological exprs (decide exprs)).filter shareFree
  { bodies := exprs.map (rewrite reps)
    table := (table 0 {} reps).toArray }

theorem build_eq (exprs : Array Expr) : build exprs = buildIxonV2Compression exprs := by
  have tableEqual (reps : List Expr) : table 0 {} reps = buildTable [] reps :=
    table_eq reps [] {} (by intro e; simp [findExprIndex?])
  simp only [build, buildIxonV2Compression, ixonV2CompressionReps, topological_eq,
    decide_eq, rewrite_eq, tableEqual]

def compress (exprs : Array Expr) : Option Compression :=
  if !exprs.all shareFree then none
  else
    let out := build exprs
    if _hstructural : structuralWF out.table out.bodies = true then
      if _hindex : out.table.size < UInt64.size then
        if _hinline : out.expanded = exprs then some out else none
      else none
    else none

theorem compress_eq (exprs : Array Expr) : compress exprs = compressIxonV2? exprs := by
  simp only [compress, compressIxonV2?, build_eq]

def canonical (bodies table : Array Expr) : Bool :=
  if !structuralWF table bodies then false
  else
    let expanded := bodies.map (inlineExpr table)
    match compress expanded with
    | some out => Decidable.decide (out.bodies = bodies ∧ out.table = table)
    | none => false

theorem canonical_eq (bodies table : Array Expr) :
    canonical bodies table = ixonV2Canonical bodies table := by
  simp only [canonical, ixonV2Canonical, compress_eq]
  rfl

def canonicalWith (limits : ResourceLimits) (bodies table : Array Expr) :
    Except Work.Exceeded Bool :=
  match Work.ensure .layer1NodeVisits (Work.layer1NodeVisits table bodies)
      limits.maxLayer1NodeVisits with
  | .error exceeded => .error exceeded
  | .ok _ =>
    match Work.expandedUnits? table bodies with
    | none => .ok false
    | some units =>
      match Work.ensure .compressionInputUnits units limits.maxCompressionInputUnits with
      | .error exceeded => .error exceeded
      | .ok _ => .ok (canonical bodies table)

theorem canonicalWith_eq : canonicalWith = ixonV2CanonicalWith := by
  funext limits bodies table
  simp only [canonicalWith, ixonV2CanonicalWith, canonical_eq]
  rfl

@[csimp] theorem compile_ixonV2CanonicalWith : ixonV2CanonicalWith = canonicalWith :=
  canonicalWith_eq.symm

end Sharing.Indexed
end Compilatrix.Ixon
