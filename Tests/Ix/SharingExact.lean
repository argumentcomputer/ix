/-
  Tests for the exact minimum sharing core (`Ix.Sharing.Exact`; specified in
  `docs/sharing-minimum.md`).

  Groups:
  * exact serializer lengths vs the production writer (integer widths,
    telescope boundaries, Share widths, complete-Constant decomposition);
  * structural IDs vs an independent naive implementation, representation
    independence, bounded expansion and its failure modes, root API;
  * the fixed-dictionary optimizer vs exhaustive enumeration in arbitrary
    dictionary orders and at every Share width boundary;
  * the full optimizer vs the exhaustive oracle (full key), vs a unit-width
    relaxation oracle, vs a brute force over independent atoms;
  * the §2 fixtures byte for byte;
  * size ≤ unshared / another encoding, idempotence, and resource limits.

  Generated inputs use a fixed-seed splitmix64 generator, so every failure
  is reproducible from the printed seed and case index.
-/
module

public import Ix.Sharing.Exact
public import Ix.Ixon
public import Ix.CompileM
public import LSpec
public import Tests.Gen.Ixon

public section

open LSpec Ixon Ix.Sharing.Exact

-- Test groups are functions run from deferred IO actions; keep their closed
-- bodies from being hoisted into constants evaluated at program start.
set_option compiler.extract_closed false

namespace Tests.SharingExact

/-! ## Helpers -/

def hexOf (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  String.join (b.toList.map fun x => String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

def P : Ixon.Expr := .sort 0

/-- Ordinary non-dependent arrow `a → b`. -/
def arr (a b : Ixon.Expr) : Ixon.Expr := .all a b

/-- `Tn = Prop → … → Prop` with `n` binders. -/
def chain : Nat → Ixon.Expr
  | 0 => P
  | n + 1 => arr P (chain n)

def axiomOf (typ : Ixon.Expr) (univs : Array Univ := #[.zero]) : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ }, sharing := #[], refs := #[], univs }

/-- Another valid shared encoding of `c` (the uniform-width construction at
`w = 1`): an input representation that differs from the canonical one. -/
def alternateOf (c : Constant) : Constant :=
  (normalizeConstantSharingUniform 1 c).toOption.getD c

/-- Little-endian bytes of a `UInt64`. -/
def u64LE (x : UInt64) : ByteArray :=
  ByteArray.mk ((Array.range 8).map fun i => (x >>> (8 * i).toUInt64).toUInt8)

def cbytes (c : Constant) : Nat := (serConstant c).size

def withOk {α} (name : String) (x : Except SharingError α) (k : α → AssertM Unit) : AssertM Unit :=
  match x with
  | .ok a => k a
  | .error e => fail s!"{name}: unexpected error {reprStr e}"

def isErr {α} (x : Except SharingError α) (p : SharingError → Bool) : Bool :=
  match x with
  | .ok _ => false
  | .error e => p e

def exhausted (r : Resource) : SharingError → Bool
  | .resourceExhausted r' _ => r' == r
  | _ => false

def expandRoots (roots : Array Ixon.Expr) : Except SharingError Expanded :=
  expand {} #[] roots false

def distinctCount (roots : Array Ixon.Expr) : Nat :=
  match expandRoots roots with
  | .ok ex => ex.dag.size
  | .error _ => 0

/-! ## Deterministic generator (splitmix64) -/

structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev RGen := StateM Rng

def rand (n : Nat) : RGen Nat := do
  let (x, r) := (← get).next
  set r
  return if n == 0 then 0 else x.toNat % n

def runGen {α} (seed : Nat) (g : RGen α) : α := (g.run ⟨seed.toUInt64⟩).1

/-- Every `let` mode, the default first. -/
def letModes : Array LetMode :=
  #[.value .many, .value .borrowed, .value .unique, .value .uniqueBorrowed, .value .once,
    .value .onceBorrowed, .value .erased, .borrow]

/-- A `let`'s `nonDep` and mode: the default mode two times in three. -/
def genLet : RGen (Bool × LetMode) := do
  let nonDep := (← rand 2) == 0
  if (← rand 3) != 0 then return (nonDep, .value .many)
  return (nonDep, letModes[← rand letModes.size]!)

def genLeaf : RGen Ixon.Expr := do
  match ← rand 12 with
  | 0 => return .sort (#[0, 1, 300][← rand 3]!)
  | 1 => return .var (#[0, 1, 9][← rand 3]!)
  | 2 => return .ref (← rand 2).toUInt64 (#[#[], #[0], #[0, 1]][← rand 3]!)
  | 3 => return .recur 0 #[]
  | 4 => return .str (← rand 2).toUInt64
  | 5 => return .nat 1
  | 6 => return .ref 1 #[]
  | 7 => return .sort 0
  | 8 => return .var 1
  | _ => return .var 0

def isApp : Ixon.Expr → Bool | .app .. => true | _ => false
def isLam : Ixon.Expr → Bool | .lam .. => true | _ => false
def isAll : Ixon.Expr → Bool | .all .. => true | _ => false

/-- A node over pool elements; with `noMerge` no telescope can merge. -/
def genNode (pool : Array Ixon.Expr) (noMerge : Bool := false) : RGen Ixon.Expr := do
  let c := pool[← rand pool.size]!
  let d := pool[← rand pool.size]!
  let e := pool[← rand pool.size]!
  match ← rand 7 with
  | 0 | 1 =>
    if noMerge && isApp c then return .prj 0 0 c else return .app c d
  | 2 =>
    if noMerge && isLam d then return .prj 1 2 d else return .lam c d
  | 3 | 4 =>
    if noMerge && isAll d then return .prj 0 1 d else return .all c d
  | 5 => return .prj (← rand 2).toUInt64 (← rand 3).toUInt64 c
  | _ =>
    let (nonDep, mode) ← genLet
    return .letE nonDep mode c d e

/-- Roots built from a pool, so subterms repeat. -/
def genRoots (leaves nodes roots : Nat) (noMerge : Bool := false) : RGen (Array Ixon.Expr) := do
  let mut pool : Array Ixon.Expr := #[]
  for _ in [0:1 + (← rand leaves)] do pool := pool.push (← genLeaf)
  for _ in [0:(← rand (nodes + 1))] do pool := pool.push (← genNode pool noMerge)
  let mut out : Array Ixon.Expr := #[]
  for _ in [0:1 + (← rand roots)] do
    let i ← if (← rand 3) == 0 then rand pool.size
      else do pure (pool.size - 1 - (← rand (min 3 pool.size)))
    out := out.push pool[i]!
  return out

def testRefs : Array Address := #[Address.blake3 ⟨#[1]⟩, Address.blake3 ⟨#[2]⟩]
def testUnivs : Array Univ := #[.zero, .succ .zero]

/-- Wrap roots in a ConstantInfo of a kind selected by the root count. -/
def wrapRoots (roots : Array Ixon.Expr) (sel : Nat) : Constant :=
  let info : ConstantInfo := match roots.size with
    | 0 => .iPrj ⟨0, testRefs[0]!⟩
    | 1 => if sel % 2 == 0 then .axio ⟨false, 0, roots[0]!⟩ else .quot ⟨.type, 0, roots[0]!⟩
    | 2 => .defn ⟨.defn, .safe, {}, 0, roots[0]!, roots[1]!⟩
    | _ =>
      if sel % 2 == 0 then
        .recr ⟨false, false, 0, 0, 0, 0, 0, roots[0]!,
          (roots.extract 1 roots.size).map fun rhs => ⟨0, rhs⟩⟩
      else
        let ctors := (roots.extract 3 roots.size).map fun t => ⟨false, 0, 0, 0, 0, .inherited, t⟩
        .muts #[.defn ⟨.defn, .safe, {}, 0, roots[0]!, roots[1]!⟩,
          .indc ⟨false, 0, 0, 0, roots[2]!, ctors⟩]
  { info, sharing := #[], refs := testRefs, univs := testUnivs }

/-! ## Independent references used by the tests -/

def exprChildren : Ixon.Expr → List Ixon.Expr
  | .prj _ _ v => [v]
  | .app f a => [f, a]
  | .lam t b => [t, b]
  | .all t b => [t, b]
  | .letE _ _ t v b => [t, v, b]
  | _ => []

partial def exprHeight (e : Ixon.Expr) : Nat :=
  (exprChildren e).foldl (fun acc c => max acc (exprHeight c + 1)) 0

partial def allSubterms (e : Ixon.Expr) : List Ixon.Expr :=
  e :: (exprChildren e).flatMap allSubterms

/-- §3.2 tag, restated from the table. -/
def exprTag : Ixon.Expr → Nat
  | .sort _ => 0 | .var _ => 1 | .ref .. => 2 | .recur .. => 3 | .prj .. => 4
  | .str _ => 5 | .nat _ => 6 | .app .. => 7 | .lam .. => 8 | .all .. => 9
  | .letE .. => 10 | .share _ => 11

/-- §3.2 scalar vector, restated from the table. -/
def exprScalars : Ixon.Expr → List Nat
  | .sort i | .var i | .str i | .nat i => [i.toNat]
  | .ref r us | .recur r us => [r.toNat, us.size] ++ us.toList.map (·.toNat)
  | .prj t f _ => [t.toNat, f.toNat]
  | .app .. | .lam .. | .all .. => []
  | .letE nonDep mode .. => [(LetMode.header nonDep mode).toNat]
  | .share i => [i.toNat]

def cmpNats : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else cmpNats xs ys

/-- Naive canonical order: distinct subterms by structural `==`, grouped by
height, sorted by `(tag, scalars, child positions)`. -/
def naiveCanonical (roots : Array Ixon.Expr) : Array Ixon.Expr := Id.run do
  let mut distinct : Array Ixon.Expr := #[]
  for r in roots do
    for s in allSubterms r do
      if !distinct.contains s then distinct := distinct.push s
  let maxH := distinct.foldl (fun acc e => max acc (exprHeight e)) 0
  let mut out : Array Ixon.Expr := #[]
  for h in [0:maxH + 1] do
    let level := distinct.filter (exprHeight · == h)
    let placed := out
    -- Tag, then scalars, then child positions (all lexicographic).
    let cmp (a b : Ixon.Expr) : Ordering :=
      match cmpNats [exprTag a] [exprTag b] with
      | .eq => match cmpNats (exprScalars a) (exprScalars b) with
        | .eq => cmpNats ((exprChildren a).map fun c => (placed.findIdx? (· == c)).getD 0)
                         ((exprChildren b).map fun c => (placed.findIdx? (· == c)).getD 0)
        | o => o
      | o => o
    out := out ++ level.qsort fun a b => cmp a b == .lt
  return out

/-- Direct substitution of a backward-reference table. -/
partial def naiveExpand (table : Array Ixon.Expr) : Ixon.Expr → Ixon.Expr
  | .share j => naiveExpand (table.extract 0 j.toNat) table[j.toNat]!
  | .prj t f v => .prj t f (naiveExpand table v)
  | .app f a => .app (naiveExpand table f) (naiveExpand table a)
  | .lam t b => .lam (naiveExpand table t) (naiveExpand table b)
  | .all t b => .all (naiveExpand table t) (naiveExpand table b)
  | .letE nonDep mode t v b =>
    .letE nonDep mode (naiveExpand table t) (naiveExpand table v) (naiveExpand table b)
  | e => e

/-! ## Integer widths and exact lengths -/

def boundaryValues : List Nat :=
  [0, 1, 7, 8, 127, 128, 255, 256, 65535, 65536, 2^24 - 1, 2^24, 2^32 - 1, 2^32,
   2^40 - 1, 2^40, 2^48 - 1, 2^48, 2^56 - 1, 2^56, 2^64 - 1] ++
  ([0, 2, 4].flatMap fun f =>
    [tagNEnd1 f, tagNEnd2 f, tagNEnd3 f, tagNEnd4 f, tagNEnd5 f].flatMap fun e =>
      [e - 1, e, e + 1])

def widthTests : Spec :=
  describe "integer widths" do
    itBool "tag0Size = putTagN 0 length at every rung boundary"
      (boundaryValues.all fun n => tag0Size n == (runPut (putTagN 0 0 n.toUInt64)).size)
    itBool "tag4Size = putTagN 4 length at every rung boundary"
      (boundaryValues.all fun n =>
        [0x7, 0x8, 0x9, 0xB].all fun (f : UInt8) =>
          tag4Size n == (runPut (putTagN 4 f n.toUInt64)).size)
    itBool "shareWidth = serialized Share length at every boundary"
      (boundaryValues.all fun n =>
        shareWidth n == (serExpr (.share n.toUInt64)).size &&
          exprSize (.share n.toUInt64) == shareWidth n)
    itBool "Share 7/8 → 1/2 bytes" (shareWidth 7 == 1 && shareWidth 8 == 2)
    itBool "Share 1031/1032 → 2/3 bytes" (shareWidth 1031 == 2 && shareWidth 1032 == 3)
    itBool "Share 66567/66568 → 3/4 bytes" (shareWidth 66567 == 3 && shareWidth 66568 == 4)
    itBool "Share 16843783/16843784 → 4/5 bytes"
      (shareWidth 16843783 == 4 && shareWidth 16843784 == 5)
    itBool "Share 4311811079/4311811080 → 5/9 bytes"
      (shareWidth 4311811079 == 5 && shareWidth 4311811080 == 9)
    itBool "Share 2^64-1 → 9 bytes" (shareWidth (2^64 - 1) == 9)
    itBool "TagN f=0 127/128 → 1/2 bytes, 16511/16512 → 2/3, 82047/82048 → 3/4, 16859263/16859264 → 4/5"
      (tag0Size 127 == 1 && tag0Size 128 == 2 && tag0Size 16511 == 2 && tag0Size 16512 == 3 &&
        tag0Size 82047 == 3 && tag0Size 82048 == 4 && tag0Size 16859263 == 4 &&
        tag0Size 16859264 == 5)
    itBool "tag0BracketStart is the start of the count's TagN rung"
      (boundaryValues.all fun k =>
        tag0Size (tag0BracketStart k) == tag0Size k &&
          (tag0BracketStart k == 0 || decide (tag0Size (tag0BracketStart k - 1) < tag0Size k)))
    itBool "tag0StepBound bounds the growth of the count's TagN width"
      ((boundaryValues.all fun n =>
          n == 0 || decide (tag0Size n - tag0Size (n - 1) ≤ tag0StepBound n)) &&
        tag0StepBound 82048 == 1 && tag0StepBound (tagNEnd5 0 - 1) == 1 &&
        tag0StepBound (tagNEnd5 0) == 4)

/-- App spine with `n` arguments, Lam/All telescopes with `n` binders, and
mixed nestings; `let`s with one- and two-byte headers. -/
def telescopeExprs : List Ixon.Expr := Id.run do
  let mut out : List Ixon.Expr := []
  for n in [1, 2, 7, 8, 9, 255, 256, 257] do
    let app := (List.range n).foldl (fun f i => .app f (.var (i % 3).toUInt64)) (.ref 0 #[])
    let lam := (List.range n).foldl (fun b _ => .lam (.sort 0) b) (.var 0)
    let all := (List.range n).foldl (fun b _ => arr (.var 1) b) (.sort 1)
    out := out ++ [app, lam, all, .app lam app, .lam all lam, arr app (.share 300),
      .app (.share 8) app, .letE true (.value .many) app lam all,
      .letE false .borrow app lam all, .prj 3 9 app, arr (.share 7) all]
  return out

def genExprForSize : RGen Ixon.Expr := do
  let roots ← genRoots 4 8 1
  let e := roots[0]!
  -- Sprinkle Shares with boundary indices.
  let idx := [0, 7, 8, 255, 256, 65535, 65536, 2^32, 2^64 - 1][← rand 9]!
  match ← rand 4 with
  | 0 => return .app e (.share idx.toUInt64)
  | 1 => return arr (.share idx.toUInt64) e
  | 2 => return .lam e (.share idx.toUInt64)
  | _ => return e

def exprSizeTests : Spec :=
  describe "exact expression length" do
    itBool "exprSize = serExpr size on telescope boundaries (1/2/7/8/9/255/256/257)"
      (telescopeExprs.all fun e => exprSize e == (serExpr e).size)
    it "exprSize = serExpr size on 2000 generated expressions with boundary Shares" do
      let gen := runGen 7 ((List.range 2000).mapM fun _ => genExprForSize)
      expect (gen.all fun e => exprSize e == (serExpr e).size)
    itBool "App with 7/8 args uses 1/2 header bytes"
      (let a7 := (List.range 7).foldl (fun f _ => .app f (.var 0)) (.var 1)
       let a8 := Ixon.Expr.app a7 (.var 0)
       (serExpr a7).size == 1 + 8 && (serExpr a8).size == 2 + 9)

/-- A table of `k` entries: entry `i` is `Var i` (so entries are distinct),
and roots reference the last entries. -/
def tableConstant (info : ConstantInfo) (k : Nat) : Constant :=
  { info, sharing := (Array.range k).map fun i => .var i.toUInt64, refs := testRefs,
    univs := testUnivs }

def decompositionHolds (c : Constant) : Bool :=
  cbytes c == fixedConstantBytes c + exprsSize (constantInfoRoots c.info) +
    tag0Size c.sharing.size + exprsSize c.sharing

def decompositionTests : Spec :=
  describe "complete-Constant length decomposition" do
    it "serConstant size = fixed + roots + tag0(table) + table (all kinds; tables 0/1/8/9/127/128/255/256/257/1032/1033)" do
      let mkRoots (k : Nat) (n : Nat) : Array Ixon.Expr :=
        (Array.range n).map fun i => .app (.share (k - 1 - i % (max k 1)).toUInt64) (.var i.toUInt64)
      let infos (rs : Array Ixon.Expr) : List ConstantInfo :=
        [ .defn ⟨.defn, .safe, {}, 0, rs[0]!, rs[1]!⟩, .axio ⟨false, 1, rs[0]!⟩,
          .quot ⟨.lift, 2, rs[0]!⟩,
          .recr ⟨true, false, 1, 2, 3, 4, 5, rs[0]!, #[⟨1, rs[1]!⟩, ⟨300, rs[2]!⟩]⟩,
          .cPrj ⟨1, 2, testRefs[0]!⟩, .rPrj ⟨3, testRefs[1]!⟩, .iPrj ⟨200, testRefs[0]!⟩,
          .dPrj ⟨0, testRefs[1]!⟩,
          .muts #[.defn ⟨.thm, .part, {}, 0, rs[0]!, rs[1]!⟩,
                  .indc ⟨true, 1, 1, 0, rs[2]!, #[⟨false, 1, 0, 1, 2, .inherited, rs[3]!⟩, ⟨false, 1, 1, 1, 0, .inherited, rs[0]!⟩]⟩,
                  .recr ⟨false, true, 0, 0, 0, 0, 0, rs[1]!, #[⟨2, rs[2]!⟩]⟩] ]
      let cases := [0, 1, 8, 9, 127, 128, 255, 256, 257, 1032, 1033].flatMap fun k =>
        (infos (mkRoots k 4)).map fun info => tableConstant info k
      expect (cases.all decompositionHolds) s!"decomposition failed on {cases.length} constants"
    itBool "Share 7/8 and 1031/1032 have widths 1/2 and 2/3"
      (exprSize (.share 7) == 1 && exprSize (.share 8) == 2 &&
        exprSize (.share 1031) == 2 && exprSize (.share 1032) == 3)

/-! ## Structural IDs, expansion and roots -/

def fixtureA : Ixon.Expr := arr P P
def fixtureB : Ixon.Expr := arr P (.sort 1)
def tiedMinimaRoot : Ixon.Expr := arr fixtureA (arr fixtureA (arr fixtureB fixtureB))

def structuralIdTests : Spec :=
  describe "structural IDs" do
    it "tied-minima fixture: ids Sort0=0 Sort1=1 A=2 B=3 (B→B)=4 (A→B→B)=5 root=6" do
      withOk "tied-minima fixture" (expandRoots #[tiedMinimaRoot]) fun ex =>
        expect (ex.dag.toExprs == #[P, .sort 1, fixtureA, fixtureB, arr fixtureB fixtureB,
          arr fixtureA (arr fixtureB fixtureB), tiedMinimaRoot] && ex.roots == #[6])
    it "witness: ids P=0 T1=1 T2=2 R=3" do
      withOk "witness" (expandRoots #[arr (chain 2) (chain 2)]) fun ex =>
        expect (ex.dag.toExprs == #[P, chain 1, chain 2, arr (chain 2) (chain 2)])
    it "canonical IDs equal an independent naive assignment on 300 generated inputs" do
      let naiveAgree := runGen 11 do
        let mut ok := true
        for _ in [0:300] do
          let roots ← genRoots 5 10 3
          match expandRoots roots with
          | .ok ex =>
            let naive := naiveCanonical roots
            let rootIdx := roots.map fun r => (naive.findIdx? (· == r)).getD 1000000
            ok := ok && ex.dag.toExprs == naive && ex.roots == rootIdx
          | .error _ => ok := false
        return ok
      expect naiveAgree
    itBool "let modes are part of structural identity"
      (distinctCount #[.lam P P, .all P P, .letE true (.value .many) P P P,
        .letE false (.value .many) P P P, .letE false .borrow P P P,
        .letE false (.value .erased) P P P] == 7)
    itBool "lexCompare: proper prefix first, then numeric"
      (lexCompare [1] [1, 0] == .lt && lexCompare [] [0] == .lt &&
        lexCompare [2] [10] == .lt && lexCompare [1, 0] [1] == .gt)
    itBool "compareBytes: unsigned, proper prefix first"
      (compareBytes ⟨#[0x7f]⟩ ⟨#[0x80]⟩ == .lt && compareBytes ⟨#[1]⟩ ⟨#[1, 0]⟩ == .lt &&
        compareBytes ⟨#[0xff]⟩ ⟨#[0x00, 0x00]⟩ == .gt)

/-- The same AST in three pointer layouts: generated (pool-shared), fresh
(deserialized, no sharing), and maximally shared (from the DAG). -/
def representationTestsWith (count : Nat) : Spec :=
  describe "representation independence" do
    it s!"pool-shared, deserialized, DAG-shared and uniform-w1-encoded inputs normalize to identical bytes, by the exact search and by the tiered construction ({count} inputs)" do
      let ok := runGen 13 do
        let mut ok := true
        for i in [0:count] do
          let roots ← genRoots 5 10 3
          let c := wrapRoots roots i
          let fresh := match deConstant (serConstant c) with
            | .ok c' => c'
            | .error _ => c
          let dagShared := match expandConstantSharing c with
            | .ok c' => c'
            | .error _ => c
          let alt := alternateOf c
          let outs := [c, fresh, dagShared, alt].map fun x =>
            (normalizeConstantSharing x).toOption.map serConstant
          let tiered := [c, fresh, dagShared, alt].map fun x =>
            (normalizeConstantSharingTiered .tagN x).toOption.map serConstant
          ok := ok && outs.all (· == outs.head!) && outs.head!.isSome &&
            tiered.all (· == tiered.head!) && tiered.head!.isSome
        return ok
      expect ok

def representationTests : Spec := representationTestsWith 120
def representationTestsPR : Spec := representationTestsWith 50

def cacheTests : Spec :=
  describe "checked expression cache" do
    it "an exact key retrieves its cached ID" do
      let empty : ExprCache Nat := {}
      let key : ExprCache.Key := ⟨0, .var 3⟩
      let cached := empty.insert key 17
      expect (cached.get? key == some 17)
    it "a colliding address with a different expression misses" do
      let empty : ExprCache Nat := {}
      let cached := empty.insert ⟨0, .var 3⟩ 17
      expect (cached.get? ⟨0, .var 4⟩ == none)
    it "collision replacement cannot return the evicted expression's ID" do
      let empty : ExprCache Nat := {}
      let key : ExprCache.Key := ⟨0, .var 3⟩
      let cached := empty.insert key 17
      let collision := cached.insert ⟨0, .var 4⟩ 29
      expect (collision.get? key == none && collision.get? ⟨0, .var 4⟩ == some 29)
    it "equal expression structure can use the same candidate bucket" do
      let empty : ExprCache Nat := {}
      let source : Ixon.Expr := .app (.var 3) (.var 4)
      expect ((empty.insert ⟨0, .app (.var 3) (.var 4)⟩ 17).get? ⟨0, source⟩ == some 17)
    it "let modes are checked before accepting a hit" do
      let empty : ExprCache Nat := {}
      expect ((empty.insert ⟨0, .letE false (.value .many) P P P⟩ 17).get?
        ⟨0, .letE false .borrow P P P⟩ == none)
    it "poisoning a pointer bucket cannot bypass actual ingestion" do
      let empty : ExprCache Nat := {}
      let context : ShareCtx := { resolved := #[], tableSize := 0, entry := none, root := 0, allowShare := false }
      let source : Ixon.Expr := .app (.var 3) (.var 4)
      let poisoned : IngestState :=
        { ptrCache := empty.insert ⟨(exprKey source).address, .sort 8⟩ 999 }
      let ordinary := (ingestExpr {} context 0 source).run {}
      let repaired := (ingestExpr {} context 0 source).run poisoned
      expect (ordinary.toOption.map (fun (id, state) => (id, state.interner.nodes, state.visits)) ==
        repaired.toOption.map (fun (id, state) => (id, state.interner.nodes, state.visits)) && repaired.isOk)
    it "a colliding candidate cannot hide an illegal Share" do
      let empty : ExprCache Nat := {}
      let context : ShareCtx := { resolved := #[], tableSize := 0, entry := none, root := 0, allowShare := false }
      let illegal : Ixon.Expr := .share 0
      let illegalState : IngestState := { ptrCache := empty.insert ⟨(exprKey illegal).address, .var 0⟩ 17 }
      expect (isErr ((ingestExpr {} context 0 illegal).run illegalState) (· == .shareInExpandedInput 0 0))
    it "fast re-expansion rejects the same colliding candidate" do
      let empty : ExprCache Nat := {}
      let context : ShareCtx := { resolved := #[], tableSize := 0, entry := none, root := 0, allowShare := false }
      let source : Ixon.Expr := .app (.var 3) (.var 4)
      let poisoned : IngestState :=
        { ptrCache := empty.insert ⟨(exprKey source).address, .sort 8⟩ 999 }
      let ordinary := (ingestExpr {} context 0 source).run {}
      expect (match ordinary with
       | .ok (id, state) =>
         let target : Dag := ⟨state.interner.nodes⟩
         match reIngestExpr {} target (ReIndex.ofDag target) context 0 source poisoned.ptrCache 0 with
         | .ok actual _ _ => actual == id
         | _ => false
       | .error _ => false)
    it "a 36-level shared DAG keeps linear ingestion work" do
      let context : ShareCtx := { resolved := #[], tableSize := 0, entry := none, root := 0, allowShare := false }
      let dag : Ixon.Expr := (List.range 36).foldl (fun e _ => .app e e) (.var 3)
      expect (match (ingestExpr {} context 0 dag).run {} with
       | .ok (_, state) => state.interner.nodes.size == 37 && state.visits == 37
       | .error _ => false)

def expansionTests : Spec :=
  describe "bounded share expansion" do
    it "expansion equals direct substitution on 100 random backward tables" do
      let validTables := runGen 17 do
        let mut ok := true
        for _ in [0:100] do
          -- A random valid backward table: entry i is a node over earlier Shares and leaves.
          let k := 1 + (← rand 6)
          let mut table : Array Ixon.Expr := #[]
          for i in [0:k] do
            let pick : RGen Ixon.Expr := do
              if i > 0 && (← rand 2) == 0 then pure (.share (← rand i).toUInt64) else genLeaf
            table := table.push (← genNode #[← pick, ← pick, ← pick])
          let roots := #[Ixon.Expr.app (.share (k - 1).toUInt64) (.share 0), .share (← rand k).toUInt64]
          let info : ConstantInfo := .defn ⟨.defn, .safe, {}, 0, roots[0]!, roots[1]!⟩
          let c : Constant := { info, sharing := table, refs := #[], univs := #[] }
          match expandConstantSharing c with
          | .ok c' => ok := ok && constantInfoRoots c'.info == roots.map (naiveExpand table)
          | .error _ => ok := false
        return ok
      expect validTables
    itBool "forward reference is rejected"
      (isErr (optimizeSharingTable #[.share 1, P] #[.share 0])
        (· == .nonBackwardShare 0 1))
    itBool "self reference is rejected"
      (isErr (optimizeSharingTable #[.app (.share 0) P] #[.share 0])
        (· == .nonBackwardShare 0 0))
    itBool "out-of-range root reference is rejected"
      (isErr (optimizeSharingTable #[] #[.share 3]) (· == .shareOutOfRange none 3 0))
    itBool "re-expanding the DAG's own roots gives their IDs; an encoding of another term (the fast path's fallback) gives it a fresh ID"
      (match expandRoots #[arr (chain 2) (chain 2)] with
       | .ok ex =>
         (reexpand {} ex.dag #[] #[arr (chain 2) (chain 2)]).toOption.map (·.2.1) == some ex.roots &&
           ((reexpand {} ex.dag #[] #[arr (chain 3) (chain 3)]).toOption.map
             fun r => r.2.1.all (fun i => decide (i ≥ ex.dag.size))) == some true
       | .error _ => false)
    itBool "out-of-range entry reference is rejected"
      (isErr (optimizeSharingTable #[.share 5] #[P]) (· == .shareOutOfRange (some 0) 5 1))
    itBool "Share in an expanded-root input is rejected"
      (isErr (optimizeSharing #[P, .share 0]) (· == .shareInExpandedInput 1 0))
    itBool "stored depth limit"
      (isErr (optimizeSharing #[chain 20] { maxDepth := 10 }) (exhausted .depth))
    itBool "expanded height limit (shallow entries, deep expansion)"
      (let chainTable (k : Nat) : Array Ixon.Expr :=
         #[.var 0] ++ (Array.range (k - 1)).map fun i => .app (.share i.toUInt64) (.var 0)
       isErr (optimizeSharingTable (chainTable 40) #[.share 39] { maxDepth := 20 })
         (exhausted .depth))
    itBool "distinct-node limit"
      (isErr (optimizeSharing #[chain 30] { maxNodes := 10 }) (exhausted .nodes))
    itBool "walk limit"
      (isErr (optimizeSharing #[chain 30] { maxExprVisits := 10 }) (exhausted .exprVisits))
    itBool "unreachable entries do not affect the result"
      (let c := axiomOf (arr (chain 2) (chain 2))
       let garbage : Constant := { c with
         info := .axio ⟨false, 0, arr (.share 2) (.share 2)⟩,
         sharing := #[.var 7, arr P P, arr P (.share 1), .app (.var 3) (.share 0)] }
       (normalizeConstantSharing garbage).toOption.map serConstant ==
         (normalizeConstantSharing c).toOption.map serConstant)

def sampleInfos : List ConstantInfo :=
  let e (i : Nat) : Ixon.Expr := .var i.toUInt64
  [ .defn ⟨.defn, .safe, {}, 0, e 0, e 1⟩, .axio ⟨false, 0, e 2⟩, .quot ⟨.ind, 0, e 3⟩,
    .recr ⟨false, false, 0, 0, 0, 0, 0, e 4, #[⟨0, e 5⟩, ⟨1, e 6⟩]⟩,
    .recr ⟨false, false, 0, 0, 0, 0, 0, e 4, #[]⟩,
    .cPrj ⟨0, 0, testRefs[0]!⟩, .rPrj ⟨0, testRefs[0]!⟩, .iPrj ⟨0, testRefs[0]!⟩,
    .dPrj ⟨0, testRefs[0]!⟩,
    .muts #[.defn ⟨.defn, .safe, {}, 0, e 7, e 8⟩,
            .indc ⟨false, 0, 0, 0, e 9, #[⟨false, 0, 0, 0, 0, .inherited, e 10⟩, ⟨false, 0, 1, 0, 0, .inherited, e 11⟩]⟩,
            .indc ⟨false, 0, 0, 0, e 12, #[]⟩,
            .recr ⟨false, false, 0, 0, 0, 0, 0, e 13, #[⟨0, e 14⟩]⟩],
    .muts #[] ]

def rootApiTests : Spec :=
  describe "root extraction and reassembly" do
    itBool "constantInfoRoots = Ix.CompileM.constantInfoRootExprs on every kind"
      (sampleInfos.all fun i => constantInfoRoots i == Ix.CompileM.constantInfoRootExprs i)
    itBool "withRoots consumes exactly the extracted roots in order"
      (let shift (rs : Array Ixon.Expr) := rs.map fun r => Ixon.Expr.app r (.var 99)
       sampleInfos.all fun i =>
         let rs := shift (constantInfoRoots i)
         match withRoots i rs with
         | .ok i' => constantInfoRoots i' == rs && (withRoots i' (constantInfoRoots i)).toOption == some i
         | .error _ => false)
    itBool "mapRoots f info = withRoots info ((constantInfoRoots info).map f) on every kind"
      (sampleInfos.all fun i =>
        let g := fun r => Ixon.Expr.app r (.var 98)
        (withRoots i ((constantInfoRoots i).map g)).toOption == some (mapRoots g i))
    itBool "withRoots rejects one root too many / too few"
      (sampleInfos.all fun i =>
        let rs := constantInfoRoots i
        isErr (withRoots i (rs.push P)) (· == .rootCountMismatch rs.size (rs.size + 1)) &&
          (rs.size == 0 || isErr (withRoots i rs.pop) (· == .rootCountMismatch rs.size (rs.size - 1))))

/-! ## Fixed-dictionary optimizer vs enumeration (P2) -/

/-- Every ordered dictionary over the DAG's terms (up to `maxOrders`), with
table indices shifted by each offset so Share widths cross every boundary;
checks `C_M` and the materialized bytes against exhaustive enumeration. -/
def dictionaryAgreement (dag : Dag) (offsets : List Nat) (maxOrders : Nat) (stride : Nat := 1) :
    Nat × Option String := Id.run do
  let p := Prep.ofDag dag
  let n := dag.size
  let mut checked := 0
  let orders := ((orderedSubsets n (List.range n)).zipIdx.filter fun (_, i) => i % stride == 0).map (·.1)
  for order in orders.take maxOrders do
    for off in offsets do
      let index := indexOfPairs n (order.zipIdx.map fun (t, i) => (t, i + off))
      match p.materialize index (Array.range n) {} with
      | .error e => return (checked, some s!"materialize error {reprStr e} order={order} off={off}")
      | .ok (exprs, cost, _) =>
        for t in [0:n] do
          match (bestPart dag index {} t).run {} with
          | .error e => return (checked, some s!"enumeration error {reprStr e}")
          | .ok ((_, bytes), _) =>
            checked := checked + 1
            unless cost[t]! == bytes.size && serExpr exprs[t]! == bytes do
              return (checked, some s!"order={order} off={off} term={t} C_M={cost[t]!} enum={bytes.size} got={hexOf (serExpr exprs[t]!)} want={hexOf bytes}")
  return (checked, none)

def dictOffsets : List Nat := [0, 5, 250, 65530, 2^24 - 3, 2^32 - 3, 2^56 - 3, 2^64 - 8]

/-- Reference `C_M`: for every telescope node, walk every inline prefix
length `j = 1..l` directly (quadratic in the spine length). -/
def walkCosts (dag : Dag) (width : Array (Option Nat)) : Array Nat := Id.run do
  let mut cost : Array Nat := Array.replicate dag.size 0
  for t in [0:dag.size] do
    let node := dag.node t
    let fam := node.head.family
    let mut inl := 0
    if fam == .none then
      inl := node.children.foldl (fun acc c => acc + cost[c]!) node.head.ownBytes
    else
      let mut l := 0
      let mut cur := t
      for _ in [0:dag.size] do
        if (dag.node cur).head.family == fam then
          l := l + 1
          cur := (dag.node cur).spineNext
        else break
      cur := t
      let mut sides := 0
      let mut best : Option Nat := none
      for j in [1:l + 1] do
        let cn := dag.node cur
        sides := sides + cn.sideExtra + cost[cn.sideChild]!
        let nxt := cn.spineNext
        let cand? : Option Nat :=
          if j < l then (width[nxt]!).map fun w => tag4Size j + sides + w
          else some (tag4Size j + sides + cost[nxt]!)
        if let some cand := cand? then
          best := some (match best with | some b => min b cand | none => cand)
        cur := nxt
      inl := best.getD 0
    cost := cost.set! t (match width[t]! with | some w => min inl w | none => inl)
  return cost

/-- Long spines over a small pool: App spines and Lam and All telescopes,
nested in each other. -/
def genSpines : RGen (Array Ixon.Expr) := do
  let pool ← (List.range 4).toArray.mapM fun _ => genLeaf
  let mut roots : Array Ixon.Expr := #[]
  for _ in [0:1 + (← rand 3)] do
    let len := 5 + (← rand 40)
    let mut e := pool[← rand pool.size]!
    for _ in [0:len] do
      let a := pool[← rand pool.size]!
      e ← match ← rand 5 with
        | 0 | 1 => pure (.app e a)
        | 2 => pure (.lam a e)
        | 3 => pure (.all a e)
        | _ => pure (arr a e)
    roots := roots.push e
    roots := roots.push (.app e e)
  return roots

def spineWalkTests : Spec :=
  describe "telescope evaluation vs full spine walk" do
    it "200 long-spine DAGs with random dictionaries (widths 1–5): costs equal the O(l) walk over every cut" do
      let (checked, err) := runGen 53 do
        let mut checked := 0
        let mut err : Option String := none
        for i in [0:200] do
          if err.isSome then break
          let roots ← genSpines
          match expandRoots roots with
          | .ok ex =>
            let n := ex.dag.size
            let p := Prep.ofDag ex.dag
            let mut width : Array (Option Nat) := Array.replicate n none
            for t in [0:n] do
              if (← rand 3) == 0 then
                let idx := [← rand 8, 8 + (← rand 300), 65530 + (← rand 12), 2^32 + (← rand 3)][← rand 4]!
                width := width.set! t (some (shareWidth idx))
            checked := checked + 1
            unless (p.costsAll width).1 == walkCosts ex.dag width &&
                p.base == walkCosts ex.dag (Array.replicate n none) do
              err := some s!"case {i}: available-descendant evaluation differs from the full spine walk"
          | .error e => err := some s!"case {i}: error {reprStr e}"
        return (checked, err)
      if let some m := err then fail m
      expect (checked == 200) s!"checked {checked} != 200"

def deepTests : Spec :=
  describe "deep inputs" do
    it "10000-deep argument nesting and a 10000-binder telescope optimize under default limits" do
      let d := 10000
      let nested : Ixon.Expr :=
        (List.range d).foldl (fun acc i => .app (.var (i % 2).toUInt64) acc) (.sort 0)
      let telescope : Ixon.Expr :=
        (List.range d).foldl (fun acc i => .lam (.var (i % 3).toUInt64) acc) (.sort 0)
      withOk "deep" (optimizeSharing #[nested, telescope]) fun r =>
        expect (r.variableBytes == r.unsharedBytes &&
          r.variableBytes == exprSize nested + exprSize telescope + 1 &&
          r.variableBytes == (serExpr nested).size + (serExpr telescope).size + 1)
          s!"variableBytes={r.variableBytes}, unsharedBytes={r.unsharedBytes}"

def dictionaryTestsWith (fixMax fixOffMax genTarget genMaxOrders : Nat) : Spec :=
  let fixtures : List (String × Array Ixon.Expr) :=
    [("T2→T2", #[arr (chain 2) (chain 2)]), ("A→A→B→B", #[tiedMinimaRoot]),
     ("mixed spines", #[.app (.app (.lam P (arr P P)) (arr P P)) (.app (.var 0) (arr P P))]),
     ("let/prj", #[.letE false (.value .many) (arr P P) (.prj 0 1 (.app (.var 0) P)) (.app (.var 0) P)])]
  describe "fixed-dictionary optimizer vs enumeration" do
    for (name, roots) in fixtures do
      it s!"{name}: C_M and byte-least materialization = enumeration" do
        withOk name (expandRoots roots) fun ex => do
          -- Up to `fixMax` of the ordered dictionaries (strided when there are
          -- more), each at indices 0.., and `fixOffMax` of them at every index offset.
          let total := (orderedSubsets ex.dag.size (List.range ex.dag.size)).length
          let stride := if total > fixMax then 7 else 1
          let (_, e1) := dictionaryAgreement ex.dag [0] fixMax stride
          let (_, e2) := dictionaryAgreement ex.dag dictOffsets fixOffMax (stride * 3)
          if let some m := e1.or e2 then fail m
    it s!"generated inputs (N ≤ 5, up to {genTarget} cases): (dictionary, term) cases agree" do
      let (_, genErr) := runGen 19 do
        let mut checked := 0
        let mut err : Option String := none
        let mut cases := 0
        for _ in [0:400] do
          if cases ≥ genTarget || err.isSome then break
          let roots ← genRoots 3 4 2
          match expandRoots roots with
          | .ok ex =>
            if ex.dag.size ≤ 5 then
              cases := cases + 1
              let (c, e) := dictionaryAgreement ex.dag [0, 6, 254] genMaxOrders
              checked := checked + c
              if let some m := e then err := some s!"{m} roots={reprStr roots}"
          | .error _ => pure ()
        return (checked, err)
      if let some m := genErr then fail m

def dictionaryTests : Spec := dictionaryTestsWith 2000 300 60 400
def dictionaryTestsPR : Spec := dictionaryTestsWith 120 40 15 80

/-! ## Full optimizer vs exhaustive oracle (P1/P3) -/

/-- Compare the optimizer with the oracle on generated constants. Inputs whose
oracle enumeration exceeds the per-case oracle budget are skipped and
counted (the optimizer is not given a budget). Returns
`(checked, skipped, tables, first failure)`. -/
def oracleAgreement (seed cases maxN : Nat) (product : Bool) : Nat × Nat × Nat × Option String :=
  runGen seed do
    let mut checked := 0
    let mut skipped := 0
    let mut attempts := 0
    let mut err : Option String := none
    let mut tables := 0
    let budget : Limits := { maxOracleVariants := 400000 }
    while checked < cases && attempts < 20 * cases && err.isNone do
      attempts := attempts + 1
      let roots ← genRoots 3 5 3
      if distinctCount roots > maxN || distinctCount roots == 0 then continue
      let c := wrapRoots roots attempts
      match optimizeSharingTable c.sharing (constantInfoRoots c.info),
          normalizeConstantSharing c, oracleConstant c budget product with
      | .ok r, .ok n, .ok (oc, o) =>
        checked := checked + 1
        tables := tables + o.work.tables
        unless serConstant n == serConstant oc && r.tableTerms == o.table do
          err := some s!"case {attempts}: exact={hexOf (serConstant n)} Q={r.tableTerms} oracle={hexOf (serConstant oc)} Q={o.table} roots={reprStr roots}"
      | .ok _, .ok _, .error (.resourceExhausted .oracleVariants _) =>
        skipped := skipped + 1
      | .error e, _, _ | _, .error e, _ | _, _, .error e =>
        err := some s!"case {attempts}: error {reprStr e} roots={reprStr roots}"
    return (checked, skipped, tables, err)

def oracleTestsWith (partCases prodCases : Nat) : Spec :=
  describe "optimizer vs exhaustive oracle (full key)" do
    it s!"per-part oracle: {partCases} generated constants (N ≤ 6, all kinds and let modes) agree on bytes and table IDs" do
      let (n1, s1, t1, e1) := oracleAgreement 23 partCases 6 false
      if let some m := e1 then fail m
      expect (n1 == partCases) s!"checked {n1}/{partCases} ({t1} tables, {s1} skipped)"
    it s!"full-product oracle: {prodCases} generated constants (N ≤ 4) agree" do
      let (n2, s2, t2, e2) := oracleAgreement 29 prodCases 4 true
      if let some m := e2 then fail m
      expect (n2 == prodCases) s!"checked {n2}/{prodCases} ({t2} tables, {s2} skipped)"

def oracleTests : Spec := oracleTestsWith 150 40
def oracleTestsPR : Spec := oracleTestsWith 30 10

/-- Unit-width relaxation (§4.1): with no telescope merging and at most 8
positive-weight terms of indegree ≥ 2, the minimum variable length is
`R + k* + tag0(k*) + Σ w(t)` over distinct terms, `w(t)` = node bytes − 1
with every child written as one byte. -/
def unitWidthLength (roots : Array Ixon.Expr) : Option Nat := Id.run do
  let distinct := naiveCanonical roots
  let stub (e : Ixon.Expr) : Ixon.Expr := match e with
    | .prj t f _ => .prj t f (.var 0)
    | .app .. => .app (.var 0) (.var 0)
    | .lam .. => .lam (.var 0) (.var 0)
    | .all .. => .all (.var 0) (.var 0)
    | .letE nonDep mode .. => .letE nonDep mode (.var 0) (.var 0) (.var 0)
    | e => e
  let w (e : Ixon.Expr) : Nat := (serExpr (stub e)).size - 1
  let indeg (t : Ixon.Expr) : Nat :=
    distinct.foldl (fun acc s => acc + ((exprChildren s).filter (· == t)).length) 0 +
      (roots.filter (· == t)).size
  let kstar := (distinct.filter fun t => w t > 0 && indeg t ≥ 2).size
  if kstar > 8 then return none
  return some (roots.size + kstar + tag0Size kstar +
    distinct.foldl (fun acc t => acc + w t) 0)

def unitWidthTestsWith (target minRequired : Nat) : Spec :=
  describe "unit-width relaxation oracle" do
    it s!"exact length = unit-width optimum on up to {target} merge-free generated inputs (≥ {minRequired})" do
      let (checked, err) := runGen 31 do
        let mut checked := 0
        let mut err : Option String := none
        for i in [0:600] do
          if checked ≥ target || err.isSome then break
          let roots ← genRoots 6 14 4 (noMerge := true)
          let some expected := unitWidthLength roots | continue
          match optimizeSharing roots with
          | .ok r =>
            checked := checked + 1
            unless r.variableBytes == expected do
              err := some s!"case {i}: exact={r.variableBytes} unit={expected} roots={reprStr roots}"
          | .error e => err := some s!"case {i}: error {reprStr e}"
        return (checked, err)
      if let some m := err then fail m
      expect (decide (checked ≥ minRequired)) s!"checked {checked} < {minRequired}"

def unitWidthTests : Spec := unitWidthTestsWith 150 100
def unitWidthTestsPR : Spec := unitWidthTestsWith 50 50

/-- Independent atoms: for a fixed stored set the optimal order gives the
cheapest slots to the most-used atoms, so a brute force over subsets gives
the exact minimum, including the width-2 slots from index 8. -/
def atomsBrute (sizes occs : Array Nat) : Nat := Id.run do
  let n := sizes.size
  let mut best := 0
  for mask in [0:2 ^ n] do
    let inS (i : Nat) := (mask >>> i) % 2 == 1
    let stored := ((List.range n).filter inS).toArray.qsort fun a b => occs[a]! > occs[b]!
    let mut cost := tag0Size stored.size
    for h : slot in [0:stored.size] do
      let a := stored[slot]
      cost := cost + sizes[a]! + occs[a]! * shareWidth slot
    for i in [0:n] do
      if !inS i then cost := cost + occs[i]! * sizes[i]!
    if mask == 0 || cost < best then best := cost
  return best

def atomsTests : Spec :=
  describe "multi-width buckets vs brute force" do
    it "independent atoms (9–11 atoms, slots cross index 8): 12 cases equal the brute-force minimum" do
      let (checked, err) := runGen 37 do
        let mut checked := 0
        let mut err : Option String := none
        for i in [0:12] do
          let n := 9 + (← rand 3)
          let mut atoms : Array Ixon.Expr := #[]
          let mut occs : Array Nat := #[]
          for j in [0:n] do
            atoms := atoms.push (.ref (j + 2).toUInt64 (Array.replicate (← rand 4) 0))
            occs := occs.push (2 + (← rand 12))
          let roots := (Array.range n).foldl (fun acc j => acc ++ Array.replicate occs[j]! atoms[j]!) #[]
          let sizes := atoms.map exprSize
          let expected := atomsBrute sizes occs
          match optimizeSharing roots with
          | .ok r =>
            checked := checked + 1
            unless r.variableBytes == expected do
              err := some s!"case {i}: exact={r.variableBytes} brute={expected} occs={occs} sizes={sizes}"
          | .error e => err := some s!"case {i}: error {reprStr e}"
        return (checked, err)
      if let some m := err then fail m
      expect (checked == 12) s!"checked {checked} != 12"

/-! ## §2 fixtures -/

def witness2 : Constant := axiomOf (arr (chain 2) (chain 2))

def witnessTests : Spec :=
  describe "fixture T2 → T2 (17 → 15)" do
    it "the 17-byte encoding decodes to T2 → T2" do
      -- A valid 17-byte encoding of T2 → T2, two bytes above the minimum.
      let altBytes := ByteArray.mk #[0xd2, 0x00, 0x00, 0x91, 0xb1, 0xb1, 0x02, 0x91,
        0x00, 0x00, 0x91, 0x00, 0xb0, 0x00, 0x01, 0x00, 0x00]
      let alt := (deConstant altBytes).toOption.getD witness2
      expect (hexOf (serConstant alt) == "d2000091b1b1029100009100b000010000" &&
        (expandConstantSharing alt).toOption.map (constantInfoRoots ·.info) ==
          some (constantInfoRoots witness2.info))
    itBool "unshared is 16 bytes" (cbytes witness2 == 16)
    it "exact table term IDs = [T2] = [2]" do
      withOk "exact" (optimizeSharingTable #[] (constantInfoRoots witness2.info)) fun r =>
        expect (r.tableTerms == #[2])
    it "exact bytes d2000091b0b0019200000000010000 (15)" do
      withOk "exact" (normalizeConstantSharing witness2) fun n =>
        expect (hexOf (serConstant n) == "d2000091b0b0019200000000010000")
    it "normalizing the 17-byte encoding gives the same 15 bytes" do
      let altBytes := ByteArray.mk #[0xd2, 0x00, 0x00, 0x91, 0xb1, 0xb1, 0x02, 0x91,
        0x00, 0x00, 0x91, 0x00, 0xb0, 0x00, 0x01, 0x00, 0x00]
      let alt := (deConstant altBytes).toOption.getD witness2
      withOk "exact from the 17-byte encoding" (normalizeConstantSharing alt) fun n =>
        expect (hexOf (serConstant n) == "d2000091b0b0019200000000010000")
    it "per-part oracle: 15-byte unique minimum over 65 ordered tables" do
      withOk "oracle" (oracleConstant witness2) fun (oc, o) =>
        expect (hexOf (serConstant oc) == "d2000091b0b0019200000000010000" &&
          o.work.tables == 65 && o.minima.size == 1)

/-- Full-product brute-force oracle over all 3,061,082 complete candidates for
`witness2` (nightly sweep). -/
def witnessProductOracleTests : Spec :=
  describe "fixture T2 → T2 (full-product oracle)" do
    it "full-product oracle: 3061082 complete candidates, 15-byte unique minimum" do
      withOk "product oracle" (oracleConstant witness2 {} true) fun (oc, o) =>
        expect (hexOf (serConstant oc) == "d2000091b0b0019200000000010000" &&
          o.work.candidates == 3061082 && o.minima.size == 1)

def witness16 : Constant := axiomOf (arr (chain 16) (chain 16))

def t16Tests : Spec :=
  describe "fixture T16 → T16" do
    itBool "unshared is 46 bytes" (cbytes witness16 == 46)
    itBool "storing only T16 is 30 bytes"
      (let only16 : Constant := { witness16 with
         info := .axio ⟨false, 0, arr (.share 0) (.share 0)⟩, sharing := #[chain 16] }
       cbytes only16 == 30)
    it "exact certified minimum ≤ 30 bytes" do
      withOk "exact" (optimizeSharingTable #[] (constantInfoRoots witness16.info)) fun r =>
        withOk "exact" (normalizeConstantSharing witness16) fun n =>
          expect (decide (cbytes n ≤ 30) && cbytes n == r.variableBytes + 7)
            s!"cbytes={cbytes n}, variableBytes={r.variableBytes}"

/-- The nine-Ref fixture, built as in the production probe: atoms sorted by
the blake3 hash of their encoding, each twice, then 98 more uses of the last (hot) atom; one
recursor with the first root as type and the rest as rule bodies. -/
def nineRef : Constant × Ixon.Expr :=
  let atoms0 : Array Ixon.Expr := (Array.range 9).map fun i => .ref i.toUInt64 #[0, 0, 0]
  let atoms := atoms0.qsort fun a b =>
    compareBytes (Address.blake3 (serExpr a)).hash (Address.blake3 (serExpr b)).hash == .lt
  let hot := atoms[8]!
  let roots := atoms.foldl (fun acc a => acc ++ #[a, a]) #[] ++ Array.replicate 98 hot
  let c : Constant := {
    info := .recr ⟨false, false, 0, 0, 0, 0, 0, roots[0]!,
      (roots.extract 1 roots.size).map fun rhs => ⟨0, rhs⟩⟩,
    sharing := #[],
    refs := (Array.range 9).map fun i => Address.blake3 (u64LE i.toUInt64),
    univs := #[.zero] }
  (c, hot)

def nineRefTests : Spec :=
  describe "fixture nine independent Refs (677 → 579)" do
    it "hot atom is Ref(2,[0,0,0])" do
      let (_, hot) := nineRef
      expect (hot == .ref 2 #[0, 0, 0])
    it "hash order: 677 bytes, hot atom in slot 8" do
      let (c, hot) := nineRef
      let atoms := (constantInfoRoots c.info).foldl
        (fun acc a => if acc.contains a then acc else acc.push a) #[]
      let tableWith (table : Array Ixon.Expr) : Constant :=
        let idxOf (a : Ixon.Expr) : Nat := (table.findIdx? (· == a)).getD 0
        let roots := (constantInfoRoots c.info).map fun a => Ixon.Expr.share (idxOf a).toUInt64
        match withRoots c.info roots with
        | .ok info => { c with info, sharing := table }
        | .error _ => c
      let hashOrder := tableWith atoms
      expect (cbytes hashOrder == 677 && atoms.size == 9 && atoms[8]? == some hot)
    it "same entries, frequency order: 579 bytes" do
      let (c, hot) := nineRef
      let atoms := (constantInfoRoots c.info).foldl
        (fun acc a => if acc.contains a then acc else acc.push a) #[]
      let tableWith (table : Array Ixon.Expr) : Constant :=
        let idxOf (a : Ixon.Expr) : Nat := (table.findIdx? (· == a)).getD 0
        let roots := (constantInfoRoots c.info).map fun a => Ixon.Expr.share (idxOf a).toUInt64
        match withRoots c.info roots with
        | .ok info => { c with info, sharing := table }
        | .error _ => c
      let freqTable := #[hot] ++ (atoms.filter (· != hot))
      expect (cbytes (tableWith freqTable) == 579)
    it "exact: 579 bytes, table IDs [0..8], hot atom at a width-1 slot" do
      let (c, hot) := nineRef
      withOk "exact" (optimizeSharingTable #[] (constantInfoRoots c.info)) fun r =>
        withOk "exact" (normalizeConstantSharing c) fun n =>
          expect (cbytes n == 579 && r.tableTerms == #[0, 1, 2, 3, 4, 5, 6, 7, 8] &&
            ((n.sharing.findIdx? (· == hot)).map fun i => decide (i < 8)) == some true)

/-- Fast PR check for the tied-minima fixture: exact solver picks `[A]`. -/
def tiedMinimaExactTests : Spec :=
  describe "fixture three 21-byte minima (exact)" do
    it "exact picks the [A] minimum (table IDs [2])" do
      let c := axiomOf tiedMinimaRoot #[.zero, .succ .zero]
      let onlyA := "d2000094b0b0910001000101910000" ++ "000200010000"
      withOk "exact" (optimizeSharingTable #[] (constantInfoRoots c.info)) fun r =>
        withOk "exact" (normalizeConstantSharing c) fun n =>
          expect (hexOf (serConstant n) == onlyA && r.tableTerms == #[2])

/-- Full 13,700-table exhaustive oracle check for the tied-minima fixture
(nightly sweep). -/
def tiedMinimaTests : Spec :=
  describe "fixture three 21-byte minima" do
    it "oracle: minimum 21 over 13700 ordered tables; [A], [A,B] and [B,A] attain it; the least table [A] wins" do
      let c := axiomOf tiedMinimaRoot #[.zero, .succ .zero]
      -- Table [A]: the root is one telescope with binders `Share 0`, `Share 0`, `B`, `P`
      -- over `Type`; tables [A,B] and [B,A]: the root is cut at `B`, all `Share`s.
      let onlyA := "d2000094b0b0910001000101910000" ++ "000200010000"
      let first := "d2000093b0b0b1b10291000091000100020001" ++ "0000"
      let second := "d2000093b1b1b0b00291000191000000020001" ++ "0000"
      withOk "oracle" (oracleConstant c) fun (oc, o) =>
        expect (cbytes oc == 21 && o.work.tables == 13700 && o.minima.size == 3 &&
          o.minima.any (hexOf · == first) && o.minima.any (hexOf · == second) &&
          hexOf (serConstant oc) == onlyA && o.table == #[2])
    it "exact picks the [A] minimum (table IDs [2])" do
      let c := axiomOf tiedMinimaRoot #[.zero, .succ .zero]
      let onlyA := "d2000094b0b0910001000101910000" ++ "000200010000"
      withOk "exact" (optimizeSharingTable #[] (constantInfoRoots c.info)) fun r =>
        withOk "exact" (normalizeConstantSharing c) fun n =>
          expect (hexOf (serConstant n) == onlyA && r.tableTerms == #[2])

/-- A parent stored before its separately stored descendant (which the
parent's entry therefore inlines): seven hot atoms take slots 0–6, the
50-use parent `P = App(Var 0, D)` takes slot 7 and `D` (3 more uses) slot 8. -/
def orderingTests : Spec :=
  describe "ordering: parent before descendant" do
    it "variable bytes = 804, table IDs = [2..8, 9 (P), 1 (D)], P's entry inlines D" do
      let d : Ixon.Expr := .ref 1 #[0, 0, 0]
      let p : Ixon.Expr := .app (.var 0) d
      let hots := (Array.range 7).map fun i => Ixon.Expr.ref (i + 2).toUInt64 #[0, 0, 0]
      let roots := hots.foldl (fun acc h => acc ++ Array.replicate 100 h) #[] ++
        Array.replicate 50 p ++ Array.replicate 3 d
      withOk "exact" (optimizeSharing roots) fun r =>
        expect (r.variableBytes == 804 && r.tableTerms == #[2, 3, 4, 5, 6, 7, 8, 9, 1] &&
          r.sharing[7]? == some p)

/-! ## Properties on generated inputs -/

def propertyTestsWith (target : Nat) : Spec :=
  describe "properties on generated inputs" do
    it s!"{target} constants: exact ≤ unshared, exact ≤ uniform-w1, idempotent, normalize(uniform-w1) = normalize(expanded) = exact, check=minimum, decomposition, expansion preserved" do
      let (checked, err) := runGen 41 do
        let mut checked := 0
        let mut err : Option String := none
        for i in [0:target] do
          if err.isSome then break
          let roots ← genRoots 5 12 4
          let c := wrapRoots roots i
          let alt := alternateOf c
          match normalizeConstantSharing c, optimizeSharingTable #[] (constantInfoRoots c.info) with
          | .ok n, .ok r =>
            checked := checked + 1
            let idem := (normalizeConstantSharing n).toOption.map serConstant == some (serConstant n)
            let fromAlt := (normalizeConstantSharing alt).toOption.map serConstant == some (serConstant n)
            let fromExpanded := ((expandConstantSharing n).toOption.bind
              fun e => (normalizeConstantSharing e).toOption).map serConstant == some (serConstant n)
            let minimum := match checkExactMinimum n with
              | .ok .minimum => true
              | _ => false
            let altCheck := match checkExactMinimum alt with
              | .ok .minimum => serConstant alt == serConstant n
              | .ok (.notMinimum exp) => exp == serConstant n
              | .error _ => false
            let f := fixedConstantBytes c
            let fixedOk := cbytes n == f + r.variableBytes && cbytes c == f + r.unsharedBytes
            let expandsBack := (expandConstantSharing n).toOption.map (fun e => constantInfoRoots e.info) ==
              some (constantInfoRoots c.info)
            unless cbytes n ≤ cbytes c && cbytes n ≤ cbytes alt && idem && fromAlt &&
                fromExpanded && minimum && altCheck && fixedOk && expandsBack do
              err := some s!"case {i}: exact={cbytes n} unshared={cbytes c} uniform-w1={cbytes alt} idem={idem} fromAlt={fromAlt} fromExpanded={fromExpanded} minimum={minimum} altCheck={altCheck} fixed={fixedOk} expands={expandsBack} roots={reprStr roots}"
          | .error e, _ | _, .error e => err := some s!"case {i}: error {reprStr e}"
        return (checked, err)
      if let some m := err then fail m
      expect (checked == target) s!"checked {checked} != {target}"

def propertyTests : Spec := propertyTestsWith 250
def propertyTestsPR : Spec := propertyTestsWith 60

/-- LB pruning never changes a result: compare
with the search with pruning disabled, on inputs with 9–11 candidates
(beyond the oracle's reach; tables can cross the 8-slot width boundary). -/
def pruningTestsWith (genTarget wideTarget : Nat) : Spec :=
  describe "pruning never changes the result" do
    it s!"{genTarget} inputs with 9–11 candidates: pruned search = unpruned search" do
      let (checked, _, err) := runGen 43 do
        let mut checked := 0
        let mut wide := 0
        let mut err : Option String := none
        for i in [0:4000] do
          if checked ≥ genTarget || err.isSome then break
          let roots ← genRoots 8 24 6
          let cands := match sharingProfile (wrapRoots roots 0) with
            | .ok p => p.candidates
            | .error _ => 0
          if cands < 9 || cands > 11 then continue
          match optimizeSharing roots,
              optimizeSharing roots { prune := false } with
          | .ok a, .ok b =>
            checked := checked + 1
            if a.sharing.size > 8 then wide := wide + 1
            unless a.sharing == b.sharing && a.roots == b.roots &&
                a.tableTerms == b.tableTerms && a.variableBytes == b.variableBytes do
              err := some s!"case {i}: pruned={a.variableBytes} {a.tableTerms} unpruned={b.variableBytes} {b.tableTerms}"
          | .error e, _ | _, .error e => err := some s!"case {i}: error {reprStr e}"
        return (checked, wide, err)
      if let some m := err then fail m
      expect (checked == genTarget) s!"checked {checked} != {genTarget}"
    it s!"{wideTarget} atom-heavy inputs with ≤ 12 candidates: pruned = unpruned" do
      -- Many profitable atoms plus nested nodes over them: optimal tables
      -- usually exceed 8 entries, so widths 1 and 2 compete.
      let genWide : RGen (Array Ixon.Expr) := do
        let n := 9 + (← rand 3)
        let atoms : Array Ixon.Expr := (Array.range n).map fun j =>
          .ref (j + 2).toUInt64 (Array.replicate (1 + j % 3) 0)
        let mut roots : Array Ixon.Expr := #[]
        for j in [0:n] do
          for _ in [0:2 + (← rand 4)] do roots := roots.push atoms[j]!
        for _ in [0:(← rand 3)] do
          let a := atoms[← rand n]!
          let b := atoms[← rand n]!
          let node : Ixon.Expr := if (← rand 2) == 0 then .app a b else arr a b
          for _ in [0:2 + (← rand 2)] do roots := roots.push node
        return roots
      let (wChecked, wWide, wErr) := runGen 47 do
        let mut checked := 0
        let mut wide := 0
        let mut err : Option String := none
        for i in [0:400] do
          if checked ≥ wideTarget || err.isSome then break
          let roots ← genWide
          let cands := match sharingProfile (wrapRoots roots 0) with
            | .ok p => p.candidates
            | .error _ => 0
          if cands > 12 then continue
          match optimizeSharing roots,
              optimizeSharing roots { prune := false } with
          | .ok a, .ok b =>
            checked := checked + 1
            if a.sharing.size > 8 then wide := wide + 1
            unless a.sharing == b.sharing && a.roots == b.roots &&
                a.tableTerms == b.tableTerms && a.variableBytes == b.variableBytes do
              err := some s!"wide case {i}: pruned={a.variableBytes} {a.tableTerms} unpruned={b.variableBytes} {b.tableTerms}"
          | .error e, _ | _, .error e => err := some s!"wide case {i}: error {reprStr e}"
        return (checked, wide, err)
      if let some m := wErr then fail m
      expect (wChecked == wideTarget && decide (wWide > 0)) s!"wChecked={wChecked}, wWide={wWide}"

def pruningTests : Spec := pruningTestsWith 25 15
def pruningTestsPR : Spec := pruningTestsWith 5 5

def profileTests : Spec :=
  describe "sharing profile" do
    it "T2→T2: N=4, 3 repeated, 2 candidates (T1,T2), height 3, unshared 9 variable bytes" do
      withOk "T2 → T2" (sharingProfile witness2) fun p =>
        expect (p.distinctSubterms == 4 && p.repeated == 3 && p.candidates == 2 && p.height == 3 &&
          p.unsharedBytes == 9 && p.inputBytes == 9)
    it "T16→T16: N=18, 16 candidates, unshared 39 variable bytes" do
      withOk "T16 → T16" (sharingProfile witness16) fun p =>
        expect (p.distinctSubterms == 18 && p.candidates == 16 && p.unsharedBytes == 39)

/-! ## Safety, limits, empty input -/

def staleProjection : Constant :=
  let info : ConstantInfo := .iPrj ⟨0, testRefs[0]!⟩
  { info, sharing := #[arr P P, .share 0], refs := testRefs, univs := #[] }

def safetyTests : Spec :=
  describe "resource limits and edge cases" do
    itBool "state limit → resourceExhausted, no result"
      (isErr (optimizeSharing (constantInfoRoots witness16.info) { maxStates := 5 }) (exhausted .states))
    itBool "transition limit → resourceExhausted"
      (isErr (optimizeSharing (constantInfoRoots witness16.info) { maxTransitions := 5 }) (exhausted .transitions))
    itBool "cost-evaluation limit → resourceExhausted"
      (isErr (optimizeSharing (constantInfoRoots witness16.info) { maxCostEvals := 50 }) (exhausted .costEvals))
    itBool "output-byte limit → resourceExhausted"
      (isErr (optimizeSharing (constantInfoRoots witness16.info) { maxOutputBytes := 10 }) (exhausted .outputBytes))
    itBool "materialization limit → resourceExhausted"
      (isErr (optimizeSharing (constantInfoRoots witness16.info) { maxMaterialize := 3 }) (exhausted .materialize))
    itBool "oracle table limit → resourceExhausted"
      (isErr (oracleConstant witness2 { maxOracleTables := 10 }) (exhausted .oracleTables))
    itBool "oracle variant limit → resourceExhausted"
      (isErr (oracleConstant witness2 { maxOracleVariants := 100 }) (exhausted .oracleVariants))
    itBool "larger limits do not change a successful result"
      (let roots := constantInfoRoots witness16.info
       (optimizeSharing roots { maxStates := 1 <<< 30, maxCostEvals := 1 <<< 40 }).toOption.map (·.sharing) ==
         (optimizeSharing roots).toOption.map (·.sharing))
    it "no roots: empty table, 1 variable byte (the table count)" do
      withOk "empty input" (optimizeSharing #[]) fun r =>
        expect (r.sharing.isEmpty && r.roots.isEmpty && r.variableBytes == 1)
    it "a constant without roots drops its (unreachable) table" do
      withOk "projection with a stale table" (normalizeConstantSharing staleProjection) fun n =>
        expect n.sharing.isEmpty
    itBool "repeated identical roots can be shared as whole roots"
      ((optimizeSharing #[chain 5, chain 5, chain 5]).toOption.map (·.sharing.size) == some 1)

/-! ## Randomized codec properties -/

def slimTests : Spec :=
  describe "randomized codec properties" do
    prop "exprSize = serExpr size" fun (e : Ixon.Expr) => exprSize e == (serExpr e).size
    prop "Constant length decomposition" fun (c : Constant) => decompositionHolds c

/-! ## Limits: defaults and overrides -/

def overrideFails (e : Except String Limits) : Bool :=
  match e with
  | .ok _ => false
  | .error _ => true

/-- Override specs and the `states` limit each sets (`none`: rejected). Values
are ASCII digits, `2^k` or `max` (no sign, no `_` separator, no other
spelling); items and keys are trimmed of space, tab, line feed and carriage
return only. -/
def limitSpecParity : List (String × Option Nat) := [
  ("states=5", some 5),
  ("states=007", some 7),
  (" states = 2^10 ", some (2 ^ 10)),
  ("states=2^0", some 1),
  ("states=2^63", some (2 ^ 63)),
  ("states=max", some limitMax),
  ("states=18446744073709551615", some limitMax),
  ("unbounded", some limitMax),
  ("", some (2 ^ 40)),
  (",,states=5,,", some 5),
  ("\tstates=5\n", some 5),
  ("states=5\r", some 5),
  ("states= 5", some 5),
  ("states =5", some 5),
  ("states=1_000", none),
  ("states=2^1_0", none),
  ("states=+5", none),
  ("states=2^+5", none),
  ("states=-1", none),
  ("states=1e3", none),
  ("states=0x10", none),
  ("states=2^64", none),
  ("states=18446744073709551616", none),
  ("states=", none),
  ("states=2^", none),
  ("=5", none),
  ("states", none),
  ("a=b=c", none),
  ("bogus=1", none),
  ("STATES=5", none),
  ("states=MAX", none),
  ("states=\u00a05", none),
  ("states=\uff15", none),
  ("states=\x0c5", none),
  ("states=\x0b5", none)]

/-- The specs of `limitSpecParity` whose verdict differs from the list. -/
def limitSpecMismatches : List String :=
  limitSpecParity.filterMap fun (spec, want) =>
    let got := match ({} : Limits).withOverrides spec with
      | .ok l => some l.maxStates
      | .error _ => none
    if got == want then none else some spec

def limitTests : Spec :=
  describe "limits" do
    itBool "the defaults are the safety net"
      (let d : Limits := {}
       d.maxExprVisits == 2 ^ 40 && d.maxDepth == 2 ^ 20 && d.maxNodes == 2 ^ 32 &&
         d.maxStates == 2 ^ 40 && d.maxTransitions == 2 ^ 40 && d.maxCostEvals == 2 ^ 50 &&
         d.maxOutputBytes == 2 ^ 40 && d.maxMaterialize == 2 ^ 40 &&
         d.maxMaterializeWork == 2 ^ 56 && d.maxKnapsackCells == 2 ^ 28)
    itBool "overrides set the named limits, left to right"
      (let d : Limits := {}
       match d.withOverrides " states = 2^10 ,cost_evals=12345, output_bytes=max,, states=2^11" with
       | .ok l => l.maxStates == 2048 && l.maxCostEvals == 12345 &&
           l.maxOutputBytes == limitMax && l.maxDepth == d.maxDepth
       | .error _ => false)
    itBool "the retired Rust port's keys are unknown keys"
      (let d : Limits := {}
       ["height=5", "work=2^3", "layer_states=9", "input_nodes=1", "distinct_nodes=1",
         "candidates=1"].all fun s => overrideFails (d.withOverrides s))
    itBool "unbounded sets every production limit to max; a later item still applies"
      (let d : Limits := {}
       match d.withOverrides "unbounded,states=2" with
       | .ok l => l.maxDepth == limitMax && l.maxMaterializeWork == limitMax &&
           l.maxStates == 2 && l.maxOracleTables == d.maxOracleTables
       | .error _ => false)
    itBool "malformed overrides are errors"
      (let d : Limits := {}
       ["bogus=1", "states", "states=2^64", "states=-1", "states=1e3", "=3",
         "states=18446744073709551616"].all fun s => overrideFails (d.withOverrides s))
    itBool s!"the {limitSpecParity.length} grammar specs get the listed verdict"
      (limitSpecParity.length == 35 && limitSpecMismatches.isEmpty)
    itBool "every production resource key names a limit"
      (let d : Limits := {}
       let resources : List Resource := [.exprVisits, .depth, .nodes, .states, .transitions,
         .costEvals, .outputBytes, .materialize, .materializeWork, .knapsackCells]
       resources.all fun r => (d.set? r.key 3).isSome)

public def suite : Spec := do
  widthTests
  limitTests
  exprSizeTests
  decompositionTests
  structuralIdTests
  representationTestsPR
  cacheTests
  expansionTests
  rootApiTests
  dictionaryTestsPR
  spineWalkTests
  deepTests
  oracleTestsPR
  unitWidthTestsPR
  atomsTests
  witnessTests
  t16Tests
  nineRefTests
  tiedMinimaExactTests
  orderingTests
  propertyTestsPR
  pruningTestsPR
  profileTests
  safetyTests
  slimTests

/-- Full exhaustive oracle and large-sweep checks for nightly CI
(`exact-sharing-full`). -/
public def nightlySuite : Spec := do
  representationTests
  dictionaryTests
  oracleTests
  unitWidthTests
  witnessProductOracleTests
  tiedMinimaTests
  propertyTests
  pruningTests

end Tests.SharingExact
