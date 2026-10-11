module

public import LSpec
public import Ix.Tc
public import Ix.IxonUniv
public import Tests.Gen.Ixon

/-!
Unit tests for the `Ix.Tc` foundations (Mode/Id/Level/Expr/Const):

- raw-node address parity with the existing `Ix.Level` wire constructors
  (shared tag bytes ⇒ shared preimages for closed levels)
- anon ≡ meta address parity per constructor (metadata never hashed)
- `ExprInfo` invariants (`lbr`, `count0`, `hasFVars`) ported from expr.rs tests
- level algebra and Géran comparison tests ported from level.rs, including the
  `norm_add_node` succ-accumulator regression and the imax-witness regression
- seeded property tests (xorshift PRNG ported from level.rs)
-/

namespace Tests.Tc.Unit

open LSpec
open Ix.Tc

/-! ### Helpers -/

def mkName (s : String) : Ix.Name := .mkStr .mkAnon s

abbrev AU := KUniv .anon
abbrev MU := KUniv .«meta»
abbrev AE := KExpr .anon
abbrev ME := KExpr .«meta»

def aId (s : String) : KId .anon := ⟨Address.blake3 s.toUTF8, ()⟩
def mId (s n : String) : KId .«meta» := ⟨Address.blake3 s.toUTF8, mkName n⟩

-- Leaf constructors need the mode pinned; composite ones (`KUniv.mkMax`,
-- `KExpr.mkApp`, …) infer it from their arguments.
def aP (i : UInt64) : AU := .mkParam i ()
def mP (i : UInt64) (n : String) : MU := .mkParam i (mkName n)
def aZ : AU := .mkZero
def mZ : MU := .mkZero
def aS (u : AU) : AU := .mkSucc u
def a1 : AU := aS aZ

def aVar (i : UInt64) : AE := .mkVar i ()
def mVar (i : UInt64) (n : String) : ME := .mkVar i (mkName n)
def aFVar (i : UInt64) : AE := .mkFVar ⟨i⟩ ()
def mFVar (i : UInt64) (n : String) : ME := .mkFVar ⟨i⟩ (mkName n)
def sort0A : AE := .mkSort .mkZero
def sort0M : ME := .mkSort .mkZero
def biD : Lean.BinderInfo := .default
def biI : Lean.BinderInfo := .implicit
def aNatLit (n : Nat) : AE := .mkNatLit n
def mNatLit (n : Nat) : ME := .mkNatLit n
def aStrLit (s : String) : AE := .mkStrLit s
def mStrLit (s : String) : ME := .mkStrLit s

/-! ### Raw-node address parity with `Ix.Level` (shared wire tags) -/

def ixZero := Ix.Level.mkZero
def ixOne := Ix.Level.mkSucc ixZero
def ixTwo := Ix.Level.mkSucc ixOne

def rawParity : TestSeq :=
  test "zero addr matches Ix.Level.mkZero" (aZ.addr == ixZero.getHash)
  ++ test "succ addr matches Ix.Level.mkSucc" ((aS aZ).addr == ixOne.getHash)
  ++ test "max-raw addr matches Ix.Level.mkMax"
    ((KUniv.mkMaxRaw a1 (aS a1)).addr == (Ix.Level.mkMax ixOne ixTwo).getHash)
  ++ test "imax-raw addr matches Ix.Level.mkIMax"
    ((KUniv.mkIMaxRaw a1 (aS a1)).addr == (Ix.Level.mkIMax ixOne ixTwo).getHash)

/-! ### Anon ≡ meta address parity (metadata never hashed) -/

def univAnonMeta : TestSeq :=
  test "zero" (aZ.addr == mZ.addr)
  ++ test "succ" ((aS aZ).addr == (KUniv.mkSucc mZ).addr)
  ++ test "param named vs anon-mode" ((aP 0).addr == (mP 0 "u").addr)
  ++ test "param name does not affect hash" ((mP 0 "u").addr == (mP 0 "v").addr)
  ++ test "param same name same hash" ((mP 0 "u").addr == (mP 0 "u").addr)
  ++ test "param index differs" ((aP 0).addr != (aP 1).addr)
  ++ test "max" ((KUniv.mkMax (aP 0) (aP 1)).addr
      == (KUniv.mkMax (mP 0 "u") (mP 1 "v")).addr)
  ++ test "imax" ((KUniv.mkIMax (aP 0) (aP 1)).addr
      == (KUniv.mkIMax (mP 0 "u") (mP 1 "v")).addr)

def someMData : Array MData := #[#[(mkName "key", .ofBool true)]]

def exprAnonMeta : TestSeq :=
  test "var" ((aVar 0).addr == (mVar 0 "x").addr)
  ++ test "var mdata not hashed"
    ((KExpr.mkVar (m := .«meta») 0 (mkName "x") someMData).addr == (aVar 0).addr)
  ++ test "fvar" ((aFVar 7).addr == (mFVar 7 "y").addr)
  ++ test "sort" (sort0A.addr == sort0M.addr)
  ++ test "const" ((KExpr.mkConst (aId "Nat") #[aP 0]).addr
      == (KExpr.mkConst (mId "Nat" "Nat") #[mP 0 "u"]).addr)
  ++ test "const name does not affect hash"
    ((KExpr.mkConst (mId "Nat" "Nat") #[]).addr
      == (KExpr.mkConst (mId "Nat" "Int") #[]).addr)
  ++ test "app" ((KExpr.mkApp (aVar 0) (aVar 1)).addr
      == (KExpr.mkApp (mVar 0 "f") (mVar 1 "a")).addr)
  ++ test "lam" ((KExpr.mkLam () () sort0A (aVar 0)).addr
      == (KExpr.mkLam (mkName "x") biD sort0M (mVar 0 "x")).addr)
  ++ test "lam binder name does not affect hash"
    ((KExpr.mkLam (mkName "x") biD sort0M (mVar 0 "x")).addr
      == (KExpr.mkLam (mkName "y") biD sort0M (mVar 0 "x")).addr)
  ++ test "lam binder info does not affect hash"
    ((KExpr.mkLam (mkName "x") biD sort0M (mVar 0 "x")).addr
      == (KExpr.mkLam (mkName "x") biI sort0M (mVar 0 "x")).addr)
  ++ test "all" ((KExpr.mkAll () () sort0A (aVar 0)).addr
      == (KExpr.mkAll (mkName "x") biD sort0M (mVar 0 "x")).addr)
  ++ test "letE" ((KExpr.mkLet () sort0A (aVar 0) (aVar 1) true).addr
      == (KExpr.mkLet (mkName "x") sort0M (mVar 0 "a") (mVar 1 "b") true).addr)
  ++ test "prj" ((KExpr.mkPrj (aId "Prod") 0 (aVar 0)).addr
      == (KExpr.mkPrj (mId "Prod" "Prod") 0 (mVar 0 "p")).addr)
  ++ test "nat" ((aNatLit 42).addr == (mNatLit 42).addr)
  ++ test "str" ((aStrLit "hello").addr == (mStrLit "hello").addr)

def renderTests : TestSeq :=
  test "render preserves leaf output through depth 20"
    (KExpr.render (aVar 0) 20 == "#0")
  ++ test "render cuts off before inspecting a node at depth 21"
    (KExpr.render (aVar 0) 21 == "...")
  ++ test "render gives children the predecessor budget"
    (KExpr.render (KExpr.mkApp (aVar 0) (aVar 1)) 20 == "(... ...)")

def canonicalTotalizationTests : TestSeq :=
  test "compareKUniv recurses structurally through successors"
    (compareKUniv (KUniv.mkSucc aZ) (KUniv.mkSucc (aP 0)) ==
      compareKUniv aZ (aP 0))
  ++ test "mergeSorted preserves the left-before-right tie rule"
    ((let leftId := aId "left"
      let rightId := aId "right"
      let c : KConst .anon := .axio () () false 0 sort0A
      match mergeSorted {} (fun _ => none) #[(leftId, c)] #[(rightId, c)] with
      | .ok items =>
        items.size == 2 && items[0]!.1 == leftId && items[1]!.1 == rightId
      | .error _ => false) : Bool)
  ++ test "canonical refinement keeps its empty-input fast path"
    ((match sortKConstsWithSeedKey (m := .anon) (fun _ => none)
        (fun id _ => id.addr) #[] with
      | .ok classes => classes.isEmpty
      | .error _ => false) : Bool)

def occurrenceTests : TestSeq :=
  test "exprMentionsAddr sees constant and projection heads"
    ((let c := aId "needle"
      let e := KExpr.mkLet () sort0A (KExpr.mkConst c #[])
        (KExpr.mkPrj c 0 (aVar 0)) false
      exprMentionsAddr e c.addr &&
        !exprMentionsAddr e (aId "absent").addr) : Bool)
  ++ test "exprMentionsAddr remains stack-safe on a deep application spine"
    ((let c := aId "deep-needle"
      let e := (List.range 4096).foldl
        (fun e _ => KExpr.mkApp e (aVar 0)) (KExpr.mkConst c #[])
      exprMentionsAddr e c.addr) : Bool)

/-! ### ExprInfo invariants (ported from expr.rs tests) -/

def exprInfo : TestSeq :=
  test "var hash deterministic" ((aVar 0).addr == (aVar 0).addr)
  ++ test "var different indices" ((aVar 0).addr != (aVar 1).addr)
  ++ test "var lbr/count0"
    ((aVar 0).lbr == 1 && (aVar 0).count0 == 1
      && (aVar 3).lbr == 4 && (aVar 3).count0 == 0)
  ++ test "fvar leaf info"
    (let f := aFVar 1
     f.lbr == 0 && f.count0 == 0 && f.hasFVars)
  ++ test "fvar id affects hash" ((aFVar 1).addr != (aFVar 2).addr)
  ++ test "hasFVars propagates through app"
    ((KExpr.mkApp (aFVar 1) (aVar 0)).hasFVars
      && !(KExpr.mkApp (aVar 0) (aVar 1)).hasFVars)
  ++ test "sort hash by level"
    (sort0A.addr != (KExpr.mkSort (aS aZ)).addr)
  ++ test "const info zero"
    (let c := KExpr.mkConst (aId "Nat") #[]
     c.lbr == 0 && c.count0 == 0)
  ++ test "app lbr/count0"
    (let a := KExpr.mkApp (aVar 0) (aVar 1)
     a.lbr == 2 && a.count0 == 1)
  ++ test "app order matters"
    ((KExpr.mkApp (aVar 0) (aVar 1)).addr
      != (KExpr.mkApp (aVar 1) (aVar 0)).addr)
  ++ test "lam lbr (body var 1)"
    ((KExpr.mkLam () () sort0A (aVar 1)).lbr == 1)
  ++ test "lam lbr (ty var 0, body var 0)"
    ((KExpr.mkLam () () (aVar 0) (aVar 0)).lbr == 1)
  ++ test "lam count0 counts only ty"
    ((KExpr.mkLam () () (aVar 0) (aVar 0)).count0 == 1)
  ++ test "all hash differs from lam"
    ((KExpr.mkLam () () sort0A (aVar 0)).addr
      != (KExpr.mkAll () () sort0A (aVar 0)).addr)
  ++ test "letE lbr/count0"
    (let e := KExpr.mkLet () sort0A (aVar 0) (aVar 1) true
     e.lbr == 1 && e.count0 == 1)
  ++ test "letE nonDep distinguishes hash"
    ((KExpr.mkLet () sort0A (aVar 0) (aVar 0) true).addr
      != (KExpr.mkLet () sort0A (aVar 0) (aVar 0) false).addr)
  ++ test "prj lbr" ((KExpr.mkPrj (aId "Prod") 0 (aVar 0)).lbr == 1)
  ++ test "prj field affects hash"
    ((KExpr.mkPrj (aId "Prod") 0 (aVar 0)).addr
      != (KExpr.mkPrj (aId "Prod") 1 (aVar 0)).addr)
  ++ test "nat vs str hash"
    ((aNatLit 42).addr != (aStrLit "42").addr && (aNatLit 42).lbr == 0)
  ++ test "nat blob 0 is blake3 [0]"
    (KExpr.natBlob 0 == Address.blake3 ⟨#[0]⟩)
  ++ test "nat value not hashed beyond blob"
    ((KExpr.mkNat (m := .anon) 42 (KExpr.natBlob 42)).addr
      == (KExpr.mkNat (m := .anon) 43 (KExpr.natBlob 42)).addr)
  ++ test "sat1 saturates" (UInt64.sat1 0 == 0 && UInt64.sat1 5 == 4)
  ++ test "cmpBytes agrees with Ord Address"
    (let x := Address.blake3 ⟨#[1]⟩
     let y := Address.blake3 ⟨#[2]⟩
     x.cmpBytes y == compare x y && y.cmpBytes x == compare y x
      && x.cmpBytes x == .eq)

/-! ### Smart-constructor simplification laws (address-level, matches Rust) -/

def smartCtors : TestSeq :=
  test "max of explicit numerals picks larger"
    ((KUniv.mkMax a1 (aS a1)).addr == (aS a1).addr
      && (KUniv.mkMax (aS a1) a1).addr == (aS a1).addr)
  ++ test "max idempotent" ((KUniv.mkMax (aP 0) (aP 0)).addr == (aP 0).addr)
  ++ test "max zero absorption"
    ((KUniv.mkMax aZ (aP 0)).addr == (aP 0).addr
      && (KUniv.mkMax (aP 0) aZ).addr == (aP 0).addr)
  ++ test "max nested absorption right"
    (let m := KUniv.mkMax (aP 0) (aP 1)
     (KUniv.mkMax (aP 0) m).addr == m.addr)
  ++ test "max nested absorption left"
    (let m := KUniv.mkMax (aP 0) (aP 1)
     (KUniv.mkMax m (aP 1)).addr == m.addr)
  ++ test "max same-base offsets"
    ((KUniv.mkMax (aS (aP 0)) (aS (aS (aP 0)))).addr == (aS (aS (aP 0))).addr)
  ++ test "max unsimplified is raw node"
    ((KUniv.mkMax (aP 0) (aP 1)).addr == (KUniv.mkMaxRaw (aP 0) (aP 1)).addr)
  ++ test "imax never-zero rhs becomes max"
    ((KUniv.mkIMax (aP 0) a1).addr == (KUniv.mkMax (aP 0) a1).addr)
  ++ test "imax rhs zero is zero" ((KUniv.mkIMax (aP 0) aZ).addr == aZ.addr)
  ++ test "imax lhs zero is rhs" ((KUniv.mkIMax aZ (aP 0)).addr == (aP 0).addr)
  ++ test "imax lhs one is rhs" ((KUniv.mkIMax a1 (aP 0)).addr == (aP 0).addr)
  ++ test "imax idempotent" ((KUniv.mkIMax (aP 0) (aP 0)).addr == (aP 0).addr)
  ++ test "imax unsimplified is raw node"
    ((KUniv.mkIMax (aP 0) (aP 1)).addr == (KUniv.mkIMaxRaw (aP 0) (aP 1)).addr)
  ++ test "offset peeling"
    (let s3 := aS (aS (aS (aP 0)))
     s3.offset.2 == 3 && aZ.offset.2 == 0 && (aS aZ).offset.2 == 1)
  ++ test "isNeverZero"
    (!aZ.isNeverZero && a1.isNeverZero && !(aP 0).isNeverZero
      && (KUniv.mkMaxRaw a1 (aP 0)).isNeverZero
      && (KUniv.mkIMaxRaw (aP 0) a1).isNeverZero)

/-! ### Level algebra (ported from level.rs Géran tests) -/

def levelAlgebra : TestSeq :=
  test "univEq basics"
    (univEq aZ aZ && univEq a1 a1 && !univEq aZ a1 && !univEq a1 (aP 0))
  ++ test "univEq max commutative"
    (univEq (KUniv.mkMaxRaw (aP 0) (aP 1)) (KUniv.mkMaxRaw (aP 1) (aP 0)))
  ++ test "univEq max idempotent (raw)"
    (univEq (KUniv.mkMaxRaw (aP 0) (aP 0)) (aP 0))
  ++ test "univEq max zero (raw)" (univEq (KUniv.mkMaxRaw (aP 0) aZ) (aP 0))
  ++ test "univEq imax zero (raw)" (univEq (KUniv.mkIMaxRaw (aP 0) aZ) aZ)
  ++ test "univEq imax succ = max succ"
    (univEq (KUniv.mkIMaxRaw (aP 0) a1) (KUniv.mkMaxRaw (aP 0) a1))
  ++ test "univEq imax distributes over max"
    (let lhs := KUniv.mkIMaxRaw (aP 0) (KUniv.mkMaxRaw (aP 1) (aP 2))
     let rhs := KUniv.mkMaxRaw (KUniv.mkIMaxRaw (aP 0) (aP 1))
       (KUniv.mkIMaxRaw (aP 0) (aP 2))
     univEq lhs rhs)
  ++ test "univGeq basics"
    (univGeq aZ aZ && univGeq a1 aZ && univGeq (aP 0) aZ
      && univGeq (aS a1) a1 && !univGeq a1 (aS a1))
  ++ test "univGeq param"
    (univGeq (aS (aP 0)) (aP 0) && !univGeq (aP 0) (aS (aP 0)))
  ++ test "meta univEq ignores names"
    ((mP 0 "u").addr == (mP 0 "v").addr && univEq (mP 0 "u") (mP 0 "v"))
  ++ test "imax witness regression (Géran gap)"
    -- b = imax(imax(succ^3 0, p0), p1); max(a, b) ≥ b
    (let a := aS (aS (aS aZ))
     let b := KUniv.mkIMax (KUniv.mkIMax a (aP 0)) (aP 1)
     let mx := KUniv.mkMax a b
     univGeq mx b)
  ++ test "norm_add_node succ-accumulator regression"
    -- succ^n(imax(u, param v)) ≥ succ^n(param v) for n > 0
    (let im := KUniv.mkIMaxRaw (aP 0) (aP 1)
     univGeq (aS im) (aS (aP 1))
      && univGeq (aS (aS im)) (aS (aS (aP 1)))
      && univEq (KUniv.mkMaxRaw (aS im) (aS (aP 1))) (aS im))

/-! ### Seeded property tests (xorshift PRNG ported from level.rs) -/

structure UPrng where
  state : UInt64

def UPrng.new (seed : UInt64) : UPrng :=
  ⟨seed * 0x9E3779B97F4A7C15 ^^^ 0xDEADBEEFCAFEBABE⟩

def UPrng.next (r : UPrng) : UInt64 × UPrng :=
  let x := r.state
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

abbrev Gen := StateM UPrng

def rnext : Gen UInt64 := fun r => r.next

def rbounded (bound : UInt32) : Gen UInt32 := do
  let x ← rnext
  return x.toUInt32 % (max bound 1)

/-- Bounded-depth level generator; parameter indices drawn from
    `0..=maxParam` so universes in one test can share parameters. -/
def genUniv : Nat → UInt64 → Gen AU
  | 0, mp => do
    match (← rbounded 3).toNat with
    | 0 => return .mkZero
    | 1 => return .mkParam ((← rnext) % (mp + 1)) ()
    | _ => return .mkSucc .mkZero
  | d + 1, mp => do
    match (← rbounded 5).toNat with
    | 0 => return .mkZero
    | 1 => return .mkParam ((← rnext) % (mp + 1)) ()
    | 2 => return .mkSucc (← genUniv d mp)
    | 3 => return .mkMax (← genUniv d mp) (← genUniv d mp)
    | _ => return .mkIMax (← genUniv d mp) (← genUniv d mp)

/-- Zero/succ/max/param only — no imax. -/
def genUnivNoImax : Nat → UInt64 → Gen AU
  | 0, mp => do
    match (← rbounded 3).toNat with
    | 0 => return .mkZero
    | 1 => return .mkParam ((← rnext) % (mp + 1)) ()
    | _ => return .mkSucc .mkZero
  | d + 1, mp => do
    match (← rbounded 4).toNat with
    | 0 => return .mkZero
    | 1 => return .mkParam ((← rnext) % (mp + 1)) ()
    | 2 => return .mkSucc (← genUnivNoImax d mp)
    | _ => return .mkMax (← genUnivNoImax d mp) (← genUnivNoImax d mp)

/-- Run `iters` seeded draws of `gen`, requiring `p` on each. -/
def runProp (seed : UInt64) (iters : Nat) (gen : Gen α) (p : α → Bool) : Bool :=
  go iters (UPrng.new seed)
where
  go : Nat → UPrng → Bool
    | 0, _ => true
    | n + 1, r =>
      let (a, r) := gen r
      p a && go n r

def pair (g : Gen α) : Gen (α × α) := do
  return ((← g), (← g))

def props : TestSeq :=
  test "prop: univEq reflexive (seed 0x1234)"
    (runProp 0x1234 200 (genUniv 4 3) (fun u => univEq u u))
  ++ test "prop: univEq symmetric (seed 0xABCD)"
    (runProp 0xABCD 200 (pair (genUniv 3 2))
      (fun (a, b) => univEq a b == univEq b a))
  ++ test "prop: univGeq reflexive (seed 0x5678)"
    (runProp 0x5678 200 (genUniv 4 3) (fun u => univGeq u u))
  ++ test "prop: univEq implies univGeq both ways (seed 0xF00D)"
    (runProp 0xF00D 200 (pair (genUniv 3 2))
      (fun (a, b) => !univEq a b || (univGeq a b && univGeq b a)))
  ++ test "prop: succ u > u (seed 0xBAD0)"
    (runProp 0xBAD0 200 (genUniv 3 2)
      (fun u => univGeq (aS u) u && !univGeq u (aS u)))
  ++ test "prop: max geq both components, no imax (seed 0xBEEF)"
    (runProp 0xBEEF 200 (pair (genUnivNoImax 3 2))
      (fun (a, b) =>
        let mx := KUniv.mkMax a b
        univGeq mx a && univGeq mx b))
  ++ test "prop: max geq both components, with imax (seed 0xCAFE)"
    (runProp 0xCAFE 400 (pair (genUniv 3 2))
      (fun (a, b) =>
        let mx := KUniv.mkMax a b
        univGeq mx a && univGeq mx b))

/-! ### Mode machinery -/

def modeTests : TestSeq :=
  test "field erases in anon" (Mode.field (m := .anon) (42 : Nat) == ())
  ++ test "field preserves in meta" (Mode.field (m := .«meta») (42 : Nat) == 42)
  ++ test "fieldWith thunk in meta"
    (Mode.fieldWith (m := .«meta») (fun _ => (7 : Nat)) == 7)
  ++ test "get? anon" (Mode.get? (m := .anon) (α := Nat) () == none)
  ++ test "get? meta" (Mode.get? (m := .«meta») (5 : Nat) == some 5)
  ++ test "hasDups anon always false"
    (!Mode.F.hasDups (m := .anon) (α := Nat) ())
  ++ test "hasDups meta detects"
    (Mode.F.hasDups (m := .«meta») #[1, 2, 1]
      && !Mode.F.hasDups (m := .«meta») #[(1 : Nat), 2, 3])
  ++ test "KId equality by addr (anon)"
    (aId "x" == aId "x" && aId "x" != aId "y")
  ++ test "KId meta equality includes name"
    (mId "x" "Foo" == mId "x" "Foo" && mId "x" "Foo" != mId "x" "Bar")
  ++ test "KId ord addr-major"
    (KId.cmp (aId "x") (aId "x") == .eq
      && (KId.cmp (aId "x") (aId "y")
          == (Address.blake3 "x".toUTF8).cmpBytes (Address.blake3 "y".toUTF8)))

/-! ### Universe-level canonicalization (canonicity §10.6, `Ix.IxonUniv`)

P0 (value preservation), P1/P2/P3/P6 + class stability, swept
exhaustively over every ≤6-node term with 3 params (the
property-relevant shapes — nested imax at depth ≥ 3 — sit outside
`genUniv`'s shallow-resized sampling; every linearizer bug found during
development lived there), on the value-change witness family, and on
the kernel level comparison's biased random levels (where P1/P2/class/P6
are conditional on slip-free normal forms, `normHasSlip`), plus:

- P4 against the kernel's own Géran machinery (`Level.normalizeLevel`
  on the mk*-rebuilt `KUniv`s), modulo subsumption's empty-entry
  artifacts — see the `Ix/IxonUniv.lean` module-doc O1 note;
- the `Ixon.reduceUniv` ≍ `Ix.Tc.reduceIxonUniv` twin pin (same
  closure, one via transliterated rules, one via the kernel's actual
  smart constructors — drift here would desync the stage-1 decoration
  test from what ingress really does). -/

/-- Kernel canonical form with value-free (empty) entries stripped. -/
def strippedKernelNorm (u : AU) : List (Level.Path × Level.NormNode) :=
  (Level.normalizeLevel u).toList.filter fun (_, n) =>
    !(n.constant == 0 && n.vars.isEmpty)

def canonUnivSweep :
    Bool × Bool × Bool × Bool × Bool × Bool × Bool := Id.run do
  let mut p0 := true
  let mut p1 := true
  let mut p2 := true
  let mut p3 := true
  let mut p4 := true
  let mut p6 := true
  let mut agree := true
  for u in Tests.Gen.Ixon.enumerateUniv 6 do
    let c := Ixon.canonUniv u
    let n := Ixon.CanonUniv.normalize u
    p0 := p0 && (Tests.Gen.Ixon.univDifferAt? 3 u c).isNone
    p1 := p1 && (Ixon.canonUniv c == c)
    p2 := p2 && Ixon.CanonUniv.normEqSemantic
      (Ixon.CanonUniv.normalize (Ixon.CanonUniv.linearize n)) n
    p3 := p3 && (Ixon.reduceUniv c == c)
    p4 := p4 &&
      (strippedKernelNorm (ixonUnivToK u)
        == strippedKernelNorm (ixonUnivToK c))
    p6 := p6 && (Ixon.canonUniv (Ixon.reduceUniv u) == c)
    agree := agree && (Ixon.reduceUniv u == reduceIxonUniv u)
  return (p0, p1, p2, p3, p4, p6, agree)

/-- Does `subsumption` leave a sublevel that a single other sublevel
    dominates (`canon_univ.rs::tests::has_slip`)? A constant `c@P` is
    dominated by a constant `≥ c` at a strict sub-path, or by an atom
    `(y, k)` with `k + 1 ≥ c` at a sub-path; an atom `(x, k)@P` by an
    atom `(x, ≥ k)` at a strict sub-path. `subsumption` mirrors the
    kernels' normalizers, which test a constant against its own node's
    vars instead of the dominator's (`max (v+1) (imax (imax 2 u) v)`
    keeps the constant `2` at `[u, v]`). Only such leftovers make equal
    levels' normal forms differ, so a slip-free normal form is the
    unique one of its class. -/
def normHasSlip (n : Ixon.CanonUniv.CNorm) : Bool :=
  let es := n.toList
  es.any fun (p, node) =>
    let c := node.constant
    let constDominated := c > 0 && es.any fun (q, m) =>
      Ixon.CanonUniv.isSubset q p
        && ((q.length < p.length && m.constant ≥ c)
          || m.vars.any (fun v => v.2 + 1 ≥ c))
    let varDominated := node.vars.any fun (x, k) => es.any fun (q, m) =>
      q.length < p.length && Ixon.CanonUniv.isSubset q p
        && m.vars.any (fun (y, k2) => y == x && k2 ≥ k)
    constDominated || varDominated

/-- Failures and slip-skipped draws of `checkCanon`. -/
structure CanonCheck where
  failures : Array String := #[]
  slips : Nat := 0
  count : Nat := 0

/-- P0–P4, P6 and class stability of one level over params `0..params`
    (`canon_univ.rs::tests::check_canon`, plus the kernel-oracle P4).
    P0 and P3 are checked unconditionally. With `strict`, so are the
    rest; otherwise P1, P2, P4 and class stability are checked when
    neither `u`'s nor its canonical form's normal form has a
    subsumption leftover (`normHasSlip`), and P6 when neither `u`'s nor
    `reduceUniv u`'s has. -/
def checkCanon (params : Nat) (strict : Bool) (acc : CanonCheck)
    (u : Ixon.Univ) : CanonCheck := Id.run do
  let mut acc := { acc with count := acc.count + 1 }
  let fail (acc : CanonCheck) (msg : String) : CanonCheck :=
    { acc with failures := acc.failures.push msg }
  let n := Ixon.CanonUniv.normalize u
  let c := Ixon.canonUniv u
  if let some vals := Tests.Gen.Ixon.univDifferAt? params u c then
    acc := fail acc s!"P0 {repr u} ↦ {repr c} at {vals}"
  if Ixon.reduceUniv c != c then
    acc := fail acc s!"P3 {repr u} ↦ {repr c}"
  let nc := Ixon.CanonUniv.normalize c
  if strict || !(normHasSlip n || normHasSlip nc) then
    if Ixon.canonUniv c != c then
      acc := fail acc s!"P1 {repr u} ↦ {repr c}"
    if !Ixon.CanonUniv.normEqSemantic (Ixon.CanonUniv.normalize (Ixon.CanonUniv.linearize n)) n then
      acc := fail acc s!"P2 {repr u}"
    if !Ixon.CanonUniv.normEqSemantic nc n then
      acc := fail acc s!"CLASS {repr u} ↦ {repr c}"
    if strippedKernelNorm (ixonUnivToK u) != strippedKernelNorm (ixonUnivToK c) then
      acc := fail acc s!"P4 {repr u} ↦ {repr c}"
  else
    acc := { acc with slips := acc.slips + 1 }
  let r := Ixon.reduceUniv u
  if (strict || !(normHasSlip n || normHasSlip (Ixon.CanonUniv.normalize r)))
      && Ixon.canonUniv r != c then
    acc := fail acc s!"P6 {repr u} ↦ {repr c}"
  return acc

/-- A `checkCanon` run as a test: no failures (the first three shown). -/
def canonCheckTest (name : String) (r : CanonCheck) : TestSeq :=
  test s!"{name} ({r.count} levels, {r.slips} slip-skipped){
    if r.failures.isEmpty then "" else s!": {r.failures.toList.take 3}"}"
    r.failures.isEmpty

/-- P0 on the smallest value-change witness and its family (strict),
    with the witness's representative pinned (`canon_univ.rs::tests::p0_witness`
    pins the same term), and on the biased random family. -/
def canonUnivValueTests : TestSeq :=
  let (u, v, w) : Ixon.Univ × Ixon.Univ × Ixon.Univ := (.var 0, .var 1, .var 2)
  let l : Ixon.Univ := .imax (.imax (.succ (.imax u w)) u) v
  let σ : Nat → Nat := fun i => [0, 1, 2].getD i 0
  let witness := Tests.Gen.Ixon.univWitnessFamily.foldl (checkCanon 4 true) {}
  let random :=
    (Tests.Gen.Ixon.biasedUnivFamily 3 10 4000 41).foldl (checkCanon 3 false) {}
  let random4 :=
    (Tests.Gen.Ixon.biasedUnivFamily 4 12 1000 43).foldl (checkCanon 4 false) {}
  test "canonUniv P0: imax (imax (imax u w + 1) u) v keeps its value 1 at (0, 1, 2)"
    (Tests.Gen.Ixon.univEval σ l == 1 && Tests.Gen.Ixon.univEval σ (Ixon.canonUniv l) == 1)
  ++ test "canonUniv: the witness's representative is pinned (Rust pins the same)"
    (Ixon.canonUniv l == .max (.imax (.imax (.succ w) u) v)
      (.imax (.imax (.imax (.succ u) w) u) v))
  ++ canonCheckTest "canonUniv P0–P6: the witness family" witness
  ++ canonCheckTest "canonUniv P0–P6: biased random, 3 params" random
  ++ canonCheckTest "canonUniv P0–P6: biased random, 4 params" random4
  -- The slip is rare; a jump here means the normal forms changed.
  ++ test "canonUniv: subsumption slips stay rare (< 1 in 200)"
    ((random.slips + random4.slips) * 200 < random.count + random4.count)

def canonUnivVectors : TestSeq :=
  let v : UInt64 → Ixon.Univ := .var
  let s : Ixon.Univ → Ixon.Univ := .succ
  let z : Ixon.Univ := .zero
  test "canonUniv: commutative twins converge"
    (Ixon.canonUniv (.max (v 1) (v 0)) == .max (v 0) (v 1))
  ++ test "canonUniv: reassociation converges"
    (Ixon.canonUniv (.max (.max (v 0) (v 1)) (v 2))
      == .max (v 0) (.max (v 1) (v 2)))
  ++ test "canonUniv: succ distributes over max"
    (Ixon.canonUniv (s (.max (v 0) (v 1))) == .max (s (v 0)) (s (v 1)))
  ++ test "canonUniv: WF eq_def shape reduces"
    (Ixon.canonUniv (.imax (.imax (s z) (v 0)) (v 0)) == v 0)
  ++ test "canonUniv: common spellings are fixpoints"
    ([z, s z, v 0, s (v 0), .max (v 0) (v 1), .imax (v 0) (v 1),
      .imax (s (v 1)) (v 0),
      .imax (.imax (s (v 0)) (v 1)) (v 2)].all fun u =>
      Ixon.canonUniv u == u)
  ++ test "reduceUniv: rule table (M1/M4/M7/I2/I4 spot checks)"
    (Ixon.reduceUniv (.max (s z) (s (s z))) == s (s z)
      && Ixon.reduceUniv (.max (v 0) z) == v 0
      && Ixon.reduceUniv (.max (s (v 0)) (s (s (v 0)))) == s (s (v 0))
      && Ixon.reduceUniv (.imax (v 0) z) == z
      && Ixon.reduceUniv (.imax (s z) (v 0)) == v 0)

/-- `imax (a (n-1)) (imax (a (n-2)) (… (imax (a 0) last)))`: one `imax` per
    binder, the shape `Meta.getLevel` returns for a long `∀`. -/
def imaxChain (a : Nat → Ixon.Univ) (last : Ixon.Univ) : Nat → Ixon.Univ
  | 0 => last
  | n + 1 => .imax (a n) (imaxChain a last n)

/-- FU item 10: `canonUniv` on long `imax` chains. The `imax` distributions
    repeat calls of the normalizer (`2ⁿ` on these chains: 6 s at `n = 22`,
    not finishing at the length of `Lean.Meta.Grind.Arith.Cutsat.EqCnstr.brecOn`'s
    type); the normalizer skips a repeated call (`CanonUniv.NState`), so
    `n = 64` finishes here. Chains up to 10 links are checked as the random
    levels are (P0–P6, the kernel's Géran normal form as P4's oracle, which is
    itself exponential on them); the long ones by value (P0), idempotence
    (P1) and the `mk*` fixpoint (P3). -/
def canonUnivChainTests : TestSeq :=
  let one : Ixon.Univ := .succ .zero
  let cutsat (n : Nat) := imaxChain (fun _ => .max one (.var 0)) (.var 0) n
  let mixed (n : Nat) := imaxChain
    (fun i => if i % 3 == 0 then .max one (.var 0) else if i % 3 == 1 then .succ (.var 1)
      else .imax (.var 1) (.var 0)) (.var (if n % 2 == 0 then 0 else 1)) n
  let small := (List.range 11).foldl
    (fun acc n => checkCanon 2 false (checkCanon 2 false acc (cutsat n)) (mixed n)) {}
  let longOk (u : Ixon.Univ) : Bool :=
    let c := Ixon.canonUniv u
    (Tests.Gen.Ixon.univDifferAt? 2 u c).isNone && Ixon.canonUniv c == c && Ixon.reduceUniv c == c
  test "canonUniv: the Cutsat-shaped chain of 64 imax is `u` (0 at u = 0, else u)"
    (Ixon.canonUniv (cutsat 64) == .var 0)
  ++ canonCheckTest "canonUniv P0–P6: imax chains up to 10 links" small
  ++ test "canonUniv P0, P1, P3: Cutsat-shaped and mixed two-parameter chains of 24, 40, 64"
    ([24, 40, 64].all fun n => longOk (cutsat n) && longOk (mixed n))

def canonUnivTests : TestSeq :=
  let (p0, p1, p2, p3, p4, p6, agree) := canonUnivSweep
  canonUnivVectors
  ++ canonUnivValueTests
  ++ canonUnivChainTests
  ++ test "canonUniv P0: value-preserving (exhaustive ≤6)" p0
  ++ test "canonUniv P1: idempotent (exhaustive ≤6)" p1
  ++ test "canonUniv P2: linearize∘normalize fixpoint (exhaustive ≤6)" p2
  ++ test "canonUniv P3: canonical forms are mk* fixpoints (exhaustive ≤6)"
    p3
  ++ test "canonUniv P4: kernel Géran oracle, modulo empty entries \
           (exhaustive ≤6)" p4
  ++ test "canonUniv P6: mk* rebuild absorbed (exhaustive ≤6)" p6
  ++ test "reduceUniv ≍ Tc.reduceIxonUniv twin agreement (exhaustive ≤6)"
    agree

public def suite : List TestSeq :=
  [rawParity, univAnonMeta, exprAnonMeta, renderTests,
    canonicalTotalizationTests, occurrenceTests, exprInfo, smartCtors,
    levelAlgebra, props, modeTests, canonUnivTests]

end Tests.Tc.Unit
