module

public import LSpec
public import Ix.Tc
public import Tests.Ix.Tc.IxonFixtures

/-!
P4 whnf tests, run with throw-stub `Methods` (the infer/isDefEq back-edges
throw and are swallowed, so K-synthesis, struct-eta, and Nat-decidable
construction are inert until the knot is tied — exactly the plan's P4
acceptance scope). Assertions are by exact node address.
-/

namespace Tests.Tc.WhnfTests

open LSpec
open Ix.Tc
open Tests.Tc.Fixtures (storeConst storeMutsWithProjs runIngress axiomA)

abbrev AE := KExpr .anon

def aId (s : String) : KId .anon := ⟨Address.blake3 s.toUTF8, ()⟩
def sort0 : AE := .mkSort .mkZero
def sort1 : AE := .mkSort (.mkSucc .mkZero)
def natLit (n : Nat) : AE := .mkNatLit n
def pConst (id : KId .anon) : AE := .mkConst id #[]
def pAddr (a : Address) : AE := .mkConst ⟨a, ()⟩ #[]
def appN (f : AE) (args : List AE) : AE := args.foldl .mkApp f

def P := PrimAddrs.canonical

/-- Run a whnf action against a given anon env with stub methods. -/
def runWhnf (env : AnonEnv) (e : AE) : Except (TcError .anon) AE :=
  match ((RecM.whnf e).run default).run (.ofEnvAnon env) with
  | .ok a _ => .ok a
  | .error err _ => .error err

def whnfEq (env : AnonEnv) (e expected : AE) : Bool :=
  match runWhnf env e with
  | .ok r => r.addr == expected.addr
  | .error _ => false

def emptyEnv : AnonEnv := {}

/-! ### Structural reduction -/

def structuralTests : TestSeq :=
  test "whnf sort/lam/forall/literals are identity"
    (whnfEq emptyEnv sort0 sort0
      && whnfEq emptyEnv (KExpr.mkLam () () sort0 (.mkVar 0 ())) (KExpr.mkLam () () sort0 (.mkVar 0 ()))
      && whnfEq emptyEnv (natLit 7) (natLit 7)
      && whnfEq emptyEnv (KExpr.mkStrLit "x") (KExpr.mkStrLit "x"))
  ++ test "beta"
    (whnfEq emptyEnv (KExpr.mkApp (KExpr.mkLam () () sort1 (.mkVar 0 ())) sort0)
      sort0)
  ++ test "multi-arg beta picks the right arg"
    -- (λ a b. a) x y → x
    (let lam2 := KExpr.mkLam () () sort1 (KExpr.mkLam () () sort1 (.mkVar 1 ()))
     whnfEq emptyEnv (appN lam2 [pConst (aId "x"), pConst (aId "y")])
      (pConst (aId "x")))
  ++ test "zeta (let elimination)"
    (whnfEq emptyEnv (KExpr.mkLet () sort1 sort0 (.mkVar 0 ()) false) sort0)
  ++ test "delta unfolds definitions and theorems, not opaques"
    (let mkEnv (kind : Ix.DefKind) : AnonEnv := (KEnv.new).insert (aId "d")
      (.defn () () kind .safe (.regular 0) 0 sort1 sort0 () (aId "d"))
     whnfEq (mkEnv .defn) (pConst (aId "d")) sort0
      && whnfEq (mkEnv .thm) (pConst (aId "d")) sort0
      && whnfEq (mkEnv .opaq) (pConst (aId "d")) (pConst (aId "d")))
  ++ test "delta unfolds applied heads"
    -- d := λ x. x  ⟹  whnf (d c) = c
    (let idLam := KExpr.mkLam () () sort1 (.mkVar 0 ())
     let env := (KEnv.new (m := .anon)).insert (aId "d")
      (.defn () () .defn .safe (.regular 0) 0 sort1 idLam () (aId "d"))
     whnfEq env (KExpr.mkApp (pConst (aId "d")) sort0) sort0)
  ++ test "self-referential definition terminates via cycle detection"
    (let env := (KEnv.new (m := .anon)).insert (aId "x")
      (.defn () () .defn .safe (.regular 0) 0 sort1 (pConst (aId "x")) ()
        (aId "x"))
     (runWhnf env (pConst (aId "x"))).isOk)

/-! ### Iota + projection via ingressed fixtures -/

/-- Block: inductive `B : Sort 1` with ctor `mk : B`, plus recursor
    `recB` (motives 1, minors 1, rule rhs = `λ motive minor. minor`). -/
def recEnv : Ixon.Env × Address := Id.run do
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let recr : Ixon.Recursor :=
    ⟨false, false, 0, 0, 0, 1, 1, .sort 0,
      #[⟨0, .lam (.sort 0) (.lam (.sort 0) (.var 0))⟩]⟩
  let block : Ixon.Constant :=
    ⟨.muts #[.indc ind, .recr recr], #[], #[], #[.succ .zero]⟩
  storeMutsWithProjs {} block

/-- Struct-like block: `S : Sort 1` with `mkS : B → B → S` (2 fields). -/
def structEnv : Ixon.Env × Address := Id.run do
  let indB : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let indS : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 2,
        .all (.recur 0 #[]) (.all (.recur 0 #[]) (.recur 1 #[]))⟩]⟩
  let block : Ixon.Constant :=
    ⟨.muts #[.indc indB, .indc indS], #[], #[], #[.succ .zero]⟩
  storeMutsWithProjs {} block

def ingressEnvOf (p : Ixon.Env × Address) : AnonEnv :=
  match (ingressAll p.1).run {} with
  | .ok _ env => env
  | .error _ _ => {}

def iotaTests : TestSeq :=
  test "iota: recB motive minor mk → minor"
    (let (ixon, blockAddr) := recEnv
     let env := ingressEnvOf (ixon, blockAddr)
     let recId := recrProjAddr blockAddr 1
     let mkId := ctorProjAddr blockAddr 0 0
     let motive := pConst (aId "motive")
     let minor := pConst (aId "minor")
     whnfEq env (appN (pAddr recId) [motive, minor, pAddr mkId]) minor)
  ++ test "iota: under-applied recursor is stuck"
    (let (ixon, blockAddr) := recEnv
     let env := ingressEnvOf (ixon, blockAddr)
     let recId := recrProjAddr blockAddr 1
     let e := appN (pAddr recId) [pConst (aId "motive")]
     whnfEq env e e)
  ++ test "proj reduces ctor application fields"
    (let (ixon, blockAddr) := structEnv
     let env := ingressEnvOf (ixon, blockAddr)
     let sId := indcProjAddr blockAddr 1
     let mkS := ctorProjAddr blockAddr 1 0
     let a := pConst (aId "a")
     let b := pConst (aId "b")
     let sVal := appN (pAddr mkS) [a, b]
     whnfEq env (KExpr.mkPrj ⟨sId, ()⟩ 0 sVal) a
      && whnfEq env (KExpr.mkPrj ⟨sId, ()⟩ 1 sVal) b)
  ++ test "proj on non-ctor value is stuck"
    (let (ixon, blockAddr) := structEnv
     let env := ingressEnvOf (ixon, blockAddr)
     let sId := indcProjAddr blockAddr 1
     let e := KExpr.mkPrj (m := .anon) ⟨sId, ()⟩ 0 (pConst (aId "opaque"))
     whnfEq env e e)

/-! ### Native Nat/String/platform/quot reduction (address-dispatched) -/

def natTests : TestSeq :=
  test "nat binary arithmetic on literals"
    (whnfEq emptyEnv (appN (pAddr P.natAdd) [natLit 2, natLit 3]) (natLit 5)
      && whnfEq emptyEnv (appN (pAddr P.natSub) [natLit 3, natLit 5]) (natLit 0)
      && whnfEq emptyEnv (appN (pAddr P.natMul) [natLit 6, natLit 7]) (natLit 42)
      && whnfEq emptyEnv (appN (pAddr P.natDiv) [natLit 7, natLit 2]) (natLit 3)
      && whnfEq emptyEnv (appN (pAddr P.natDiv) [natLit 7, natLit 0]) (natLit 0)
      && whnfEq emptyEnv (appN (pAddr P.natMod) [natLit 7, natLit 4]) (natLit 3)
      && whnfEq emptyEnv (appN (pAddr P.natPow) [natLit 2, natLit 10]) (natLit 1024)
      && whnfEq emptyEnv (appN (pAddr P.natGcd) [natLit 12, natLit 18]) (natLit 6)
      && whnfEq emptyEnv (appN (pAddr P.natLand) [natLit 6, natLit 3]) (natLit 2)
      && whnfEq emptyEnv (appN (pAddr P.natLor) [natLit 6, natLit 3]) (natLit 7)
      && whnfEq emptyEnv (appN (pAddr P.natXor) [natLit 6, natLit 3]) (natLit 5)
      && whnfEq emptyEnv (appN (pAddr P.natShiftLeft) [natLit 3, natLit 2]) (natLit 12)
      && whnfEq emptyEnv (appN (pAddr P.natShiftRight) [natLit 12, natLit 2]) (natLit 3))
  ++ test "nat pow beyond kernel cap stays stuck"
    (let e := appN (pAddr P.natPow) [natLit 2, natLit 16777217]
     whnfEq emptyEnv e e)
  ++ test "nat predicates produce Bool constants"
    (whnfEq emptyEnv (appN (pAddr P.natBeq) [natLit 3, natLit 3]) (pAddr P.boolTrue)
      && whnfEq emptyEnv (appN (pAddr P.natBeq) [natLit 3, natLit 4]) (pAddr P.boolFalse)
      && whnfEq emptyEnv (appN (pAddr P.natBle) [natLit 3, natLit 4]) (pAddr P.boolTrue)
      && whnfEq emptyEnv (appN (pAddr P.natBle) [natLit 5, natLit 4]) (pAddr P.boolFalse))
  ++ test "succ collapses onto literals"
    (whnfEq emptyEnv (KExpr.mkApp (pAddr P.natSucc) (natLit 5)) (natLit 6)
      && whnfEq emptyEnv
        (KExpr.mkApp (pAddr P.natSucc) (KExpr.mkApp (pAddr P.natSucc) (natLit 3)))
        (natLit 5))
  ++ test "succ chain on symbolic base is stuck"
    (let e := KExpr.mkApp (pAddr P.natSucc) (pConst (aId "x"))
     whnfEq emptyEnv e e)
  ++ test "nested arithmetic collapses"
    -- (2 + 3) * (10 - 4) = 30
    (let sum := appN (pAddr P.natAdd) [natLit 2, natLit 3]
     let diff := appN (pAddr P.natSub) [natLit 10, natLit 4]
     whnfEq emptyEnv (appN (pAddr P.natMul) [sum, diff]) (natLit 30))
  ++ test "decidable falls through with stub methods (no error)"
    (let e := appN (pAddr P.natDecLe) [natLit 1, natLit 2]
     whnfEq emptyEnv e e)

def nativeTests : TestSeq :=
  test "System.Platform.numBits → 64"
    (whnfEq emptyEnv (pAddr P.systemPlatformNumBits) (natLit 64))
  ++ test "Subtype.val (getNumBits ()) form → 64"
    (let inner := KExpr.mkApp (pAddr P.systemPlatformGetNumBits) sort0
     let e := appN (pAddr P.subtypeVal) [sort0, sort0, inner]
     whnfEq emptyEnv e (natLit 64))
  ++ test "String.utf8ByteSize literal"
    (whnfEq emptyEnv (KExpr.mkApp (pAddr P.stringUtf8ByteSize) (.mkStrLit "hé"))
      (natLit 3))
  ++ test "String.back literal → Char.ofNat codepoint"
    (let expected := KExpr.mkApp (pAddr P.charOfNat) (natLit 98)
     whnfEq emptyEnv (KExpr.mkApp (pAddr P.stringBack) (.mkStrLit "ab")) expected)
  ++ test "String.toByteArray empty → ByteArray.empty"
    (whnfEq emptyEnv (KExpr.mkApp (pAddr P.stringToByteArray) (.mkStrLit ""))
      (pAddr P.byteArrayEmpty))
  ++ test "quot lift/ind reduce on Quot.mk majors"
    (let a := pConst (aId "A"); let r := pConst (aId "r")
     let f := pConst (aId "f"); let h := pConst (aId "h")
     let x := pConst (aId "x"); let β := pConst (aId "B")
     let mk := appN (pAddr P.quotCtor) [a, r, x]
     whnfEq emptyEnv (appN (pAddr P.quotLift) [a, r, β, f, h, mk])
       (KExpr.mkApp f x)
      && whnfEq emptyEnv (appN (pAddr P.quotInd) [a, r, β, f, mk])
       (KExpr.mkApp f x))
  ++ test "Int decidable literals normalize to ctor form"
    -- Int.decEq (Int.ofNat (succ-numeral 2)) (Int.ofNat 2) rebuilds args
    -- as canonical literals.
    ((let two := KExpr.mkApp (pAddr P.natSucc) (natLit 1)
     let ofNat (e : AE) : AE := KExpr.mkApp (pAddr P.intOfNat) e
     let e := appN (pAddr P.intDecEq) [ofNat two, ofNat (natLit 2)]
     -- succ-numeral collapses first via nat reduction inside whnf of args;
     -- the result should be headed by Int.decEq with both args literal 2.
     match runWhnf emptyEnv e with
     | .ok r =>
       let (head, args) := r.collectSpine
       head.addr == (pAddr P.intDecEq).addr && args.size == 2
        && args[0]!.addr == (ofNat (natLit 2)).addr
        && args[1]!.addr == (ofNat (natLit 2)).addr
     | .error _ => false : Bool))

/-! ### Cache-policy invariants -/

def cacheTests : TestSeq :=
  test "whnf caches full results"
    ((let e := appN (pAddr P.natAdd) [natLit 2, natLit 3]
     match ((RecM.whnf e).run default).run (.ofEnvAnon {}) with
     | .ok _ s => !s.env.whnfCache.isEmpty
     | .error _ _ => false : Bool))
  ++ test "iota results land in the whnf cache"
    ((let (ixon, blockAddr) := recEnv
     let env := ingressEnvOf (ixon, blockAddr)
     let recId := recrProjAddr blockAddr 1
     let e := appN (pAddr recId)
       [pConst (aId "m"), pConst (aId "n"), pAddr (ctorProjAddr blockAddr 0 0)]
     match ((RecM.whnf e).run default).run (.ofEnvAnon env) with
     | .ok _ s => !s.env.whnfCache.isEmpty
     | .error _ _ => false : Bool))

public def suite : List TestSeq :=
  [structuralTests, iotaTests, natTests, nativeTests, cacheTests]

end Tests.Tc.WhnfTests
