module

public import LSpec
public import Ix.Tc

/-!
Unit tests for `Ix.Tc` P2 substrate (Equiv/Primitive/Env/Subst/Lctx/Monad):
subst/lift/instantiateRev/abstractFVars round-trips (ported from subst.rs
tests), cheap-beta cases, ctx-id chain determinism, suffix-aware cache keys,
fuel/tick semantics under EStateM, union-find behavior, local-context
open/close, universe instantiation, and the primitives parity check against
the live Rust `PrimAddrs::new()` table (FFI).
-/

namespace Tests.Tc.Substrate

open LSpec
open Ix.Tc

/-! ### Helpers -/

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

abbrev AE := KExpr .anon
abbrev AU := KUniv .anon

def aId (s : String) : KId .anon := ⟨Address.blake3 s.toUTF8, ()⟩
def aVar (i : UInt64) : AE := .mkVar i ()
def aFVar (i : UInt64) : AE := .mkFVar ⟨i⟩ ()
def sort0 : AE := .mkSort .mkZero
def sort1 : AE := .mkSort (.mkSucc .mkZero)
def natC : AE := .mkConst (aId "Nat") #[]
def nat3 : AE := .mkNatLit 3

/-- Run an intern-table action with a fresh table. -/
def runI (x : InternM .anon α) : α := (x.run {}).1

/-- Run a `TcM .anon` action on a fresh state. -/
def runTc (x : TcM .anon α) :
    Except (TcError .anon) α × TcState .anon :=
  match x.run (.ofEnvAnon {}) with
  | .ok a s => (.ok a, s)
  | .error e s => (.error e, s)

def runTcVal (x : TcM .anon α) : Except (TcError .anon) α := (runTc x).1

/-! ### subst / lift (ported from subst.rs tests) -/

def substTests : TestSeq :=
  test "subst var 0" (runI (subst (aVar 0) nat3 0) == nat3)
  ++ test "subst closed skip" (runI (subst natC nat3 0) == natC)
  ++ test "subst free var shift"
    (runI (subst (aVar 1) nat3 0) == aVar 0)
  ++ test "subst app"
    (runI (subst (KExpr.mkApp natC (aVar 0)) nat3 0)
      == KExpr.mkApp natC nat3)
  ++ test "subst under lambda"
    (runI (subst (KExpr.mkLam () () natC (aVar 1)) nat3 0)
      == KExpr.mkLam () () natC nat3)
  ++ test "subst bound var unchanged"
    (let lam := KExpr.mkLam () () natC (aVar 0)
     runI (subst lam nat3 0) == lam)
  ++ test "subst lifts arg under binder"
    -- (λ. #1)[#0/Var(0)] at depth 0: body's Var(1) at depth 1 → lift #0 by 1 → #1
    (runI (subst (KExpr.mkLam () () natC (aVar 1)) (aVar 0) 0)
      == KExpr.mkLam () () natC (aVar 1))
  ++ test "lift var"
    (runI (lift (aVar 0) 1 0) == aVar 1
      && runI (lift (aVar 0) 1 1) == aVar 0)
  ++ test "lift zero shift" (runI (lift (aVar 0) 0 0) == aVar 0)
  ++ test "substNoIntern matches subst"
    (substNoIntern (KExpr.mkApp natC (aVar 0)) nat3 0
      == runI (subst (KExpr.mkApp natC (aVar 0)) nat3 0))

def simulSubstTests : TestSeq :=
  test "simulSubst basic"
    -- App(#1, #0)[a,b]: Var(0)→a, Var(1)→b
    (let a : AE := .mkNatLit 1
     let b : AE := .mkNatLit 2
     runI (simulSubst (KExpr.mkApp (aVar 1) (aVar 0)) #[a, b] 0)
      == KExpr.mkApp b a)
  ++ test "simulSubst shift"
    (runI (simulSubst (aVar 2) #[nat3, nat3] 0) == aVar 0)

def instantiateRevTests : TestSeq :=
  test "empty passthrough"
    (runI (instantiateRev (aVar 0) #[]) == aVar 0)
  ++ test "closed passthrough"
    (runI (instantiateRev natC #[aFVar 0]) == natC)
  ++ test "innermost" (runI (instantiateRev (aVar 0) #[aFVar 0]) == aFVar 0)
  ++ test "outermost"
    (runI (instantiateRev (aVar 1) #[aFVar 0, aFVar 1]) == aFVar 0)
  ++ test "mix"
    (runI (instantiateRev (KExpr.mkApp (aVar 0) (aVar 1))
      #[aFVar 0, aFVar 1]) == KExpr.mkApp (aFVar 1) (aFVar 0))
  ++ test "free var shifts down"
    (runI (instantiateRev (aVar 3) #[aFVar 0, aFVar 1]) == aVar 1)
  ++ test "under inner binder"
    (let lam := KExpr.mkLam () () natC (KExpr.mkApp (aVar 0) (aVar 1))
     runI (instantiateRev lam #[aFVar 0])
      == KExpr.mkLam () () natC (KExpr.mkApp (aVar 0) (aFVar 0)))

def abstractFVarsTests : TestSeq :=
  test "empty passthrough"
    (runI (abstractFVars (aVar 0) #[]) == aVar 0)
  ++ test "no fvars passthrough"
    (runI (abstractFVars (aVar 0) #[⟨0⟩]) == aVar 0)
  ++ test "single replacement"
    (runI (abstractFVars (aFVar 0) #[⟨0⟩]) == aVar 0)
  ++ test "position mapping"
    (runI (abstractFVars (KExpr.mkApp (aFVar 0) (aFVar 1)) #[⟨0⟩, ⟨1⟩])
      == KExpr.mkApp (aVar 1) (aVar 0))
  ++ test "unrelated fvar passes through"
    (runI (abstractFVars (aFVar 2) #[⟨0⟩, ⟨1⟩]) == aFVar 2)
  ++ test "lifts loose bvars"
    (runI (abstractFVars (KExpr.mkApp (aFVar 0) (aVar 0)) #[⟨0⟩])
      == KExpr.mkApp (aVar 0) (aVar 1))
  ++ test "instantiateRev then abstract roundtrip"
    (Id.run do
      let body := KExpr.mkLam () () natC (KExpr.mkApp (aVar 0) (aVar 1))
      let (r, _) := (do
        let openedOuter ← instantiateRev body #[aFVar 7]
        let inner := match openedOuter with
          | .lam _ _ _ b _ => b
          | _ => openedOuter
        let openedInner ← instantiateRev inner #[aFVar 8]
        let okOpen := openedInner == KExpr.mkApp (aFVar 8) (aFVar 7)
        let closed ← abstractFVars openedInner #[⟨7⟩, ⟨8⟩]
        pure (okOpen && closed == KExpr.mkApp (aVar 0) (aVar 1))
        : InternM .anon Bool).run {}
      return r)

def cheapBetaTests : TestSeq :=
  test "non-app returns input" (runI (cheapBetaReduce (aVar 0)) == aVar 0)
  ++ test "app non-lam head returns input"
    (let app := KExpr.mkApp natC nat3
     runI (cheapBetaReduce app) == app)
  ++ test "closed body drops lam"
    (runI (cheapBetaReduce (KExpr.mkApp (KExpr.mkLam () () natC natC) nat3))
      == natC)
  ++ test "bvar picks arg"
    (runI (cheapBetaReduce
      (KExpr.mkApp (KExpr.mkLam () () natC (aVar 0)) nat3)) == nat3)
  ++ test "nested bvar picks outer arg"
    -- (λa b. a) x y → x
    (let innerLam := KExpr.mkLam () () natC (aVar 1)
     let outerLam := KExpr.mkLam () () natC innerLam
     let x : AE := .mkNatLit 7
     let y : AE := .mkNatLit 8
     runI (cheapBetaReduce (KExpr.mkApp (KExpr.mkApp outerLam x) y)) == x)
  ++ test "overapplied appends remaining"
    -- (λx. x) y z → y z
    (let lam := KExpr.mkLam () () natC (aVar 0)
     let y : AE := .mkConst (aId "y") #[]
     let z : AE := .mkConst (aId "z") #[]
     runI (cheapBetaReduce (KExpr.mkApp (KExpr.mkApp lam y) z))
      == KExpr.mkApp y z)
  ++ test "non-trivial body returns input"
    (let lam := KExpr.mkLam () () natC (KExpr.mkApp natC (aVar 0))
     let app := KExpr.mkApp lam nat3
     runI (cheapBetaReduce app) == app)
  ++ test "underapplied returns input"
    (let innerLam := KExpr.mkLam () () natC (aVar 1)
     let outerLam := KExpr.mkLam () () natC innerLam
     let app := KExpr.mkApp outerLam natC
     runI (cheapBetaReduce app) == app)

/-! ### Intern table -/

def internTests : TestSeq :=
  test "intern dedup returns first value"
    (let it : InternTable .anon := {}
     let (a, it) := it.internExpr (aVar 0)
     let (b, _) := it.internExpr (aVar 0)
     a == b)
  ++ test "intern different stay different"
    (let it : InternTable .anon := {}
     let (a, it) := it.internExpr (aVar 0)
     let (b, _) := it.internExpr (aVar 1)
     a != b)

/-! ### EquivManager (ported from equiv.rs tests) -/

def eqAddr (n : UInt64) : Address := Address.blake3 ⟨n.toLEBytes.data⟩

def equivTests : TestSeq :=
  test "basic equiv"
    (Id.run do
      let z := eqAddr 0
      let em : EquivManager := {}
      let (before, em) := em.isEquiv (eqAddr 100, z) (eqAddr 200, z)
      let em := em.addEquiv (eqAddr 100, z) (eqAddr 200, z)
      let (after, em) := em.isEquiv (eqAddr 100, z) (eqAddr 200, z)
      let (sym, _) := em.isEquiv (eqAddr 200, z) (eqAddr 100, z)
      return !before && after && sym)
  ++ test "transitivity"
    (Id.run do
      let z := eqAddr 0
      let em := EquivManager.empty
        |>.addEquiv (eqAddr 100, z) (eqAddr 200, z)
        |>.addEquiv (eqAddr 200, z) (eqAddr 300, z)
      let (r, _) := em.isEquiv (eqAddr 100, z) (eqAddr 300, z)
      return r)
  ++ test "context isolation"
    (Id.run do
      let c1 := eqAddr 1
      let c2 := eqAddr 2
      let em := EquivManager.empty.addEquiv (eqAddr 100, c1) (eqAddr 200, c1)
      let (inC1, em) := em.isEquiv (eqAddr 100, c1) (eqAddr 200, c1)
      let (inC2, _) := em.isEquiv (eqAddr 100, c2) (eqAddr 200, c2)
      return inC1 && !inC2)

/-! ### TcM: ctx-id chain, cache keys, fuel, modes (ported from tc.rs tests) -/

def ctxTests : TestSeq :=
  test "push/pop depth roundtrip"
    (runTcVal (do
      let d0 ← TcM.depth
      TcM.pushLocal sort0
      let d1 ← TcM.depth
      TcM.pushLocal sort1
      let d2 ← TcM.depth
      TcM.popLocal
      TcM.popLocal
      let d3 ← TcM.depth
      return d0 == 0 && d1 == 1 && d2 == 2 && d3 == 0) == .ok true)
  ++ test "ctx id deterministic and restores on pop"
    (runTcVal (do
      let initial := (← get).ctxId
      TcM.pushLocal sort0
      let l1 := (← get).ctxId
      TcM.pushLocal sort1
      let l2 := (← get).ctxId
      TcM.popLocal
      let afterPop := (← get).ctxId
      TcM.popLocal
      let afterPop2 := (← get).ctxId
      return initial == emptyCtxAddr && l1 != initial && l2 != l1
        && afterPop == l1 && afterPop2 == initial) == .ok true)
  ++ test "same pushes yield same ctx id"
    (let run1 := runTc (do TcM.pushLocal sort0; TcM.pushLocal sort1)
     let run2 := runTc (do TcM.pushLocal sort0; TcM.pushLocal sort1)
     run1.2.ctxId == run2.2.ctxId)
  ++ test "let hashes differently than local"
    (let asLocal := runTc (TcM.pushLocal sort0)
     let asLet := runTc (TcM.pushLet sort0 sort0)
     asLocal.2.ctxId != asLet.2.ctxId)
  ++ test "let count tracking"
    (runTcVal (do
      TcM.pushLet sort0 sort0
      TcM.pushLocal sort0
      let c1 := (← get).numLetBindings
      TcM.popLocal
      let c2 := (← get).numLetBindings
      TcM.popLocal
      let c3 := (← get).numLetBindings
      return c1 == 1 && c2 == 1 && c3 == 0) == .ok true)
  ++ test "whnfKey empty ctx for closed expr"
    (runTcVal (do
      TcM.pushLocal sort0
      let (h, ctx) ← TcM.whnfKey sort0
      return h == sort0.addr && ctx == emptyCtxAddr) == .ok true)
  ++ test "whnfKey includes ctx id for open expr"
    (runTcVal (do
      TcM.pushLocal sort0
      let (_, ctx) ← TcM.whnfKey (aVar 0)
      return ctx == (← get).ctxId && ctx != emptyCtxAddr) == .ok true)
  ++ test "whnfKey suffix-aware across different outers"
    (let k1 := runTcVal (do
      TcM.pushLocal sort0  -- outer A
      TcM.pushLocal sort1  -- inner X
      TcM.ctxAddrForLbr 1)
     let k2 := runTcVal (do
      TcM.pushLocal sort1  -- outer B
      TcM.pushLocal sort1  -- inner X
      TcM.ctxAddrForLbr 1)
     k1 == k2 && k1 != .ok emptyCtxAddr)
  ++ test "lookupVar lifts and errors out of range"
    (runTcVal (do
      TcM.pushLocal natC
      let ty ← TcM.lookupVar 0
      return ty == natC) == .ok true
     && (match runTcVal (do TcM.pushLocal sort0; TcM.lookupVar 5) with
       | .error (.varOutOfRange 5 1) => true
       | _ => false))
  ++ test "lookupLetVal lifts value"
    (runTcVal (do
      TcM.pushLet natC nat3
      TcM.lookupLetVal 0) == .ok (some nat3))
  ++ test "isLetVar"
    (runTcVal (do
      TcM.pushLet natC nat3
      TcM.pushLocal natC
      return (← TcM.isLetVar 0, ← TcM.isLetVar 1))
      == .ok (false, true))

def fuelTests : TestSeq :=
  test "tick consumes fuel"
    (runTcVal (do
      TcM.tick
      TcM.tick
      TcM.fuelUsed) == .ok 2)
  ++ test "tick exhaustion throws maxRecFuel"
    ((runTc (do
      modify fun s => { s with recFuel := 1 }
      TcM.tick
      TcM.tick)).1
      == .error .maxRecFuel)
  ++ test "caught error keeps consumed fuel (EStateM non-backtracking)"
    (runTcVal (do
      TcM.tick
      try
        TcM.tick
        throw (.other "boom")
      catch _ =>
        pure ()
      TcM.fuelUsed) == .ok 2)
  ++ test "withInferOnly restores on error"
    (runTcVal (do
      let r ← try
        TcM.withInferOnly (do
          if !(← get).inferOnly then
            throw (.other "not set")
          throw .defEqFailed)
      catch _ =>
        pure ()
      let after := (← get).inferOnly
      return !after && r == ()) == .ok true)

def openBinderTests : TestSeq :=
  test "openBinder instantiates Var 0 and pushes lctx"
    (runTcVal (do
      let body := KExpr.mkApp (aVar 0) (aVar 1)
      let (opened, fvId) ← TcM.openBinderAnon natC body
      let s ← get
      let fv := KExpr.mkFVar (m := .anon) fvId ()
      return opened == KExpr.mkApp fv (aVar 0)
        && s.lctx.size == 1
        && (s.lctx.find? fvId).any (·.ty == natC)) == .ok true)
  ++ test "fvar ids env-scoped and increasing"
    (runTcVal (do
      let a ← TcM.freshFVarId
      let b ← TcM.freshFVarId
      return a != b && a.id + 1 == b.id) == .ok true)
  ++ test "lctx truncate drops decls"
    (let lctx := LocalContext.empty
      |>.push ⟨0⟩ (.cdecl (m := .anon) () () sort0)
      |>.push ⟨1⟩ (.cdecl () () sort1)
     let lctx1 := lctx.truncate 1
     lctx.size == 2 && lctx1.size == 1
      && (lctx1.find? ⟨1⟩).isNone && (lctx1.find? ⟨0⟩).isSome)
  ++ test "mkLambda closes over fvars"
    (runI (do
      let body := KExpr.mkApp (aFVar 0) (aFVar 1)
      let lctx := LocalContext.empty
        |>.push ⟨0⟩ (.cdecl (m := .anon) () () natC)
        |>.push ⟨1⟩ (.cdecl () () sort0)
      lctx.mkLambda #[⟨0⟩, ⟨1⟩] body)
      == KExpr.mkLam () () natC
          (KExpr.mkLam () () sort0 (KExpr.mkApp (aVar 1) (aVar 0))))
  ++ test "mkPi closes as foralls"
    (runI (do
      let lctx := LocalContext.empty
        |>.push ⟨0⟩ (.cdecl (m := .anon) () () natC)
      lctx.mkPi #[⟨0⟩] (aFVar 0))
      == KExpr.mkAll () () natC (aVar 0))

/-! ### Universe instantiation -/

def univInstTests : TestSeq :=
  test "substUniv replaces params"
    (TcM.substUniv (m := .anon) (.mkParam 0 ()) #[.mkSucc .mkZero]
      == .ok (.mkSucc .mkZero))
  ++ test "substUniv out of range"
    ((match TcM.substUniv (m := .anon) (.mkParam 2 ()) #[.mkZero] with
     | .error (.univParamOutOfRange 2 1) => true
     | _ => false : Bool))
  ++ test "substUniv simplifies via smart ctors"
    -- max(param 0, 0)[0/param 0] = max(0,0) simplifies to 0
    (TcM.substUniv (m := .anon) (.mkMaxRaw (.mkParam 0 ()) .mkZero) #[.mkZero]
      == .ok .mkZero)
  ++ test "instantiateUnivParams rewrites sorts and consts"
    (runTcVal (do
      let e := KExpr.mkApp
        (KExpr.mkConst (aId "f") #[.mkParam 0 ()])
        (KExpr.mkSort (.mkParam 0 ()))
      TcM.instantiateUnivParams e #[.mkSucc .mkZero])
      == .ok (KExpr.mkApp
        (KExpr.mkConst (aId "f") #[.mkSucc .mkZero])
        (KExpr.mkSort (.mkSucc .mkZero))))
  ++ test "instantiateUnivParams empty us is identity"
    (runTcVal (TcM.instantiateUnivParams (aVar 0) #[]) == .ok (aVar 0))

/-! ### Env basics -/

def envTests : TestSeq :=
  test "insert/get/contains"
    (let env := (KEnv.new (m := .anon)).insert (aId "Nat")
      (.axio () () false 0 sort0)
     env.contains (aId "Nat") && !env.contains (aId "missing")
      && (env.get? (aId "Nat")).isSome && env.size == 1)
  ++ test "clear preserves aux order"
    (let env := KEnv.new (m := .anon) (recursorAuxOrder := .source)
     let env := env.insert (aId "A") (.axio () () false 0 sort0)
     let env := env.clear
     env.isEmpty && env.recursorAuxOrder == .source)
  ++ test "reservedMarkerName recognizes markers"
    ((reservedMarkerName PrimAddrs.canonical.eagerReduce).isSome
      && (reservedMarkerName PrimAddrs.canonical.nat).isNone)
  ++ test "anon prims resolve to bare addresses"
    (let p := Primitives.ofAnonAddrs
     p.nat.addr == PrimAddrs.canonical.nat
      && p.eagerReduce.addr == PrimAddrs.canonical.eagerReduce)
  ++ test "isEagerReduce spine check"
    (runTcVal (do
      let er := KExpr.mkConst (m := .anon) ⟨PrimAddrs.canonical.eagerReduce, ()⟩ #[]
      return (← TcM.isEagerReduce (KExpr.mkApp (KExpr.mkApp er sort0) nat3),
              ← TcM.isEagerReduce (KExpr.mkApp er sort0)))
      == .ok (true, false))

/-! ### Primitives parity vs live Rust table (FFI) -/

@[extern "rs_prim_addrs_canonical"]
private opaque rsPrimAddrsCanonicalFFI : IO (Array (String × String))

def primsParity : TestSeq :=
  .individualIO "PrimAddrs.canonical parity vs Rust PrimAddrs::new()" none (do
    let rust ← rsPrimAddrsCanonicalFFI
    let lean := PrimAddrs.leanParityTable
    if rust.size != lean.size then
      return (false, rust.size, lean.size,
        some s!"size mismatch: rust {rust.size} vs lean {lean.size}")
    let mut bad : Array String := #[]
    for ((rn, rh), (ln, la)) in rust.zip lean do
      if rn != ln then
        bad := bad.push s!"order mismatch: {rn} vs {ln}"
      else if toString la != rh then
        bad := bad.push s!"{rn}: rust {rh} != lean {toString la}"
    if bad.isEmpty then
      return (true, rust.size, rust.size, none)
    return (false, bad.size, rust.size,
      some (String.intercalate "; " bad.toList))) .done

public def suite : List TestSeq :=
  [substTests, simulSubstTests, instantiateRevTests, abstractFVarsTests,
   cheapBetaTests, internTests, equivTests, ctxTests, fuelTests,
   openBinderTests, univInstTests, envTests, primsParity]

end Tests.Tc.Substrate
