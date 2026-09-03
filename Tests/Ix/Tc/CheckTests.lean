module

public import LSpec
public import Ix.Tc
public import Tests.Ix.Tc.IxonFixtures
public import Tests.Ix.Tc.IngressMetaTests

/-!
Constant-checking tests: `checkConst` dispatch (axio/defn/theorem/quot paths),
well-scopedness validation, the safety lattice, defn-block coordination with
failure replay, the lazy-fault driver end-to-end (`TcState.newLazyAnon`,
`checkEnvAnon`), and the parallel driver (`Ix.Tc.ParCheck`:
`ingressAnonEnvParallel`/`ingressMetaEnvParallel` + `buildCheckWork` +
`checkEnvParallel`) against the sequential verdicts.
-/

namespace Tests.Tc.CheckTests

open LSpec
open Ix.Tc
open Tests.Tc.Fixtures (storeConst storeMutsWithProjs axiomA envA)

abbrev AE := KExpr .anon

def pAddr (a : Address) : AE := .mkConst ⟨a, ()⟩ #[]

def ingressEnvOf (env : Ixon.Env) : AnonEnv :=
  match (ingressAll env).run {} with
  | .ok _ e => e
  | .error _ _ => {}

/-- Run `checkConst` eagerly (whole env pre-ingressed). -/
def checkOn (ixon : Ixon.Env) (addr : Address) : Except (TcError .anon) Unit :=
  match (TcM.checkConst (⟨addr, ()⟩ : KId .anon)).run
      (.ofEnvAnon (ingressEnvOf ixon)) with
  | .ok () _ => .ok ()
  | .error e _ => .error e

/-- Run `checkConst` against an already-ingressed environment. Adversarial
    metadata tests use this boundary to model an incomplete/malformed block
    index without changing the serialized fixture's expression graph. -/
def checkKEnvOn (env : KEnv .anon) (id : KId .anon) :
    Except (TcError .anon) Unit :=
  match (TcM.checkConst id).run (.ofEnvAnon env) with
  | .ok () _ => .ok ()
  | .error e _ => .error e

def kenvFailsContaining (env : KEnv .anon) (id : KId .anon)
    (frag : String) : Bool :=
  match checkKEnvOn env id with
  | .error e => ((toString e).splitOn frag).length > 1
  | .ok () => false

def passes (ixon : Ixon.Env) (addr : Address) : Bool :=
  (checkOn ixon addr).isOk

def failsContaining (ixon : Ixon.Env) (addr : Address) (frag : String) : Bool :=
  match checkOn ixon addr with
  | .error e => ((toString e).splitOn frag).length > 1
  | .ok () => false

/-! ### Accept / reject: axio, defn, theorem -/

def acceptRejectTests : TestSeq :=
  test "axiom A : Sort 1 checks"
    ((let (ixon, aAddr) := envA
      passes ixon aAddr : Bool))
  ++ test "defn idA : A → A := λ a. a checks"
    ((let (ixon, aAddr) := envA
      let idDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0,
          .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩,
         #[], #[aAddr], #[]⟩
      let (ixon, idAddr) := storeConst ixon idDefn
      passes ixon idAddr : Bool))
  ++ test "defn with mismatched value type is rejected"
    ((let (ixon, aAddr) := envA
      -- bad : A := Sort 0  (Sort 0 : Sort 1 ≠ A)
      let bad : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 0⟩, #[], #[aAddr], #[.zero]⟩
      let (ixon, badAddr) := storeConst ixon bad
      (match checkOn ixon badAddr with
        | .error .declTypeMismatch => true
        | _ => false) : Bool))
  ++ test "theorem must be Prop"
    ((let (ixon, aAddr) := envA
      -- thmBad : A := c — type A : Sort 1 is not a proposition.
      let cAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, cAddr) := storeConst ixon cAxio
      let thmBad : Ixon.Constant :=
        ⟨.defn ⟨.thm, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[aAddr, cAddr], #[]⟩
      let (ixon, thmBadAddr) := storeConst ixon thmBad
      -- thmOk : Pr := h with Pr : Sort 0.
      let prAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
      let (ixon, prAddr) := storeConst ixon prAxio
      let hAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[prAddr], #[]⟩
      let (ixon, hAddr) := storeConst ixon hAxio
      let thmOk : Ixon.Constant :=
        ⟨.defn ⟨.thm, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[prAddr, hAddr], #[]⟩
      let (ixon, thmOkAddr) := storeConst ixon thmOk
      failsContaining ixon thmBadAddr "theorem type must be a proposition"
        && passes ixon thmOkAddr : Bool))

/-! ### Well-scopedness -/

def wellScopedTests : TestSeq :=
  test "loose bvar in a type is rejected"
    ((let bad : Ixon.Constant := ⟨.axio ⟨false, 0, .var 0⟩, #[], #[], #[]⟩
      let (ixon, badAddr) := storeConst {} bad
      (match checkOn ixon badAddr with
        | .error (.varOutOfRange 0 0) => true
        | _ => false) : Bool))
  ++ test "universe param out of declared arity is rejected"
    ((let bad : Ixon.Constant :=
        ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.var 0]⟩
      let (ixon, badAddr) := storeConst {} bad
      (match checkOn ixon badAddr with
        | .error (.univParamOutOfRange 0 0) => true
        | _ => false) : Bool))
  ++ test "const universe arity mismatch is rejected"
    ((let (ixon, aAddr) := envA
      -- refers to A (lvls 0) with one universe argument
      let bad : Ixon.Constant :=
        ⟨.axio ⟨false, 0, .ref 0 #[0]⟩, #[], #[aAddr], #[.zero]⟩
      let (ixon, badAddr) := storeConst ixon bad
      (match checkOn ixon badAddr with
        | .error (.univParamMismatch 0 1) => true
        | _ => false) : Bool))
  ++ test "unknown reference is rejected"
    ((let ghost := Address.blake3 "ghost".toUTF8
      let bad : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[ghost], #[]⟩
      let (ixon, badAddr) := storeConst {} bad
      (match checkOn ixon badAddr with
        | .error (.unknownConst _) => true
        | _ => false) : Bool))

/-! ### K0 totalization boundaries -/

def totalizationTests : TestSeq :=
  test "universe validation preserves LIFO error order"
    ((let a : KUniv .anon :=
        .param 2 () (Address.blake3 "univ-work-a".toUTF8)
      let b : KUniv .anon :=
        .param 3 () (Address.blake3 "univ-work-b".toUTF8)
      let root : KUniv .anon :=
        .max a b (Address.blake3 "univ-work-root".toUTF8)
      match ((RecM.validateUnivParamsSeen root 0 {}).run default).run
          (TcState.ofEnvAnon {}) with
      | .error (.univParamOutOfRange idx 0) _ => idx == 3
      | _ => false) : Bool)
  ++ test "well-scopedness worklist remains stack-safe on a deep spine"
    ((let deep := (List.range 4096).foldl
        (fun e n => KExpr.mkApp e (.mkNatLit n)) (.mkNatLit 0)
      match ((RecM.validateExprWellScoped deep 0 0).run default).run
          (TcState.ofEnvAnon {}) with
      | .ok () _ => true
      | .error _ _ => false) : Bool)
  ++ test "nested-positivity zero depth fails before changing state"
    ((let initial : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 7 }
      let groups : Array (PositivityGroup .anon) := #[]
      let addrs : Array Address := #[]
      match ((RecM.checkPositivityDomainFuel 0
          (.mkSort .mkZero : KExpr .anon) groups addrs).run default).run
          initial with
      | .error .maxRecDepth s => s.recFuel == 7 && s.lctx.size == 0
      | _ => false) : Bool)
  ++ test "nested constructor with a short parameter telescope is rejected"
    ((let methods : Methods .anon :=
        { (default : Methods .anon) with whnf := fun e => pure e }
      let sort0 : KExpr .anon := .mkSort .mkZero
      match ((RecM.checkNestedCtorFieldsFuel 1 sort0 1 #[] #[] #[] #[]).run
          methods).run (TcState.ofEnvAnon {}) with
      | .error (.other msg) _ =>
          msg ==
            "positivity: nested constructor has fewer parameter binders than declared"
      | _ => false) : Bool)
  ++ test "forall counting restores the local context"
    ((let sort0 : AE := .mkSort .mkZero
      let ty := KExpr.mkAll () () sort0
        (KExpr.mkAll () () sort0 (KExpr.mkAll () () sort0 sort0))
      match ((RecM.countForalls ty).run default).run (TcState.ofEnvAnon {}) with
      | .ok n s => n == 3 && s.lctx.size == 0
      | .error _ _ => false) : Bool)

/-! ### Safety lattice -/

def safetyTests : TestSeq :=
  test "safe defn referencing an unsafe axiom is rejected"
    ((let (ixon, aAddr) := envA
      let unsafeC : Ixon.Constant := ⟨.axio ⟨true, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, uAddr) := storeConst ixon unsafeC
      let safeDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[aAddr, uAddr], #[]⟩
      let (ixon, dAddr) := storeConst ixon safeDefn
      failsContaining ixon dAddr "references unsafe axiom" : Bool))
  ++ test "unsafe defn may reference an unsafe axiom"
    ((let (ixon, aAddr) := envA
      let unsafeC : Ixon.Constant := ⟨.axio ⟨true, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, uAddr) := storeConst ixon unsafeC
      let unsafeDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .unsaf, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[aAddr, uAddr], #[]⟩
      let (ixon, dAddr) := storeConst ixon unsafeDefn
      passes ixon dAddr : Bool))
  ++ test "safe defn referencing a partial defn is rejected; partial may"
    ((let (ixon, aAddr) := envA
      let cAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, cAddr) := storeConst ixon cAxio
      let partialDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .part, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[aAddr, cAddr], #[]⟩
      let (ixon, pAddr') := storeConst ixon partialDefn
      let safeUser : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[aAddr, pAddr'], #[]⟩
      let (ixon, sAddr) := storeConst ixon safeUser
      let partialUser : Ixon.Constant :=
        ⟨.defn ⟨.defn, .part, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[aAddr, pAddr'], #[]⟩
      let (ixon, puAddr) := storeConst ixon partialUser
      failsContaining ixon sAddr "references partial definition"
        && passes ixon puAddr : Bool))
  ++ test "safety worklist remains stack-safe on a deep application spine"
    ((let leaf := pAddr (Address.blake3 "safety-leaf".toUTF8)
      let deep := (List.range 4096).foldl
        (fun e n => KExpr.mkApp e (.mkNatLit n)) leaf
      match ((RecM.checkNoUnsafeRefs deep .safe).run default).run
          (TcState.ofEnvAnon {}) with
      | .ok () _ => true
      | .error _ _ => false) : Bool)

/-! ### Quot validation -/

/-- Direct kernel environment for the canonical bundle installed by Lean's
    `Environment.addQuot`. Direct construction is intentional: it lets the
    adversarial tests retain a reserved primitive address while changing only
    the loaded declaration, which serialized content-addressed ingress would
    reject earlier as an integrity mismatch. -/
def canonicalQuotEnv : KEnv .anon := Id.run do
  let p := Primitives.ofAnonAddrs
  let mut env : KEnv .anon := {}
  env := env.insert p.eq
    (.indc () () 1 2 1 false p.eq 0
      (RecM.canonicalEqType (m := .anon)) #[p.eqRefl] ())
  env := env.insert p.eqRefl
    (.ctor () () false 1 p.eq 0 2 0 (RecM.canonicalEqReflType p))
  env := env.insert p.quotType
    (.quot () () .type 1 (RecM.canonicalQuotType p .type))
  env := env.insert p.quotCtor
    (.quot () () .ctor 1 (RecM.canonicalQuotType p .ctor))
  env := env.insert p.quotLift
    (.quot () () .lift 2 (RecM.canonicalQuotType p .lift))
  env := env.insert p.quotInd
    (.quot () () .ind 1 (RecM.canonicalQuotType p .ind))
  return env

def replaceQuotType (env : KEnv .anon) (id : KId .anon) (ty : AE) :
    KEnv .anon :=
  match env.get? id with
  | some (.quot name levelParams kind lvls _) =>
      env.insert id (.quot name levelParams kind lvls ty)
  | _ => env

def replaceQuotMetadata (env : KEnv .anon) (id : KId .anon)
    (kind : Ix.QuotKind) (lvls : UInt64) : KEnv .anon :=
  match env.get? id with
  | some (.quot name levelParams _ _ ty) =>
      env.insert id (.quot name levelParams kind lvls ty)
  | _ => env

def replaceEqType (env : KEnv .anon) (ty : AE) : KEnv .anon :=
  let p := Primitives.ofAnonAddrs
  env.insert p.eq (.indc () () 1 2 1 false p.eq 0 ty #[p.eqRefl] ())

def replaceEqReflType (env : KEnv .anon) (ty : AE) : KEnv .anon :=
  let p := Primitives.ofAnonAddrs
  env.insert p.eqRefl (.ctor () () false 1 p.eq 0 2 0 ty)

/-- A well-typed type satisfying the old minimum-forall test but carrying no
    quotient semantics. -/
def forgedForallType (n : Nat) : AE :=
  (List.range n).foldl
    (fun body _ => KExpr.mkAll () () (.mkSort .mkZero) body)
    (.mkSort .mkZero)

/-- Same binders as Eq, but returns `Sort 1` instead of `Prop`; this keeps the
    canonical Quot.lift type inferable so the exact Eq prerequisite is what
    rejects the environment. -/
def forgedEqType : AE :=
  let u : KUniv .anon := .mkParam 0 ()
  KExpr.mkAll () () (.mkSort u)
    (KExpr.mkAll () () (.mkVar 0 ())
      (KExpr.mkAll () () (.mkVar 1 ()) (.mkSort (.mkSucc .mkZero))))

def quotTests : TestSeq :=
  test "quot at a non-primitive address is rejected"
    ((let (ixon, aAddr) := envA
      let fakeQuot : Ixon.Constant :=
        ⟨.quot ⟨.type, 1, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, qAddr) := storeConst ixon fakeQuot
      failsContaining ixon qAddr "unknown quot address" : Bool))
  ++ test "canonical Quot bundle is accepted"
    ((let p := Primitives.ofAnonAddrs
      (checkKEnvOn canonicalQuotEnv p.quotType).isOk
        && (checkKEnvOn canonicalQuotEnv p.quotCtor).isOk
        && (checkKEnvOn canonicalQuotEnv p.quotLift).isOk
        && (checkKEnvOn canonicalQuotEnv p.quotInd).isOk : Bool))
  ++ test "quot kind must agree with its reserved address"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceQuotMetadata canonicalQuotEnv p.quotType .ctor 1
      kenvFailsContaining env p.quotType "kind mismatch" : Bool))
  ++ test "Quot.lift requires exactly two universe parameters"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceQuotMetadata canonicalQuotEnv p.quotLift .lift 3
      kenvFailsContaining env p.quotLift "expects 2 universe params" : Bool))
  ++ test "forged Quot type with two foralls is rejected"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceQuotType canonicalQuotEnv p.quotType
        (forgedForallType 2)
      kenvFailsContaining env p.quotType "type is not canonical" : Bool))
  ++ test "forged Quot.mk type with three foralls is rejected"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceQuotType canonicalQuotEnv p.quotCtor
        (forgedForallType 3)
      kenvFailsContaining env p.quotCtor "type is not canonical" : Bool))
  ++ test "forged Quot.lift type with six foralls is rejected"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceQuotType canonicalQuotEnv p.quotLift
        (forgedForallType 6)
      kenvFailsContaining env p.quotLift "type is not canonical" : Bool))
  ++ test "forged Quot.ind type with five foralls is rejected"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceQuotType canonicalQuotEnv p.quotInd
        (forgedForallType 5)
      kenvFailsContaining env p.quotInd "type is not canonical" : Bool))
  ++ test "Quot.lift rejects a noncanonical Eq type"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceEqType canonicalQuotEnv forgedEqType
      kenvFailsContaining env p.quotLift "Eq type is not canonical" : Bool))
  ++ test "Quot.lift rejects a noncanonical Eq.refl type"
    ((let p := Primitives.ofAnonAddrs
      let env := replaceEqReflType canonicalQuotEnv (forgedForallType 2)
      kenvFailsContaining env p.quotLift "Eq.refl type is not canonical" : Bool))
  ++ test "Quot.lift rejects noncanonical Eq.refl metadata"
    ((let p := Primitives.ofAnonAddrs
      let env := canonicalQuotEnv.insert p.eqRefl
        (.ctor () () false 1 p.eq 0 2 1 (RecM.canonicalEqReflType p))
      kenvFailsContaining env p.quotLift
        "Eq.refl metadata is not canonical" : Bool))

/-! ### Block coordination -/

def blockTests : TestSeq :=
  test "defn block failure replays for every member"
    ((let (ixon, aAddr) := envA
      -- Two mutually-referencing defns; g's declared type is A but its
      -- value is Sort 0 — ill-typed. Checking either member must fail.
      let f : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 1 #[]⟩
      let g : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 1⟩
      let block : Ixon.Constant :=
        ⟨.muts #[f, g], #[], #[aAddr], #[.zero, .succ .zero]⟩
      let (ixon, blockAddr) := storeMutsWithProjs ixon block
      let fAddr := defnProjAddr blockAddr 0
      let gAddr := defnProjAddr blockAddr 1
      !(passes ixon fAddr) && !(passes ixon gAddr) : Bool))
  ++ test "healthy mutual defn block checks and memoizes"
    ((let (ixon, aAddr) := envA
      let cAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, cAddr) := storeConst ixon cAxio
      -- f := g, g := c (well-typed at A)
      let f : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 1 #[]⟩
      let g : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩
      let block : Ixon.Constant :=
        ⟨.muts #[f, g], #[], #[aAddr, cAddr], #[]⟩
      let (ixon, blockAddr) := storeMutsWithProjs ixon block
      let fAddr := defnProjAddr blockAddr 0
      match (do
          TcM.checkConst (m := .anon) ⟨fAddr, ()⟩
          TcM.checkConst (m := .anon) ⟨defnProjAddr blockAddr 1, ()⟩
        : TcM .anon Unit).run (.ofEnvAnon (ingressEnvOf ixon)) with
      | .ok () s => s.env.blockCheckResults.size == 1
      | .error _ _ => false : Bool))

/-! ### Lazy faulting end-to-end -/

def lazyTests : TestSeq :=
  test "checkConst faults dependencies on demand"
    ((let (ixon, aAddr) := envA
      let idDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0,
          .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩,
         #[], #[aAddr], #[]⟩
      let (ixon, idAddr) := storeConst ixon idDefn
      -- Kernel env starts EMPTY; the fault hook pulls idA then A.
      match (TcM.checkConst (m := .anon) ⟨idAddr, ()⟩).run
          (TcState.newLazyAnon ixon) with
      | .ok () s =>
        s.env.consts.size == 2 && s.faultedAddrs.size ≥ 1
      | .error _ _ => false : Bool))
  ++ test "missing reference through the fault hook is unknownConst"
    ((let ghost := Address.blake3 "ghost".toUTF8
      let bad : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[ghost], #[]⟩
      let (ixon, badAddr) := storeConst {} bad
      match (TcM.checkConst (m := .anon) ⟨badAddr, ()⟩).run
          (TcState.newLazyAnon ixon) with
      | .error (.unknownConst a) _ => a == ghost
      | _ => false : Bool))
  ++ test "checkEnvAnon: standalones and inductive blocks all pass"
    ((let (ixon, aAddr) := envA
      let idDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0,
          .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩,
         #[], #[aAddr], #[]⟩
      let (ixon, _) := storeConst ixon idDefn
      let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
      let block : Ixon.Constant := ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
      let (ixon, _) := storeMutsWithProjs ixon block
      match checkEnvAnon ixon with
      | .ok results =>
        results.size == 4  -- A, idA, B, B.mk
          && results.all (·.err?.isNone)
      | .error _ => false : Bool))
  ++ test "integrity violation surfaces through the fault path"
    ((let wrongAddr := Address.blake3 "wrong".toUTF8
      let base : Ixon.Env := {}
      let ixon := { base with
        consts := base.consts.insert wrongAddr (.ofConstant axiomA) }
      match (TcM.checkConst (m := .anon) ⟨wrongAddr, ()⟩).run
          (TcState.newLazyAnon ixon) with
      | .error (.other msg) _ => (msg.splitOn "integrity").length > 1
      | _ => false : Bool))

/-! ### Failed-check cache isolation -/

/-- Sizes of exactly the caches rolled back by the public `checkConst` error
boundary. `blockCheckResults` is intentionally separate because new failures
are retained for deterministic replay. -/
def subjectCacheSizes (env : KEnv .anon) : Array Nat := #[
  env.whnfCache.size,
  env.whnfNoDeltaCache.size,
  env.whnfNoDeltaCheapCache.size,
  env.whnfCoreCache.size,
  env.whnfCoreCheapCache.size,
  env.inferCache.size,
  env.inferOnlyCache.size,
  env.defEqCache.size,
  env.defEqCheapCache.size,
  env.defEqFailure.size,
  env.unfoldCache.size,
  env.natSuccStuck.size,
  env.isPropCache.size,
  env.isRecCache.size,
  env.recursorCache.size,
  env.recMajorsCache.size,
  env.blockPeerAgreementCache.size
]

def cacheIsolationTests : TestSeq :=
  test "failed pending check rolls back new caches and preserves warm caches"
    ((let (ixon, aAddr) := envA
      let bad : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 0⟩,
          #[], #[aAddr], #[.zero]⟩
      let (ixon, badAddr) := storeConst ixon bad
      let warmExpr := pAddr aAddr
      let warmKey := (warmExpr.addr, emptyCtxAddr)
      let replayBlock : KId .anon :=
        ⟨Address.blake3 "cache-isolation-replay".toUTF8, ()⟩
      let base := ingressEnvOf ixon
      let warmed : KEnv .anon := { base with
        whnfCache := base.whnfCache.insert warmKey warmExpr
        blockCheckResults := base.blockCheckResults.insert replayBlock
          (.error .typeExpected) }
      let initial := TcState.ofEnvAnon warmed
      let raw := (TcM.runRec
        (RecM.checkConst (m := .anon) ⟨badAddr, ()⟩)).run initial
      let isolated := (TcM.checkConst (m := .anon) ⟨badAddr, ()⟩).run initial
      match raw, isolated with
      | .error _ rawState, .error _ isolatedState =>
        let rawGrew := subjectCacheSizes rawState.env != subjectCacheSizes warmed
        let rolledBack :=
          subjectCacheSizes isolatedState.env == subjectCacheSizes warmed
        let warmEntryKept :=
          isolatedState.env.whnfCache[warmKey]? == some warmExpr
        let replayKept :=
          match isolatedState.env.blockCheckResults[replayBlock]? with
          | some (.error .typeExpected) => true
          | _ => false
        let nonCacheStateKept :=
          isolatedState.env.consts.size == rawState.env.consts.size &&
            isolatedState.recFuel == rawState.recFuel
        let nextWarm :=
          (TcM.checkConst (m := .anon) ⟨aAddr, ()⟩).run isolatedState
        let nextFresh :=
          (TcM.checkConst (m := .anon) ⟨aAddr, ()⟩).run initial
        let sameVerdict := match nextWarm, nextFresh with
          | .ok () _, .ok () _ => true
          | .error e _, .error e' _ => e == e'
          | _, _ => false
        rawGrew && rolledBack && warmEntryKept && replayKept &&
          nonCacheStateKept && sameVerdict
      | _, _ => false : Bool))
  ++ test "error rollback retains an earlier block success"
    ((let block : KId .anon :=
        ⟨Address.blake3 "cache-isolation-old-success".toUTF8, ()⟩
      let emptyEnv : KEnv .anon := {}
      let before : KEnv .anon := { emptyEnv with
        blockCheckResults := emptyEnv.blockCheckResults.insert block (.ok ()) }
      let after : KEnv .anon := { before with
        blockCheckResults := before.blockCheckResults.insert block
          (.error .typeExpected) }
      match (before.restoreCheckCachesOnError after).blockCheckResults[block]? with
      | some (.ok ()) => true
      | _ => false : Bool))

/-! ### Forced verification of primitive addresses (`--no-verify` hole)

Acceleration substitutes native semantics for the declarations at the
hardcoded primitive addresses, so those must verify even when the caller
skips integrity checking (`Ix/Tc/Primitive.lean` at `primAddrSet`). -/

def primVerifyTests : TestSeq :=
  test "prim-addressed constant is verified even under verify := false"
    ((let base : Ixon.Env := {}
      let tampered := { base with
        consts := base.consts.insert PrimAddrs.canonical.natAdd
          (.ofConstant axiomA) }
      (match getConstVerified tampered PrimAddrs.canonical.natAdd
          (verify := false) with
        | .error e => (e.splitOn "integrity").length > 1
        | _ => false) : Bool))
  ++ test "non-prim mislabeled constant is admitted under verify := false"
    ((let wrongAddr := Address.blake3 "c1-nonprim-wrong".toUTF8
      let base : Ixon.Env := {}
      let tampered := { base with
        consts := base.consts.insert wrongAddr (.ofConstant axiomA) }
      (match getConstVerified tampered wrongAddr (verify := false) with
        | .ok (some _) => true
        | _ => false) : Bool))
  ++ test "prim-addressed tamper also rejected under default verify"
    ((let base : Ixon.Env := {}
      let tampered := { base with
        consts := base.consts.insert PrimAddrs.canonical.natAdd
          (.ofConstant axiomA) }
      (match getConstVerified tampered PrimAddrs.canonical.natAdd with
        | .error e => (e.splitOn "integrity").length > 1
        | _ => false) : Bool))

/-! ### Inductive validation (A1–A4, S3, cidx) -/

def indPasses (block : Ixon.Constant) (extra : Ixon.Env := {}) : Bool := Id.run do
  let (ixon, blockAddr) := storeMutsWithProjs extra block
  passes ixon (indcProjAddr blockAddr 0)

def indFailsWith (block : Ixon.Constant) (frag : String)
    (extra : Ixon.Env := {}) : Bool := Id.run do
  let (ixon, blockAddr) := storeMutsWithProjs extra block
  failsContaining ixon (indcProjAddr blockAddr 0) frag

/-- A two-constructor family used to probe constructor header metadata. -/
def ctorMetadataFixture :
    KEnv .anon × KId .anon × KId .anon × KId .anon := Id.run do
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
        ⟨false, 0, 1, 0, 0, .recur 0 #[]⟩]⟩
  let (ixon, blockAddr) := storeMutsWithProjs {}
    ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let blockId : KId .anon := ⟨blockAddr, ()⟩
  let indId : KId .anon := ⟨indcProjAddr blockAddr 0, ()⟩
  let ctorId : KId .anon := ⟨ctorProjAddr blockAddr 0 0, ()⟩
  return (ingressEnvOf ixon, blockId, indId, ctorId)

def replaceCtorMetadata (env : KEnv .anon) (ctorId : KId .anon)
    (isUnsafe : Bool) (lvls cidx params fields : UInt64) : KEnv .anon :=
  match env.get? ctorId with
  | some (.ctor name levelParams _ _ induct _ _ _ ty) =>
      env.insert ctorId
        (.ctor name levelParams isUnsafe lvls induct cidx params fields ty)
  | _ => env

def removeInductiveCtors (env : KEnv .anon) (indId : KId .anon) :
    KEnv .anon :=
  match env.get? indId with
  | some (.indc name levelParams lvls params indices isUnsafe block memberIdx
      ty _ leanAll) =>
    env.insert indId (.indc name levelParams lvls params indices isUnsafe
      block memberIdx ty #[] leanAll)
  | _ => env

def inductiveTests : TestSeq :=
  test "Nat-like recursive inductive validates"
    -- N : Sort 1, zero : N, succ : N → N
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
            ⟨false, 0, 1, 0, 1, .leanAll (.recur 0 #[]) (.recur 0 #[])⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩ : Bool))
  ++ test "parameterized inductive validates"
    -- P : Sort 1 → Sort 1, mkP : ∀ (α : Sort 1), α → P α
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 1, 0, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 1, 1,
            .leanAll (.sort 0)
              (.leanAll (.var 0) (.app (.recur 0 #[]) (.var 1)))⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩ : Bool))
  ++ test "negative occurrence is rejected (A3)"
    -- bad : ((B → B) → B) — B in the domain of a field's Pi
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1,
            .leanAll (.leanAll (.recur 0 #[]) (.recur 0 #[])) (.recur 0 #[])⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "strict positivity" : Bool))
  ++ test "non-uniform parameter in a recursive field is rejected (F2)"
    -- I : (A : Sort 1) → Sort 1,
    -- I.mk : (A : Sort 1) → I ExternalA → I A.
    ((let (extra, aAddr) := envA
      let ind : Ixon.Inductive :=
        ⟨false, 0, 1, 0, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 1, 1,
            .leanAll (.sort 0)
              (.leanAll (.app (.recur 0 #[]) (.ref 0 #[]))
                (.app (.recur 0 #[]) (.var 1)))⟩]⟩
      indFailsWith
        ⟨.muts #[.indc ind], #[], #[aAddr], #[.succ .zero]⟩
        "non-uniform parameter" (extra := extra) : Bool))
  ++ test "non-uniform universe in a recursive field is rejected (F2)"
    -- J.{u} : Sort 1, J.mk.{u} : J.{0} → J.{u}.
    ((let ind : Ixon.Inductive :=
        ⟨false, 1, 0, 0, .sort 2,
          #[⟨false, 1, 0, 0, 1,
            .leanAll (.recur 0 #[1]) (.recur 0 #[0])⟩]⟩
      indFailsWith
        ⟨.muts #[.indc ind], #[], #[], #[.var 0, .zero, .succ .zero]⟩
        "non-uniform universe arguments" : Bool))
  ++ test "recursive field index mentioning the block is rejected (F3)"
    -- K : Sort 1 → Sort 1, K.mk : K (K ExternalA) → K ExternalA.
    ((let (extra, aAddr) := envA
      let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 1, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 0, 1,
            .leanAll
              (.app (.recur 0 #[])
                (.app (.recur 0 #[]) (.ref 0 #[])))
              (.app (.recur 0 #[]) (.ref 0 #[]))⟩]⟩
      indFailsWith
        ⟨.muts #[.indc ind], #[], #[aAddr], #[.succ .zero]⟩
        "index mentions an active inductive" (extra := extra) : Bool))
  ++ test "ill-typed phantom nested argument is checked before rewriting (#14576)"
    ((let (extra, aAddr) := envA
      -- Phantom : Sort 1 → Sort 1; Phantom.mk : (A : Sort 1) → Phantom A.
      -- Its parameter is absent from constructor fields.
      let phantom : Ixon.Inductive :=
        ⟨false, 0, 1, 0, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 1, 0,
            .leanAll (.sort 0) (.app (.recur 0 #[]) (.var 0))⟩]⟩
      let (extra, phantomBlockAddr) := storeMutsWithProjs extra
        ⟨.muts #[.indc phantom], #[], #[], #[.succ .zero]⟩
      let phantomAddr := indcProjAddr phantomBlockAddr 0
      -- Bad.mk : Phantom (A A) → Bad. A : Sort 1 is not a function, so
      -- the original stored constructor is ill-typed. A rewrite that erased
      -- Phantom's parameter would lose this error.
      let bad : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1,
            .leanAll
              (.app (.ref 0 #[]) (.app (.ref 1 #[]) (.ref 1 #[])))
              (.recur 0 #[])⟩]⟩
      indFailsWith
        ⟨.muts #[.indc bad], #[], #[phantomAddr, aAddr], #[.succ .zero]⟩
        "function expected" (extra := extra) : Bool))
  ++ test "distinct specializations of an active nested helper are accepted"
    ((let (extra, aAddr) := envA
      -- Opt : Sort 1 → Sort 1.
      let opt : Ixon.Inductive :=
        ⟨false, 0, 1, 0, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 1, 0,
              .leanAll (.sort 0) (.app (.recur 0 #[]) (.var 0))⟩,
            ⟨false, 0, 1, 1, 1,
              .leanAll (.sort 0)
                (.leanAll (.var 0) (.app (.recur 0 #[]) (.var 1)))⟩]⟩
      let (extra, optBlockAddr) := storeMutsWithProjs extra
        ⟨.muts #[.indc opt], #[], #[], #[.succ .zero]⟩
      let optAddr := indcProjAddr optBlockAddr 0
      -- Helper A has an unrelated `Opt ExternalA`, a root-carrying `Opt A`,
      -- and a positive A field. While checking Root below, Opt is already
      -- active at the specialization `Opt (Helper Root)`.
      let helper : Ixon.Inductive :=
        ⟨false, 0, 1, 0, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 1, 3,
            .leanAll (.sort 0)
              (.leanAll (.app (.ref 0 #[]) (.ref 1 #[]))
                (.leanAll (.app (.ref 0 #[]) (.var 1))
                  (.leanAll (.var 2)
                    (.app (.recur 0 #[]) (.var 3)))))⟩]⟩
      let (extra, helperBlockAddr) := storeMutsWithProjs extra
        ⟨.muts #[.indc helper], #[], #[optAddr, aAddr], #[.succ .zero]⟩
      let helperAddr := indcProjAddr helperBlockAddr 0
      -- Root.mk : Opt (Helper Root) → Root.
      let root : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1,
            .leanAll
              (.app (.ref 0 #[]) (.app (.ref 1 #[]) (.recur 0 #[])))
              (.recur 0 #[])⟩]⟩
      indPasses
        ⟨.muts #[.indc root], #[], #[optAddr, helperAddr], #[.succ .zero]⟩
        (extra := extra) : Bool))
  ++ test "unsafe inductive skips positivity (A3 exemption)"
    ((let ind : Ixon.Inductive :=
        ⟨true, 0, 0, 0, .sort 0,
          #[⟨true, 0, 0, 0, 1,
            .leanAll (.leanAll (.recur 0 #[]) (.recur 0 #[])) (.recur 0 #[])⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩ : Bool))
  ++ test "field universe above inductive level is rejected (A4)"
    -- B : Sort 1 with a field of type Sort 1 (level 2 > 1)
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1, .leanAll (.sort 0) (.recur 0 #[])⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "field universe exceeds" : Bool))
  ++ test "Prop inductive permits any field universe (A4 exemption)"
    -- B : Prop with a field of type Sort 1
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1, .leanAll (.sort 1) (.recur 0 #[])⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.zero, .succ .zero]⟩ : Bool))
  ++ test "ctor returning the wrong type is rejected (A2)"
    -- mk : A instead of mk : B
    ((let (extra, aAddr) := envA
      let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .ref 0 #[]⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[aAddr], #[.succ .zero]⟩
        "head is not the inductive" (extra := extra) : Bool))
  ++ test "ctor cidx mismatch is rejected"
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 1, 0, 0, .recur 0 #[]⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "cidx mismatch" : Bool))
  ++ test "ctor params mismatch is rejected"
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 1, 0, .recur 0 #[]⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "params mismatch" : Bool))
  ++ test "standalone ctor params mismatch is rejected"
    ((let (env, blockId, _, ctorId) := ctorMetadataFixture
      let env := replaceCtorMetadata env ctorId false 0 0 1 0
      let env := { env with blocks := env.blocks.erase blockId }
      kenvFailsContaining env ctorId "ctor params mismatch" : Bool))
  ++ test "standalone ctor cidx mismatch is rejected"
    ((let (env, blockId, _, ctorId) := ctorMetadataFixture
      let env := replaceCtorMetadata env ctorId false 0 1 0 0
      let env := { env with blocks := env.blocks.erase blockId }
      kenvFailsContaining env ctorId "ctor cidx mismatch" : Bool))
  ++ test "standalone ctor universe arity mismatch is rejected"
    ((let (env, blockId, _, ctorId) := ctorMetadataFixture
      let env := replaceCtorMetadata env ctorId false 1 0 0 0
      let env := { env with blocks := env.blocks.erase blockId }
      kenvFailsContaining env ctorId "ctor universe arity mismatch" : Bool))
  ++ test "unlisted ctor in an inductive block is rejected"
    ((let (env, _, indId, _) := ctorMetadataFixture
      let env := removeInductiveCtors env indId
      kenvFailsContaining env indId "not listed by parent" : Bool))
  ++ test "ctor safety must match its parent inductive"
    ((let (env, _, indId, ctorId) := ctorMetadataFixture
      let env := replaceCtorMetadata env ctorId true 0 0 0 0
      kenvFailsContaining env indId "ctor safety mismatch" : Bool))
  ++ test "ctor fields metadata is exact (telescope negative control)"
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 0,
            .leanAll (.recur 0 #[]) (.recur 0 #[])⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "head is not the inductive" : Bool))
  ++ test "inductive params-plus-indices overflow is rejected"
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 18446744073709551615, 1, .sort 0, #[]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "inductive params + indices metadata sum overflow" : Bool))
  ++ test "generated recursor universe arity overflow is rejected"
    ((let ind : Ixon.Inductive :=
        ⟨false, 18446744073709551615, 0, 0, .sort 0, #[]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "generated recursor universe arity metadata sum overflow" : Bool))
  ++ test "mutual peers in different universes are rejected (S3)"
    ((let indB : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      let indC : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 1, #[]⟩
      indFailsWith
        ⟨.muts #[.indc indB, .indc indC], #[], #[],
          #[.succ .zero, .succ (.succ .zero)]⟩
        "same universe" : Bool))
  ++ test "mutual peers agreeing in universe validate (S3)"
    ((let indB : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      let indC : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      indPasses ⟨.muts #[.indc indB, .indc indC], #[], #[], #[.succ .zero]⟩
      : Bool))
  ++ test "mutual peers must share universe-parameter arity"
    ((let indB : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      let indC : Ixon.Inductive := ⟨false, 1, 0, 0, .sort 0, #[]⟩
      indFailsWith
        ⟨.muts #[.indc indB, .indc indC], #[], #[], #[.succ .zero]⟩
        "same universe arity" : Bool))
  ++ test "mutual peers must share the declaration safety flag"
    ((let indB : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      let indC : Ixon.Inductive := ⟨true, 0, 0, 0, .sort 0, #[]⟩
      indFailsWith
        ⟨.muts #[.indc indB, .indc indC], #[], #[], #[.succ .zero]⟩
        "same safety flag" : Bool))
  ++ test "index mentioning a block inductive is rejected (A2)"
    -- Block [B : Sort 1 (no ctors), I : Sort 1 → Sort 1] with
    -- `mk : I (B → B)` — the index arg is well-typed but mentions B.
    ((let indB : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      let indI : Ixon.Inductive :=
        ⟨false, 0, 0, 1, .leanAll (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 0, 0,
            .app (.recur 1 #[]) (.leanAll (.recur 0 #[]) (.recur 0 #[]))⟩]⟩
      let (ixon, blockAddr) := storeMutsWithProjs {}
        ⟨.muts #[.indc indB, .indc indI], #[], #[], #[.succ .zero]⟩
      failsContaining ixon (indcProjAddr blockAddr 1)
        "index mentions block inductive" : Bool))

/-! ### Recursor stored-vs-generated validation -/

/-- Env with `B : Sort 1`, `B.mk : B`, and a recursor block whose single
    recursor is shaped exactly like the canonical generation for B:
    `∀ (motive : B → Sort u) (minor : motive B.mk) (t : B), motive t`
    with the single rule `λ motive minor, minor`. Returns
    `(env, recProjAddr)`. -/
def recFixtureWithMetadata (indUnsafe recUnsafe : Bool) (recLvls : UInt64)
    (k : Bool) (tamperRule : Bool) : Ixon.Env × Address := Id.run do
  let ind : Ixon.Inductive :=
    ⟨indUnsafe, 0, 0, 0, .sort 0,
      #[⟨indUnsafe, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let (env, bBlockAddr) := storeMutsWithProjs {}
    ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let bAddr := indcProjAddr bBlockAddr 0
  let mkAddr := ctorProjAddr bBlockAddr 0 0
  -- B is not Prop → large eliminator: lvls 1, Sort (param 0).
  let motiveTy : Ixon.Expr := .leanAll (.ref 0 #[]) (.sort 0)
  let recTyp : Ixon.Expr :=
    .leanAll motiveTy
      (.leanAll (.app (.var 0) (.ref 1 #[]))
        (.leanAll (.ref 0 #[])
          (.app (.var 2) (.var 0))))
  let ruleRhs : Ixon.Expr :=
    if tamperRule then
      .leanLam motiveTy (.leanLam (.app (.var 0) (.ref 1 #[])) (.var 1))
    else
      .leanLam motiveTy (.leanLam (.app (.var 0) (.ref 1 #[])) (.var 0))
  let recr : Ixon.Recursor :=
    ⟨k, recUnsafe, recLvls, 0, 0, 1, 1, recTyp, #[⟨0, ruleRhs⟩]⟩
  let (env, recBlockAddr) := storeMutsWithProjs env
    ⟨.muts #[.recr recr], #[], #[bAddr, mkAddr], #[.var 0]⟩
  return (env, recrProjAddr recBlockAddr 0)

def recFixture (k : Bool) (tamperRule : Bool) : Ixon.Env × Address :=
  recFixtureWithMetadata false false 1 k tamperRule

/-- F1 exploit fixture: a fabricated recursor over `B` whose attacker-supplied
    `motives = 2` used to bypass both type and rule comparison. -/
def badMultiMotiveRecFixture : Ixon.Env × Address := Id.run do
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0, #[]⟩
  let (env, bBlockAddr) := storeMutsWithProjs {}
    ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let bAddr := indcProjAddr bBlockAddr 0
  -- (C : B → Prop) → (junk : B) → (b : B) → C b
  let recTyp : Ixon.Expr :=
    .leanAll (.leanAll (.ref 0 #[]) (.sort 0))
      (.leanAll (.ref 0 #[])
        (.leanAll (.ref 0 #[])
          (.app (.var 2) (.var 0))))
  let recr : Ixon.Recursor :=
    -- Keep large-eliminator metadata canonical so the fixture tests
    -- the fabricated motive count rather than failing at the earlier arity gate.
    ⟨false, false, 1, 0, 0, 2, 0, recTyp, #[]⟩
  let (env, recBlockAddr) := storeMutsWithProjs env
    ⟨.muts #[.recr recr], #[], #[bAddr], #[.zero]⟩
  return (env, recrProjAddr recBlockAddr 0)

/-- The four serialized recursor arities must not wrap while computing the
    major-premise position. -/
def overflowRecursorFixture : Ixon.Env × Address := Id.run do
  let recr : Ixon.Recursor :=
    ⟨false, false, 0, 18446744073709551615, 0, 1, 0, .sort 0, #[]⟩
  let (env, recBlockAddr) := storeMutsWithProjs {}
    ⟨.muts #[.recr recr], #[], #[], #[.zero]⟩
  return (env, recrProjAddr recBlockAddr 0)

def recursorTests : TestSeq :=
  test "canonical-shaped recursor validates against generation"
    ((let (ixon, recAddr) := recFixture false false
      passes ixon recAddr : Bool))
  ++ test "K-flag mismatch is rejected (S1)"
    ((let (ixon, recAddr) := recFixture true false
      failsContaining ixon recAddr "K-target mismatch" : Bool))
  ++ test "tampered rule RHS is rejected"
    ((let (ixon, recAddr) := recFixture false true
      failsContaining ixon recAddr "RHS mismatch" : Bool))
  ++ test "fabricated multi-motive recursor is rejected (F1)"
    ((let (ixon, recAddr) := badMultiMotiveRecFixture
      failsContaining ixon recAddr "no generated recursor for major" : Bool))
  ++ test "recursor major-index overflow is rejected before layout use"
    ((let (ixon, recAddr) := overflowRecursorFixture
      failsContaining ixon recAddr
        "recursor major index metadata sum overflow" : Bool))
  ++ test "recursor universe arity must match canonical generation"
    ((let (ixon, recAddr) := recFixtureWithMetadata false false 2 false false
      failsContaining ixon recAddr
        "populate_recursor_rules_from_block: canonical header mismatch" : Bool))
  ++ test "safe recursor cannot be attached to an unsafe inductive"
    ((let (ixon, recAddr) := recFixtureWithMetadata true false 1 false false
      failsContaining ixon recAddr
        "populate_recursor_rules_from_block: canonical header mismatch" : Bool))

/-! ### Parallel driver (`Ix.Tc.ParCheck`) -/

/-- Env with two passing standalones (A, idA) and a passing inductive
    block (B, B.mk) — 4 targets, mirrors the `checkEnvAnon` lazy test. -/
def parFixtureEnv : Ixon.Env := Id.run do
  let (ixon, aAddr) := envA
  let idDefn : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩,
     #[], #[aAddr], #[]⟩
  let (ixon, _) := storeConst ixon idDefn
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let block : Ixon.Constant := ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let (ixon, _) := storeMutsWithProjs ixon block
  return ixon

/-- Env with A (passes) and an ill-typed mutual defn block (both members
    must fail). Returns the block address for projection labels. -/
def parTamperEnv : Ixon.Env × Address := Id.run do
  let (ixon, aAddr) := envA
  let f : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 1 #[]⟩
  let g : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 1⟩
  let block : Ixon.Constant :=
    ⟨.muts #[f, g], #[], #[aAddr], #[.zero, .succ .zero]⟩
  let (ixon, blockAddr) := storeMutsWithProjs ixon block
  return (ixon, blockAddr)

def quietCfg : ParCheckCfg :=
  { workers := 4, silent := true, progressMs := 0, stuckMs := 0 }

/-- Anon parallel pipeline: eager parallel ingress → check work →
    parallel check (tiny chunks to exercise multi-chunk `KEnv.union`). -/
def runParAnon (ixon : Ixon.Env) : IO (Except String ParCheckReport) := do
  match buildAnonWork ixon with
  | .error e => return .error s!"work: {e}"
  | .ok work =>
    match ingressAnonEnvParallel ixon work (chunkSize := 2) with
    | .error e => return .error s!"ingress: {e}"
    | .ok kenv =>
      let report ← checkEnvParallel kenv .ofAnonAddrs (buildCheckWork kenv)
        (labelOf := toString) (failLabelOf := fun id => s!"#{id.addr}")
        quietCfg
      return .ok report

def parallelTests : TestSeq :=
  .individualIO "parallel anon check matches sequential (all pass)" none (do
    let ixon := parFixtureEnv
    let seqOk := match checkEnvAnon ixon with
      | .ok rs => rs.size == 4 && rs.all (·.err?.isNone)
      | .error _ => false
    match ← runParAnon ixon with
    | .error e => return (false, 0, 0, some e)
    | .ok report =>
      let ok := seqOk && report.passed == 4 && report.targetsCovered == 4
        && report.failures.isEmpty
      return (ok, report.targetsCovered, 0, if ok then none else some
        s!"seqOk={seqOk} passed={report.passed}/{report.targetsCovered} \
           fails={report.failures.size}")) .done
  ++ .individualIO "parallel anon check fans block failure like sequential" none (do
    let (ixon, blockAddr) := parTamperEnv
    let projF := defnProjAddr blockAddr 0
    let projG := defnProjAddr blockAddr 1
    let sortAddrs := fun (a : Array Address) =>
      a.qsort fun x y => x.cmpBytes y == .lt
    let seqOk := match checkEnvAnon ixon with
      | .ok rs => rs.size == 3
          && sortAddrs ((rs.filter (·.err?.isSome)).map (·.addr))
             == sortAddrs #[projF, projG]
      | .error _ => false
    match ← runParAnon ixon with
    | .error e => return (false, 0, 0, some e)
    | .ok report =>
      let expected := (#[s!"#{projF}", s!"#{projG}"]).qsort (· < ·)
      let ok := seqOk && report.passed == 1 && report.targetsCovered == 3
        && report.failures.map (·.1) == expected
      return (ok, report.targetsCovered, 0, if ok then none else some
        s!"seqOk={seqOk} passed={report.passed}/{report.targetsCovered} \
           failLabels={report.failures.map (·.1)}")) .done
  ++ .individualIO "parallel anon check reports deterministically" none (do
    let (ixon, _) := parTamperEnv
    match ← runParAnon ixon, ← runParAnon ixon with
    | .ok r1, .ok r2 =>
      let ok := r1.passed == r2.passed
        && r1.targetsCovered == r2.targetsCovered
        && r1.failures == r2.failures
      return (ok, r1.targetsCovered, 0, if ok then none else some
        s!"run1 passed={r1.passed} fails={r1.failures.size}; \
           run2 passed={r2.passed} fails={r2.failures.size}")
    | e1, e2 => return (false, 0, 0, some s!"{e1.isOk} {e2.isOk}")) .done
  ++ .individualIO "parallel meta check over meta fixture env" none (do
    let (env, _, _) := Tests.Tc.IngressMeta.envMetaDefn
    match ingressMetaEnvParallel env (chunkSize := 1) with
    | .error e => return (false, 0, 0, some s!"ingress: {e}")
    | .ok kenv =>
      let report ← checkEnvParallel kenv (.fromEnv kenv) (buildCheckWork kenv)
        (labelOf := toString) (failLabelOf := fun id => toString id.name)
        quietCfg
      let ok := report.failures.isEmpty && report.passed > 0
        && report.passed == report.targetsCovered
        && report.targetsCovered == kenv.consts.size
      return (ok, report.passed, 0, if ok then none else some
        s!"passed={report.passed}/{report.targetsCovered} \
           fails={report.failures.size} kenv={kenv.consts.size}")) .done

public def suite : List TestSeq :=
  [acceptRejectTests, wellScopedTests, totalizationTests, safetyTests,
   quotTests, blockTests,
   lazyTests, cacheIsolationTests, primVerifyTests, inductiveTests,
   recursorTests, parallelTests]

end Tests.Tc.CheckTests
