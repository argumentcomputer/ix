module

public import LSpec
public import Ix.Tc
public import Tests.Ix.Tc.IxonFixtures
public import Tests.Ix.Tc.WhnfTests

/-!
Type inference and definitional equality with the real knot
(`Ix.Tc.methodsN`). Exercises the tiers that were inert under stub methods:
K-like ctor synthesis in iota, proof irrelevance, lambda eta, struct eta,
and unit-like equality.
-/

namespace Tests.Tc.InferDefEq

open LSpec
open Ix.Tc
open Tests.Tc.Fixtures (storeConst storeMutsWithProjs axiomA)

abbrev AE := KExpr .anon

def aId (s : String) : KId .anon := ⟨Address.blake3 s.toUTF8, ()⟩
def sort0 : AE := .mkSort .mkZero
def sort1 : AE := .mkSort (.mkSucc .mkZero)
def pAddr (a : Address) : AE := .mkConst ⟨a, ()⟩ #[]
def appN (f : AE) (args : List AE) : AE := args.foldl .mkApp f
def P := PrimAddrs.canonical

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

def runTcOn (env : AnonEnv) (x : TcM .anon α) : Except (TcError .anon) α :=
  match x.run (.ofEnvAnon env) with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- One of the direct method-table reads used by the production knot. -/
def directInferBackedge (e : AE) : RecM .anon AE :=
  fun methods => methods.infer e

/-- The two policy-sensitive WHNF back-edges added to make cheap projection
    and stuck-successor recursion decrease the same method-table index. -/
def directWhnfModeBackedge (e : AE) (mode : NatSuccMode) : RecM .anon AE :=
  fun methods => methods.whnfMode e mode

def directWhnfCoreFlagsBackedge (e : AE) (flags : WhnfFlags) :
    RecM .anon AE :=
  fun methods => methods.whnfCoreFlags e flags

def knotFuelTests : TestSeq :=
  test "zero current fuel rejects the first method back-edge without mutation"
    ((let initial : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 0, fuelBudget := 37 }
      match (TcM.runRec (directInferBackedge sort0)).run initial with
      | .error .maxRecFuel final =>
        final.recFuel == 0 && final.fuelBudget == 37 &&
          final.dispatchDepth == initial.dispatchDepth &&
          final.env.consts.size == initial.env.consts.size
      | _ => false) : Bool)
  ++ test "one method-table level permits one non-recursive infer dispatch"
    ((let initial : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 1, fuelBudget := 99 }
      match (TcM.runRec (directInferBackedge sort0)).run initial with
      | .ok ty final => ty.addr == sort1.addr && final.recFuel == 1
      | _ => false) : Bool)
  ++ test "zero depth rejects policy-sensitive WHNF back-edges unchanged"
    ((let initial : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 0, fuelBudget := 41 }
      match (TcM.runRec
              (directWhnfModeBackedge sort0 .stuck)).run initial,
          (TcM.runRec
              (directWhnfCoreFlagsBackedge sort0 .DEF_EQ_CORE)).run initial with
      | .error .maxRecFuel modeFinal, .error .maxRecFuel flagsFinal =>
        modeFinal.recFuel == initial.recFuel &&
          modeFinal.fuelBudget == initial.fuelBudget &&
          modeFinal.dispatchDepth == initial.dispatchDepth &&
          modeFinal.env.consts.size == initial.env.consts.size &&
          flagsFinal.recFuel == initial.recFuel &&
          flagsFinal.fuelBudget == initial.fuelBudget &&
          flagsFinal.dispatchDepth == initial.dispatchDepth &&
          flagsFinal.env.consts.size == initial.env.consts.size
      | _, _ => false) : Bool)
  ++ test "one level admits non-recursive policy-sensitive WHNF dispatch"
    ((let initial : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 1, fuelBudget := 43 }
      match (TcM.runRec
              (directWhnfModeBackedge sort0 .stuck)).run initial,
          (TcM.runRec
              (directWhnfCoreFlagsBackedge sort0 .DEF_EQ_CORE)).run initial with
      | .ok modeResult modeFinal, .ok flagsResult flagsFinal =>
        modeResult.addr == sort0.addr && flagsResult.addr == sort0.addr &&
          modeFinal.recFuel == initial.recFuel &&
          modeFinal.fuelBudget == initial.fuelBudget &&
          modeFinal.dispatchDepth == initial.dispatchDepth &&
          flagsFinal.recFuel == initial.recFuel &&
          flagsFinal.fuelBudget == initial.fuelBudget &&
          flagsFinal.dispatchDepth == initial.dispatchDepth
      | _, _ => false) : Bool)
  ++ test "zero fuel still permits a top-level infer with no back-edge"
    ((let initial : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 0, fuelBudget := 99 }
      match (TcM.infer sort0).run initial with
      | .ok ty final => ty.addr == sort1.addr && final.recFuel == 0
      | _ => false) : Bool)
  ++ test "Infer structural recursion consumes method-table depth"
    ((let forallExpr := KExpr.mkAll () () sort0 sort0
      let zero : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 0, fuelBudget := 17 }
      let one : TcState .anon :=
        { TcState.ofEnvAnon {} with recFuel := 1, fuelBudget := 17 }
      match (TcM.infer forallExpr).run zero,
          (TcM.infer forallExpr).run one with
      | .error .maxRecFuel zeroFinal, .ok _ oneFinal =>
        zeroFinal.recFuel == 0 && zeroFinal.fuelBudget == 17 &&
          zeroFinal.env.inferCache.isEmpty && oneFinal.recFuel == 1
      | _, _ => false) : Bool)

def inferEq (env : AnonEnv) (e expected : AE) : Bool :=
  match runTcOn env (TcM.infer e) with
  | .ok ty => ty.addr == expected.addr
  | .error _ => false

def defEq (env : AnonEnv) (a b : AE) : Bool :=
  runTcOn env (TcM.isDefEq a b) == .ok true

def defNeq (env : AnonEnv) (a b : AE) : Bool :=
  runTcOn env (TcM.isDefEq a b) == .ok false

def ingressEnvOf (p : Ixon.Env × Address) : AnonEnv :=
  match (ingressAll p.1).run {} with
  | .ok _ env => env
  | .error _ _ => {}

/-- `A : Sort 1` plus `idA : A → A := λ a. a` and an axiom `c : A`. -/
def baseEnv : AnonEnv × Address × Address × Address := Id.run do
  let (ixon, aAddr) := Tests.Tc.Fixtures.envA
  let idDefn : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩,
     #[], #[aAddr], #[]⟩
  let (ixon, idAddr) := storeConst ixon idDefn
  let cAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
  let (ixon, cAddr) := storeConst ixon cAxio
  (ingressEnvOf (ixon, aAddr), aAddr, idAddr, cAddr)

/-- `baseEnv` plus a second inhabitant `d : A`, with an explicit hint on
    `idA`. The hint channel is separate from the content-addressed constant. -/
def sameHeadEnv (hints : Lean.ReducibilityHints) :
    AnonEnv × Address × Address × Address × Address := Id.run do
  let (ixon, aAddr) := Tests.Tc.Fixtures.envA
  let idDefn : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0,
      .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩,
     #[], #[aAddr], #[]⟩
  let (ixon, idAddr) := storeConst ixon idDefn
  let ixon := { ixon with anonHints := ixon.anonHints.insert idAddr hints }
  let cAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
  let (ixon, cAddr) := storeConst ixon cAxio
  let dAxio : Ixon.Constant :=
    ⟨.axio ⟨true, 0, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
  let (ixon, dAddr) := storeConst ixon dAxio
  (ingressEnvOf (ixon, aAddr), aAddr, idAddr, cAddr, dAddr)

def sameHeadCongruenceDoesNotUnfold (hints : Lean.ReducibilityHints) : Bool :=
  let (env, aAddr, idAddr, cAddr, _) := sameHeadEnv hints
  let head := pAddr idAddr
  let c := pAddr cAddr
  let betaArg := KExpr.mkApp
    (KExpr.mkLam () () (pAddr aAddr) (.mkVar 0 ())) c
  let left := KExpr.mkApp head betaArg
  let right := KExpr.mkApp head c
  match (TcM.isDefEq left right).run (.ofEnvAnon env) with
  | .ok result state => result && !(state.env.unfoldCache.contains head.addr)
  | .error _ _ => false

def sameHeadCongruenceFallsBackAfterSpeculationWindow : Bool :=
  let (env, aAddr, idAddr, cAddr, _) := sameHeadEnv .abbrev
  let head := pAddr idAddr
  let c := pAddr cAddr
  let betaArg := KExpr.mkApp
    (KExpr.mkLam () () (pAddr aAddr) (.mkVar 0 ())) c
  let left := KExpr.mkApp head betaArg
  let right := KExpr.mkApp head c
  let state := { TcState.ofEnvAnon env with
    recFuel := maxRecFuel - sameHeadSpeculationStartFuel }
  match (TcM.isDefEq left right).run state with
  | .ok result state =>
      result && state.env.unfoldCache.contains head.addr
  | .error _ _ => false

/-! ### Infer (ported from infer.rs tests) -/

def inferTests : TestSeq :=
  test "infer sort" (inferEq {} sort0 sort1)
  ++ test "infer nat literal : Nat"
    (inferEq {} (.mkNatLit 5) (pAddr P.nat))
  ++ test "infer str literal : String"
    (inferEq {} (.mkStrLit "s") (pAddr P.string))
  ++ test "infer const / app / lam over fixtures"
    ((let (env, aAddr, idAddr, cAddr) := baseEnv
      let aC := pAddr aAddr
      -- idA : A → A
      inferEq env (pAddr idAddr) (KExpr.mkAll () () aC aC)
      -- idA c : A
      && inferEq env (KExpr.mkApp (pAddr idAddr) (pAddr cAddr)) aC
      -- λ (x : A). x : A → A
      && inferEq env (KExpr.mkLam () () aC (.mkVar 0 ())) (KExpr.mkAll () () aC aC)
      -- (A → A) : Sort 1
      && inferEq env (KExpr.mkAll () () aC aC) sort1 : Bool))
  ++ test "infer let substitutes value into body type"
    ((let (env, aAddr, _, cAddr) := baseEnv
      -- let x : A := c in x  ⟹  : A
      inferEq env (KExpr.mkLet () (pAddr aAddr) (pAddr cAddr) (.mkVar 0 ()) false)
        (pAddr aAddr) : Bool))
  ++ test "infer unknown const errors"
    ((match runTcOn {} (TcM.infer (pAddr (Address.blake3 "nope".toUTF8))) with
      | .error (.unknownConst _) => true
      | _ => false : Bool))
  ++ test "infer var out of range"
    ((match runTcOn {} (TcM.infer (.mkVar 3 ())) with
      | .error (.varOutOfRange 3 0) => true
      | _ => false : Bool))
  ++ test "infer app of non-function errors"
    ((let (env, _, _, cAddr) := baseEnv
      match runTcOn env (TcM.infer (KExpr.mkApp (pAddr cAddr) sort0)) with
      | .error (.funExpected ..) => true
      | _ => false : Bool))
  ++ test "infer app argument mismatch errors"
    ((let (env, _, idAddr, _) := baseEnv
      -- idA Sort0 : Sort0 is not A
      match runTcOn env (TcM.infer (KExpr.mkApp (pAddr idAddr) sort0)) with
      | .error (.appTypeMismatch ..) => true
      | _ => false : Bool))
  ++ test "infer let value type mismatch errors"
    ((let (env, aAddr, _, _) := baseEnv
      match runTcOn env (TcM.infer
        (KExpr.mkLet () (pAddr aAddr) sort0 (.mkVar 0 ()) false)) with
      | .error .declTypeMismatch => true
      | _ => false : Bool))
  ++ test "inferOnly skips app validation"
    ((let (env, _, idAddr, _) := baseEnv
      match runTcOn env (TcM.withInferOnly
        (TcM.infer (KExpr.mkApp (pAddr idAddr) sort0))) with
      | .ok _ => true
      | .error _ => false : Bool))
  ++ test "univ param count mismatch"
    ((let (env, aAddr, _, _) := baseEnv
      match runTcOn env (TcM.infer (KExpr.mkConst ⟨aAddr, ()⟩ #[.mkZero])) with
      | .error (.univParamMismatch 0 1) => true
      | _ => false : Bool))

/-! ### DefEq tiers -/

def defEqBasics : TestSeq :=
  test "identical addresses"
    (defEq {} sort0 sort0)
  ++ test "distinct sorts unequal + semantic univ equality"
    (defNeq {} sort0 sort1
      && defEq {} (KExpr.mkSort (.mkMaxRaw (.mkParam 0 ()) (.mkParam 1 ())))
        (KExpr.mkSort (.mkMaxRaw (.mkParam 1 ()) (.mkParam 0 ()))))
  ++ test "beta equivalence"
    ((let (env, aAddr, _, cAddr) := baseEnv
      defEq env (KExpr.mkApp (KExpr.mkLam () () (pAddr aAddr) (.mkVar 0 ()))
        (pAddr cAddr)) (pAddr cAddr) : Bool))
  ++ test "delta equivalence (idA c ≡ c)"
    ((let (env, _, idAddr, cAddr) := baseEnv
      defEq env (KExpr.mkApp (pAddr idAddr) (pAddr cAddr)) (pAddr cAddr) : Bool))
  ++ test "nat literal ↔ constructor bridging"
    (let succ (e : AE) : AE := KExpr.mkApp (pAddr P.natSucc) e
     let zero : AE := pAddr P.natZero
     defEq {} (.mkNatLit 3) (succ (succ (succ zero)))
      && defEq {} (.mkNatLit 0) zero
      && defNeq {} (.mkNatLit 2) (succ zero))
  ++ test "binder comparison via common fvar"
    ((let (env, aAddr, _, _) := baseEnv
      let aC := pAddr aAddr
      -- λ (x : A). x  vs  λ (x : id-type-reduced A). x with a beta-redex type
      let redexTy := KExpr.mkApp (KExpr.mkLam () () sort1 (.mkVar 0 ())) aC
      defEq env (KExpr.mkLam () () aC (.mkVar 0 ()))
        (KExpr.mkLam () () redexTy (.mkVar 0 ())) : Bool))

/-- Prop fixtures: `Pr : Sort 0` (axiom), `h : Pr` (axiom),
    `hOpaque : Pr` (opaque definition := h). -/
def propEnv : AnonEnv × Address × Address × Address := Id.run do
  let pAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let (ixon, prAddr) := storeConst {} pAxio
  let hAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[prAddr], #[]⟩
  let (ixon, hAddr) := storeConst ixon hAxio
  let hOpaque : Ixon.Constant :=
    ⟨.defn ⟨.opaq, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[prAddr, hAddr], #[]⟩
  let (ixon, hoAddr) := storeConst ixon hOpaque
  (ingressEnvOf (ixon, prAddr), prAddr, hAddr, hoAddr)

def defEqAdvanced : TestSeq :=
  test "proof irrelevance (opaque proof ≡ axiom proof)"
    ((let (env, _, hAddr, hoAddr) := propEnv
      -- hOpaque is opaque: delta can't prove this; only tier-3 proof
      -- irrelevance can.
      defEq env (pAddr hAddr) (pAddr hoAddr) : Bool))
  ++ test "lambda eta (λ x. f x ≡ f)"
    ((let (ixon, aAddr) := Tests.Tc.Fixtures.envA
      let fAxio : Ixon.Constant :=
        ⟨.axio ⟨false, 0, .leanAll (.ref 0 #[]) (.ref 0 #[])⟩, #[], #[aAddr], #[]⟩
      let (ixon, fAddr) := storeConst ixon fAxio
      let env := ingressEnvOf (ixon, aAddr)
      let lam := KExpr.mkLam () () (pAddr aAddr)
        (KExpr.mkApp (pAddr fAddr) (.mkVar 0 ()))
      defEq env lam (pAddr fAddr) && defEq env (pAddr fAddr) lam : Bool))
  ++ test "unit-like equality (two inhabitants of a 0-field struct)"
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
      let block : Ixon.Constant := ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
      let (ixon, blockAddr) := storeMutsWithProjs {} block
      let uAddr := indcProjAddr blockAddr 0
      let aAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[uAddr], #[]⟩
      let (ixon, aAddr) := storeConst ixon aAxio
      let bOpaq : Ixon.Constant :=
        ⟨.defn ⟨.opaq, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], #[uAddr, aAddr], #[]⟩
      let (ixon, bAddr) := storeConst ixon bOpaq
      let env := ingressEnvOf (ixon, blockAddr)
      defEq env (pAddr aAddr) (pAddr bAddr) : Bool))
  ++ test "struct eta (s ≡ mkS (prj 0 s) (prj 1 s))"
    -- S must be non-recursive for struct-likeness: its fields reference an
    -- EXTERNAL B (separate block), not a mutual sibling.
    ((let indB : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
      let blockB : Ixon.Constant := ⟨.muts #[.indc indB], #[], #[], #[.succ .zero]⟩
      let (ixon, blockBAddr) := storeMutsWithProjs {} blockB
      let bAddr := indcProjAddr blockBAddr 0
      let indS : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 2,
            .leanAll (.ref 0 #[]) (.leanAll (.ref 0 #[]) (.recur 0 #[]))⟩]⟩
      let blockS : Ixon.Constant :=
        ⟨.muts #[.indc indS], #[], #[bAddr], #[.succ .zero]⟩
      let (ixon, blockSAddr) := storeMutsWithProjs ixon blockS
      let sAddr := indcProjAddr blockSAddr 0
      let mkSAddr := ctorProjAddr blockSAddr 0 0
      let sAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[sAddr], #[]⟩
      let (ixon, sVal) := storeConst ixon sAxio
      let env := ingressEnvOf (ixon, blockSAddr)
      let s := pAddr sVal
      let rhs := appN (pAddr mkSAddr)
        [KExpr.mkPrj ⟨sAddr, ()⟩ 0 s, KExpr.mkPrj ⟨sAddr, ()⟩ 1 s]
      defEq env s rhs && defEq env rhs s : Bool))
  ++ test "K-like recursor synthesizes ctor from major's type"
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
      -- recE : (motive : _) → (minor : _) → (t : E) → _ — the forall
      -- structure is what getMajorInductiveId peels (skip = motives+minors
      -- = 2, then the major's domain must be E).
      let recr : Ixon.Recursor :=
        ⟨true, false, 0, 0, 0, 1, 1,
          .leanAll (.sort 0)
            (.leanAll (.sort 0) (.leanAll (.recur 0 #[]) (.sort 0))),
          #[⟨0, .leanLam (.sort 0) (.leanLam (.sort 0) (.var 0))⟩]⟩
      let block : Ixon.Constant :=
        ⟨.muts #[.indc ind, .recr recr], #[], #[], #[.succ .zero]⟩
      let (ixon, blockAddr) := storeMutsWithProjs {} block
      let eAddr := indcProjAddr blockAddr 0
      let recAddr := recrProjAddr blockAddr 1
      -- h : E is an axiom, NOT a ctor — K-synthesis must replace it.
      let hAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[eAddr], #[]⟩
      let (ixon, hAddr) := storeConst ixon hAxio
      let minorAxio : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
      let (ixon, minorAddr) := storeConst ixon minorAxio
      let env := ingressEnvOf (ixon, blockAddr)
      let e := appN (pAddr recAddr)
        [pAddr minorAddr, pAddr minorAddr, pAddr hAddr]
      match runTcOn env (TcM.whnf e) with
      | .ok r => r.addr == (pAddr minorAddr).addr
      | .error _ => false : Bool))
  ++ test "same-head Abbrev congruence avoids unfolding the head"
    (sameHeadCongruenceDoesNotUnfold .abbrev)
  ++ test "same-head Regular congruence still avoids unfolding the head"
    (sameHeadCongruenceDoesNotUnfold (.regular 7))
  ++ test "same-head Opaque-hint congruence avoids unfolding the head"
    (sameHeadCongruenceDoesNotUnfold .opaque)
  ++ test "same-head speculation window falls back to ordinary delta"
    sameHeadCongruenceFallsBackAfterSpeculationWindow
  ++ test "same-head argument miss is cached and falls back to delta"
    ((let (env, _, idAddr, cAddr, dAddr) := sameHeadEnv .abbrev
      let head := pAddr idAddr
      let left := KExpr.mkApp head (pAddr cAddr)
      let right := KExpr.mkApp head (pAddr dAddr)
      match (TcM.isDefEq left right).run (.ofEnvAnon env) with
      | .ok result state =>
          !result && state.env.defEqFailure.size > 0 &&
            state.env.unfoldCache.contains head.addr
      | .error _ _ => false : Bool))

def natOffsetTests : TestSeq :=
  let succ (e : AE) : AE := KExpr.mkApp (pAddr P.natSucc) e
  let x : AE := .mkConst (aId "x") #[]
  let compact (k : Nat) : AE := appN (pAddr P.natAdd) [x, .mkNatLit k]
  test "succ tower ↔ compact add decided by offset decomposition"
    (defEq {} (succ (succ x)) (compact 2)
      && defNeq {} (succ x) (compact 2))
  ++ test "large shared offset strips in bulk without depth exhaustion"
    -- One-succ-per-level peeling would exceed the def-eq depth limit here;
    -- offset stripping must decide it in a handful of levels.
    (let tower := (List.range 2500).foldl (fun e _ => succ e) x
     defEq {} tower (compact 2500))
  ++ test "div-derived and add-derived stuck offsets are not equated"
    (defNeq {} (appN (pAddr P.natDiv) [x, .mkNatLit 2]) (compact 2))

public def suite : List TestSeq :=
  [knotFuelTests, inferTests, defEqBasics, defEqAdvanced, natOffsetTests]

end Tests.Tc.InferDefEq
