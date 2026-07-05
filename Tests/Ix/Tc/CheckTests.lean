module

public import LSpec
public import Ix.Tc
public import Tests.Ix.Tc.IxonFixtures

/-!
P7 tests: `checkConst` dispatch (axio/defn/theorem/quot paths),
well-scopedness validation, the safety lattice, defn-block coordination with
failure replay, and the lazy-fault driver end-to-end (`TcState.newLazyAnon`,
`checkEnvAnon`).
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
          .all (.ref 0 #[]) (.ref 0 #[]), .lam (.ref 0 #[]) (.var 0)⟩,
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

/-! ### Quot validation -/

def quotTests : TestSeq :=
  test "quot at a non-primitive address is rejected"
    ((let (ixon, aAddr) := envA
      let fakeQuot : Ixon.Constant :=
        ⟨.quot ⟨.type, 1, .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
      let (ixon, qAddr) := storeConst ixon fakeQuot
      failsContaining ixon qAddr "unknown quot address" : Bool))

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
          .all (.ref 0 #[]) (.ref 0 #[]), .lam (.ref 0 #[]) (.var 0)⟩,
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
  ++ test "checkEnvAnon: standalones pass, inductive items report P8 stub"
    ((let (ixon, aAddr) := envA
      let idDefn : Ixon.Constant :=
        ⟨.defn ⟨.defn, .safe, 0,
          .all (.ref 0 #[]) (.ref 0 #[]), .lam (.ref 0 #[]) (.var 0)⟩,
         #[], #[aAddr], #[]⟩
      let (ixon, _) := storeConst ixon idDefn
      let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
      let block : Ixon.Constant := ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
      let (ixon, _) := storeMutsWithProjs ixon block
      match checkEnvAnon ixon with
      | .ok results =>
        results.size == 4  -- A, idA, B, B.mk
          && results.all (fun r =>
            match r.err? with
            | none => true
            | some msg => (msg.splitOn "not yet ported").length > 1)
          && (results.filter (·.err?.isNone)).size == 2
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

public def suite : List TestSeq :=
  [acceptRejectTests, wellScopedTests, safetyTests, quotTests, blockTests,
   lazyTests]

end Tests.Tc.CheckTests
