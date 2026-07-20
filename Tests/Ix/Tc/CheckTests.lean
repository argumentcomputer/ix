module

public import LSpec
public import Ix.Tc
public import Tests.Ix.Tc.IxonFixtures
public import Tests.Ix.Tc.IngressMetaTests

/-!
P7 tests: `checkConst` dispatch (axio/defn/theorem/quot paths),
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
  ++ test "checkEnvAnon: standalones and inductive blocks all pass"
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

/-! ### P8: inductive validation (A1–A4, S3, cidx) -/

def indPasses (block : Ixon.Constant) (extra : Ixon.Env := {}) : Bool := Id.run do
  let (ixon, blockAddr) := storeMutsWithProjs extra block
  passes ixon (indcProjAddr blockAddr 0)

def indFailsWith (block : Ixon.Constant) (frag : String)
    (extra : Ixon.Env := {}) : Bool := Id.run do
  let (ixon, blockAddr) := storeMutsWithProjs extra block
  failsContaining ixon (indcProjAddr blockAddr 0) frag

def inductiveTests : TestSeq :=
  test "Nat-like recursive inductive validates"
    -- N : Sort 1, zero : N, succ : N → N
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
            ⟨false, 0, 1, 0, 1, .all (.recur 0 #[]) (.recur 0 #[])⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩ : Bool))
  ++ test "parameterized inductive validates"
    -- P : Sort 1 → Sort 1, mkP : ∀ (α : Sort 1), α → P α
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 1, 0, .all (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 1, 1,
            .all (.sort 0) (.all (.var 0) (.app (.recur 0 #[]) (.var 1)))⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩ : Bool))
  ++ test "negative occurrence is rejected (A3)"
    -- bad : ((B → B) → B) — B in the domain of a field's Pi
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1,
            .all (.all (.recur 0 #[]) (.recur 0 #[])) (.recur 0 #[])⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "strict positivity" : Bool))
  ++ test "unsafe inductive skips positivity (A3 exemption)"
    ((let ind : Ixon.Inductive :=
        ⟨true, 0, 0, 0, .sort 0,
          #[⟨true, 0, 0, 0, 1,
            .all (.all (.recur 0 #[]) (.recur 0 #[])) (.recur 0 #[])⟩]⟩
      indPasses ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩ : Bool))
  ++ test "field universe above inductive level is rejected (A4)"
    -- B : Sort 1 with a field of type Sort 1 (level 2 > 1)
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1, .all (.sort 0) (.recur 0 #[])⟩]⟩
      indFailsWith ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
        "field universe exceeds" : Bool))
  ++ test "Prop inductive permits any field universe (A4 exemption)"
    -- B : Prop with a field of type Sort 1
    ((let ind : Ixon.Inductive :=
        ⟨false, 0, 0, 0, .sort 0,
          #[⟨false, 0, 0, 0, 1, .all (.sort 1) (.recur 0 #[])⟩]⟩
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
  ++ test "index mentioning a block inductive is rejected (A2)"
    -- Block [B : Sort 1 (no ctors), I : Sort 1 → Sort 1] with
    -- `mk : I (B → B)` — the index arg is well-typed but mentions B.
    ((let indB : Ixon.Inductive := ⟨false, 0, 0, 0, .sort 0, #[]⟩
      let indI : Ixon.Inductive :=
        ⟨false, 0, 0, 1, .all (.sort 0) (.sort 0),
          #[⟨false, 0, 0, 0, 0,
            .app (.recur 1 #[]) (.all (.recur 0 #[]) (.recur 0 #[]))⟩]⟩
      let (ixon, blockAddr) := storeMutsWithProjs {}
        ⟨.muts #[.indc indB, .indc indI], #[], #[], #[.succ .zero]⟩
      failsContaining ixon (indcProjAddr blockAddr 1)
        "index mentions block inductive" : Bool))

/-! ### P9: recursor stored-vs-generated validation -/

/-- Env with `B : Sort 1`, `B.mk : B`, and a recursor block whose single
    recursor is shaped exactly like the canonical generation for B:
    `∀ (motive : B → Sort u) (minor : motive B.mk) (t : B), motive t`
    with the single rule `λ motive minor, minor`. Returns
    `(env, recProjAddr)`. -/
def recFixture (k : Bool) (tamperRule : Bool) : Ixon.Env × Address := Id.run do
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let (env, bBlockAddr) := storeMutsWithProjs {}
    ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let bAddr := indcProjAddr bBlockAddr 0
  let mkAddr := ctorProjAddr bBlockAddr 0 0
  -- B is not Prop → large eliminator: lvls 1, Sort (param 0).
  let motiveTy : Ixon.Expr := .all (.ref 0 #[]) (.sort 0)
  let recTyp : Ixon.Expr :=
    .all motiveTy
      (.all (.app (.var 0) (.ref 1 #[]))
        (.all (.ref 0 #[])
          (.app (.var 2) (.var 0))))
  let ruleRhs : Ixon.Expr :=
    if tamperRule then
      .lam motiveTy (.lam (.app (.var 0) (.ref 1 #[])) (.var 1))
    else
      .lam motiveTy (.lam (.app (.var 0) (.ref 1 #[])) (.var 0))
  let recr : Ixon.Recursor :=
    ⟨k, false, 1, 0, 0, 1, 1, recTyp, #[⟨0, ruleRhs⟩]⟩
  let (env, recBlockAddr) := storeMutsWithProjs env
    ⟨.muts #[.recr recr], #[], #[bAddr, mkAddr], #[.var 0]⟩
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

/-! ### Parallel driver (`Ix.Tc.ParCheck`) -/

/-- Env with two passing standalones (A, idA) and a passing inductive
    block (B, B.mk) — 4 targets, mirrors the `checkEnvAnon` lazy test. -/
def parFixtureEnv : Ixon.Env := Id.run do
  let (ixon, aAddr) := envA
  let idDefn : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0,
      .all (.ref 0 #[]) (.ref 0 #[]), .lam (.ref 0 #[]) (.var 0)⟩,
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
  [acceptRejectTests, wellScopedTests, safetyTests, quotTests, blockTests,
   lazyTests, inductiveTests, recursorTests, parallelTests]

end Tests.Tc.CheckTests
