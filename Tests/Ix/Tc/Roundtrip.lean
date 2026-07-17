module

public import LSpec
public import Ix.Tc
public import Ix.CompileM
public import Ix.CanonM
public import Ix.Meta
public import Ix.Common
public import Tests.Ix.Tc.AnonDiff
public import Tests.Ix.Tc.IxonFixtures

/-!
Kernel ↔ Ixon roundtrip (`tc-roundtrip` ignored suite + `tc-unit` entries).

Two halves, mirroring the Rust `kernel-ixon-roundtrip`'s scope:

**Anon** (structural): every constant of a Rust-compiler-produced env is
ingressed into the pure-Lean kernel, egressed back to an `Ixon.Constant`,
and compared **structurally** against the original (canonical forms —
sharing expanded, tables renumbered, universes reduced; see
`Ix.Tc.Egress`). Projections compare byte-exact. Certifies exactly the
kernel-held, hash-relevant structure.

**Meta** (full fidelity): the whole env is meta-ingressed (phase-parallel:
chunked local envs merged via `KEnv.union`), every named entry is egressed
back to `Ix.ConstantInfo` (`Ix.Tc.EgressLean`), and compared against
`CanonM.canonConst` of the source Lean constant with Rust `compare_envs`
semantics — LEON content hashes are name/info/mdata-sensitive, so this
certifies metadata fidelity too. Skipped with counts: aux-rewritten
entries (`original.isSome` — decompile regenerates those) and
altering-surgery entries (`metaHasAlteringSurgery` — only decompile's
surgery replay can restore their source form); `notFound` (ixon names
absent from the Lean env) is informational, as in Rust.

Layers:
- `unitTests` (runs in `tc-unit`, no FFI): hand-built fixture envs roundtrip
  clean; tampered kernel constants are **caught** (comparator-teeth
  negatives — proves the canonical comparison can't be satisfied vacuously).
- `suite` (`tc-roundtrip`, ignored): Rust-compiled seed closures with full
  coverage accounting, then the ENTIRE current Lean env (`get_env!`) —
  anon and meta. Parallel over the task pool. Arbitrary Lean files (and
  external `.ixe` images) go through `ix validate-lean` instead, which
  shares the same drivers (`Ix.Tc.Validate`).
-/

namespace Tests.Tc.Roundtrip

open LSpec
open Ix.Tc

public section

/-- Roundtrip every work item of an env (shared driver:
    `Ix.Tc.anonRoundtripEnv`). -/
def roundtripAll (ixonEnv : Ixon.Env) : Nat × Option String :=
  anonRoundtripEnv ixonEnv

/-! ### Fixture roundtrips + tamper negatives (`tc-unit`) -/

open Tests.Tc.Fixtures in
/-- All hand-built fixture envs roundtrip clean. Exercises: axioms, defns
    with refs, nat/str literal blobs, `share` normalization, mutual `recur`
    blocks with projections, inductive blocks with ctor projections. -/
def fixtureTests : TestSeq := Id.run do
  let cases : List (String × Ixon.Env) :=
    [ ("axiom", envA.1),
      ("defn with ref", envIdA.1),
      ("nat literal blob", envNatLit.1),
      ("str literal blob", envStrLit.1),
      ("shared subterms", envShare.1),
      ("mutual defs block", envMutualDefs.1),
      ("inductive block", envInductive.1) ]
  let mut ts : TestSeq := .done
  for (label, env) in cases do
    let (rows, err?) := roundtripAll env
    let msg := match err? with | some e => s!" — {e}" | none => ""
    ts := ts ++ test s!"roundtrip fixture: {label} ({rows} rows){msg}" err?.isNone
  return ts

open Tests.Tc.Fixtures in
/-- Ingress a standalone fixture constant and hand back
    `(original, kernel constant)` for tampering. -/
def ingressedStandalone (env : Ixon.Env) (addr : Address) :
    Except String (Ixon.Constant × KConst .anon) := do
  let go : IngressM (Ixon.Constant × KConst .anon) := do
    let some original ← IngressM.liftExcept (getConstVerified env addr)
      | throw s!"missing {addr}"
    let selfId ← ingressAnonStandalone env addr original
    let some kc := (← get).get? selfId
      | throw "ingressed constant absent"
    return (original, kc)
  match go.run {} with
  | .ok r _ => .ok r
  | .error e _ => .error e

/-- A tampered kernel constant must NOT survive the canonical comparison. -/
def tamperCaught (original : Ixon.Constant) (tampered : KConst .anon)
    (selfAddr : Address) : Bool :=
  match egressStandalone tampered selfAddr with
  | .error _ => true  -- egress itself rejecting the tamper also counts
  | .ok egressed =>
    match roundtripCompare original egressed with
    | .ok none => false
    | .ok (some _) => true
    | .error _ => true

open Tests.Tc.Fixtures in
/-- Standalone recursor fixture (`R.rec`-shaped): one rule, for the
    dropped-rule tamper. -/
def envRecrStandalone : Ixon.Env × Address := Id.run do
  let (env, aAddr) := envA
  let r : Ixon.Recursor :=
    ⟨false, false, 0, 0, 0, 1, 1, .ref 0 #[], #[⟨0, .ref 0 #[]⟩]⟩
  let c : Ixon.Constant := ⟨.recr r, #[], #[aAddr], #[]⟩
  let addr := Address.blake3 (Ixon.serConstant c)
  return (env.storeConst addr c, addr)

open Tests.Tc.Fixtures in
/-- Standalone defn whose value is a `letE` (for the nonDep-flip tamper). -/
def envLetDefn : Ixon.Env × Address := Id.run do
  let (env, aAddr) := envA
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[],
      .letE true (.ref 0 #[]) (.ref 0 #[]) (.var 0)⟩,
     #[], #[aAddr], #[]⟩
  let addr := Address.blake3 (Ixon.serConstant c)
  return (env.storeConst addr c, addr)

/-- Tamper 1: swap a defn's value for its type. -/
def tamperDefnValue : Bool :=
  let (env, _, idAddr) := Tests.Tc.Fixtures.envIdA
  match ingressedStandalone env idAddr with
  | .error _ => false
  | .ok (orig, kc) =>
    match kc with
    | .defn n lp kind safety hints lvls ty _ la block =>
      tamperCaught orig (.defn n lp kind safety hints lvls ty ty la block)
        idAddr
    | _ => false

/-- Tamper 2: flip a letE nonDep flag. -/
def tamperLetNonDep : Bool :=
  let (envL, letAddr) := envLetDefn
  match ingressedStandalone envL letAddr with
  | .error _ => false
  | .ok (orig, kc) =>
    match kc with
    | .defn n lp kind safety hints lvls ty val la block =>
      match val with
      | .letE _ lty lval lbody nd _ =>
        let val' := KExpr.mkLet () lty lval lbody (!nd)
        tamperCaught orig
          (.defn n lp kind safety hints lvls ty val' la block) letAddr
      | _ => false
    | _ => false

/-- Tamper 3: drop a recursor rule. -/
def tamperRecrRules : Bool :=
  let (envR, recAddr) := envRecrStandalone
  match ingressedStandalone envR recAddr with
  | .error _ => false
  | .ok (orig, kc) =>
    match kc with
    | .recr n lp k u lvls ps is ms mns block mi ty _ la =>
      tamperCaught orig
        (.recr n lp k u lvls ps is ms mns block mi ty #[] la) recAddr
    | _ => false

/-- Tamper 4: bump a recursor's minors count (header field). -/
def tamperRecrMinors : Bool :=
  let (envR, recAddr) := envRecrStandalone
  match ingressedStandalone envR recAddr with
  | .error _ => false
  | .ok (orig, kc) =>
    match kc with
    | .recr n lp k u lvls ps is ms mns block mi ty rules la =>
      tamperCaught orig
        (.recr n lp k u lvls ps is ms (mns + 1) block mi ty rules la)
        recAddr
    | _ => false

def negativeTests : TestSeq :=
  test "tamper caught: defn value replaced by type" tamperDefnValue
  ++ test "tamper caught: letE nonDep flipped" tamperLetNonDep
  ++ test "tamper caught: recursor rule dropped" tamperRecrRules
  ++ test "tamper caught: recursor minors bumped" tamperRecrMinors

/-- Registered in `tc-unit` (pure Lean, no FFI). -/
def unitTests : List TestSeq := [fixtureTests, negativeTests]

/-! ### Rust-compiled closures (`tc-roundtrip`, ignored) -/

/-- Compile a seed closure through the Rust compiler and roundtrip every
    constant of the resulting env. -/
def roundtripOnSeeds (leanEnv : Lean.Environment) (label : String)
    (seeds : List Lean.Name) : IO (Nat × Option String) := do
  let consts := Tests.Tc.AnonDiff.closureOf leanEnv seeds
  if consts.isEmpty then
    return (0, some s!"empty closure for {seeds}")
  let dir ← IO.FS.createTempDir
  let path := dir / s!"tc-roundtrip-{label}.ixe"
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  match Ixon.deEnvAnon bytes with
  | .error e => return (0, some s!"deEnvAnon failed: {e}")
  | .ok ixonEnv => return roundtripAll ixonEnv

def seedSets : List (String × List Lean.Name) :=
  Tests.Tc.AnonDiff.seedSets ++
  [ ("inductives-recursors",
      [`Nat.rec, `List.rec, `Acc.rec, `WellFounded.fix, `Prod.rec,
       `PSigma.rec, `Or.rec]) ]

def closureSuite : TestSeq := Id.run do
  let mut ts : TestSeq := .done
  for (label, seeds) in seedSets do
    ts := ts ++ .individualIO s!"roundtrip closure: {label}" none (do
      let env ← get_env!
      let (rows, err?) ← roundtripOnSeeds env label seeds
      return (err?.isNone, rows, 0, err?)) .done
  return ts

/-- Whole-environment roundtrip: compile the ENTIRE current Lean env through
    the Rust compiler and roundtrip every constant of the result — the
    direct analog of the Rust `kernel-ixon-roundtrip`'s input scope. For
    external `.ixe` files (e.g. `compilemathlib.ixe`), use
    `ix roundtrip-tc <path>` instead. -/
def wholeEnvSuite : TestSeq :=
  .individualIO "roundtrip whole get_env environment" none (do
    let leanEnv ← get_env!
    let consts := leanEnv.constants.toList
    let dir ← IO.FS.createTempDir
    let path := dir / "tc-roundtrip-whole-env.ixe"
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
    let bytes ← IO.FS.readBinFile path
    IO.FS.removeDirAll dir
    match Ixon.deEnvAnon bytes with
    | .error e => return (false, 0, 0, some s!"deEnvAnon failed: {e}")
    | .ok ixonEnv =>
      let (rows, err?) := roundtripAll ixonEnv
      return (err?.isNone, rows, 0, err?)) .done

/-! ### Meta roundtrip (kernel → Lean, `compare_envs` semantics)

The full-fidelity half: pure-parse the Rust-compiled env, meta-ingress the
WHOLE env into one shared kernel env (phase 1, parallel chunked local envs
merged via `KEnv.union`), then egress every named entry back to
`Ix.ConstantInfo` and compare content hashes against `CanonM.canonConst`
of the source Lean constant (phase 2, parallel) — Rust
`rs_kernel_roundtrip`/`compare_envs` semantics: type hash always, value
hash for defn/thm/opaque, per-rule RHS for recursors; missing Lean-side
names are informational `notFound`; aux-rewritten entries
(`original.isSome`) are skipped with a count (their anon-structural
fidelity is covered by the anon roundtrip above). -/

/-- Compile `consts` through the Rust compiler and run the shared meta
    roundtrip driver (`Ix.Tc.metaRoundtripEnv`) against `leanEnv`. -/
def metaRoundtripOn (leanEnv : Lean.Environment) (label : String)
    (consts : List (Lean.Name × Lean.ConstantInfo)) :
    IO (Ix.Tc.MetaRoundtripReport × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := dir / s!"tc-meta-roundtrip-{label}.ixe"
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  let ixonEnv ← match Ixon.deEnv bytes with
    | .ok env => pure env
    | .error e => return ({}, some s!"pure deEnv failed: {e}")
  match metaRoundtripEnv leanEnv ixonEnv with
  | .error e => return ({}, some e)
  | .ok report =>
    if report.errorCount == 0 then
      return (report, none)
    else
      let shown := report.errors.toSubarray 0 (min 5 report.errors.size)
        |>.toArray
      let msgs := shown.map fun (n, m) => s!"{n}: {m}"
      return (report,
        some s!"{report.errorCount} comparison error(s); first: \
                {String.intercalate " | " msgs.toList}")

def metaClosureSuite : TestSeq := Id.run do
  let mut ts : TestSeq := .done
  for (label, seeds) in seedSets do
    ts := ts ++ .individualIO s!"meta roundtrip closure: {label}" none (do
      let env ← get_env!
      let consts := Tests.Tc.AnonDiff.closureOf env seeds
      let (report, err?) ← metaRoundtripOn env label consts
      return (err?.isNone, report.checked, 0, err?)) .done
  return ts

/-- The centerpiece: meta roundtrip of the WHOLE current Lean env. -/
def metaWholeEnvSuite : TestSeq :=
  .individualIO "meta roundtrip whole get_env environment" none (do
    let leanEnv ← get_env!
    let (report, err?) ←
      metaRoundtripOn leanEnv "whole-env" leanEnv.constants.toList
    IO.println s!"[tc-meta-roundtrip] checked {report.checked}, \
                  notFound {report.notFound}, skippedAux {report.skippedAux}, \
                  skippedSurgery {report.skippedSurgery}"
    return (err?.isNone, report.checked, 0, err?)) .done

public def suite : List TestSeq :=
  [closureSuite, wholeEnvSuite, metaClosureSuite, metaWholeEnvSuite]

end

end Tests.Tc.Roundtrip
