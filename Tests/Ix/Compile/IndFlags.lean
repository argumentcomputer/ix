/-
  compile-ind-flags: both compilers refuse an input inductive whose stored
  flags (`isRec`, `isReflexive`, `numNested`) differ from the recomputed
  ones (Rust `validate_ind_groups`, Lean `Ix.CompileM.validateInductiveFlags`),
  and compile the same closure with the true flags byte-identically.

  The closure is `T` (a recursive inductive) with its recursor and the
  aux-gen seeds; the refused neighbour stores `isRec := false` on `T`. The
  Lean refusal is checked on both Lean drivers: the IO pipeline
  (`compileLeanConsts`, the parallel driver) and the pure compiler
  (`Ix.Cert.compile`, the sequential driver).

  The second domain restriction: both compilers refuse a mutual block whose
  members disagree on safety (Rust `validate_mutual_safety`, Lean
  `Ix.CompileM.validateMutualSafety`). Its fixtures are a safe and an unsafe
  mutual inductive pair and an unsafe mutual definition pair, each compiled
  as stored (every leg, byte-identically) and with one member forged to the
  other safety (an inductive with its constructors and recursor; a
  definition to safe, and one to partial): every leg refuses with the same
  text.

  Run with: `lake test -- --ignored compile-ind-flags`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.Cert.Compile
import LSpec

open Lean

namespace Tests.Ix.Compile.IndFlags

namespace Fixture

/-- A recursive inductive: Lean's stored `isRec` is `true`. -/
inductive T where
  | leaf : T
  | node : T → T

-- Safe mutual inductives, each referring to the other.
mutual
inductive SA where
  | a0 : SA
  | a : SB → SA
inductive SB where
  | b0 : SB
  | b : SA → SB
end

-- Unsafe mutual inductives, each referring to the other.
mutual
unsafe inductive UA where
  | a0 : UA
  | a : UB → UA
unsafe inductive UB where
  | b0 : UB
  | b : UA → UB
end

-- Unsafe mutual definitions, each referring to the other.
mutual
unsafe def uf : Nat → Nat
  | 0 => 0
  | n + 1 => ug n
unsafe def ug : Nat → Nat
  | 0 => 1
  | n + 1 => uf n
end

end Fixture

def tName : Name := ``Fixture.T

/-- The aux-gen seed names (`Ix.CompileM.auxGenSeedNames`), as Lean names. -/
def auxSeeds : List Name :=
  [``PUnit, ``PProd, ``Eq, ``Eq.refl, ``Eq.symm, ``Eq.ndrec, ``rfl, ``HEq,
    ``HEq.refl, ``eq_of_heq, ``True]

/-- The closure of `T`, with `T`'s stored `isRec` replaced by `isRec`. -/
def closure (env : Environment) (isRec : Bool) :
    Except String (List (Name × ConstantInfo)) := do
  let base := Ix.EnvScope.collectDeps env ([tName, tName ++ `rec] ++ auxSeeds)
  let some (.inductInfo v) := env.find? tName | throw "T missing"
  unless v.isRec do throw "T is not recursive"
  return base.map fun (n, ci) =>
    if n == tName then (n, .inductInfo { v with isRec }) else (n, ci)

/-- The expected refusal's text, without the error-kind prefix. -/
def flagsMessage : String :=
  s!"non-canonical inductive flags for '{tName}': stored isRec=false \
isReflexive=false numNested=0, computed isRec=true isReflexive=false numNested=0"

/-- Rust (`ix compile`, fail-closed): `ok bytes`, or the refusal text. -/
def rust (env : Environment) (cs : List (Name × ConstantInfo)) (out : System.FilePath) :
    IO (Except String ByteArray) := do
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env cs)
  try
    let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared out.toString false
    if let some (n, m) := status.ungrounded[0]? then
      return .error s!"{n}: {m}"
    return .ok (← IO.FS.readBinFile out)
  catch e => return .error (toString e)

/-- The Lean IO pipeline (`compile-lean`): `ok bytes`, or the refusal text. -/
def lean (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Except String ByteArray) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env cs).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := 1) with
  | .error e => return .error e
  | .ok o =>
    if let some (n, m) := o.cenv.ungrounded.toList.head? then
      return .error s!"{n}: {m}"
    return .ok o.bytes

/-- The pure compiler (`Ix.Cert.compile`): `ok bytes`, or the refusal text. -/
def pure (cs : List (Name × ConstantInfo)) : Except String ByteArray := do
  let consts := (Ix.CanonM.canonChunk cs.toArray).foldl (init := {}) fun m (n, c) =>
    m.insert n c
  let ixe ← Ix.Cert.compile { consts }
  Ixon.serEnv ixe

/-! ## Mixed safety -/

/-- A closure with the aux-gen seeds. -/
def closureOf (env : Environment) (roots : List Name) : List (Name × ConstantInfo) :=
  Ix.EnvScope.collectDeps env (roots ++ auxSeeds)

/-- Forge inductive `n`'s safety: the inductive, its constructors and its
    recursor. -/
def forgeInductive (n : Name) (isUnsafe : Bool) (cs : List (Name × ConstantInfo)) :
    List (Name × ConstantInfo) :=
  cs.map fun (m, ci) => match ci with
    | .inductInfo v => if m == n then (m, .inductInfo { v with isUnsafe }) else (m, ci)
    | .ctorInfo v => if v.induct == n then (m, .ctorInfo { v with isUnsafe }) else (m, ci)
    | .recInfo v => if m == n ++ `rec then (m, .recInfo { v with isUnsafe }) else (m, ci)
    | _ => (m, ci)

/-- Forge definition `n`'s safety. -/
def forgeDefinition (n : Name) (safety : DefinitionSafety) (cs : List (Name × ConstantInfo)) :
    List (Name × ConstantInfo) :=
  cs.map fun (m, ci) => match ci with
    | .defnInfo v => if m == n then (m, .defnInfo { v with safety }) else (m, ci)
    | _ => (m, ci)

/-- The mixed-safety refusal's text in a leg's error, to the end of its line or the
    closing quote of Rust's debug rendering. -/
def safetyRefusal? (e : String) : Option String :=
  match e.splitOn "mixed safety in a mutual block" with
  | _ :: rest :: _ =>
    some ("mixed safety in a mutual block" ++ (((rest.splitOn "\n").headD "").splitOn "\"").headD "")
  | _ => none

/-- A leg's outcome, for a failure line. -/
def showLeg : Except String ByteArray → String
  | .ok b => s!"compiled ({b.size} bytes)"
  | .error e => e

/-- Every leg compiles `cs`, byte-identically; returns the failures. -/
def checkCompiles (env : Environment) (dir : System.FilePath) (label : String)
    (cs : List (Name × ConstantInfo)) : IO Nat := do
  match ← rust env cs (dir / s!"{label}.ixe"), ← lean env cs, pure cs with
  | .ok r, .ok l, .ok p =>
    if r == l && l == p then
      IO.println s!"[ind-flags] {label}: all three compile, byte-identical ({r.size} bytes)"
      return 0
    IO.println s!"[ind-flags] {label}: FAIL: outputs differ \
(rust {r.size}, lean {l.size}, pure {p.size} bytes)"
    return 1
  | r, l, p =>
    IO.println s!"[ind-flags] {label}: FAIL: rust {showLeg r}; lean {showLeg l}; \
pure {showLeg p}"
    return 1

/-- Every leg refuses `cs` with the same mixed-safety text, naming two
    members; returns the failures. -/
def checkMixedSafety (env : Environment) (dir : System.FilePath) (label : String)
    (cs : List (Name × ConstantInfo)) : IO Nat := do
  let legs := [← rust env cs (dir / s!"{label}.ixe"), ← lean env cs, pure cs]
  let texts := legs.map fun result => match result with
    | .ok _ => none
    | .error e => safetyRefusal? e
  match texts with
  | some t :: rest =>
    if rest.all (· == some t) && (t.splitOn "' is ").length == 3 then
      IO.println s!"[ind-flags] {label}: all three refuse: {t}"
      return 0
  | _ => Pure.pure ()
  IO.println s!"[ind-flags] {label}: FAIL: {legs.map showLeg}"
  return 1

/-- The mixed-safety fixtures: the true closures compile, the forged ones
    are refused by every leg. -/
def safetyCases (env : Environment) (dir : System.FilePath) : IO Nat := do
  let safeInd := closureOf env [``Fixture.SA, ``Fixture.SA.rec, ``Fixture.SB.rec]
  let unsafeInd := closureOf env [``Fixture.UA, ``Fixture.UA.rec, ``Fixture.UB.rec]
  let unsafeDef := closureOf env [``Fixture.uf]
  let mut failures := 0
  failures := failures + (← checkCompiles env dir "safe inductives" safeInd)
  failures := failures + (← checkCompiles env dir "unsafe inductives" unsafeInd)
  failures := failures + (← checkCompiles env dir "unsafe definitions" unsafeDef)
  failures := failures + (← checkMixedSafety env dir "safe inductives, SA forged unsafe"
    (forgeInductive ``Fixture.SA true safeInd))
  failures := failures + (← checkMixedSafety env dir "unsafe inductives, UA forged safe"
    (forgeInductive ``Fixture.UA false unsafeInd))
  failures := failures + (← checkMixedSafety env dir "unsafe definitions, uf forged safe"
    (forgeDefinition ``Fixture.uf .safe unsafeDef))
  failures := failures + (← checkMixedSafety env dir "unsafe definitions, ug forged partial"
    (forgeDefinition ``Fixture.ug .partial unsafeDef))
  return failures

def run : IO UInt32 := do
  let env ← get_env!
  let dir ← IO.FS.createTempDir
  let mut failures := 0
  try
    let good ← IO.ofExcept (closure env true)
    let bad ← IO.ofExcept (closure env false)
    -- valid neighbour: every leg compiles, byte-identically
    match ← rust env good (dir / "good.ixe"), ← lean env good, pure good with
    | .ok r, .ok l, .ok p =>
      if r == l && l == p then
        IO.println s!"[ind-flags] true flags: all three compile, byte-identical ({r.size} bytes)"
      else
        failures := failures + 1
        IO.println s!"[ind-flags] true flags: FAIL: outputs differ \
(rust {r.size}, lean {l.size}, pure {p.size} bytes)"
    | r, l, p =>
      failures := failures + 1
      IO.println s!"[ind-flags] true flags: FAIL: rust {r.isOk}, lean {l.isOk}, pure {p.isOk}"
    -- stored `isRec := false`: every leg refuses with the same message
    let legs := [("rust", ← rust env bad (dir / "bad.ixe")), ("lean", ← lean env bad),
      ("pure", pure bad)]
    for (label, result) in legs do
      match result with
      | .ok _ =>
        failures := failures + 1
        IO.println s!"[ind-flags] stored isRec=false: {label}: FAIL: compiled"
      | .error e =>
        if (e.splitOn flagsMessage).length > 1 then
          IO.println s!"[ind-flags] stored isRec=false: {label} refuses: {flagsMessage}"
        else
          failures := failures + 1
          IO.println s!"[ind-flags] stored isRec=false: {label}: FAIL: other refusal: {e}"
    failures := failures + (← safetyCases env dir)
  finally
    IO.FS.removeDirAll dir
  IO.println s!"[ind-flags] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.IndFlags
