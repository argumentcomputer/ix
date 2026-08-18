/-
  Materialization FFI + `import_ixe` tests (plan C6/C8).

  A self-contained fixture environment is built by direct kernel
  `addDecl` on an empty env (no Init, so the compiled `.ixe` is closed
  over exactly the fixture constants), exercising every ConstantInfo
  kind the materializer must construct — inductives (plain + mutual),
  constructors, kernel-generated recursors, definitions (all three
  reducibility hints, implicit/inst-implicit binders, letE, mdata with
  string/bool/nat/name payloads, `Expr.proj`), theorems, axioms with
  max/imax level polymorphism, and opaques.

  Gates:
  - C6 parity: `rs_decompile_env_consts` output matches the original
    constants field-for-field (types, values, level params, hints,
    recursor rules — the round trip is exact on this fixture).
  - Root equality: recompiling the materialized constants reproduces
    the original canonical root — compile ∘ materialize ∘ compile is a
    fixed point, so every computed field (hashes, cached flags) the
    Rust side produced is byte-faithful under re-reading.
  - Fresh kernel replay: `Ix.Catalog.planDeclarations` over the
    materialized map replays clean into an empty kernel env — the
    non-elaborator core of `import_ixe`.
  - Closure scoping: `only [TIxImp.dbl]` returns the reference closure
    and nothing else.
  - C8: an in-process consumer file `import_ixe`s the artifact and
    defines a term over the materialized constants (interpreter +
    linked FFI, `supportInterpreter`).
-/
module

public import LSpec
public import Ix.ImportIxe
-- The C8 consumer subprocess `import`s Ix.IxEval; importing it here keeps
-- its olean in the test target's build closure (hermetic builds ship only
-- that closure — a local `lake build ix` leftover masked this once).
public import Ix.IxEval
public import Ix.Catalog
public import Ix.CompileM
public import Ix.Meta

public section

open LSpec

namespace Tests.Ix.ImportIxe

/-! ### Fixture environment (kernel-level, Init-free) -/

private def nN : Lean.Name := `TIxImp.N
private def nZero : Lean.Name := `TIxImp.N.zero
private def nSucc : Lean.Name := `TIxImp.N.succ
private def nRec : Lean.Name := `TIxImp.N.rec

private def cN : Lean.Expr := .const nN []
private def eZero : Lean.Expr := .const nZero []
private def eSucc (e : Lean.Expr) : Lean.Expr := .app (.const nSucc []) e
private def type1 : Lean.Expr := .sort (.succ .zero)

private def arrow (a b : Lean.Expr) : Lean.Expr :=
  .forallE `a a b .default

/-- The fixture declarations, in dependency order. -/
private def fixtureDecls : List Lean.Declaration := [
  -- Plain inductive with a recursive constructor (recursor exercised).
  .inductDecl [] 0 [{
    name := nN
    type := type1
    ctors := [
      { name := nZero, type := cN },
      { name := nSucc, type := arrow cN cN } ] }] false,
  -- Prop inductive backing the theorem.
  .inductDecl [] 0 [{
    name := `TIxImp.T
    type := .sort .zero
    ctors := [{ name := `TIxImp.T.intro, type := .const `TIxImp.T [] }] }]
    false,
  -- Structure-shaped inductive for `Expr.proj`.
  .inductDecl [] 0 [{
    name := `TIxImp.P
    type := type1
    ctors := [{
      name := `TIxImp.P.mk
      type := arrow cN (arrow cN (.const `TIxImp.P [])) }] }] false,
  -- Mutual inductive pair (grouped inductDecl, mutual recursors).
  .inductDecl [] 0 [
    { name := `TIxImp.A, type := type1
      ctors := [{ name := `TIxImp.A.mk
                  type := arrow (.const `TIxImp.B []) (.const `TIxImp.A []) }] },
    { name := `TIxImp.B, type := type1
      ctors := [{ name := `TIxImp.B.mk
                  type := arrow (.const `TIxImp.A []) (.const `TIxImp.B []) }] }]
    false,
  -- Doubling via the recursor: const-with-levels, app spine, lambdas.
  .defnDecl {
    name := `TIxImp.dbl
    levelParams := []
    type := arrow cN cN
    value := .lam `n cN
      (Lean.mkApp4 (.const nRec [.succ .zero])
        (.lam `x cN cN .default)
        eZero
        (.lam `a cN (.lam `ih cN (eSucc (eSucc (.bvar 0))) .default) .default)
        (.bvar 0))
      .default
    hints := .regular 2
    safety := .safe
    all := [`TIxImp.dbl] },
  -- Structure projection.
  .defnDecl {
    name := `TIxImp.fst
    levelParams := []
    type := arrow (.const `TIxImp.P []) cN
    value := .lam `p (.const `TIxImp.P []) (.proj `TIxImp.P 0 (.bvar 0))
      .default
    hints := .abbrev
    safety := .safe
    all := [`TIxImp.fst] },
  -- letE with an ordinary dependent-irrelevant binding.
  .defnDecl {
    name := `TIxImp.letD
    levelParams := []
    type := arrow cN cN
    value := .lam `n cN
      (.letE `m cN (eSucc (.bvar 0)) (eSucc (.bvar 0)) false) .default
    hints := .regular 1
    safety := .safe
    all := [`TIxImp.letD] },
  -- mdata wrapping with all constructible payload kinds.
  .defnDecl {
    name := `TIxImp.mdt
    levelParams := []
    type := cN
    value := .mdata
      ((({} : Lean.KVMap).insert `s (.ofString "marker")
        |>.insert `b (.ofBool true)
        |>.insert `n (.ofNat 42)
        |>.insert `nm (.ofName `TIxImp.some.name))
      ) eZero
    hints := .opaque
    safety := .safe
    all := [`TIxImp.mdt] },
  -- Implicit and instance-implicit binders.
  .defnDecl {
    name := `TIxImp.bin
    levelParams := []
    type := .forallE `n cN
      (.forallE `i (.const `TIxImp.T []) cN .instImplicit) .implicit
    value := .lam `n cN
      (.lam `i (.const `TIxImp.T []) (.bvar 1) .instImplicit) .implicit
    hints := .regular 1
    safety := .safe
    all := [`TIxImp.bin] },
  -- Theorem over the Prop inductive.
  .thmDecl {
    name := `TIxImp.thm
    levelParams := []
    type := .const `TIxImp.T []
    value := .const `TIxImp.T.intro []
    all := [`TIxImp.thm] },
  -- Level-polymorphic axioms: max and imax spellings.
  .axiomDecl {
    name := `TIxImp.axm
    levelParams := [`u, `v]
    type := .sort (.max (.param `u) (.param `v))
    isUnsafe := false },
  .axiomDecl {
    name := `TIxImp.axi
    levelParams := [`u, `v]
    type := .sort (.imax (.param `u) (.param `v))
    isUnsafe := false },
  -- Opaque with a value.
  .opaqueDecl {
    name := `TIxImp.opq
    levelParams := []
    type := cN
    value := eZero
    isUnsafe := false
    all := [`TIxImp.opq] } ]

/-- Kernel-replay the fixture into an empty environment and return its
    constants. -/
private def buildFixtureConsts :
    IO (Array (Lean.Name × Lean.ConstantInfo)) := do
  let env ← Lean.mkEmptyEnvironment
  let mut kenv := env.toKernelEnv
  for decl in fixtureDecls do
    match kenv.addDecl {} decl with
    | .ok kenv' => kenv := kenv'
    | .error _ =>
      throw <| IO.userError
        s!"fixture kernel replay failed at {decl.getNames}"
  return kenv.constants.fold (init := #[]) fun acc name info =>
    acc.push (name, info)

/-! ### Comparators -/

private def compareExpr (what : String) (a b : Lean.Expr) :
    Option String :=
  if a == b then none else some s!"{what} differs"

private def compareCI (name : Lean.Name) (a b : Lean.ConstantInfo) :
    Option String := Id.run do
  if a.levelParams != b.levelParams then
    return some s!"{name}: levelParams differ"
  if let some e := compareExpr s!"{name}: type" a.type b.type then
    return some e
  match a, b with
  | .axiomInfo x, .axiomInfo y =>
    if x.isUnsafe != y.isUnsafe then return some s!"{name}: isUnsafe"
  | .defnInfo x, .defnInfo y =>
    if let some e := compareExpr s!"{name}: value" x.value y.value then
      return some e
    if x.hints != y.hints then return some s!"{name}: hints differ"
    if x.safety != y.safety then return some s!"{name}: safety differs"
    if x.all != y.all then return some s!"{name}: all differs"
  | .thmInfo x, .thmInfo y =>
    if let some e := compareExpr s!"{name}: value" x.value y.value then
      return some e
    if x.all != y.all then return some s!"{name}: all differs"
  | .opaqueInfo x, .opaqueInfo y =>
    if let some e := compareExpr s!"{name}: value" x.value y.value then
      return some e
    if x.isUnsafe != y.isUnsafe then return some s!"{name}: isUnsafe"
  | .inductInfo x, .inductInfo y =>
    if x.numParams != y.numParams || x.numIndices != y.numIndices then
      return some s!"{name}: inductive arity differs"
    if x.all != y.all || x.ctors != y.ctors then
      return some s!"{name}: inductive family differs"
    if x.isRec != y.isRec || x.isReflexive != y.isReflexive
        || x.numNested != y.numNested then
      return some s!"{name}: inductive flags differ"
  | .ctorInfo x, .ctorInfo y =>
    if x.induct != y.induct || x.cidx != y.cidx
        || x.numParams != y.numParams || x.numFields != y.numFields then
      return some s!"{name}: constructor shape differs"
  | .recInfo x, .recInfo y =>
    if x.all != y.all || x.numParams != y.numParams
        || x.numIndices != y.numIndices || x.numMotives != y.numMotives
        || x.numMinors != y.numMinors || x.k != y.k then
      return some s!"{name}: recursor shape differs"
    if x.rules.length != y.rules.length then
      return some s!"{name}: rule count differs"
    for (rx, ry) in x.rules.zip y.rules do
      if rx.ctor != ry.ctor || rx.nfields != ry.nfields then
        return some s!"{name}: rule {rx.ctor} shape differs"
      if let some e :=
          compareExpr s!"{name}: rule {rx.ctor} rhs" rx.rhs ry.rhs then
        return some e
  | .quotInfo _, .quotInfo _ => pure ()
  | _, _ => return some s!"{name}: kind differs"
  return none

/-! ### The tests -/

private def roundtripTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := (dir / "fixture.ixe").toString
  try
    let original ← buildFixtureConsts
    let status ← Ix.CompileM.rsCompileEnvBytesFFI original.toList path false
    if status.ungrounded.size > 0 then
      return (false, 0, 0,
        some s!"fixture compile ungrounded: {status.ungrounded}")
    -- C6 parity: materialize everything and compare per constant.
    let materialized ← Ix.ImportIxe.materializeIxe path
    if materialized.size != original.size then
      return (false, 0, 0, some s!"constant count: original \
{original.size}, materialized {materialized.size}")
    let mut origMap : Lean.NameMap Lean.ConstantInfo := {}
    for (n, ci) in original do
      origMap := origMap.insert n ci
    let mut matMap : Lean.NameMap Lean.ConstantInfo := {}
    for (n, ci) in materialized do
      let some oci := origMap.find? n
        | return (false, 0, 0, some s!"unexpected constant {n}")
      if let some e := compareCI n oci ci then
        return (false, 0, 0, some e)
      matMap := matMap.insert n ci
    -- Root equality: recompiling the materialized constants is a fixed
    -- point of the canonical root.
    let path2 := (dir / "rebuilt.ixe").toString
    let status2 ← Ix.CompileM.rsCompileEnvBytesFFI materialized.toList
      path2 false
    if status2.root != status.root then
      return (false, 0, 0, some s!"root drift: {status.root.take 12}… → \
{status2.root.take 12}…")
    -- Fresh kernel replay via the shared planner (import_ixe core).
    let matMapFrozen := matMap
    let plan ← match Ix.Catalog.planDeclarations matMap
        matMapFrozen.find? with
      | .ok plan => pure plan
      | .error e => return (false, 0, 0, some s!"planDeclarations: {e}")
    let emptyEnv ← Lean.mkEmptyEnvironment
    let mut kenv := emptyEnv.toKernelEnv
    for (key, decl) in plan do
      match kenv.addDecl {} decl with
      | .ok kenv' => kenv := kenv'
      | .error _ =>
        return (false, 0, 0, some s!"fresh kernel replay rejected {key}")
    unless kenv.constants.contains `TIxImp.dbl do
      return (false, 0, 0, some "fresh replay lost TIxImp.dbl")
    return (true, original.size, 0, none)
  finally
    IO.FS.removeDirAll dir

private def closureTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := (dir / "fixture.ixe").toString
  try
    let original ← buildFixtureConsts
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI original.toList path false
    let subset ← Ix.ImportIxe.materializeIxe path #[`TIxImp.dbl]
    let names : Std.HashSet Lean.Name :=
      subset.foldl (fun s (n, _) => s.insert n) {}
    let checks : List (String × Bool) := [
      ("dbl present", names.contains `TIxImp.dbl),
      ("N pulled in", names.contains nN),
      ("N.succ pulled in", names.contains nSucc),
      ("N.rec pulled in", names.contains nRec),
      ("axiom excluded", !names.contains `TIxImp.axm),
      ("theorem excluded", !names.contains `TIxImp.thm),
      ("proj fixture excluded", !names.contains `TIxImp.P) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, subset.size, 0, none)
  finally
    IO.FS.removeDirAll dir

/-- C8: a consumer file `import_ixe`s the fixture artifact through the
    real command elaborator (in-process frontend + interpreter) and
    defines a term over the materialized constants. -/
private def elabTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let ixePath := (dir / "fixture.ixe").toString
  let consumerPath := dir / "Consumer.lean"
  try
    let original ← buildFixtureConsts
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI original.toList ixePath false
    -- Materialized constants carry no compiled code (kernel-level
    -- import), so consumer definitions over them are `noncomputable`;
    -- execution is `#ixeval`'s job, Lean-native code the post-hoc LCNF
    -- path (plan D5).
    IO.FS.writeFile consumerPath
      s!"import Ix.ImportIxe\n\
         import Ix.IxEval\n\
         import_ixe \"{ixePath}\"\n\
         noncomputable def Consumer.uses : TIxImp.N := TIxImp.dbl \
         (TIxImp.N.succ TIxImp.N.zero)\n\
         theorem Consumer.alsoUses : TIxImp.T := TIxImp.thm\n\
         #ixeval TIxImp.dbl (TIxImp.N.succ TIxImp.N.zero)\n"
    let env ← getFileEnv consumerPath
    let checks : List (String × Bool) := [
      ("consumer def elaborated", env.contains `Consumer.uses),
      ("consumer theorem elaborated", env.contains `Consumer.alsoUses),
      ("materialized inductive present", env.contains nN),
      ("materialized recursor present", env.contains nRec),
      ("materialized defn present", env.contains `TIxImp.dbl) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)
  catch e =>
    return (false, 0, 0, some s!"consumer elaboration failed: {e}")
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO "materialize ∘ compile is exact and root-stable" none
    roundtripTest .done,
  .individualIO "only-scoped materialization returns the closure" none
    closureTest .done,
  .individualIO "import_ixe elaborates a consumer file (C8)" none
    elabTest .done ]

end Tests.Ix.ImportIxe
