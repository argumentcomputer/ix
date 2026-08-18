/-
  `import_ixe`: materialize a `.ixe`'s constants into the current
  elaboration environment.

  The `.ixe` is ix's fundamental artifact (plan D5 — no olean layer
  anywhere): a consumer file writes `import_ixe "catalog.ixe"` and the
  catalog's qualified constants become referenceable source-level
  names, kernel-checked on the way in. The heavy lifting happens in
  Rust: `rs_decompile_env_consts` decompiles the artifact and hands
  back real `Lean.ConstantInfo` object graphs (constructed through the
  toolchain's exported `lean_expr_mk_*` constructors, so hashes and
  cached flags are Lean's own); the Lean side reconstructs kernel
  `Declaration`s with the shared `Ix.Catalog.planDeclarations` planner
  and replays them with `Lean.addDecl`.

  Semantics:
  - Names already present in the environment are skipped, trusting the
    shared toolchain base (the `.ixe` carries its complete base; the
    consumer already has one). Genuine content drift surfaces as
    kernel errors on dependents — fail closed, never silent overwrite.
  - Declarations are added with `forceExpose := true`: materialized
    bodies stay transparent even when the consumer file is in module
    mode — Ix punches through the Lean module system (plan D6).
  - `import_ixe "path" only [n₁, n₂]` materializes just the named
    constants plus their full reference closure (computed Rust-side) —
    the bounded-cost import for large catalogs (plan DQ2).
  - Kernel-level only: instances, attributes, and native code do not
    transfer. Instance constants arrive as ordinary definitions; apps
    re-register them locally with `attribute [instance]` as needed.
  - No compiled code either: consumer definitions that *use*
    materialized constants must be `noncomputable` (the LCNF backend
    has no signatures for them). Theorems, types, and specifications
    work unrestricted; execution goes through IxVM (`#ixeval`), and
    Lean-native compilation is the post-hoc decompile-then-LCNF path
    (plan D5).

  Paths resolve relative to the process working directory (for
  `lake build`, the workspace root).

  Note on qualification: bare `Name`/`ConstantInfo` inside the `Ix`
  namespace resolve to ix's own mirror types, so Lean's are
  `Lean.`-qualified explicitly throughout (repo convention).
-/
module

public import Lean
public meta import Ix.Catalog

public section

namespace Ix.ImportIxe

/-- Decompile a `.ixe` and materialize constants as real
    `Lean.ConstantInfo`s, in Rust
    (`crates/ffi/src/compile.rs::rs_decompile_env_consts`, construction
    in `crates/ffi/src/lean_build.rs`). Empty `only` ⇒ every named
    constant; nonempty ⇒ the requested constants plus their reference
    closure. Fails on thin bundles, broken closures, and absent
    requested names. Pairs return sorted by name. -/
@[extern "rs_decompile_env_consts"]
opaque rsDecompileEnvConstsFFI : @& String → @& Array Lean.Name →
    IO (Array (Lean.Name × Lean.ConstantInfo))

/-- Meta twin of `rsDecompileEnvConstsFFI`, binding the same symbol:
    the `import_ixe` elaborator chain is `meta` and may only reference
    `meta` declarations, while compiled programs and tests use the
    plain twin. -/
@[extern "rs_decompile_env_consts"]
meta opaque rsDecompileEnvConstsMetaFFI : @& String → @& Array Lean.Name →
    IO (Array (Lean.Name × Lean.ConstantInfo))

def materializeIxe (path : String) (only : Array Lean.Name := #[]) :
    IO (Array (Lean.Name × Lean.ConstantInfo)) :=
  rsDecompileEnvConstsFFI path only

/-- Add materialized constants to the environment by checked kernel
    replay in dependency order, skipping names already present.
    Returns `(declarations replayed, constants skipped)`. -/
meta def addMaterialized (consts : Array (Lean.Name × Lean.ConstantInfo)) :
    Lean.CoreM (Nat × Nat) := do
  let env ← Lean.getEnv
  let mut owned : Lean.NameMap Lean.ConstantInfo := {}
  let mut skipped := 0
  for (name, info) in consts do
    if env.contains name then
      skipped := skipped + 1
    else
      owned := owned.insert name info
  let ownedFrozen := owned
  let find? := fun n => (ownedFrozen.find? n).orElse fun _ => env.find? n
  let plan ← match Ix.Catalog.planDeclarations owned find? with
    | .ok plan => pure plan
    | .error e => throwError "import_ixe: {e}"
  let mut replayed := 0
  for (_, decl) in plan do
    -- forceExpose: materialized bodies stay transparent under the
    -- module system (plan D6).
    Lean.addDecl decl (forceExpose := true)
    replayed := replayed + 1
  return (replayed, skipped)

meta def runImportIxe (path : String) (only : Array Lean.Name := #[]) :
    Lean.Elab.Command.CommandElabM Unit := do
  let consts ← rsDecompileEnvConstsMetaFFI path only
  let (replayed, skipped) ←
    Lean.Elab.Command.liftCoreM (addMaterialized consts)
  Lean.logInfo m!"import_ixe {path}: {consts.size} constants \
materialized, {replayed} declarations replayed, {skipped} already \
present"

/-- `import_ixe "catalog.ixe"` materializes every constant of the
    artifact into the current environment;
    `import_ixe "catalog.ixe" only [A.foo, B.bar]` materializes just
    the named constants plus their reference closure. -/
syntax (name := importIxe) "import_ixe " str
    (" only " "[" ident,* "]")? : command

open Lean Elab Command in
@[command_elab importIxe]
meta def elabImportIxe : CommandElab := fun stx => do
  match stx with
  | `(command| import_ixe $path:str) =>
      runImportIxe path.getString
  | `(command| import_ixe $path:str only [$names:ident,*]) =>
      runImportIxe path.getString (names.getElems.map (·.getId))
  | _ => throwUnsupportedSyntax

end Ix.ImportIxe

end
