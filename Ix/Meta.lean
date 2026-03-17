module
public import Lean.Meta.Reduce
public import Ix.Address
public import Ix.CompileM

public section

open Lean

open System (FilePath)

/-- Uses `LEAN_PATH` if set, otherwise falls back to `lake env printenv LEAN_PATH`. -/
def initLeanSearchPath (cwd : Option FilePath := none) : IO Unit := do
  if (← IO.getEnv "LEAN_PATH").isNone then
    let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd }
    let paths := out.stdout.trimAscii.toString.splitOn ":" |>.map FilePath.mk
    initSearchPath (← findSysroot) paths
  else
    initSearchPath (← findSysroot)

open Elab in
/-- Loads a Lean `Environment` from a file path provided at runtime -/
def getFileEnv (path : FilePath) : IO Environment := do
  let path ← IO.FS.realPath path
  initLeanSearchPath path.parent
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeaderCore
    (HeaderSyntax.startPos header) (HeaderSyntax.imports header)
    (isModule := false) default messages inputCtx 0
  if messages.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← messages.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)
  return env

/-- Captures the current module and its imports at compile time. -/
elab "this_file!" : term => do
  let env ← getEnv
  return toExpr (env.header.imports.map (·.module) |>.push env.header.mainModule)

/-- Loads a Lean `Environment` from compiled `.olean` files. -/
def getCompileEnv (imports : Array Name) : IO Environment := do
  initLeanSearchPath
  importModules (imports.map ({ module := · : Import })) default

macro "get_env!" : term =>
  `(getCompileEnv this_file!)

def runCore (f : CoreM α) (env : Environment) : IO α :=
  Prod.fst <$> f.toIO { fileName := default, fileMap := default } { env }

def runMeta (f : MetaM α) (env : Environment) : IO α :=
  Prod.fst <$> f.toIO { fileName := default, fileMap := default } { env }

def metaMakeList (α: Lean.Expr) (names: List Lean.Name) : MetaM Expr := do
  let nil <- Meta.mkAppOptM ``List.nil #[.some α]
  names.foldrM (fun n t => Meta.mkAppOptM ``List.cons #[.some α, mkConst n, t]) nil

def metaMakeDef [Lean.ToExpr α] (a: α) : MetaM (List Lean.Name × Lean.Expr × Lean.Expr) := do
  let val := Lean.toExpr a
  let typ <- Meta.inferType val
  let lvls := (Lean.collectLevelParams default typ).params.toList
  return (lvls, typ, val)

def metaMakeEvalClaim (func: Lean.Name) (args : List Lean.Expr)
  : MetaM (List Lean.Name × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let input <- Meta.mkAppM func args.toArray
  let output <- Meta.reduce input
  let type <- Meta.inferType output
  let sort <- Meta.inferType type
  let lvls := (Lean.collectLevelParams default input).params.toList
  return (lvls, input, output, type, sort)

end
