module
public import Lean.Meta.Reduce
public import Ix.Address
public import Ix.CompileM

public section

open Lean

open System (FilePath)

open Elab in
def getFileEnv (path : FilePath) : IO Environment := do
  let path ← IO.FS.realPath path
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "printenv", "LEAN_PATH"]
    cwd := path.parent
  }
  let paths := out.stdout.trimAscii.toString.splitOn ":" |>.map FilePath.mk
  initSearchPath (← findSysroot) paths

  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header default messages inputCtx 0
  if messages.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← messages.toList.mapM (·.toString)).map (String.trimAscii · |>.toString)
  return env

elab "this_file!" : term => do
  let ctx ← readThe Core.Context
  let srcPath := FilePath.mk ctx.fileName
  return ToExpr.toExpr srcPath

macro "get_env!" : term =>
  `(getFileEnv this_file!)


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
