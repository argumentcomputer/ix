import Lean
import Ix.Address
import Ix.CompileM

open Lean

open System (FilePath)

open Elab in
def getFileEnv (path : FilePath) : IO Environment := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["setup-file", path.toString]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  let paths := split.replace "\"" "" |>.splitOn ","|>.map FilePath.mk
  initSearchPath (← findSysroot) paths

  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default
  let stt ← IO.processCommands inputCtx parserState commandState
  let msgs := stt.commandState.messages
  if msgs.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← msgs.toList.mapM (·.toString)).map String.trim
  else return stt.commandState.env

elab "this_file!" : term => do
  let ctx ← readThe Core.Context
  let srcPath := FilePath.mk ctx.fileName
  return ToExpr.toExpr srcPath

macro "get_env!" : term =>
  `(getFileEnv this_file!)

def computeIxAddress (env: Lean.Environment) (const : ConstantInfo) : IO MetaAddress := do
  let (addr, _) <- (Ix.compileConst const >>= Ix.dematerializeConst).runIO env
  return addr

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


