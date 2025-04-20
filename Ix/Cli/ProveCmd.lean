import Cli
import Ix.Cronos
import Ix.Common
import Ix.CompileM
import Ix.Store
import Ix.Address
import Ix.Meta
import Lean

-- ix prove eval AcmeInput
-- ix prove eval --address deadbeef
-- ix prove eval AcmeFun AcmeArg1 AcmeArg2
-- ix prove eval --address abcde 1234 5678
-- ix prove check --name AcmeTheo
-- ix prove check --address deadbeef


def runProveCheck 
  (env: Lean.Environment)
  (constInfo: Lean.ConstantInfo)
  (commit: Bool)
  : IO UInt32
  := do
  let constSort <- runMeta (Lean.Meta.inferType constInfo.type) env
  let signature <- runMeta (Lean.PrettyPrinter.ppSignature constInfo.name) env
  IO.println "typechecking:"
  IO.println signature.fmt.pretty
  let ((claim, _, _), _stt) <- 
    (Ix.Compile.checkClaim constInfo.name constInfo.type constSort
    constInfo.levelParams commit).runIO' 200000 (.init env)
  IO.println $ s!"claim: {claim}"
  -- TODO: prove
  return 0

def mkConst' (constName : Lean.Name) : Lean.MetaM Lean.Expr := do
  return Lean.mkConst constName (← (← Lean.getConstInfo constName).levelParams.mapM fun _ => Lean.Meta.mkFreshLevelMVar)

def runProveEval
  (env: Lean.Environment)
  (constInfo: Lean.ConstantInfo)
  (args: Array String)
  (commit: Bool)
  : IO UInt32
  := do
  let signature <- runMeta (Lean.PrettyPrinter.ppSignature constInfo.name) env
  let args : Array Lean.Expr <- args.mapM $ fun a => do
    let argInfo <- match env.constants.find? a.toName with
      | some c => runMeta (mkConst' c.name) env
      | none => throw $ IO.userError s!"unknown constant {a.toName}"
  let (lvls, input, output, type, sort) <- 
    runMeta (metaMakeEvalClaim constInfo.name (args.toList)) env
  IO.println "evaluating:"
  IO.println signature.fmt.pretty
  let inputPretty <- runMeta (Lean.Meta.ppExpr input) env
  let outputPretty <- runMeta (Lean.Meta.ppExpr output) env
  let typePretty <- runMeta (Lean.Meta.ppExpr type) env
  IO.println s!"{inputPretty}"
  IO.println s!"  ~> {outputPretty}"
  IO.println s!"  : {typePretty}"
  IO.println s!"  @ {repr lvls}"
  let ((claim, _, _), _stt) <- 
    (Ix.Compile.evalClaim lvls input output type sort commit).runIO' 200000 (.init env)
  IO.println $ s!"claim: {claim}"
  -- TODO: prove
  return 0



def runProve (p: Cli.Parsed): IO UInt32 := do
  let input : String       := p.positionalArg! "input" |>.as! String
  let const : String       := p.positionalArg! "const" |>.as! String
  let path := ⟨input⟩
  Lean.setLibsPaths input
  let env ← Lean.runFrontend (← IO.FS.readFile path) path
  let constInfo <- match env.constants.find? const.toName with
    | some c => pure c
    | none => throw $ IO.userError s!"unknown constant {const.toName}"
  let commit := p.hasFlag "commit"
  if let some evalArgs := p.flag? "eval"
  then runProveEval env constInfo (evalArgs.as! (Array String)) commit
  else runProveCheck env constInfo commit
  return 0


def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProve;
  "Generates a ZK proof of a given Lean constant"

  FLAGS:
    cron, "cronos"   : String; "enable Cronos timings"
    eval, "eval"     : Array String; "prove evaluation with arguments"

  ARGS:
   input  : String; "Source file input"
   const  : String; "constant name"
]
