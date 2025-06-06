import Cli
import Ix.Cronos
import Ix.Common
import Ix.CompileM
import Ix.Store
import Ix.Address
import Ix.Meta
import Lean

open Ix.Compile

--❯ ix prove IxTest.lean "id'"
--typechecking:
--id' (A : Type) (x : A) : A
--claim: #bbd740022aa44acd553c52e156807a5571428220a926377fe3c57d63b06a99f4 : #ba33b735b743386477f7a0e6802c67d388c165cab0e34b04880b50270205f265 @ #0000000000000000000000000000000000000000000000000000000000000000
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
    (checkClaim constInfo.name constInfo.type constSort constInfo.levelParams commit).runIO env
  IO.println $ s!"claim: {claim}"
  -- TODO: prove
  return 0

def mkConst' (constName : Lean.Name) : Lean.MetaM Lean.Expr := do
  return Lean.mkConst constName (← (← Lean.getConstInfo constName).levelParams.mapM fun _ => Lean.Meta.mkFreshLevelMVar)

--ix prove IxTest.lean "id'" --eval=Nat,one
--evaluating:
--id' (A : Type) (x : A) : A
--id' Nat one
--  ~> 1
--  : Nat
--  @ []
--claim: #88ba2a7b099ce94a030eef202dc26ee3d9eb088057830049b926c7e88044bba1 ~> #d5ea7e6e7a3ee02780ba254a0becfe1fe712436a5a30832095ab71f7c64e25cd : #41ba41a9691e8167a387046f736a82ce0ec1601e7fb996c58d5930887c4b7764 @ #0000000000000000000000000000000000000000000000000000000000000000
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
  let ((claim, _, _), _stt) <- (evalClaim lvls input output type sort commit).runIO env
  IO.println $ s!"claim: {claim}"
  -- TODO: prove
  return 0



def runProve (p: Cli.Parsed): IO UInt32 := do
  let input : String       := p.positionalArg! "input" |>.as! String
  let const : String       := p.positionalArg! "const" |>.as! String
  StoreIO.toIO Store.ensureStoreDir
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
