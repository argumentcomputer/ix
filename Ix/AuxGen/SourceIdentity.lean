module
public import Ix.AuxGen.CasesOn
public import Ix.AuxGen.RecOn
public import Ix.Compile.Image.Expr
public section

namespace Ix.AuxGen.SourceIdentity

open Ix.Compile.Image (alphaEq)
open Ix.Compile.Image.RawExact (nameEq)

/-- Put declared universe parameters in positional form. Unknown parameters
and metavariables fail; two failed conversions never constitute a match.
This only renames parameters, without normalizing universe arithmetic. -/
def level (params : Array Name) : Level → Option Level
  | .zero _ => some Level.mkZero
  | .succ u _ => Level.mkSucc <$> level params u
  | .max u v _ => Level.mkMax <$> level params u <*> level params v
  | .imax u v _ => Level.mkIMax <$> level params u <*> level params v
  | .param n _ => do
    let i ← params.findIdx? (nameEq n ·)
    return Level.mkParam (Name.mkNat Name.mkAnon i)
  | .mvar .. => none

/-- Parameter renaming for a closed declaration. Constant and projection
identities stay exact; binders and metadata are compared by `alphaEq` later.
Open free variables and metavariables cannot authenticate a source helper. -/
def expr (params : Array Name) : Expr → Option Expr
  | .bvar i _ => some (Expr.mkBVar i)
  | .fvar .. | .mvar .. => none
  | .sort u _ => Expr.mkSort <$> level params u
  | .const n us _ => Expr.mkConst n <$> us.mapM (level params)
  | .app f a _ => Expr.mkApp <$> expr params f <*> expr params a
  | .lam n t b bi _ => Expr.mkLam n <$> expr params t <*> expr params b <*> pure bi
  | .forallE n t b bi _ => Expr.mkForallE n <$> expr params t <*> expr params b <*> pure bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n <$> expr params t <*> expr params v <*> expr params b <*> pure nd
  | .lit l _ => some (Expr.mkLit l)
  | .mdata md e _ => Expr.mkMData md <$> expr params e
  | .proj n i e _ => Expr.mkProj n i <$> expr params e

/-- Conservative syntactic correspondence, including the actual body. Cached
expression hashes do not establish equality. Universe binder spellings may
differ, but their positions and all constant references must agree. -/
def agrees (leftParams rightParams : Array Name) (left right : Expr) : Bool :=
  match expr leftParams left, expr rightParams right with
  | some left, some right => alphaEq left right
  | _, _ => false

/-- A generated definition can identify a source definition only when its
kind, safety, universe arity, type and value agree. Reducibility hints and
binder presentation do not identify the helper's meaning. -/
def definitionMatches (expected : AuxDef) (source : ConstantInfo) : Bool :=
  match source with
  | .defnInfo actual =>
    nameEq expected.name actual.cnst.name &&
      actual.safety == (if expected.isUnsafe then .unsafe else .safe) &&
      expected.levelParams.size == actual.cnst.levelParams.size &&
      agrees expected.levelParams actual.cnst.levelParams expected.typ actual.cnst.type &&
      agrees expected.levelParams actual.cnst.levelParams expected.value actual.value
  | _ => false

/-- Reconstruct `casesOn` or `recOn` from the *source* recursor. In particular,
the canonical recursor of a collapsed block is not a source-body oracle.
Generation failure merely declines this recognition. -/
def wrapper? (env : Environment) (name : Name) : Option AuxDef := do
  let .str parent suffix _ := name | none
  let some (.recInfo rv) := env.get? (Name.mkStr parent "rec") | none
  if suffix == "recOn" then
    generateRecOn name rv
  else if suffix == "casesOn" then
    let cenv : Ix.CompileM.CompileEnv :=
      { env, nameToNamed := {}, constants := {}, blobs := {}, totalBytes := 0 }
    let benv : Ix.CompileM.BlockEnv :=
      { all := {}, current := name, mutCtx := {}, univCtx := [] }
    match Ix.CompileM.CompileM.run cenv benv {} (generateCasesOn name rv) with
    | .ok (candidate, _) => candidate
    | .error _ => none
  else none

/-- Name lookup chooses a candidate; successful body correspondence licenses
the standard-wrapper interpretation. Other auxiliary families need their own
source construction/recognition contracts. -/
def checkedWrapper? (env : Environment) (name : Name) : Option AuxDef := do
  let candidate ← wrapper? env name
  let actual ← env.get? name
  if definitionMatches candidate actual then some candidate else none

/-- Guard the two simple wrapper families at production optimization call
sites. Other heads retain their existing checks; this is not authentication
of `below`, `brecOn`, equation lemmas or arbitrary generated auxiliaries. -/
def permitsOptimization (env : Environment) (name : Name) : Bool :=
  match name with
  | .str _ "casesOn" _ | .str _ "recOn" _ => (checkedWrapper? env name).isSome
  | _ => true

end Ix.AuxGen.SourceIdentity
