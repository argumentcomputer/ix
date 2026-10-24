module
public import Ix.AuxGen.CasesOn
public import Ix.AuxGen.RecOn
public import Ix.Compile.Image.MotiveEq
public section

/-!
# Source-body recognition of the simple recursor wrappers

A source `X.casesOn` or `X.recOn` may be Lean's generated wrapper or a user
declaration that only shares its name. Names choose a candidate; recognition
regenerates the wrapper from the *source* recursor (`generateCasesOn`,
`generateRecOn`) and compares the actual declaration with it, body included.
Only a recognized wrapper may later be replaced by the compiler's own form.
Nothing on the compile path calls these functions yet.

Mirrors Rust `aux_gen/source_identity.rs`.
-/

namespace Ix.AuxGen.SourceIdentity

open Ix.Compile.Image (exprEqWith motiveUniv)
open Ix.Compile.Image.RawExact (nameEq)

/-- Universes agree when their positional forms are equal: each parameter by
its position in its own declaration's list (`motiveUniv`, the image
generator's converter: complete raw names), with no universe arithmetic
normalized. Unknown parameters and metavariables never agree. -/
def levelAgrees (leftParams rightParams : Array Name) (left right : Level) : Bool :=
  match motiveUniv leftParams left, motiveUniv rightParams right with
  | some left, some right => left == right
  | _, _ => false

/-- No free variables or metavariables: an open expression cannot
authenticate a source helper. -/
def closed : Expr → Bool
  | .fvar .. | .mvar .. => false
  | .app f a _ => closed f && closed a
  | .lam _ t b _ _ | .forallE _ t b _ _ => closed t && closed b
  | .letE _ t v b _ _ => closed t && closed v && closed b
  | .mdata _ e _ | .proj _ _ e _ => closed e
  | _ => true

/-- Conservative syntactic correspondence, including the actual body:
`exprEqWith` (binder names, binder info and let flags do not count, metadata
must be paired, constant and projection names are compared exactly) with
universes by position. Cached expression hashes do not establish equality. -/
def agrees (leftParams rightParams : Array Name) (left right : Expr) : Bool :=
  closed left && closed right && exprEqWith (levelAgrees leftParams rightParams) left right

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
    let benv : Ix.CompileM.BlockEnv :=
      { all := {}, current := name, mutCtx := {}, univCtx := [] }
    match Ix.CompileM.CompileM.run (Ix.CompileM.CompileEnv.new env) benv {}
        (generateCasesOn name rv) with
    | .ok (candidate, _) => candidate
    | .error _ => none
  else none

/-- Name lookup chooses a candidate; successful body correspondence licenses
the standard-wrapper interpretation. Other auxiliary families need their own
source construction/recognition contracts (`Ix.AuxGen.SourceFamily`). -/
def checkedWrapper? (env : Environment) (name : Name) : Option AuxDef := do
  let candidate ← wrapper? env name
  let actual ← env.get? name
  if definitionMatches candidate actual then some candidate else none

/-- Whether a call site may treat `name` as the standard wrapper: a
`casesOn`/`recOn` head only when recognized; any other head is not this
module's decision. Not authentication of `below`, `brecOn`, equation lemmas
or arbitrary generated auxiliaries. -/
def permitsOptimization (env : Environment) (name : Name) : Bool :=
  match name with
  | .str _ "casesOn" _ | .str _ "recOn" _ => (checkedWrapper? env name).isSome
  | _ => true

end Ix.AuxGen.SourceIdentity

end
