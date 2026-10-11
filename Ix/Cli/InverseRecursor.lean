/-
  A qualified reading of a permuted canonical recursor in Lean, for phase 9.
  The stored image supplies a bijection of motives/minors and universes;
  its inverse defines the canonical name over the original Lean recursor.
  This is a correspondence assumption, not a consequence of phase 7 and not
  a proof of the compiler image. Collapsed/split blocks and non-permutation
  images remain explicitly unsupported.
-/
module
public import Lean.Meta
public import Ix.Ixon
public section

namespace IxCliqueValues.InverseRecursor

open Lean Meta

structure Permutation where
  /-- Canonical argument position → source argument position. -/
  args : Array Nat
  /-- Canonical universe position → source universe position. -/
  levels : Array Nat
  deriving Inhabited

def isPermutation (p : Array Nat) (n : Nat) : Bool :=
  p.size == n && (List.range n).all (fun i => (p.filter (· == i)).size == 1)

def inverse (p : Array Nat) : Except String (Array Nat) := do
  unless isPermutation p p.size do throw "not a complete bijection"
  return (List.range p.size).toArray.map fun i => (p.findIdx? (· == i)).getD p.size

/-- Keep parameters, indices and the major in their original positions.
Only motives and minors may move, each within its own complete segment. -/
def preservesSegments (r : RecursorVal) (p : Array Nat) : Bool :=
  isPermutation p (r.numParams + r.numMotives + r.numMinors + r.numIndices + 1) &&
  (p.zipIdx).all fun (j, i) =>
    if i < r.numParams then j == i
    else if i < r.numParams + r.numMotives then
      r.numParams ≤ j && j < r.numParams + r.numMotives
    else if i < r.numParams + r.numMotives + r.numMinors then
      r.numParams + r.numMotives ≤ j && j < r.numParams + r.numMotives + r.numMinors
    else j == i

/-- Read the actual developed image, without unfolding the canonical head.
Packed slots, projections, relocation/adapters and dropped arguments are not
guessed to be permutations. -/
def readPermutation (source canonical : RecursorVal) (image : DefinitionVal) : MetaM Permutation := do
  unless !source.isUnsafe && !canonical.isUnsafe && image.safety == .safe &&
      source.numParams == canonical.numParams && source.numMotives == canonical.numMotives &&
      source.numMinors == canonical.numMinors && source.numIndices == canonical.numIndices &&
      image.levelParams.length == source.levelParams.length do
    throwError "inverse correspondence: recursor/image telescopes differ"
  let sourceLevels := source.levelParams.map Level.param
  let imageType := image.type.instantiateLevelParams image.levelParams sourceLevels
  unless ← withTransparency .all (isDefEq imageType source.type) do
    throwError "inverse correspondence: image statement differs from the source recursor"
  let value := image.value.instantiateLevelParams image.levelParams sourceLevels
  lambdaTelescope value fun xs body => do
    let body := body.headBeta.consumeMData
    let .const head us := body.getAppFn | throwError "inverse correspondence: image has no direct recursor head"
    unless head == canonical.name do throwError "inverse correspondence: image targets another recursor"
    let mut args := #[]
    for arg in body.getAppArgs do
      let some i := xs.findIdx? (· == arg.consumeMData)
        | throwError "inverse correspondence: image argument is not a telescope variable"
      args := args.push i
    unless xs.size == args.size && preservesSegments source args do
      throwError "inverse correspondence: image is not a complete motive/minor permutation"
    let mut levels := #[]
    for u in us do
      let .param p := u | throwError "inverse correspondence: universe argument is not a parameter"
      let some i := source.levelParams.toArray.findIdx? (· == p)
        | throwError "inverse correspondence: foreign universe parameter"
      levels := levels.push i
    unless canonical.levelParams.length == source.levelParams.length &&
        isPermutation levels source.levelParams.length do
      throwError "inverse correspondence: universe arguments are not a complete permutation"
    return { args, levels }

/-- The same application constructor is used by the bridge and the negative
control. The full bridge additionally checks its dependent type below. -/
def applyInverse (source : Name) (p : Permutation) (us : Array Level) (xs : Array Expr) : Except String Expr := do
  unless us.size == p.levels.size && xs.size == p.args.size do throw "inverse correspondence: arity"
  let pi ← inverse p.args
  let ui ← inverse p.levels
  return mkAppN (mkConst source (ui.map (us[·]!)).toList) (pi.map (xs[·]!))

def definition (source canonical : RecursorVal) (p : Permutation) : MetaM DefinitionVal := do
  unless preservesSegments source p.args do throwError "inverse correspondence: invalid argument permutation"
  let us := canonical.levelParams.toArray.map Level.param
  let value ← forallTelescope canonical.type fun xs result => do
    let body ← ofExcept (applyInverse source.name p us xs)
    -- `inferType` alone does not check the types of every application
    -- argument. In particular a wrong minor permutation can keep the
    -- result type while exchanging incompatible dependent hypotheses.
    check body
    unless ← withTransparency .all (isDefEq (← inferType body) result) do
      throwError "inverse correspondence: inverse application has the wrong result type"
    mkLambdaFVars xs body
  return { canonical.toConstantVal with value, hints := .abbrev, safety := .safe, all := [canonical.name] }

/-- The source owner of a display name, including nested `rec_j` suffixes. -/
def sourceOwner? : Name → Option Name
  | .str p "_ix" => some p
  | .str p _ | .num p _ => sourceOwner? p
  | .anonymous => none

/-- Read only inductive projections. In particular an image definition is
not evidence that two original inductive types were kept distinct. -/
def memberKey? (env : Ixon.Env) (n : Name) : Option (Address × Nat) := do
  let nd ← env.named.get? (Ix.Name.fromLeanName n)
  let c ← env.getConst? nd.addr
  let .iPrj p := c.info | none
  return (p.block, p.idx.toNat)

/-- A single complete physical inductive block with distinct original members.
The source order must actually change. Collapsed and split blocks are refused
before any image is inverted. Extra canonical inductives are unsupported. -/
def requirePermuted (env : Ixon.Env) (all : List Name) : Except String Unit := do
  unless !all.isEmpty && all.all (fun n => (all.filter (· == n)).length == 1) do
    throw "inverse correspondence: empty or repeated source members"
  let keys ← all.toArray.mapM fun n => match memberKey? env n with
    | some k => pure k
    | none => throw s!"inverse correspondence: no inductive projection for {n}"
  let (block, _) := keys[0]!
  unless keys.all (·.1 == block) do throw "inverse correspondence: split block is unsupported"
  let positions := keys.map (·.2)
  unless positions.all (fun i => (positions.filter (· == i)).size == 1) do
    throw "inverse correspondence: collapsed block is unsupported"
  let some c := env.getConst? block | throw "inverse correspondence: missing physical block"
  let .muts ms := c.info | throw "inverse correspondence: expected a physical mutual block"
  let inds := ms.zipIdx.filterMap fun (m, i) => match m with | .indc _ => some i | _ => none
  unless positions.size == inds.size && positions.all inds.contains do
    throw "inverse correspondence: incomplete source/canonical member correspondence"
  unless positions != inds do throw "inverse correspondence: block is not a member permutation"

structure Bridge where
  decl : DefinitionVal
  source : Name
  permutation : Permutation

/-- Select the source recursor by its stored image's canonical head. Never
infer an inverse from the suffix spelling or phase-7 forward-rule success. -/
def build (env : Ixon.Env) (read : Ix.Name → Except String ConstantInfo)
    (canonical : RecursorVal) : MetaM Bridge := do
  let some owner := sourceOwner? canonical.name | throwError "inverse correspondence: no source block owner"
  let some (.inductInfo iv) := (← getEnv).find? owner
    | throwError "inverse correspondence: owner is not a source inductive"
  ofExcept (requirePermuted env iv.all)
  let recs := iv.all.toArray.map (·.str "rec") ++
    (List.range iv.numNested).toArray.map (fun i => iv.all.head!.str s!"rec_{i + 1}")
  let mut found : Option Bridge := none
  for n in recs do
    let some (.recInfo source) := (← getEnv).find? n | continue
    let some nd := env.named.get? (Ix.Name.fromLeanName n) | continue
    if nd.original.isNone then continue
    let .ok (.defnInfo image) := read (Ix.Name.fromLeanName n) | continue
    let head := image.value.consumeMData.getLambdaBody.headBeta.consumeMData.getAppFn
    unless head.isConstOf canonical.name do continue
    if found.isSome then throwError "inverse correspondence: multiple images target {canonical.name}"
    let permutation ← readPermutation source canonical image
    let decl ← definition source canonical permutation
    found := some { decl, source := n, permutation }
  let some bridge := found | throwError "inverse correspondence: no direct bijective recursor image for {canonical.name}"
  return bridge

end IxCliqueValues.InverseRecursor
end
