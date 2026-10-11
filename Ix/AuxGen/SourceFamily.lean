module
public import Ix.AuxGen.Patches
public import Ix.AuxGen.SourceIdentity
public section

namespace Ix.AuxGen.SourceFamily

open Ix.Compile.Image.RawExact (nameEq)
open Ix.CompileM (CompileEnv BlockEnv CompileM)

/-- Source recipes use the original mutual order and recursors. They never
identify a source helper with a generator run over the canonical layout. -/
inductive Recipe where
  | definition (expected : AuxDef)
  | theoremDecl (expected : AuxDef)
  | inductiveDecl (expected : BelowIndc) (all : Array Name)
  | constructor (expected : BelowCtor) (owner : Name) (params : Array Name)
      (index : Nat) (isUnsafe : Bool)

def Recipe.name : Recipe → Name
  | .definition d | .theoremDecl d => d.name
  | .inductiveDecl d _ => d.name
  | .constructor d .. => d.name

def namesAgree (a b : Array Name) : Bool :=
  a.size == b.size && (a.zip b).all (fun (x, y) => nameEq x y)

def signatureMatches (name : Name) (params : Array Name) (type : Expr)
    (actual : ConstantVal) : Bool :=
  nameEq name actual.name && params.size == actual.levelParams.size &&
    SourceIdentity.agrees params actual.levelParams type actual.type

/-- Definition bodies participate in source identification. For a theorem,
the checked statement determines its use by proof irrelevance; dependencies
of that statement are still authenticated. Inductive signatures include every
constructor and the complete source mutual membership. -/
def Recipe.matches (recipe : Recipe) (actual : ConstantInfo) : Bool :=
  match recipe, actual with
  | .definition expected, actual => SourceIdentity.definitionMatches expected actual
  | .theoremDecl d, .thmInfo actual =>
    !d.isUnsafe && signatureMatches d.name d.levelParams d.typ actual.cnst
  | .inductiveDecl d all, .inductInfo actual =>
    signatureMatches d.name d.levelParams d.typ actual.cnst &&
      d.nParams == actual.numParams && d.nIndices == actual.numIndices &&
      d.isUnsafe == actual.isUnsafe && d.isReflexive == actual.isReflexive &&
      actual.numNested == 0 && namesAgree all actual.all &&
      namesAgree (d.ctors.map (·.name)) actual.ctors
  | .constructor d owner params index isUnsafe, .ctorInfo actual =>
    signatureMatches d.name params d.typ actual.cnst && nameEq owner actual.induct &&
      index == actual.cidx && d.nParams == actual.numParams &&
      d.nFields == actual.numFields && isUnsafe == actual.isUnsafe
  | _, _ => false

/-- References without a cached-hash deduplication step. Metadata does not
contribute semantic dependencies; projection owners do. -/
def exprReferences : Expr → Array Name
  | .const name .. => #[name]
  | .app f a _ => exprReferences f ++ exprReferences a
  | .lam _ t b _ _ | .forallE _ t b _ _ => exprReferences t ++ exprReferences b
  | .letE _ t v b _ _ => exprReferences t ++ exprReferences v ++ exprReferences b
  | .mdata _ e _ => exprReferences e
  | .proj name _ e _ => #[name] ++ exprReferences e
  | _ => #[]

def Recipe.references : Recipe → Array Name
  | .definition d => exprReferences d.typ ++ exprReferences d.value
  | .theoremDecl d => exprReferences d.typ
  | .inductiveDecl d all => all ++ d.ctors.map (·.name) ++ exprReferences d.typ
  | .constructor d .. => exprReferences d.typ

/-- Check the requested recipe and every recipe it refers to. A visited node
still checks its actual source lookup before cutting the traversal, so a
structurally equal name with a different cache cannot bypass declaration
checking. Mutual below inductives need no cyclic unchecked assumption. -/
def authenticatedVisit (env : Environment) (recipes : Array Recipe) :
    Nat → Array Name → Name → Option (Array Name)
  | 0, _, _ => none
  | fuel + 1, seen, name =>
    match recipes.find? (fun recipe => nameEq recipe.name name), env.get? name with
    | some recipe, some actual =>
      if nameEq name actual.getCnst.name && recipe.matches actual then
        if seen.any (nameEq name) then some seen else
        recipe.references.foldlM (fun visited dependency =>
          if recipes.any (fun r => nameEq r.name dependency) then
            authenticatedVisit env recipes fuel visited dependency
          else some visited) (seen.push name)
      else none
    | _, _ => none

/-- Share visited nodes across sibling edges. Dense mutual below families
must not enumerate every simple path through their dependency graph. -/
def authenticated (env : Environment) (recipes : Array Recipe)
    (fuel : Nat) (seen : Array Name) (name : Name) : Bool :=
  (authenticatedVisit env recipes fuel seen name).isSome

def isDerived (name : Name) : Bool :=
  let family (s : String) :=
    s == "below" || s.startsWith "below_" || s == "brecOn" || s.startsWith "brecOn_"
  match name with
  | .str (.str _ s _) sub _ =>
    family sub || ((sub == "go" || sub == "eq") && (s == "brecOn" || s.startsWith "brecOn_"))
  | .str _ s _ => family s
  | _ => false

def isBRecOn (name : Name) : Bool :=
  let family (s : String) := s == "brecOn" || s.startsWith "brecOn_"
  match name with
  | .str (.str _ s _) sub _ => family sub || ((sub == "go" || sub == "eq") && family s)
  | .str _ s _ => family s
  | _ => false

def propFormer : Expr → Bool
  | .forallE _ _ body _ _ | .mdata _ body _ => propFormer body
  | .sort (.zero _) _ => true
  | _ => false

/-- Reuse the actual generators with original source recursors and a fresh
source-only bridge. No compiled addresses, canonical classes or rewritten
overlay participate in identifying the supplied source declaration. -/
def reconstruct (source : Environment) (all : Array Name) (includeBRecOn : Bool := true) :
    Except String (Array Recipe) := do
  let env := { source with overlay := {} }
  let some owner := all[0]? | throw "source auxiliary family is empty"
  let some (.inductInfo ind) := env.get? owner | throw "source auxiliary owner is absent"
  unless namesAgree all ind.all do throw "source auxiliary mutual order differs"
  let classes := all.map (fun n => #[n])
  let mut recs : Array (Name × RecursorVal) := #[]
  let recNames := all.map (·.mkStr "rec") ++
    (Array.range ind.numNested).map (fun i => owner.mkStr s!"rec_{i + 1}")
  for name in recNames do
    let some (.recInfo rv) := env.get? name | throw s!"source recursor absent: {name.pretty}"
    unless nameEq name rv.cnst.name && namesAgree all rv.all do
      throw s!"source recursor family differs: {name.pretty}"
    recs := recs.push (name, rv)
  let action : KBridgeM (Array Recipe) := do
    let maps : AddrMaps := { nameToAddr := fun _ => none }
    let isProp := propFormer ind.cnst.type
    let below ← generateBelowConstants classes recs isProp maps (allAux := true)
    let brecon ← if includeBRecOn then do
        populateCanonKenvWithBelow below classes maps
        generateBreconConstants classes recs below isProp maps (allAux := true)
      else pure #[]
    let belowAll := below.filterMap fun b => match b with
      | .indc i => some i.name
      | _ => none
    let mut recipes := #[]
    for b in below do
      match b with
      | .defn d => recipes := recipes.push (.definition {
          name := d.name, levelParams := d.levelParams, typ := d.typ,
          value := d.value, isUnsafe := d.isUnsafe })
      | .indc i =>
        recipes := recipes.push (.inductiveDecl i belowAll)
        for (ctor, index) in i.ctors.zipIdx do
          recipes := recipes.push (.constructor ctor i.name i.levelParams index i.isUnsafe)
    for d in brecon do
      let expected : AuxDef := {
        name := d.name, levelParams := d.levelParams, typ := d.typ,
        value := d.value, isUnsafe := d.isUnsafe }
      let isEq := match d.name with | .str _ "eq" _ => true | _ => false
      recipes := recipes.push (if !d.isUnsafe && (d.isProp || isEq) then
        .theoremDecl expected else .definition expected)
    return recipes
  let cenv : CompileEnv := { env, nameToNamed := {}, constants := {}, blobs := {}, totalBytes := 0 }
  let benv : BlockEnv := { all := {}, current := owner, mutCtx := {}, univCtx := [] }
  let ((recipes, _), _) ← (CompileM.run cenv benv {} (action AuxKernelCtx.new)).mapError toString
  return recipes

/-- Evaluate family recognition once when selecting image heads, before the
heads can be published or made available to occurrence optimizations. -/
def filterHeads (env : Environment) (all heads : Array Name) : Array Name := Id.run do
  if !heads.any isDerived then return heads
  let recipes := (reconstruct env all (heads.any isBRecOn)).toOption.getD #[]
  return heads.filter fun name =>
    !isDerived name || authenticated { env with overlay := {} } recipes (recipes.size + 1) #[] name

end Ix.AuxGen.SourceFamily

end
