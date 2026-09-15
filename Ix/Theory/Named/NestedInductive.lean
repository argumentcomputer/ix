/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Inductive

open Ix.Theory (VLevel)

/-!
# Nested-inductive flattening

The Theory mirror of the kernel's `ElimNestedInductive` transformation,
with representation probes in `Verify/Environment/NestedRepresentation.lean`:
the stored
payload of a nested declaration is the source `VInductDecl`, and nested
support flows through an additive artifact coupling

1. the flattened mutual block, an ordinary `VInductDecl` handled by the
   existing arbitrary-block analyzer, and
2. one auxiliary specification per auxiliary family — the Theory analog of
   the kernel's `aux2nested` map.

`nestedElimination?` computes both from the source declaration plus the
caller-supplied metadata of the previously declared inductives that are
nested into (`NestedTargetBlock`).  Keeping the target metadata an explicit
input keeps this analyzer environment-free, exactly like `checked?`;
`NestedTargetBlock.WF` separately ties the supplied copy to a Theory
environment.

The transformation mirrors the kernel phase for phase:

- An application `I Ds is` is a nested occurrence when `I` is a family of a
  supplied target block, the spine covers at least `I`'s parameters, and
  the parametric arguments `Ds` mention a family of the growing flattened
  block.  Parametric arguments that also mention a constructor-local binder
  reject the declaration (the kernel's "parameters cannot contain local
  variables"), and matched occurrences are rewritten without descending
  into the emitted replacement, exactly like `Expr.replace`.
- One auxiliary family is created per family of `I`'s block, in `all`
  order, with `I`'s family and constructor types level-instantiated at the
  occurrence's levels and parameter-instantiated at `Ds`; auxiliary
  constructor bodies are queued and flattened by the same loop until the
  block is stable.
- Auxiliary names are canonical: `(`_nested` ++ familyName).appendIndexAfter i`
  with a global counter, matching the kernel's choice whenever the ambient
  environment contains no colliding `_nested.*` constant. The representation
  collision probe shows the choice is erased from all final artifacts, and
  in-block collisions are rejected downstream by `blockNamesOK` exactly
  where the kernel's `checkName` rejects its own collisions.

Acceptance (`nestedStage3`) is flattening success plus generation
readiness of the flattened block through the block analyzer and generator.
Generation artifacts are subsequently restored by the substitution defined
in this module; environment replay is verified separately.
-/

namespace Ix.Theory.Named

deriving instance DecidableEq for VConstant
deriving instance DecidableEq for VDefEq
deriving instance DecidableEq for VConstVal
deriving instance DecidableEq for VInductiveType
deriving instance DecidableEq for VInductDecl

/-- Does `e` mention, through a loose bvar, one of the `k` binders directly
below its root?  `d` counts binders passed inside `e` itself. -/
def VExpr.hasLooseBelow (k : Nat) : VExpr → (d : Nat := 0) → Bool
  | .bvar i, d => d ≤ i && i - d < k
  | .sort _, _ | .const .., _ => false
  | .app e1 e2, d => e1.hasLooseBelow k d || e2.hasLooseBelow k d
  | .lam e1 e2, d | .forallE e1 e2, d =>
      e1.hasLooseBelow k d || e2.hasLooseBelow k (d+1)

/-- Lower every loose bvar of `e` by `n`.  Total; meaningful only when no
loose bvar lies below `n`, which callers establish with `hasLooseBelow`. -/
def VExpr.lowerN (n : Nat) : VExpr → (d : Nat := 0) → VExpr
  | .bvar i, d => if i < d then .bvar i else .bvar (i - n)
  | .sort l, _ => .sort l
  | .const c ls, _ => .const c ls
  | .app e1 e2, d => .app (e1.lowerN n d) (e2.lowerN n d)
  | .lam e1 e2, d => .lam (e1.lowerN n d) (e2.lowerN n (d+1))
  | .forallE e1 e2, d => .forallE (e1.lowerN n d) (e2.lowerN n (d+1))

namespace VInductDecl

/-- Simultaneous outermost-first parameter substitution: the first list
element replaces the outermost of the `args.length` innermost loose bvars.
The same shape as `instantiateRev` on the implementation side. -/
def instRevParams : VExpr → List VExpr → VExpr
  | C, [] => C
  | C, e :: es => instRevParams (C.inst e es.length) es

/-- Substitute the leading `np`-binder telescope of `ty` simultaneously at
`args` (outermost parameter first), mirroring the kernel's
`instantiateForallParams`.  Fails when `ty` exposes fewer than `np`
binders. -/
def instTelescope (np : Nat) (ty : VExpr) (args : List VExpr) :
    Option VExpr := do
  guard (args.length == np)
  guard ((VExpr.telN np ty).length == np)
  return instRevParams (VExpr.dropN np ty) args

/-- One previously declared mutual block that nested occurrences may point
into.  `families` is the complete block in `all` order, in that block's own
universe parameters; a copy is supplied so the analyzer stays
environment-free, and `NestedTargetBlock.WF` ties the copy to an
environment. -/
structure NestedTargetBlock where
  nparams : Nat
  families : List VInductiveType

/-- The supplied target copy agrees with the environment's stored
constants. -/
structure NestedTargetBlock.WF (env : VEnv) (block : NestedTargetBlock) :
    Prop where
  families : ∀ f ∈ block.families,
    env.constants f.name = some f.toVConstVal.toVConstant
  ctors : ∀ f ∈ block.families, ∀ c ∈ f.ctors,
    env.constants c.name = some c.toVConstant

def NestedTargetsWF (env : VEnv) (targets : List NestedTargetBlock) : Prop :=
  ∀ t ∈ targets, t.WF env

/-- One auxiliary family created by nested elimination: the Theory analog
of one `aux2nested` binding.  `values` are the parametric arguments `Ds`,
open over the block parameters (innermost bvar = last parameter), in
declaration level-world. -/
structure NestedAuxSpec where
  aux : Name
  target : Name
  levels : List VLevel
  values : List VExpr
  deriving DecidableEq

/-- The nested occurrence this auxiliary family abbreviates: `I Ds`. -/
def NestedAuxSpec.value (spec : NestedAuxSpec) : VExpr :=
  (VExpr.const spec.target spec.levels).appN spec.values

/-- The flattening result: the flattened mutual block plus one auxiliary
specification per auxiliary family, in flattened family order.  When the
source contains no nested occurrence, `flat` is the source itself and
`specs` is empty. -/
structure NestedElimination (source : VInductDecl) where
  flat : VInductDecl
  specs : List NestedAuxSpec

namespace ElimNested

/-- Growing flattening state.  `types` extends the source families with the
auxiliary families; `specs` aligns with `types.drop ntypes`. -/
structure State where
  types : Array VInductiveType
  specs : Array NestedAuxSpec
  nextIdx : Nat := 1

variable (targets : List NestedTargetBlock) (uvars np : Nat)

/-- The target block owning family `c`, ignoring names that are currently
part of the flattened block itself (the kernel only recognizes previously
*declared* inductives). -/
def findTarget? (st : State) (c : Name) : Option NestedTargetBlock :=
  if st.types.any (·.name == c) then none
  else targets.find? fun t => t.families.any (·.name == c)

/-- Register the auxiliary families for one first-seen nested occurrence
`I Ds` and return the auxiliary family name standing for `I` itself.
`doms` is the discovering constructor's parameter telescope, and `values`
are the parametric arguments in parameter-world. -/
def registerAux (st : State) (block : NestedTargetBlock) (I : Name)
    (ls : List VLevel) (doms values : List VExpr) :
    Option (Name × State) := do
  let mut st := st
  let mut result := none
  for J in block.families do
    if J.uvars != ls.length then failure
    let auxName := (`_nested ++ J.name).appendIndexAfter st.nextIdx
    let auxType ← instTelescope block.nparams (J.type.instL ls) values
    let mut auxCtors : List VConstVal := []
    for c in J.ctors do
      let ctype ← instTelescope block.nparams (c.type.instL ls) values
      auxCtors := auxCtors ++
        [⟨⟨uvars, VExpr.forallN doms ctype⟩, c.name.replacePrefix J.name auxName⟩]
    let auxFamily : VInductiveType :=
      { name := auxName, uvars, type := VExpr.forallN doms auxType
        ctors := auxCtors }
    st :=
      { types := st.types.push auxFamily
        specs := st.specs.push ⟨auxName, J.name, ls, values⟩
        nextIdx := st.nextIdx + 1 }
    if J.name == I then result := some auxName
  match result with
  | some auxName => return (auxName, st)
  | none => none

/-- Rewrite one constructor-body subterm at binder depth `k`, mirroring
`replaceAllNested`: matched occurrences are replaced without descending
into the replacement; unmatched nodes recurse into their children. -/
def replace (doms : List VExpr) :
    VExpr → (k : Nat) → State → Option (VExpr × State)
  | e@(.app f a), k, st => do
      match rewrite? e k st with
      | some result => result
      | none =>
          let (f', st) ← replace doms f k st
          let (a', st) ← replace doms a k st
          return (.app f' a', st)
  | e@(.const ..), k, st => (rewrite? e k st).getD (some (e, st))
  | .lam ty body, k, st => do
      let (ty', st) ← replace doms ty k st
      let (body', st) ← replace doms body (k+1) st
      return (.lam ty' body', st)
  | .forallE ty body, k, st => do
      let (ty', st) ← replace doms ty k st
      let (body', st) ← replace doms body (k+1) st
      return (.forallE ty' body', st)
  | e, _, st => some (e, st)
  where
  /-- `some (some ..)` rewrites the node, `some none` is a hard rejection,
  `none` leaves the node to the structural recursion. -/
  rewrite? (e : VExpr) (k : Nat) (st : State) :
      Option (Option (VExpr × State)) := do
    let .const c ls := VExpr.appHead e | none
    let args := e.appArgs []
    let block ← findTarget? targets st c
    guard (block.nparams ≤ args.length)
    guard (0 < block.nparams)
    let ds := args.take block.nparams
    let names := st.types.toList.map (·.name)
    guard (ds.any (·.hasAnyConst names))
    -- the kernel's "nested inductive datatypes parameters cannot contain
    -- local variables" rejection
    if ds.any (·.hasLooseBelow k) then return none
    let values := ds.map (·.lowerN k)
    let key := (VExpr.const c ls).appN values
    let rest := args.drop block.nparams
    let recover (auxName : Name) (st : State) : VExpr × State :=
      ((VExpr.const auxName (VLevel.params uvars)).appN
        (VExpr.bvarRevRange k np ++ rest), st)
    match st.specs.find? (·.value == key) with
    | some spec => return some (recover spec.aux st)
    | none =>
        match registerAux uvars st block c ls doms values with
        | some (auxName, st) => return some (recover auxName st)
        | none => return none

/-- Flatten every constructor of every block family, including the queued
auxiliary families, until the block is stable.  `fuel` mirrors the
kernel's `inductiveFuel` bound on the same loop. -/
def run (fuel : Nat) (i : Nat) (st : State) : Option State :=
  match fuel with
  | 0 => none
  | fuel+1 =>
    if h : i < st.types.size then
      let ty := st.types[i]
      let step := ty.ctors.foldlM (init := ([], st)) fun (acc, st) c => do
        let doms := VExpr.telN np c.type
        guard (doms.length == np)
        let (body, st) ← replace targets uvars np doms (VExpr.dropN np c.type) 0 st
        return (acc ++ [{ c with type := VExpr.forallN doms body }], st)
      match step with
      | some (ctors, st) =>
          run fuel (i+1) { st with types := st.types.set! i { ty with ctors } }
      | none => none
    else some st

end ElimNested

/-- Flatten one source declaration against the supplied target blocks.
Returns the flattened block plus the auxiliary specifications; the
identity result (`flat = source`, no specs) is returned when nothing is
nested. -/
def nestedElimination? (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) :
    Option (NestedElimination source) := do
  let st ← ElimNested.run targets source.uvars source.nparams fuel 0
    { types := source.types.toArray, specs := #[] }
  return { flat := { source with types := st.types.toList }
           specs := st.specs.toList }

/-- The number of auxiliary families, matching the stored
`InductiveVal.numNested` of an accepted nested declaration. -/
def NestedElimination.numNested {source : VInductDecl}
    (elim : NestedElimination source) : Nat :=
  elim.specs.length

/-- A flattened declaration accepted by the unchanged arbitrary-block
machinery. Positivity, name, level, anatomy, and generation-shape checking
reuse the block analyzers. -/
structure NestedBlockChecked (source : VInductDecl) where
  elim : NestedElimination source
  generation : BlockGenerationChecked elim.flat

def nestedBlockChecked? (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) :
    Option (NestedBlockChecked source) := do
  let elim ← nestedElimination? targets source fuel
  let generation ← elim.flat.identityBlockGeneration?
  return ⟨elim, generation⟩

/-- Structural acceptance for a nested declaration. -/
def nestedStage3 (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) : Bool :=
  (nestedBlockChecked? targets source fuel).isSome

/-! ## Restoration

The restoration substitution σ maps the flattened block's generation
artifacts back to the stored metadata surface: auxiliary family constants
become their nested values, auxiliary constructor constants become the
target block's constructors applied to the instantiated value's own
arguments, and auxiliary recursor constants are renamed onto the main
family's `appendIndexAfter` inventory.  On an application spine headed by
an auxiliary family or constructor, the first `nparams` spine arguments
are consumed by the value instantiation, mirroring
`ElimNestedInductive.Result.restoreNested`; generated artifacts always
apply auxiliary constants to at least the block parameters (the kernel
asserts exactly this), so the identity fallback on an under-applied
auxiliary head is unreachable from real artifacts and merely keeps σ
total. -/

/-- One σ replacement entry.  `value` is already in the level world of the
artifact being restored (`instL`-spliced by the caller for recursor-world
artifacts). -/
structure RestoreEntry where
  aux : Name
  np : Nat
  value : VExpr
  deriving DecidableEq

def findRestoreCtor (entries : List RestoreEntry) (c : Name) :
    Option (RestoreEntry × Name) :=
  entries.findSome? fun entry =>
    if entry.aux.isPrefixOf c && c != entry.aux then
      some (entry, c.replacePrefix entry.aux .anonymous)
    else none

/-- σ on one expression, bottom-up: a replacement fires at the innermost
spine node where an auxiliary head has collected exactly its block-parameter
count, and enclosing applications extend the already-restored value.  On
generated artifacts — where auxiliary constants are always applied to at
least the block parameters and never occur inside another auxiliary spine's
arguments — this coincides with `restoreNested`'s top-down
replace-without-descending pass.  `recMap` renames auxiliary recursor
constants and is consulted before the constructor-prefix case, exactly like
`restoreNested`'s `auxRec` map. -/
def restoreExpr (entries : List RestoreEntry) (recMap : List (Name × Name)) :
    VExpr → VExpr
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .lam ty body => .lam (restoreExpr entries recMap ty) (restoreExpr entries recMap body)
  | .forallE ty body =>
      .forallE (restoreExpr entries recMap ty) (restoreExpr entries recMap body)
  | .app f a =>
      let e := VExpr.app (restoreExpr entries recMap f) (restoreExpr entries recMap a)
      (restoreSpine e).getD e
  | e@(.const ..) => (restoreSpine e).getD e
  where
  /-- Fire one replacement at a completed spine.  The head constant is
  still unrestored exactly when no inner node completed its parameter
  count. -/
  restoreSpine (e : VExpr) : Option VExpr :=
    match VExpr.appHead e with
    | .const c ls =>
      let args := e.appArgs []
      match recMap.find? (·.1 == c) with
      | some (_, newName) =>
          if args.isEmpty then some (VExpr.const newName ls) else none
      | none =>
      match entries.find? (·.aux == c) with
      | some entry =>
          if args.length == entry.np then
            some (instRevParams entry.value args)
          else none
      | none =>
      match findRestoreCtor entries c with
      | some (entry, suffix) =>
          if args.length == entry.np then
            let value := instRevParams entry.value args
            match VExpr.appHead value with
            | .const iname ils =>
                some ((VExpr.const (iname ++ suffix) ils).appN (value.appArgs []))
            | _ => none
          else none
      | none => none
    | _ => none

namespace NestedBlockChecked

variable {source : VInductDecl}

/-- The main family name owning the restored recursor inventory. -/
def mainName (_nested : NestedBlockChecked source) : Name :=
  match source.types with
  | ty :: _ => ty.name
  | [] => .anonymous

/-- Auxiliary recursor renaming: the `i`-th auxiliary family's recursor
becomes `mainName.rec_(i+1)`, matching `mkAuxRecNameMap`. -/
def recMap (nested : NestedBlockChecked source) : List (Name × Name) :=
  nested.elim.specs.mapIdx fun i spec =>
    (.str spec.aux "rec", ((.str nested.mainName "rec" : Name)).appendIndexAfter (i + 1))

/-- σ entries in declaration level-world (constructor-type restorations). -/
def declEntries (nested : NestedBlockChecked source) : List RestoreEntry :=
  nested.elim.specs.map fun spec =>
    ⟨spec.aux, source.nparams, spec.value⟩

/-- σ entries spliced into recursor level-world by the elimination
offset. -/
def recEntries (nested : NestedBlockChecked source) : List RestoreEntry :=
  nested.elim.specs.map fun spec =>
    ⟨spec.aux, source.nparams,
      spec.value.instL (VLevel.params' source.uvars
        (nested.generation.recUvars - source.uvars))⟩

/-- σ on a recursor-world artifact. -/
def restoreRec (nested : NestedBlockChecked source) (e : VExpr) : VExpr :=
  restoreExpr nested.recEntries nested.recMap e

/-- The restored recursor inventory: the flattened block's recursors with
auxiliary names renamed and every type restored.  Source-family recursors
keep their `.str name "rec"` names. -/
def recursors (nested : NestedBlockChecked source) : List VConstVal :=
  nested.generation.recursors.map fun r =>
    ⟨⟨r.uvars, nested.restoreRec r.type⟩,
      ((nested.recMap.find? (·.1 == r.name)).map (·.2)).getD r.name⟩

/-- The restored rule inventory, in the flattened block's globally ordered
rule order. -/
def generatedRules (nested : NestedBlockChecked source) : List VDefEq :=
  nested.generation.generatedRules.map fun df =>
    { df with
        lhs := nested.restoreRec df.lhs
        rhs := nested.restoreRec df.rhs
        type := nested.restoreRec df.type }

end NestedBlockChecked

end VInductDecl

/-- The nested transaction: the four-phase shape of
`addInductBlockGeneration` with the *source* families and constructors as
the stored payload and the *restored* recursors and rules as the generated
artifacts.  No auxiliary constant enters the environment. -/
def VEnv.addInductNested {source : VInductDecl} (env : VEnv)
    (nested : source.NestedBlockChecked) : Option VEnv := do
  let env ← source.blockTypeConstants.foldlM
    (fun env type => env.addConst type.name type.toVConstant) env
  let env ← source.blockConstructorConstants.foldlM
    (fun env constructor => env.addConst constructor.name constructor.toVConstant) env
  let env ← nested.recursors.foldlM
    (fun env recursor => env.addConst recursor.name recursor.toVConstant) env
  return nested.generatedRules.foldl VEnv.addDefEq env

namespace VInductDecl

/-- Chained constant well-formedness along an `addConst` fold: each
constant is well formed in the environment already holding every earlier
one. -/
def NestedConstsWF (env : VEnv) : List VConstVal → Prop
  | [] => True
  | c :: cs => c.toVConstant.WF env ∧
      ∀ env', env.addConst c.name c.toVConstant = some env' →
        NestedConstsWF env' cs

/-- Chained rule well-formedness along an `addDefEq` fold. -/
def NestedRulesWF (env : VEnv) : List VDefEq → Prop
  | [] => True
  | df :: dfs => df.WF env ∧ NestedRulesWF (env.addDefEq df) dfs

/-- Semantic input to nested preservation: the four transaction phases are
well formed at their exact insertion environments.  The phase environments
are determined by the deterministic constant folds, so each later field
takes the earlier folds as hypotheses; a fixture discharges them by
computation.  Inhabiting this package from the flattened block's staged
semantic certificate requires typing transport along σ; fixtures may also
inhabit it from direct checker
executions on the restored artifacts. -/
structure NestedBlockChecked.WF {source : VInductDecl}
    (nested : NestedBlockChecked source) (env : VEnv) : Prop where
  types : NestedConstsWF env source.blockTypeConstants
  ctors : ∀ {typeEnv},
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv →
    NestedConstsWF typeEnv source.blockConstructorConstants
  recs : ∀ {typeEnv ctorEnv},
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv →
    source.blockConstructorConstants.foldlM
      (fun env constructor => env.addConst constructor.name constructor.toVConstant)
      typeEnv = some ctorEnv →
    NestedConstsWF ctorEnv nested.recursors
  rules : ∀ {typeEnv ctorEnv recEnv},
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv →
    source.blockConstructorConstants.foldlM
      (fun env constructor => env.addConst constructor.name constructor.toVConstant)
      typeEnv = some ctorEnv →
    nested.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      ctorEnv = some recEnv →
    NestedRulesWF recEnv nested.generatedRules

end VInductDecl

/-- Exact phase boundaries of a successful nested transaction. -/
structure VEnv.AddInductNestedTrace {source : VInductDecl}
    (env env' : VEnv) (nested : source.NestedBlockChecked) where
  typeEnv : VEnv
  ctorEnv : VEnv
  recEnv : VEnv
  addTypes :
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv
  addCtors :
    source.blockConstructorConstants.foldlM
      (fun env constructor => env.addConst constructor.name constructor.toVConstant)
      typeEnv = some ctorEnv
  addRecs :
    nested.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      ctorEnv = some recEnv
  addRules :
    nested.generatedRules.foldl VEnv.addDefEq recEnv = env'

end Ix.Theory.Named
