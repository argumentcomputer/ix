/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Reference.Environment
import Ix.Theory.Named.Inductive
import Ix.Theory.Named.Meta

open Ix.Theory (VLevel)

/-!
# Spec-09A: nested-inductive representation audit and decision

This file is the committed design note and the executable metadata probes
for the nested-inductive representation decision.  Every claim below is
pinned by a build-failing probe in this file unless it is explicitly marked
as a forward-looking obligation.  This checkpoint changes no acceptance
behavior: the probes only observe the implementation and the existing
Theory analyzers.

## Audit: how the implementation represents nested inductives

`Environment.addInductive` (Inductive/Add.lean) runs three phases:

1. `ElimNestedInductive.run` rewrites the source declaration into a
   flattened mutual block: every nested occurrence `I Ds is` whose
   parametric arguments `Ds` mention a block family is replaced by
   `auxI As is`, where `auxI` is a fresh auxiliary family abstracted over
   the block parameters `As`, and one auxiliary family is created for each
   family of `I`'s mutual block, with constructor types instantiated at
   `Ds` (recursively rewritten).  `aux2nested` records `auxI ↦ I Ds`, open
   over the block parameters.  Auxiliary names are uniquified against the
   ambient environment (`mkUniqueName`).
2. `AddInductive.run` checks and generates the flattened block as an
   ordinary mutual block, receiving `numNested` (the number of auxiliary
   families) as opaque metadata.
3. When `numNested ≠ 0`, a restoration pass rebuilds the final environment
   from the *pre-block* environment: source families and constructors are
   re-added with every auxiliary constant replaced by its nested
   restoration (`Result.restoreNested`), each auxiliary family's recursor
   is re-added under the name `(mkRecName mainName).appendIndexAfter i`
   with restored type and rules, and finally every `aux2nested` value
   `I Ds` is type-checked (the lean4#14577 escape-hatch check, regression
   tested in `Tests/NestedInductive.lean`).  The auxiliary families,
   constructors, and recursor names never enter the final environment.

The stored metadata therefore has this shape (probes P1, P2):

- The source `inductInfo` keeps `all` = the source family names only and
  carries `numNested` = the number of auxiliary families; stored
  constructor types are in restored form (they mention `I Ds`, e.g.
  `List (RoseTree α)`).
- The recursor inventory is one recursor per source family plus one per
  auxiliary family, all with `all` = source names, and with
  `numMotives`/`numMinors` counting the *flattened* block's families and
  minors.  Auxiliary recursors have rules keyed by constructors of the
  previously declared nested inductive (`List.nil`, `List.cons`, ...) with
  `nfields` counting the instantiated auxiliary constructor's fields, and
  every rule RHS references the restored recursor constants mutually.
- No `_nested.*` constant, and no auxiliary recursor under its original
  name, survives into the final environment.

## Decision: additive artifact type; `VInductDecl` unchanged

The stored Theory payload for a nested declaration must be the *source*
`VInductDecl` (restored form), because that is what the implementation
stores and what Verify alignment must replay.  Storing the flattened block
is unrepresentable: the final `ConstMap` contains neither the auxiliary
families nor their constructors (probe P2), and the stored constructor
types differ from the flattened ones (probe P1).  `VInductDecl` needs no
new field: `numNested` is implementation metadata recoverable as the
number of auxiliary specifications, and parity fixtures pin it per row
exactly as they already pin `numNested == 0` for non-nested rows.

Nested support is an additive checked-block artifact (built in Spec-09B/C),
coupling:

1. the flattened block as an ordinary `VInductDecl` — probe P4 shows both
   target fixtures' flattened blocks are already accepted by the existing
   `identityBlockGeneration?` machinery, so flattening reuses the complete
   Spec-08 block analyzer and generator unchanged;
2. one auxiliary specification per auxiliary family, in flattened family
   order: the auxiliary name, the nested value `I Ds` open over the block
   parameters (the Theory analog of `aux2nested`), and the restored
   recursor name — plus executable coherence checks tying the flattened
   block to the source declaration and to the environment's metadata for
   `I` at `Ds`;
3. the restoration substitution σ, a structural constant substitution on
   `VExpr` (probe P5, `restoreV09A`): on an application spine headed by an
   auxiliary constant, the first `nparams` spine arguments are consumed
   and replaced by the instantiated value `I Ds`; auxiliary constructor
   constants are renamed by prefix into `I`'s constructors, applied to the
   instantiated value's own arguments; auxiliary recursor constants are
   renamed (checked *before* the constructor-prefix case, exactly like
   `restoreNested`'s `auxRec` map); levels come from the recorded value,
   not the auxiliary constant.

σ has one level-world subtlety (probe P5): specification values live in
declaration level-world, while recursor types and rules live in recursor
level-world, so σ over generation artifacts splices
`value.instL (VLevel.params' uvars elimOffset)`.  Constructor types are
restored with the unshifted value.  With that splice, σ over the flattened
block's existing `BlockGenerationChecked` artifacts reproduces the stored
kernel metadata *exactly* — every recursor type and every rule RHS of all
three probe fixtures — and no auxiliary constant survives the image.
Probe P2 additionally shows the port's full nested path reproduces Lean's
stored metadata field-for-field, and that the final metadata is
independent of auxiliary-name collisions (the uniquified names are erased
by σ), so Theory may choose canonical auxiliary names as artifact data.

Rejected alternatives:

- *Flattened block as stored payload*: contradicts the stored metadata
  (P1/P2); Verify alignment would have to invent constants the
  implementation never stores.
- *Changing `VInductDecl` fields*: unnecessary — the probes demonstrate
  the additive artifact expresses real rose-tree, nested-indexed, and
  constant-universe metadata; a payload change would ripple through every
  exported Theory API without demonstrated need.
- *A Prop-only pre-flattening relation without an artifact*: the
  specifications and σ are data consumed by generation and replay; a
  relation alone would force Verify to re-synthesize them.  The artifact's
  executable coherence checks subsume the relation.

## Obligations recorded for Spec-09B/09C (not claimed here)

- 09B: Theory-side flattening and auxiliary-specification validation —
  positivity through the existing block analyzer on the flattened block;
  executable instantiation checks of auxiliary family/constructor types
  against `I`'s metadata at `Ds`; nearest rejection differentials
  (ill-typed `Ds` — the lean4#14577 class — wrong specification order,
  non-matching instantiation).
- 09C: σ as a total Theory function.  The spine rule needs a simultaneous
  `instantiateRev`-style multi-substitution for `nparams > 1`: iterating
  single `VExpr.inst` is wrong once parameter arguments mention bvars.
  Generation, preservation (typing transport along σ: auxiliary constants
  behave as definitions `auxI := λ As, I Ds`, so staged flattened-block WF
  transports to restored WF given environment lookup facts for `I`'s
  families and constructors), insertion order, and replay of real
  `Inductive.Add.run` output.
- The kernel's trailing `checkType (I Ds)` becomes a WF premise of the
  auxiliary specification, never a trusted escape hatch.
-/

namespace Ix.Theory.Named.NestedRepresentation

open Lean

/-! ## Probe fixtures

`RoseTree` is the universe-polymorphic rose tree through `List`; `NVTree`
nests through the locally declared indexed family `PVec` (indices spelled
with `Nat.zero`/`Nat.succ` to keep the probe dependency maps free of
notation instances); `CURose` nests `List` at a constant universe, so its
auxiliary constant carries no block level while the restored `List`
carries level `1` — the level-instantiation case σ must represent. -/

inductive RoseTree (α : Type u) : Type u where
  | node : α → List (RoseTree α) → RoseTree α

inductive PVec (α : Type) : Nat → Type where
  | nil : PVec α Nat.zero
  | cons : α → {n : Nat} → PVec α n → PVec α (Nat.succ n)

inductive NVTree : Type where
  | node : (n : Nat) → PVec NVTree n → NVTree

inductive CURose : Type 1 where
  | node : List CURose → CURose

/-! ## Quoted stored metadata

Local pin records keep this file independent of the replay fixture
inventory; a change in Lean's emitted metadata is a compile failure. -/

structure InductPins where
  name : Name
  lparams : List Name
  numParams : Nat
  numIndices : Nat
  all : List Name
  ctors : List Name
  numNested : Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool
  deriving ToExpr, BEq

structure CtorPins where
  name : Name
  lparams : List Name
  induct : Name
  cidx : Nat
  numParams : Nat
  numFields : Nat
  deriving ToExpr, BEq

structure RecPins where
  name : Name
  lparams : List Name
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  k : Bool
  rules : List (Name × Nat)
  deriving ToExpr, BEq

open Elab Term in
elab "nestedInductPins09A%" n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let .inductInfo i ← getConstInfo name | throwError "expected inductive {name}"
  return toExpr (InductPins.mk i.name i.levelParams i.numParams i.numIndices
    i.all i.ctors i.numNested i.isRec i.isReflexive i.isUnsafe)

open Elab Term in
elab "nestedCtorPins09A%" n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let .ctorInfo i ← getConstInfo name | throwError "expected constructor {name}"
  return toExpr (CtorPins.mk i.name i.levelParams i.induct i.cidx
    i.numParams i.numFields)

open Elab Term in
elab "nestedRecPins09A%" n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let .recInfo i ← getConstInfo name | throwError "expected recursor {name}"
  return toExpr (RecPins.mk i.name i.levelParams i.all i.numParams i.numIndices
    i.numMotives i.numMinors i.k (i.rules.map fun r => (r.ctor, r.nfields)))

-- Quote a stored `ConstantInfo.type` in that record's own universe order.
open Elab Term in
elab "nestedConstVType09A%" n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let info ← getConstInfo name
  let type ← Ix.Theory.Named.Meta.expandExpr info.type
  return toExpr (← Ix.Theory.Named.Meta.ofExpr info.levelParams {} type)

/-! ## P1: stored-metadata pins

The source family keeps `all` = source names and counts its auxiliary
families in `numNested`; constructor types are restored; the recursor
inventory reveals the flattened block through `numMotives`/`numMinors` and
through auxiliary recursors whose rules are keyed by the constructors of a
previously declared inductive. -/

def roseAux : Name := (`_nested ++ ``List).appendIndexAfter 1
def nvAux : Name := (`_nested ++ ``PVec).appendIndexAfter 1

def roseInductPins : InductPins := nestedInductPins09A% RoseTree
def roseNodePins : CtorPins := nestedCtorPins09A% RoseTree.node
def roseRecPins : RecPins := nestedRecPins09A% RoseTree.rec
def roseRec1Pins : RecPins := nestedRecPins09A% RoseTree.rec_1

#guard roseInductPins.numNested == 1
#guard roseInductPins.all == [``RoseTree]
#guard roseInductPins.ctors == [``RoseTree.node]
#guard roseInductPins.lparams == [`u] && roseInductPins.numParams == 1
#guard roseInductPins.isRec && !roseInductPins.isReflexive && !roseInductPins.isUnsafe
#guard roseNodePins ==
  { name := ``RoseTree.node, lparams := [`u], induct := ``RoseTree, cidx := 0,
    numParams := 1, numFields := 2 }
#guard roseRecPins ==
  { name := ``RoseTree.rec, lparams := [`u_1, `u], all := [``RoseTree], numParams := 1,
    numIndices := 0, numMotives := 2, numMinors := 3, k := false,
    rules := [(``RoseTree.node, 2)] }
#guard roseRec1Pins ==
  { name := (mkRecName ``RoseTree).appendIndexAfter 1, lparams := [`u_1, `u],
    all := [``RoseTree], numParams := 1, numIndices := 0, numMotives := 2, numMinors := 3,
    k := false, rules := [(``List.nil, 0), (``List.cons, 2)] }

/-- The stored constructor type is the restored form: it mentions
`List (RoseTree α)`, not an auxiliary constant. -/
def roseNodeStoredType : VExpr := nestedConstVType09A% RoseTree.node

#guard roseNodeStoredType ==
  .forallE (.sort (.succ (.param 0)))
    (.forallE (.bvar 0)
      (.forallE (.app (.const ``List [.param 0]) (.app (.const ``RoseTree [.param 0]) (.bvar 1)))
        (.app (.const ``RoseTree [.param 0]) (.bvar 2))))

def nvInductPins : InductPins := nestedInductPins09A% NVTree
def nvNodePins : CtorPins := nestedCtorPins09A% NVTree.node
def nvRecPins : RecPins := nestedRecPins09A% NVTree.rec
def nvRec1Pins : RecPins := nestedRecPins09A% NVTree.rec_1

#guard nvInductPins.numNested == 1
#guard nvInductPins.all == [``NVTree] && nvInductPins.ctors == [``NVTree.node]
#guard nvNodePins ==
  { name := ``NVTree.node, lparams := [], induct := ``NVTree, cidx := 0,
    numParams := 0, numFields := 2 }
#guard nvRecPins ==
  { name := ``NVTree.rec, lparams := [`u], all := [``NVTree], numParams := 0,
    numIndices := 0, numMotives := 2, numMinors := 3, k := false,
    rules := [(``NVTree.node, 2)] }
-- The auxiliary recursor keeps the auxiliary family's index and its rules
-- count the instantiated constructor's fields (`PVec.cons` retains its
-- implicit index field: 3 fields, not 2).
#guard nvRec1Pins ==
  { name := (mkRecName ``NVTree).appendIndexAfter 1, lparams := [`u], all := [``NVTree],
    numParams := 0, numIndices := 1, numMotives := 2, numMinors := 3, k := false,
    rules := [(``PVec.nil, 0), (``PVec.cons, 3)] }

def nvNodeStoredType : VExpr := nestedConstVType09A% NVTree.node

#guard nvNodeStoredType ==
  .forallE (.const ``Nat [])
    (.forallE (.app (.app (.const ``PVec []) (.const ``NVTree [])) (.bvar 0))
      (.const ``NVTree []))

def cuInductPins : InductPins := nestedInductPins09A% CURose
def cuRecPins : RecPins := nestedRecPins09A% CURose.rec
def cuRec1Pins : RecPins := nestedRecPins09A% CURose.rec_1

#guard cuInductPins.numNested == 1 && cuInductPins.all == [``CURose]
#guard cuRecPins.rules == [(``CURose.node, 1)] && cuRecPins.numMotives == 2
#guard cuRec1Pins.rules == [(``List.nil, 0), (``List.cons, 2)]

/-- The restored constructor type instantiates `List` at the constant level
`1` even though the declaration has no level parameters. -/
def cuNodeStoredType : VExpr := nestedConstVType09A% CURose.node

#guard cuNodeStoredType ==
  .forallE (.app (.const ``List [.succ .zero]) (.const ``CURose []))
    (.const ``CURose [])

/-! ## Shared probe plumbing -/

def sourceType09A (env : Environment) (n : Name) : InductiveType := Id.run do
  let some (.inductInfo info) := env.find? n | panic! "expected inductive"
  let ctors := info.ctors.map fun c => Id.run do
    let some (.ctorInfo ci) := env.find? c | panic! "expected constructor"
    return { name := c, type := ci.type : Constructor }
  return { name := n, type := info.type, ctors }

def depMap09A (env : Environment) (ns : List Name) : ConstMap :=
  ns.foldl (fun m n => m.insert n (env.find? n).get!) {}

open ElimNestedInductive in
/-- Run the port's flattening phase, returning the flattened block and the
`aux2nested` values abstracted over the block parameters. -/
def runElim09A (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) :
    Except Kernel.Exception (List InductiveType × List (Name × Expr)) := do
  let res : ElimNestedInductive.Result ← ElimNestedInductive.run 1000 nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  return (res.types, res.aux2nested.toList.map fun (n, e) => (n, e.abstract res.params))

/-- Field-for-field stored/ported agreement for the constant kinds a nested
declaration emits. -/
def sameConst09A (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
    match a, b with
    | .recInfo ra, .recInfo rb =>
        ra.all == rb.all && ra.numParams == rb.numParams &&
          ra.numIndices == rb.numIndices && ra.numMotives == rb.numMotives &&
          ra.numMinors == rb.numMinors && ra.k == rb.k &&
          ra.isUnsafe == rb.isUnsafe &&
          ra.rules.map (fun r => (r.ctor, r.nfields, r.rhs)) ==
            rb.rules.map (fun r => (r.ctor, r.nfields, r.rhs))
    | .inductInfo ia, .inductInfo ib =>
        ia.all == ib.all && ia.numParams == ib.numParams &&
          ia.numIndices == ib.numIndices && ia.ctors == ib.ctors &&
          ia.numNested == ib.numNested && ia.isRec == ib.isRec &&
          ia.isReflexive == ib.isReflexive && ia.isUnsafe == ib.isUnsafe
    | .ctorInfo ca, .ctorInfo cb =>
        ca.induct == cb.induct && ca.cidx == cb.cidx &&
          ca.numParams == cb.numParams && ca.numFields == cb.numFields &&
          ca.isUnsafe == cb.isUnsafe
    | _, _ => false

def roseDeps : List Name := [``List, ``List.nil, ``List.cons]
def nvDeps : List Name :=
  [``Nat, ``Nat.zero, ``Nat.succ, ``PVec, ``PVec.nil, ``PVec.cons]

def roseRestored : List Name :=
  [``RoseTree, ``RoseTree.node, mkRecName ``RoseTree,
    (mkRecName ``RoseTree).appendIndexAfter 1]
def nvRestored : List Name :=
  [``NVTree, ``NVTree.node, mkRecName ``NVTree,
    (mkRecName ``NVTree).appendIndexAfter 1]
def cuRestored : List Name :=
  [``CURose, ``CURose.node, mkRecName ``CURose,
    (mkRecName ``CURose).appendIndexAfter 1]

/-! ## P2: the port's nested path reproduces the stored metadata

`Environment.addInductive`, run on a dependency-only kernel environment,
re-creates exactly the constants Lean stores — including every restored
type and rule RHS — and no auxiliary constant.  The final output is
independent of auxiliary-name collisions: pre-seeding `_nested.List_1`
only shifts the uniquified internal names, which restoration erases. -/

open Elab in
run_meta do
  let env ← getEnv
  let checkPort (label : String) (main : Name) (lparams : List Name) (nparams : Nat)
      (deps auxNames restored : List Name) (extra : ConstMap → ConstMap) :
      MetaM Unit := do
    let src := sourceType09A env main
    let kenv := Kernel.Environment.ofConstants (`_spec09A ++ main) (extra (depMap09A env deps))
    match Ix.Theory.Named.Environment.addInductive kenv lparams nparams [src] false false with
    | .error _ => throwError "{label}: port addInductive failed"
    | .ok env' =>
      for n in restored do
        let some stored := env.find? n | throwError "{label}: {n} not stored"
        let some ported := env'.find? n | throwError "{label}: {n} missing from port output"
        unless sameConst09A stored ported do
          throwError "{label}: stored/ported metadata differ at {n}"
      for n in auxNames do
        unless (env'.find? n).isNone do
          throwError "{label}: auxiliary constant {n} leaked into the final environment"
        unless (env.find? n).isNone do
          throwError "{label}: auxiliary constant {n} present in the ambient environment"
  checkPort "rose" ``RoseTree [`u] 1 roseDeps
    [roseAux, roseAux ++ `nil, roseAux ++ `cons, mkRecName roseAux,
      (mkRecName ``RoseTree).appendIndexAfter 2] roseRestored id
  checkPort "nv" ``NVTree [] 0 nvDeps
    [nvAux, nvAux ++ `nil, nvAux ++ `cons, mkRecName nvAux,
      (mkRecName ``NVTree).appendIndexAfter 2] nvRestored id
  checkPort "cu" ``CURose [] 0 roseDeps
    [roseAux, mkRecName roseAux] cuRestored id
  -- auxiliary-name-collision independence
  checkPort "rose-collision" ``RoseTree [`u] 1 roseDeps
    [(`_nested ++ ``List).appendIndexAfter 2] roseRestored
    (fun m => m.insert roseAux (env.find? ``Nat).get!)

/-! ## P3: exact flattening pins

The flattened blocks, translated to binder-erased `VExpr` form.  These are
the descriptors the Spec-09B transformation must produce. -/

def roseFlatFamilies : List (Name × VExpr) :=
  [(``RoseTree, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))),
    (roseAux, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))))]

def roseFlatCtors : List (Name × VExpr) :=
  [(``RoseTree.node,
    .forallE (.sort (.succ (.param 0)))
      (.forallE (.bvar 0)
        (.forallE (.app (.const roseAux [.param 0]) (.bvar 1))
          (.app (.const ``RoseTree [.param 0]) (.bvar 2))))),
   (roseAux ++ `nil,
    .forallE (.sort (.succ (.param 0))) (.app (.const roseAux [.param 0]) (.bvar 0))),
   (roseAux ++ `cons,
    .forallE (.sort (.succ (.param 0)))
      (.forallE (.app (.const ``RoseTree [.param 0]) (.bvar 0))
        (.forallE (.app (.const roseAux [.param 0]) (.bvar 1))
          (.app (.const roseAux [.param 0]) (.bvar 2)))))]

/-- `aux2nested` for the rose tree: `List (RoseTree α)`, open over `α`. -/
def roseAuxValue : VExpr :=
  .app (.const ``List [.param 0]) (.app (.const ``RoseTree [.param 0]) (.bvar 0))

def nvFlatFamilies : List (Name × VExpr) :=
  [(``NVTree, .sort (.succ .zero)),
    (nvAux, .forallE (.const ``Nat []) (.sort (.succ .zero)))]

def nvFlatCtors : List (Name × VExpr) :=
  [(``NVTree.node,
    .forallE (.const ``Nat [])
      (.forallE (.app (.const nvAux []) (.bvar 0)) (.const ``NVTree []))),
   (nvAux ++ `nil, .app (.const nvAux []) (.const ``Nat.zero [])),
   (nvAux ++ `cons,
    .forallE (.const ``NVTree [])
      (.forallE (.const ``Nat [])
        (.forallE (.app (.const nvAux []) (.bvar 0))
          (.app (.const nvAux []) (.app (.const ``Nat.succ []) (.bvar 1))))))]

/-- `aux2nested` for `NVTree`: the closed partial application `PVec NVTree`
(the index argument stays behind on each occurrence). -/
def nvAuxValue : VExpr := .app (.const ``PVec []) (.const ``NVTree [])

def cuFlatFamilies : List (Name × VExpr) :=
  [(``CURose, .sort (.succ (.succ .zero))),
    (roseAux, .sort (.succ (.succ .zero)))]

def cuFlatCtors : List (Name × VExpr) :=
  [(``CURose.node, .forallE (.const roseAux []) (.const ``CURose [])),
   (roseAux ++ `nil, .const roseAux []),
   (roseAux ++ `cons,
    .forallE (.const ``CURose []) (.forallE (.const roseAux []) (.const roseAux [])))]

/-- `aux2nested` for `CURose`: the block-level-free auxiliary constant
restores to `List` at the constant level `1`. -/
def cuAuxValue : VExpr := .app (.const ``List [.succ .zero]) (.const ``CURose [])

open Elab in
/-- Translate one flattened block and compare it with its pinned shape. -/
def checkFlat09A (label : String) (main : Name) (lparams : List Name) (nparams : Nat)
    (deps : List Name) (families ctors : List (Name × VExpr))
    (auxValues : List (Name × VExpr)) : MetaM (List VInductiveType) := do
  let env ← getEnv
  let src := sourceType09A env main
  let kenv := Kernel.Environment.ofConstants (`_spec09AFlat ++ main) (depMap09A env deps)
  let .ok (flatTypes, aux) := runElim09A kenv lparams nparams [src]
    | throwError "{label}: flattening failed"
  let uvars := lparams.length
  let mut vtypes : List VInductiveType := []
  let mut actualFamilies : List (Name × VExpr) := []
  let mut actualCtors : List (Name × VExpr) := []
  for t in flatTypes do
    let vty ← Ix.Theory.Named.Meta.ofExpr lparams {} t.type
    actualFamilies := actualFamilies ++ [(t.name, vty)]
    let mut vctors : List VConstVal := []
    for c in t.ctors do
      let vc ← Ix.Theory.Named.Meta.ofExpr lparams {} c.type
      actualCtors := actualCtors ++ [(c.name, vc)]
      vctors := vctors ++ [{ name := c.name, uvars, type := vc }]
    vtypes := vtypes ++ [{ name := t.name, uvars, type := vty, ctors := vctors }]
  unless actualFamilies == families do
    throwError "{label}: flattened families differ from the pinned shape"
  unless actualCtors == ctors do
    throwError "{label}: flattened constructors differ from the pinned shape"
  let mut actualValues : List (Name × VExpr) := []
  for (n, e) in aux do
    actualValues := actualValues ++ [(n, ← Ix.Theory.Named.Meta.ofExpr lparams {} e)]
  unless actualValues == auxValues do
    throwError "{label}: aux2nested values differ from the pinned shape"
  return vtypes

/-! ## P4: Theory viability, with acceptance behavior unchanged

The flattened blocks are already inside the supported arbitrary-block
class, while the source declarations remain rejected by every current
analyzer and by the public transaction. -/

open Elab in
run_meta do
  let checkViability (label : String) (main : Name) (lparams : List Name)
      (nparams : Nat) (deps : List Name) (families ctors : List (Name × VExpr))
      (auxValues : List (Name × VExpr)) : MetaM Unit := do
    let vtypes ← checkFlat09A label main lparams nparams deps families ctors auxValues
    let uvars := lparams.length
    let flatDecl : VInductDecl := { uvars, nparams, types := vtypes }
    unless flatDecl.stage3 do
      throwError "{label}: flattened block rejected by the block analyzer"
    unless flatDecl.identityBlockGeneration?.isSome do
      throwError "{label}: flattened block is not generation-ready"
    let env ← getEnv
    let src := sourceType09A env main
    let vsrcTy ← Ix.Theory.Named.Meta.ofExpr lparams {} src.type
    let mut vctors : List VConstVal := []
    for c in src.ctors do
      vctors := vctors ++ [{ name := c.name, uvars, type := ← Ix.Theory.Named.Meta.ofExpr lparams {} c.type }]
    let srcTy : VInductiveType := { name := main, uvars, type := vsrcTy, ctors := vctors }
    let srcDecl : VInductDecl := { uvars, nparams, types := [srcTy] }
    if srcDecl.stage3 then
      throwError "{label}: source declaration unexpectedly accepted by stage3"
    if srcDecl.checked?.isSome then
      throwError "{label}: source declaration unexpectedly accepted by checked?"
    if (VEnv.empty.addInduct srcDecl).isSome then
      throwError "{label}: source declaration unexpectedly accepted by addInduct"
  checkViability "rose" ``RoseTree [`u] 1 roseDeps
    roseFlatFamilies roseFlatCtors [(roseAux, roseAuxValue)]
  checkViability "nv" ``NVTree [] 0 nvDeps
    nvFlatFamilies nvFlatCtors [(nvAux, nvAuxValue)]
  checkViability "cu" ``CURose [] 0 roseDeps
    cuFlatFamilies cuFlatCtors [(roseAux, cuAuxValue)]

/-! ## P5: the restoration substitution σ

`restoreV09A` mirrors `ElimNestedInductive.Result.restoreNested` on
`VExpr`.  It is probe-local: the Spec-09C artifact path must define the
total Theory version (with a simultaneous parameter substitution once
`nparams > 1` is in scope; the probe fixtures have `nparams ≤ 1`, where
iterated `VExpr.inst` coincides with it). -/

structure AuxSpec09A where
  aux : Name
  np : Nat
  value : VExpr
  recName : Name

def instParams09A (value : VExpr) : List VExpr → VExpr
  | [] => value
  | [a] => value.inst a
  | _ => panic! "the probe fixtures have nparams ≤ 1"

def findCtorSpec09A (specs : List AuxSpec09A) (c : Name) : Option (AuxSpec09A × Name) :=
  specs.findSome? fun spec =>
    if spec.aux.isPrefixOf c && c != spec.aux then
      some (spec, c.replacePrefix spec.aux .anonymous)
    else none

/-- σ.  The recursor-rename case is checked before the constructor-prefix
case, exactly like `restoreNested`'s `auxRec` map: an auxiliary recursor
name is prefixed by its auxiliary family name and would otherwise be
mangled by the constructor branch. -/
partial def restoreV09A (specs : List AuxSpec09A) (recMap : List (Name × Name)) :
    VExpr → VExpr
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .lam ty body => .lam (restoreV09A specs recMap ty) (restoreV09A specs recMap body)
  | .forallE ty body =>
      .forallE (restoreV09A specs recMap ty) (restoreV09A specs recMap body)
  | e@(.app ..) => restoreSpine (VExpr.appHead e) (e.appArgs [])
  | e@(.const ..) => restoreSpine e []
  where
  restoreSpine (head : VExpr) (args : List VExpr) : VExpr :=
    let args' := args.map (restoreV09A specs recMap)
    match head with
    | .const c ls =>
      match recMap.find? (·.1 == c) with
      | some (_, newName) => (VExpr.const newName ls).appN args'
      | none =>
      match specs.find? (·.aux == c) with
      | some spec =>
          (instParams09A spec.value (args'.take spec.np)).appN (args'.drop spec.np)
      | none =>
      match findCtorSpec09A specs c with
      | some (spec, suffix) =>
          let value := instParams09A spec.value (args'.take spec.np)
          match VExpr.appHead value with
          | .const iname ils =>
              (VExpr.const (iname ++ suffix) ils).appN
                (value.appArgs [] ++ args'.drop spec.np)
          | _ => panic! "auxiliary value head is not a constant"
      | none => (VExpr.const c ls).appN args'
    | h => (restoreV09A specs recMap h).appN args'

open Elab in
/-- σ over the flattened block's existing generation artifacts reproduces
the stored kernel metadata exactly: recursor names and types, and every
rule RHS in the globally flattened order, with no auxiliary constant in
the image.  Constructor types are restored with the declaration-world
value; recursor artifacts use the value spliced by the elimination
offset. -/
def checkRestore09A (label : String) (main : Name) (lparams : List Name)
    (nparams : Nat) (deps : List Name) : MetaM Unit := do
  let env ← getEnv
  let src := sourceType09A env main
  let kenv := Kernel.Environment.ofConstants (`_spec09ARestore ++ main) (depMap09A env deps)
  let .ok (flatTypes, aux) := runElim09A kenv lparams nparams [src]
    | throwError "{label}: flattening failed"
  let uvars := lparams.length
  let mut vtypes : List VInductiveType := []
  for t in flatTypes do
    let vty ← Ix.Theory.Named.Meta.ofExpr lparams {} t.type
    let mut vctors : List VConstVal := []
    for c in t.ctors do
      vctors := vctors ++ [{ name := c.name, uvars, type := ← Ix.Theory.Named.Meta.ofExpr lparams {} c.type }]
    vtypes := vtypes ++ [{ name := t.name, uvars, type := vty, ctors := vctors }]
  let flatDecl : VInductDecl := { uvars, nparams, types := vtypes }
  let some gen := flatDecl.identityBlockGeneration?
    | throwError "{label}: flattened block is not generation-ready"
  let elimOffset := gen.recUvars - uvars
  let mut declSpecs : List AuxSpec09A := []
  let mut recSpecs : List AuxSpec09A := []
  let mut recMap : List (Name × Name) := []
  let mut i := 1
  for t in flatTypes.drop 1 do
    let some (_, value) := aux.find? (·.1 == t.name)
      | throwError "{label}: no aux2nested value for {t.name}"
    let v ← Ix.Theory.Named.Meta.ofExpr lparams {} value
    let recName := (mkRecName main).appendIndexAfter i
    let recValue := v.instL (VLevel.params' uvars elimOffset)
    declSpecs := declSpecs ++ [{ aux := t.name, np := nparams, value := v, recName }]
    recSpecs := recSpecs ++ [{ aux := t.name, np := nparams, value := recValue, recName }]
    recMap := recMap ++ [(mkRecName t.name, recName)]
    i := i + 1
  let auxConsts := declSpecs.map (·.aux) ++ recMap.map (·.1) ++
    (flatTypes.drop 1).flatMap (fun t => t.ctors.map (·.name))
  -- declaration-world σ: restored source constructors
  for (t, vt) in flatTypes.zip vtypes do
    if t.name == main then
      for c in vt.ctors do
        let some stored := env.find? c.name | throwError "{label}: {c.name} not stored"
        let storedType ← Ix.Theory.Named.Meta.ofExpr stored.levelParams {}
          (← Ix.Theory.Named.Meta.expandExpr stored.type)
        unless restoreV09A declSpecs recMap c.type == storedType do
          throwError "{label}: σ(flattened {c.name}) differs from the stored type"
  -- recursor-world σ: recursor types, names, and every rule RHS
  let expectedNames := [mkRecName main] ++ recSpecs.map (·.recName)
  for (r, expected) in gen.recursors.zip expectedNames do
    let restoredName := match recMap.find? (·.1 == r.name) with
      | some (_, n) => n
      | none => r.name
    unless restoredName == expected do
      throwError "{label}: restored recursor name {restoredName}, expected {expected}"
    let some (.recInfo stored) := env.find? expected
      | throwError "{label}: stored recursor {expected} missing"
    let storedType ← Ix.Theory.Named.Meta.ofExpr stored.levelParams {}
      (← Ix.Theory.Named.Meta.expandExpr stored.type)
    let restored := restoreV09A recSpecs recMap r.type
    unless restored == storedType do
      throwError "{label}: σ(recursor type) differs from stored for {expected}"
    unless !VExpr.hasAnyConst auxConsts restored do
      throwError "{label}: auxiliary constant survives σ in the type of {expected}"
  let mut storedRules : List (Name × Expr) := []
  for n in expectedNames do
    let some (.recInfo stored) := env.find? n
      | throwError "{label}: stored recursor {n} missing"
    for rule in stored.rules do
      storedRules := storedRules ++ [(rule.ctor, rule.rhs)]
  let genRules := gen.generatedRules
  unless storedRules.length == genRules.length do
    throwError "{label}: {genRules.length} generated rules, {storedRules.length} stored"
  let some (.recInfo mainRec) := env.find? (mkRecName main)
    | throwError "{label}: stored main recursor missing"
  for (df, (ctor, storedRhs)) in genRules.zip storedRules do
    let storedRhs ← Ix.Theory.Named.Meta.ofExpr mainRec.levelParams {}
      (← Ix.Theory.Named.Meta.expandExpr storedRhs)
    let restoredRhs := restoreV09A recSpecs recMap df.rhs
    unless restoredRhs == storedRhs do
      throwError "{label}: σ(rule rhs) differs from stored for {ctor}"
    unless !VExpr.hasAnyConst auxConsts restoredRhs &&
        !VExpr.hasAnyConst auxConsts (restoreV09A recSpecs recMap df.lhs) do
      throwError "{label}: auxiliary constant survives σ in the rule for {ctor}"

run_meta do
  checkRestore09A "rose" ``RoseTree [`u] 1 roseDeps
  checkRestore09A "nv" ``NVTree [] 0 nvDeps
  checkRestore09A "cu" ``CURose [] 0 roseDeps

end Ix.Theory.Named.NestedRepresentation
