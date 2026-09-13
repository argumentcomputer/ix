/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.NestedRepresentation
import Ix.Theory.Named.NestedInductiveFixtures

/-!
# Nested flattening differential (Spec-09B)

Ties the Theory transformation `nestedElimination?` to the implementation:

- the hand-written `List` target block in the Theory fixtures is exactly
  Lean's stored metadata;
- on the real rose-tree, nested-indexed, and constant-universe fixtures,
  the Theory flattening reproduces the port's `ElimNestedInductive` output
  family for family, constructor for constructor, and specification for
  `aux2nested` binding — including the canonical auxiliary names — and its
  auxiliary count equals the stored `numNested`;
- Theory acceptance (`nestedStage3`) agrees with kernel acceptance on the
  positives and on the nearest rejections: a parametric argument touching
  a constructor-local binder (rejected by flattening itself, with the
  kernel's exact error), an off-spine parametric application (rejected by
  the unchanged block analyzer where the kernel fails constructor
  checking), an in-block collision with the canonical auxiliary name
  (rejected by `blockNamesOK` where the kernel's `checkName` rejects the
  duplicate insertion), and a missing target declaration.
-/

namespace Ix.Theory.Named.NestedTransformation

open Lean
open Ix.Theory.Named.NestedRepresentation
open Ix.Theory.Named.NestedInductiveFixtures
open VInductDecl

/-! ## The hand-written `List` target is the stored metadata -/

def listNilStoredType : VExpr := nestedConstVType09A% List.nil
def listConsStoredType : VExpr := nestedConstVType09A% List.cons
def listStoredType : VExpr := nestedConstVType09A% List

#guard listTarget.families.map (·.name) == [``List]
#guard listTarget.nparams == 1
#guard listTarget.families.map (·.type) == [listStoredType]
#guard listTarget.families.map (·.ctors.map fun c => (c.name, c.uvars, c.type)) ==
  [[(``List.nil, 1, listNilStoredType), (``List.cons, 1, listConsStoredType)]]

/-! ## Real-metadata target blocks -/

def pvecStoredTarget : NestedTargetBlock where
  nparams := 1
  families :=
    [{ name := ``PVec
       uvars := 0
       type := nestedConstVType09A% PVec
       ctors :=
         [⟨⟨0, nestedConstVType09A% PVec.nil⟩, ``PVec.nil⟩,
          ⟨⟨0, nestedConstVType09A% PVec.cons⟩, ``PVec.cons⟩] }]

/-! ## Shared translation plumbing -/

open Elab in
/-- Translate a list of kernel `InductiveType`s into a `VInductDecl`. -/
def toVInductDecl09B (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) : MetaM VInductDecl := do
  let uvars := lparams.length
  let mut vtypes : List VInductiveType := []
  for t in types do
    let vty ← Ix.Theory.Named.Meta.ofExpr lparams {} t.type
    let mut vctors : List VConstVal := []
    for c in t.ctors do
      vctors := vctors ++ [⟨⟨uvars, ← Ix.Theory.Named.Meta.ofExpr lparams {} c.type⟩, c.name⟩]
    vtypes := vtypes ++ [{ name := t.name, uvars, type := vty, ctors := vctors }]
  return { uvars, nparams, types := vtypes }

open Elab in
/-- Check that the Theory flattening of one real source declaration equals
the port's flattening, that its specifications are the translated
`aux2nested` bindings, and that its auxiliary count is the stored
`numNested`. -/
def checkFlattenParity (label : String) (main : Name) (lparams : List Name)
    (nparams : Nat) (deps : List Name) (targets : List NestedTargetBlock) :
    MetaM Unit := do
  let env ← getEnv
  let src := sourceType09A env main
  let kenv := Kernel.Environment.ofConstants (`_spec09B ++ main) (depMap09A env deps)
  let .ok (flatTypes, aux) := runElim09A kenv lparams nparams [src]
    | throwError "{label}: port flattening failed"
  let sourceV ← toVInductDecl09B lparams nparams [src]
  let portFlatV ← toVInductDecl09B lparams nparams flatTypes
  let some elim := nestedElimination? targets sourceV
    | throwError "{label}: Theory flattening failed"
  unless elim.flat == portFlatV do
    throwError "{label}: Theory flattened block differs from the port's"
  unless elim.specs.length == aux.length do
    throwError "{label}: {elim.specs.length} specs vs {aux.length} aux2nested bindings"
  for spec in elim.specs do
    let some (_, value) := aux.find? (·.1 == spec.aux)
      | throwError "{label}: no aux2nested binding for {spec.aux}"
    let valueV ← Ix.Theory.Named.Meta.ofExpr lparams {} value
    unless spec.value == valueV do
      throwError "{label}: spec value for {spec.aux} differs from aux2nested"
    let .const target ls := VExpr.appHead valueV
      | throwError "{label}: aux2nested head is not a constant"
    unless spec.target == target && spec.levels == ls &&
        spec.values == valueV.appArgs [] do
      throwError "{label}: spec decomposition differs for {spec.aux}"
  let some (.inductInfo stored) := env.find? main
    | throwError "{label}: stored inductive missing"
  unless elim.numNested == stored.numNested do
    throwError "{label}: numNested {elim.numNested} vs stored {stored.numNested}"
  unless nestedStage3 targets sourceV do
    throwError "{label}: Theory acceptance rejected an accepted declaration"

run_meta do
  checkFlattenParity "rose" ``RoseTree [`u] 1 roseDeps [listTarget]
  checkFlattenParity "nv" ``NVTree [] 0 nvDeps [pvecStoredTarget]
  checkFlattenParity "cu" ``CURose [] 0 roseDeps [listTarget]

/-! ## Rejection differentials

Each negative is written once at the kernel `Expr` level and once as a
`VInductDecl`; the kernel run and the Theory gate must both reject. -/

def natDeps09B (env : Environment) : ConstMap :=
  depMap09A env [``Nat, ``Nat.zero, ``Nat.succ, ``List, ``List.nil, ``List.cons]

/-- `inductive Loose0 | node : (n : Nat) → List (Loose0 n) → Loose0` — the
parametric argument mentions the constructor-local `n`. -/
def looseDecl : Declaration :=
  .inductDecl [] 0
    [{ name := `Loose0
       type := .sort 1
       ctors := [{
         name := `Loose0.node
         type := .forallE `n (.const ``Nat [])
           (.forallE `t
             (mkApp (mkConst ``List [.zero]) (.app (.const `Loose0 []) (.bvar 0)))
             (.const `Loose0 []) .default) .default }] }]
    false

def looseSourceV : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `Loose0
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const ``Nat [])
             (.forallE (.app (.const ``List [.zero])
                 (.app (.const `Loose0 []) (.bvar 0)))
               (.const `Loose0 []))⟩, `Loose0.node⟩] }]

/-- `inductive Bad0N | node : Bad0N → List (Bad0N Nat.zero) → Bad0N` — the
parametric argument applies a block family off the parameter spine. -/
def badAppDecl : Declaration :=
  .inductDecl [] 0
    [{ name := `Bad0N
       type := .sort 1
       ctors := [{
         name := `Bad0N.node
         type := .forallE `x (.const `Bad0N [])
           (.forallE `t
             (mkApp (mkConst ``List [.zero])
               (.app (.const `Bad0N []) (.const ``Nat.zero [])))
             (.const `Bad0N []) .default) .default }] }]
    false

def badAppSourceV : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `Bad0N
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Bad0N [])
             (.forallE (.app (.const ``List [.zero])
                 (.app (.const `Bad0N []) (.const ``Nat.zero [])))
               (.const `Bad0N []))⟩, `Bad0N.node⟩] }]

/-- A two-family source whose second family occupies the canonical first
auxiliary name `_nested.List_1`. -/
def collisionDecl : Declaration :=
  let rose := fun a => mkApp (mkConst `Rose0 [.param `u]) a
  .inductDecl [`u] 1
    [{ name := `Rose0
       type := .forallE `α (.sort (.succ (.param `u))) (.sort (.succ (.param `u))) .default
       ctors := [{
         name := `Rose0.node
         type := .forallE `α (.sort (.succ (.param `u)))
           (.forallE `t (mkApp (mkConst ``List [.param `u]) (rose (.bvar 0)))
             (rose (.bvar 1)) .default) .default }] },
     { name := (`_nested ++ ``List).appendIndexAfter 1
       type := .forallE `α (.sort (.succ (.param `u))) (.sort (.succ (.param `u))) .default
       ctors := [] }]
    false

def collisionSourceV : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose0
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const ``List [.param 0])
                   (.app (.const `Rose0 [.param 0]) (.bvar 1)))
                 (.app (.const `Rose0 [.param 0]) (.bvar 2))))⟩, `Rose0.node⟩] },
     { name := (`_nested ++ ``List).appendIndexAfter 1
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors := [] }]

open Elab in
run_meta do
  let env ← getEnv
  let deps := natDeps09B env
  let kenv := Kernel.Environment.ofConstants `_spec09BNeg deps
  -- the loose parametric argument rejects in flattening, with the kernel's
  -- exact diagnostic
  match Ix.Theory.Named.addDecl kenv looseDecl with
  | .ok _ => throwError "loose: kernel accepted a local-variable parametric argument"
  | .error (.other msg) =>
      unless msg == "invalid nested inductive datatype 'List', \
          nested inductive datatypes parameters cannot contain local variables." do
        throwError "loose: unexpected kernel diagnostic {msg}"
  | .error _ => throwError "loose: unexpected kernel error shape"
  unless (nestedElimination? [listTarget] looseSourceV).isNone do
    throwError "loose: Theory flattening accepted"
  unless !nestedStage3 [listTarget] looseSourceV do
    throwError "loose: Theory gate accepted"
  -- the off-spine parametric application flattens but fails checking
  match Ix.Theory.Named.addDecl kenv badAppDecl with
  | .ok _ => throwError "badApp: kernel accepted an off-spine parametric application"
  | .error _ => pure ()
  unless (nestedElimination? [listTarget] badAppSourceV).isSome do
    throwError "badApp: Theory flattening should succeed"
  unless !nestedStage3 [listTarget] badAppSourceV do
    throwError "badApp: Theory gate accepted"
  -- the canonical-name collision rejects at insertion (kernel) and at
  -- `blockNamesOK` (Theory)
  match Ix.Theory.Named.addDecl kenv collisionDecl with
  | .ok _ => throwError "collision: kernel accepted a duplicate auxiliary name"
  | .error _ => pure ()
  unless (nestedElimination? [listTarget] collisionSourceV).isSome do
    throwError "collision: Theory flattening should succeed"
  unless !nestedStage3 [listTarget] collisionSourceV do
    throwError "collision: Theory gate accepted"
  -- a missing target declaration rejects on both sides
  let kenvNoList := Kernel.Environment.ofConstants `_spec09BNoList
    (depMap09A env [``Nat, ``Nat.zero, ``Nat.succ])
  let roseSrc := sourceType09A env ``RoseTree
  match Ix.Theory.Named.Environment.addInductive kenvNoList [`u] 1 [roseSrc] false false with
  | .ok _ => throwError "noTarget: kernel accepted without the List declaration"
  | .error _ => pure ()
  let roseV ← toVInductDecl09B [`u] 1 [roseSrc]
  unless !nestedStage3 [] roseV do
    throwError "noTarget: Theory gate accepted without target metadata"

/-! ## Restoration parity (Spec-09C)

The Theory restoration over the flattened block's generation artifacts
reproduces Lean's stored metadata exactly: every restored recursor name,
universe count, and type, and every rule RHS in the globally flattened
order, on all three real fixtures.  This runs the product σ
(`NestedBlockChecked.recursors`/`generatedRules`), not the Spec-09A design
probe. -/

open Elab in
def checkRestoreParity (label : String) (main : Name) (lparams : List Name)
    (nparams : Nat) (targets : List NestedTargetBlock) : MetaM Unit := do
  let env ← getEnv
  let src := sourceType09A env main
  let sourceV ← toVInductDecl09B lparams nparams [src]
  let some nested := nestedBlockChecked? targets sourceV
    | throwError "{label}: nested acceptance failed"
  let expectedNames := [mkRecName main] ++
    nested.elim.specs.mapIdx fun i _ => (mkRecName main).appendIndexAfter (i + 1)
  unless nested.recursors.length == expectedNames.length do
    throwError "{label}: {nested.recursors.length} restored recursors, \
      expected {expectedNames.length}"
  for (r, expected) in nested.recursors.zip expectedNames do
    unless r.name == expected do
      throwError "{label}: restored recursor name {r.name}, expected {expected}"
    let some (.recInfo stored) := env.find? expected
      | throwError "{label}: stored recursor {expected} missing"
    unless r.uvars == stored.levelParams.length do
      throwError "{label}: recursor universe count differs for {expected}"
    let storedType ← Ix.Theory.Named.Meta.ofExpr stored.levelParams {}
      (← Ix.Theory.Named.Meta.expandExpr stored.type)
    unless r.type == storedType do
      throwError "{label}: restored recursor type differs from stored for {expected}"
  let mut storedRules : List (Name × Expr) := []
  for n in expectedNames do
    let some (.recInfo stored) := env.find? n
      | throwError "{label}: stored recursor {n} missing"
    for rule in stored.rules do
      storedRules := storedRules ++ [(rule.ctor, rule.rhs)]
  let rules := nested.generatedRules
  unless rules.length == storedRules.length do
    throwError "{label}: {rules.length} restored rules, stored {storedRules.length}"
  let some (.recInfo mainRec) := env.find? (mkRecName main)
    | throwError "{label}: stored main recursor missing"
  for (df, (ctor, storedRhs)) in rules.zip storedRules do
    let storedRhsV ← Ix.Theory.Named.Meta.ofExpr mainRec.levelParams {}
      (← Ix.Theory.Named.Meta.expandExpr storedRhs)
    unless df.rhs == storedRhsV do
      throwError "{label}: restored rule RHS differs from stored for {ctor}"

run_meta do
  checkRestoreParity "rose" ``RoseTree [`u] 1 [listTarget]
  checkRestoreParity "nv" ``NVTree [] 0 [pvecStoredTarget]
  checkRestoreParity "cu" ``CURose [] 0 [listTarget]

/-! ## Real-output round-trip (Spec-09C)

Run the port's complete `Environment.addInductive` on a dependency-only
kernel environment and compare its entire output — not the ambient
elaborator metadata — against the Theory nested artifacts: the stored
payload against the source constants, and every emitted recursor's name,
universe count, type, rule constructors, rule field counts, and rule RHSs
against the restored inventory.  Nothing in this comparison is
hand-authored: the left side is real `Inductive.Add.run`-derived output
and the right side is computed by `nestedBlockChecked?`. -/

open Elab in
def checkOutputRoundTrip (label : String) (main : Name) (lparams : List Name)
    (nparams : Nat) (deps : List Name) (targets : List NestedTargetBlock) :
    MetaM Unit := do
  let env ← getEnv
  let src := sourceType09A env main
  let kenv := Kernel.Environment.ofConstants (`_spec09C ++ main) (depMap09A env deps)
  let .ok kout := Ix.Theory.Named.Environment.addInductive kenv lparams nparams [src] false false
    | throwError "{label}: port addInductive failed"
  let sourceV ← toVInductDecl09B lparams nparams [src]
  let some nested := nestedBlockChecked? targets sourceV
    | throwError "{label}: nested acceptance failed"
  -- the stored payload: families and constructors
  for tyV in sourceV.types do
    let some (.inductInfo out) := kout.find? tyV.name
      | throwError "{label}: output family {tyV.name} missing"
    let outType ← Ix.Theory.Named.Meta.ofExpr out.levelParams {} (← Ix.Theory.Named.Meta.expandExpr out.type)
    unless out.levelParams.length == tyV.uvars && outType == tyV.type do
      throwError "{label}: output family metadata differs for {tyV.name}"
    unless out.numNested == nested.elim.numNested do
      throwError "{label}: output numNested {out.numNested} vs \
        artifact {nested.elim.numNested}"
    for cV in tyV.ctors do
      let some (.ctorInfo outC) := kout.find? cV.name
        | throwError "{label}: output constructor {cV.name} missing"
      let outCType ← Ix.Theory.Named.Meta.ofExpr outC.levelParams {}
        (← Ix.Theory.Named.Meta.expandExpr outC.type)
      unless outC.levelParams.length == cV.uvars && outCType == cV.type do
        throwError "{label}: output constructor metadata differs for {cV.name}"
  -- the restored recursors and their rules, in inventory order
  let mut ruleIdx := 0
  let rules := nested.generatedRules
  for r in nested.recursors do
    let some (.recInfo out) := kout.find? r.name
      | throwError "{label}: output recursor {r.name} missing"
    let outType ← Ix.Theory.Named.Meta.ofExpr out.levelParams {} (← Ix.Theory.Named.Meta.expandExpr out.type)
    unless out.levelParams.length == r.uvars && outType == r.type do
      throwError "{label}: output recursor metadata differs for {r.name}"
    unless out.k == nested.generation.kTarget do
      throwError "{label}: output recursor K flag differs for {r.name}"
    for rule in out.rules do
      let some df := rules[ruleIdx]?
        | throwError "{label}: more output rules than restored rules"
      let outRhs ← Ix.Theory.Named.Meta.ofExpr out.levelParams {}
        (← Ix.Theory.Named.Meta.expandExpr rule.rhs)
      unless outRhs == df.rhs do
        throwError "{label}: output rule RHS differs for {rule.ctor}"
      ruleIdx := ruleIdx + 1
  unless ruleIdx == rules.length do
    throwError "{label}: {rules.length} restored rules, output consumed {ruleIdx}"

run_meta do
  checkOutputRoundTrip "rose" ``RoseTree [`u] 1 roseDeps [listTarget]
  checkOutputRoundTrip "nv" ``NVTree [] 0 nvDeps [pvecStoredTarget]
  checkOutputRoundTrip "cu" ``CURose [] 0 roseDeps [listTarget]

end Ix.Theory.Named.NestedTransformation
