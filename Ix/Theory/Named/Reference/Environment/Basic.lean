/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Lean.Environment
import Batteries.Tactic.OpenPrivate

namespace Lean.Kernel.Environment

def contains (env : Environment) (n : Name) : Bool :=
  env.constants.contains n

def get (env : Environment) (n : Name) : Except Exception ConstantInfo :=
  match env.find? n with
  | some ci => pure ci
  | none => throw <| .unknownConstant env n

def checkDuplicatedUnivParams : List Name → Except Exception Unit
  | [] => pure ()
  | p :: ls => do
    if p ∈ ls then
      throw <| .other
        s!"failed to add declaration to environment, duplicate universe level parameter: '{p}'"
    checkDuplicatedUnivParams ls

def checkNoMVar (env : Environment) (n : Name) (e : Expr) : Except Exception Unit := do
  if e.hasMVar then
    throw <| .declHasMVars env n e

def checkNoFVar (env : Environment) (n : Name) (e : Expr) : Except Exception Unit := do
  if e.hasFVar then
    throw <| .declHasFVars env n e

def checkNoMVarNoFVar (env : Environment) (n : Name) (e : Expr) : Except Exception Unit := do
  checkNoMVar env n e
  checkNoFVar env n e

def primitives : NameSet := .ofList [
  ``Bool, ``Bool.false, ``Bool.true,
  ``Nat, ``Nat.zero, ``Nat.succ,
  ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
  ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight,
  ``String.ofList, ``Char.ofNat]

/--
Returns true iff `constName` is a non-recursive inductive datatype that has only one constructor and no indices.

Such types have special kernel support (e.g. the eta rule).
This must be in sync with `is_non_rec_structure()`.
-/
def isNonRecStructure (env : Environment) (constName : Name) : Bool :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [_], numIndices := 0, .. }) => true
  | _ => false

/-- A one-constructor, unindexed structure whose constructor and generated
recursor have both reached the host environment.  Family metadata is staged
before either artifact is inserted; projection verification may only demand a
registered Theory view at this later boundary.

Unlike `isNonRecStructure`, projection readiness deliberately does not inspect
`InductiveVal.isRec`: Lean emits primitive projections for recursive structures
too (including nested-recursive structures in the Lean prelude). -/
def isProjectionReadyStructure (env : Environment) (constName : Name) : Bool :=
  match env.constants.find?' constName with
  | some (.inductInfo { ctors := [ctor], numIndices := 0, .. }) =>
    match env.constants.find?' ctor,
        env.constants.find?' (mkRecName constName) with
    | some (.ctorInfo _), some (.recInfo _) => true
    | _, _ => false
  | _ => false

theorem isProjectionReadyStructure_false_of_no_ctorInfo
    {env : Environment} {name : Name} {info : InductiveVal}
    (hfind : env.constants.find?' name = some (.inductInfo info))
    (hnoCtor : ∀ ctor ctorInfo,
      env.constants.find?' ctor ≠ some (.ctorInfo ctorInfo)) :
    env.isProjectionReadyStructure name = false := by
  cases info
  rename_i constant numParams numIndices all ctors numNested isRec isUnsafe isReflexive
  cases constant
  unfold isProjectionReadyStructure
  rw [hfind]
  cases numIndices with
  | succ _ => rfl
  | zero =>
    cases ctors with
    | nil => rfl
    | cons ctor rest =>
      cases rest with
      | cons _ _ => rfl
      | nil =>
        cases hctor : env.constants.find?' ctor with
        | none => simp [hctor]
        | some info =>
          cases info <;> simp_all

theorem isProjectionReadyStructure_false_of_numIndices_ne
    {env : Environment} {name : Name} {info : InductiveVal}
    (hfind : env.constants.find?' name = some (.inductInfo info))
    (hindices : info.numIndices ≠ 0) :
    env.isProjectionReadyStructure name = false := by
  cases info
  simp_all [isProjectionReadyStructure]

theorem isProjectionReadyStructure_false_of_not_found
    {env : Environment} {name : Name}
    (hfind : env.constants.find?' name = none) :
    env.isProjectionReadyStructure name = false := by
  simp [isProjectionReadyStructure, hfind]

def checkName (env : Environment) (n : Name)
    (allowPrimitive := false) : Except Exception Unit := do
  if env.contains n then
    throw <| .alreadyDeclared env n
  unless allowPrimitive do
    if primitives.contains n then
      throw <| .other s!"unexpected use of primitive name {n}"

open private subsumesInfo Kernel.Environment.mk EnvironmentHeader.mk moduleNames
  moduleNameMap parts toEffectiveImport getData? from Lean.Environment

def empty (mainModule : Name) (trustLevel : UInt32 := 0) : Environment :=
  Kernel.Environment.mk
    (constants := {})
    (quotInit := false)
    (diagnostics := {})
    (const2ModIdx := {})
    (extensions := #[])
    (irBaseExts := #[])
    (header := EnvironmentHeader.mk
      (mainModule := mainModule)
      (trustLevel := trustLevel)
      (isModule := false)
      (imports := #[])
      (regions := #[])
      (modules := #[])
      (moduleName2Idx := {})
      (importAllModules := #[])
      (moduleData := #[]))

/-- A minimal kernel environment backed by an explicit constant map.

This is used by verified staged checks (for example, while an inductive family
has been inserted but its constructors have not). Such states are real kernel
checking stages but are not importable modules, so they intentionally carry no
extensions or module metadata. -/
def ofConstants (mainModule : Name) (constants : ConstMap)
    (quotInit := false) (trustLevel : UInt32 := 0) : Environment :=
  Kernel.Environment.mk
    (constants := constants)
    (quotInit := quotInit)
    (diagnostics := {})
    (const2ModIdx := {})
    (extensions := #[])
    (irBaseExts := #[])
    (header := EnvironmentHeader.mk
      (mainModule := mainModule)
      (trustLevel := trustLevel)
      (isModule := false)
      (imports := #[])
      (regions := #[])
      (modules := #[])
      (moduleName2Idx := {})
      (importAllModules := #[])
      (moduleData := #[]))

def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx)
    (modIdx : Nat) (cname : Name) : Except Exception α := do
  let modName := (moduleNames s)[modIdx]!
  let constModName := (moduleNames s)[const2ModIdx[cname]!.toNat]!
  throw <| .other
    s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

def finalizeImport (s : ImportState) (imports : Array Import) (mainModule : Name)
    (trustLevel : UInt32 := 0) : Except Exception Environment := do
  let modules := (moduleNames s).filterMap ((moduleNameMap s)[·]?)
  let moduleData ← modules.mapM fun mod => do
    let some data := getData? mod .private |
      throw <| .other s!"missing data file for module {mod.module}"
    return data
  let numConsts := moduleData.foldl (init := 0) fun numConsts data => Id.run do
    numConsts + data.constants.size
  let mut const2ModIdx := .emptyWithCapacity (capacity := numConsts)
  let mut constantMap := .emptyWithCapacity (capacity := numConsts)
  for h : modIdx in *...moduleData.size do
    let data := moduleData[modIdx]
    for cname in data.constNames, cinfo in data.constants do
      match constantMap.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, constantMap') =>
        constantMap := constantMap'
        if let some cinfoPrev := cinfoPrev? then
          -- Recall that the map has not been modified when `cinfoPrev? = some _`.
          if subsumesInfo constantMap cinfo cinfoPrev then
            constantMap := constantMap.insert cname cinfo
          else if !subsumesInfo constantMap cinfoPrev cinfo then
            throwAlreadyImported s const2ModIdx modIdx cname
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
    for cname in data.extraConstNames do
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
  let mut moduleName2Idx := {}
  for _h : idx in [0:modules.size] do
    let mod := modules[idx]
    moduleName2Idx := moduleName2Idx.insert mod.module idx

  return Kernel.Environment.mk
    (constants := SMap.fromHashMap constantMap false)
    (quotInit := !imports.isEmpty) -- We assume `Init.Prelude` initializes quotient module
    (diagnostics := {})
    (const2ModIdx := const2ModIdx)
    (extensions := #[])
    (irBaseExts := #[])
    (header := EnvironmentHeader.mk
      (mainModule := mainModule)
      (trustLevel := trustLevel)
      (isModule := false)
      (imports := imports)
      (regions := modules.flatMap (parts · |>.map (·.2)))
      (modules := modules.map toEffectiveImport)
      (moduleName2Idx := moduleName2Idx)
      (importAllModules := #[])
      (moduleData := moduleData))
