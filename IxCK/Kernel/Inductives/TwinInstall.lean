module

public import IxCK.Kernel.CheckerBase
public import IxCK.Kernel.Inductives.WrapCheck

@[expose] public section

/-! # Checking recursor twins against stored canonical recursors

Headers are checked in the original environment. Model companions, when present, are
copied before rule-less recursors are provisioned. Rule annotation uses that complete
provisioned environment. A single checked renaming relates every installed rule to its
canonical rule. The existing modeled route remains available to declarations carrying
their own model companions.
-/

namespace Ix.Kernel.NativeTwin

open Ix.Kernel.Semantics (wrapRelOk letFree)

variable {m : Type → Type} [Monad m] [MonadExcept (CheckError md) m]

structure Part (md : Mode) where
  raw : ConstantVal md
  annotated : ConstantVal md
  canonical : ConstantVal md
  canonicalKey : Key md
  majorIndex : Nat
  rulePrefix : Nat
  rawRules : List (RecRule md)
  canonicalRules : List (RecRule md)
  checkedRules : List (RecRule md) := []
  model? : Option (ConstantVal md × Expr md × ReducibilityHint)

def modelInfo? (part : Part md) : Option (ConstantInfo md) :=
  part.model?.map fun (cv, value, hint) =>
    .defnInfo ⟨auxKey part.raw.name .model, cv.levelParams, cv.type⟩ value hint

def models (parts : List (Part md)) : List (ConstantInfo md) := parts.filterMap modelInfo?

def provision (parts : List (Part md)) : List (ConstantInfo md) :=
  parts.map fun part => .recInfo part.annotated part.majorIndex part.rulePrefix []

def recursors (parts : List (Part md)) : List (ConstantInfo md) :=
  parts.map fun part => .recInfo part.annotated part.majorIndex part.rulePrefix part.checkedRules

def selfEnv (env : Env md) (parts : List (Part md)) : Env md :=
  ⟨provision parts ++ models parts ++ env.consts⟩

def majorAgrees (majorIndex : Nat) (canonical annotated : Expr md) : Bool :=
  match annotated.stripPis majorIndex with
  | some (_, .forallE domW _ _) =>
    match canonical.stripPis majorIndex with
    | some (_, .forallE domC _ _) => domW.getAppFn == domC.getAppFn && domW.getAppArgs == domC.getAppArgs
    | _ => false
  | _ => true

def candidate (find? : Key md → Option (ConstantInfo md))
    (raw annotated : ConstantVal md) (majorIndex rulePrefix : Nat) (rules : List (RecRule md))
    (key : Key md) : Option (Part md) := do
  let some (.recInfo canonical mI rP canonicalRules) := find? key | none
  unless mI == majorIndex && rP == rulePrefix && raw.levelParams == canonical.levelParams &&
      rules.length == canonicalRules.length && wrapRelOk find? canonical.type annotated.type do none
  let model? := match find? (auxKey key .model) with
    | some (.defnInfo cv value hint) => some (cv, value, hint)
    | _ => none
  unless model?.isSome || majorAgrees majorIndex canonical.type annotated.type do none
  pure {
    raw := raw
    annotated := annotated
    canonical := canonical
    canonicalKey := key
    majorIndex := majorIndex
    rulePrefix := rulePrefix
    rawRules := rules
    canonicalRules := canonicalRules
    model? := model?
  }

def findCanonical (find? : Key md → Option (ConstantInfo md))
    (raw annotated : ConstantVal md) (majorIndex rulePrefix : Nat) (rules : List (RecRule md)) :
    List (ConstantInfo md) → Option (Part md)
  | [] => none
  | .recInfo cv _ _ _ :: rest =>
    candidate find? raw annotated majorIndex rulePrefix rules cv.name <|>
      findCanonical find? raw annotated majorIndex rulePrefix rules rest
  | _ :: rest => findCanonical find? raw annotated majorIndex rulePrefix rules rest

def checkHeader (ops : CheckerOps md m) (env : Env md) (ci : ConstantInfo md) : m (Part md) := do
  let .recInfo raw majorIndex rulePrefix rules := ci
    | throw (.notImplemented "twin route requires recursor-only declarations")
  let annotated ← checkConstantVal ops env raw
  unless letFree annotated.type do throw (.notImplemented "twin recursor type contains let")
  let some part := findCanonical env.find? raw annotated majorIndex rulePrefix rules env.consts
    | throw (.notImplemented msg!"no compatible stored recursor for {raw.name}")
  pure part

def checkHeaders (ops : CheckerOps md m) (env : Env md) : List (ConstantInfo md) → m (List (Part md))
  | [] => pure []
  | ci :: rest => do
    let part ← checkHeader ops env ci
    let parts ← checkHeaders ops env rest
    pure (part :: parts)

def prepare (ops : CheckerOps md m) (env : Env md) (block : List (ConstantInfo md)) : m (List (Part md)) := do
  if block.isEmpty then throw (.notImplemented "empty twin recursor declaration")
  let parts ← checkHeaders ops env block
  let added := provision parts ++ models parts
  unless (added.map (·.name)).Nodup do throw (.invalid "duplicate twin or model name")
  unless added.all (fun ci => (env.find? ci.name).isNone) do throw (.invalid "twin or model name already stored")
  pure parts

def ruleShape (env : Env md) (part : Part md) (rule : RecRule md) : Bool :=
  match rule.fire with
  | .plain =>
    match env.find? rule.ctor with
    | some (.ctorInfo cv _ _) =>
      Expr.recRulePlain part.annotated.type part.majorIndex part.rulePrefix rule.ctorParams cv.levelParams
    | _ => false
  | .nested levels pins =>
    match part.annotated.type.stripPis part.majorIndex with
    | some (_, .forallE dom _ _) =>
      match dom.getAppFn with
      | .const _ foundLevels =>
        foundLevels == levels && dom.getAppArgs ==
          pins.map (Expr.liftLooseBVars (part.majorIndex - part.rulePrefix) 0) ++
            (List.range (part.majorIndex - part.rulePrefix)).map
              (fun i => Expr.bvar (part.majorIndex - part.rulePrefix - 1 - i))
      | _ => false
    | _ => false
  | .inert => true

def checkRule (ops : CheckerOps md m) (env envSelf : Env md) (part : Part md)
    (raw canonical : RecRule md) : m (RecRule md) := do
  unless raw.ctor == canonical.ctor && raw.nfields == canonical.nfields do
    throw (.notImplemented "twin constructor or field count mismatch")
  unless raw.rhs.looseBVarsBounded 0 && !raw.rhs.hasFvar do
    throw (.invalid "unscoped twin recursor rule")
  let rhs ← ops.annotate envSelf 0 raw.rhs
  unless rhs.allLevelParamsDefined part.canonical.levelParams && rhs.constsResolve envSelf && letFree rhs do
    throw (.invalid "unscoped annotated twin recursor rule")
  unless ruleShape env part canonical do throw (.notImplemented "twin rule major-premise shape mismatch")
  pure { canonical with rhs := rhs, eta := recRuleEtaOf env.find? part.raw.name canonical.ctor }

def checkRules (ops : CheckerOps md m) (env envSelf : Env md) (part : Part md) :
    List (RecRule md) → List (RecRule md) → m (List (RecRule md))
  | [], [] => pure []
  | raw :: raws, canonical :: canonicals => do
    let checked ← checkRule ops env envSelf part raw canonical
    let rest ← checkRules ops env envSelf part raws canonicals
    pure (checked :: rest)
  | _, _ => throw (.notImplemented "twin recursor rule count mismatch")

def checkPartsRules (ops : CheckerOps md m) (env envSelf : Env md) : List (Part md) → m (List (Part md))
  | [] => pure []
  | part :: parts => do
    let checkedRules ← checkRules ops env envSelf part part.rawRules part.canonicalRules
    let rest ← checkPartsRules ops env envSelf parts
    pure ({ part with checkedRules := checkedRules } :: rest)

def peerRename (parts : List (Part md)) (key : Key md) : Key md :=
  match parts.find? (fun part => part.canonicalKey == key) with
  | some part => part.raw.name
  | none => key

def rulesWrap (env : Env md) (rename : Key md → Key md) (parts : List (Part md)) : Bool :=
  parts.all fun part =>
    (part.checkedRules.zip part.canonicalRules).all fun (checked, canonical) =>
      wrapRelOk env.find? (canonical.rhs.renameConsts rename) checked.rhs

def finish (env : Env md) (parts : List (Part md)) : m (Env md) := do
  unless rulesWrap env id parts || rulesWrap env (peerRename parts) parts do
    throw (.notImplemented "twin recursor rules differ from the stored recursor")
  pure ⟨recursors parts ++ models parts ++ env.consts⟩

def check (ops : CheckerOps md m) (env : Env md) (block : List (ConstantInfo md)) : m (Env md) := do
  let parts ← prepare ops env block
  let checked ← checkPartsRules ops env (selfEnv env parts) parts
  finish env checked

/-- A declaration with its own model companions keeps the established modeled route. -/
def usesStoredRecursors (find? : Key md → Option (ConstantInfo md)) (block : List (ConstantInfo md)) : Bool :=
  !block.isEmpty && block.all (fun | .recInfo .. => true | _ => false) &&
    !(block.all fun ci => match find? (auxKey ci.name .model) with
      | some (.defnInfo ..) => true
      | _ => false)

end Ix.Kernel.NativeTwin
