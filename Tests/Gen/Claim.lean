/-
  Generators for Ix.Claim types (RevealConstructorInfo, RevealRecursorRule, etc.).
-/
module

public import LSpec
public import Tests.Gen.Ixon
public import Ix.Claim

public section

open LSpec SlimCheck Gen
open Ix (RevealConstructorInfo RevealRecursorRule RevealMutConstInfo RevealConstantInfo Claim
         DefKind DefinitionSafety QuotKind)
open Tests.Gen.Ixon (genAddress genUInt64Small genDefKind genDefinitionSafety genQuotKindNew
                      genSmallArray)

namespace Tests.Gen.Claim

/-! ## Helper -/

def genOptional (g : Gen α) : Gen (Option α) :=
  frequency [
    (1, pure none),
    (1, some <$> g),
  ]

/-! ## Generators -/

def genRevealConstructorInfo : Gen RevealConstructorInfo :=
  RevealConstructorInfo.mk
    <$> genOptional genBool
    <*> genOptional genUInt64Small
    <*> genOptional genUInt64Small
    <*> genOptional genUInt64Small
    <*> genOptional genUInt64Small
    <*> genOptional genAddress

def genRevealRecursorRule : Gen RevealRecursorRule :=
  RevealRecursorRule.mk <$> genUInt64Small <*> genUInt64Small <*> genAddress

def genRevealMutConstInfo : Gen RevealMutConstInfo :=
  frequency [
    (10, RevealMutConstInfo.defn
      <$> genOptional genDefKind <*> genOptional genDefinitionSafety
      <*> genOptional genUInt64Small <*> genOptional genAddress <*> genOptional genAddress),
    (5, RevealMutConstInfo.indc
      <$> genOptional genBool <*> genOptional genUInt64Small
      <*> genOptional genUInt64Small <*> genOptional genUInt64Small
      <*> genOptional genAddress
      <*> genOptional (genSmallArray (Prod.mk <$> genUInt64Small <*> genRevealConstructorInfo))),
    (5, RevealMutConstInfo.recr
      <$> genOptional genBool <*> genOptional genBool
      <*> genOptional genUInt64Small <*> genOptional genUInt64Small
      <*> genOptional genUInt64Small <*> genOptional genUInt64Small
      <*> genOptional genUInt64Small <*> genOptional genAddress
      <*> genOptional (genSmallArray genRevealRecursorRule)),
  ]

def genRevealConstantInfo : Gen RevealConstantInfo :=
  frequency [
    (10, RevealConstantInfo.defn
      <$> genOptional genDefKind <*> genOptional genDefinitionSafety
      <*> genOptional genUInt64Small <*> genOptional genAddress <*> genOptional genAddress),
    (5, RevealConstantInfo.recr
      <$> genOptional genBool <*> genOptional genBool
      <*> genOptional genUInt64Small <*> genOptional genUInt64Small
      <*> genOptional genUInt64Small <*> genOptional genUInt64Small
      <*> genOptional genUInt64Small <*> genOptional genAddress
      <*> genOptional (genSmallArray genRevealRecursorRule)),
    (10, RevealConstantInfo.axio
      <$> genOptional genBool <*> genOptional genUInt64Small <*> genOptional genAddress),
    (10, RevealConstantInfo.quot
      <$> genOptional genQuotKindNew <*> genOptional genUInt64Small <*> genOptional genAddress),
    (10, RevealConstantInfo.cPrj
      <$> genOptional genUInt64Small <*> genOptional genUInt64Small <*> genOptional genAddress),
    (5, RevealConstantInfo.rPrj
      <$> genOptional genUInt64Small <*> genOptional genAddress),
    (5, RevealConstantInfo.iPrj
      <$> genOptional genUInt64Small <*> genOptional genAddress),
    (5, RevealConstantInfo.dPrj
      <$> genOptional genUInt64Small <*> genOptional genAddress),
    (5, RevealConstantInfo.muts
      <$> genSmallArray (Prod.mk <$> genUInt64Small <*> genRevealMutConstInfo)),
  ]

def genOptAddress : Gen (Option Address) := genOptional genAddress

/-- A context that validates its binding. -/
def genClaimContext : Gen Ix.ClaimContext :=
  (fun spec binding axioms => { spec, binding, axioms })
    <$> genAddress <*> genAddress <*> genOptAddress

/-- A context for `check` or `checkEnv`, which may assume its binding. -/
def genAssumableContext : Gen Ix.ClaimContext :=
  (fun ctx assumed => { ctx with bindingAssumed := assumed })
    <$> genClaimContext <*> genBool

def genClaim : Gen Claim :=
  frequency [
    (10, Claim.eval     <$> genClaimContext <*> genAddress <*> genAddress <*> genOptAddress),
    (10, Claim.check    <$> genAssumableContext <*> genAddress <*> genOptAddress),
    (10, Claim.checkEnv <$> genAssumableContext <*> genAddress <*> genOptAddress),
    (10, Claim.reveal   <$> genAddress <*> genRevealConstantInfo),
    (10, Claim.contains <$> genAddress <*> genAddress),
    (10, Claim.binding  <$> genAddress <*> genAddress),
    (10, Claim.catalog  <$> genClaimContext <*> genAddress <*> genAddress <*> genOptAddress),
    (10, Claim.resource <$> genAddress <*> genAddress),
  ]

/-! ## Shrinkable instances -/

instance : Shrinkable RevealConstructorInfo where
  shrink info :=
    if info.isUnsafe.isSome || info.lvls.isSome || info.cidx.isSome ||
       info.params.isSome || info.fields.isSome || info.typ.isSome
    then [⟨none, none, none, none, none, none⟩]
    else []

instance : Shrinkable RevealRecursorRule where
  shrink rule :=
    (if rule.ruleIdx > 0 then [{ rule with ruleIdx := rule.ruleIdx / 2 }] else []) ++
    (if rule.fields > 0 then [{ rule with fields := rule.fields / 2 }] else [])

instance : Shrinkable RevealMutConstInfo where
  shrink
    | .defn none none none none none => []
    | _ => [.defn none none none none none]

instance : Shrinkable RevealConstantInfo where
  shrink
    | .axio none none none => []
    | _ => [.axio none none none]

instance : Shrinkable Claim where
  shrink
    | .check _ _ none => []
    | .checkEnv _ _ none => []
    | .check ctx c (some _) => [.check ctx c none]
    | .checkEnv ctx r (some _) => [.checkEnv ctx r none]
    | .eval ctx input _ _ => [.check ctx input none]
    | .reveal comm info =>
      (.reveal comm <$> Shrinkable.shrink info) ++ [.check default comm none]
    | .contains t _ => [.checkEnv default t none]
    | .catalog ctx m _ none => [.checkEnv ctx m none]
    | .resource _ _ => []
    | .binding _ _ => []
    | .catalog ctx m c (some _) => [.catalog ctx m c none]

/-! ## SampleableExt instances -/

instance : SampleableExt RevealConstructorInfo := SampleableExt.mkSelfContained genRevealConstructorInfo
instance : SampleableExt RevealRecursorRule := SampleableExt.mkSelfContained genRevealRecursorRule
instance : SampleableExt RevealMutConstInfo := SampleableExt.mkSelfContained genRevealMutConstInfo
instance : SampleableExt RevealConstantInfo := SampleableExt.mkSelfContained genRevealConstantInfo
instance : SampleableExt Claim := SampleableExt.mkSelfContained genClaim

end Tests.Gen.Claim

end

