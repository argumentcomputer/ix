import LSpec
import Ix.Ixon
import Ix.Ixon.Metadata
import LSpec.SlimCheck.Gen
import LSpec

import Tests.Ixon.Gen.Common
import Tests.Ixon.Gen.Univ
import Tests.Ixon.Gen.Expr
import Batteries

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon

def genNamePart : Gen NamePart := oneOf #[ .str <$> genString, .num <$> genNat']

def genName : Gen Lean.Name := nameFromParts <$> genList' genNamePart

def genBinderInfo : Gen Lean.BinderInfo := oneOf
  #[ pure .default
   , pure .instImplicit
   , pure .strictImplicit
   , pure .instImplicit
   ]

def genMetaNode : Gen MetaNode := 
  .mk <$> genOption genName <*> genOption genBinderInfo <*> genOption genAddress

def genMetadata : Gen Metadata := do
  let xs ← genList' genMetaNode
  return .mk (Batteries.RBMap.ofList ((List.range xs.length).zip xs) compare)
