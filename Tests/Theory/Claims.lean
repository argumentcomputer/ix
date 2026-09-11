/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Claims
import Ix.Theory.Certified.ClaimComposition
import Tests.Theory.Acceptance
import Tests.Theory.Standard

open Ix.Theory

namespace Tests.Theory.Claims

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certificate
open Tests.Theory.Certified (primitives)
open Tests.Theory.Checker (identity identityType)

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def ref (n : Nat) : ConstRef Nat := .member n 0
def aliasDeclaration (n : Nat) : Const Nat :=
  .defn 1 .theorem (identityType (.param 0)).erase (.const (ref n) [.param 0]) .safe

def declaration : Nat → Const Nat
  | 10 => PrimitiveSignature.falseDeclaration
  | 11 => primitives.falseElimDeclaration
  | 12 => Acceptance.idDeclaration
  | 13 | 14 => aliasDeclaration 12
  | 15 => .defn 1 .theorem (identityType (.param 0)).erase
      (.app (.lam (identityType (.param 0)).erase (.const (ref 13) [.param 0]))
        (.const (ref 14) [.param 0])) .safe
  | _ => .axiom 0 primitives.falseExpr .safe

def store (alter : Nat → Const Nat → Const Nat := fun _ c => c) : Store Nat where
  dom := [10, 11, 12, 13, 14, 15]
  nodup := by decide
  blocks b := if b ∈ [10, 11, 12, 13, 14, 15] then some ⟨[alter b (declaration b)]⟩ else none
  mem_dom b := by split <;> simp_all

def specs : List (List (ConstRef Nat) × List (ConstRef Nat)) :=
  [([], [ref 12]), ([ref 12], [ref 13]), ([ref 12], [ref 14]), ([ref 13, ref 14], [ref 15])]

def nodes? (source : Store Nat := store) : Option (List (ClaimNode Nat)) :=
  specs.mapM fun (frontier, subjects) => claimNode? 1000 primitives source frontier subjects

def accepted (source : Store Nat) (nodes : List (ClaimNode Nat)) : Bool :=
  (batchFrontier? 1000 primitives source nodes).any fun frontier =>
    acceptsBatch.{0,0} 1000 primitives source frontier nodes

def positive : Bool := (nodes?).any (accepted store)
#guard positive

-- Each leaf is independently a valid conditional check.
#guard (nodes?).any fun nodes => nodes.all fun node =>
  (checkNode?.{0,0} 1000 primitives store node).isSome

-- The same diamond can retain A as a genuine external obligation.
#guard (nodes?).any fun nodes => accepted store (nodes.drop 1)
#guard (nodes?).any fun nodes =>
  (batchFrontier? 1000 primitives store (nodes.drop 1)).any fun frontier =>
    (checkBatch?.{0,0} 1000 primitives store frontier (nodes.drop 1)).any fun result =>
      result.receipt.frontier.refs == [ref 12]

-- Structural discharge closes all four subjects and produces their model.
#guard (nodes?).any fun nodes =>
  (checkBatch?.{0,0} 1000 primitives store [] nodes).any fun result =>
    result.receipt.frontier.refs.isEmpty && nodeSubjects result.nodes == [ref 12, ref 13, ref 14, ref 15]

-- A reverse dependency cannot be supplied by a later node.
#guard (nodes?).any fun nodes => !accepted store nodes.reverse
#guard (nodes?).any fun nodes => !accepted store (nodes[0]! :: nodes[3]! :: [nodes[1]!, nodes[2]!])
-- Repeated subjects share an existing checked interpretation.
#guard (nodes?).any fun nodes => accepted store (nodes ++ nodes)
#guard (nodes?).any fun nodes =>
  !(acceptsBatch.{0,0} 1000 primitives store [] (nodes.drop 1))
#guard (nodes?).any fun nodes =>
  !(acceptsBatch.{0,0} 0 primitives store [] nodes)

-- Source changes reject an original valid leaf certificate.
#guard (nodes?).any fun nodes =>
  !accepted (store fun n c => if n = 15 then
    .defn 1 .theorem primitives.falseExpr (.const (ref 13) [.param 0]) .safe else c) nodes
#guard (nodes?).any fun nodes =>
  !accepted (store fun n c => if n = 12 then .axiom 1 (identityType (.param 0)).erase .safe else c) nodes

def cyclicStore : Store Nat := store fun n c =>
  if n = 12 then .defn 0 .theorem primitives.falseExpr (.const (ref 13) []) .safe
  else if n = 13 then .defn 0 .theorem primitives.falseExpr (.const (ref 12) []) .safe else c

def cyclicNodes? : Option (List (ClaimNode Nat)) := do
  return [← claimNode? 1000 primitives cyclicStore [ref 13] [ref 12],
    ← claimNode? 1000 primitives cyclicStore [ref 12] [ref 13]]

-- Both conditional implications pass, but neither circular ordering closes.
#guard cyclicNodes?.any fun nodes => nodes.all fun node =>
  (checkNode?.{0,0} 1000 primitives cyclicStore node).isSome
#guard cyclicNodes?.any fun nodes => !accepted cyclicStore nodes
#guard cyclicNodes?.any fun nodes => !accepted cyclicStore nodes.reverse

-- Claiming a deferred member as an owned subject is rejected.
#guard (claimNode? 1000 primitives store [ref 12] [ref 12]).any fun node =>
  (checkNode?.{0,0} 1000 primitives store node).isNone

-- A source axiom cannot enter as a deferred assumption, including supported
-- schemas: their semantic producer must run, and their use remains recorded.
#guard (frontierWitnesses? 1000 Standard.store primitives.environment [Standard.propextRef]).isNone

def standardNodes? : Option (List (ClaimNode Nat)) := do
  return [← claimNode? 2000 primitives Standard.store [] [Standard.propextRef],
    ← claimNode? 2000 primitives Standard.store [] [Standard.choiceRef]]

#guard standardNodes?.any fun nodes =>
  (checkBatch?.{0,0} 2000 primitives Standard.store [] nodes).any fun result =>
    result.receipt.frontier.refs.isEmpty &&
      result.logicalUses == [Standard.propextRef, Standard.choiceRef]

-- The recorded axiom remains even when that same reference is a checked subject.
#guard standardNodes?.any fun nodes =>
  (checkBatch?.{0,0} 2000 primitives Standard.store [] (nodes.take 1)).any fun result =>
    Standard.propextRef ∈ nodeSubjects result.nodes &&
      Standard.propextRef ∈ result.logicalUses

-- Regrouping composition has identical acceptance and complete subjects.
#guard nodes?.any fun nodes =>
  accepted store (composeClaims (composeClaims (nodes.take 1) ((nodes.drop 1).take 1)) (nodes.drop 2)) &&
    accepted store (composeClaims (nodes.take 1) (composeClaims ((nodes.drop 1).take 1) (nodes.drop 2)))

end Tests.Theory.Claims
