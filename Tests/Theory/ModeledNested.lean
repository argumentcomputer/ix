/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Theory.Modeled

open Ix.Theory

namespace Tests.Theory.ModeledNested

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certificate Ix.Theory.Inductive
open Tests.Theory.Certified (primitives)
open Tests.Theory.Modeled (ref const)

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def boxShape : Ix.Theory.Certified.Ordinary.Shape Nat :=
  ⟨1, [.sort (.succ (.param 0))], [], .succ (.param 0), [⟨[.bvar 0], [], []⟩]⟩

def unaryShape (recursivePi : Bool) : Ix.Theory.Certified.Ordinary.Shape Nat :=
  ⟨1, [.sort (.succ (.param 0))], [], .succ (.param 0),
    [⟨[.bvar 0], [], []⟩, ⟨[], [⟨if recursivePi then [.bvar 0] else [], []⟩], []⟩]⟩

def tree (level : VLevel) (parameter : VExpr Nat) : VExpr Nat := .app (const 40 0 [level]) parameter
def box (level : VLevel) (parameter : VExpr Nat) : VExpr Nat := .app (const 20 0 [level]) parameter
def unary (level : VLevel) (parameter : VExpr Nat) : VExpr Nat := .app (const 30 0 [level]) parameter
def branch (recursivePi : Bool) (parameter family : VExpr Nat) : VExpr Nat :=
  if recursivePi then .forallE parameter (family.liftN 1) else family

def boxMk (level : VLevel) (parameter value : VExpr Nat) : VExpr Nat :=
  .appN (.const (.ctor 20 0 0) [level]) [parameter, value]

/-- Tree α = leaf α | node (Box (Tree α)), or node (Box (α → Tree α)).
Both are parameterized nested occurrences with a restored Box recursor. -/
def treeSource (recursivePi : Bool) : Const Nat := .induct 1 1 0
  (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) [
  ⟨1, 1, 1, .forallE (.sort (.succ (.param 0)))
    (.forallE (.bvar 0) (tree (.param 0) (.bvar 1))), .safe⟩,
  ⟨1, 1, 1, .forallE (.sort (.succ (.param 0)))
    (.forallE (box (.param 0) (branch recursivePi (.bvar 0) (tree (.param 0) (.bvar 0)))) (tree (.param 0) (.bvar 1))), .safe⟩] .safe

def sourceBlock (recursivePi : Bool) : Nat → Block Nat
  | 10 => ⟨[PrimitiveSignature.falseDeclaration]⟩
  | 11 => ⟨[primitives.falseElimDeclaration]⟩
  | 20 => ⟨[boxShape.source 20]⟩
  | 21 => ⟨[boxShape.recursorSource 20 21 .large]⟩
  | 30 => ⟨[(unaryShape recursivePi).source 30]⟩
  | 31 => ⟨[(unaryShape recursivePi).recursorSource 30 31 .large]⟩
  | 40 => ⟨[treeSource recursivePi]⟩
  | _ => ⟨[]⟩

def storeFor (blocks : Nat → Block Nat) : Store Nat where
  dom := List.range 53
  nodup := List.nodup_range
  blocks b := if b < 53 then some (blocks b) else none
  mem_dom b := by split <;> simp_all

def sourceStore (recursivePi : Bool) : Store Nat := storeFor (sourceBlock recursivePi)
def treeRecursors (recursivePi : Bool) : Block Nat :=
  if recursivePi then ModeledFixtures.nestedPiRecursors else ModeledFixtures.nestedRecursors

def modelTargets : List (ConstRef Nat) := [ref 30, .ctor 30 0 0, ref 50, ref 51, ref 52]
def modelPairs : List (ConstRef Nat × ConstRef Nat) :=
  [ref 40, .ctor 40 0 0, .ctor 40 0 1, ref 41, ref 41 1].zip modelTargets
def mapped (expression : VExpr Nat) : VExpr Nat := expression.mapRefs (Certificate.Modeled.target modelPairs)
def recursorType (recursivePi : Bool) (index : Nat) : VExpr Nat :=
  mapped (((treeRecursors recursivePi).members[index]?).map Const.type |>.getD (.sort .zero))
def recPrefix (recursivePi : Bool) : List (VExpr Nat) := (recursorType recursivePi 0).telN 6

def nodeType (recursivePi : Bool) : VExpr Nat :=
  match treeSource recursivePi with
  | .induct _ _ _ _ ctors _ => mapped ((ctors[1]?).map Ctor.type |>.getD (.sort .zero))
  | _ => .sort .zero
def nodeBody (recursivePi : Bool) : VExpr Nat := .lam (.sort (.succ (.param 0)))
  (.lam (box (.param 0) (branch recursivePi (.bvar 0) (unary (.param 0) (.bvar 0))))
    (.appN (.const (.ctor 30 0 1) [.param 0]) [.bvar 1, .proj (ref 20) 0 (.bvar 0)]))

/-- Ordinary unary recursion supplies both nested calls. The constructor
and auxiliary recursor use Box's independently checked projection and eta. -/
def treeModel (recursivePi : Bool) : VExpr Nat := .lamN (recPrefix recursivePi)
  (.appN (const 31 0 [.param 0, .param 1]) [
    .bvar 5, .bvar 4, .bvar 2,
    .lam (branch recursivePi (.bvar 5) (unary (.param 1) (.bvar 5)))
      (.lam (if recursivePi then .forallE (.bvar 6) (.app (.bvar 6) (.app (.bvar 1) (.bvar 0)))
          else .app (.bvar 5) (.bvar 0))
        (.appN (.bvar 3) [boxMk (.param 1) (branch recursivePi (.bvar 7) (unary (.param 1) (.bvar 7))) (.bvar 1),
          .appN (.bvar 2) [.bvar 1, .bvar 0]]))])

def boxModel (recursivePi : Bool) : VExpr Nat := .lamN (recPrefix recursivePi)
  (.appN (const 21 0 [.param 0, .param 1]) [
    branch recursivePi (.bvar 5) (unary (.param 1) (.bvar 5)), .bvar 3,
    .lam (branch recursivePi (.bvar 5) (unary (.param 1) (.bvar 5)))
      (.appN (.bvar 1) [.bvar 0,
        if recursivePi then .lam (.bvar 6)
          (.appN (const 51 0 [.param 0, .param 1]) (VExpr.bvarRevRange 2 6 ++ [.app (.bvar 1) (.bvar 0)]))
        else .appN (const 51 0 [.param 0, .param 1]) (VExpr.bvarRevRange 1 6 ++ [.bvar 0])])])

def block (recursivePi : Bool) : Nat → Block Nat
  | 41 => treeRecursors recursivePi
  | 50 => ⟨[.defn 1 .definition (nodeType recursivePi) (nodeBody recursivePi) .safe]⟩
  | 51 => ⟨[.defn 2 .definition (recursorType recursivePi 0) (treeModel recursivePi) .safe]⟩
  | 52 => ⟨[.defn 2 .definition (recursorType recursivePi 1) (boxModel recursivePi) .safe]⟩
  | n => sourceBlock recursivePi n
def store (recursivePi : Bool) : Store Nat := storeFor (block recursivePi)
def candidate : Certificate.Modeled.Candidate Nat := ⟨40, [ref 41, ref 41 1], modelTargets, []⟩

def prefixWitnesses? (recursivePi : Bool) : Option (Environment Nat × List (DeclarationWitness Nat)) :=
  declarationWitnesses? 4000 (store recursivePi) primitives.environment
    [.ordinary 20 21, .ordinary 30 31, .definition (ref 50), .definition (ref 51), .definition (ref 52)]
def modeledWitness? (recursivePi : Bool) : Option (Ix.Theory.Certified.Modeled.Witness Nat) := do
  let (entries, _) ← prefixWitnesses? recursivePi
  candidate.witness? 4000 entries (store recursivePi)
def generated? (recursivePi : Bool) : Option (List (DeclarationWitness Nat)) :=
  Certificate.storeWitness? 4000 primitives (store recursivePi) [ref 41, ref 41 1] [candidate]
def accepted (recursivePi : Bool) : Bool := (generated? recursivePi).any
  (acceptsStoreCertified.{0,0} 4000 primitives (store recursivePi) [ref 40, ref 41, ref 41 1])

#guard [false, true].all fun recursivePi => (treeRecursors recursivePi).members.length == 2
#guard [false, true].all fun recursivePi =>
  (Ix.Theory.Certified.Modeled.sourceRefs? (store recursivePi) 40 [ref 41, ref 41 1]).isSome
#guard [false, true].all fun recursivePi =>
  (Ix.Theory.Certified.Modeled.recursorRules? (store recursivePi) (ref 41)).any (fun rules => rules.length == 2)
#guard [false, true].all fun recursivePi =>
  (Ix.Theory.Certified.Modeled.recursorRules? (store recursivePi) (ref 41 1)).any (fun rules => rules.length == 1)
#guard [false, true].all fun recursivePi => (prefixWitnesses? recursivePi).isSome
#guard [false, true].all fun recursivePi => (modeledWitness? recursivePi).isSome
#guard [false, true].all accepted

def computed (recursivePi : Bool) : VExpr Nat :=
  let treeType := tree .zero (.sort .zero)
  let fieldType := branch recursivePi (.sort .zero) treeType
  let boxType := box .zero fieldType
  let leaf := fun value => VExpr.appN (.const (.ctor 40 0 0) [.zero]) [.sort .zero, value]
  let field := if recursivePi then .lam (.sort .zero) (leaf (.bvar 0)) else leaf (.bvar 1)
  .appN (const 41 0 [.succ .zero, .zero]) [
    .sort .zero,
    .lam treeType (.sort .zero), .lam boxType (.sort .zero),
    .lam (.sort .zero) (.bvar 0),
    .lam boxType (.lam (.sort .zero) (.bvar 0)),
    .lam fieldType (.lam
      (if recursivePi then .forallE (.sort .zero) (.sort .zero) else .sort .zero)
      (if recursivePi then .app (.bvar 0) (.bvar 3) else .bvar 0)),
    .appN (.const (.ctor 40 0 1) [.zero]) [.sort .zero, boxMk .zero fieldType field]]

def input (recursivePi : Bool) : ProofInput Nat :=
  ⟨store recursivePi, 0, Tests.Theory.Modeled.proof,
    .forallE (.sort .zero) (.forallE (.bvar 0) (computed recursivePi))⟩
def proofAccepted (recursivePi : Bool) : Bool :=
  (Certificate.proofWitness? 4000 primitives (input recursivePi) [candidate]).any
    (acceptsCertified.{0,0} 4000 primitives (input recursivePi))

#guard [false, true].all proofAccepted

def tampered (recursivePi : Bool) (alter : Const Nat → Const Nat) : Store Nat :=
  storeFor fun n => if n = 41 then ⟨(treeRecursors recursivePi).members.map alter⟩ else block recursivePi n

def rejected (recursivePi : Bool) (source : Store Nat) : Bool := (generated? recursivePi).any fun witnesses =>
  !(acceptsStoreCertified.{0,0} 4000 primitives source [ref 41, ref 41 1] witnesses)

#guard [false, true].all fun recursivePi => rejected recursivePi (tampered recursivePi fun c => match c with
  | .recursor u p i m n t rs k s => .recursor u p i m n (t.instL [.param 1, .param 0]) rs k s
  | c => c)
#guard [false, true].all fun recursivePi => rejected recursivePi (tampered recursivePi fun c => match c with
  | .recursor u p i m n t rs k s => .recursor u p i m n t (rs.map fun r => { r with nfields := 0 }) k s
  | c => c)

-- Swapping the restored auxiliary with its root, or substituting its model
-- for the root's model, cannot preserve the actual selected rule statements.
#guard [false, true].all fun recursivePi => (prefixWitnesses? recursivePi).any fun (entries, _) =>
  (Certificate.Modeled.witness? 4000 entries (store recursivePi) 40 [ref 41 1, ref 41] modelTargets).isNone
#guard [false, true].all fun recursivePi => (prefixWitnesses? recursivePi).any fun (entries, _) =>
  (Certificate.Modeled.witness? 4000 entries (store recursivePi) 40 [ref 41, ref 41 1]
    [ref 30, .ctor 30 0 0, ref 50, ref 52, ref 51]).isNone

end Tests.Theory.ModeledNested
