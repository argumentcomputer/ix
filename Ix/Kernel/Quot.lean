/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Quot.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Store

/-! # Canonical quotient declarations

The quotient computation rules are selected by declaration content rather
than ambient names.  This file records the exact anonymous kernel types of
`Eq`, `Quot`, `Quot.mk`, `Quot.lift`, and `Quot.ind`, parameterized by their
content-addressed references.
-/

namespace Ix.Kernel
namespace Store

/-- References used by the primitive quotient interface, including the
equality family appearing in the type of `Quot.lift`. -/
structure QuotRefs (β : Type u) where
  eq : ConstRef β
  type : ConstRef β
  ctor : ConstRef β
  lift : ConstRef β
  ind : ConstRef β
  deriving DecidableEq

/-- The two blocks whose contents make up the canonical equality and quotient
interface. -/
structure QuotBlocks (β : Type u) where
  equality : β
  quotient : β
  deriving DecidableEq

namespace QuotBlocks

/-- Positional references exposed by the canonical two-block layout. -/
def refs (blocks : QuotBlocks β) : QuotRefs β where
  eq := .member blocks.equality 0
  type := .member blocks.quotient 0
  ctor := .member blocks.quotient 1
  lift := .member blocks.quotient 2
  ind := .member blocks.quotient 3

end QuotBlocks

namespace Quotient

/-- Binary relation on the most recently bound sort. -/
def relationType : VExpr β :=
  .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))

/-- Exact kernel type of the equality family. -/
def eqType : VExpr β :=
  .forallE (.sort (.param 0))
    (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))

/-- Exact kernel type of the reflexivity constructor at `eq`. -/
def eqCtorType (eq : ConstRef β) : VExpr β :=
  .forallE (.sort (.param 0))
    (.forallE (.bvar 0)
      (VExpr.appN (.const eq [.param 0]) [.bvar 1, .bvar 0, .bvar 0]))

/-- Canonical equality-family member, including its nested reflexivity
constructor. -/
def eqConstant (eq : ConstRef β) : Const β :=
  .induct 1 2 1 eqType
    [{
      uvars := 1
      nparams := 2
      nfields := 0
      type := eqCtorType eq
      safety := .safe
    }]
    .safe

/-- Canonical one-member equality block at `block`. -/
def eqBlock (block : β) : Block β :=
  { members := [eqConstant (.member block 0)] }

/-- Exact kernel type of the quotient family. -/
def typeType : VExpr β :=
  .forallE (.sort (.param 0))
    (.forallE relationType (.sort (.param 0)))

/-- Exact kernel type of the quotient constructor. -/
def ctorType (refs : QuotRefs β) : VExpr β :=
  .forallE (.sort (.param 0))
    (.forallE relationType
      (.forallE (.bvar 1)
        (VExpr.appN (.const refs.type [.param 0]) [.bvar 2, .bvar 1])))

/-- Exact kernel type of quotient lifting. -/
def liftType (refs : QuotRefs β) : VExpr β :=
  .forallE (.sort (.param 0))
    (.forallE relationType
      (.forallE (.sort (.param 1))
        (.forallE (.forallE (.bvar 2) (.bvar 1))
          (.forallE
            (.forallE (.bvar 3)
              (.forallE (.bvar 4)
                (.forallE
                  (VExpr.appN (.bvar 4) [.bvar 1, .bvar 0])
                  (VExpr.appN (.const refs.eq [.param 1])
                    [.bvar 4, .app (.bvar 3) (.bvar 2),
                      .app (.bvar 3) (.bvar 1)]))))
            (.forallE
              (VExpr.appN (.const refs.type [.param 0]) [.bvar 4, .bvar 3])
              (.bvar 3))))))

/-- Exact kernel type of quotient induction. -/
def indType (refs : QuotRefs β) : VExpr β :=
  .forallE (.sort (.param 0))
    (.forallE relationType
      (.forallE
        (.forallE
          (VExpr.appN (.const refs.type [.param 0]) [.bvar 1, .bvar 0])
          (.sort .zero))
        (.forallE
          (.forallE (.bvar 2)
            (.app (.bvar 1)
              (VExpr.appN (.const refs.ctor [.param 0])
                [.bvar 3, .bvar 2, .bvar 0])))
          (.forallE
            (VExpr.appN (.const refs.type [.param 0]) [.bvar 3, .bvar 2])
            (.app (.bvar 2) (.bvar 0))))))

def typeConstant (_refs : QuotRefs β) : Const β :=
  .quot .type 1 typeType

def ctorConstant (refs : QuotRefs β) : Const β :=
  .quot .ctor 1 (ctorType refs)

def liftConstant (refs : QuotRefs β) : Const β :=
  .quot .lift 2 (liftType refs)

def indConstant (refs : QuotRefs β) : Const β :=
  .quot .ind 1 (indType refs)

/-- Canonical four-member quotient block at the selected block addresses. -/
def quotBlock (blocks : QuotBlocks β) : Block β :=
  let refs := blocks.refs
  { members := [typeConstant refs, ctorConstant refs,
      liftConstant refs, indConstant refs] }

/-- The canonical quotient block is syntactically closed. -/
theorem quotBlock_closed (blocks : QuotBlocks β) :
    (quotBlock blocks).Closed := by
  simp [Block.Closed, quotBlock, typeConstant, ctorConstant, liftConstant,
    indConstant, Const.Closed, typeType, ctorType, liftType, indType,
    relationType, VExpr.appN, VExpr.Closed, VExpr.ClosedN]

/-- Canonical quotient blocks contain no nested inductive-family members. -/
theorem quotBlock_no_inductive {blocks : QuotBlocks β} {member uvars
    nparams nindices : Nat} {type : VExpr β} {ctors : List (Ctor β)}
    {safety : Safety}
    (found : (quotBlock blocks).members[member]? = some
      (.induct uvars nparams nindices type ctors safety)) : False := by
  cases member with
  | zero => simp [quotBlock, typeConstant] at found
  | succ member =>
      cases member with
      | zero => simp [quotBlock, ctorConstant] at found
      | succ member =>
          cases member with
          | zero => simp [quotBlock, liftConstant] at found
          | succ member =>
              cases member with
              | zero => simp [quotBlock, indConstant] at found
              | succ member => simp [quotBlock] at found

end Quotient

/-- Exact content certificate for the canonical equality and quotient blocks. -/
structure QuotBlocksCanonical (store : Store β)
    (blocks : QuotBlocks β) : Prop where
  equality : store.blocks blocks.equality =
    some (Quotient.eqBlock blocks.equality)
  quotient : store.blocks blocks.quotient =
    some (Quotient.quotBlock blocks)

/-- Exact canonical block content is stable under store inclusion. -/
theorem QuotBlocksCanonical.mono {left right : Store β}
    (subset : left ⊆ right) {blocks : QuotBlocks β}
    (canonical : left.QuotBlocksCanonical blocks) :
    right.QuotBlocksCanonical blocks where
  equality := subset _ _ canonical.equality
  quotient := subset _ _ canonical.quotient

/-- The exact declarations selected by the primitive quotient rules. -/
structure QuotReady (store : Store β) (refs : QuotRefs β) : Prop where
  eq : store.lookup refs.eq = some (Quotient.eqConstant refs.eq)
  type : store.lookup refs.type = some (Quotient.typeConstant refs)
  ctor : store.lookup refs.ctor = some (Quotient.ctorConstant refs)
  lift : store.lookup refs.lift = some (Quotient.liftConstant refs)
  ind : store.lookup refs.ind = some (Quotient.indConstant refs)

/-- Discover the unique canonical equality block by content. -/
def eqBlock? [DecidableEq β] (store : Store β) : Option β :=
  match store.dom.filter fun block =>
      store.blocks block == some (Quotient.eqBlock block) with
  | [block] => some block
  | _ => none

/-- Discover the unique canonical quotient block relative to `equality`. -/
def quotBlock? [DecidableEq β] (store : Store β)
    (equality : β) : Option β :=
  match store.dom.filter fun quotient =>
      let blocks : QuotBlocks β := { equality, quotient }
      store.blocks quotient == some (Quotient.quotBlock blocks) with
  | [block] => some block
  | _ => none

/-- Discover both uniquely designated blocks of the quotient interface. -/
def quotBlocks? [DecidableEq β] (store : Store β) : Option (QuotBlocks β) := do
  let equality ← store.eqBlock?
  let quotient ← store.quotBlock? equality
  pure { equality, quotient }

/-- Exact canonical block content exposes the rule-facing declaration
inventory. -/
theorem QuotBlocksCanonical.ready [DecidableEq β] {store : Store β}
    {blocks : QuotBlocks β} (canonical : store.QuotBlocksCanonical blocks) :
    store.QuotReady blocks.refs := by
  constructor
  · simp [Store.lookup, QuotBlocks.refs, Quotient.eqBlock,
      canonical.equality]
  · simp [Store.lookup, QuotBlocks.refs, Quotient.quotBlock,
      canonical.quotient]
  · simp [Store.lookup, QuotBlocks.refs, Quotient.quotBlock,
      canonical.quotient]
  · simp [Store.lookup, QuotBlocks.refs, Quotient.quotBlock,
      canonical.quotient]
  · simp [Store.lookup, QuotBlocks.refs, Quotient.quotBlock,
      canonical.quotient]

end Store
end Ix.Kernel
