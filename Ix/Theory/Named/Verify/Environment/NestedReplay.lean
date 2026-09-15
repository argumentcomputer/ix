/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Verify.Environment.SingletonParityReplay
import Ix.Theory.Named.Verify.Environment.NestedTransformation

/-!
# Nested environment replay

Both ladder fixtures replayed from real stored metadata: the rose tree
over the completed `List` environment and the nested-indexed family over
a staged `PVec` boundary.  Each inserts its stored constants through
`AddInductNestedTrace`, proves the `NestedBlockChecked.WF` package by
direct concrete typing derivations over the exact phase environments,
and drives the final map and environment through `TrEnv'.inductNested`,
with `Ordered` derived and the transitional closures guarded.
-/

namespace Ix.Theory.Named.NestedReplayFixtures

open Lean
open Ix.Theory.Named.InductiveReplayFixtures
open Ix.Theory.Named.NestedRepresentation
open Ix.Theory.Named.NestedInductiveFixtures
open VInductDecl

local instance : Inhabited VEnv := ⟨.empty⟩
local instance : Inhabited VConstVal := ⟨⟨⟨0, .sort .zero⟩, .anonymous⟩⟩

/-! ## The completed List replay as the input boundary -/

theorem listTrEnv07 : TrEnv' .safe listMap07 false listFinalEnv07 :=
  .induct listAddInduct07 .empty

theorem listFinalOrdered07 : listFinalEnv07.Ordered :=
  listTrEnv07.wf.ordered

/-! ## The translated rose source and its nested artifact -/

def roseSourceV : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := ``RoseTree
       uvars := 1
       type := nestedConstVType09A% RoseTree
       ctors :=
         [⟨⟨1, nestedConstVType09A% RoseTree.node⟩, ``RoseTree.node⟩] }]

def roseNestedC? : Option (NestedBlockChecked roseSourceV) :=
  nestedBlockChecked? [listTarget] roseSourceV

#guard roseNestedC?.isSome

def roseNestedC : NestedBlockChecked roseSourceV :=
  roseNestedC?.get (by native_decide)

/-! ## Stored metadata and phase maps/environments -/

def roseInfo09 : ConstantInfo := kernelInductInfo% RoseTree
def roseNodeInfo09 : ConstantInfo := kernelCtorInfo% RoseTree.node
def roseRecInfo09 : ConstantInfo := kernelRecInfo% RoseTree.rec
def roseRec1Info09 : ConstantInfo := kernelRecInfo% RoseTree.rec_1

def roseFamilyV : VConstVal := roseSourceV.types[0].toVConstVal
def roseNodeV : VConstVal := roseSourceV.types[0].ctors[0]
def roseRecV : VConstVal := roseNestedC.recursors[0]!
def roseRec1V : VConstVal := roseNestedC.recursors[1]!

#guard roseRecV.name == ``RoseTree.rec
#guard roseRec1V.name == `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1

def roseTypeMap09 : ConstMap := listMap07.insert ``RoseTree roseInfo09
def roseCtorMap09 : ConstMap := roseTypeMap09.insert ``RoseTree.node roseNodeInfo09
def roseRecMap09 : ConstMap := roseCtorMap09.insert ``RoseTree.rec roseRecInfo09
def roseMap09 : ConstMap :=
  roseRecMap09.insert `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1 roseRec1Info09

def roseTypeEnv09 : VEnv :=
  (listFinalEnv07.addConst roseFamilyV.name roseFamilyV.toVConstant).get!
def roseCtorEnv09 : VEnv :=
  (roseTypeEnv09.addConst roseNodeV.name roseNodeV.toVConstant).get!
-- the recursor and rule phase environments are defined below, over the
-- printed literal inventories


/-! ## Printed artifact literals

The restored recursor types and rule components, printed from the
computed artifact and tied back to it below; the concrete typing
derivations are stated over these literals. -/

/-- Printed image of `roseNestedC.recursors[0]!.type`. -/
def roseRecTypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.app (.bvar 5) (.bvar 0))))))))

def roseRec1TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const `List [.param 1])
                  (.app
                    (.const
                      `Ix.Theory.Named.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))
                (.app (.bvar 4) (.bvar 0))))))))

def roseRule0LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.bvar 5)
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree.rec
                                  [.param 0, .param 1])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.app
                      (.app
                        (.app
                          (.const
                            `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                            [.param 1])
                          (.bvar 7))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule0RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.bvar 5)
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app (.bvar 4) (.bvar 1))
                      (.bvar 0))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1
                                    [.param 0, .param 1])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 0))))))))))

def roseRule0TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.bvar 5)
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.bvar 6)
                    (.app
                      (.app
                        (.app
                          (.const
                            `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                            [.param 1])
                          (.bvar 7))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule1LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const
                              `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1
                              [.param 0, .param 1])
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.bvar 1))
                  (.bvar 0))
                (.app
                  (.const `List.nil [.param 1])
                  (.app
                    (.const
                      `Ix.Theory.Named.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))))))))

def roseRule1RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.bvar 1))))))

def roseRule1TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.app
                (.bvar 3)
                (.app
                  (.const `List.nil [.param 1])
                  (.app
                    (.const
                      `Ix.Theory.Named.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))))))))

def roseRule2LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1
                                  [.param 0, .param 1])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.app
                      (.app
                        (.app
                          (.const `List.cons [.param 1])
                          (.app
                            (.const
                              `Ix.Theory.Named.NestedRepresentation.RoseTree
                              [.param 1])
                            (.bvar 7)))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule2RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app (.bvar 2) (.bvar 1))
                        (.bvar 0))
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.app
                                    (.const
                                      `Ix.Theory.Named.NestedRepresentation.RoseTree.rec
                                      [.param 0, .param 1])
                                    (.bvar 7))
                                  (.bvar 6))
                                (.bvar 5))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1
                                    [.param 0, .param 1])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 0))))))))))

def roseRule2TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Ix.Theory.Named.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Ix.Theory.Named.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Ix.Theory.Named.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const
                    `Ix.Theory.Named.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Ix.Theory.Named.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.bvar 5)
                    (.app
                      (.app
                        (.app
                          (.const `List.cons [.param 1])
                          (.app
                            (.const
                              `Ix.Theory.Named.NestedRepresentation.RoseTree
                              [.param 1])
                            (.bvar 7)))
                        (.bvar 1))
                      (.bvar 0))))))))))

#guard roseRecV.type == roseRecTypeL
#guard roseRec1V.type == roseRec1TypeL
#guard roseNestedC.generatedRules.map (fun df => (df.uvars, df.lhs, df.rhs, df.type)) ==
  [(2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL),
   (2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL),
   (2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL)]
#guard roseRecV.uvars == 2 && roseRec1V.uvars == 2


/-! ## Literal inventories -/

def roseRecVL : VConstVal := ⟨⟨2, roseRecTypeL⟩, ``RoseTree.rec⟩
def roseRec1VL : VConstVal :=
  ⟨⟨2, roseRec1TypeL⟩, `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1⟩

def roseRulesL : List VDefEq :=
  [⟨2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL⟩,
   ⟨2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL⟩,
   ⟨2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL⟩]

theorem roseRecursors_eq : roseNestedC.recursors = [roseRecVL, roseRec1VL] := by
  native_decide

theorem roseRules_eq : roseNestedC.generatedRules = roseRulesL := by
  native_decide

def roseRecEnv09 : VEnv :=
  (roseCtorEnv09.addConst roseRecVL.name roseRecVL.toVConstant).get!
def roseRec1Env09 : VEnv :=
  (roseRecEnv09.addConst roseRec1VL.name roseRec1VL.toVConstant).get!
def roseFinalEnv09 : VEnv :=
  roseRulesL.foldl VEnv.addDefEq roseRec1Env09

/-! ## Concrete constant well-formedness -/

theorem roseFamilyWF09 : roseFamilyV.toVConstant.WF listFinalEnv07 :=
  ⟨_, by type_tac⟩

theorem roseTypeEnv09_eq :
    listFinalEnv07.addConst roseFamilyV.name roseFamilyV.toVConstant =
      some roseTypeEnv09 := rfl

theorem roseTypeOrdered09 : roseTypeEnv09.Ordered :=
  .const listFinalOrdered07 roseFamilyWF09 roseTypeEnv09_eq

theorem roseNodeWF09 : roseNodeV.toVConstant.WF roseTypeEnv09 := by
  have hList : roseTypeEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseTypeEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  exact ⟨_, by type_tac⟩


theorem roseCtorEnv09_eq :
    roseTypeEnv09.addConst roseNodeV.name roseNodeV.toVConstant =
      some roseCtorEnv09 := rfl

theorem roseCtorOrdered09 : roseCtorEnv09.Ordered :=
  .const roseTypeOrdered09 roseNodeWF09 roseCtorEnv09_eq

set_option maxRecDepth 4000 in
theorem roseRecWF09 : (⟨2, roseRecTypeL⟩ : VConstant).WF roseCtorEnv09 := by
  have hList : roseCtorEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseCtorEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseCtorEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseCtorEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseCtorEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  exact ⟨_, by type_tac⟩


theorem roseRecEnv09_eq :
    roseCtorEnv09.addConst roseRecVL.name roseRecVL.toVConstant =
      some roseRecEnv09 := rfl

theorem roseRecOrdered09 : roseRecEnv09.Ordered :=
  .const roseCtorOrdered09 roseRecWF09 roseRecEnv09_eq

set_option maxRecDepth 4000 in
theorem roseRec1WF09 : (⟨2, roseRec1TypeL⟩ : VConstant).WF roseRecEnv09 := by
  have hList : roseRecEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseRecEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseRecEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseRecEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseRecEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem roseRec1Env09_eq :
    roseRecEnv09.addConst roseRec1VL.name roseRec1VL.toVConstant =
      some roseRec1Env09 := rfl

theorem roseRec1Ordered09 : roseRec1Env09.Ordered :=
  .const roseRecOrdered09 roseRec1WF09 roseRec1Env09_eq


/-! ## Rule well-formedness at the rule-phase environment -/

section RuleWF

set_option maxRecDepth 8000

/-- The lookup hypotheses shared by every rule component derivation; the
environment argument is any `addDefEq` extension of `roseRec1Env09`, whose
constants agree definitionally. -/
macro "rose_rule_hyps" e:term : tactic => `(tactic| (
  have hList : VEnv.constants $e ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : VEnv.constants $e ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : VEnv.constants $e ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : VEnv.constants $e ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : VEnv.constants $e ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  have hRec : VEnv.constants $e ``RoseTree.rec =
      some ⟨2, roseRecTypeL⟩ := rfl
  have hRec1 : VEnv.constants $e
      `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1 =
      some ⟨2, roseRec1TypeL⟩ := rfl))

def roseRuleEnv1 : VEnv := roseRec1Env09.addDefEq roseRulesL[0]
def roseRuleEnv2 : VEnv := roseRuleEnv1.addDefEq roseRulesL[1]

theorem roseRule0WF09 : roseRulesL[0].WF roseRec1Env09 := by
  constructor
  · rose_rule_hyps roseRec1Env09; type_tac
  · rose_rule_hyps roseRec1Env09; type_tac

theorem roseRule1WF09 : roseRulesL[1].WF roseRuleEnv1 := by
  constructor
  · rose_rule_hyps roseRuleEnv1; type_tac
  · rose_rule_hyps roseRuleEnv1; type_tac

theorem roseRule2WF09 : roseRulesL[2].WF roseRuleEnv2 := by
  constructor
  · rose_rule_hyps roseRuleEnv2; type_tac
  · rose_rule_hyps roseRuleEnv2; type_tac

end RuleWF


/-! ## The semantic package -/

theorem roseTypesFold_eq :
    roseSourceV.blockTypeConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) listFinalEnv07 =
      some roseTypeEnv09 := rfl

theorem roseCtorsFold_eq :
    roseSourceV.blockConstructorConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) roseTypeEnv09 =
      some roseCtorEnv09 := rfl

theorem roseRecsFold_eq :
    roseNestedC.recursors.foldlM
      (fun env c => env.addConst c.name c.toVConstant) roseCtorEnv09 =
      some roseRec1Env09 := by
  rw [roseRecursors_eq]; rfl

theorem roseNestedWF09 : roseNestedC.WF listFinalEnv07 := by
  refine ⟨⟨roseFamilyWF09, fun env' h => ?_⟩, fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_, fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (roseTypeEnv09_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (roseTypesFold_eq.symm.trans h)
    exact ⟨roseNodeWF09, fun env' h' => by
      cases Option.some.inj (roseCtorEnv09_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (roseTypesFold_eq.symm.trans hT)
    cases Option.some.inj (roseCtorsFold_eq.symm.trans hC)
    rw [roseRecursors_eq]
    exact ⟨roseRecWF09, fun env' h' => by
      cases Option.some.inj (roseRecEnv09_eq.symm.trans h')
      exact ⟨roseRec1WF09, fun env'' h'' => by
        cases Option.some.inj (roseRec1Env09_eq.symm.trans h'')
        exact trivial⟩⟩
  · cases Option.some.inj (roseTypesFold_eq.symm.trans hT)
    cases Option.some.inj (roseCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (roseRecsFold_eq.symm.trans hR)
    rw [roseRules_eq]
    exact ⟨roseRule0WF09, roseRule1WF09, roseRule2WF09, trivial⟩


/-! ## Freshness of the stored insertions -/

theorem listMapWF07 : listMap07.WF :=
  listCtorMapWF07.insert _ _ listRecFresh07

theorem roseTypeFresh09 : listMap07.find? ``RoseTree = none := by
  rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseTypeMapWF09 : roseTypeMap09.WF :=
  listMapWF07.insert _ _ roseTypeFresh09

theorem roseNodeFresh09 : roseTypeMap09.find? ``RoseTree.node = none := by
  rw [roseTypeMap09, listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseCtorMapWF09 : roseCtorMap09.WF :=
  roseTypeMapWF09.insert _ _ roseNodeFresh09

theorem roseRecFresh09 : roseCtorMap09.find? ``RoseTree.rec = none := by
  rw [roseCtorMap09, roseTypeMapWF09.find?_insert, roseTypeMap09,
    listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseRecMapWF09 : roseRecMap09.WF :=
  roseCtorMapWF09.insert _ _ roseRecFresh09

theorem roseRec1Fresh09 :
    roseRecMap09.find? `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1 = none := by
  rw [roseRecMap09, roseCtorMapWF09.find?_insert, roseCtorMap09,
    roseTypeMapWF09.find?_insert, roseTypeMap09,
    listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-! ## Stored-metadata translations -/

theorem roseInfoTr09 :
    TrConstVal .safe listFinalEnv07 roseInfo09 roseFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr listFinalEnv07 roseInfo09.levelParams []
      roseInfo09.type roseFamilyV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS listFinalOrdered07 trivial ⟨_, by type_tac⟩

theorem roseNodeTr09 :
    TrConstVal .safe roseTypeEnv09 roseNodeInfo09 roseNodeV := by
  have hList : roseTypeEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseTypeEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseTypeEnv09 roseNodeInfo09.levelParams []
      roseNodeInfo09.type roseNodeV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS roseTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem roseRecTr09 :
    TrConstVal .safe roseCtorEnv09 roseRecInfo09 roseRecVL := by
  have hList : roseCtorEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseCtorEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseCtorEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseCtorEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseCtorEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseCtorEnv09 roseRecInfo09.levelParams []
      roseRecInfo09.type roseRecVL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := roseRecWF09
  exact shape.to_trExprS roseCtorOrdered09 trivial ⟨_, hty⟩

theorem roseRec1Tr09 :
    TrConstVal .safe roseRecEnv09 roseRec1Info09 roseRec1VL := by
  have hList : roseRecEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseRecEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseRecEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseRecEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseRecEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseRecEnv09 roseRec1Info09.levelParams []
      roseRec1Info09.type roseRec1VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := roseRec1WF09
  exact shape.to_trExprS roseRecOrdered09 trivial ⟨_, hty⟩


/-! ## Recursor K metadata and stored lookups -/

theorem roseKTarget09 : roseNestedC.generation.kTarget = false := by
  native_decide

theorem roseRecLookup09 :
    roseMap09.find? ``RoseTree.rec = some roseRecInfo09 := by
  rw [roseMap09, roseRecMapWF09.find?_insert]
  simp [roseRecMap09, roseCtorMapWF09.find?_insert]

theorem roseRec1Lookup09 :
    roseMap09.find? `Ix.Theory.Named.NestedRepresentation.RoseTree.rec_1 =
      some roseRec1Info09 := by
  rw [roseMap09, roseRecMapWF09.find?_insert]
  simp

theorem roseRecK09 :
    RecursorMapKMatches roseMap09 roseNestedC.recursors
      roseNestedC.generation.kTarget := by
  rw [roseRecursors_eq, roseKTarget09]
  intro recursor hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨roseRecInfo09, roseRecLookup09, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨roseRec1Info09, roseRec1Lookup09, by decide⟩
  · cases hmem

/-! ## The nested alignment trace and its `TrEnv'` drive -/

def roseTrace09 :
    AddInductNestedTrace listMap07 listFinalEnv07 roseSourceV
      roseMap09 roseFinalEnv09 where
  nested := roseNestedC
  nested_wf := roseNestedWF09
  typeMap := roseTypeMap09
  typeEnv := roseTypeEnv09
  ctorMap := roseCtorMap09
  ctorEnv := roseCtorEnv09
  recEnv := roseRec1Env09
  addTypes := .cons
    { info := roseInfo09
      kind_eq := trivial
      tr := roseInfoTr09
      map_fresh := roseTypeFresh09
      env_add := roseTypeEnv09_eq
      map_add := rfl } .nil
  addCtors := .cons
    { info := roseNodeInfo09
      kind_eq := trivial
      tr := roseNodeTr09
      map_fresh := roseNodeFresh09
      env_add := roseCtorEnv09_eq
      map_add := rfl } .nil
  addRecs := roseRecursors_eq ▸ .cons
    { info := roseRecInfo09
      kind_eq := trivial
      tr := roseRecTr09
      map_fresh := roseRecFresh09
      env_add := roseRecEnv09_eq
      map_add := rfl } (.cons
    { info := roseRec1Info09
      kind_eq := trivial
      tr := roseRec1Tr09
      map_fresh := roseRec1Fresh09
      env_add := roseRec1Env09_eq
      map_add := rfl } .nil)
  recK := roseRecK09
  addRules := ⟨by rw [roseRules_eq]; rfl⟩

theorem roseAddInductNested09 :
    AddInductNested listMap07 listFinalEnv07 roseSourceV
      roseMap09 roseFinalEnv09 :=
  ⟨roseTrace09⟩

/-- The rose-tree nested declaration, replayed from real stored metadata
over the completed `List` environment through the nested alignment
constructor. -/
theorem roseTrEnv09 : TrEnv' .safe roseMap09 false roseFinalEnv09 :=
  .inductNested roseAddInductNested09 listTrEnv07

theorem roseFinalOrdered09 : roseFinalEnv09.Ordered :=
  roseTrEnv09.wf.ordered


/-! ## Round-trip guards

The stored-metadata surface inserted by the trace is tied to the Theory
artifact inventory, and the final map/environment pair carries the
documented closure (persistent-map contracts plus the compiler-trust axioms
introduced by the `native_decide` observations). -/

#guard roseNestedC.elim.numNested == 1
#guard roseRecV == roseRecVL && roseRec1V == roseRec1VL

#guard_named_axioms Ix.Theory.Named.NestedReplayFixtures.roseTrEnv09 [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert,
  Ix.Theory.Named.NestedReplayFixtures.roseKTarget09._native.native_decide.ax_1_1,
  Ix.Theory.Named.NestedReplayFixtures.roseNestedC._native.native_decide.ax_1,
  Ix.Theory.Named.NestedReplayFixtures.roseRecursors_eq._native.native_decide.ax_1_1,
  Ix.Theory.Named.NestedReplayFixtures.roseRules_eq._native.native_decide.ax_1_1]

#guard_named_axioms Ix.Theory.Named.NestedReplayFixtures.roseNestedWF09 [
  propext,
  Classical.choice,
  Quot.sound,
  Ix.Theory.Named.NestedReplayFixtures.roseNestedC._native.native_decide.ax_1,
  Ix.Theory.Named.NestedReplayFixtures.roseRecursors_eq._native.native_decide.ax_1_1,
  Ix.Theory.Named.NestedReplayFixtures.roseRules_eq._native.native_decide.ax_1_1]


/-! # The nested-indexed fixture

`NVTree` nests through the locally declared indexed `PVec`.  The base
environment stages the `PVec` family and constructors over the completed
`Nat` replay through `TrEnv'.inductStaging`; the nested trace then inserts
the stored `NVTree` metadata and drives `TrEnv'.inductNested`. -/

/-! ## Staged `PVec` base -/

def pvecInfo09 : ConstantInfo := kernelInductInfo% PVec
def pvecNilInfo09 : ConstantInfo := kernelCtorInfo% PVec.nil
def pvecConsInfo09 : ConstantInfo := kernelCtorInfo% PVec.cons

def pvecFamilyVL : VConstVal :=
  ⟨⟨0, .forallE (.sort (.succ .zero))
    (.forallE (.const `Nat []) (.sort (.succ .zero)))⟩, ``PVec⟩
def pvecNilVL : VConstVal := ⟨⟨0, nestedConstVType09A% PVec.nil⟩, ``PVec.nil⟩
def pvecConsVL : VConstVal := ⟨⟨0, nestedConstVType09A% PVec.cons⟩, ``PVec.cons⟩

def pvecTypeMap09 : ConstMap := natMap.insert ``PVec pvecInfo09
def pvecNilMap09 : ConstMap := pvecTypeMap09.insert ``PVec.nil pvecNilInfo09
def pvecCtorMap09 : ConstMap := pvecNilMap09.insert ``PVec.cons pvecConsInfo09

def pvecTypeEnv09 : VEnv :=
  (natFinalEnv.addConst pvecFamilyVL.name pvecFamilyVL.toVConstant).get!
def pvecNilEnv09 : VEnv :=
  (pvecTypeEnv09.addConst pvecNilVL.name pvecNilVL.toVConstant).get!
def pvecCtorEnv09 : VEnv :=
  (pvecNilEnv09.addConst pvecConsVL.name pvecConsVL.toVConstant).get!

theorem pvecTypeFresh09 : natMap.find? ``PVec = none := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem pvecTypeMapWF09 : pvecTypeMap09.WF :=
  natMap_wf.insert _ _ pvecTypeFresh09

theorem pvecNilFresh09 : pvecTypeMap09.find? ``PVec.nil = none := by
  rw [pvecTypeMap09, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem pvecNilMapWF09 : pvecNilMap09.WF :=
  pvecTypeMapWF09.insert _ _ pvecNilFresh09

theorem pvecConsFresh09 : pvecNilMap09.find? ``PVec.cons = none := by
  rw [pvecNilMap09, pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem pvecCtorMapWF09 : pvecCtorMap09.WF :=
  pvecNilMapWF09.insert _ _ pvecConsFresh09

theorem natFinalOrdered09 : natFinalEnv.Ordered :=
  (nat_trEnv' (safety := .safe)).wf.ordered

theorem pvecFamilyWF09 : pvecFamilyVL.toVConstant.WF natFinalEnv := by
  have hNat : natFinalEnv.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem pvecTypeEnv09_eq :
    natFinalEnv.addConst pvecFamilyVL.name pvecFamilyVL.toVConstant =
      some pvecTypeEnv09 := rfl

theorem pvecTypeOrdered09 : pvecTypeEnv09.Ordered :=
  .const natFinalOrdered09 pvecFamilyWF09 pvecTypeEnv09_eq

theorem pvecNilWF09 : pvecNilVL.toVConstant.WF pvecTypeEnv09 := by
  have hNat : pvecTypeEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hZero : pvecTypeEnv09.constants ``Nat.zero = some ⟨0, .const `Nat []⟩ := rfl
  have hPVec : pvecTypeEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem pvecNilEnv09_eq :
    pvecTypeEnv09.addConst pvecNilVL.name pvecNilVL.toVConstant =
      some pvecNilEnv09 := rfl

theorem pvecNilOrdered09 : pvecNilEnv09.Ordered :=
  .const pvecTypeOrdered09 pvecNilWF09 pvecNilEnv09_eq

theorem pvecConsWF09 : pvecConsVL.toVConstant.WF pvecNilEnv09 := by
  have hNat : pvecNilEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hSucc : pvecNilEnv09.constants ``Nat.succ =
      some ⟨0, .forallE (.const `Nat []) (.const `Nat [])⟩ := rfl
  have hPVec : pvecNilEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem pvecConsEnv09_eq :
    pvecNilEnv09.addConst pvecConsVL.name pvecConsVL.toVConstant =
      some pvecCtorEnv09 := rfl

theorem pvecCtorOrdered09 : pvecCtorEnv09.Ordered :=
  .const pvecNilOrdered09 pvecConsWF09 pvecConsEnv09_eq

theorem pvecInfoTr09 : TrConstVal .safe natFinalEnv pvecInfo09 pvecFamilyVL := by
  have hNat : natFinalEnv.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr natFinalEnv pvecInfo09.levelParams []
      pvecInfo09.type pvecFamilyVL.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS natFinalOrdered09 trivial ⟨_, by type_tac⟩

theorem pvecNilTr09 : TrConstVal .safe pvecTypeEnv09 pvecNilInfo09 pvecNilVL := by
  have hNat : pvecTypeEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hZero : pvecTypeEnv09.constants ``Nat.zero = some ⟨0, .const `Nat []⟩ := rfl
  have hPVec : pvecTypeEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr pvecTypeEnv09 pvecNilInfo09.levelParams []
      pvecNilInfo09.type pvecNilVL.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS pvecTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem pvecConsTr09 : TrConstVal .safe pvecNilEnv09 pvecConsInfo09 pvecConsVL := by
  have hNat : pvecNilEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hSucc : pvecNilEnv09.constants ``Nat.succ =
      some ⟨0, .forallE (.const `Nat []) (.const `Nat [])⟩ := rfl
  have hPVec : pvecNilEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr pvecNilEnv09 pvecConsInfo09.levelParams []
      pvecConsInfo09.type pvecConsVL.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS pvecNilOrdered09 trivial ⟨_, by type_tac⟩

/-- The staged `PVec` boundary: family and constructors present, no
recursor or rules — exactly the constants the nested `NVTree` artifacts
reference. -/
theorem pvecTrEnv09 : TrEnv' .safe pvecCtorMap09 false pvecCtorEnv09 :=
  .inductStaging (kind := .ctor)
    { info := pvecConsInfo09
      kind_eq := trivial
      tr := pvecConsTr09
      map_fresh := pvecConsFresh09
      env_add := pvecConsEnv09_eq
      map_add := rfl } pvecConsWF09 <|
  .inductStaging (kind := .ctor)
    { info := pvecNilInfo09
      kind_eq := trivial
      tr := pvecNilTr09
      map_fresh := pvecNilFresh09
      env_add := pvecNilEnv09_eq
      map_add := rfl } pvecNilWF09 <|
  .inductStaging (kind := .induct)
    { info := pvecInfo09
      kind_eq := trivial
      tr := pvecInfoTr09
      map_fresh := pvecTypeFresh09
      env_add := pvecTypeEnv09_eq
      map_add := rfl } pvecFamilyWF09 nat_trEnv'


/-! ## The translated NV source and its nested artifact -/

def nvSourceV : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := ``NVTree
       uvars := 0
       type := nestedConstVType09A% NVTree
       ctors := [⟨⟨0, nestedConstVType09A% NVTree.node⟩, ``NVTree.node⟩] }]

def nvNestedC? : Option (NestedBlockChecked nvSourceV) :=
  nestedBlockChecked? [NestedTransformation.pvecStoredTarget] nvSourceV

#guard nvNestedC?.isSome

def nvNestedC : NestedBlockChecked nvSourceV :=
  nvNestedC?.get (by native_decide)

def nvInfo09 : ConstantInfo := kernelInductInfo% NVTree
def nvNodeInfo09 : ConstantInfo := kernelCtorInfo% NVTree.node
def nvRecInfo09 : ConstantInfo := kernelRecInfo% NVTree.rec
def nvRec1Info09 : ConstantInfo := kernelRecInfo% NVTree.rec_1

def nvFamilyV : VConstVal := nvSourceV.types[0].toVConstVal
def nvNodeV : VConstVal := nvSourceV.types[0].ctors[0]

def nvTypeMap09 : ConstMap := pvecCtorMap09.insert ``NVTree nvInfo09
def nvCtorMap09 : ConstMap := nvTypeMap09.insert ``NVTree.node nvNodeInfo09
def nvRecMap09 : ConstMap := nvCtorMap09.insert ``NVTree.rec nvRecInfo09
def nvMap09 : ConstMap :=
  nvRecMap09.insert `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1 nvRec1Info09

def nvTypeEnv09 : VEnv :=
  (pvecCtorEnv09.addConst nvFamilyV.name nvFamilyV.toVConstant).get!
def nvCtorEnv09 : VEnv :=
  (nvTypeEnv09.addConst nvNodeV.name nvNodeV.toVConstant).get!

def nvFamilyTypeL : VExpr :=
  .sort (.succ (.zero))

def nvNodeTypeL : VExpr :=
  .forallE
    (.const `Nat [])
    (.forallE
      (.app
        (.app
          (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
          (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
        (.bvar 0))
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))

def nvRecTypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.app (.bvar 5) (.bvar 0)))))))

def nvRec1TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Nat [])
              (.forallE
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.app (.bvar 5) (.bvar 1))
                  (.bvar 0))))))))

def nvRule0LhsL : VExpr :=
  .lam
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Nat [])
              (.lam
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const
                              `Ix.Theory.Named.NestedRepresentation.NVTree.rec
                              [.param 0])
                            (.bvar 6))
                          (.bvar 5))
                        (.bvar 4))
                      (.bvar 3))
                    (.bvar 2))
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                      (.bvar 1))
                    (.bvar 0)))))))))

def nvRule0RhsL : VExpr :=
  .lam
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Nat [])
              (.lam
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.app
                    (.app (.bvar 4) (.bvar 1))
                    (.bvar 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1
                                  [.param 0])
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 1))
                    (.bvar 0)))))))))

def nvRule0TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Nat [])
              (.forallE
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.bvar 6)
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                      (.bvar 1))
                    (.bvar 0)))))))))

def nvRule1LhsL : VExpr :=
  .lam
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.app
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.const
                            `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1
                            [.param 0])
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.bvar 1))
                  (.bvar 0))
                (.const `Nat.zero []))
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))))))

def nvRule1RhsL : VExpr :=
  .lam
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.bvar 1)))))

def nvRule1TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.app
              (.app (.bvar 3) (.const `Nat.zero []))
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))))))

def nvRule2LhsL : VExpr :=
  .lam
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.lam
                (.const `Nat [])
                (.lam
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1
                                  [.param 0])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.app
                        (.const `Nat.succ [])
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const `Ix.Theory.Named.NestedRepresentation.PVec.cons [])
                            (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                          (.bvar 2))
                        (.bvar 1))
                      (.bvar 0))))))))))

def nvRule2RhsL : VExpr :=
  .lam
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.lam
                (.const `Nat [])
                (.lam
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app (.bvar 3) (.bvar 2))
                          (.bvar 1))
                        (.bvar 0))
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Ix.Theory.Named.NestedRepresentation.NVTree.rec
                                    [.param 0])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1
                                    [.param 0])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 1))
                      (.bvar 0))))))))))

def nvRule2TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Ix.Theory.Named.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Ix.Theory.Named.NestedRepresentation.PVec.nil [])
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Ix.Theory.Named.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Ix.Theory.Named.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Ix.Theory.Named.NestedRepresentation.PVec [])
                      (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.app
                    (.app
                      (.bvar 6)
                      (.app
                        (.const `Nat.succ [])
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const `Ix.Theory.Named.NestedRepresentation.PVec.cons [])
                            (.const `Ix.Theory.Named.NestedRepresentation.NVTree []))
                          (.bvar 2))
                        (.bvar 1))
                      (.bvar 0))))))))))

def nvRecVL : VConstVal := ⟨⟨1, nvRecTypeL⟩, ``NVTree.rec⟩
def nvRec1VL : VConstVal :=
  ⟨⟨1, nvRec1TypeL⟩, `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1⟩

def nvRulesL : List VDefEq :=
  [⟨1, nvRule0LhsL, nvRule0RhsL, nvRule0TypeL⟩,
   ⟨1, nvRule1LhsL, nvRule1RhsL, nvRule1TypeL⟩,
   ⟨1, nvRule2LhsL, nvRule2RhsL, nvRule2TypeL⟩]

theorem nvRecursors_eq : nvNestedC.recursors = [nvRecVL, nvRec1VL] := by
  native_decide

theorem nvRules_eq : nvNestedC.generatedRules = nvRulesL := by
  native_decide

def nvRecEnv09 : VEnv :=
  (nvCtorEnv09.addConst nvRecVL.name nvRecVL.toVConstant).get!
def nvRec1Env09 : VEnv :=
  (nvRecEnv09.addConst nvRec1VL.name nvRec1VL.toVConstant).get!
def nvFinalEnv09 : VEnv :=
  nvRulesL.foldl VEnv.addDefEq nvRec1Env09


/-! ## NV constant well-formedness and phase chains -/

macro "nv_hyps" e:term : tactic => `(tactic| (
  have hNat : VEnv.constants $e ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hZero : VEnv.constants $e ``Nat.zero = some ⟨0, .const `Nat []⟩ := rfl
  have hSucc : VEnv.constants $e ``Nat.succ =
      some ⟨0, .forallE (.const `Nat []) (.const `Nat [])⟩ := rfl
  have hPVec : VEnv.constants $e ``PVec = some pvecFamilyVL.toVConstant := rfl
  have hPNil : VEnv.constants $e ``PVec.nil = some pvecNilVL.toVConstant := rfl
  have hPCons : VEnv.constants $e ``PVec.cons = some pvecConsVL.toVConstant := rfl))

theorem nvFamilyWF09 : nvFamilyV.toVConstant.WF pvecCtorEnv09 :=
  ⟨_, by type_tac⟩

theorem nvTypeEnv09_eq :
    pvecCtorEnv09.addConst nvFamilyV.name nvFamilyV.toVConstant =
      some nvTypeEnv09 := rfl

theorem nvTypeOrdered09 : nvTypeEnv09.Ordered :=
  .const pvecCtorOrdered09 nvFamilyWF09 nvTypeEnv09_eq

theorem nvNodeWF09 : nvNodeV.toVConstant.WF nvTypeEnv09 := by
  nv_hyps nvTypeEnv09
  have hNV : nvTypeEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem nvCtorEnv09_eq :
    nvTypeEnv09.addConst nvNodeV.name nvNodeV.toVConstant =
      some nvCtorEnv09 := rfl

theorem nvCtorOrdered09 : nvCtorEnv09.Ordered :=
  .const nvTypeOrdered09 nvNodeWF09 nvCtorEnv09_eq

set_option maxRecDepth 4000 in
theorem nvRecWF09 : (⟨1, nvRecTypeL⟩ : VConstant).WF nvCtorEnv09 := by
  nv_hyps nvCtorEnv09
  have hNV : nvCtorEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvCtorEnv09.constants ``NVTree.node =
      some nvNodeV.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem nvRecEnv09_eq :
    nvCtorEnv09.addConst nvRecVL.name nvRecVL.toVConstant =
      some nvRecEnv09 := rfl

theorem nvRecOrdered09 : nvRecEnv09.Ordered :=
  .const nvCtorOrdered09 nvRecWF09 nvRecEnv09_eq

set_option maxRecDepth 4000 in
theorem nvRec1WF09 : (⟨1, nvRec1TypeL⟩ : VConstant).WF nvRecEnv09 := by
  nv_hyps nvRecEnv09
  have hNV : nvRecEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvRecEnv09.constants ``NVTree.node =
      some nvNodeV.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem nvRec1Env09_eq :
    nvRecEnv09.addConst nvRec1VL.name nvRec1VL.toVConstant =
      some nvRec1Env09 := rfl

theorem nvRec1Ordered09 : nvRec1Env09.Ordered :=
  .const nvRecOrdered09 nvRec1WF09 nvRec1Env09_eq

section NVRuleWF

set_option maxRecDepth 8000

macro "nv_rule_hyps" e:term : tactic => `(tactic| (
  nv_hyps $e
  have hNV : VEnv.constants $e ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : VEnv.constants $e ``NVTree.node = some nvNodeV.toVConstant := rfl
  have hRec : VEnv.constants $e ``NVTree.rec = some ⟨1, nvRecTypeL⟩ := rfl
  have hRec1 : VEnv.constants $e
      `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1 = some ⟨1, nvRec1TypeL⟩ := rfl))

def nvRuleEnv1 : VEnv := nvRec1Env09.addDefEq nvRulesL[0]
def nvRuleEnv2 : VEnv := nvRuleEnv1.addDefEq nvRulesL[1]

theorem nvRule0WF09 : nvRulesL[0].WF nvRec1Env09 := by
  constructor
  · nv_rule_hyps nvRec1Env09; type_tac
  · nv_rule_hyps nvRec1Env09; type_tac

theorem nvRule1WF09 : nvRulesL[1].WF nvRuleEnv1 := by
  constructor
  · nv_rule_hyps nvRuleEnv1; type_tac
  · nv_rule_hyps nvRuleEnv1; type_tac

theorem nvRule2WF09 : nvRulesL[2].WF nvRuleEnv2 := by
  constructor
  · nv_rule_hyps nvRuleEnv2; type_tac
  · nv_rule_hyps nvRuleEnv2; type_tac

end NVRuleWF


/-! ## NV semantic package -/

theorem nvTypesFold_eq :
    nvSourceV.blockTypeConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) pvecCtorEnv09 =
      some nvTypeEnv09 := rfl

theorem nvCtorsFold_eq :
    nvSourceV.blockConstructorConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) nvTypeEnv09 =
      some nvCtorEnv09 := rfl

theorem nvRecsFold_eq :
    nvNestedC.recursors.foldlM
      (fun env c => env.addConst c.name c.toVConstant) nvCtorEnv09 =
      some nvRec1Env09 := by
  rw [nvRecursors_eq]; rfl

theorem nvNestedWF09 : nvNestedC.WF pvecCtorEnv09 := by
  refine ⟨⟨nvFamilyWF09, fun env' h => ?_⟩, fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_, fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (nvTypeEnv09_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (nvTypesFold_eq.symm.trans h)
    exact ⟨nvNodeWF09, fun env' h' => by
      cases Option.some.inj (nvCtorEnv09_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (nvTypesFold_eq.symm.trans hT)
    cases Option.some.inj (nvCtorsFold_eq.symm.trans hC)
    rw [nvRecursors_eq]
    exact ⟨nvRecWF09, fun env' h' => by
      cases Option.some.inj (nvRecEnv09_eq.symm.trans h')
      exact ⟨nvRec1WF09, fun env'' h'' => by
        cases Option.some.inj (nvRec1Env09_eq.symm.trans h'')
        exact trivial⟩⟩
  · cases Option.some.inj (nvTypesFold_eq.symm.trans hT)
    cases Option.some.inj (nvCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (nvRecsFold_eq.symm.trans hR)
    rw [nvRules_eq]
    exact ⟨nvRule0WF09, nvRule1WF09, nvRule2WF09, trivial⟩

/-! ## NV freshness and stored-metadata translations -/

theorem nvTypeFresh09 : pvecCtorMap09.find? ``NVTree = none := by
  rw [pvecCtorMap09, pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvTypeMapWF09 : nvTypeMap09.WF :=
  pvecCtorMapWF09.insert _ _ nvTypeFresh09

theorem nvNodeFresh09 : nvTypeMap09.find? ``NVTree.node = none := by
  rw [nvTypeMap09, pvecCtorMapWF09.find?_insert, pvecCtorMap09,
    pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvCtorMapWF09 : nvCtorMap09.WF :=
  nvTypeMapWF09.insert _ _ nvNodeFresh09

theorem nvRecFresh09 : nvCtorMap09.find? ``NVTree.rec = none := by
  rw [nvCtorMap09, nvTypeMapWF09.find?_insert, nvTypeMap09,
    pvecCtorMapWF09.find?_insert, pvecCtorMap09,
    pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvRecMapWF09 : nvRecMap09.WF :=
  nvCtorMapWF09.insert _ _ nvRecFresh09

theorem nvRec1Fresh09 :
    nvRecMap09.find? `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1 = none := by
  rw [nvRecMap09, nvCtorMapWF09.find?_insert, nvCtorMap09,
    nvTypeMapWF09.find?_insert, nvTypeMap09,
    pvecCtorMapWF09.find?_insert, pvecCtorMap09,
    pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvInfoTr09 : TrConstVal .safe pvecCtorEnv09 nvInfo09 nvFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr pvecCtorEnv09 nvInfo09.levelParams []
      nvInfo09.type nvFamilyV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS pvecCtorOrdered09 trivial ⟨_, by type_tac⟩

theorem nvNodeTr09 : TrConstVal .safe nvTypeEnv09 nvNodeInfo09 nvNodeV := by
  nv_hyps nvTypeEnv09
  have hNV : nvTypeEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr nvTypeEnv09 nvNodeInfo09.levelParams []
      nvNodeInfo09.type nvNodeV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS nvTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem nvRecTr09 : TrConstVal .safe nvCtorEnv09 nvRecInfo09 nvRecVL := by
  nv_hyps nvCtorEnv09
  have hNV : nvCtorEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvCtorEnv09.constants ``NVTree.node = some nvNodeV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr nvCtorEnv09 nvRecInfo09.levelParams []
      nvRecInfo09.type nvRecVL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := nvRecWF09
  exact shape.to_trExprS nvCtorOrdered09 trivial ⟨_, hty⟩

theorem nvRec1Tr09 : TrConstVal .safe nvRecEnv09 nvRec1Info09 nvRec1VL := by
  nv_hyps nvRecEnv09
  have hNV : nvRecEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvRecEnv09.constants ``NVTree.node = some nvNodeV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr nvRecEnv09 nvRec1Info09.levelParams []
      nvRec1Info09.type nvRec1VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := nvRec1WF09
  exact shape.to_trExprS nvRecOrdered09 trivial ⟨_, hty⟩

/-! ## NV recursor K metadata, trace, and `TrEnv'` drive -/

theorem nvKTarget09 : nvNestedC.generation.kTarget = false := by
  native_decide

theorem nvRecLookup09 : nvMap09.find? ``NVTree.rec = some nvRecInfo09 := by
  rw [nvMap09, nvRecMapWF09.find?_insert]
  simp [nvRecMap09, nvCtorMapWF09.find?_insert]

theorem nvRec1Lookup09 :
    nvMap09.find? `Ix.Theory.Named.NestedRepresentation.NVTree.rec_1 =
      some nvRec1Info09 := by
  rw [nvMap09, nvRecMapWF09.find?_insert]
  simp

theorem nvRecK09 :
    RecursorMapKMatches nvMap09 nvNestedC.recursors
      nvNestedC.generation.kTarget := by
  rw [nvRecursors_eq, nvKTarget09]
  intro recursor hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨nvRecInfo09, nvRecLookup09, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨nvRec1Info09, nvRec1Lookup09, by decide⟩
  · cases hmem

def nvTrace09 :
    AddInductNestedTrace pvecCtorMap09 pvecCtorEnv09 nvSourceV
      nvMap09 nvFinalEnv09 where
  nested := nvNestedC
  nested_wf := nvNestedWF09
  typeMap := nvTypeMap09
  typeEnv := nvTypeEnv09
  ctorMap := nvCtorMap09
  ctorEnv := nvCtorEnv09
  recEnv := nvRec1Env09
  addTypes := .cons
    { info := nvInfo09
      kind_eq := trivial
      tr := nvInfoTr09
      map_fresh := nvTypeFresh09
      env_add := nvTypeEnv09_eq
      map_add := rfl } .nil
  addCtors := .cons
    { info := nvNodeInfo09
      kind_eq := trivial
      tr := nvNodeTr09
      map_fresh := nvNodeFresh09
      env_add := nvCtorEnv09_eq
      map_add := rfl } .nil
  addRecs := nvRecursors_eq ▸ .cons
    { info := nvRecInfo09
      kind_eq := trivial
      tr := nvRecTr09
      map_fresh := nvRecFresh09
      env_add := nvRecEnv09_eq
      map_add := rfl } (.cons
    { info := nvRec1Info09
      kind_eq := trivial
      tr := nvRec1Tr09
      map_fresh := nvRec1Fresh09
      env_add := nvRec1Env09_eq
      map_add := rfl } .nil)
  recK := nvRecK09
  addRules := ⟨by rw [nvRules_eq]; rfl⟩

theorem nvAddInductNested09 :
    AddInductNested pvecCtorMap09 pvecCtorEnv09 nvSourceV
      nvMap09 nvFinalEnv09 :=
  ⟨nvTrace09⟩

/-- The nested-indexed declaration, replayed from real stored metadata over
the staged `PVec` boundary through the nested alignment constructor. -/
theorem nvTrEnv09 : TrEnv' .safe nvMap09 false nvFinalEnv09 :=
  .inductNested nvAddInductNested09 pvecTrEnv09

theorem nvFinalOrdered09 : nvFinalEnv09.Ordered :=
  nvTrEnv09.wf.ordered

#guard nvNestedC.elim.numNested == 1


#guard_named_axioms Ix.Theory.Named.NestedReplayFixtures.nvTrEnv09 [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert,
  Ix.Theory.Named.NestedReplayFixtures.nvKTarget09._native.native_decide.ax_1_1,
  Ix.Theory.Named.NestedReplayFixtures.nvNestedC._native.native_decide.ax_1,
  Ix.Theory.Named.NestedReplayFixtures.nvRecursors_eq._native.native_decide.ax_1_1,
  Ix.Theory.Named.NestedReplayFixtures.nvRules_eq._native.native_decide.ax_1_1]

end Ix.Theory.Named.NestedReplayFixtures
