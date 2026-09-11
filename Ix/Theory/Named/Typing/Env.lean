/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Typing.Basic
import Ix.Theory.Named.VDecl
import Ix.Theory.Named.Quot
import Ix.Theory.Named.Inductive
import Ix.Theory.Named.NestedInductive

namespace Ix.Theory.Named

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | mutualDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.mutualDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct {gen : decl.GenerationChecked} :
    gen.WF env →
    env.addInductGeneration gen = some env' →
    VDecl.WF env (.induct decl) env'
  | inductBlock {gen : decl.BlockGenerationChecked} :
    gen.WF env blockEnv →
    env.addInductBlockGeneration gen = some env' →
    VDecl.WF env (.induct decl) env'
  | inductNested {nested : decl.NestedBlockChecked} :
    nested.WF env →
    env.addInductNested nested = some env' →
    VDecl.WF env (.induct decl) env'

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)
  /-- A checked structure-eta descriptor is an environment capability, not a
  source declaration.  Keep it in the environment history without inventing
  a `VDecl`; its subject-reduction certificate is exactly the premise used by
  `Ordered.structEta`. -/
  | structEta {env : VEnv} {rule : VStructEta} : rule.WF env → env.WF' ds →
      (env.addStructEta rule).WF' ds

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

/- A normalized inductive history entry carries only the standard Theory
logical baseline; in particular it cannot import Verify's implementation
axioms into `VEnv.WF`. -/
#guard_named_axioms Ix.Theory.Named.VDecl.WF.induct [propext, Quot.sound]
