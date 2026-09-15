/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import LSpec
import Ix.Kernel.Verify.Consistency.Inductive.Run
import Ix.Kernel.Verify.Consistency.Resolution
import Tests.Ix.Kernel.IxonFixtures

/-!
Regressions for the singleton inductive witness: a `Nat`-like family with its
constructors in one block and its canonical recursor in a separate block. The
production checker accepts every member, the erased shape is read from the
stored declarations, and the decidable witness check accepts the annotated
shape against the stored recursor. This file is not a `module` because the
proof library it exercises is not one.
-/

namespace Tests.Kernel.Inductive

open LSpec Ix.Kernel Ix.Kernel.Consistency.Inductive Tests.Kernel.Fixtures
open Ix.Theory Ix.Theory.Model Ix.Theory.Certified.Ordinary Ix.Theory.Inductive

/-- `N : Sort 1`, `zero : N`, `succ : N → N` in one block; `N.rec` in its own
block, in the canonical form
`∀ (motive : N → Sort u), motive zero → (∀ (n : N), motive n → motive (succ n)) → ∀ (t : N), motive t`
with the canonical rules `λ motive z s, z` and `λ motive z s n, s n (N.rec motive z s n)`. -/
def natLikeEnv : Ixon.Env × Address × Address := Id.run do
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0,
      #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩,
        ⟨false, 0, 1, 0, 1, .leanAll (.recur 0 #[]) (.recur 0 #[])⟩]⟩
  let (env, familyBlock) := storeMutsWithProjs {} ⟨.muts #[.indc ind], #[], #[], #[.succ .zero]⟩
  let nRef : Ixon.Expr := .ref 0 #[]
  let zeroRef : Ixon.Expr := .ref 1 #[]
  let succRef : Ixon.Expr := .ref 2 #[]
  let motiveTy : Ixon.Expr := .leanAll nRef (.sort 0)
  let minorZero : Ixon.Expr := .app (.var 0) zeroRef
  let minorSucc : Ixon.Expr :=
    .leanAll nRef (.leanAll (.app (.var 2) (.var 0)) (.app (.var 3) (.app succRef (.var 1))))
  let recTy : Ixon.Expr :=
    .leanAll motiveTy (.leanAll minorZero (.leanAll minorSucc (.leanAll nRef (.app (.var 3) (.var 0)))))
  let ruleZero : Ixon.Expr := .leanLam motiveTy (.leanLam minorZero (.leanLam minorSucc (.var 1)))
  let recCall : Ixon.Expr :=
    .app (.app (.app (.app (.recur 0 #[0]) (.var 3)) (.var 2)) (.var 1)) (.var 0)
  let ruleSucc : Ixon.Expr :=
    .leanLam motiveTy (.leanLam minorZero (.leanLam minorSucc
      (.leanLam nRef (.app (.app (.var 1) (.var 0)) recCall))))
  let recr : Ixon.Recursor :=
    ⟨false, false, 1, 0, 0, 1, 2, recTy, #[⟨0, ruleZero⟩, ⟨1, ruleSucc⟩]⟩
  let (env, recursorBlock) := storeMutsWithProjs env
    ⟨.muts #[.recr recr], #[],
      #[indcProjAddr familyBlock 0, ctorProjAddr familyBlock 0 0, ctorProjAddr familyBlock 0 1],
      #[.var 0]⟩
  return (env, familyBlock, recursorBlock)

def ingressEnvOf (env : Ixon.Env) : AnonEnv :=
  match (ingressAll env).run {} with
  | .ok _ kenv => kenv
  | .error _ _ => {}

def accepts (env : Ixon.Env) (addr : Address) : Bool :=
  match (TcM.checkConst (⟨addr, ()⟩ : KId .anon)).run (.ofEnvAnon (ingressEnvOf env)) with
  | .ok () _ => true
  | .error _ _ => false

/-- The erased shape read from the stored family and constructor types. -/
def readShape (env : Ixon.Env) (familyBlock : Address) : Option (ErasedShape Address) := do
  let kenv := ingressEnvOf env
  let resolve := env.resolve
  let family ← kenv.get? ⟨indcProjAddr familyBlock 0, ()⟩
  let zero ← kenv.get? ⟨ctorProjAddr familyBlock 0 0, ()⟩
  let succ ← kenv.get? ⟨ctorProjAddr familyBlock 0 1, ()⟩
  let familyType ← Ix.Kernel.Consistency.readScopedExpr? resolve [] family.ty
  let zeroType ← Ix.Kernel.Consistency.readScopedExpr? resolve [] zero.ty
  let succType ← Ix.Kernel.Consistency.readScopedExpr? resolve [] succ.ty
  erasedShape? familyBlock family.lvls.toNat 0 familyType [zeroType, succType]

/-- The expected erased shape: no parameters, level `1`, a constructor with no
fields and a constructor with one recursive field. -/
def expectedShape : ErasedShape Address :=
  ⟨0, [], .succ .zero, [⟨[], []⟩, ⟨[], [[]]⟩]⟩

/-- The decidable witness check on the annotated shape and the stored
recursor, in the given elimination mode. -/
def witnessAcceptedWith (env : Ixon.Env) (familyBlock recursorBlock : Address) (mode : ElimMode) : Bool :=
  let kenv := ingressEnvOf env
  match kenv.get? ⟨indcProjAddr familyBlock 0, ()⟩, kenv.get? ⟨ctorProjAddr familyBlock 0 0, ()⟩,
      kenv.get? ⟨ctorProjAddr familyBlock 0 1, ()⟩, kenv.get? ⟨recrProjAddr recursorBlock 0, ()⟩,
      readShape env familyBlock with
  | some family, some zero, some succ, some recr, some erased =>
      singletonWitnessCheck env.resolve familyBlock recursorBlock family [zero, succ] recr
        erased.annotate mode
  | _, _, _, _, _ => false

def witnessAccepted (env : Ixon.Env) (familyBlock recursorBlock : Address) : Bool :=
  witnessAcceptedWith env familyBlock recursorBlock .large

private def cases : TestSeq :=
  let (env, familyBlock, recursorBlock) := natLikeEnv
  test "singleton inductive: production accepts the family, constructors, and recursor"
    (accepts env (indcProjAddr familyBlock 0) && accepts env (ctorProjAddr familyBlock 0 0) &&
      accepts env (ctorProjAddr familyBlock 0 1) && accepts env (recrProjAddr recursorBlock 0))
  ++ test "singleton inductive: the erased shape reads from the stored declarations"
    (decide (readShape env familyBlock = some expectedShape))
  ++ test "singleton inductive: the witness check accepts the annotated shape and stored recursor"
    (witnessAccepted env familyBlock recursorBlock)
  ++ test "singleton inductive: the witness check rejects the wrong elimination mode"
    (!witnessAcceptedWith env familyBlock recursorBlock .small)

def suite : List TestSeq := [cases]

end Tests.Kernel.Inductive
