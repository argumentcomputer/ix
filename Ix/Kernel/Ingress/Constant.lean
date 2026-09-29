/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress.Expr

namespace Ix.Kernel.Ingress

/-- A proof-carrying traversal preserves list length and ordering. -/
def readListC {R : α → β → Prop} (read : (a : α) → Search { b : β // R a b }) :
    (inputs : List α) → Search { outputs : List β // Forall₂ R inputs outputs }
  | [] => .ok ⟨[], .nil⟩
  | input :: inputs => do
    let output ← read input
    let outputs ← readListC read inputs
    return ⟨output.val :: outputs.val, .cons output.property outputs.property⟩

def readDefinitionC (ctx : Context) (fuel : Nat) (source : Ixon.Definition) :
    Search { target : Const Address // DefinitionReads ctx source target } := do
  let type ← readExprC ctx fuel ctx.source.sharing.size source.typ
  let value ← readExprC ctx fuel ctx.source.sharing.size source.value
  return ⟨.defn source.lvls.toNat (kind source.kind) type.val value.val (safety source.safety),
    .mk type.property value.property⟩

def readConstructorC (ctx : Context) (fuel : Nat) (source : Ixon.Constructor × Nat) :
    Search { target : Ctor Address // ConstructorReads ctx source target } := do
  if position : source.1.cidx.toNat = source.2 then
    let type ← readExprC ctx fuel ctx.source.sharing.size source.1.typ
    return ⟨⟨source.1.lvls.toNat, source.1.params.toNat, source.1.fields.toNat,
      type.val, unsafeFlag source.1.isUnsafe⟩,
      position, rfl, rfl, rfl, rfl, type.property⟩
  else throw (.malformed "constructor index differs from its position in the block")

def readRuleC (ctx : Context) (fuel : Nat) (source : Ixon.RecursorRule) :
    Search { target : RecRule Address // RuleReads ctx source target } := do
  let rhs ← readExprC ctx fuel ctx.source.sharing.size source.rhs
  return ⟨⟨source.fields.toNat, rhs.val⟩, rfl, rhs.property⟩

def readRecursorC (ctx : Context) (fuel : Nat) (source : Ixon.Recursor) :
    Search { target : Const Address // RecursorReads ctx source target } := do
  let type ← readExprC ctx fuel ctx.source.sharing.size source.typ
  let rules ← readListC (readRuleC ctx fuel) source.rules.toList
  return ⟨.recursor source.lvls.toNat source.params.toNat source.indices.toNat
    source.motives.toNat source.minors.toNat type.val rules.val source.k (unsafeFlag source.isUnsafe),
    .mk type.property rules.property⟩

def readInductiveC (ctx : Context) (fuel : Nat) (source : Ixon.Inductive) :
    Search { target : Const Address // InductiveReads ctx source target } := do
  let type ← readExprC ctx fuel ctx.source.sharing.size source.typ
  let ctors ← readListC (readConstructorC ctx fuel) source.ctors.toList.zipIdx
  return ⟨.induct source.lvls.toNat source.params.toNat source.indices.toNat
    type.val ctors.val (unsafeFlag source.isUnsafe), .mk type.property ctors.property⟩

def readMemberC (ctx : Context) (fuel : Nat) :
    (source : Ixon.MutConst) → Search { target : Const Address // MemberReads ctx source target }
  | .defn source => do
    let target ← readDefinitionC ctx fuel source
    return ⟨target.val, .defn target.property⟩
  | .indc source => do
    let target ← readInductiveC ctx fuel source
    return ⟨target.val, .indc target.property⟩
  | .recr source => do
    let target ← readRecursorC ctx fuel source
    return ⟨target.val, .recr target.property⟩

private def readInfoC (ctx : Context) (fuel : Nat) : (source : Ixon.ConstantInfo) →
    Search { target : Block Address // InfoReads ctx source target }
  | .defn source => do
    let target ← readDefinitionC ctx fuel source
    return ⟨⟨[target.val]⟩, .defn target.property⟩
  | .recr source => do
    let target ← readRecursorC ctx fuel source
    return ⟨⟨[target.val]⟩, .recr target.property⟩
  | .axio source => do
    let type ← readExprC ctx fuel ctx.source.sharing.size source.typ
    return ⟨⟨[.axiom source.lvls.toNat type.val (unsafeFlag source.isUnsafe)]⟩, .axio type.property⟩
  | .quot source => do
    let type ← readExprC ctx fuel ctx.source.sharing.size source.typ
    return ⟨⟨[.quot (quotientKind source.kind) source.lvls.toNat type.val]⟩, .quot type.property⟩
  | .muts members => do
    let constants ← readListC (readMemberC ctx fuel) members.toList
    return ⟨⟨constants.val⟩, .muts constants.property⟩
  | .dPrj _ | .rPrj _ | .iPrj _ | .cPrj _ =>
    .error (.malformed "a projection is a reference to an owning block, not a declaration")

def readBlockC (ctx : Context) (fuel : Nat) :
    Search { target : Block Address // BlockReads ctx target } :=
  readInfoC ctx fuel ctx.source.info

def readBlock (ctx : Context) (fuel : Nat) : Search (Block Address) :=
  (readBlockC ctx fuel).map Subtype.val

theorem readBlock_reading {ctx : Context} {fuel : Nat} {block : Block Address}
    (h : readBlock ctx fuel = .ok block) : BlockReads ctx block := by
  unfold readBlock at h
  cases hc : readBlockC ctx fuel with
  | error failure => simp [hc, Except.map] at h
  | ok result =>
    simp [hc, Except.map] at h
    exact h ▸ result.property

end Ix.Kernel.Ingress
