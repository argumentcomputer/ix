/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Check

/-! # Admission of separate inductive and recursor records

Ixon stores an ordinary inductive family and its recursor in separate primary
records. Like `Ix.Tc` and the Rust kernel, association uses the recursor's
major premise. This reader handles the syntactic ordinary profile; it does
not reduce open telescope bodies in an empty context. Association is only
candidate discovery: `checkInductiveC` checks both complete records, all
metadata and rules, formation, and freshness before installing either.

The driver consumes the associated pair together without rewriting addresses,
member positions, types, or rules. Other records retain their relative order.
Every record consumed by the driver gets its own exact installed reading.
-/

namespace Ix.Kernel.Ingress

universe u v
variable {β : Type u} [DecidableEq β]

/-- The ordinary recursor's major follows parameters, motives, minors, and
indices. Natural-number metadata cannot overflow while locating it. -/
def recursorMajor : Const β → Option (ConstRef β)
  | .recursor _ params indices motives minors type _ _ _ => do
    let (_, tail) ← Certified.Ordinary.splitN (params + motives + minors + indices) type
    let .forallE domain _ := tail | none
    let .const family _ := domain.appHead | none
    return family
  | _ => none

/-- A selected physical record and the remaining records. Proof fields ensure
that finding a candidate cannot silently discard another input record. -/
structure RecursorCandidate (decls : List (Decl β)) where
  declaration : Decl β
  constant : Const β
  rest : List (Decl β)
  singleton : declaration.block = ⟨[constant]⟩
  noConstructors : constant.ctorCount = 0
  covers : ∀ d ∈ decls, d = declaration ∨ d ∈ rest
  shorter : rest.length < decls.length

def findRecursor (family : ConstRef β) : (decls : List (Decl β)) → Option (RecursorCandidate decls)
  | [] => none
  | d :: ds =>
    let remaining : Unit → Option (RecursorCandidate (d :: ds)) := fun _ => do
      let candidate ← findRecursor family ds
      return {
        declaration := candidate.declaration
        constant := candidate.constant
        rest := d :: candidate.rest
        singleton := candidate.singleton
        noConstructors := candidate.noConstructors
        covers := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact .inr List.mem_cons_self
          · rcases candidate.covers q hq with same | member
            · exact .inl same
            · exact .inr (List.mem_cons_of_mem _ member)
        shorter := Nat.succ_lt_succ candidate.shorter }
    match hm : d.block.members with
    | [.recursor u p i mo mi type rules k safety] =>
      let constant := Const.recursor u p i mo mi type rules k safety
      if recursorMajor constant = some family then
        some {
          declaration := d
          constant
          rest := ds
          singleton := congrArg Block.mk hm
          noConstructors := rfl
          covers := fun q hq => List.mem_cons.mp hq
          shorter := Nat.lt_succ_self _ }
      else remaining ()
    | _ => remaining ()

/-- A proof-carrying fold over physical declarations. The ordinary paired
layout remains supported by `checkDeclC`; separate records are admitted by
the same inductive checker at their original references. -/
def checkDeclarationsC (cfg : Config) (env : Env β) :
    (decls : List (Decl β)) → Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      ∀ d ∈ decls, d.block.Installed d.address env'.toEnvironment }
  | [] => .ok ⟨env, AdmissionClaim.refl env, by simp⟩
  | d :: ds =>
    match hm : d.block.members with
    | [.induct u p i type constructors safety] =>
      let family := Const.induct u p i type constructors safety
      match findRecursor (.member d.address 0) ds with
      | none => do
        let ⟨env₁, step₁, hd⟩ ← checkDeclC.{u,v} cfg env d
        let ⟨env₂, step₂, installed⟩ ← checkDeclarationsC cfg env₁ ds
        return ⟨env₂, step₁.trans step₂, by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hd.mono step₂.preserves
          · exact installed q hq⟩
      | some candidate => do
        let ⟨env₁, step₁, hf, hr⟩ ← checkInductiveC.{u,v} cfg env d.address
          (.member candidate.declaration.address 0) family candidate.constant
        let ⟨env₂, step₂, installed⟩ ← checkDeclarationsC cfg env₁ candidate.rest
        return ⟨env₂, step₁.trans step₂, by
          intro q hq
          rcases List.mem_cons.mp hq with same | hq
          · subst q
            have hblock : d.block = ⟨[family]⟩ := congrArg Block.mk hm
            rw [hblock]
            exact Block.installed_singleton (hf.mono step₂.preserves)
          · rcases candidate.covers q hq with rfl | hq
            · rw [candidate.singleton]
              obtain ⟨entry, found, reading⟩ := hr
              exact Block.installed_singleton ((Const.installed_of_lookup found reading
                candidate.noConstructors).mono step₂.preserves)
            · exact installed q hq⟩
    | _ => do
      let ⟨env₁, step₁, hd⟩ ← checkDeclC.{u,v} cfg env d
      let ⟨env₂, step₂, installed⟩ ← checkDeclarationsC cfg env₁ ds
      return ⟨env₂, step₁.trans step₂, by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hd.mono step₂.preserves
        · exact installed q hq⟩
  termination_by decls => decls.length
  decreasing_by
    · exact Nat.lt_succ_self _
    · exact Nat.lt_trans candidate.shorter (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self _

end Ix.Kernel.Ingress
