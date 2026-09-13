/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Checker
import Ix.Theory.Model.Signature

/-! Internal formation of a finite signature. These operations publish no
admitted environment: membership and every computation equation must still
be constructed by the caller's semantic producer. -/

namespace Ix.Theory.Certified.Signature

open Model

universe u v
variable {β : Type u} [DecidableEq β]

structure Header (β : Type u) where
  ref : ConstRef β
  universes : Nat
  type : AExpr β

def Header.entry (header : Header β) : ConstantEntry β :=
  ⟨header.universes, header.type, none, [], []⟩

def environment (entries : Environment β) : List (Header β) → Environment β
  | [] => entries
  | header :: rest => environment (entries.insert header.ref header.entry) rest

structure TypeWitness (β : Type u) where
  level : VLevel
  typing : TypingWitness β

inductive Formed : Environment β → List (Header β) → Prop where
  | nil (entries) : Formed entries []
  | cons {entries header rest} (fresh : entries header.ref = none)
      (scope : header.type.Scope header.universes 0) (references : header.type.ReferencesIn entries)
      {level : VLevel} (typing : TypingClaim.{u,v} entries [] header.type (.sort level))
      (tail : Formed (entries.insert header.ref header.entry) rest) : Formed entries (header :: rest)

def checkTypes (fuel : Nat) (entries : Environment β) : (headers : List (Header β)) →
    List (TypeWitness β) → Option (CheckedClaim.{u} (Formed.{u,v} entries headers))
  | [], [] => some ⟨.nil entries⟩
  | header :: headers, witness :: witnesses =>
    if hf : entries header.ref = none then
      if hs : header.type.Scope header.universes 0 then
        if hr : header.type.ReferencesIn entries then do
          let ht ← verifyType.{u,v} fuel header.universes entries [] header.type (.sort witness.level) witness.typing
          let rest ← checkTypes fuel (entries.insert header.ref header.entry) headers witnesses
          return ⟨.cons hf hs hr ht.down rest.down⟩
        else none
      else none
    else none
  | _, _ => none

theorem checkTypes_sound {fuel : Nat} {entries : Environment β} {headers : List (Header β)}
    {witnesses : List (TypeWitness β)} {result}
    (_ : checkTypes.{u,v} fuel entries headers witnesses = some result) : Formed.{u,v} entries headers := result.down

theorem Formed.old {entries : Environment β} {headers : List (Header β)}
    (h : Formed.{u,v} entries headers) {r : ConstRef β} {entry : ConstantEntry β}
    (hr : entries r = some entry) : environment entries headers r = some entry := by
  induction h with
  | nil => exact hr
  | cons hf _ _ _ _ ih => exact ih (Environment.insert_old hf hr)

theorem Formed.lookup {entries : Environment β} {headers : List (Header β)}
    (h : Formed.{u,v} entries headers) {header : Header β} (hm : header ∈ headers) :
    environment entries headers header.ref = some header.entry := by
  induction h with
  | nil => cases hm
  | @cons entries hd rest hf hs hr level ht tail ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst header
      exact tail.old (Environment.insert_same ..)
    · exact ih hm

theorem environment_source {entries : Environment β} {headers : List (Header β)}
    {r : ConstRef β} {entry : ConstantEntry β} (h : environment entries headers r = some entry) :
    entries r = some entry ∨ ∃ header ∈ headers, r = header.ref ∧ entry = header.entry := by
  induction headers generalizing entries with
  | nil => exact Or.inl h
  | cons header rest ih =>
    rcases ih h with hold | ⟨hd, hm, he, hv⟩
    · unfold Environment.insert at hold
      split at hold
      · exact Or.inr ⟨header, List.mem_cons_self, ‹r = header.ref›, (Option.some.inj hold).symm⟩
      · exact Or.inl hold
    · exact Or.inr ⟨hd, List.mem_cons_of_mem _ hm, he, hv⟩

theorem Formed.wf {entries : Environment β} {headers : List (Header β)}
    (h : Formed.{u,v} entries headers) (hE : entries.WF) : (environment entries headers).WF := by
  induction h with
  | nil => exact hE
  | cons _ hs hr _ _ ih =>
    apply ih
    exact hE.insert hs (by simp [Header.entry]) hr (by simp [Header.entry])
      (by simp [Header.entry]) (by simp [Header.entry])
      (by simp [Header.entry]) (by simp [Header.entry])

structure Rule (β : Type u) where
  universes : Nat
  type : AExpr β
  lhs : AExpr β
  rhs : AExpr β

structure RuleWitness (β : Type u) where
  level : VLevel
  type : TypingWitness β
  lhs : TypingWitness β
  rhs : TypingWitness β

structure RuleFormed (entries : Environment β) (rule : Rule β) : Prop where
  scope : rule.type.Scope rule.universes 0 ∧ rule.lhs.Scope rule.universes 0 ∧ rule.rhs.Scope rule.universes 0
  references : rule.type.ReferencesIn entries ∧ rule.lhs.ReferencesIn entries ∧ rule.rhs.ReferencesIn entries
  type : ∃ level, TypingClaim.{u,v} entries [] rule.type (.sort level)
  lhs : TypingClaim.{u,v} entries [] rule.lhs rule.type
  rhs : TypingClaim.{u,v} entries [] rule.rhs rule.type

/-- Both complete endpoints are checked against their common formed type,
before the environment has acquired the new computation equations. -/
def checkRule (fuel : Nat) (entries : Environment β) (rule : Rule β) (witness : RuleWitness β) :
    Option (CheckedClaim.{u} (RuleFormed.{u,v} entries rule)) :=
  if hs : rule.type.Scope rule.universes 0 ∧ rule.lhs.Scope rule.universes 0 ∧ rule.rhs.Scope rule.universes 0 then
    if hr : rule.type.ReferencesIn entries ∧ rule.lhs.ReferencesIn entries ∧ rule.rhs.ReferencesIn entries then do
      let ht ← verifyType.{u,v} fuel rule.universes entries [] rule.type (.sort witness.level) witness.type
      let hl ← verifyType.{u,v} fuel rule.universes entries [] rule.lhs rule.type witness.lhs
      let hh ← verifyType.{u,v} fuel rule.universes entries [] rule.rhs rule.type witness.rhs
      return ⟨⟨hs, hr, ⟨witness.level, ht.down⟩, hl.down, hh.down⟩⟩
    else none
  else none

variable {V : Type v} [SetTheory V]
open SetTheory

/-- Formation supplies hereditary validity. The caller supplies membership
from the concrete mathematical values, in the same assignment throughout. -/
theorem Formed.realizes {entries : Environment β} {headers : List (Header β)}
    (h : Formed.{u,v} entries headers) {constants : Assignment β V} (hM : Realizes constants entries)
    (members : ∀ header ∈ headers, ∀ levels, levels.length = header.universes → ∀ env,
      constants header.ref levels ∈ˢ interp constants levels env header.type) :
    Realizes constants (environment entries headers) := by
  induction h with
  | nil => exact hM
  | cons _ _ _ ht _ ih =>
    apply ih
    · apply hM.insert
      constructor
      · intro levels _ env
        exact (ht V constants hM levels env (Context.valid_nil constants levels env)).1
      · intro levels hn env
        exact members _ List.mem_cons_self levels hn env
      · intro body hb; cases hb
      · intro body hb; cases hb
      · intro law hl; cases hl
      · intro fact hf; cases hf
    · intro header hm
      exact members header (List.mem_cons_of_mem _ hm)

end Ix.Theory.Certified.Signature
