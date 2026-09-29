/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Const

/-! # Exact declaration readings in an installed environment

These syntactic contracts complement model existence. They retain the raw
type, definition body, universe count, member position, and constructor
position. Equations and facts are specified by each admission adapter's
published-entry equality and are preserved by `Env.Preserves`.
-/

namespace Ix.Kernel
open Model
universe u
variable {β : Type u}

/-- The fields supplied for one member, before adding certified facts. -/
def Const.Reads (c : Const β) (entry : ConstantEntry β) : Prop :=
  entry.universes = c.uvars ∧ entry.type.erase = c.type ∧
    match c with
    | .defn _ _ _ body _ => entry.body.map AExpr.erase = some body
    | _ => entry.body = none

/-- A constructor reading preserves its complete supplied type. -/
def Ctor.Reads (c : Ctor β) (entry : ConstantEntry β) : Prop :=
  entry.universes = c.uvars ∧ entry.type.erase = c.type ∧ entry.body = none

def Const.Installed (c : Const β) (source : β) (index : Nat) (entries : Environment β) : Prop :=
  (∃ entry, entries (.member source index) = some entry ∧ c.Reads entry) ∧
    match c with
    | .induct _ _ _ _ ctors _ => ∀ j ctor, ctors[j]? = some ctor →
        ∃ entry, entries (.ctor source index j) = some entry ∧ ctor.Reads entry
    | _ => True

def Block.Installed (block : Block β) (source : β) (entries : Environment β) : Prop :=
  ∀ (i : Nat) (c : Const β), block.members[i]? = some c → c.Installed source i entries

theorem Const.installed_of_lookup {c : Const β} {entry : ConstantEntry β}
    {source : β} {index : Nat} {entries : Environment β}
    (he : entries (.member source index) = some entry) (hr : c.Reads entry)
    (hc : c.ctorCount = 0) : c.Installed source index entries := by
  refine ⟨⟨entry, he, hr⟩, ?_⟩
  cases c <;> try trivial
  simp only [Const.ctorCount, List.length_eq_zero_iff] at hc
  simp [hc]

theorem Block.installed_singleton {c : Const β} {source : β} {entries : Environment β}
    (h : c.Installed source 0 entries) : (Block.mk [c]).Installed source entries := by
  intro i d hd
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hd; subst d; exact h
  | succ i => simp at hd

theorem Block.installed_pair {a b : Const β} {source : β} {entries : Environment β}
    (ha : a.Installed source 0 entries) (hb : b.Installed source 1 entries) :
    (Block.mk [a, b]).Installed source entries := by
  intro i d hd
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hd; subst d; exact ha
  | succ i =>
    cases i with
    | zero => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
              subst d; exact hb
    | succ i => simp at hd

theorem Block.installed_singleton_push [DecidableEq β] (env : Env β) (source : β)
    (c : Const β) (entry : ConstantEntry β) (hr : c.Reads entry) (hc : c.ctorCount = 0) :
    (Block.mk [c]).Installed source (env.push (.member source 0) entry).toEnvironment :=
  installed_singleton (Const.installed_of_lookup (Env.lookup_push_same ..) hr hc)

theorem Const.Installed.mono {c : Const β} {source : β} {index : Nat}
    {before after : Environment β} (h : c.Installed source index before)
    (preserves : ∀ r entry, before r = some entry → after r = some entry) :
    c.Installed source index after := by
  refine ⟨?_, ?_⟩
  · obtain ⟨entry, he, hr⟩ := h.1
    exact ⟨entry, preserves _ _ he, hr⟩
  · cases c <;> try trivial
    intro j ctor hc
    obtain ⟨entry, he, hr⟩ := h.2 j ctor hc
    exact ⟨entry, preserves _ _ he, hr⟩

theorem Block.Installed.mono {block : Block β} {source : β} {before after : Environment β}
    (h : block.Installed source before)
    (preserves : ∀ r entry, before r = some entry → after r = some entry) :
    block.Installed source after := fun i c hc => (h i c hc).mono preserves

end Ix.Kernel
