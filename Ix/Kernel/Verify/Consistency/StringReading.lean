/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Primitive
import Ix.Theory.Expr

/-!
# Structural reading of string literals

The reading uses the same five canonical primitives as production's
`strLitToConstructor`. It expands characters through `Char.ofNat` and lists
through `List.nil`/`List.cons`, preserving source order. Unknown primitive
references fail just as unknown explicit constants do. No new model syntax
or assumed meaning for the primitives is introduced here.
-/

namespace Ix.Kernel.Consistency

open Theory

universe u
variable {β : Type u}

structure StringPrimitiveRefs (β : Type u) where
  charType : ConstRef β
  charOfNat : ConstRef β
  stringOfList : ConstRef β
  listNil : ConstRef β
  listCons : ConstRef β

namespace StringPrimitiveRefs

def resolve? (resolve : Address → Option (ConstRef β)) : Option (StringPrimitiveRefs β) := do
  return ⟨← resolve PrimAddrs.canonical.charType, ← resolve PrimAddrs.canonical.charOfNat,
    ← resolve PrimAddrs.canonical.stringOfList, ← resolve PrimAddrs.canonical.listNil,
    ← resolve PrimAddrs.canonical.listCons⟩

theorem resolve?_fields {resolve : Address → Option (ConstRef β)}
    {refs : StringPrimitiveRefs β} (reading : resolve? resolve = some refs) :
    resolve PrimAddrs.canonical.charType = some refs.charType ∧
    resolve PrimAddrs.canonical.charOfNat = some refs.charOfNat ∧
    resolve PrimAddrs.canonical.stringOfList = some refs.stringOfList ∧
    resolve PrimAddrs.canonical.listNil = some refs.listNil ∧
    resolve PrimAddrs.canonical.listCons = some refs.listCons := by
  unfold resolve? at reading
  obtain ⟨typeRef, typeReads, reading⟩ := Option.bind_eq_some_iff.mp reading
  obtain ⟨charRef, charReads, reading⟩ := Option.bind_eq_some_iff.mp reading
  obtain ⟨stringRef, stringReads, reading⟩ := Option.bind_eq_some_iff.mp reading
  obtain ⟨nilRef, nilReads, reading⟩ := Option.bind_eq_some_iff.mp reading
  obtain ⟨consRef, consReads, reading⟩ := Option.bind_eq_some_iff.mp reading
  cases reading
  exact ⟨typeReads, charReads, stringReads, nilReads, consReads⟩

def charExpr (refs : StringPrimitiveRefs β) (char : Char) : VExpr β :=
  .app (.const refs.charOfNat []) (.natLit char.toNat)

def nilExpr (refs : StringPrimitiveRefs β) : VExpr β :=
  .app (.const refs.listNil [.zero]) (.const refs.charType [])

def consExpr (refs : StringPrimitiveRefs β) : VExpr β :=
  .app (.const refs.listCons [.zero]) (.const refs.charType [])

def listExpr (refs : StringPrimitiveRefs β) (chars : List Char) : VExpr β :=
  chars.foldr (fun char rest => .app (.app refs.consExpr (refs.charExpr char)) rest) refs.nilExpr

def expr (refs : StringPrimitiveRefs β) (value : String) : VExpr β :=
  .app (.const refs.stringOfList []) (refs.listExpr value.toList)

@[simp] theorem listExpr_liftN (refs : StringPrimitiveRefs β) (chars : List Char)
    (shift cutoff : Nat) : (refs.listExpr chars).liftN shift cutoff = refs.listExpr chars := by
  induction chars <;>
    simp_all [listExpr, charExpr, nilExpr, consExpr, VExpr.liftN]

@[simp] theorem expr_liftN (refs : StringPrimitiveRefs β) (value : String)
    (shift cutoff : Nat) : (refs.expr value).liftN shift cutoff = refs.expr value := by
  simp [expr, VExpr.liftN]

@[simp] theorem listExpr_inst (refs : StringPrimitiveRefs β) (chars : List Char)
    (arg : VExpr β) (cutoff : Nat) : (refs.listExpr chars).inst arg cutoff = refs.listExpr chars := by
  induction chars <;>
    simp_all [listExpr, charExpr, nilExpr, consExpr, VExpr.inst]

@[simp] theorem expr_inst (refs : StringPrimitiveRefs β) (value : String)
    (arg : VExpr β) (cutoff : Nat) : (refs.expr value).inst arg cutoff = refs.expr value := by
  simp [expr, VExpr.inst]

@[simp] theorem listExpr_instL (refs : StringPrimitiveRefs β) (chars : List Char)
    (levels : List VLevel) : (refs.listExpr chars).instL levels = refs.listExpr chars := by
  induction chars <;>
    simp_all [listExpr, charExpr, nilExpr, consExpr, VExpr.instL, VLevel.inst]

@[simp] theorem expr_instL (refs : StringPrimitiveRefs β) (value : String)
    (levels : List VLevel) : (refs.expr value).instL levels = refs.expr value := by
  simp [expr, VExpr.instL]

theorem listExpr_closed (refs : StringPrimitiveRefs β) (chars : List Char) (depth : Nat) :
    (refs.listExpr chars).ClosedN depth := by
  induction chars <;>
    simp_all [listExpr, charExpr, nilExpr, consExpr, VExpr.ClosedN]

theorem expr_closed (refs : StringPrimitiveRefs β) (value : String) (depth : Nat) :
    (refs.expr value).ClosedN depth := by
  simpa only [expr, VExpr.ClosedN, true_and] using refs.listExpr_closed value.toList depth

theorem listExpr_levelWF (refs : StringPrimitiveRefs β) (chars : List Char) (arity : Nat) :
    (refs.listExpr chars).LevelWF arity := by
  induction chars <;>
    simp_all [listExpr, charExpr, nilExpr, consExpr, VExpr.LevelWF, VLevel.WF]

theorem expr_levelWF (refs : StringPrimitiveRefs β) (value : String) (arity : Nat) :
    (refs.expr value).LevelWF arity := by
  simpa [expr, VExpr.LevelWF] using refs.listExpr_levelWF value.toList arity

end StringPrimitiveRefs

def readString? (resolve : Address → Option (ConstRef β)) (value : String) : Option (VExpr β) :=
  (StringPrimitiveRefs.resolve? resolve).map (·.expr value)

theorem readString?_parts {resolve : Address → Option (ConstRef β)} {value : String}
    {source : VExpr β} (reading : readString? resolve value = some source) :
    ∃ refs, StringPrimitiveRefs.resolve? resolve = some refs ∧ source = refs.expr value := by
  obtain ⟨refs, resolved, same⟩ := Option.map_eq_some_iff.mp reading
  exact ⟨refs, resolved, same.symm⟩

theorem readString?_liftN {resolve : Address → Option (ConstRef β)} {value : String}
    {source : VExpr β} (reading : readString? resolve value = some source) (shift cutoff : Nat) :
    source.liftN shift cutoff = source := by
  obtain ⟨refs, _, rfl⟩ := readString?_parts reading
  exact refs.expr_liftN value shift cutoff

theorem readString?_inst {resolve : Address → Option (ConstRef β)} {value : String}
    {source : VExpr β} (reading : readString? resolve value = some source)
    (arg : VExpr β) (cutoff : Nat) : source.inst arg cutoff = source := by
  obtain ⟨refs, _, rfl⟩ := readString?_parts reading
  exact refs.expr_inst value arg cutoff

theorem readString?_instL {resolve : Address → Option (ConstRef β)} {value : String}
    {source : VExpr β} (reading : readString? resolve value = some source)
    (levels : List VLevel) : source.instL levels = source := by
  obtain ⟨refs, _, rfl⟩ := readString?_parts reading
  exact refs.expr_instL value levels

theorem readString?_closed {resolve : Address → Option (ConstRef β)} {value : String}
    {source : VExpr β} (reading : readString? resolve value = some source) (depth : Nat) :
    source.ClosedN depth := by
  obtain ⟨refs, _, rfl⟩ := readString?_parts reading
  exact refs.expr_closed value depth

theorem readString?_levelWF {resolve : Address → Option (ConstRef β)} {value : String}
    {source : VExpr β} (reading : readString? resolve value = some source) (arity : Nat) :
    source.LevelWF arity := by
  obtain ⟨refs, _, rfl⟩ := readString?_parts reading
  exact refs.expr_levelWF value arity

end Ix.Kernel.Consistency
