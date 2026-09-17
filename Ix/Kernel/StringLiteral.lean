/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/StringLiteral.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
import Ix.Kernel.Expr

/-!
# Shared string-literal expressions

The set-model syntax has natural-number literals. Strings use the
constructor expansion built by the production kernel:

```
String.ofList (List.cons.{0} Char (Char.ofNat n₁) (… (List.nil.{0} Char)))
```

The compiler value relations and kernel expansion proofs share this
representation over resolved block references. Characters stay in source
order, and unresolved primitive references make the reading fail.
-/

namespace Ix.Kernel

open Ix.Kernel (VExpr ConstRef)

universe u v

/-- Resolved references of the five constants used by string-literal
expansion. -/
structure StringRefs (β : Type u) where
  /-- `Char` -/
  char : ConstRef β
  /-- `Char.ofNat` -/
  charOfNat : ConstRef β
  /-- `String.ofList` -/
  stringOfList : ConstRef β
  /-- `List.nil` -/
  listNil : ConstRef β
  /-- `List.cons` -/
  listCons : ConstRef β

namespace StringRefs

variable {β : Type u} (refs : StringRefs β)

/-- `Char`, applied to no universe levels. -/
def charType : VExpr β := .const refs.char []

/-- `Char.ofNat n` with the code point as a native literal. -/
def charLit (c : Char) : VExpr β :=
  .app (.const refs.charOfNat []) (.natLit c.toNat)

/-- `List.nil.{0} Char`. -/
def nil : VExpr β := .app (.const refs.listNil [.zero]) refs.charType

/-- `List.cons.{0} Char`, awaiting its head and tail. -/
def cons : VExpr β := .app (.const refs.listCons [.zero]) refs.charType

/-- The character list in source order. -/
def charList : List Char → VExpr β
  | [] => refs.nil
  | c :: cs => .app (.app refs.cons (refs.charLit c)) (charList cs)

/-- The set-model reading of a string literal: `String.ofList` applied to the
source-ordered character list. -/
def stringLiteral (s : String) : VExpr β :=
  .app (.const refs.stringOfList []) (refs.charList s.toList)

/-- Resolve the five expansion constants from their content addresses.  The
kernel side instantiates `resolve` with its store resolution and the addresses
with the corresponding `Ix.Tc.PrimAddrs` fields (the production checker's primitive table). -/
def ofResolve? {α : Type v} (resolve : α → Option (ConstRef β))
    (char charOfNat stringOfList listNil listCons : α) :
    Option (StringRefs β) := do
  return {
    char := ← resolve char
    charOfNat := ← resolve charOfNat
    stringOfList := ← resolve stringOfList
    listNil := ← resolve listNil
    listCons := ← resolve listCons }


/-- The recursive character list is the source-order right fold. -/
theorem charList_eq_foldr (chars : List Char) :
    refs.charList chars =
      chars.foldr (fun char rest => .app (.app refs.cons (refs.charLit char)) rest) refs.nil := by
  induction chars <;> simp_all [charList]

@[simp] theorem charList_liftN (chars : List Char) (shift cutoff : Nat) :
    (refs.charList chars).liftN shift cutoff = refs.charList chars := by
  induction chars <;> simp_all [charList, charLit, nil, cons, charType, VExpr.liftN]

@[simp] theorem stringLiteral_liftN (value : String) (shift cutoff : Nat) :
    (refs.stringLiteral value).liftN shift cutoff = refs.stringLiteral value := by
  simp [stringLiteral, VExpr.liftN]

@[simp] theorem charList_inst (chars : List Char) (arg : VExpr β) (cutoff : Nat) :
    (refs.charList chars).inst arg cutoff = refs.charList chars := by
  induction chars <;> simp_all [charList, charLit, nil, cons, charType, VExpr.inst]

@[simp] theorem stringLiteral_inst (value : String) (arg : VExpr β) (cutoff : Nat) :
    (refs.stringLiteral value).inst arg cutoff = refs.stringLiteral value := by
  simp [stringLiteral, VExpr.inst]

@[simp] theorem charList_instL (chars : List Char) (levels : List VLevel) :
    (refs.charList chars).instL levels = refs.charList chars := by
  induction chars <;> simp_all [charList, charLit, nil, cons, charType, VExpr.instL, VLevel.inst]

@[simp] theorem stringLiteral_instL (value : String) (levels : List VLevel) :
    (refs.stringLiteral value).instL levels = refs.stringLiteral value := by
  simp [stringLiteral, VExpr.instL]

theorem charList_closed (chars : List Char) (depth : Nat) :
    (refs.charList chars).ClosedN depth := by
  induction chars <;> simp_all [charList, charLit, nil, cons, charType, VExpr.ClosedN]

theorem stringLiteral_closed (value : String) (depth : Nat) :
    (refs.stringLiteral value).ClosedN depth := by
  simpa only [stringLiteral, VExpr.ClosedN, true_and] using refs.charList_closed value.toList depth

theorem charList_levelWF (chars : List Char) (arity : Nat) :
    (refs.charList chars).LevelWF arity := by
  induction chars <;> simp_all [charList, charLit, nil, cons, charType, VExpr.LevelWF, VLevel.WF]

theorem stringLiteral_levelWF (value : String) (arity : Nat) :
    (refs.stringLiteral value).LevelWF arity := by
  simpa [stringLiteral, VExpr.LevelWF] using refs.charList_levelWF value.toList arity

end StringRefs

end Ix.Kernel
