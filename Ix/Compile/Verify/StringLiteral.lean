import Ix.Theory.Expr

/-!
# String literals as set-model expressions

The set-model syntax `Ix.Theory.VExpr` has a native natural-number literal but
no string literal.  Production `Ix.Kernel` expands a string literal on demand
(`Ix.Kernel.strLitToConstructor` in `Ix/Kernel/Whnf.lean`) into the
application spine

```
String.ofList (List.cons.{0} Char (Char.ofNat n₁) (… (List.nil.{0} Char)))
```

where each `nᵢ` is the natural-number literal of one code point in source
order.  `strLitToConstructor` builds `List.nil.{0} Char` and `List.cons.{0} Char`
once, then `strLitListToConstructor` folds the reversed character list,
prepending `List.cons.{0} Char (Char.ofNat nᵢ)` at each step, so the final list
is in source order.  This module states that expansion once, over already
resolved block references, so that the compiler relation (`IxonExprRel`,
`SourceExprRel`) and the kernel-side reading (plan item WP6, extending
`Ix.Kernel.Consistency.readExpr?`) use one definition: reading the kernel's
expansion with `readExpr? resolve` yields exactly `StringRefs.stringLiteral`
for the references obtained by `StringRefs.ofResolve?` on the addresses in
`Ix.Kernel.PrimAddrs` (`charType`, `charOfNat`, `stringOfList`, `listNil`,
`listCons`).

The definitions are generic in the block identifier `β` so that they can move
into `Ix/Theory/` unchanged when the kernel side adopts them.
-/

namespace Ix.Compile.Verify

open Ix.Theory (VExpr ConstRef)

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
with the corresponding `Ix.Kernel.PrimAddrs` fields. -/
def ofResolve? {α : Type v} (resolve : α → Option (ConstRef β))
    (char charOfNat stringOfList listNil listCons : α) :
    Option (StringRefs β) := do
  return {
    char := ← resolve char
    charOfNat := ← resolve charOfNat
    stringOfList := ← resolve stringOfList
    listNil := ← resolve listNil
    listCons := ← resolve listCons }

end StringRefs

end Ix.Compile.Verify
