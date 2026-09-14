/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.RequestCodec
import Ix.IxonSyntax

/-! Data codecs using the existing Ixon constructor-expression syntax.
Readers recognize concrete constructors and literal helpers. They do not
evaluate user code, resolve imports, or run Lean elaboration.
-/

namespace Ix.Certified.Text

open Ixon.Syntax

/-- A convenient literal helper for Lean authors. Text input checks the same
hexadecimal form and rejects invalid addresses before constructing a value. -/
def address! (hex : String) : Address := (Address.fromString hex).get!

/-- A byte-string literal for Lean authors and Ixon constructor expressions. -/
def bytes! (hex : String) : ByteArray := (bytesOfHex hex).get!

def ref (name : String) : Term :=
  .ref { name := some { parts := (name.splitOn ".").toArray.map NameComponent.str } }

def ctor (name : String) (args : Array Term := #[]) : Term :=
  if args.isEmpty then ref name else .app (ref name) args {}

class Codec (α : Type) where
  type : Term
  encode : α → Term
  decode : Term → Except String α

def typeOf (α : Type) [Codec α] : Term := Codec.type (α := α)
def encode [Codec α] (value : α) : Term := Codec.encode value
def decode [Codec α] (term : Term) : Except String α := Codec.decode term

def expectType [Codec α] (term : Term) : Except String Unit := do
  if printTerm term != printTerm (typeOf α) then
    throw s!"expected Ixon type {printTerm (typeOf α)}"

/-- Parenthesized application spines have the same constructor arguments. -/
def spine : Term → Term × Array Term
  | .app head args _ =>
    let (head, previous) := spine head
    (head, previous ++ args)
  | term => (term, #[])

def constructor (term : Term) : Except String (String × Array Term) := do
  let (head, args) := spine term
  let .ref reference := head | throw "expected an Ixon data constructor"
  let some name := reference.name | throw "expected a named Ixon data constructor"
  if reference.hash.isSome || reference.levels.isSome then
    throw "data constructors must use unpinned names with default universe levels"
  let parts ← name.parts.toList.mapM fun
    | .str value => pure value
    | .num _ => throw "invalid data constructor name"
  return (String.intercalate "." parts, args)

def arguments (name : String) (count : Nat) (term : Term) : Except String (Array Term) := do
  let (actual, args) ← constructor term
  if actual != name || args.size != count then
    throw s!"expected {name} with {count} arguments"
  return args

def arity (name : String) (count : Nat) (args : Array Term) : Except String Unit := do
  if args.size != count then throw s!"expected {count} arguments to {name}"

instance : Codec Address where
  type := ref "Address"
  encode value := ctor "Ix.Certified.Text.address!" #[.strLit (hexOfBytes value.hash) {}]
  decode term := do
    let args ← arguments "Ix.Certified.Text.address!" 1 term
    let .strLit hex _ := args[0]! | throw "expected a hexadecimal address string"
    match Address.fromString hex with
    | some value => return value
    | none => throw "expected a 32-byte hexadecimal address"

instance : Codec ByteArray where
  type := ref "ByteArray"
  encode value := ctor "Ix.Certified.Text.bytes!" #[.strLit (hexOfBytes value) {}]
  decode term := do
    let args ← arguments "Ix.Certified.Text.bytes!" 1 term
    let .strLit hex _ := args[0]! | throw "expected a hexadecimal byte string"
    match bytesOfHex hex with
    | some value => return value
    | none => throw "expected an even-length hexadecimal byte string"

instance : Codec Bool where
  type := ref "Bool"
  encode value := ref (if value then "Bool.true" else "Bool.false")
  decode term := do
    let (name, args) ← constructor term
    arity name 0 args
    match name with
    | "Bool.true" => return true
    | "Bool.false" => return false
    | _ => throw "expected Bool.true or Bool.false"

instance : Codec UInt64 where
  type := ref "UInt64"
  encode value := ctor "UInt64.ofNat" #[.natLit value.toNat {}]
  decode term := do
    let args ← arguments "UInt64.ofNat" 1 term
    let .natLit value _ := args[0]! | throw "expected an unsigned integer literal"
    if value >= 2 ^ 64 then throw "unsigned integer exceeds UInt64"
    return value.toUInt64

instance [Codec α] : Codec (Option α) where
  type := ctor "Option" #[typeOf α]
  encode
    | none => ctor "Option.none" #[typeOf α]
    | some value => ctor "Option.some" #[typeOf α, encode value]
  decode term := do
    let (name, args) ← constructor term
    if name == "Option.none" then
      arity name 1 args
      expectType (α := α) args[0]!
      return none
    else if name == "Option.some" then
      arity name 2 args
      expectType (α := α) args[0]!
      return some (← decode args[1]!)
    else throw "expected Option.none or Option.some"

def encodeList [Codec α] : List α → Term
  | [] => ctor "List.nil" #[typeOf α]
  | value :: rest => ctor "List.cons" #[typeOf α, encode value, encodeList rest]

def decodeList [Codec α] : Nat → Term → Except String (List α)
  | 0, _ => .error "Ixon data list exceeds the nesting limit"
  | fuel + 1, term => do
    let (name, args) ← constructor term
    if name == "List.nil" then
      arity name 1 args
      expectType (α := α) args[0]!
      return []
    else if name == "List.cons" then
      arity name 3 args
      expectType (α := α) args[0]!
      return (← decode args[1]!) :: (← decodeList fuel args[2]!)
    else throw "expected List.nil or List.cons"

instance [Codec α] : Codec (List α) where
  type := ctor "List" #[typeOf α]
  encode := encodeList
  decode := decodeList 1024

instance [Codec α] : Codec (Array α) where
  type := ctor "Array" #[typeOf α]
  encode values := ctor "List.toArray" #[typeOf α, encode values.toList]
  decode term := do
    let args ← arguments "List.toArray" 2 term
    expectType (α := α) args[0]!
    return (← decode (α := List α) args[1]!).toArray

instance [Codec α] [Codec β] : Codec (α × β) where
  type := ctor "Prod" #[typeOf α, typeOf β]
  encode value := ctor "Prod.mk" #[typeOf α, typeOf β, encode value.1, encode value.2]
  decode term := do
    let args ← arguments "Prod.mk" 4 term
    expectType (α := α) args[0]!
    expectType (α := β) args[1]!
    return (← decode args[2]!, ← decode args[3]!)

/-- Print a single typed definition in the standard `.ixon` file grammar. -/
def write [Codec α] (name : String) (value : α) : String :=
  printFile { version := VERSION, decls := #[.defn {
    kw := .defn, name := some { parts := #[.str name] },
    ty := typeOf α, value := encode value }] }

/-- A data file contains one safe monomorphic definition or one annotated main
expression. Its type annotation and every constructor are checked explicitly. -/
def read [Codec α] (text : String) : Except String α := do
  let file ← (parseFile text).mapError toString
  unless file.imports.isEmpty do throw "Ixon data files cannot import code"
  let (type, value) ← match file.decls.toList, file.main with
    | [], some main => pure (main.ty, main.value)
    | [.defn declaration], none => do
      unless declaration.kw == .defn && !declaration.mods.isUnsafe &&
          !declaration.mods.isPartial && declaration.uparams.isEmpty do
        throw "expected a safe monomorphic data definition"
      pure (declaration.ty, declaration.value)
    | _, _ => throw "expected exactly one typed Ixon data value"
  expectType (α := α) type
  decode value

end Ix.Certified.Text
