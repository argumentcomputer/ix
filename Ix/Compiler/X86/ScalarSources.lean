import Ix.Compiler.X86.ScalarSourceSelect
import Ix.Compiler.Coverage.Sources

/-! Synthetic Ixon programs with open scalar entry functions. Every constant
crosses the ordinary source identity gate, and the fixtures use the complete
source compiler. Runtime inputs are supplied separately. -/
namespace Ix.Compiler.X86.Scalar.Examples
open Ix.Compiler.Ixon (Address Constant)

structure Library where
  constants : List (Address × Constant)
  natBlock : Address
  natType : Address
  addition : Address
  subtraction : Address
  caseAlias : Address

private def definition (value typ : Ixon.Expr) (refs : Array Address) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing := #[], refs, univs := #[.zero] }

private def sharedLiteral (index : Nat) : Ixon.Expr :=
  .app (.lam .erased (.sort 0) (.nat index.toUInt64)) (.sort 0)

def library : Except String Library := do
  let nat : Ixon.Expr := .recur 0 #[]
  let stepType : Ixon.Expr := .all .many .shared nat (.all .many .shared nat nat)
  let thunkType : Ixon.Expr := .all .many .shared nat nat
  let recursor : Ixon.Recursor := {
    k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0, motives := 0, minors := 2
    typ := .all .many .shared nat (.all .many .shared stepType (.all .many .shared nat nat))
    rules := #[
      { fields := 0, rhs := .lam .many nat (.lam .many stepType (.var 1)) },
      { fields := 1, rhs := .lam .many nat (.lam .many stepType (.lam .many nat
        (.app (.app (.var 1) (.var 0))
          (.app (.app (.app (.recur 1 #[]) (.var 2)) (.var 1)) (.var 0))))) }] }
  let caseRecursor : Ixon.Recursor := {
    k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0, motives := 0, minors := 2
    typ := .all .many .shared thunkType (.all .many .shared thunkType (.all .many .shared nat nat))
    rules := #[
      { fields := 0, rhs := .lam .many thunkType (.lam .many thunkType (.app (.var 1) (sharedLiteral 0))) },
      { fields := 1, rhs := .lam .many thunkType (.lam .many thunkType (.lam .many nat (.app (.var 1) (.var 0)))) }] }
  let block ← Coverage.addressed {
    info := .muts #[.indc {
      isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
      ctors := #[
        { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := nat },
        { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1, typ := .all .many .shared nat nat }] },
      .recr recursor, .recr caseRecursor]
    sharing := #[], refs := #[ValidatedScalar.literalAddress 0], univs := #[.zero] }
  let project := fun info => Coverage.addressed { info, sharing := #[], refs := #[], univs := #[] }
  let natType ← project (.iPrj { idx := 0, block := block.1 })
  let successor ← project (.cPrj { idx := 0, cidx := 1, block := block.1 })
  let recursor ← project (.rPrj { idx := 1, block := block.1 })
  let caseAlias ← project (.rPrj { idx := 2, block := block.1 })
  let nat : Ixon.Expr := .ref 0 #[]
  let binary : Ixon.Expr := .all .many .shared nat (.all .many .shared nat nat)
  let addition ← Coverage.addressed (definition
    (.lam .many nat (.lam .many nat
      (.app (.app (.app (.ref 2 #[]) (.var 1))
        (.lam .many nat (.lam .many nat (.app (.ref 1 #[]) (.var 0))))) (.var 0))))
    binary #[natType.1, successor.1, recursor.1])
  let predecessor ← Coverage.addressed (definition
    (.lam .many nat (.app (.app (.app (.ref 1 #[]) (sharedLiteral 2))
      (.lam .many nat (.lam .many nat (.var 1)))) (.var 0)))
    (.all .many .shared nat nat) #[natType.1, recursor.1, ValidatedScalar.literalAddress 0])
  let subtraction ← Coverage.addressed (definition
    (.lam .many nat (.lam .many nat
      (.app (.app (.app (.ref 1 #[]) (.var 1))
        (.lam .many nat (.lam .many nat (.app (.ref 2 #[]) (.var 0))))) (.var 0))))
    binary #[natType.1, recursor.1, predecessor.1])
  return {
    constants := [block, natType, successor, recursor, caseAlias, addition, predecessor, subtraction]
    natBlock := block.1, natType := natType.1, addition := addition.1, subtraction := subtraction.1, caseAlias := caseAlias.1 }

def atomConstants : Atom → List Nat
  | .constant word => [word.toNat]
  | _ => []

def constantsOf : Expr → List Nat
  | .atom value => atomConstants value
  | .add left right | .sub left right => atomConstants left ++ atomConstants right
  | .letE value body => constantsOf value ++ constantsOf body
  | .branch scrutinee zero successor => atomConstants scrutinee ++ constantsOf zero ++ constantsOf successor
  | .call _ arguments => arguments.toList.flatMap atomConstants

private def bindingSource (literals : List Nat) (literalStart : Nat) : Source.Binding → Ixon.Expr
  | .var index => .var index.toUInt64
  | .constant word => sharedLiteral (literalStart + literals.idxOf word.toNat)

private def atomSource (bindings : Array Source.Binding) (literals : List Nat) (literalStart : Nat) : Atom → Ixon.Expr
  | .var index => bindingSource literals literalStart (bindings[index]?.getD (.var 0))
  | .constant word => bindingSource literals literalStart (.constant word)

private def expressionSource (literals : List Nat) (literalStart : Nat) : Array Source.Binding → Expr → Ixon.Expr
  | bindings, .atom value => atomSource bindings literals literalStart value
  | bindings, .add left right => .app (.app (.ref 1 #[]) (atomSource bindings literals literalStart left)) (atomSource bindings literals literalStart right)
  | bindings, .sub left right => .app (.app (.ref 2 #[]) (atomSource bindings literals literalStart left)) (atomSource bindings literals literalStart right)
  | bindings, .letE value body => .letE true (.ref 0 #[])
      (expressionSource literals literalStart bindings value) (expressionSource literals literalStart (Source.push bindings) body)
  | bindings, .branch scrutinee zero successor =>
      .app (.app (.app (.ref 3 #[]) (.lam .many (.ref 0 #[]) (expressionSource literals literalStart (Source.lift bindings) zero)))
        (.lam .many (.ref 0 #[]) (expressionSource literals literalStart (Source.lift bindings) successor)))
        (atomSource bindings literals literalStart scrutinee)
  | bindings, .call function arguments =>
      arguments.foldl (fun function argument => .app function (atomSource bindings literals literalStart argument))
        (.ref (4 + function).toUInt64 #[])

private def functionType : Nat → Ixon.Expr
  | 0 => .ref 0 #[]
  | n + 1 => .all .many .shared (.ref 0 #[]) (functionType n)

private def lambda : Nat → Ixon.Expr → Ixon.Expr
  | 0, body => body
  | n + 1, body => .lam .many (.ref 0 #[]) (lambda n body)

def source (name : String) (program : Program) : Except String Coverage.Source := do
  let library ← library
  let literals := (0 :: program.functions.toList.flatMap (fun function => constantsOf function.body)).eraseDups
  let mut constants := library.constants
  let mut entries : Array Address := #[]
  for function in program.functions do
    let refs := #[library.natType, library.addition, library.subtraction, library.caseAlias] ++ entries ++
      (literals.map ValidatedScalar.literalAddress).toArray
    let body := expressionSource literals (4 + entries.size) (Source.parameters function.parameters) function.body
    let entry ← Coverage.addressed (definition (lambda function.parameters body) (functionType function.parameters) refs)
    constants := constants ++ [entry]
    entries := entries.push entry.1
  let some root := entries[program.entry]? | throw "scalar fixture entry is missing"
  return { name, constants, root, literals, natBlock := some library.natBlock, expected := .scalar 0 false }

def addition : Program := { functions := #[⟨2, .add (.var 0) (.var 1)⟩], entry := 0 }
def subtraction : Program := { functions := #[⟨2, .sub (.var 0) (.var 1)⟩], entry := 0 }
def diamond : Program := {
  functions := #[⟨2, .letE (.branch (.var 0) (.atom (.var 1)) (.add (.var 0) (.var 1)))
    (.sub (.var 2) (.constant 1))⟩], entry := 0 }
def helperCalls : Program := {
  functions := #[⟨2, .add (.var 0) (.var 1)⟩, ⟨1, .sub (.var 0) (.constant 1)⟩,
    ⟨2, .letE (.call 0 #[.var 0, .var 1]) (.call 1 #[.var 2])⟩], entry := 2 }
def nested : Program := {
  functions := #[⟨0, .atom (.constant 7)⟩, ⟨2, .sub (.var 0) (.var 1)⟩,
    ⟨2, .branch (.var 0) (.call 0 #[]) (.letE (.call 1 #[.var 0, .var 1])
      (.branch (.var 2) (.add (.var 0) (.var 1)) (.atom (.var 2))))⟩], entry := 2 }

def families : List (String × Program) :=
  [("add", addition), ("sub", subtraction), ("diamond", diamond), ("helpers", helperCalls), ("nested", nested)]

end Ix.Compiler.X86.Scalar.Examples
