import Lean.Data.Json

/-! Declarative input and deterministic transformations for the Phase A corpus.
Templates are source data. Elaboration, including rejection, is a driver outcome;
the generator never silently removes a candidate because Lean might reject it. -/

namespace Tests.Ix.Compile.Corpus

open Lean

structure Shape where
  id : String
  family : String
  axes : Array (String × String) := #[]
  decl : String
  extras : Array (String × String) := #[]
  prelude : String := ""
  members : Array String := #[]
  mutualDefs : Array String := #[]
  suffix : String := ""
  deriving FromJson, ToJson, Inhabited

def defaultNames : List (Char × String) :=
  [('T', "T"), ('A', "A"), ('B', "B"), ('C', "C"), ('D', "D")]

def renamedNames : List (Char × String) :=
  [('T', "Zq"), ('A', "Kq"), ('B', "Lq"), ('C', "Mq"), ('D', "Nq")]

private def identChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Replace a complete `$T`-style token, never a substring of a longer name. -/
def substitute (text : String) (names : List (Char × String)) : String :=
  let rec go : List Char → List Char
    | '$' :: c :: rest =>
      if !rest.head?.any identChar then
        match names.lookup c with
        | some value => value.toList ++ go rest
        | none => '$' :: go (c :: rest)
      else '$' :: go (c :: rest)
    | c :: rest => c :: go rest
    | [] => []
  String.ofList (go text.toList)

def wrap (ns body : String) : String := s!"namespace {ns}\n{body}end {ns}\n"

/-- All permutations, identity first. Callers sort index vectors lexicographically
before assigning variant IDs. No random seed or ambient state. -/
def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    (permutations xs).flatMap fun ys =>
      (List.range (ys.length + 1)).map fun i => ys.take i ++ [x] ++ ys.drop i

def Shape.source (shape : Shape) (extras : Array String := #[]) (rename := false) : String :=
  wrap (s!"{if rename then "AY" else "AX"}.{shape.id}")
    (substitute (shape.decl ++ String.join extras.toList)
      (if rename then renamedNames else defaultNames))

def Shape.permuted (shape : Shape) (order : List Nat) (extras : Array String) : Except String String := do
  if order.mergeSort (· ≤ ·) != List.range shape.members.size then
    throw s!"{shape.id}: not a member permutation"
  let members ← order.mapM fun i =>
    match shape.members[i]? with
    | some member => .ok member
    | none => .error s!"{shape.id}: member {i} missing"
  let defs := if shape.mutualDefs.isEmpty then "" else
    "mutual\n" ++ String.intercalate "\n" shape.mutualDefs.toList.reverse ++ "end\n"
  return wrap s!"AX.{shape.id}" (substitute
    (shape.prelude ++ "mutual\n" ++ String.intercalate "\n" members ++ "end\n" ++
      defs ++ shape.suffix ++ String.join extras.toList) defaultNames)

end Tests.Ix.Compile.Corpus
