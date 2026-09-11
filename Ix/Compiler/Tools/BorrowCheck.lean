import Ix.Compiler.Tools.Check
import Blake3.Rust

/-! Independent JSON artifact inspection. This module imports no compiler,
borrow optimizer, ownership validator, or evaluator. IxIR₂ JSON remains a
diagnostic format; this checker is a regression oracle for the named gate. -/

namespace Ix.Compiler.Tools.BorrowCheck

open Lean Ix.Compiler.Tools.Check

def number (value : Json) (key : String) : IO Nat := do nat (← field value key)
def obj := Json.mkObj
def tagged (tag : String) (fields : List (String × Json)) : Json := obj [(tag, obj fields)]
def reg (id : Nat) : Json := tagged "reg" [("id", toJson id)]
def owned : Json := tagged "owned" [("world", toJson "shared")]
def borrowed : Json := tagged "borrowed" [("world", toJson "shared"), ("lender", toJson "caller")]
def scalar (n : Nat) : Json := tagged "lit" [("l", tagged "nat" [("n", toJson n)])]

def constructor (value : Json) : IO (String × Json) := do
  let [(tag, arguments)] ← pairs value | throw (IO.userError "expected one constructor tag")
  return (tag, arguments)

def replace (value : Json) (key : String) (replacement : Json) : IO Json := do
  let fields ← pairs value
  need (fields.any (·.1 == key)) s!"cannot replace missing field {key}"
  return obj (fields.map fun (name, old) => (name, if name == key then replacement else old))

def hash (bytes : ByteArray) : String :=
  (Blake3.Rust.hash bytes).val.data.foldl (fun output byte =>
    output ++ (if byte.toNat < 16 then "0" else "") ++ hexNat byte.toNat) ""

def hashField (value : Json) (payload key : String) : IO Unit := do
  let bytes ← checked (unhex (← strField value payload))
  need (hash bytes == (← strField value key)) s!"{payload}/{key} hash mismatch"

def entry (value : Json) : IO (String × Json) := do
  let #[owner, declaration] ← array value | throw (IO.userError "malformed declaration entry")
  return (← string owner, ← field (← field declaration "fn") "definition")

def function (program : Json) (owner : String) : IO Json := do
  if owner == "main" then return ← field program "main"
  let entries ← (← arrField program "declarations").mapM entry
  let some (_, definition) := entries.find? (·.1 == owner)
    | throw (IO.userError "missing addressed function")
  return definition

def target (summaries : Array Json) (owner : String) : IO String := do
  for summary in summaries do
    if (← strField summary "owner") == owner then return ← strField summary "borrowed"
  return owner

private def loan (loans : Array Bool) (atom : Json) : IO Bool := do
  if atom == toJson "erased" then return false
  let (tag, fields) ← constructor atom
  if tag == "reg" then return loans[← number fields "id"]?.getD false
  need (tag == "lit") "unknown atom"
  return false

private def redirect (summaries : Array Json) (term : Json) : IO Json := do
  let (tag, args) ← constructor term
  if tag != "call" && tag != "tailCall" then return term
  return obj [(tag, ← replace args "function" (toJson (← target summaries (← strField args "function"))))]

def variantBlock (summaries : Array Json) (block : Json) : IO Json := do
  need ((← arrField block "creditParams").isEmpty) "borrow variant retained credit parameters"
  let parameters ← arrField block "valueParams"
  let mut loans := parameters.map (· == owned)
  let mut rewritten := #[]
  for instruction in ← arrField block "instructions" do
    let (tag, args) ← constructor instruction
    match tag with
    | "move" =>
        loans := loans.push (← loan loans (← field args "value"))
        rewritten := rewritten.push instruction
    | "retainShared" =>
        let atom ← field args "target"
        let isLoan ← loan loans atom
        loans := loans.push isLoan
        rewritten := rewritten.push (if isLoan then tagged "move" [("value", atom)] else instruction)
    | "releaseShared" =>
        if !(← loan loans (← field args "target")) then rewritten := rewritten.push instruction
    | "call" =>
        loans := loans.push false
        rewritten := rewritten.push (← redirect summaries instruction)
    | "alloc" | "fetch" | "papp" | "apply" =>
        loans := loans.push false
        rewritten := rewritten.push instruction
    | "dropUnique" | "freeUnique" => rewritten := rewritten.push instruction
    | _ => throw (IO.userError "unsupported borrowed variant instruction")
  let term ← field block "terminator"
  let (tag, _) ← constructor term
  need (tag != "tailCallSelf" && tag != "branchCredit") "unsupported borrowed terminator"
  let block ← replace block "valueParams" (toJson (parameters.map fun cap => if cap == owned then borrowed else cap))
  let block ← replace block "instructions" (toJson rewritten)
  replace block "terminator" (← redirect summaries term)

def variant (summaries : Array Json) (definition : Json) : IO Json := do
  let signature ← field definition "signature"
  let ownedParam := obj [("world", toJson "shared"), ("passing", toJson "owned")]
  need ((← field signature "params") == toJson #[ownedParam] &&
    (← strField signature "result") == "shared") "invalid borrow summary signature"
  let signature ← replace signature "params"
    (toJson #[obj [("world", toJson "shared"), ("passing", toJson "borrowed")]])
  let signature ← replace signature "papSafe" (toJson false)
  let definition ← replace definition "signature" signature
  replace definition "blocks" (toJson (← (← arrField definition "blocks").mapM (variantBlock summaries)))

def wrapper (borrowedAddress : String) (definition : Json) : IO Json := do
  let block := obj [
    ("valueParams", toJson #[owned]), ("creditParams", toJson (#[] : Array Json)),
    ("instructions", toJson #[
      tagged "call" [("function", toJson borrowedAddress), ("args", toJson #[reg 0])],
      tagged "releaseShared" [("target", reg 0)]]),
    ("terminator", tagged "ret" [("value", reg 1)])]
  replace definition "blocks" (toJson #[block])

def declaration (owner : String) (definition : Json) : Json :=
  toJson #[toJson owner, tagged "fn" [("definition", definition)]]

def inspectRewrite (baseline rewritten : Json) (summaries : Array Json) : IO Unit := do
  let originals ← (← arrField baseline "declarations").mapM entry
  let owners ← summaries.mapM (strField · "owner")
  let labels ← summaries.mapM (strField · "borrowed")
  need (owners.toList.eraseDups.length == owners.size && labels.toList.eraseDups.length == labels.size)
    "duplicate borrow summary or label"
  need (labels.all fun label => !(originals.any (·.1 == label))) "borrow label aliases an owned entry"
  let mut expected := #[]
  for (owner, definition) in originals do
    let label ← target summaries owner
    expected := expected.push (declaration owner (← if label == owner then pure definition else wrapper label definition))
  for summary in summaries do
    let owner ← strField summary "owner"
    let label ← strField summary "borrowed"
    let bytes ← checked (unhex owner)
    need (hash ("compilatrix/borrowed-entry/1\x00".toUTF8 ++ bytes) == label) "borrow label preimage mismatch"
    expected := expected.push (declaration label (← variant summaries (← function baseline owner)))
  let rebuilt ← replace baseline "declarations" (toJson expected)
  need (rebuilt == rewritten) "borrowed graph differs from independent caller/callee reconstruction"

def programSize (program : Json) : IO Json := do
  let definitions ← (← arrField program "declarations").mapM (fun value => do return (← entry value).2)
  let mut blocks := 0
  let mut instructions := 0
  for definition in definitions.push (← field program "main") do
    let body ← arrField definition "blocks"
    blocks := blocks + body.size
    for block in body do instructions := instructions + (← arrField block "instructions").size
  return obj [("declarations", toJson definitions.size), ("blocks", toJson blocks),
    ("instructions", toJson instructions)]

end Ix.Compiler.Tools.BorrowCheck
