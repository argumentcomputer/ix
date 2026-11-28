import Lean.Data.Json

/-! Ordered JSON for the corpus files.

`Lean.Json` keeps object keys sorted, but the frozen fixture files were
written by `jq`, which keeps insertion order. `OJson` keeps the order it is
built in and renders exactly as `jq` pretty-prints: two-space indentation,
`"key": value`, `[]` and `{}` for empty containers, the escapes `jq` uses, and
a final newline. The corpus builder writes every file it produces through it,
so a rebuild is byte-identical to the frozen pack. -/

namespace IxCCTests.Corpus

/-- JSON with ordered object fields. -/
inductive OJson where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : Array OJson)
  | obj (kvs : Array (String × OJson))
  deriving Inhabited, BEq

namespace OJson

private def hex4 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- A string literal as `jq` writes it. -/
def quote (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | '\r' => "\\r"
      | '\x08' => "\\b"
      | '\x0c' => "\\f"
      | c => if c.toNat < 0x20 || c.toNat == 0x7f then "\\u" ++ hex4 c.toNat else String.singleton c
  return out ++ "\""

private def pad (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Pretty-printed at indentation `ind`, without a final newline. -/
partial def renderAt (ind : Nat) : OJson → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => quote s
  | .arr xs =>
    if xs.isEmpty then "[]" else
    "[\n" ++ ",\n".intercalate (xs.toList.map fun x => pad (ind + 2) ++ renderAt (ind + 2) x) ++
      "\n" ++ pad ind ++ "]"
  | .obj kvs =>
    if kvs.isEmpty then "{}" else
    "{\n" ++ ",\n".intercalate (kvs.toList.map fun (k, v) => pad (ind + 2) ++ quote k ++ ": " ++
      renderAt (ind + 2) v) ++ "\n" ++ pad ind ++ "}"

/-- A whole file: pretty-printed, with a final newline (as `jq .`). -/
def render (j : OJson) : String := renderAt 0 j ++ "\n"

/-- From `Lean.Json` (object keys in `Lean.Json`'s sorted order; numbers
must be integers). -/
partial def ofJson : Lean.Json → Except String OJson
  | .null => pure .null
  | .bool b => pure (.bool b)
  | .num n =>
    if n.exponent == 0 then pure (.num n.mantissa) else throw s!"non-integer number {n}"
  | .str s => pure (.str s)
  | .arr xs => return .arr (← xs.mapM ofJson)
  | .obj kvs => return .obj (← kvs.toArray.mapM fun (k, v) => return (k, ← ofJson v))

/-- To `Lean.Json`, for reading back. -/
partial def toJson : OJson → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .num n => .num (Lean.JsonNumber.fromInt n)
  | .str s => .str s
  | .arr xs => .arr (xs.map toJson)
  | .obj kvs => Lean.Json.mkObj (kvs.toList.map fun (k, v) => (k, toJson v))

end OJson

/-- Object fields, dropping absent ones. -/
def OJson.fields (kvs : List (String × Option OJson)) : OJson :=
  .obj (kvs.filterMap fun (k, v) => v.map (k, ·)).toArray

def OJson.strs (xs : List String) : OJson := .arr (xs.map OJson.str).toArray
def OJson.nat (n : Nat) : OJson := .num n

end IxCCTests.Corpus
