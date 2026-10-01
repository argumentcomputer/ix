import Std.Data.HashMap

/-! # Reading and summarising environment-check rows (untrusted tooling)

The row files `kernel-check-ixe` writes (one JSON object per line:
`address, names, kind, outcome, reason, micros, readMicros`) and the output
conventions of the summaries over them (`--report`, `--summary`, `--compare`,
`--paired`, in `Benchmarks.Kernel.CheckIxeReport` and
`Benchmarks.Kernel.CheckIxePaired`). These were Python scripts until
2026-10-01, and their outputs are kept byte for byte: a JSON value here keeps
its objects' key order (`Lean.Json` sorts keys), and it renders as Python's
`json.dumps(…, indent=n)` does (ASCII escapes, `", "`-free separators), with
floats as Python's `repr` writes them (the shortest decimal that reads back to
the same double) and fixed-point formats as `format(x, ".nf")` rounds them
(the exact binary value, half to even). Tooling only: not part of the
certified closure. -/

namespace Benchmarks.Kernel.CheckIxeRows

/-! ## Python's float formats -/

/-- A finite double as `(negative, significand, binary exponent)`: its value
is `significand * 2^exponent`. -/
def decode (f : Float) : Bool × Nat × Int :=
  let bits := f.toBits
  let neg := bits >>> 63 == 1
  let e := ((bits >>> 52) &&& 0x7ff).toNat
  let m := (bits &&& 0xfffffffffffff).toNat
  if e == 0 then (neg, m, -1074) else (neg, m + 2 ^ 52, (e : Int) - 1075)

def isFinite (f : Float) : Bool := ((f.toBits >>> 52) &&& 0x7ff) != 0x7ff

/-- `n / d` rounded to an integer, half to even. -/
def roundHalfEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d then q + 1 else if 2 * r < d then q else if q % 2 == 1 then q + 1 else q

/-- `format(f, f".{d}f")`. -/
def fixed (f : Float) (d : Nat) : String :=
  if !isFinite f then (if f.isNaN then "nan" else if f > 0 then "inf" else "-inf") else
  let (neg, m, e) := decode f
  -- the value times 10^d, rounded
  let n : Nat :=
    if e ≥ 0 then m * 2 ^ e.toNat * 10 ^ d else roundHalfEven (m * 10 ^ d) (2 ^ (-e).toNat)
  let digits := toString n
  let digits := String.ofList (List.replicate (d + 1 - min (d + 1) digits.length) '0') ++ digits
  let whole := String.ofList (digits.toList.take (digits.length - d))
  let frac := String.ofList (digits.toList.drop (digits.length - d))
  (if neg then "-" else "") ++ whole ++ (if d == 0 then "" else "." ++ frac)

/-- Python's `repr` layout of a decimal `0.digits × 10^decpt` (digits without
trailing zeros). -/
def reprLayout (neg : Bool) (digits : String) (decpt : Int) : String :=
  let sign := if neg then "-" else ""
  let len : Int := digits.length
  if decpt ≤ -4 || decpt > 16 then
    let exp := decpt - 1
    let rest := String.ofList (digits.toList.drop 1)
    let mant := String.ofList (digits.toList.take 1) ++ (if rest.isEmpty then "" else "." ++ rest)
    let e := toString exp.natAbs
    sign ++ mant ++ "e" ++ (if exp < 0 then "-" else "+") ++ (if e.length < 2 then "0" ++ e else e)
  else if decpt ≤ 0 then
    sign ++ "0." ++ String.ofList (List.replicate (-decpt).toNat '0') ++ digits
  else if decpt ≥ len then
    sign ++ digits ++ String.ofList (List.replicate (decpt - len).toNat '0') ++ ".0"
  else
    sign ++ String.ofList (digits.toList.take decpt.toNat) ++ "." ++
      String.ofList (digits.toList.drop decpt.toNat)

/-- A power of two `2^x` as a fraction `(numerator, denominator)`. -/
def pow2 (x : Int) : Nat × Nat := if x ≥ 0 then (2 ^ x.toNat, 1) else (1, 2 ^ (-x).toNat)

/-- A power of ten `10^x` as a fraction. -/
def pow10 (x : Int) : Nat × Nat := if x ≥ 0 then (10 ^ x.toNat, 1) else (1, 10 ^ (-x).toNat)

/-- Python's `repr` of a double: the shortest decimal that reads back to it
(of those, the closest), in `repr`'s layout. -/
def pyRepr (f : Float) : String :=
  if f.isNaN then "nan" else if !isFinite f then (if f > 0 then "inf" else "-inf") else
  let (neg, m, e) := decode f
  if m == 0 then (if neg then "-0.0" else "0.0") else
  -- v = m·2^e; in units u = 2^(e-2) the rounding interval is
  -- [4m-2, 4m+2]·u, or [4m-1, 4m+2]·u just above a power of two (the gap
  -- below is half the gap above), closed when m is even (reads tie to even)
  let (un, ud) := pow2 (e - 2)
  let loU : Nat := if m == 2 ^ 52 && e > -1074 then 4 * m - 1 else 4 * m - 2
  let hiU : Nat := 4 * m + 2
  let closed := m % 2 == 0
  let (vn, vd) := pow2 e
  let vn := m * vn
  -- k = floor(log10 v): v ≥ 10^k
  let ge (k : Int) : Bool := let (pn, pd) := pow10 k; vn * pd ≥ pn * vd
  let k : Int := Id.run do
    let mut k : Int := 0
    while ge (k + 1) do k := k + 1
    while !ge k do k := k - 1
    return k
  Id.run do
    for p in [1:18] do
      -- the closest p-digit decimal: D·10^(k+1-p), D = round(v·10^(p-1-k))
      let (tn, td) := pow10 ((p : Int) - 1 - k)
      let d := roundHalfEven (vn * tn) (vd * td)
      let (cn, cd) := pow10 (k + 1 - p)
      let cn := d * cn
      -- lo·u ≤ c ≤ hi·u, strictly when the interval is open
      let lhs := loU * un * cd
      let rhs := cn * ud
      let top := hiU * un * cd
      let inside := if closed then lhs ≤ rhs && rhs ≤ top else lhs < rhs && rhs < top
      if inside then
        let digits := toString d
        -- rounding may carry into a new digit (9.96 → 10)
        let decpt : Int := k + 1 + ((digits.length : Int) - p)
        let trimmed := String.ofList (digits.toList.reverse.dropWhile (· == '0')).reverse
        return reprLayout neg trimmed decpt
    return toString f

/-- `repr(float(s))` for a plain decimal `s` (`12.34`, `0.00`) of at most 15
significant digits, which reads to the double nearest it and back. -/
def reprDecimal (s : String) : Option String := do
  let (neg, body) := if s.startsWith "-" then (true, s.drop 1 |>.toString) else (false, s)
  let parts := body.splitOn "."
  let (whole, frac) ← match parts with
    | [w] => some (w, "")
    | [w, f] => some (w, f)
    | _ => none
  guard (!(whole ++ frac).isEmpty && (whole ++ frac).all Char.isDigit)
  let all := (whole ++ frac).toList
  let lead := (all.takeWhile (· == '0')).length
  let sig := all.drop lead
  let digits := String.ofList (sig.reverse.dropWhile (· == '0')).reverse
  guard (digits.length ≤ 15)
  if digits.isEmpty then return if neg then "-0.0" else "0.0"
  let decpt : Int := (whole.length : Int) - lead
  return reprLayout neg digits decpt

/-- Right-align `s` in `width` (Python's `{:>width}`, the default for numbers). -/
def rjust (width : Nat) (s : String) : String :=
  String.ofList (List.replicate (width - min width s.length) ' ') ++ s

/-- Left-align `s` in `width` (Python's `{:width}` for strings). -/
def ljust (width : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (width - min width s.length) ' ')

/-- Python's `s[:n]`. -/
def take (n : Nat) (s : String) : String := String.ofList (s.toList.take n)

/-! ## JSON with ordered objects -/

inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | float (f : Float)
  /-- A number read with a fraction or an exponent, kept as written. -/
  | num (lexeme : String)
  | str (s : String)
  | arr (xs : Array Value)
  | obj (kvs : Array (String × Value))
  deriving Inhabited

namespace Value

def get? (v : Value) (key : String) : Option Value :=
  match v with
  | .obj kvs => (kvs.find? (·.1 == key)).map (·.2)
  | _ => none

def str? : Value → Option String
  | .str s => some s
  | _ => none

def int? : Value → Option Int
  | .int n => some n
  | _ => none

def arr? : Value → Option (Array Value)
  | .arr xs => some xs
  | _ => none

/-- Python's dict semantics on construction: a repeated key keeps its first
position and takes the last value. -/
def mkObj (kvs : Array (String × Value)) : Value := Id.run do
  let mut out : Array (String × Value) := #[]
  for (k, v) in kvs do
    match out.findIdx? (·.1 == k) with
    | some i => out := out.set! i (k, v)
    | none => out := out.push (k, v)
  return .obj out

def hex4 (n : Nat) : String :=
  let h := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (4 - min 4 h.length) '0') ++ h

/-- `json.dumps` of a string (`ensure_ascii`). -/
def quote (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    let n := c.toNat
    out := out ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | '\x08' => "\\b"
      | '\x0c' => "\\f"
      | _ =>
        if 0x20 ≤ n && n < 0x7f then c.toString
        else if n < 0x10000 then "\\u" ++ hex4 n
        else
          let v := n - 0x10000
          "\\u" ++ hex4 (0xd800 + v / 0x400) ++ "\\u" ++ hex4 (0xdc00 + v % 0x400)
  return out ++ "\""

/-- `json.dumps(v, indent=indent, sort_keys=sortKeys)`. -/
partial def dumps (v : Value) (indent : Nat) (sortKeys : Bool := false) (level : Nat := 0) : String :=
  let pad (l : Nat) := "\n" ++ String.ofList (List.replicate (indent * l) ' ')
  match v with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int n => toString n
  | .float f =>
    if f.isNaN then "NaN" else if !isFinite f then (if f > 0 then "Infinity" else "-Infinity")
    else pyRepr f
  | .num s => s
  | .str s => quote s
  | .arr xs =>
    if xs.isEmpty then "[]" else
      "[" ++ ",".intercalate (xs.toList.map fun x => pad (level + 1) ++ dumps x indent sortKeys (level + 1))
        ++ pad level ++ "]"
  | .obj kvs =>
    if kvs.isEmpty then "{}" else
      let kvs := if sortKeys then kvs.qsort (fun a b => a.1 < b.1) else kvs
      "{" ++ ",".intercalate (kvs.toList.map fun (k, x) =>
          pad (level + 1) ++ quote k ++ ": " ++ dumps x indent sortKeys (level + 1))
        ++ pad level ++ "}"

end Value

/-! ## The parser (`json.loads`, on one line) -/

structure Parser where
  s : Array Char
  i : Nat := 0

abbrev ParseM := StateT Parser (Except String)

def peek : ParseM (Option Char) := do let p ← get; return p.s[p.i]?

def advance : ParseM Unit := modify fun p => { p with i := p.i + 1 }

def ws : ParseM Unit := do
  while (← peek).any (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r') do advance

def expect (c : Char) : ParseM Unit := do
  if (← peek) == some c then advance else throw s!"expected '{c}' at char {(← get).i}"

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : ParseM Nat := do
  let mut n := 0
  for _ in [0:4] do
    let some c ← peek | throw "truncated \\u escape"
    let some d := hexDigit c | throw "invalid \\u escape"
    n := n * 16 + d
    advance
  return n

def string : ParseM String := do
  expect '"'
  let mut out : Array Char := #[]
  repeat
    let some c ← peek | throw "unterminated string"
    advance
    if c == '"' then break
    if c == '\\' then
      let some e ← peek | throw "unterminated escape"
      advance
      match e with
      | '"' => out := out.push '"'
      | '\\' => out := out.push '\\'
      | '/' => out := out.push '/'
      | 'b' => out := out.push '\x08'
      | 'f' => out := out.push '\x0c'
      | 'n' => out := out.push '\n'
      | 'r' => out := out.push '\r'
      | 't' => out := out.push '\t'
      | 'u' =>
        let n ← hex4
        -- a surrogate pair is one character, as Python reads it
        if 0xd800 ≤ n && n < 0xdc00 then
          let p ← get
          if p.s[p.i]? == some '\\' && p.s[p.i + 1]? == some 'u' then
            advance; advance
            let lo ← hex4
            if 0xdc00 ≤ lo && lo < 0xe000 then
              out := out.push (Char.ofNat (0x10000 + (n - 0xd800) * 0x400 + (lo - 0xdc00)))
            else
              out := (out.push (Char.ofNat n)).push (Char.ofNat lo)
          else out := out.push (Char.ofNat n)
        else out := out.push (Char.ofNat n)
      | _ => throw s!"invalid escape \\{e}"
    else out := out.push c
  return String.ofList out.toList

def number : ParseM Value := do
  let start := (← get).i
  let mut isFloat := false
  if (← peek) == some '-' then advance
  while (← peek).any Char.isDigit do advance
  if (← peek) == some '.' then
    isFloat := true; advance
    while (← peek).any Char.isDigit do advance
  if (← peek).any (fun c => c == 'e' || c == 'E') then
    isFloat := true; advance
    if (← peek).any (fun c => c == '+' || c == '-') then advance
    while (← peek).any Char.isDigit do advance
  let p ← get
  let lexeme := String.ofList (p.s.extract start p.i).toList
  if lexeme.isEmpty || lexeme == "-" then throw s!"invalid number at char {start}"
  if isFloat then return .num lexeme
  match lexeme.toInt? with
  | some n => return .int n
  | none => throw s!"invalid number {lexeme}"

def literal (w : String) (v : Value) : ParseM Value := do
  for c in w.toList do expect c
  return v

partial def value : ParseM Value := do
  ws
  match ← peek with
  | some '{' =>
    advance; ws
    let mut kvs : Array (String × Value) := #[]
    if (← peek) == some '}' then advance; return .obj kvs
    repeat
      ws
      let k ← string
      ws; expect ':'
      let v ← value
      kvs := kvs.push (k, v)
      ws
      if (← peek) == some ',' then advance else break
    ws; expect '}'
    return Value.mkObj kvs
  | some '[' =>
    advance; ws
    let mut xs : Array Value := #[]
    if (← peek) == some ']' then advance; return .arr xs
    repeat
      xs := xs.push (← value)
      ws
      if (← peek) == some ',' then advance else break
    ws; expect ']'
    return .arr xs
  | some '"' => return .str (← string)
  | some 't' => literal "true" (.bool true)
  | some 'f' => literal "false" (.bool false)
  | some 'n' => literal "null" .null
  | some _ => number
  | none => throw "expecting value"

def parse (line : String) : Except String Value := do
  let (v, p) ← (do let v ← value; ws; return v).run { s := line.toList.toArray }
  if p.i < p.s.size then throw s!"extra data at char {p.i}"
  return v

/-! ## Rows -/

/-- Python's `str.splitlines()`, the lines of a row file. -/
def splitLines (text : String) : Array String := Id.run do
  let seps := ['\n', '\r', '\x0b', '\x0c', '\x1c', '\x1d', '\x1e', '\x85', ' ', ' ']
  let mut lines := #[]
  let mut cur : Array Char := #[]
  let chars := text.toList.toArray
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if seps.contains c then
      lines := lines.push (String.ofList cur.toList)
      cur := #[]
      if c == '\r' && chars[i + 1]? == some '\n' then i := i + 1
    else cur := cur.push c
    i := i + 1
  if !cur.isEmpty then lines := lines.push (String.ofList cur.toList)
  return lines

/-- A row's field as a string, an integer (`micros`), or the row's names. -/
def field (row : Value) (key : String) : String := ((row.get? key).bind Value.str?).getD ""

def micros (row : Value) (key : String := "micros") : Int := ((row.get? key).bind Value.int?).getD 0

def names (row : Value) : Array String :=
  (((row.get? "names").bind Value.arr?).getD #[]).filterMap Value.str?

/-- An insertion-ordered counter (Python's `Counter`). -/
structure Counter where
  keys : Array String := #[]
  counts : Std.HashMap String Nat := {}

def Counter.add (c : Counter) (k : String) (n : Nat := 1) : Counter :=
  match c.counts[k]? with
  | some m => { c with counts := c.counts.insert k (m + n) }
  | none => { keys := c.keys.push k, counts := c.counts.insert k n }

def Counter.get (c : Counter) (k : String) : Nat := c.counts.getD k 0

def Counter.items (c : Counter) : Array (String × Nat) := c.keys.map fun k => (k, c.get k)

/-- A stable sort by descending count (`Counter.most_common`, and `sorted`
with `key=-count`). -/
def byCountDesc (items : Array (String × Nat)) : Array (String × Nat) :=
  let indexed := items.mapIdx fun i x => (i, x)
  (indexed.qsort fun a b => a.2.2 > b.2.2 || (a.2.2 == b.2.2 && a.1 < b.1)).map (·.2)

/-- Python's `str(Path(p))`: empty and `.` components dropped. -/
def pathStr (p : String) : String :=
  let parts := (p.splitOn "/").filter (fun c => c != "" && c != ".")
  let body := "/".intercalate parts
  if p.startsWith "/" then "/" ++ body else if body.isEmpty then "." else body

/-- `Path(p).name`. -/
def pathName (p : String) : String := ((pathStr p).splitOn "/").getLastD ""

end Benchmarks.Kernel.CheckIxeRows
