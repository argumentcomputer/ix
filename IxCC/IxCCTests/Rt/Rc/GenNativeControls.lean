import IxCCTests.Exe.Session
import IxCC.Rt.Rc.Layout

/-!
# Native controls of the general-layout procedures, in a test executable

Independent controls of the general-layout RC procedures (`Rt.Rc.Gen`) emitted as one object
(`Emit.genProgram`: `cx_init`, allocation by layout for five layouts, the release `cx_rc_dec`, the
uniqueness test `cx_rc_is_unique`) and run natively in a test executable IxCC writes
(`IxCCTests.Exe.TestShell`, a 64 KiB region): the host writes cells and reads memory through the
session; the generated procedures do every allocation, release and test. The cases are those of
the interpreter controls (`GenControls`), with the expected words written out independently.
-/

namespace IxCCTests.Rt.Rc.GenNativeControls

open IxCCTests.Exe

/-- The exports, by the index the session calls them with. -/
def exports : List String :=
  ["cx_init", "cx_rc_alloc_40_0_3", "cx_rc_alloc_0_1_5", "cx_rc_alloc_254_1_7", "cx_rc_alloc_2_0_1",
   "cx_rc_alloc_0_0_1", "cx_rc_dec", "cx_rc_is_unique"]

def initK := 0
def alloc40 := 1
def allocBox := 2
def alloc254 := 3
def alloc2 := 4
def allocNone := 5
def dec := 6
def isUnique := 7

def mem : TestShell.Mem := { stack := 65536, region := 65536 }
def regionSize : Nat := 65536
def testBudget : Nat := 65536 - 4096

structure Env where
  s : Session.Session
  base : Nat
  assertions : IO.Ref Nat
  out : IO.Ref (Array String)

def require (e : Env) (c : Bool) (label : String) : IO Unit := do
  e.assertions.modify (· + 1)
  unless c do throw (IO.userError s!"FAIL {label}")

def readable (e : Env) (p n : Nat) : Bool := e.base + 16 ≤ p && p + n ≤ e.base + regionSize

def word (e : Env) (p : Nat) : IO Nat := do
  require e (readable e p 8) "bounded fixture read"
  return (← Session.readWord e.s p).toNat

def putword (e : Env) (p v : Nat) : IO Unit := do
  require e (readable e p 8) "bounded fixture write"
  Session.writeWord e.s p v

def contextAt (e : Env) (offset : Int) : Nat := Int.toNat (e.base + 64 + offset)
def ctxField (e : Env) (offset : Int) : IO Nat := do
  return (← Session.readWord e.s (contextAt e offset)).toNat
def head (e : Env) (cls : Nat) : IO Nat := ctxField e (8 * cls)

def invoke (e : Env) (fn a : Nat) (b : Nat := 0) : IO (Nat × Nat) := do
  let (rax, rdx, ok) ← Session.call e.s fn [e.base, a, b]
  require e ok "native callee-saved registers and stack pointer"
  return (rax.toNat, rdx.toNat)

def ok (e : Env) (fn arg : Nat) : IO Nat := do
  let (rax, rdx) ← invoke e fn arg
  require e (rax == 0) "native success status"
  return rdx

def status (e : Env) (fn arg expected : Nat) : IO Unit := do
  let (rax, _) ← invoke e fn arg
  require e (rax == expected) "native failure status"

/-- A dynamic header, written out: scan, class, tag, count `refs − 1`. -/
def hdr (scan cls tag refs : Nat) : Nat := scan + 256 * cls + 65536 * tag + 2 ^ 32 * (refs - 1)
/-- A static header (count word negative). -/
def staticHdr (scan tag : Nat) : Nat := scan + 65536 * tag + 2 ^ 32 * 0x80000000

/-- A cell at `p`: header, then the given words. -/
def cellAt (e : Env) (p h : Nat) (words : List Nat) : IO Unit := do
  putword e p h
  for (w, j) in words.zipIdx do putword e (p + 8 + 8 * j) w

/-- The words of class `c`'s free list (at most `n`). -/
def freeList (e : Env) (c : Nat) (n : Nat := 200) : IO (List Nat) := do
  let mut out := #[]
  let mut a ← head e c
  for _ in List.range n do
    if a == 0 then break
    out := out.push a
    a ← word e a
  return out.toList

def emit (e : Env) (line : String) : IO Unit := e.out.modify (·.push line)

/-- `cx_init`, then a limit `capacity` bytes past the first object. -/
def fresh (e : Env) (capacity : Nat) : IO Nat := do
  putword e (contextAt e (-48)) testBudget
  let (rax, _) ← invoke e initK regionSize testBudget
  require e (rax == 0) "cx_init succeeds"
  let start ← ctxField e (-40)
  require e (start % 64 == 0 && readable e start capacity) "object region"
  putword e (contextAt e (-32)) (start + capacity)
  for c in List.range' 1 71 do require e ((← head e c) == 0) "every head of classes 1-71 empty"
  return start

def allocation (e : Env) : IO Unit := do
  let start ← fresh e 4096
  let p ← ok e alloc40 0
  require e (p == start && (← ctxField e (-40)) == start + 384 && (← word e p) == hdr 40 34 3 1)
    "40-field cell: class 34, 384 bytes, header"
  let q ← ok e allocBox 0
  require e (q == start + 384 && (← ctxField e (-40)) == start + 400 && (← word e q) == hdr 0 2 5 1)
    "scalar-only box: class 2, 16 bytes"
  for j in List.range 40 do putword e (p + 8 + 8 * j) (2 * j + 1)
  discard <| ok e dec p
  require e ((← freeList e 34) == [p]) "released 40-field cell on class 34's list"
  let r ← ok e alloc40 0
  require e (r == p && (← head e 34) == 0 && (← ctxField e (-40)) == start + 400 &&
      (← word e r) == hdr 40 34 3 1) "pop from class 34's list leaves the bump"
  let bump ← ctxField e (-40)
  putword e (contextAt e (-32)) (bump + 2047)
  status e alloc254 0 1
  require e ((← ctxField e (-40)) == bump) "one byte short of the 256-word class fails heap"
  putword e (contextAt e (-32)) (bump + 2048)
  let w ← ok e alloc254 0
  require e (w == bump && (← ctxField e (-40)) == bump + 2048 && (← word e w) == hdr 254 44 7 1)
    "exact fit of the 256-word class"
  status e allocNone 0 4
  require e ((← ctxField e (-40)) == bump + 2048) "a field-less layout traps before any write"
  emit e "PASS allocation by layout: classes 34, 2 and 44, free-list pop, exact and short fit, refusal"

def release (e : Env) : IO Unit := do
  -- a 40-field parent with 40 unique two-field children, freed in field order
  let start ← fresh e 8192
  let kids ← (List.range 40).mapM fun _ => do
    let k ← ok e alloc2 0
    putword e (k + 8) 1
    putword e (k + 16) 3
    pure k
  let p ← ok e alloc40 0
  for (k, j) in kids.zipIdx do putword e (p + 8 + 8 * j) k
  discard <| ok e dec p
  require e ((← freeList e 34) == [p] && (← freeList e 3) == kids.reverse)
    "40 children and their parent recycled, children in field order"
  -- a scalar-only box whose scalar word is the address of a live cell
  let start ← fresh e 4096
  let live := start
  cellAt e live (hdr 2 3 1 1) [5, 7]
  let box := start + 64
  cellAt e box (hdr 0 2 9 1) [live]
  discard <| ok e dec box
  require e ((← freeList e 2) == [box] && (← freeList e 3) == [] && (← word e live) == hdr 2 3 1 1)
    "scalar-only box recycled, the cell its scalar names untouched"
  -- one scanned child and two scalar words that name live cells
  let start ← fresh e 4096
  cellAt e start (hdr 2 3 1 1) [5, 7]
  cellAt e (start + 64) (hdr 2 3 1 1) [5, 7]
  cellAt e (start + 128) (hdr 2 3 1 1) [1, 1]
  cellAt e (start + 192) (hdr 1 4 4 1) [start + 128, start, start + 64]
  discard <| ok e dec (start + 192)
  require e ((← freeList e 4) == [start + 192] && (← freeList e 3) == [start + 128] &&
      (← word e start) == hdr 2 3 1 1 && (← word e (start + 64)) == hdr 2 3 1 1)
    "scalar words never followed"
  -- a static child under a freed parent
  let start ← fresh e 4096
  cellAt e start (staticHdr 2 1) [5, 7]
  cellAt e (start + 64) (hdr 2 3 1 1) [start, 1]
  discard <| ok e dec (start + 64)
  require e ((← freeList e 3) == [start + 64] && (← word e start) == staticHdr 2 1)
    "static child not written"
  -- the widest constructor: 254 scanned fields and a scalar word, class 44
  let start ← fresh e 4096
  cellAt e start (hdr 254 44 1 1) ((List.range 254).map (fun _ => 1) ++ [start])
  discard <| ok e dec start
  require e ((← freeList e 44) == [start]) "254 scanned fields and a scalar word: class 44"
  -- a chain of 100 cells of one scanned field and one scalar word, released iteratively
  let start ← fresh e 4096
  for j in List.range 100 do
    let a := start + 32 * j
    cellAt e a (hdr 1 3 1 1) [if j + 1 = 100 then 1 else a + 32, a]
  discard <| ok e dec start
  require e ((← freeList e 3) == (List.range 100).map (start + 32 * ·))
    "chain of 100 cells with scalar words released iteratively, deepest first"
  -- shared and repeated children
  let start ← fresh e 4096
  cellAt e start (hdr 2 3 1 2) [7, 1]
  cellAt e (start + 64) (hdr 2 3 1 1) [start, start]
  discard <| ok e dec (start + 64)
  require e ((← freeList e 3) == [start + 64, start]) "repeated child freed once, then its parent"
  let start ← fresh e 4096
  cellAt e start (hdr 2 3 1 3) [7, 1]
  cellAt e (start + 64) (hdr 2 3 1 1) [start, start]
  discard <| ok e dec (start + 64)
  require e ((← freeList e 3) == [start + 64] && (← word e start) == hdr 2 3 1 1 &&
      (← word e (start + 8)) == 7) "child with an outside reference survives"
  emit e "PASS general release: field order, scalar words, static and shared children, depth 100"

def uniqueness (e : Env) : IO Unit := do
  let start ← fresh e 4096
  cellAt e start (hdr 2 3 1 1) [1, 1]
  cellAt e (start + 64) (hdr 2 3 1 2) [1, 1]
  cellAt e (start + 128) (staticHdr 2 1) [1, 1]
  cellAt e (start + 192) (hdr 2 3 1 0x80000000) [1, 1]
  let before ← Session.read e.s start 256
  require e ((← ok e isUnique 1) == 0) "immediate is not unique"
  require e ((← ok e isUnique start) == 1) "one reference is unique"
  require e ((← ok e isUnique (start + 64)) == 0) "two references are not unique"
  require e ((← ok e isUnique (start + 128)) == 0) "static cell is not unique"
  require e ((← ok e isUnique (start + 192)) == 0) "largest count is not unique"
  require e ((← Session.read e.s start 256).data == before.data) "the test writes nothing"
  -- in place: `3 :: l1` at start + 320 rewritten as `4 :: l1`, then unique and released
  cellAt e (start + 256) (hdr 2 3 1 2) [5, 1]
  cellAt e (start + 320) (hdr 2 3 1 1) [7, start + 256]
  let bump ← ctxField e (-40)
  cellAt e (start + 320) (hdr 2 3 1 1) [9, start + 256]
  require e ((← ok e isUnique (start + 320)) == 1) "rewritten cell is unique"
  discard <| ok e dec (start + 320)
  require e ((← freeList e 3) == [start + 320] && (← word e (start + 256)) == hdr 2 3 1 1 &&
      (← ctxField e (-40)) == bump) "rewritten cell released, its tail kept with one reference"
  emit e "PASS uniqueness test: immediate, unique, shared, static, largest count, no writes, in place"

/-- Run the controls in the test executable `exe`: the output lines and the assertion count. -/
def run (exe : System.FilePath) : IO (List String × Nat) := do
  Session.withSession exe (seconds := some 30) fun s => do
    let e : Env := { s, base := mem.base, assertions := ← IO.mkRef 0, out := ← IO.mkRef #[] }
    let region ← Session.read s e.base regionSize
    require e (region.data.all (· == 0)) "region zero-filled"
    require e mem.ok "guarded native stack"
    allocation e
    release e
    uniqueness e
    let n ← e.assertions.get
    emit e s!"PASS native general-layout procedures: {n} independent assertions"
    return ((← e.out.get).toList, n)

end IxCCTests.Rt.Rc.GenNativeControls
