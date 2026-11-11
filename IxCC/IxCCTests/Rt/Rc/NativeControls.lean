import IxCCTests.Exe.Session

/-!
# The native RC controls, in a test executable

Independent controls of the generated RC procedures (`cx_rc_alloc2`,
`cx_rc_alloc31`, `cx_rc_alloc0`, `cx_rc_alloc32`, `cx_rc_inc`, `cx_rc_dec`,
with `cx_init`), over a test executable IxCC writes of their object
(`IxCCTests.Exe.TestShell`): an 8 KiB region and a 64 KiB stack (budget
60 KiB); the host initializes fixture fields and reads complete values and
free chains through the session, the generated procedures perform every
allocation and release. Until X1 these controls were a C program linked with
the object; this is that program transcribed to Lean: every check of the C
program is one check here, in the same order (4,393), and its output lines are
the ones the C program printed. The check the C program made of its own
`mmap` of the region is a check that the region reads back zero-filled, and
the one of its guarded stack mapping a check that the test executable's
memory is one the test shell supports (`Mem.ok`).
-/

namespace IxCCTests.Rt.Rc.NativeControls

open IxCCTests.Exe

/-- The exports, by the index the session calls them with. -/
def exports : List String :=
  ["cx_init", "cx_rc_alloc2", "cx_rc_alloc31", "cx_rc_alloc0", "cx_rc_alloc32", "cx_rc_inc", "cx_rc_dec"]

def initK := 0
def alloc2 := 1
def alloc31 := 2
def alloc0 := 3
def alloc32 := 4
def inc := 5
def dec := 6

def mem : TestShell.Mem := { stack := 65536, region := 8192 }
def regionSize : Nat := 8192
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

/-- `ctx_field(offset)`: no check, as in C. -/
def ctxField (e : Env) (offset : Int) : IO Nat := do
  return (← Session.readWord e.s (contextAt e offset)).toNat

def invoke (e : Env) (fn a b : Nat) : IO (Nat × Nat) := do
  let (rax, rdx, ok) ← Session.call e.s fn [e.base, a, b]
  require e ok "native callee-saved registers and stack pointer"
  return (rax.toNat, rdx.toNat)

def ok (e : Env) (fn arg : Nat) : IO Nat := do
  let (rax, rdx) ← invoke e fn arg 0
  require e (rax == 0) "native success status"
  return rdx

def status (e : Env) (fn arg expected : Nat) : IO Unit := do
  let (rax, _) ← invoke e fn arg 0
  require e (rax == expected) "native failure status"

def fresh (e : Env) (capacity : Nat) : IO Nat := do
  putword e (contextAt e (-48)) testBudget
  let (rax, _) ← invoke e initK regionSize testBudget
  require e (rax == 0) "cx_init succeeds"
  let start ← ctxField e (-40)
  require e (start % 64 == 0 && readable e start capacity) "object region"
  putword e (contextAt e (-32)) (start + capacity)
  return start

def fields (e : Env) (p a b : Nat) : IO Unit := do
  require e ((← word e p) == 66306) "new unique scanned class3 tag1 header"
  putword e (p + 8) a
  putword e (p + 16) b

def listValue (e : Env) (p : Nat) (values : List Nat) : IO Unit := do
  let mut p := p
  for v in values do
    require e (p % 8 == 0 && p != 0) "list pointer alignment"
    let h ← word e p
    require e (h % 2 ^ 32 == 66306) "complete live list layout"
    require e (h / 2 ^ 32 < 0x80000000) "positive dynamic list count"
    require e ((← word e (p + 8)) == 2 * v + 1) "full list element and order"
    p ← word e (p + 16)
  require e (p == 1) "exact list length and nil"

def emit (e : Env) (line : String) : IO Unit := e.out.modify (·.push line)

def cycles (e : Env) : IO Unit := do
  let start ← fresh e 48
  for _ in List.range 50 do
    let a ← ok e alloc2 0
    fields e a 7 1
    let b ← ok e alloc2 0
    fields e b 15 a
    require e (a != b && (a == start || a == start + 24) && (b == start || b == start + 24))
      "exact two-cell address reuse"
    listValue e b [7, 3]
    discard <| ok e inc b
    require e ((← word e b) == 4295033602) "increment exact count"
    discard <| ok e dec b
    require e ((← word e b) == 66306) "shared decrement preserves live body"
    listValue e b [7, 3]
    listValue e a [3]
    discard <| ok e dec b
    require e ((← ctxField e 24) == b && (← word e b) == a && (← word e a) == 0)
      "completed parent then child free chain"
    require e ((← ctxField e (-40)) == start + 48) "same-region bump never reset or advanced"
  emit e "PASS 50 same-region two-cell cycles, full values, exact free-chain reuse"

def aliases (e : Env) : IO Unit := do
  for external in [false, true] do
    let start ← fresh e 48
    let child ← ok e alloc2 0
    fields e child 87 1
    discard <| ok e inc child
    if external then discard <| ok e inc child
    let parent ← ok e alloc2 0
    fields e parent child child
    discard <| ok e dec parent
    if external then
      listValue e child [43]
      require e ((← word e child) == 66306) "external alias remains unique"
      require e ((← ctxField e 24) == parent && (← word e parent) == 0) "only parent freed"
      discard <| ok e dec child
      require e ((← ctxField e 24) == child && (← word e child) == parent && (← word e parent) == 0)
        "external output drop reclaims both"
    else
      require e ((← ctxField e 24) == parent && (← word e parent) == child && (← word e child) == 0)
        "two repeated edges free child exactly once"
    require e ((← ctxField e (-40)) == start + 48) "alias case allocation count"
  emit e "PASS repeated edges and external shared-child preservation/release"

def deepList (e : Env) : IO Unit := do
  let start ← fresh e (64 * 24)
  let mut p := 1
  for i in List.range 64 do
    let a ← ok e alloc2 0
    fields e a (2 * i + 1) p
    p := a
  listValue e p ((List.range 64).map (63 - ·))
  discard <| ok e dec p
  let mut cursor ← ctxField e 24
  for i in List.range 64 do
    require e (cursor == start + 24 * (63 - i)) "deep free-chain exact order"
    cursor ← word e cursor
  require e (cursor == 0) "deep chain finite and all64 reclaimed"
  emit e "PASS iterative64-cell release and complete constructor values"

def boundaries (e : Env) : IO Unit := do
  let start ← fresh e 23
  status e alloc2 0 1
  require e ((← ctxField e (-40)) == start && (← ctxField e 24) == 0) "short allocation unchanged"
  putword e (contextAt e (-32)) (start + 24)
  let p ← ok e alloc2 0
  fields e p 7 1
  require e (p == start && (← ctxField e (-40)) == start + 24) "exact24-byte fit"
  discard <| ok e dec p
  require e ((← ok e alloc2 0) == p) "recycle succeeds at exhausted bump limit"
  fields e p 7 1
  putword e p 0x7fffffff00010302
  status e inc p 1
  require e ((← word e p) == 0x7fffffff00010302 && (← word e (p + 8)) == 7 && (← word e (p + 16)) == 1)
    "overflow preserves full live cell"
  putword e p 0x8000000000010302
  discard <| ok e inc p
  discard <| ok e dec p
  require e ((← word e p) == 0x8000000000010302 && (← word e (p + 8)) == 7 && (← word e (p + 16)) == 1)
    "static operations preserve full cell"
  let bump ← ctxField e (-40)
  let head ← ctxField e 24
  discard <| ok e inc 1
  discard <| ok e dec 1
  require e ((← ctxField e (-40)) == bump && (← ctxField e 24) == head) "immediate operations no-op"
  status e alloc0 0 4
  status e alloc32 0 4
  require e ((← ctxField e (-40)) == bump && (← ctxField e 24) == head) "unsupported layouts trap before mutation"
  putword e (contextAt e (-48)) 0
  status e inc p 2
  require e ((← word e p) == 0x8000000000010302) "stack refusal preserves cell"
  putword e (contextAt e (-48)) testBudget
  let start ← fresh e 256
  let p ← ok e alloc31 0
  require e (p == start && (← ctxField e (-40)) == start + 256 && (← word e p) == 73759)
    "class32 exact256-byte allocation"
  for i in List.range 31 do putword e (p + 8 + 8 * i) (2 * i + 1)
  discard <| ok e dec p
  require e ((← ctxField e 256) == p && (← word e p) == 0) "class32 reclamation"
  emit e "PASS exact/short heap, count overflow, static/immediate, layout and stack boundaries"

/-- Run the controls in the test executable `exe`: the output lines, as the
C program printed them, and the assertion count. -/
def run (exe : System.FilePath) : IO (List String × Nat) := do
  Session.withSession exe (seconds := some 30) fun s => do
    let e : Env := { s, base := mem.base, assertions := ← IO.mkRef 0, out := ← IO.mkRef #[] }
    let region ← Session.read s e.base regionSize
    require e (region.data.all (· == 0)) "region mmap"
    require e mem.ok "guarded native stack"
    cycles e
    aliases e
    deepList e
    boundaries e
    let n ← e.assertions.get
    emit e s!"PASS native H2 procedures: {n} independent assertions"
    return ((← e.out.get).toList, n)

end IxCCTests.Rt.Rc.NativeControls
