import IxCC.Lir.Semantics

/-!
# The mapped test region

One region for generated programs and kernels, laid out as `Rt.Layout` lays out
the driver's region: the context register points 64 bytes in, with the
context fields below it and the free-list heads above it; objects follow.

```text
base          ctx = base+64      heap = base+0x400    ro = base+0x800   end = base+0x900
| ctx fields  | heads (r/w)      | heap (1 KiB, r/w)  | read-only       | unmapped
```

The `regionBase` field (`ctx − 24`) holds `heap`; generated functions load
their heap base from it. Every other byte starts as a seeded pattern, so
loads see varied data.
-/

namespace IxCCTests.Lir.Region

open IxCC

abbrev Word := X86.Word

def base : Word := 0x10000
def ctx : Word := base + 64
def heap : Word := base + 0x400
def heapSize : Nat := 0x400
def ro : Word := base + 0x800
def stop : Word := base + 0x900

/-- Context offsets. -/
def entrySpOff : Int := -64
def stackLimitOff : Int := -56
def regionBaseOff : Int := -24

def pattern (seed : UInt64) (address : Word) : UInt8 :=
  ((address * 0x9e3779b97f4a7c15 + seed) >>> 29).toUInt8

/-- The initial memory: `regionBase` holds `heap`, the rest is the pattern. -/
def initial (seed : UInt64) : X86.Memory :=
  let field := ctx - 24
  { bytes := fun a =>
      if field ≤ a && a < field + 8 then (heap >>> (8 * (a - field))).toUInt8 else pattern seed a
    readable := fun a => base ≤ a && a < stop
    writable := fun a => base ≤ a && a < ro }

/-- The words of the writable heap, for comparing final memories. -/
def heapWords (mem : X86.Memory) : List Word :=
  (List.range (heapSize / 8)).map fun i => mem.read64 (heap + UInt64.ofNat (8 * i))

/-- The context fields and the heads generated programs may write
(`[ctx − 64, ctx + 272)`), for comparing final memories. -/
def ctxWords (mem : X86.Memory) : List Word :=
  (List.range 42).map fun i => mem.read64 (base + UInt64.ofNat (8 * i))

end IxCCTests.Lir.Region
