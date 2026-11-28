import IxCC.X86.Driver
import IxCC.Rt.Readback
import IxCC.Sem.Entry
import IxCC.Sem.Transform

/-!
# The object's execution as a language

`X86.Linked` is an ELF object with its roots, run as the caller `X86.Driver`
describes runs it: on input `(r, ns)`,

1. a `Nat` argument the caller cannot pass (2^64 or more) fails with
   `natOverflow` (the wrapper's status 3 covers the rest above 2^63);
2. `cx_init` is called by its symbol (`ObjectEval.call`) on the region,
   its size and the stack budget, from the driver's first memory;
3. root `r` is called by its symbol on the arguments' words, from the bytes
   `cx_init` left, in the process's mapping;
4. the returned word is read back at the root's type (`Rt.readback`, fuel
   the region's size in words) over the part of the region Lir uses
   (`Driver.lirView`), as `Rt.Loaded` observes it; a root without a type
   observes nothing.

A status from either call is its outcome (`statusResult`: 1–3 resource
failures, 4 a trap). Roots are applied as at every level (`Sem.entryRun`):
exactly their parameter count calls them; fewer arguments give a value
with no observation; more call them on the first ones and are stuck.

`X86.LinkedAt` is the same with the root called from a call site of its own
(its own return address, flags and registers), as a caller with two call
sites makes the calls; `Linked` is its instance at the driver's own site
(`LinkedAt.run_site`).
-/

namespace IxCC.X86

open IxCC.Sem (Result Obs Lang ClockMono)

/-- A root of a linked object: its symbol, its parameter count and its
readback signature and type (`none`: read back as nothing). -/
structure Linked.Root where
  symbol : String
  params : Nat
  ty : Option (Rt.Sig × Rt.FoTy)

/-- An object with its roots, run by the driver. -/
structure Linked where
  object : ByteArray
  /-- `cx_init`'s symbol. -/
  init : String
  roots : List Linked.Root
  driver : Driver

namespace Linked

variable (L : Linked)

/-- A returned word read back at a root's type. -/
def observe (r : Root) (w : Word) (m : Memory) : Option Obs :=
  match r.ty with
  | some (sig, ty) => Rt.readback sig (L.driver.size.toNat / 8) (L.driver.lirView m) ty w
  | none => none

/-- `cx_init`'s call. -/
def initCall (k : Nat) : Result (Word × Memory) :=
  ObjectEval.call L.object L.init L.driver.base
    (L.driver.core [L.driver.size, L.driver.budget] L.driver.initBytes) L.driver.flags k

/-- A root's call on the arguments' words, from the bytes `bytes`. -/
def rootCall (r : Root) (ns : List Nat) (bytes : Word → UInt8) (k : Nat) : Result (Word × Memory) :=
  ObjectEval.call L.object r.symbol L.driver.base (L.driver.core (ns.map UInt64.ofNat) bytes) L.driver.flags k

/-- A call of a root on exactly its arguments (see the module note). -/
def call (r : Root) (ns : List Nat) (k : Nat) : Result (Option Obs) :=
  if ns.all (· < 2 ^ 64) then
    (L.initCall k).bind fun v => (L.rootCall r ns v.2.bytes k).map fun v' => L.observe r v'.1 v'.2
  else .resource .natOverflow

/-- A run of root `i.1` on the `Nat` inputs `i.2`, applied as at every level. -/
def run (i : Nat × List Nat) (k : Nat) : Result (Option Obs) :=
  match L.roots[i.1]? with
  | some r => Sem.entryRun r.params none (L.call r) i.2 k
  | none => .stuck

theorem call_mono (r : Root) (ns : List Nat) : ClockMono (L.call r ns) := by
  unfold call
  split
  · exact ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun _ =>
      ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun _ => ClockMono.const _
  · exact ClockMono.const _

end Linked

instance : Lang (Nat × List Nat) Linked where
  Val := Option Obs
  run := Linked.run
  mono L i := by
    unfold Linked.run
    split
    · exact Sem.entryRun_mono (fun ns => L.call_mono _ ns) _
    · exact ClockMono.const _
  obs := id

theorem Linked.lang_run (L : Linked) (i : Nat × List Nat) : Lang.run L i = L.run i := rfl

/-! ## The root from a call site of its own

A caller with two call sites (the standalone executable's shell calls
`cx_init` from one and the root from another) enters the root with its own
return address, flags and registers. `LinkedAt` is a linked object whose
root is called from `rootSite`: `cx_init` exactly as in `Linked`, the root
under `driver.withSite rootSite` (the same text, region, budget, stack
pointer and bytes). At the driver's own site it is `Linked`
(`LinkedAt.run_site`). -/

/-- A linked object whose root is called from its own site. -/
structure LinkedAt where
  linked : Linked
  rootSite : Driver.Site

namespace LinkedAt

variable (L : LinkedAt)

/-- The root call's driver. -/
def rootDriver : Driver := L.linked.driver.withSite L.rootSite

/-- A root's call on the arguments' words, from the bytes `bytes`, at the root's site. -/
def rootCall (r : Linked.Root) (ns : List Nat) (bytes : Word → UInt8) (k : Nat) : Result (Word × Memory) :=
  ObjectEval.call L.linked.object r.symbol L.rootDriver.base (L.rootDriver.core (ns.map UInt64.ofNat) bytes)
    L.rootDriver.flags k

/-- A call of a root on exactly its arguments: `Linked.call` with the root at its site. -/
def call (r : Linked.Root) (ns : List Nat) (k : Nat) : Result (Option Obs) :=
  if ns.all (· < 2 ^ 64) then
    (L.linked.initCall k).bind fun v => (L.rootCall r ns v.2.bytes k).map fun v' => L.linked.observe r v'.1 v'.2
  else .resource .natOverflow

/-- A run of root `i.1` on the `Nat` inputs `i.2`, applied as at every level. -/
def run (i : Nat × List Nat) (k : Nat) : Result (Option Obs) :=
  match L.linked.roots[i.1]? with
  | some r => Sem.entryRun r.params none (L.call r) i.2 k
  | none => .stuck

theorem call_mono (r : Linked.Root) (ns : List Nat) : ClockMono (L.call r ns) := by
  unfold call
  split
  · exact ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun _ =>
      ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun _ => ClockMono.const _
  · exact ClockMono.const _

end LinkedAt

instance : Lang (Nat × List Nat) LinkedAt where
  Val := Option Obs
  run := LinkedAt.run
  mono L i := by
    unfold LinkedAt.run
    split
    · exact Sem.entryRun_mono (fun ns => L.call_mono _ ns) _
    · exact ClockMono.const _
  obs := id

theorem LinkedAt.lang_run (L : LinkedAt) (i : Nat × List Nat) : Lang.run L i = L.run i := rfl

/-- **The one-site model is the two-site one at the driver's own site.** -/
theorem LinkedAt.run_site (L : Linked) (i : Nat × List Nat) (k : Nat) :
    Lang.run (⟨L, L.driver.site⟩ : LinkedAt) i k = Lang.run L i k := rfl

/-! ## Linked object with read-only `.rodata` static cells (DR1)

`X86.LinkedRodata` extends `X86.Linked` with an optional read-only `.rodata`
segment mapped at `rodataBase` (8-byte aligned, disjoint from the writable
region and stack). When the ELF object carries `.rodata`, both `cx_init` and
the root call execute with `.rodata` readable and non-writable (`writable =
false`), and readback observes `.rodata` alongside the Lir region. When the
ELF object has no `.rodata`, execution reduces identically to `X86.Linked`
(`LinkedRodata.rodata_none_eq`). -/

structure LinkedRodata where
  linked : Linked
  /-- Base address where the object's `.rodata` section is mapped read-only. -/
  rodataBase : Word

namespace LinkedRodata

variable (L : LinkedRodata)

/-- A call's core with `.rodata` mapped read-only when present in the object. -/
def coreWithRodata (args : List Word) (bytes : Word → UInt8) : Core :=
  let baseCore := L.linked.driver.core args bytes
  match ELFRead.rodata? L.linked.object with
  | none => baseCore
  | some rodata => { baseCore with memory := ELFRodata.mapRodata baseCore.memory L.rodataBase rodata }

/-- Lir/readback memory view: writable Lir region plus read-only `.rodata` (if any). -/
def readbackView (m : Memory) : Memory :=
  let baseView := L.linked.driver.lirView m
  match ELFRead.rodata? L.linked.object with
  | none => baseView
  | some rodata =>
      { bytes := m.bytes
        readable := fun a => baseView.readable a || ELFRodata.inRodata L.rodataBase rodata.size a
        writable := baseView.writable }

def observe (r : Linked.Root) (w : Word) (m : Memory) : Option Obs :=
  match r.ty with
  | some (sig, ty) => Rt.readback sig (L.linked.driver.size.toNat / 8) (L.readbackView m) ty w
  | none => none

def initCall (k : Nat) : Result (Word × Memory) :=
  ObjectEval.call L.linked.object L.linked.init L.linked.driver.base
    (L.coreWithRodata [L.linked.driver.size, L.linked.driver.budget] L.linked.driver.initBytes)
    L.linked.driver.flags k

def rootCall (r : Linked.Root) (ns : List Nat) (bytes : Word → UInt8) (k : Nat) :
    Result (Word × Memory) :=
  ObjectEval.call L.linked.object r.symbol L.linked.driver.base
    (L.coreWithRodata (ns.map UInt64.ofNat) bytes) L.linked.driver.flags k

def call (r : Linked.Root) (ns : List Nat) (k : Nat) : Result (Option Obs) :=
  if ns.all (· < 2 ^ 64) then
    (L.initCall k).bind fun v => (L.rootCall r ns v.2.bytes k).map fun v' => L.observe r v'.1 v'.2
  else .resource .natOverflow

def run (i : Nat × List Nat) (k : Nat) : Result (Option Obs) :=
  match L.linked.roots[i.1]? with
  | some r => Sem.entryRun r.params none (L.call r) i.2 k
  | none => .stuck

theorem call_mono (r : Linked.Root) (ns : List Nat) : ClockMono (L.call r ns) := by
  unfold call
  split
  · exact ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun _ =>
      ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun _ => ClockMono.const _
  · exact ClockMono.const _

/-- Read-only `.rodata` framing for `LinkedRodata.initCall`. -/
theorem initCall_preserves_rodata {rodata : ByteArray} {k : Nat} {val : Word} {mem' : Memory}
    (hparse : ELFRead.rodata? L.linked.object = some rodata)
    (h0 : L.rodataBase ≠ 0) (hal : L.rodataBase.toNat % 8 = 0)
    (hfit : L.rodataBase.toNat + rodata.size < 2 ^ 63)
    (hcall : L.initCall k = .ok (val, mem')) :
    ObjectEval.RodataLoaded L.linked.object L.rodataBase mem' := by
  unfold initCall coreWithRodata at hcall
  simp only [hparse] at hcall
  exact ObjectEval.call_preserves_rodata
    ⟨rodata, hparse, ELFRodata.mapRodata_mapped _ h0 hal hfit⟩ hcall

/-- Read-only `.rodata` framing for `LinkedRodata.rootCall`. -/
theorem rootCall_preserves_rodata {rodata : ByteArray} {r : Linked.Root} {ns : List Nat}
    {bytes : Word → UInt8} {k : Nat} {val : Word} {mem' : Memory}
    (hparse : ELFRead.rodata? L.linked.object = some rodata)
    (h0 : L.rodataBase ≠ 0) (hal : L.rodataBase.toNat % 8 = 0)
    (hfit : L.rodataBase.toNat + rodata.size < 2 ^ 63)
    (hcall : L.rootCall r ns bytes k = .ok (val, mem')) :
    ObjectEval.RodataLoaded L.linked.object L.rodataBase mem' := by
  unfold rootCall coreWithRodata at hcall
  simp only [hparse] at hcall
  exact ObjectEval.call_preserves_rodata
    ⟨rodata, hparse, ELFRodata.mapRodata_mapped _ h0 hal hfit⟩ hcall

/-- Backward compatibility: when the ELF object has no `.rodata` section,
`LinkedRodata.run` agrees identically with `Linked.run`. -/
theorem rodata_none_eq (hnone : ELFRead.rodata? L.linked.object = none)
    (i : Nat × List Nat) (k : Nat) :
    L.run i k = L.linked.run i k := by
  have hinit : ∀ k', L.initCall k' = L.linked.initCall k' := by
    intro k'; simp [initCall, Linked.initCall, coreWithRodata, hnone]
  have hroot : ∀ r ns bs k', L.rootCall r ns bs k' = L.linked.rootCall r ns bs k' := by
    intro r ns bs k'; simp [rootCall, Linked.rootCall, coreWithRodata, hnone]
  have hobs : ∀ r w m, L.observe r w m = L.linked.observe r w m := by
    intro r w m; simp [observe, Linked.observe, readbackView, hnone]
  have hcall : ∀ r ns k', L.call r ns k' = L.linked.call r ns k' := by
    intro r ns k'
    unfold call Linked.call
    split
    · simp only [hinit, hroot, hobs]
    · rfl
  unfold run Linked.run
  cases L.linked.roots[i.1]? with
  | none => rfl
  | some r =>
      dsimp only
      have hf : L.call r = L.linked.call r := funext fun ns => funext fun k' => hcall r ns k'
      rw [hf]

end LinkedRodata

instance : Lang (Nat × List Nat) LinkedRodata where
  Val := Option Obs
  run := LinkedRodata.run
  mono L i := by
    unfold LinkedRodata.run
    split
    · exact Sem.entryRun_mono (fun ns => L.call_mono _ ns) _
    · exact ClockMono.const _
  obs := id

end IxCC.X86
