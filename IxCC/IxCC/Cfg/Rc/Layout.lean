import IxCC.Rt.Rc.Gen.Procs
import IxCC.Lam.Syntax

/-! # Physical runtime function-table layout for native RC lowering

Shared by `Cfg.Rc.Native` and `Cfg.Rc.Inline` so the inline RC pass can locate
the wrapper and runtime procedure indices without importing the full native
lowering pipeline. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native

structure Layout where
  sourceCount : Nat
  ctors : List Lam.CtorInfo

def Layout.incWrapper (l : Layout) := l.sourceCount
def Layout.decWrapper (l : Layout) := l.sourceCount + 1
def Layout.allocWrapper (l : Layout) (i : Nat) := l.sourceCount + 2 + i
def Layout.incProc (l : Layout) := l.sourceCount + 2 + l.ctors.length
def Layout.decProc (l : Layout) := l.incProc + 1
def Layout.allocProc (l : Layout) (i : Nat) := l.incProc + 2 + i
def Layout.init (l : Layout) := l.incProc + 2 + l.ctors.length
def Layout.isUniqueProc (l : Layout) := l.init + 3
def Layout.resetWrapper (l : Layout) (i : Nat) := l.init + 4 + i
def Layout.resetUWrapper (l : Layout) (i : Nat) := l.init + 4 + l.ctors.length + i
def Layout.reuseWrapper (l : Layout) (i : Nat) := l.init + 4 + 2 * l.ctors.length + i
def Layout.reuseUWrapper (l : Layout) (i : Nat) := l.init + 4 + 3 * l.ctors.length + i

/-- Second argument is the gate-checked literal one; there is no incMany
implementation hidden here. The dummy result occupies only reserved registers. -/
def incrementWrapper (callee : Nat) : Lir.Func :=
  { name := "rc_marker_inc1", params := [0, 1], results := 1
    blocks := #[{ body := #[.call [] callee [.v 0]], term := .ret [.imm 1] }] }

def decrementWrapper (callee : Nat) : Lir.Func :=
  { name := "rc_marker_dec", params := [0], results := 1
    blocks := #[{ body := #[.call [] callee [.v 0]], term := .ret [.imm 1] }] }

/-- The reserved allocator result is never exposed before all fields have been
published. Field parameters retain their original registers across the call. -/
def allocationWrapper (callee fields : Nat) : Lir.Func :=
  { name := s!"rc_publish_{fields}", params := List.range fields, results := 1
    blocks := #[{
      body := (Lir.Stmt.call [fields] callee [] ::
        (List.range fields).map (fun i => .store .w64
          { base := some (.v fields), disp := Int.ofNat (8 * (i + 1)) } (.v i))).toArray
      term := .ret [.v fields] }] }

/-- Dynamic `reset` wrapper for constructor layout `lay` (class `cls`, `n = lay.nobj` scanned fields).
Parameters: `v0 = cell`, `v1 = tagged live-field bitmask` (`bit (j + 1) = 1` iff field `j` is live).
If `isUnique(v0) == 1`: loads old fields, writes the `resetShell` body (`hdr` + `n` immediates `1`),
releases every dead field (`bit (j + 1) == 0`), and returns `v0`.
Otherwise: increments every live field (`bit (j + 1) == 1`), releases `v0`, and returns `1` (`.erased`). -/
def mkResetWrapper (isUniqueProc incProc decProc : Nat) (lay : Rt.Rc.CellLayout) (cls : Nat) :
    Lir.Func :=
  let n := lay.nobj
  let hdr := Rt.Rc.dynamicHeader n cls lay.tag 1
  let sharedBase := 3 + 2 * n
  let b0 : Lir.Block :=
    { body := #[.call [2] isUniqueProc [.v 0]]
      term := .br .eq .w64 (.v 2) (.imm 1) ⟨1, []⟩ ⟨sharedBase, []⟩ }
  let loadOld : List Lir.Stmt :=
    (List.range n).map fun j =>
      .assign (3 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })
  let writeShell : List Lir.Stmt :=
    .store .w64 { base := some (.v 0), disp := 0 } (.imm hdr) ::
      (List.range n).map fun j =>
        .store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1)
  let b1 : Lir.Block :=
    { body := (loadOld ++ writeShell).toArray
      term := .jump ⟨2, []⟩ }
  let uniqueDecBlocks : List Lir.Block :=
    (List.range n).flatMap fun j =>
      let cur := 2 + 2 * j
      let bit := UInt64.ofNat (2 ^ (j + 1))
      [ { term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩ },
        { body := #[.call [] decProc [.v (3 + j)]], term := .jump ⟨cur + 2, []⟩ } ]
  let bUniqueRet : Lir.Block := { term := .ret [.v 0] }
  let sharedIncBlocks : List Lir.Block :=
    (List.range n).flatMap fun j =>
      let cur := sharedBase + 2 * j
      let bit := UInt64.ofNat (2 ^ (j + 1))
      [ { term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 1, []⟩ ⟨cur + 2, []⟩ },
        { body := #[
            .assign (3 + n + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) }),
            .call [] incProc [.v (3 + n + j)]],
          term := .jump ⟨cur + 2, []⟩ } ]
  let bSharedRet : Lir.Block :=
    { body := #[.call [] decProc [.v 0]]
      term := .ret [.imm 1] }
  { name := s!"rc_reset_{n}_{lay.tag}"
    params := [0, 1]
    results := 1
    blocks := ([b0, b1] ++ uniqueDecBlocks ++ [bUniqueRet] ++ sharedIncBlocks ++ [bSharedRet]).toArray }

/-- Static `@unique` `reset` wrapper: unconditional in-place `resetShell` rewrite without `isUnique`
or a shared fallback path. -/
def mkResetUWrapper (decProc : Nat) (lay : Rt.Rc.CellLayout) (cls : Nat) : Lir.Func :=
  let n := lay.nobj
  let hdr := Rt.Rc.dynamicHeader n cls lay.tag 1
  let loadOld : List Lir.Stmt :=
    (List.range n).map fun j =>
      .assign (2 + j) (.load .w64 .zero { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) })
  let writeShell : List Lir.Stmt :=
    .store .w64 { base := some (.v 0), disp := 0 } (.imm hdr) ::
      (List.range n).map fun j =>
        .store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.imm 1)
  let b0 : Lir.Block :=
    { body := (loadOld ++ writeShell).toArray
      term := .jump ⟨1, []⟩ }
  let decBlocks : List Lir.Block :=
    (List.range n).flatMap fun j =>
      let cur := 1 + 2 * j
      let bit := UInt64.ofNat (2 ^ (j + 1))
      [ { term := .br .tnz .w64 (.v 1) (.imm bit) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩ },
        { body := #[.call [] decProc [.v (2 + j)]], term := .jump ⟨cur + 2, []⟩ } ]
  let bRet : Lir.Block := { term := .ret [.v 0] }
  { name := s!"rc_reset_u_{n}_{lay.tag}"
    params := [0, 1]
    results := 1
    blocks := ([b0] ++ decBlocks ++ [bRet]).toArray }

/-- Dynamic `reuse` wrapper: if `v0` (slot) is a cell pointer (`v0 & 1 == 0`), rewrites header
and fields in place via `writeCell`; otherwise allocates a fresh cell via `allocProc`. -/
def mkReuseWrapper (allocProc : Nat) (lay : Rt.Rc.CellLayout) (cls : Nat) : Lir.Func :=
  let n := lay.nobj
  let hdr := Rt.Rc.dynamicHeader n cls lay.tag 1
  let reuseStores : List Lir.Stmt :=
    .store .w64 { base := some (.v 0), disp := 0 } (.imm hdr) ::
      (List.range n).map fun j =>
        .store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))
  let allocStores : List Lir.Stmt :=
    Lir.Stmt.call [n + 1] allocProc [] ::
      (List.range n).map fun j =>
        .store .w64 { base := some (.v (n + 1)), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))
  { name := s!"rc_reuse_{n}_{lay.tag}"
    params := List.range (n + 1)
    results := 1
    blocks := #[
      { term := .br .tnz .w64 (.v 0) (.imm 1) ⟨2, []⟩ ⟨1, []⟩ },
      { body := reuseStores.toArray, term := .ret [.v 0] },
      { body := allocStores.toArray, term := .ret [.v (n + 1)], cold := true }] }

/-- Static `@unique` `reuse` wrapper: unconditional in-place `writeCell` (zero branch, zero alloc). -/
def mkReuseUWrapper (lay : Rt.Rc.CellLayout) (cls : Nat) : Lir.Func :=
  let n := lay.nobj
  let hdr := Rt.Rc.dynamicHeader n cls lay.tag 1
  let reuseStores : List Lir.Stmt :=
    .store .w64 { base := some (.v 0), disp := 0 } (.imm hdr) ::
      (List.range n).map fun j =>
        .store .w64 { base := some (.v 0), disp := Int.ofNat (8 * (j + 1)) } (.v (j + 1))
  { name := s!"rc_reuse_u_{n}_{lay.tag}"
    params := List.range (n + 1)
    results := 1
    blocks := #[{ body := reuseStores.toArray, term := .ret [.v 0] }] }

def ctorIndex (l : Layout) (key : Key.CtorKey) : Option Nat :=
  (l.ctors.zipIdx.find? fun p => p.1.key == key).map (·.2)

end IxCC.Cfg.Rc.Native
