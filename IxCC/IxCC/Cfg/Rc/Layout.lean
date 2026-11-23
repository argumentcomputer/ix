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

def ctorIndex (l : Layout) (key : Key.CtorKey) : Option Nat :=
  (l.ctors.zipIdx.find? fun p => p.1.key == key).map (·.2)

end IxCC.Cfg.Rc.Native
