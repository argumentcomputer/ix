import Compilatrix.Rt.Rc.Procs
import Compilatrix.Lir.Semantics
import Compilatrix.Rt.Readback

open Compilatrix
open Compilatrix.Rt.Rc.Procs
namespace CompilatrixTests.Rt.Rc.DeepControls
def initial (limit : UInt64) : X86.Memory :=
  let m : X86.Memory := {
    bytes := fun _ => 0
    readable := fun a => a < 8192
    writable := fun a => a < 8192 }
  (m.write64 24 1024).write64 32 limit
def fill (m : X86.Memory) (p head tail : UInt64) : X86.Memory :=
  ((m.write64 p 66306).write64 (p+8) head).write64 (p+16) tail
def execute (f : Lir.Func) (args : List UInt64) (m : X86.Memory) : Lir.Outcome :=
  Lir.eval { funcs := #[f], main := 0 } 10000 args m 64
def ok (label : String) (result : Lir.Outcome) : IO (List UInt64 × X86.Memory) :=
  match result with
  | .ok answer => pure answer
  | _ => throw (IO.userError (label ++ ": did not return normally"))
def expect (name : String) (value : Bool) : IO Unit := do
  unless value do throw (IO.userError name)
  IO.println ("PASS " ++ name)
def listSig : Rt.Sig := { inds := [[[], [.nat, .ind 0]]] }
def want (xs : List Nat) : Sem.Obs :=
  xs.foldr (fun x rest => .ctor 1 [.nat x, rest]) (.ctor 0 [])

def tests : IO Unit := do
  let mut m := initial 8192
  let mut root : UInt64 := 1
  for j in List.range 64 do
    let p := UInt64.ofNat (1024+24*j)
    m := fill m p (UInt64.ofNat (2*j+1)) root
    root := p
  expect "deep input complete list readback" (Rt.readback listSig 256 m (.ind 0) root == some (want ((List.range 64).reverse)))
  let (_, released) ← ok "deep release" (execute dec [root] m)
  let mut head := released.read64 88
  for j in (List.range 64).reverse do
    unless head == UInt64.ofNat (1024+24*j) do throw (IO.userError "deep free-list order")
    head := released.read64 head
  expect "64-cell iterative release, exact unique free list" (head == 0)
  let mut arena := initial 1072
  for round in List.range 50 do
    let (a, aMem) ← ok "allocate child" (execute (alloc 2 1) [] arena)
    let [child] := a | throw (IO.userError "child result arity")
    let (b, bMem) ← ok "allocate parent" (execute (alloc 2 1) [] aMem)
    let [parent] := b | throw (IO.userError "parent result arity")
    unless parent != child do throw (IO.userError "live allocation alias")
    let occupied := fill (fill bMem child (UInt64.ofNat (2*round+1)) 1)
      parent (UInt64.ofNat (2*(round+100)+1)) child
    unless Rt.readback listSig 32 occupied (.ind 0) parent == some (want [round+100, round]) do
      throw (IO.userError "recycled full list value mismatch")
    unless (match execute (alloc 2 1) [] occupied with | .resource .heap => true | _ => false) do
      throw (IO.userError "bounded region did not exhaust")
    let (_, dropped) ← ok "release two" (execute dec [parent] occupied)
    unless dropped.read64 24 == 1072 && dropped.read64 88 == parent &&
        dropped.read64 parent == child && dropped.read64 child == 0 do
      throw (IO.userError "recycled capacity/free-list mismatch")
    arena := dropped
  expect "50 same-region two-cell cycles preserve values, exhaust and reclaim" (arena.read64 24 == 1072)

end CompilatrixTests.Rt.Rc.DeepControls
