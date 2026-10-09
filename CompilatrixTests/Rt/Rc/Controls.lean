import Compilatrix.Rt.Rc.Procs
import Compilatrix.Lir.Semantics

/-! Executable controls over actual Lir semantics, with literal
addresses/counts and independent expected free-list order. No native claim. -/
open Compilatrix
open Compilatrix.Rt.Rc.Procs

namespace CompilatrixTests.Rt.Rc.Controls
def context : UInt64 := 64
def memory : X86.Memory := {
  bytes := fun _ => 0
  readable := fun a => a < 8192
  writable := fun a => a < 8192 }
def put (m : X86.Memory) (a value : UInt64) : X86.Memory := m.write64 a value
def init : X86.Memory := put (put memory 24 1024) 32 8192
def cell (m : X86.Memory) (a : UInt64) (fields : List UInt64) (refs : Nat := 1) : X86.Memory :=
  let hdr := UInt64.ofNat (fields.length + 256 * (fields.length+1) + 65536 + 4294967296 * (refs-1))
  let m := put m a hdr
  (fields.zipIdx).foldl (fun m (w, i) => put m (a + UInt64.ofNat (8+8*i)) w) m
def run (f : Lir.Func) (args : List UInt64) (m : X86.Memory) (clock : Nat := 1000) : Lir.Outcome :=
  Lir.eval { funcs := #[f], main := 0 } clock args m context
def success (label : String) (o : Lir.Outcome) : IO (List UInt64 × X86.Memory) :=
  match o with
  | .ok r => pure r
  | .resource _ => throw (IO.userError (label ++ ": resource"))
  | .timeout => throw (IO.userError (label ++ ": timeout"))
  | .trap => throw (IO.userError (label ++ ": trap"))
  | .stuck => throw (IO.userError (label ++ ": stuck"))
def checkCase (name : String) (b : Bool) : IO Unit := do
  unless b do throw (IO.userError name)
  IO.println ("PASS " ++ name)

def tests : IO Unit := do
  let (vals, m) ← success "bump alloc" (run (alloc 2 1) [] init)
  checkCase "bump returns unique cell and advances exactly24" (vals == [1024] && m.read64 24 == 1048 && m.read64 1024 == 66306)
  let (_, exact) ← success "exact fit" (run (alloc 2 1) [] (put init 32 1048))
  checkCase "exact fit accepted" (exact.read64 24 == 1048)
  checkCase "one-byte short fails heap" (match run (alloc 2 1) [] (put init 32 1047) with | .resource .heap => true | _ => false)
  checkCase "nullary allocation declined" (match run (alloc 0 1) [] init with | .trap => true | _ => false)
  checkCase "class33 allocation declined" (match run (alloc 32 1) [] init with | .trap => true | _ => false)
  let (large, lm) ← success "class32" (run (alloc 31 1) [] init)
  checkCase "class32 alloc256" (large == [1024] && lm.read64 24 == 1280)
  let recycled := put (put (put init 88 2048) 2048 4096) 4096 0
  let (reused, rm) ← success "free pop" (run (alloc 2 7) [] recycled)
  checkCase "free pop preserves bump and installs new unique tag" (reused == [2048] && rm.read64 88 == 4096 && rm.read64 24 == 1024 && rm.read64 2048 == 459522)
  let unique := cell init 2048 [7, 1]
  let (_, im) ← success "inc unique" (run inc [2048] unique)
  checkCase "inc changes count only" (im.read64 2048 == 4295033602 && im.read64 2056 == 7 && im.read64 2064 == 1)
  let (_, dm) ← success "dec shared" (run dec [2048] im)
  checkCase "shared dec preserves full body" (dm.read64 2048 == unique.read64 2048 && dm.read64 2056 == 7 && dm.read64 88 == 0)
  let overflow := cell init 2048 [7, 1] (2^31)
  checkCase "inc max fails heap" (match run inc [2048] overflow with | .resource .heap => true | _ => false)
  let static := put unique 2048 9223372036854842114
  for f in [inc, dec] do
    let (_, sm) ← success "static" (run f [2048] static)
    checkCase "static header and payload untouched" (sm.read64 2048 == static.read64 2048 && sm.read64 2056 == 7 && sm.read64 88 == 0)
    let (_, scalar) ← success "immediate" (run f [1] init)
    checkCase "immediate leaves context untouched" (scalar.read64 24 == 1024 && scalar.read64 88 == 0)
  let dag := cell (cell init 2048 [7, 1] 2) 4096 [2048, 2048]
  let (_, freed) ← success "repeated child" (run dec [4096] dag)
  checkCase "repeated edge frees child once then parent" (freed.read64 88 == 4096 && freed.read64 4096 == 2048 && freed.read64 2048 == 0)
  let (again, fresh) ← success "recycle after drop" (run (alloc 2 1) [] freed)
  checkCase "same-region recycled allocation" (again == [4096] && fresh.read64 88 == 2048 && fresh.read64 24 == 1024)
  let shared := cell (cell init 2048 [7, 1] 3) 4096 [2048, 2048]
  let (_, retained) ← success "external child token" (run dec [4096] shared)
  checkCase "external child remains live unique" (retained.read64 88 == 4096 && retained.read64 4096 == 0 && retained.read64 2048 == 66306 && retained.read64 2056 == 7)
  checkCase "zero clock release times out" (match run dec [4096] dag 0 with | .timeout => true | _ => false)

end CompilatrixTests.Rt.Rc.Controls
