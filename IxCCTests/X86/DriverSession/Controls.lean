import IxCC.X86.DriverSession

namespace IxCCTests.X86.DriverSession.Controls
open IxCC IxCC.X86 IxCC.X86.DriverSession
def driver : Driver := {
  base := 0, region := 65536, size := 4096, budget := 1024
  sp := 8192, ret := 12345, init := fun _ => 91, flags := {}, other := fun _ => 0 }
def session : Session := {
  linked := {
    object := ByteArray.empty, init := "cx_init", driver
    roots := [{ symbol := "cx_root", params := 1, ty := none }] } }
def isStuck {α : Type} : Sem.Result α → Bool
  | .stuck => true
  | _ => false
def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)
  IO.println ("PASS " ++ label)
def tests : IO Unit := do
  let bytes : Word → UInt8 := fun _ => 173
  check "missing root refuses" (isStuck (session.one ⟨1, [0]⟩ bytes 10))
  check "underapplication refuses" (isStuck (session.one ⟨0, []⟩ bytes 10))
  check "overapplication refuses" (isStuck (session.one ⟨0, [0,1]⟩ bytes 10))
  let overflow := match session.one ⟨0, [2^64]⟩ bytes 10 with
    | .resource .natOverflow => true
    | _ => false
  check "Nat overflow before empty object lookup" overflow
  check "actual empty object root refuses" (isStuck (session.one ⟨0, [0]⟩ bytes 10))
  check "actual empty object init refuses" (isStuck (session.run [] 10))
  check "actual empty object release refuses" (isStuck (session.dropCall 7 bytes 10))
  let empty := match session.runCalls [] bytes 0 with
    | .ok output => output.events.isEmpty && output.bytes 65536 == 173
    | _ => false
  check "empty continuation preserves bytes without init" empty
  check "high raw result word unchanged" (driver.regs [18446744073709551614] .rsi == 18446744073709551614)
  check "odd raw result word unchanged" (driver.regs [1] .rsi == 1)
  check "region byte unchanged by call setup" ((driver.mem bytes).bytes 65536 == 173)
  check "return slot receives caller return address" ((driver.mem bytes).read64 driver.sp == driver.ret)
end IxCCTests.X86.DriverSession.Controls
