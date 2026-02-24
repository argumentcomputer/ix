module
public import Std.Data.HashMap

public section

structure Cronos where
  refs : Std.HashMap String Nat
  data : Std.HashMap String Nat
  deriving Inhabited

namespace Cronos

def new : Cronos :=
  default

def clock (c : Cronos) (tag : String) : IO Cronos := do
  let now ← IO.monoNanosNow
  match c.refs.get? tag with
  | none => return { c with refs := c.refs.insert tag now }
  | some ref => return {
    refs := c.refs.insert tag now,
    data := c.data.insert tag (now - ref) }

def nanoToSec (nanos : Nat) : Float :=
  Float.ofNat nanos / 1000000000

def secToNano (s : Float) : Nat :=
  s.toUInt64.toNat * 1000000000

def tagSummary (c : Cronos) (tag: String): String := Id.run do
  match c.data.get? tag with
  | some time => s!"{tag} | {nanoToSec time}s"
  | none => s!"{tag} not logged"

def summary (c : Cronos) : String := Id.run do
  let mut str := ""
  for (tag, time) in c.data do
    str := str.append s!"\n  {tag} | {nanoToSec time}s"
  s!"Timings:{str}"

-- Get the average time in nanoseconds, returns NaN if no `data` entries
def mean (c : Cronos) : Float := Id.run do
  let mut sum : Nat := 0
  for (_, time) in c.data do
    sum := sum + time
  Float.ofNat sum / Float.ofNat c.data.size

end Cronos

end
