import Batteries

open Batteries (RBMap)

structure Cronos where
  refs : RBMap String Nat compare
  data : RBMap String Nat compare
  deriving Inhabited

namespace Cronos

def new : Cronos :=
  default

def clock (c : Cronos) (tag : String) : IO Cronos := do
  let now ← IO.monoNanosNow
  match c.refs.find? tag with
  | none => return { c with refs := c.refs.insert tag now }
  | some ref => return {
    refs := c.refs.insert tag now,
    data := c.data.insert tag (now - ref) }

def nanoToSec (nanos : Nat) : Float :=
  Float.ofNat nanos / 1000000000

def summary (c : Cronos) : String :=
  let timings := c.data.foldl (init := "")
    fun acc tag time => s!"{acc}\n  {tag} | {nanoToSec time}s"
  s!"Timings:{timings}"


end Cronos
