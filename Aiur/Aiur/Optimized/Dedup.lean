import Aiur.Optimized.DedupCertificate

namespace Aiur.Optimized
namespace Dedup

structure Result (F : Type) where
  system : Circuit.System F
  representatives : List (String × String)
  classes : Array Nat
  deriving Repr, BEq

/-- The partitioning heuristic produces data; certification gives the semantic
guarantee, including recursive rules and fixed public entrypoints. -/
structure CheckedResult [Field F] [DecidableEq F] (source : Circuit.System F) (entries : List String)
    extends Result F where
  certificate : Certificate source system representatives entries

def certify [Field F] [DecidableEq F] (source : Circuit.System F) (entries : List String)
    (result : Result F) : Except String (CheckedResult source entries) :=
  if valid : Certificate source result.system result.representatives entries then
    .ok { toResult := result, certificate := valid }
  else .error "chip deduplication certificate failed"

/-- Call slots keep their order, payloads, results, and enables. Only the
destination names of function calls are replaced by candidate class indices. -/
def signature (system : Circuit.System F) (classes : Array Nat)
    (chip : Circuit.Chip F) : Circuit.Chip F :=
  { chip with
    name := ""
    sends := chip.sends.map fun send =>
      let index := system.chips.findIdx (·.name == send.channel)
      let destination := if index < system.chips.length then
        "function:" ++ toString (classes[index]?.getD index)
        else "map:" ++ send.channel
      { send with channel := destination }
  }

def refine [DecidableEq F] (system : Circuit.System F) (entries : List String)
    (classes : Array Nat) : Array Nat := Id.run do
  let chips := system.chips.toArray
  let signatures := chips.map (signature system classes)
  let mut result := #[]
  for i in List.range chips.size do
    let previous := (List.range i).find? fun j =>
      classes[i]? == classes[j]? && signatures[i]? == signatures[j]? &&
      !(entries.contains (chips[i]?.map Circuit.Chip.name |>.getD "")) &&
      !(entries.contains (chips[j]?.map Circuit.Chip.name |>.getD ""))
    result := result.push (match previous with
      | none => i
      | some j => result[j]?.getD j)
  return result

/-- Finite partition refinement compares regular unfoldings, including mutual
recursion. Each strict iteration splits at least one candidate class. -/
def partition [DecidableEq F] (system : Circuit.System F) (entries : List String) :
    Nat → Array Nat → Except String (Array Nat)
  | 0, _ => .error "chip partition refinement failed to stabilize"
  | fuel + 1, classes =>
      let next := refine system entries classes
      if next == classes then .ok classes else partition system entries fuel next

def identity (system : Circuit.System F) : Result F :=
  ⟨system, system.chips.map (fun chip => (chip.name, chip.name)),
    (List.range system.chips.length).toArray⟩

def compute [DecidableEq F] (system : Circuit.System F) (entries : List String) : Except String (Result F) := do
  let count := system.chips.length
  let classes ← partition system entries (count + 1) (Array.replicate count 0)
  unless classes.size == count && refine system entries classes == classes do
    throw "invalid chip partition"
  let mut representatives := []
  for (chip, index) in system.chips.zipIdx do
    let some representative := classes[index]? | throw "missing representative"
    let some target := system.chips[representative]? | throw "invalid representative"
    unless classes[representative]? == some representative do throw "non-idempotent representative"
    if entries.contains chip.name && chip.name != target.name then throw "entrypoint was merged"
    representatives := representatives ++ [(chip.name, target.name)]
  let rename := fun name => ((representatives.find? (·.1 == name)).map Prod.snd).getD name
  let chips := system.chips.zipIdx.filterMap fun (chip, index) =>
    if classes[index]? == some index then
      some { chip with sends := chip.sends.map fun send => { send with channel := rename send.channel } }
    else none
  return ⟨{ system with chips }, representatives, classes⟩

def run [Field F] [DecidableEq F] (system : Circuit.System F) (entries : List String) :
    Except String (CheckedResult system entries) := do
  certify system entries (← compute system entries)

end Dedup
end Aiur.Optimized
