import Aiur.Optimized.Depth.Basic
import Aiur.Optimized.Physical

/-!
# Untrusted depth-pass planning

Computes the SCC partition of a physical system's call graph (Tarjan), ranks
the components so that callees rank lower, and classifies every call slot.
`Depth.Certified` re-checks everything soundness needs, so nothing here is
trusted; a wrong `exact` only makes honest proving fail.

Static exact/gap rule (conservative). An intra-SCC slot on channel `X` is
`exact` if it is the chip's only intra-SCC slot, or if it is the only slot on
`X` and every logical call on `X` lies in a control-flow scope exclusive with
every logical call on every other intra-SCC channel. Otherwise it is `gap`.
External depth is option E1 for every slot into a recursive chip of another SCC.
-/

namespace Aiur.Optimized.Depth

open Circuit

variable {F : Type}

/-- Callee chip indices per chip; the first chip of a name wins, as in `findChip?`. -/
def callGraph (source : System F) : Array (Array Nat) := Id.run do
  let mut index : Std.HashMap String Nat := {}
  for (chip, i) in source.chips.zipIdx do
    unless index.contains chip.name do index := index.insert chip.name i
  return (source.chips.map fun chip =>
    (chip.sends.filterMap fun send => index[send.channel]?).toArray).toArray

/-- Tarjan's algorithm. Component ids follow emission order, so every edge
between components goes from a higher id to a lower one. -/
def components (graph : Array (Array Nat)) : Array Nat := Id.run do
  let n := graph.size
  let unseen := n
  let mut index := Array.replicate n unseen
  let mut low := Array.replicate n 0
  let mut onStack := Array.replicate n false
  let mut stack : Array Nat := #[]
  let mut component := Array.replicate n 0
  let mut counter := 0
  let mut next := 0
  for root in [0:n] do
    if index[root]! != unseen then continue
    index := index.set! root counter
    low := low.set! root counter
    counter := counter + 1
    stack := stack.push root
    onStack := onStack.set! root true
    let mut calls : Array (Nat × Nat) := #[(root, 0)]
    while calls.size > 0 do
      let (v, i) := calls.back!
      let edges := graph[v]!
      if i < edges.size then
        calls := calls.set! (calls.size - 1) (v, i + 1)
        let w := edges[i]!
        if index[w]! == unseen then
          index := index.set! w counter
          low := low.set! w counter
          counter := counter + 1
          stack := stack.push w
          onStack := onStack.set! w true
          calls := calls.push (w, 0)
        else if onStack[w]! then
          low := low.set! v (min low[v]! index[w]!)
      else
        calls := calls.pop
        if calls.size > 0 then
          let (u, _) := calls.back!
          low := low.set! u (min low[u]! low[v]!)
        if low[v]! == index[v]! then
          let mut popping := true
          while popping do
            let w := stack.back!
            stack := stack.pop
            onStack := onStack.set! w false
            component := component.set! w next
            if w == v then popping := false
          next := next + 1
  return component

/-- Plan every chip. `calls name` lists a chip's logical calls (physical
channel, control-flow path), when known. -/
def plan (source : System F) (calls : String → Option (List (String × Path)))
    (limbs : List Nat := [16, 8]) : Config := Id.run do
  let graph := callGraph source
  let component := components graph
  let mut size : Array Nat := Array.replicate graph.size 0
  for c in component do size := size.modify c (· + 1)
  let mut index : Std.HashMap String Nat := {}
  for (chip, i) in source.chips.zipIdx do
    unless index.contains chip.name do index := index.insert chip.name i
  let recursive (i : Nat) : Bool := size[component[i]!]! > 1 || graph[i]!.contains i
  let mut plans := #[]
  let mut ranks := #[]
  for (chip, i) in source.chips.zipIdx do
    let intra (channel : String) : Bool :=
      match index[channel]? with
      | some k => component[k]! == component[i]!
      | none => false
    let intraSlots := chip.sends.filter (intra ·.channel)
    let logical := calls chip.name
    let exactOK (channel : String) : Bool :=
      intraSlots.length == 1 ||
        (intraSlots.filter (·.channel == channel)).length == 1 &&
          match logical with
          | none => false
          | some logical =>
              logical.all fun (x, p) => x != channel ||
                logical.all fun (y, q) => y == channel || !intra y || Path.exclusive p q
    let slots := chip.sends.map fun send =>
      match index[send.channel]? with
      | none => SlotKind.plain
      | some k =>
          if component[k]! == component[i]! then
            if exactOK send.channel then .exact else .gap
          else if recursive k then .external else .plain
    plans := plans.push (chip.name, { recursive := recursive i, slots := slots : ChipPlan })
    ranks := ranks.push (chip.name, component[i]!)
  return { limbs, plans := plans.toList, ranks := ranks.toList }

variable [Field F] [DecidableEq F]

/-- Logical calls of each physical chip from the optimized layouts, with
channels renamed to their physical representatives. -/
def logicalCalls {artifact : Artifact F} (physical : Physical.Prepared artifact)
    (name : String) : Option (List (String × Path)) :=
  (artifact.layouts.find? (·.chip.name == name)).map fun layout =>
    layout.logical.calls.toList.map fun call =>
      (physical.representative call.channel,
        ((layout.logical.scopes[call.scope]?).map (·.path)).getD [])

def planPrepared {artifact : Artifact F} (physical : Physical.Prepared artifact)
    (limbs : List Nat := [16, 8]) : Config :=
  plan physical.system (logicalCalls physical) limbs

end Aiur.Optimized.Depth
