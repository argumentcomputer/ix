import Aiur.Optimized.Depth.Basic
import Aiur.Optimized.Physical

/-!
# Untrusted depth-pass planning

Computes the SCC partition of a physical system's call graph (Tarjan), ranks
the components so that callees rank lower, and classifies every call slot.
`Depth.Certified` re-checks everything soundness needs, so nothing here is
trusted; a wrong `exact` only makes honest proving fail.

Static exact/gap rule (`N9b`, conservative). An intra-SCC slot on channel `X` is
`exact` if:
* it is the chip's only intra-SCC slot; or
* it is the only slot on `X` and every logical call on `X` lies in a
  control-flow scope exclusive with every logical call on every other intra-SCC
  channel; or
* every logical call on `X` is pairwise exclusive with every other intra-SCC
  logical call (including other calls on `X`), even when unmerged across
  multiple physical slots; or
* per-slot exclusivity: every logical call merged into that specific physical
  send slot lies in a control-flow scope exclusive with every other intra-SCC
  logical call in the chip.

Otherwise it is `gap`. External depth is option E1 for every slot into a
recursive chip of another SCC.
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

/-- Plan every chip, with optional per-physical-send logical-call origins
(`slotCalls name`, indexed by physical send position, each entry listing the
`(logicalCallIndex, path)` pairs merged into that physical send). -/
def planWithSlots (source : System F)
    (calls : String → Option (List (String × Path)))
    (slotCalls : String → Option (List (List (Nat × Path))))
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
    let indexed := logical.map List.zipIdx
    let slotGroups := slotCalls chip.name
    let exactChannelOK (channel : String) : Bool :=
      intraSlots.length == 1 ||
        match indexed with
        | none => false
        | some indexed =>
            -- Per-call pairwise exclusivity across all intra-SCC calls
            -- (covers multiple unmerged mutually-exclusive slots on `channel`).
            (indexed.all fun ((x, p), idx) => x != channel ||
              indexed.all fun ((y, q), j) => j == idx || !intra y || Path.exclusive p q) ||
            -- Single physical slot on `channel` exclusive with all other intra-SCC channels.
            ((intraSlots.filter (·.channel == channel)).length == 1 &&
              indexed.all fun ((x, p), _) => x != channel ||
                indexed.all fun ((y, q), _) => y == channel || !intra y || Path.exclusive p q)
    let exactSlotOK (slotIdx : Nat) (channel : String) : Bool :=
      exactChannelOK channel ||
        match indexed, slotGroups with
        | some indexed, some groups =>
            match groups[slotIdx]? with
            | some myCalls =>
                !myCalls.isEmpty &&
                  myCalls.all fun (idx, p) =>
                    indexed.all fun ((y, q), j) => j == idx || !intra y || Path.exclusive p q
            | none => false
        | _, _ => false
    let slots := chip.sends.zipIdx.map fun (send, slotIdx) =>
      match index[send.channel]? with
      | none => SlotKind.plain
      | some k =>
          if component[k]! == component[i]! then
            if exactSlotOK slotIdx send.channel then .exact else .gap
          else if recursive k then .external else .plain
    plans := plans.push (chip.name, { recursive := recursive i, slots := slots : ChipPlan })
    ranks := ranks.push (chip.name, component[i]!)
  return { limbs, plans := plans.toList, ranks := ranks.toList }

/-- Plan every chip. `calls name` lists a chip's logical calls (physical
channel, control-flow path), when known. -/
def plan (source : System F) (calls : String → Option (List (String × Path)))
    (limbs : List Nat := [16, 8]) : Config :=
  planWithSlots source calls (fun _ => none) limbs

variable [Field F] [DecidableEq F]

private structure SlotOrigin where
  channel : String
  result : WireValue Witness
  argShapes : List (Ty × Nat)
  calls : List (Nat × Path)

private def SlotOrigin.compatible (left right : SlotOrigin) : Bool :=
  left.channel == right.channel && left.result == right.result &&
    left.argShapes == right.argShapes

private def SlotOrigin.exclusive (left right : SlotOrigin) : Bool :=
  left.calls.all fun (_, p) => right.calls.all fun (_, q) => Path.exclusive p q

private def insertSlotOrigin (right : SlotOrigin) : List SlotOrigin → List SlotOrigin
  | [] => [right]
  | left :: rest =>
      if left.compatible right && left.exclusive right &&
          rest.all (fun other => right.exclusive other) then
        { left with calls := left.calls ++ right.calls } :: rest
      else
        left :: insertSlotOrigin right rest

/-- Per-physical-send logical call origins, mirroring `LookupMerging.mergeCalls`
and fail-closed against `chip.sends` length and physical channels. -/
def logicalSlotCalls {artifact : Artifact F} (physical : Physical.Prepared artifact)
    (name : String) : Option (List (List (Nat × Path))) := do
  let chip ← physical.system.findChip? name
  let layout ← artifact.layouts.find? (·.chip.name == name)
  let logicalList := layout.logical.calls.toList
  let pathOf (scope : ScopeId) : Path := ((layout.logical.scopes[scope]?).map (·.path)).getD []
  let chipChannels := chip.sends.map (·.channel)
  if chip.sends.length == logicalList.length then
    if logicalList.map (fun c => physical.representative c.channel) == chipChannels then
      return logicalList.zipIdx.map fun (c, idx) => [(idx, pathOf c.scope)]
    else none
  else
    let initial : List SlotOrigin := logicalList.zipIdx.map fun (c, idx) =>
      { channel := c.channel
        result := c.result.map layout.layout.column
        argShapes := c.args.map fun w => (w.type, w.words.length)
        calls := [(idx, pathOf c.scope)] }
    let merged := initial.foldl (fun acc s => insertSlotOrigin s acc) []
    if merged.length == chip.sends.length &&
        merged.map (fun s => physical.representative s.channel) == chipChannels then
      return merged.map (·.calls)
    else none

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
  planWithSlots physical.system (logicalCalls physical) (logicalSlotCalls physical) limbs

end Aiur.Optimized.Depth
