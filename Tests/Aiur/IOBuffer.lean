module

public import Ix.Aiur.Semantics.BytecodeFfi

/-! The host advice-buffer append must preserve the old data and entry-map
representations as well as lookup behavior. These controls cover both a
consumed buffer and retained versions, without performance thresholds.
-/

public section

namespace AiurTests.IOBuffer

private structure Append where
  channel : Aiur.G
  key : Array Aiur.G
  payload : Array Aiur.G

/-- Reference implementation before the ownership optimization. -/
private def referenceExtend (buffer : Aiur.IOBuffer) (channel : Aiur.G)
    (key payload : Array Aiur.G) : Aiur.IOBuffer :=
  let arena := buffer.data.getD channel #[]
  let idx := arena.size
  let len := payload.size
  { buffer with
    data := buffer.data.insert channel (arena ++ payload)
    map := buffer.map.insert (channel, key) { idx, len } }

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def same (label : String) (actual expected : Aiur.IOBuffer) : IO Unit := do
  need s!"{label}: buffer equality differs" (actual == expected)
  need s!"{label}: data iteration or arena contents differ"
    (actual.data.toArray == expected.data.toArray)
  need s!"{label}: entry iteration or offsets differ"
    (actual.map.toArray == expected.map.toArray)

private def contents (buffer : Aiur.IOBuffer) (channel : Aiur.G)
    (key : Array Aiur.G) : Option (Array Aiur.G) := do
  let info ← buffer.map.get? (channel, key)
  let arena ← buffer.data.get? channel
  if info.idx + info.len > arena.size then none
  else some (arena.extract info.idx (info.idx + info.len))

private def applyAll (extend : Aiur.IOBuffer → Aiur.G → Array Aiur.G → Array Aiur.G → Aiur.IOBuffer)
    (initial : Aiur.IOBuffer) (ops : Array Append) : Aiur.IOBuffer :=
  ops.foldl (fun buffer op => extend buffer op.channel op.key op.payload) initial

private def checkSequence (label : String) (initial : Aiur.IOBuffer)
    (ops : Array Append) : IO Unit := do
  -- No intermediate actual buffers survive this fold: exercise the uniquely
  -- owned arena path in addition to the shared-history path below.
  let final := applyAll Aiur.IOBuffer.extend initial ops
  let expectedFinal := applyAll referenceExtend initial ops
  same s!"{label}/consumed" final expectedFinal
  let mut actual := initial
  let mut expected := initial
  let mut history : Array (Aiur.IOBuffer × Aiur.IOBuffer) := #[]
  for h : index in [:ops.size] do
    let op := ops[index]
    history := history.push (actual, expected)
    let before := actual.data.getD op.channel #[]
    actual := actual.extend op.channel op.key op.payload
    expected := referenceExtend expected op.channel op.key op.payload
    same s!"{label}/step {index}" actual expected
    need s!"{label}/step {index}: append changed the prior arena prefix"
      (actual.data.get? op.channel == some (before ++ op.payload))
    need s!"{label}/step {index}: wrong offset or length"
      (actual.map.get? (op.channel, op.key) == some { idx := before.size, len := op.payload.size })
    need s!"{label}/step {index}: key does not resolve to its latest payload"
      (contents actual op.channel op.key == some op.payload)
  same s!"{label}/retained result" actual final
  for index in [:history.size] do
    let (old, oldReference) := history[index]!
    same s!"{label}/history {index}" old oldReference
    let left := old.extend 0 #[101] #[102, 103]
    let right := old.extend 1 #[] #[]
    same s!"{label}/left branch {index}" left (referenceExtend oldReference 0 #[101] #[102, 103])
    same s!"{label}/right branch {index}" right (referenceExtend oldReference 1 #[] #[])
    same s!"{label}/history after branching {index}" old oldReference

private def channelChecks : IO Unit := do
  let ops : Array Append := #[
    { channel := 0, key := #[], payload := #[] },
    { channel := 1, key := #[7], payload := #[11, 12] },
    { channel := 2, key := #[7], payload := #[21] },
    { channel := 1, key := #[], payload := #[13, 14, 15] },
    { channel := 2, key := #[], payload := #[] },
    { channel := 1, key := #[7], payload := #[16] },
    { channel := 1, key := #[7], payload := #[] },
    { channel := 0, key := #[7], payload := #[31, 32] }]
  checkSequence "channels, duplicate keys and empty payloads" default ops
  let result := applyAll Aiur.IOBuffer.extend default ops
  need "an empty first append must register its empty channel and key"
    (contents result 0 #[] == some #[])
  need "duplicate-key replacement did not retain the appended bytes"
    (result.data.get? 1 == some #[11, 12, 13, 14, 15, 16] &&
      result.map.get? (1, #[7]) == some { idx := 6, len := 0 })
  need "equal keys on different channels interfere"
    (contents result 0 #[7] == some #[31, 32] && contents result 2 #[7] == some #[21])

private def collisionChecks : IO Unit := do
  -- All these channels share their low eight hash bits, so they collide
  -- throughout the small map's growth instead of relying on random keys.
  let channels := Id.run do
    let mut found : Array Aiur.G := #[]
    for i in [:65536] do
      let channel := Aiur.G.ofNat i
      if hash channel &&& 255 == 0 then found := found.push channel
      if found.size == 64 then break
    return found
  need "collision fixture did not find 64 distinct channels" (channels.size == 64)
  need "collision fixture hash prefixes differ" (channels.all (fun ch => hash ch &&& 255 == 0))
  let ops := Id.run do
    let mut result : Array Append := #[]
    for round in [:3] do
      for i in [:channels.size] do
        let channel := channels[(17 * i + round) % channels.size]?.getD 0
        let key := if round == 2 then #[] else #[7]
        let payload := if round == 1 && i % 5 == 0 then #[]
          else #[Aiur.G.ofNat round, Aiur.G.ofNat i]
        result := result.push { channel, key, payload }
    return result
  checkSequence "colliding channels and map growth" default ops

private def sharingChecks : IO Unit := do
  let initial := Aiur.IOBuffer.ofArrays #[(5, #[10, 20]), (8, #[])] #[]
  let initialOrder ← IO.lazyPure fun _ => initial.data.toArray
  let arena := initial.data.getD 5 #[]
  let ops : Array Append := #[
    { channel := 5, key := arena, payload := arena },
    { channel := 8, key := arena, payload := arena },
    { channel := 5, key := #[1], payload := #[] },
    { channel := 8, key := arena, payload := #[30] }]
  checkSequence "arena shared with keys, payloads and historical buffers" initial ops
  need "append mutated its caller's retained input arena"
    (arena == #[10, 20] && initial.data.toArray == initialOrder &&
      initial.data.get? 5 == some #[10, 20] && initial.data.get? 8 == some #[] &&
      initial.map.isEmpty)

def runSuite : IO UInt32 := do
  channelChecks
  collisionChecks
  sharingChecks
  IO.println "IOBuffer append reference, collision and persistence controls PASS"
  return 0

end AiurTests.IOBuffer

end
