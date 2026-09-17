import Compilatrix.Ixby.Runtime.Chunked.Execute
import Compilatrix.Ixby.Runtime.Execute
import CompilatrixTests.Ixby.RuntimeV2

namespace CompilatrixTests.Ixby.Chunked

open Compilatrix.Tools.Check
open Ix.Ixby
open Compilatrix.Ixby

private def same [BEq α] [BEq β] : Except α β → Except α β → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def vectors (values : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => values.flatMap fun value => (vectors values n).map (value :: ·)

private def comparePrimitive (limits : Limits) (primitive : Primitive)
    (args : List Runtime.Chunked.Value) : IO Unit := do
  let actual := (Runtime.Chunked.eval limits primitive args).map Runtime.Chunked.Value.toReference
  let expected := primitive.eval limits (args.map Runtime.Chunked.Value.toReference)
  need (same actual expected) s!"chunked primitive differs: {reprStr primitive}; {reprStr args}"

private def compareStep (limits : Limits) (program : Program) (state : Runtime.Chunked.State) : IO Unit := do
  need (same ((Runtime.Chunked.step limits program state).map Runtime.Chunked.Transition.toReference)
    (step limits program state.toReference)) s!"chunked transition differs: {reprStr state}"

def run : IO Nat := do
  let old := Runtime.Chunked.Builder.empty.append RuntimeV2.firstChunk
  let newest := old.append RuntimeV2.secondChunk
  let id : CtorId := { block := 23 }
  let values : List Runtime.Chunked.Value := [
    .scalar (.nat 0), .scalar (.nat (2 ^ 128)), .scalar (.word32 0xffffffff),
    .scalar (.field 7), .scalar (.extField ⟨3, 5⟩), .scalar (.str "aλ"),
    .scalar (.bool false), .scalar (.bytes #[]), .scalar (.bytes #[1, 2, 3, 4]),
    .scalar (.bytes (bytesLE 8 goldilocksModulus)), .erased,
    .ctor id #[.byteBuilder newest], .pap 0 #[.byteBuilder old],
    .array #[.byteBuilder old, .array #[.byteBuilder newest]],
    .byteBuilder Runtime.Chunked.Builder.empty, .byteBuilder old, .byteBuilder newest]
  let mut count := 0
  for primitive in Compilatrix.Ixby.Binary.primitives do
    for args in vectors values primitive.arity do
      comparePrimitive { natBits := 128, byteArrayBytes := 64, stringBytes := 2 } primitive args
      count := count + 1
    comparePrimitive {} primitive (List.replicate (primitive.arity + 1) (.byteBuilder newest))
    comparePrimitive {} primitive (List.replicate (primitive.arity + 2) (.scalar (.nat 0)))
    count := count + 2
  -- The old builder is still observable after append; all nested forms use
  -- the same immutable aliases, and byte limits see the cached full length.
  need (old.freeze == RuntimeV2.firstChunk) "old builder alias changed"
  need (newest.freeze == RuntimeV2.firstChunk ++ RuntimeV2.secondChunk) "builder chunk order changed"
  need ((newest.append #[]).freeze == newest.freeze) "empty builder append changed bytes"
  for capacity in #[0, 30, 31, 64, 65, 66] do
    for builder in #[old, newest] do
      for primitive in #[Primitive.byteBuilderLength, .byteBuilderFreeze] do
        for bits in #[0, 5, 6, 7, 128] do
          comparePrimitive { natBits := bits, byteArrayBytes := capacity } primitive [.byteBuilder builder]
          count := count + 1
      comparePrimitive { byteArrayBytes := capacity } .byteBuilderAppend
        [.byteBuilder builder, .scalar (.bytes #[])]
      count := count + 1
  let fixture := RuntimeV2.fixture
  for fuel in [:20] do
    need (same (Runtime.Chunked.execute fixture.limits fixture.program RuntimeV2.fixtureInput fuel)
      (execute fixture.limits fixture.program RuntimeV2.fixtureInput fuel)) s!"chunked fixture fuel {fuel}"
    count := count + 1
  let initial ← checked ((Runtime.Chunked.initialState fixture.limits fixture.program RuntimeV2.fixtureInput).mapError reprStr)
  for fuel in [:20] do
    for counter in #[0, 7, 2 ^ 64] do
      let actual := (Runtime.Chunked.runChunk fixture.limits fixture.program fuel initial counter).map Runtime.Chunked.chunkToReference
      let expected := Compilatrix.Ixby.Runtime.runChunk fixture.limits fixture.program fuel
        initial.toReference counter
      need (same actual expected) s!"chunked logical count {fuel}/{counter}"
      count := count + 1
  let program : Program := { constructors := #[⟨id, 1⟩], functions := #[
    { arity := 2, blocks := #[⟨2, .ret (.local 0)⟩] },
    { arity := 1, blocks := #[⟨1, .letOp (.copy (.local 0)) 1⟩, ⟨2, .ret (.local 1)⟩] }] }
  let frames : Array Runtime.Chunked.Frame := #[⟨0, 0, #[.byteBuilder old, .byteBuilder newest]⟩,
    ⟨1, 0, #[.array #[.byteBuilder newest]]⟩, ⟨1, 1, #[]⟩, ⟨2, 0, #[]⟩,
    ⟨0, 9, #[]⟩]
  let continuations : Array (Array Runtime.Chunked.Continuation) := #[#[],
    #[.resume frames[0]!], #[.apply #[.byteBuilder old]],
    #[.resume frames[1]!, .apply #[.byteBuilder newest]], #[.resume frames[2]!]]
  for continuation in continuations do
    for depth in #[0, 1, 2, 3] do
      let limits : Limits := { continuations := depth }
      for frame in frames do
        compareStep limits program ⟨.eval frame, continuation⟩
        count := count + 1
      for value in values ++ [.pap 0 #[], .pap 0 #[.byteBuilder old],
          .pap 0 #[.erased, .erased], .pap 100 #[]] do
        compareStep limits program ⟨.ret value, continuation⟩
        count := count + 1
        for args in #[#[], #[.byteBuilder old], #[.byteBuilder newest, .erased],
            #[.erased, .byteBuilder old, .byteBuilder newest]] do
          compareStep limits program ⟨.apply value args, continuation⟩
          count := count + 1
  -- Stress the representation whose eager prefix copies made the full image
  -- impractical. The expected bytes come from a flat index formula.
  let mut builder := Runtime.Chunked.Builder.empty
  for i in [:100000] do builder := builder.append #[i.toUInt8, (i >>> 8).toUInt8]
  need (builder.size == 200000) "builder stress cached length"
  let bytes := builder.freeze
  need (bytes == (Array.range 200000).map fun i =>
    if i % 2 == 0 then (i / 2).toUInt8 else (i / 512).toUInt8) "builder stress order"
  IO.println s!"chunked execution: {count} reference comparisons; exact fuel/counts, error ordering, nested aliases and 100000 chunks passed"
  return count

end CompilatrixTests.Ixby.Chunked
