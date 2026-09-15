module
public import Ix.MultiStark.Verify.Protocol.Wire
public import Ix.MultiStark.Verify.Codec.Key

/-! Dense-v5 key grammar: u16 counts, no per-circuit prefix, sixteen
closed node tags and a 0xffff absent-index sentinel. The parser may read a
large encoding of a small constant, but the canonical writer grammar does
not permit it; canonical admission requires the exact same bytes on both
sides. Structural/graph/key approval is intentionally not a codec premise. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol.Wire

open Codec.Wire (ReadState WriteState)

def ParametersRead (state : ReadState) (value : Parameters) (final : ReadState) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6,
    NatRead 2 state value.logBlowup s1 ∧ NatRead 2 s1 value.capHeight s2 ∧ NatRead 2 s2 value.logFinalPolyLen s3 ∧
    NatRead 2 s3 value.maxLogArity s4 ∧ NatRead 2 s4 value.numQueries s5 ∧
    NatRead 2 s5 value.commitPowBits s6 ∧ NatRead 2 s6 value.queryPowBits final

def NodeBodyRead (tag : UInt8) (state : ReadState) (value : Node) (final : ReadState) : Prop :=
  match tag with
  | 0 => ∃ word, NatRead 2 state word final ∧ Node.const (Ix.Ixby.Goldilocks.reduce word) = value
  | 1 => ∃ field, FieldRead state field final ∧ Node.const field = value
  | 2 => ∃ index, NatRead 1 state index final ∧ Node.public index = value
  | 3 => Node.first = value ∧ state = final
  | 4 => Node.last = value ∧ state = final
  | 5 => Node.transition = value ∧ state = final
  | 6 => ∃ left middle right, NatRead 2 state left middle ∧ NatRead 2 middle right final ∧ Node.add left right = value
  | 7 => ∃ left middle right, NatRead 2 state left middle ∧ NatRead 2 middle right final ∧ Node.sub left right = value
  | 8 => ∃ left middle right, NatRead 2 state left middle ∧ NatRead 2 middle right final ∧ Node.mul left right = value
  | 9 => ∃ child, NatRead 2 state child final ∧ Node.neg child = value
  | 10 => ∃ column, NatRead 2 state column final ∧ Node.var .preprocessed false column = value
  | 11 => ∃ column, NatRead 2 state column final ∧ Node.var .preprocessed true column = value
  | 12 => ∃ column, NatRead 2 state column final ∧ Node.var .main false column = value
  | 13 => ∃ column, NatRead 2 state column final ∧ Node.var .main true column = value
  | 14 => ∃ column, NatRead 2 state column final ∧ Node.var .stage2 false column = value
  | 15 => ∃ column, NatRead 2 state column final ∧ Node.var .stage2 true column = value
  | _ => False

def NodeRead (state : ReadState) (value : Node) (final : ReadState) : Prop :=
  ∃ tag middle, ByteRead state tag middle ∧ NodeBodyRead tag middle value final

def LookupRead (state : ReadState) (value : Lookup) (final : ReadState) : Prop :=
  ∃ middle, NatRead 2 state value.multiplicity middle ∧ VectorRead 2 (NatRead 2) middle value.args final

def CircuitRead (state : ReadState) (value : Circuit) (final : ReadState) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6 s7,
    NatRead 2 state value.mainWidth s1 ∧ NatRead 2 s1 value.preprocessedWidth s2 ∧ NatRead 4 s2 value.preprocessedHeight s3 ∧
    NatRead 2 s3 value.maxConstraintDegree s4 ∧ NatRead 1 s4 value.lookupGroupSize s5 ∧
    VectorRead 2 NodeRead s5 value.nodes s6 ∧ VectorRead 2 (NatRead 2) s6 value.zeros s7 ∧
    VectorRead 2 LookupRead s7 value.lookups final

def IndexRead (state : ReadState) (value : Option Nat) (final : ReadState) : Prop :=
  ∃ word, NatRead 2 state word final ∧ (if word = 65535 then none else some word) = value

def KeyRead (state : ReadState) (value : Key) (final : ReadState) : Prop :=
  ∃ s1 s2 s3, ParametersRead state value.params s1 ∧ VectorRead 2 CircuitRead s1 value.circuits s2 ∧
    OptionRead (VectorRead 2 DigestRead) s2 value.preprocessed s3 ∧
    CountedRead value.circuits.size IndexRead s3 value.preprocessedIndices final

def ParametersWritten (value : Parameters) (state final : WriteState) : Prop :=
  ListWritten (NatWritten 2) value.words.toList state final

def NodeWritten : WriteRel Node
  | .const value, state, final =>
    if value.val < 65536 then ∃ middle, ByteWritten 0 state middle ∧ NatWritten 2 value.val middle final
    else ∃ middle, ByteWritten 1 state middle ∧ FieldWritten value middle final
  | .public index, state, final => ∃ middle, ByteWritten 2 state middle ∧ NatWritten 1 index middle final
  | .first, state, final => ByteWritten 3 state final
  | .last, state, final => ByteWritten 4 state final
  | .transition, state, final => ByteWritten 5 state final
  | .add left right, state, final =>
    ∃ s1 s2, ByteWritten 6 state s1 ∧ NatWritten 2 left s1 s2 ∧ NatWritten 2 right s2 final
  | .sub left right, state, final =>
    ∃ s1 s2, ByteWritten 7 state s1 ∧ NatWritten 2 left s1 s2 ∧ NatWritten 2 right s2 final
  | .mul left right, state, final =>
    ∃ s1 s2, ByteWritten 8 state s1 ∧ NatWritten 2 left s1 s2 ∧ NatWritten 2 right s2 final
  | .neg child, state, final => ∃ middle, ByteWritten 9 state middle ∧ NatWritten 2 child middle final
  | .var source next column, state, final =>
    let tag : UInt8 := match source, next with
      | .preprocessed, false => 10 | .preprocessed, true => 11
      | .main, false => 12 | .main, true => 13 | .stage2, false => 14 | .stage2, true => 15
    ∃ middle, ByteWritten tag state middle ∧ NatWritten 2 column middle final

def LookupWritten (value : Lookup) (state final : WriteState) : Prop :=
  ∃ middle, NatWritten 2 value.multiplicity state middle ∧ VectorWritten 2 (NatWritten 2) value.args middle final

def CircuitWritten (value : Circuit) (state final : WriteState) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6 s7,
    NatWritten 2 value.mainWidth state s1 ∧ NatWritten 2 value.preprocessedWidth s1 s2 ∧ NatWritten 4 value.preprocessedHeight s2 s3 ∧
    NatWritten 2 value.maxConstraintDegree s3 s4 ∧ NatWritten 1 value.lookupGroupSize s4 s5 ∧
    VectorWritten 2 NodeWritten value.nodes s5 s6 ∧ VectorWritten 2 (NatWritten 2) value.zeros s6 s7 ∧
    VectorWritten 2 LookupWritten value.lookups s7 final

def IndexWritten : WriteRel (Option Nat)
  | none, state, final => NatWritten 2 65535 state final
  | some index, state, final => index < 65535 ∧ NatWritten 2 index state final

def KeyWritten (value : Key) (state final : WriteState) : Prop :=
  value.preprocessedIndices.size = value.circuits.size ∧ ∃ s1 s2 s3,
    ParametersWritten value.params state s1 ∧ VectorWritten 2 CircuitWritten value.circuits s1 s2 ∧
    OptionWritten (VectorWritten 2 DigestWritten) value.preprocessed s2 s3 ∧
    CountedWritten IndexWritten value.preprocessedIndices s3 final

def CanonicalKey (limits : DecodeLimits) (bytes : Bytes) (value : Key) : Prop :=
  Decoded limits bytes KeyRead value ∧ Written limits (KeyWritten value) bytes

end MultiStark.Verify.Protocol.Wire
