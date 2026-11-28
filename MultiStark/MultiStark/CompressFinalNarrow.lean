import MultiStark.BN.KzgPackedTerminal
import MultiStark.CompressFinal
import Blake3.Rust

/-! Terminal Aiur relation over the narrow last BN stage of a packed-SHPLONK
chain (`IXAUKG01` policy), with two 128-bit public statement limbs.

The predecessor is one fixed stage: the fixed-key narrow stage
(`CompressNarrowFixed::step_v1`) laid out by the narrow template backend,
whose packed key is embedded in `KzgPackedTerminal`'s fixed tables. The
key's BLAKE3 digest is computed from those same bytes at export and fixed
here. The narrow key verifies exactly one stage, so the terminal stage is a
configuration constant (the configuration row's stage interval is that one
stage) and the predecessor claim's stage is the stage before it.

The narrow claim is the `step_v1` call split into keyed chunks: chunk `j` is
`[tag_j, instance, values_j]`, where the tag names the entry function and
chunk and the instance is the entry's fixed invocation id. Both, and each
chunk's value count, are fixed per chunk in `claim_headers`. The chunk values,
in order, are the call's policy digest, stage and original statement and its
carried accumulator.

The entry authenticates the chain policy against the configured digest and
binds its anchors to the key's and the configured pairing anchors, checks the
claim against the configured policy, stage and the public statement,
verifies the narrow proof under the embedded key, and folds the carried
accumulator with the transcript-derived weight (`CompressBNPacked::fold`). It
returns the folded pair as eighteen affine words for the terminal PLONK
backend's constrained pairing assertion. -/
namespace MultiStark.FinalNarrow
open Aiur

private def template : Modules.Program Nat := aiur⟦
module CompressFinalNarrow {
  type Digest=KzgIO::Digest;
  type Values=Lists::List<Field>;
  -- Replaced, with every table below, by `source`.
  const CHUNKS: Field = 0;
  table configuration_inputs: () {}
  table configuration_outputs: ([Field;8],[Field;128],Field,Field) {}
  map configuration()->([Field;8],[Field;128],Field,Field) = configuration_inputs => configuration_outputs;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field;8] {}
  map key_digest()->[Field;8] = key_digest_inputs => key_digest_outputs;
  -- Per claim chunk: tag, instance key, value count.
  table header_inputs: (Field,) {}
  table header_values: [Field;3] {}
  map header(index: Field)->[Field;3] = header_inputs => header_values;

  inline fn word(bytes:[Field;4])->Field {
    bytes[0]+256*bytes[1]+65536*bytes[2]+16777216*bytes[3]
  }

  fn statement(low:Field,high:Field)->Digest {
    let a=BN254G1Encoding::chunk_bytes(low);
    let b=BN254G1Encoding::chunk_bytes(high);
    [word(a[0 .. 4]),word(a[4 .. 8]),word(a[8 .. 12]),word(a[12 .. 16]),
     word(b[0 .. 4]),word(b[4 .. 8]),word(b[8 .. 12]),word(b[12 .. 16])]
  }

  fn anchor_stream(raw:[Field;128])->KzgIO::Input {
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[96 .. 128]),&(Lists::Node::Nil));
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[64 .. 96]),tail);
    let tail=KzgIO::prepend_words32(Blake3::address_from_fields(raw[32 .. 64]),tail);
    (KzgIO::prepend_words32(Blake3::address_from_fields(raw[0 .. 32]),tail),0)
  }

  -- The chunk values in order, each chunk's header checked.
  fn values(claims:Lists::List<Values>,index:Field)->Values {
    match *claims {
      Lists::Node::Nil=>{assert_eq!(index,CHUNKS,"narrow claim chunk count");&(Lists::Node::Nil)},
      Lists::Node::Cons(claim,rest)=>{
        let expected=header(index);
        let Lists::Node::Cons(tag,claim)=*claim;
        let Lists::Node::Cons(owner,chunk)=*claim;
        assert_eq!(tag,expected[0],"narrow claim chunk tag");
        assert_eq!(owner,expected[1],"narrow claim instance");
        assert_eq!(Lists::length(chunk),expected[2],"narrow claim chunk width");
        Lists::concat(chunk,values(rest,index+1))
      },
    }
  }

  fn previous(values:Values,policy_digest:Digest,stage:Field,statement:Digest)->(BN254G1::Point,BN254G1::Point) {
    let (claimed_policy,values)=CompressBN::take8(values);
    assert_eq!(claimed_policy,policy_digest,"narrow predecessor policy");
    let Lists::Node::Cons(previous_stage,values)=*values;
    assert_eq!(previous_stage,stage-1,"narrow predecessor stage");
    let (claimed_statement,values)=CompressBN::take8(values);
    assert_eq!(claimed_statement,statement,"narrow predecessor statement");
    let Lists::Node::Cons(a0,values)=*values; let Lists::Node::Cons(a1,values)=*values;
    let Lists::Node::Cons(b0,values)=*values; let Lists::Node::Cons(b1,values)=*values;
    let Lists::Node::Nil=*values;
    KzgAccumulator::unpack([a0,a1,b0,b1])
  }

  fn verify_accumulator_v1(statement_low:Field,statement_high:Field)->[Field;18] {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,stage,_last_stage)=configuration();
    let (policy_bytes,policy_length)=KzgIO::sized_channel(4);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(policy_bytes,policy_length)),policy_digest,"compression policy digest mismatch");
    let policy=KzgPackedDeserialize::chain_policy(policy_bytes);
    let KzgDeserialize::Policy::Mk(anchors,_gl_key,_gl_entry,bn_key,_bn_entry)=policy;
    let key_digest=key_digest();
    assert_eq!(key_digest,bn_key,"unauthorized narrow compression predecessor key");
    let key=KzgPackedTerminal::key();
    let KzgPackedDeserialize::Key::Mk(_seed,_max_log,_budget,_generator,key_anchors,_circuits,_fixed)=key;
    KzgIO::equal_bytes(anchors,key_anchors);
    KzgIO::equal_bytes(anchors,anchor_stream(expected_anchors));
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (previous_a,previous_b)=previous(values(claims,0),policy_digest,stage,statement);
    let (transcript,current_a,current_b)=KzgPackedTerminal::verify_key(key,KzgPackedDeserialize::proof(KzgIO::channel(3)),claims);
    let (a,b)=CompressBNPacked::fold(transcript,policy_digest,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    let points=BN254G1Encoding::from_chunks(KzgAccumulator::pack(a,b));
    let a=BN254G1::to_raw(points.0);
    let b=BN254G1::to_raw(points.1);
    [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],
     b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8]]
  }
}
⟧

#aiur_check MultiStark.BN.libraries.append MultiStark.BN.source |>.append MultiStark.BN.Packed.source
  |>.append MultiStark.Source.kzgPackedTerminal |>.append template

def entry : String := "CompressFinalNarrow::verify_accumulator_v1"

/-- Claim chunk header: tag, instance key and value count. -/
structure Header where
  tag : Nat
  key : Nat
  values : Nat

/-- The template with its configuration row, claim headers and the digest of
`key`. The configuration's stage interval must be the one terminal stage. -/
def source (configuration : Final.Configuration) (headers : List Header) (key : ByteArray) :
    Except String (Modules.Program Nat) := do
  unless configuration.policyDigest.length == 8 && configuration.policyDigest.all (· < 2^32) do
    throw "final policy digest requires eight u32 words"
  unless configuration.anchors.length == 128 && configuration.anchors.all (· < 256) do
    throw "final pairing anchors require 128 canonical bytes"
  unless 2 ≤ configuration.minStage && configuration.minStage == configuration.maxStage &&
      configuration.maxStage < 2^32 do
    throw "the narrow terminal follows one fixed BN stage"
  unless headers.length != 0 && headers.all (fun h => h.tag < MultiStark.BN.modulus &&
      h.key < MultiStark.BN.modulus && h.values != 0) do
    throw "invalid narrow claim headers"
  unless (headers.map (·.values)).sum == 21 do
    throw "narrow claim headers must cover the step_v1 call"
  let keyDigest := BN.PackedTerminal.digestWords (Blake3.Rust.hash key).val
  let row : Generic.Expr Nat := .tuple [
    .array (configuration.policyDigest.map .literal),
    .array (configuration.anchors.map .literal),
    .literal configuration.minStage,.literal configuration.maxStage]
  let tables : List (Generic.Table Nat) := [
    ⟨"configuration_inputs",.tuple [],[.tuple []]⟩,
    ⟨"configuration_outputs",.tuple [.array .field 8,.array .field 128,.field,.field],[row]⟩,
    ⟨"key_digest_inputs",.tuple [],[.tuple []]⟩,
    ⟨"key_digest_outputs",.array .field 8,[.array (keyDigest.map .literal)]⟩,
    ⟨"header_inputs",.tuple [.field],(List.range headers.length).map fun i => .tuple [.literal i]⟩,
    ⟨"header_values",.array .field 3,headers.map fun h =>
      .array [.literal h.tag,.literal h.key,.literal h.values]⟩]
  return { template with modules := template.modules.map fun m =>
    {m with body := match m.body with
      | .definitions d => .definitions {d with program := { d.program with
          tables := tables
          consts := d.program.consts.map fun c =>
            if c.name == "CHUNKS" then ⟨c.name, .literal headers.length⟩ else c } }
      | body => body} }

/-- Anchor coordinates and canonical bytes are checked against the prepared
lines before compilation, as for `CompressFinal`. -/
def program (configuration : Final.Configuration) (lines : List (List Nat)) (headers : List Header)
    (key : ByteArray) : Except String (Modules.Program BN.F) := do
  Library.Field.BN254.Pairing.Preparation.validate configuration.anchorCoordinates configuration.anchors lines
  let verifier ← BN.PackedTerminal.program key
  let terminal ← source configuration headers key
  return verifier.append (terminal.toField BN.F)

def compilePackage (configuration : Final.Configuration) (lines : List (List Nat))
    (headers : List Header) (key : ByteArray) : IO ByteArray := do
  let program ← IO.ofExcept (program configuration lines headers key)
  let prepared ← IO.ofExcept (Modules.prepare program [entry])
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← Trace.exportPlanParallelWide BN.modulus ZMod.val
    prepared.environment.source prepared.entries exported
  IO.ofExcept (Artifact.packageWide exported BN.modulus ZMod.val (some circuits))

end MultiStark.FinalNarrow
