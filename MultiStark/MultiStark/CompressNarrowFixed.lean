import MultiStark.BN.KzgPackedTerminal
import Blake3.Rust

/-! The fixed-key narrow compression stage of a packed-SHPLONK chain
(`IXAUKG01` policy): stage one, verifying the packed CompressGL proof under
one pinned CompressGL key.

The CompressGL key is embedded in `KzgPackedTerminal`'s fixed tables, so this
program's own key commits to it; its BLAKE3 digest is computed from the same
bytes at export and fixed here, so the policy's authorized GL key is compared
with the key actually verified.

The public call is the policy digest, the stage and the original statement,
returning the packed accumulator:

- the policy bytes (channel 4) hash to the policy digest and parse as a chain
  policy; its GL key digest is the embedded key's and its anchors are the
  key's;
- the predecessor claim (channel 2) is the CompressGL claim of the GL entry
  with reserved zero words and the statement (`CompressBN::previous` at stage
  one);
- the packed proof (channel 3) is verified by `KzgPackedTerminal::verify_key`;
- the deferred pair is folded with the transcript-derived weight
  (`CompressBNPacked::fold`), from the point at infinity. -/
namespace MultiStark.NarrowFixed
open Aiur

private def template : Modules.Program Nat := aiur⟦
module CompressNarrowFixed {
  type Digest=KzgIO::Digest;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field;8] {}
  map key_digest()->[Field;8] = key_digest_inputs => key_digest_outputs;

  fn step_v1(policy_digest: Digest, stage: Field, statement: Digest) -> [Field;4] {
    CompressBN::digest_onto(policy_digest,&(Lists::Node::Nil)); CompressBN::digest_onto(statement,&(Lists::Node::Nil));
    KzgIO::digest_word(stage);
    assert_eq!(stage,1,"the fixed-key narrow stage verifies the CompressGL proof");
    let (policy_bytes,policy_length)=KzgIO::sized_channel(4);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(policy_bytes,policy_length)),policy_digest,"compression policy digest mismatch");
    let policy=KzgPackedDeserialize::chain_policy(policy_bytes);
    let KzgDeserialize::Policy::Mk(anchors,gl_key,_gl_entry,_bn_key,_bn_entry)=policy;
    let key_digest=key_digest();
    assert_eq!(key_digest,gl_key,"unauthorized compression predecessor key");
    let key=KzgPackedTerminal::key();
    let KzgPackedDeserialize::Key::Mk(_seed,_max_log,_budget,_generator,key_anchors,_circuits,_fixed)=key;
    KzgIO::equal_bytes(anchors,key_anchors);
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (previous_a,previous_b)=CompressBN::previous(policy,policy_digest,stage,statement,claims);
    let (transcript,current_a,current_b)=KzgPackedTerminal::verify_key(key,KzgPackedDeserialize::proof(KzgIO::channel(3)),claims);
    let (a,b)=CompressBNPacked::fold(transcript,policy_digest,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    KzgAccumulator::pack(a,b)
  }
}
⟧

#aiur_check MultiStark.BN.libraries.append MultiStark.BN.source |>.append MultiStark.BN.Packed.source
  |>.append MultiStark.Source.kzgPackedTerminal |>.append template

def entry : String := "CompressNarrowFixed::step_v1"

/-- The template with the digest of the embedded CompressGL `key`. -/
def source (key : ByteArray) : Modules.Program Nat :=
  let keyDigest := BN.PackedTerminal.digestWords (Blake3.Rust.hash key).val
  let tables : List (Generic.Table Nat) := [
    ⟨"key_digest_inputs",.tuple [],[.tuple []]⟩,
    ⟨"key_digest_outputs",.array .field 8,[.array (keyDigest.map .literal)]⟩]
  { template with modules := template.modules.map fun m =>
    {m with body := match m.body with
      | .definitions d => .definitions {d with program.tables := tables}
      | body => body} }

def program (key : ByteArray) : Except String (Modules.Program BN.F) := do
  let verifier ← BN.PackedTerminal.program key
  return verifier.append ((source key).toField BN.F)

def compilePackage (key : ByteArray) : IO ByteArray := do
  let program ← IO.ofExcept (program key)
  let prepared ← IO.ofExcept (Modules.prepare program [entry])
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← Trace.exportPlanParallelWide BN.modulus ZMod.val
    prepared.environment.source prepared.entries exported
  IO.ofExcept (Artifact.packageWide exported BN.modulus ZMod.val (some circuits))

end MultiStark.NarrowFixed
