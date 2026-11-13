import MultiStark.BN.Program
import Aiur.Library.Field.BN254.Pairing
import Aiur.Library.Field.BN254.Pairing.Preparation

/-! Terminal Aiur relations with two 128-bit statement limbs. Policy and pairing
anchors are compiler constants, and a bounded private stage selects an authorized
predecessor. The full-source entry discharges the pairing; the accumulator entry
returns affine points for the terminal PLONK backend's constrained assertion. -/
namespace MultiStark.Final
open Aiur

structure Configuration where
  policyDigest : List Nat
  anchors : List Nat
  anchorCoordinates : List (List Nat)
  minStage : Nat
  maxStage : Nat
  deriving Repr

def Configuration.validate (configuration : Configuration) : Except String Unit := do
  unless configuration.policyDigest.length == 8 && configuration.policyDigest.all (· < 2^32) do
    throw "final policy digest requires eight u32 words"
  unless configuration.anchors.length == 128 && configuration.anchors.all (· < 256) do
    throw "final pairing anchors require 128 canonical bytes"
  unless (configuration.minStage == 1 || configuration.minStage == 2) &&
      configuration.minStage ≤ configuration.maxStage && configuration.maxStage < 2^32 do
    throw "invalid final compression stage interval"

private def template : Modules.Program Nat := aiur⟦
module CompressFinal {
  type Digest=KzgIO::Digest;
  table configuration_inputs: () {}
  table configuration_outputs: ([Field;8],[Field;128],Field,Field) {}
  map configuration()->([Field;8],[Field;128],Field,Field) = configuration_inputs => configuration_outputs;

  inline fn word(bytes:[Field;4])->Field {
    bytes[0]+256*bytes[1]+65536*bytes[2]+16777216*bytes[3]
  }

  fn statement(low:Field,high:Field)->Digest {
    let a=BN254G1Encoding::chunk_bytes(low);
    let b=BN254G1Encoding::chunk_bytes(high);
    [word(a[0 .. 4]),word(a[4 .. 8]),word(a[8 .. 12]),word(a[12 .. 16]),
     word(b[0 .. 4]),word(b[4 .. 8]),word(b[8 .. 12]),word(b[12 .. 16])]
  }

  fn anchor_stream(raw:[Field;128])->Bytes::Stream {
    let tail=KzgIO::prepend32(Blake3::address_from_fields(raw[96 .. 128]),&(Lists::Node::Nil));
    let tail=KzgIO::prepend32(Blake3::address_from_fields(raw[64 .. 96]),tail);
    let tail=KzgIO::prepend32(Blake3::address_from_fields(raw[32 .. 64]),tail);
    KzgIO::prepend32(Blake3::address_from_fields(raw[0 .. 32]),tail)
  }

  fn verify_v1(statement_low:Field,statement_high:Field)->() {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,min_stage,max_stage)=configuration();
    let stage=hint::<Field>("kzg.final.stage",());
    KzgIO::digest_word(stage);
    assert_eq!(UInt32::less_than_fields(stage,min_stage),0,"final stage below configured interval");
    assert_eq!(UInt32::less_than_fields(max_stage,stage),0,"final stage exceeds configured interval");
    let (accumulator,actual_anchors)=CompressBN::step_v1(policy_digest,stage,statement);
    KzgIO::equal_bytes(actual_anchors,anchor_stream(expected_anchors));
    BN254Pairing::check_chunks(accumulator)
  }

  fn verify_accumulator_v1(statement_low:Field,statement_high:Field)->[Field;18] {
    let statement=statement(statement_low,statement_high);
    let (policy_digest,expected_anchors,min_stage,max_stage)=configuration();
    let stage=hint::<Field>("kzg.final.stage",());
    KzgIO::digest_word(stage);
    assert_eq!(UInt32::less_than_fields(stage,min_stage),0,"final stage below configured interval");
    assert_eq!(UInt32::less_than_fields(max_stage,stage),0,"final stage exceeds configured interval");
    let (accumulator,actual_anchors)=CompressBN::step_v1(policy_digest,stage,statement);
    KzgIO::equal_bytes(actual_anchors,anchor_stream(expected_anchors));
    let points=BN254G1Encoding::from_chunks(accumulator);
    let a=BN254G1::to_raw(points.0);
    let b=BN254G1::to_raw(points.1);
    [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],
     b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8]]
  }
}
⟧

/-- Fixed configuration rows are authenticated by the final compiler key. -/
def source (configuration : Configuration) : Except String (Modules.Program Nat) := do
  configuration.validate
  let row : Generic.Expr Nat := .tuple [
    .array (configuration.policyDigest.map .literal),
    .array (configuration.anchors.map .literal),
    .literal configuration.minStage,.literal configuration.maxStage]
  return { template with modules := template.modules.map fun m =>
    {m with body := match m.body with
      | .definitions d => .definitions {d with program.tables := [
          ⟨"configuration_inputs",.tuple [],[.tuple []]⟩,
          ⟨"configuration_outputs",.tuple [.array .field 8,.array .field 128,.field,.field],[row]⟩]}
      | body => body} }

def entry : String := "CompressFinal::verify_v1"

/-- This entry returns a deferred accumulator. Complete acceptance requires the
terminal PLONK schema's constrained pairing assertion on these output words. -/
def accumulatorEntry : String := "CompressFinal::verify_accumulator_v1"

/-- Anchor coordinates, canonical bytes and every prepared line are checked
before compilation. The runtime program binds the verified policy's anchors
to those same constants before discharging the pairing. -/
def program (configuration : Configuration) (lines : List (List Nat)) :
    Except String (Modules.Program BN.F) := do
  Library.Field.BN254.Pairing.Preparation.validate configuration.anchorCoordinates configuration.anchors lines
  let pairing ← Library.Field.BN254.Pairing.declarations lines
  let terminal ← source configuration
  return BN.program
    |>.append (Library.Field.BN254.Pairing.FqProducts.declarations.toField BN.F)
    |>.append (Library.Field.BN254.Pairing.Fp2.declarations.toField BN.F)
    |>.append (Library.Field.BN254.Pairing.Fp6.declarations.toField BN.F)
    |>.append (Library.Field.BN254.Pairing.Fp12.declarations.toField BN.F)
    |>.append (pairing.toField BN.F)
    |>.append (terminal.toField BN.F)

def compilePackage (configuration : Configuration) (lines : List (List Nat))
    (trace : Bool := true) (accumulatorOnly : Bool := false) : IO ByteArray := do
  let program ← IO.ofExcept (program configuration lines)
  let prepared ← IO.ofExcept (Modules.prepare program
    [if accumulatorOnly then accumulatorEntry else entry])
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ← Trace.exportPlanParallelWide BN.modulus ZMod.val
        prepared.environment.source prepared.entries exported
      pure (exported,some circuits)
    else pure (exported,none)
  IO.ofExcept (Artifact.packageWide exported BN.modulus ZMod.val circuits)

end MultiStark.Final
