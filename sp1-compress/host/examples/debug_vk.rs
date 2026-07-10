//! Diagnostic: check the vk codec round-trip fixpoint and compare the
//! decoded system's circuit count against a proof's opening counts.
//! Usage: debug_vk <vk.bin> <proof.bin>

use aiur::vk_codec::AiurVerifyingKey;

fn main() {
  let mut args = std::env::args().skip(1);
  let vk_bytes = std::fs::read(args.next().expect("vk path")).unwrap();
  let key = AiurVerifyingKey::from_bytes(&vk_bytes).expect("vk decode");
  let reencoded = key.to_bytes();
  println!(
    "vk: {} bytes, re-encoded: {} bytes, fixpoint: {}",
    vk_bytes.len(),
    reencoded.len(),
    vk_bytes == reencoded
  );
  if vk_bytes != reencoded {
    let i = vk_bytes
      .iter()
      .zip(&reencoded)
      .position(|(a, b)| a != b)
      .unwrap_or(vk_bytes.len().min(reencoded.len()));
    println!("first divergence at byte offset {i}");
  }
  println!("decoded circuits: {}", key.num_circuits());

  if let Some(proof_path) = args.next() {
    let proof_bytes = std::fs::read(proof_path).unwrap();
    let proof =
      multi_stark::prover::Proof::from_bytes(&proof_bytes).expect("proof");
    println!(
      "proof: stage1 {} stage2 {} quotient {} preprocessed {:?} log_degrees {}",
      proof.stage_1_opened_values.len(),
      proof.stage_2_opened_values.len(),
      proof.quotient_opened_values.len(),
      proof.preprocessed_opened_values.as_ref().map(Vec::len),
      proof.log_degrees.len(),
    );
  }
}
