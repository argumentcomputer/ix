//! Pure-Rust BN254 Groth16 Fermat's Last Theorem 256-byte Margin Note demo CLI.
//!
//! Runs deterministic DEV/UNSAFE setup -> Groth16 proving (256-byte uncompressed
//! EVM proof vs 262-byte Fermat Margin Note; 128-byte compressed proof) ->
//! native Rust verification -> negative controls -> exports
//! `Groth16Verifier.DEV_INSECURE.sol`, `proof.bin` (256 B), and
//! `fermat_vector.json`.
//!
//! Usage:
//!   `groth16_fermat_demo [--out DIR] [--deterministic] [--cuda]`

use ark_bn254::{Fr, G1Projective, G2Projective};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::Field;
use ix_proof_compression::aiur_backend::groth16::{
  FERMAT_DEMO_DEV_SEED, FERMAT_MARGIN_NOTE, Groth16Accelerator, Proof,
  default_fermat_claim_digest, export_fermat_vector, export_solidity,
  fermat_demo_assignment, fermat_demo_r1cs, prove_with_accel,
  prove_with_blinding_accel, setup_dev, solidity_filename, verify,
  verify_compressed_bytes, verify_evm_bytes,
};
use std::{env, fs, path::PathBuf, time::Instant};

struct Cli {
  out_dir: Option<PathBuf>,
  deterministic: bool,
  use_cuda: bool,
}

fn parse_cli() -> Result<Cli, String> {
  let args: Vec<String> = env::args().skip(1).collect();
  let mut out_dir = None;
  let mut deterministic = false;
  let mut use_cuda = false;
  let mut i = 0;
  while i < args.len() {
    match args[i].as_str() {
      "--out" => {
        i += 1;
        let path = args.get(i).ok_or("--out requires a directory path")?;
        out_dir = Some(PathBuf::from(path));
        i += 1;
      },
      "--deterministic" => {
        deterministic = true;
        i += 1;
      },
      "--cuda" => {
        use_cuda = true;
        i += 1;
      },
      "-h" | "--help" => {
        return Err(
          "usage: groth16_fermat_demo [--out DIR] [--deterministic] [--cuda]"
            .into(),
        );
      },
      other => return Err(format!("unknown argument: {other}")),
    }
  }
  Ok(Cli { out_dir, deterministic, use_cuda })
}

fn run() -> Result<(), String> {
  let cli = parse_cli()?;
  let accel = if cli.use_cuda {
    Groth16Accelerator::cuda()?
  } else {
    Groth16Accelerator::cpu()
  };

  println!("=== Ix Pure-Rust BN254 Groth16: Fermat Margin Note Demo ===");
  println!(
    "WARNING: DEV/UNSAFE deterministic setup (NO trusted setup ceremony)"
  );
  println!(
    "Backend: {}",
    if accel.is_cuda() { "Ix-CUDA (sppark)" } else { "CPU (GLV 2D parallel)" }
  );

  let r1cs = fermat_demo_r1cs();
  let digest = default_fermat_claim_digest();
  let (assignment, public_inputs) = fermat_demo_assignment(
    &digest,
    Fr::from(3u64),
    Fr::from(4u64),
    Fr::from(5u64),
  )?;

  let t_setup = Instant::now();
  let (pk, vk) = setup_dev(&r1cs, FERMAT_DEMO_DEV_SEED)?;
  let setup_ms = t_setup.elapsed().as_secs_f64() * 1e3;

  let t_prove = Instant::now();
  let proof = if cli.deterministic {
    prove_with_blinding_accel(
      &pk,
      &assignment,
      Fr::from(1637u64),
      Fr::from(1670u64),
      accel,
    )?
  } else {
    prove_with_accel(&pk, &assignment, accel)?
  };
  let prove_ms = t_prove.elapsed().as_secs_f64() * 1e3;

  let evm_bytes = proof.to_evm_bytes();
  let compressed_bytes = proof.to_compressed_bytes();

  let t_verify = Instant::now();
  verify_evm_bytes(&vk, &public_inputs, &evm_bytes)?;
  let verify_ms = t_verify.elapsed().as_secs_f64() * 1e3;
  verify_compressed_bytes(&vk, &public_inputs, &compressed_bytes)?;

  println!(
    "Circuit: {} constraints, {} wires ({} public, {} private), QAP domain N={}",
    r1cs.constraints.len(),
    r1cs.num_wires,
    r1cs.num_public,
    r1cs.num_private(),
    pk.domain_size
  );
  println!(
    "Proof size: {} bytes uncompressed EVM ({} < {} byte Fermat Margin Note!), {} bytes compressed",
    evm_bytes.len(),
    evm_bytes.len(),
    FERMAT_MARGIN_NOTE.len(),
    compressed_bytes.len()
  );
  println!(
    "Timings: setup={setup_ms:.3} ms, prove={prove_ms:.3} ms, verify={verify_ms:.3} ms"
  );

  // Run inline negative controls.
  let bad_pub = [public_inputs[0] + Fr::ONE, public_inputs[1]];
  if verify(&vk, &bad_pub, &proof).is_ok() {
    return Err("negative control failed: wrong public input accepted".into());
  }
  let mut bad_a = proof;
  bad_a.a =
    (G1Projective::from(proof.a) + G1Projective::generator()).into_affine();
  if verify(&vk, &public_inputs, &bad_a).is_ok() {
    return Err("negative control failed: tampered A accepted".into());
  }
  let mut bad_b = proof;
  bad_b.b =
    (G2Projective::from(proof.b) + G2Projective::generator()).into_affine();
  if verify(&vk, &public_inputs, &bad_b).is_ok() {
    return Err("negative control failed: tampered B accepted".into());
  }
  let mut bad_c = proof;
  bad_c.c =
    (G1Projective::from(proof.c) + G1Projective::generator()).into_affine();
  if verify(&vk, &public_inputs, &bad_c).is_ok() {
    return Err("negative control failed: tampered C accepted".into());
  }
  let swapped = Proof { a: proof.c, b: proof.b, c: proof.a };
  if verify(&vk, &public_inputs, &swapped).is_ok() {
    return Err("negative control failed: swapped A/C accepted".into());
  }
  let mut bad_bytes = evm_bytes;
  bad_bytes[0] = 0xff;
  if verify_evm_bytes(&vk, &public_inputs, &bad_bytes).is_ok() {
    return Err("negative control failed: malformed proof accepted".into());
  }
  println!("Negative controls: 6/6 strictly rejected");

  let solidity_src = export_solidity(&vk)?;
  let vector = export_fermat_vector(&vk, &digest, &proof)?;
  let vector_json =
    serde_json::to_string_pretty(&vector).map_err(|e| e.to_string())?;

  if let Some(out_dir) = cli.out_dir {
    fs::create_dir_all(&out_dir)
      .map_err(|e| format!("failed to create {}: {e}", out_dir.display()))?;
    let sol_path = out_dir.join(solidity_filename(true));
    let bin_path = out_dir.join("proof.bin");
    let json_path = out_dir.join("fermat_vector.json");
    fs::write(&sol_path, solidity_src.as_bytes())
      .map_err(|e| format!("write {}: {e}", sol_path.display()))?;
    fs::write(&bin_path, evm_bytes)
      .map_err(|e| format!("write {}: {e}", bin_path.display()))?;
    fs::write(&json_path, vector_json.as_bytes())
      .map_err(|e| format!("write {}: {e}", json_path.display()))?;
    println!("Wrote:");
    println!("  {} ({} bytes)", sol_path.display(), solidity_src.len());
    println!("  {} ({} bytes)", bin_path.display(), evm_bytes.len());
    println!("  {} ({} bytes)", json_path.display(), vector_json.len());
  }

  Ok(())
}

fn main() {
  if let Err(err) = run() {
    eprintln!("error: {err}");
    std::process::exit(1);
  }
}
