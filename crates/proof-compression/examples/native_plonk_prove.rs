//! Standalone 100% Go-free native Rust (+ optional Ix-CUDA) PLONK + BSB22
//! prover, verifier, and Solidity exporter over Lean's `ix-aiur-scs-v1`
//! (`ixscs001`) format for both BN254 and BLS12-381.
//!
//! Compiles and runs under default features (`--features plonk` is NOT needed
//! and Go is NOT invoked).
//!
//! Usage:
//! - Self-test (synthetic `ix-aiur-scs-v1` on BN254 and/or BLS12-381):
//!   `native_plonk_prove --self-test [--curve bn254|bls12-381|both] [--out DIR] [--cuda]`
//! - Emit Lean `plonk_export` stage schema from an `.ixa` package:
//!   `native_plonk_prove --stage-only --ixa FILE.ixa [--entry NAME] [--args a,b] [--advice FILE] [--curve bn254|bls12-381] --out DIR`
//! - Prove & verify any `.ixscs` file with a binary witness or `.ixa` program:
//!   `native_plonk_prove FILE.ixscs [--curve bn254|bls12-381] [--witness FILE.bin] [--ixa FILE.ixa [--entry NAME] [--args a,b] [--advice FILE]] [--out DIR] [--cuda]`

use aiur::{
  FieldWord, artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use ix_proof_compression::{
  aiur_backend::{
    Bls12381 as Bls12381Aiur, Bn254 as Bn254Aiur,
    plonk::{
      native::{
        self, NativeProver, PackedGate, PlonkAccelerator, ScsBuilder, ScsFile,
        WireHint, domain_size_for_scs, export_solidity, parse_binary_witness,
        prepare_to_dir,
        scs_file::{SEL_L, SEL_M, SEL_O, SEL_R},
        verify_native_bytes, verify_solidity_bytes,
      },
      scs::{CurveWitness, Table, stage_for_plan},
    },
  },
  kzg::{
    Srs,
    curve::{Bls12381, Bn254, Curve, G1AffineOf, G1ProjectiveOf, KzgCurve},
    field::CurveScalar,
  },
};
use num_bigint::BigUint;
use serde_json::json;
use std::{
  env, fs,
  path::{Path, PathBuf},
  sync::Arc,
  time::Instant,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CurveChoice {
  Bn254,
  Bls12381,
  Both,
}

struct Cli {
  self_test: bool,
  stage_only: bool,
  curve: CurveChoice,
  scs_path: Option<PathBuf>,
  witness_path: Option<PathBuf>,
  ixa_path: Option<PathBuf>,
  advice_path: Option<PathBuf>,
  entry: Option<String>,
  args: Vec<u64>,
  out_dir: Option<PathBuf>,
  use_cuda: bool,
}

fn parse_cli() -> Result<Cli, String> {
  let mut raw: Vec<String> = env::args().skip(1).collect();
  if raw.is_empty() {
    return Err(usage());
  }
  let mut self_test = false;
  let mut stage_only = false;
  let mut curve = CurveChoice::Bn254;
  let mut scs_path = None;
  let mut witness_path = None;
  let mut ixa_path = None;
  let mut advice_path = None;
  let mut entry = None;
  let mut args = Vec::new();
  let mut out_dir = None;
  let mut use_cuda = false;

  let mut i = 0usize;
  while i < raw.len() {
    match raw[i].as_str() {
      "--self-test" => {
        self_test = true;
        i += 1;
      },
      "--stage-only" => {
        stage_only = true;
        i += 1;
      },
      "--cuda" => {
        use_cuda = true;
        i += 1;
      },
      "--curve" => {
        i += 1;
        let val = raw.get(i).ok_or("--curve requires bn254|bls12-381|both")?;
        curve = match val.as_str() {
          "bn254" => CurveChoice::Bn254,
          "bls12-381" | "bls12381" => CurveChoice::Bls12381,
          "both" => CurveChoice::Both,
          other => return Err(format!("unknown curve {other:?}")),
        };
        i += 1;
      },
      "--witness" => {
        i += 1;
        witness_path =
          Some(PathBuf::from(raw.get(i).ok_or("--witness requires a path")?));
        i += 1;
      },
      "--ixa" => {
        i += 1;
        ixa_path =
          Some(PathBuf::from(raw.get(i).ok_or("--ixa requires a path")?));
        i += 1;
      },
      "--advice" => {
        i += 1;
        advice_path =
          Some(PathBuf::from(raw.get(i).ok_or("--advice requires a path")?));
        i += 1;
      },
      "--entry" => {
        i += 1;
        entry = Some(raw.get(i).ok_or("--entry requires a name")?.clone());
        i += 1;
      },
      "--args" => {
        i += 1;
        let val = raw.get(i).ok_or("--args requires comma-separated u64s")?;
        for part in val.split(',').filter(|s| !s.is_empty()) {
          args.push(
            part
              .trim()
              .parse::<u64>()
              .map_err(|e| format!("invalid arg {part:?}: {e}"))?,
          );
        }
        i += 1;
      },
      "--out" => {
        i += 1;
        out_dir =
          Some(PathBuf::from(raw.get(i).ok_or("--out requires a directory")?));
        i += 1;
      },
      "-h" | "--help" => return Err(usage()),
      other if other.starts_with('-') => {
        return Err(format!("unknown flag {other:?}\n{}", usage()));
      },
      _ => {
        if scs_path.is_some() {
          return Err(format!(
            "unexpected extra positional argument {}",
            raw[i]
          ));
        }
        scs_path = Some(PathBuf::from(std::mem::take(&mut raw[i])));
        i += 1;
      },
    }
  }
  Ok(Cli {
    self_test,
    stage_only,
    curve,
    scs_path,
    witness_path,
    ixa_path,
    advice_path,
    entry,
    args,
    out_dir,
    use_cuda,
  })
}

fn usage() -> String {
  "Usage:\n  \
   native_plonk_prove --self-test [--curve bn254|bls12-381|both] [--out DIR] [--cuda]\n  \
   native_plonk_prove --stage-only --ixa FILE.ixa [--entry NAME] [--args a,b] [--advice FILE] [--curve bn254|bls12-381] --out DIR\n  \
   native_plonk_prove FILE.ixscs [--curve bn254|bls12-381] [--witness FILE.bin | --ixa FILE.ixa [--entry NAME] [--args a,b] [--advice FILE]] [--out DIR] [--cuda]"
    .into()
}

fn fr_to_dec<C: KzgCurve>(val: C::Fr) -> String {
  BigUint::from_bytes_le(&val.into_bigint().to_bytes_le()).to_string()
}

fn build_synthetic_scs<C: KzgCurve>(
  num_outputs: usize,
) -> (Vec<u8>, Vec<C::Fr>) {
  let coeffs = vec![
    C::FR_ONE,
    C::FR_NEG_ONE,
    C::Fr::from(2u64),
    C::Fr::from(4u64),
    C::Fr::from(8u64),
  ];
  let publics = 2usize;
  let outputs: Vec<u32> = (0..num_outputs)
    .map(|k| u32::try_from(publics + k).expect("fits u32"))
    .collect();
  let w_x = u32::try_from(publics + num_outputs).expect("fits u32");
  let w_y = w_x + 1;
  let w_m = w_x + 2;
  let cells = (w_m as usize) + 1;
  let mut hints = vec![WireHint::Input; cells];
  let mut gates = Vec::new();

  let mut add_wire = |h: WireHint| -> u32 {
    let id = u32::try_from(hints.len()).expect("fits u32");
    hints.push(h);
    id
  };

  let g_prod = u32::try_from(gates.len()).expect("fits u32");
  let w_prod = add_wire(WireHint::Solve { gate: g_prod });
  gates.push(PackedGate {
    a: w_x,
    b: w_y,
    c: w_prod,
    sel: SEL_M | SEL_O,
    alpha_id: 0,
    beta_id: 0,
    omega_id: 1,
    qc: 0,
  });

  let g_diff = u32::try_from(gates.len()).expect("fits u32");
  let w_diff = add_wire(WireHint::Solve { gate: g_diff });
  gates.push(PackedGate {
    a: w_prod,
    b: 0,
    c: w_diff,
    sel: SEL_L | SEL_R | SEL_O,
    alpha_id: 0,
    beta_id: 1,
    omega_id: 1,
    qc: 5,
  });
  gates.push(PackedGate {
    a: w_diff,
    b: 1,
    c: 0,
    sel: SEL_L | SEL_R,
    alpha_id: 0,
    beta_id: 1,
    omega_id: 0,
    qc: 0,
  });
  let pre = gates.len();

  let w_gamma = add_wire(WireHint::Challenge);
  let mut bits = [0u32; 4];
  for (bit, slot) in bits.iter_mut().enumerate() {
    let wb = add_wire(WireHint::Bit {
      wire: w_gamma,
      bit: u32::try_from(bit).expect("fits u32"),
    });
    *slot = wb;
    gates.push(PackedGate {
      a: wb,
      b: wb,
      c: wb,
      sel: SEL_M | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 1,
      qc: 0,
    });
  }
  let g_b01 = u32::try_from(gates.len()).expect("fits u32");
  let w_b01 = add_wire(WireHint::Solve { gate: g_b01 });
  gates.push(PackedGate {
    a: bits[0],
    b: bits[1],
    c: w_b01,
    sel: SEL_L | SEL_R | SEL_O,
    alpha_id: 0,
    beta_id: 2,
    omega_id: 1,
    qc: 0,
  });
  let g_b012 = u32::try_from(gates.len()).expect("fits u32");
  let w_b012 = add_wire(WireHint::Solve { gate: g_b012 });
  gates.push(PackedGate {
    a: w_b01,
    b: bits[2],
    c: w_b012,
    sel: SEL_L | SEL_R | SEL_O,
    alpha_id: 0,
    beta_id: 3,
    omega_id: 1,
    qc: 0,
  });
  let g_beta = u32::try_from(gates.len()).expect("fits u32");
  let w_beta = add_wire(WireHint::Solve { gate: g_beta });
  gates.push(PackedGate {
    a: w_b012,
    b: bits[3],
    c: w_beta,
    sel: SEL_L | SEL_R | SEL_O,
    alpha_id: 0,
    beta_id: 4,
    omega_id: 1,
    qc: 0,
  });

  let g_d0 = u32::try_from(gates.len()).expect("fits u32");
  let w_d0 = add_wire(WireHint::Solve { gate: g_d0 });
  gates.push(PackedGate {
    a: w_gamma,
    b: w_x,
    c: w_d0,
    sel: SEL_L | SEL_R | SEL_O,
    alpha_id: 0,
    beta_id: 0,
    omega_id: 1,
    qc: 1,
  });
  let g_d1 = u32::try_from(gates.len()).expect("fits u32");
  let w_d1 = add_wire(WireHint::Solve { gate: g_d1 });
  gates.push(PackedGate {
    a: w_gamma,
    b: w_y,
    c: w_d1,
    sel: SEL_L | SEL_R | SEL_O,
    alpha_id: 0,
    beta_id: 0,
    omega_id: 1,
    qc: 1,
  });

  let mut qs = [0u32; 4];
  for (slot, (den, num)) in
    qs.iter_mut().zip([(w_d0, w_m), (w_d0, w_m), (w_d1, w_x), (w_d1, w_x)])
  {
    let g_idx = u32::try_from(gates.len()).expect("fits u32");
    let w_q = add_wire(WireHint::Solve { gate: g_idx });
    *slot = w_q;
    gates.push(PackedGate {
      a: w_q,
      b: den,
      c: num,
      sel: SEL_M | SEL_O,
      alpha_id: 0,
      beta_id: 0,
      omega_id: 1,
      qc: 0,
    });
  }

  let mut prev = qs[0];
  for (other, coeff_id) in
    [(qs[1], 1), (qs[2], 0), (qs[3], 1), (w_beta, 0), (w_beta, 1)]
  {
    let g_idx = u32::try_from(gates.len()).expect("fits u32");
    let next = add_wire(WireHint::Solve { gate: g_idx });
    gates.push(PackedGate {
      a: prev,
      b: other,
      c: next,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: 0,
      beta_id: coeff_id,
      omega_id: 1,
      qc: 0,
    });
    prev = next;
  }
  let w_free = add_wire(WireHint::Free);
  gates.push(PackedGate {
    a: w_free,
    b: w_gamma,
    c: prev,
    sel: SEL_M | SEL_O,
    alpha_id: 0,
    beta_id: 0,
    omega_id: 0,
    qc: 0,
  });

  let builder = ScsBuilder::<C> {
    publics,
    wires: hints.len(),
    pre,
    gamma: w_gamma,
    beta: w_beta,
    outputs,
    coeffs,
    gates,
    commits: vec![0, 1, w_x, w_y, w_m],
    hints,
    tables: vec![
      Table {
        name: "root".into(),
        cell_base: 0,
        rows: 1,
        width: u32::try_from(publics + num_outputs).expect("fits u32"),
      },
      Table {
        name: "witness".into(),
        cell_base: u64::try_from(publics + num_outputs).expect("fits u64"),
        rows: 1,
        width: 3,
      },
    ],
  };

  let mut inputs = Vec::with_capacity(cells);
  inputs.push(C::Fr::from(100u64));
  inputs.push(C::Fr::from(296u64));
  for k in 0..num_outputs {
    inputs.push(C::Fr::from(u64::try_from(500 + k).expect("fits u64")));
  }
  inputs.push(C::Fr::from(17u64));
  inputs.push(C::Fr::from(23u64));
  inputs.push(C::Fr::from(9u64));
  (builder.encode(), inputs)
}

fn load_and_execute_ixa<B, C>(
  backend: B,
  ixa_path: &Path,
  entry_opt: Option<&str>,
  args_u64: &[u64],
  advice_path: Option<&Path>,
) -> Result<
  (TracePlan<'static, B>, String, aiur::Execution<B>, Vec<CurveScalar<C>>),
  String,
>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>
    + Copy
    + Send
    + Sync
    + 'static,
  C: KzgCurve,
{
  let bytes =
    fs::read(ixa_path).map_err(|e| format!("{}: {e}", ixa_path.display()))?;
  let pkg = WidePackage::decode(&bytes)?;
  if pkg.program.modulus != backend.modulus() {
    return Err(format!("package modulus does not match {}", C::NAME));
  }
  let trace = pkg.trace.ok_or("package has no trace section")?;
  let mut program = pkg.program.check_with(backend)?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let entry = entry_opt.map_or_else(
    || plan.program().program().entries[0].name.clone(),
    str::to_owned,
  );
  let args: Vec<CurveScalar<C>> =
    args_u64.iter().map(|&v| backend.from_u64(v)).collect();
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, backend)?;
  aiur::library::u64::register(&mut hints, backend)?;
  aiur::library::ixcc::register(&mut hints, backend)?;
  if let Some(p) = advice_path {
    let adv_bytes = fs::read(p).map_err(|e| format!("{}: {e}", p.display()))?;
    let adv_pkg = WidePackage::decode(&adv_bytes)?;
    let mut adv_prog = adv_pkg.program.check_with(backend)?;
    if let Some(adv_trace) = &adv_pkg.trace {
      adv_prog.track_depth(adv_trace)?;
    }
    aiur::library::ixcc::register_advice_program(
      &mut hints,
      plan.program(),
      adv_prog,
    )?;
  }
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute(&entry, args.clone())
    .map_err(|e| e.to_string())?;
  Ok((plan, entry, record, args))
}

fn execute_ixa_stage<B, C>(
  backend: B,
  ixa_path: &Path,
  entry_opt: Option<&str>,
  args_u64: &[u64],
  advice_path: Option<&Path>,
  out_dir: &Path,
) -> Result<(), String>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>
    + Copy
    + Send
    + Sync
    + 'static,
  C: KzgCurve,
{
  let (plan, entry, record, args) = load_and_execute_ixa::<B, C>(
    backend,
    ixa_path,
    entry_opt,
    args_u64,
    advice_path,
  )?;
  let public_args = plan.public_args(&record, &entry, &args)?;
  let schema = stage_for_plan::<B, C>(&plan, &entry, &record, &public_args)?;
  fs::create_dir_all(out_dir)
    .map_err(|e| format!("{}: {e}", out_dir.display()))?;
  let stage_path = out_dir.join("stage.json");
  fs::write(&stage_path, serde_json::to_vec_pretty(&schema).unwrap())
    .map_err(|e| e.to_string())?;
  println!("Wrote {} stage schema to {}", C::NAME, stage_path.display());
  Ok(())
}

fn build_ixa_witness<B, C>(
  backend: B,
  ixa_path: &Path,
  entry_opt: Option<&str>,
  args_u64: &[u64],
  advice_path: Option<&Path>,
  scs: &ScsFile<C>,
) -> Result<Vec<C::Fr>, String>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>
    + Copy
    + Send
    + Sync
    + 'static,
  C: KzgCurve,
{
  let (plan, entry, record, args) = load_and_execute_ixa::<B, C>(
    backend,
    ixa_path,
    entry_opt,
    args_u64,
    advice_path,
  )?;
  let witness_builder =
    CurveWitness::<B, C>::new(&plan, &entry, scs.to_inputs())?;
  let bin = witness_builder.binary(&record, &args)?;
  parse_binary_witness::<C>(&bin, scs.publics, scs.cells)
}

fn run_prove_verify_pipeline<C: KzgCurve>(
  scs_bytes: &[u8],
  input_wires: &[C::Fr],
  out_dir: Option<&Path>,
  use_cuda: bool,
) -> Result<(), String> {
  let scs = ScsFile::<C>::parse(scs_bytes)?;
  let domain = domain_size_for_scs(&scs)?;
  let srs_len = (domain + 3).next_power_of_two();
  let accel = PlonkAccelerator::<C>::new(use_cuda)?;

  let t_srs = Instant::now();
  let srs = Srs::<C>::unsafe_dev_setup(srs_len, b"ix-native-plonk-cli-dev-srs");
  let srs_ms = t_srs.elapsed().as_secs_f64() * 1e3;

  let t_setup = Instant::now();
  let (pk, vk) = native::setup(&scs, &srs, &accel)?;
  let setup_ms = t_setup.elapsed().as_secs_f64() * 1e3;
  let vk_sha = vk.sha256();
  let public_inputs = input_wires[..scs.publics].to_vec();

  let prover = NativeProver::from_parts(scs.clone(), pk, accel);
  let bundle = prover.prove(input_wires, &public_inputs)?;

  let t_verify = Instant::now();
  verify_native_bytes(&vk, &vk_sha, &bundle.native, &public_inputs)?;
  let verify_native_ms = t_verify.elapsed().as_secs_f64() * 1e3;

  let t_verify_sol = Instant::now();
  verify_solidity_bytes(&vk, &vk_sha, &bundle.solidity, &public_inputs)?;
  let verify_solidity_ms = t_verify_sol.elapsed().as_secs_f64() * 1e3;

  let solidity_src = export_solidity(&vk)?;

  // Run 5 live negative controls.
  let mut bad_pub = public_inputs.clone();
  bad_pub[0] += C::FR_ONE;
  assert!(
    verify_solidity_bytes(&vk, &vk_sha, &bundle.solidity, &bad_pub).is_err(),
    "negative control failed: wrong public input accepted"
  );
  let mut bad_vk = vk_sha;
  bad_vk[0] ^= 1;
  assert!(
    verify_native_bytes(&vk, &bad_vk, &bundle.native, &public_inputs).is_err(),
    "negative control failed: wrong VK digest accepted"
  );
  let mut decoded =
    native::NativeProof::<C>::from_native_bytes(&bundle.native)?;
  let shift = |p: G1AffineOf<C>| -> G1AffineOf<C> {
    (G1ProjectiveOf::<C>::from(p) + G1ProjectiveOf::<C>::generator())
      .into_affine()
  };
  let mut bad_l = decoded.clone();
  bad_l.lro[0] = shift(bad_l.lro[0]);
  assert!(native::verify(&vk, &vk_sha, &bad_l, &public_inputs).is_err());
  let mut bad_bsb = decoded.clone();
  bad_bsb.bsb22_commitments[0] = shift(bad_bsb.bsb22_commitments[0]);
  assert!(native::verify(&vk, &vk_sha, &bad_bsb, &public_inputs).is_err());
  decoded.claimed_values[1] += C::FR_ONE;
  assert!(native::verify(&vk, &vk_sha, &decoded, &public_inputs).is_err());

  if let Some(dir) = out_dir {
    fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let scs_out = dir.join("circuit.ixscs");
    fs::write(&scs_out, scs_bytes).map_err(|e| e.to_string())?;
    let prep_dir = dir.join("prepared");
    let manifest =
      prepare_to_dir(&scs_out, &srs, "dev-srs", &prep_dir, &accel)?;
    let reopened =
      NativeProver::<C>::open(&prep_dir, &scs_out, &manifest, accel)?;
    assert_eq!(reopened.vk_sha256(), vk_sha);

    let sol_name = match C::CURVE {
      Curve::Bn254 => "PlonkVerifier.sol",
      Curve::Bls12381 => "Bls12381PlonkVerifier.sol",
    };
    fs::write(dir.join(sol_name), solidity_src.as_bytes())
      .map_err(|e| e.to_string())?;
    fs::write(dir.join("proof.bin"), &bundle.native)
      .map_err(|e| e.to_string())?;
    fs::write(dir.join("proof.solidity.bin"), &bundle.solidity)
      .map_err(|e| e.to_string())?;
    let pub_json: Vec<String> =
      public_inputs.iter().copied().map(fr_to_dec::<C>).collect();
    fs::write(
      dir.join("public_inputs.json"),
      serde_json::to_vec_pretty(&pub_json).unwrap(),
    )
    .map_err(|e| e.to_string())?;
    let summary = json!({
      "curve": C::NAME,
      "domain": domain,
      "gates": scs.gates_count,
      "pre_gates": scs.pre,
      "commits": scs.commits.len(),
      "public_inputs": scs.publics,
      "outputs": scs.outputs.len(),
      "native_proof_bytes": bundle.native.len(),
      "solidity_proof_bytes": bundle.solidity.len(),
      "solidity_verifier_bytes": solidity_src.len(),
      "vk_sha256": vk.sha256_hex(),
      "srs_ms": srs_ms,
      "setup_ms": setup_ms,
      "prove_timings": bundle.timings,
      "verify_native_ms": verify_native_ms,
      "verify_solidity_ms": verify_solidity_ms,
    });
    fs::write(
      dir.join("summary.json"),
      serde_json::to_vec_pretty(&summary).unwrap(),
    )
    .map_err(|e| e.to_string())?;
  }

  println!(
    "[{}] domain={} gates={} commits={} outputs={} | setup={:.2}ms prove={:.2}ms verify_native={:.2}ms verify_sol={:.2}ms | proof_native={}B proof_sol={}B verifier_sol={}B | 5/5 negative controls rejected",
    C::NAME,
    domain,
    scs.gates_count,
    scs.commits.len(),
    scs.outputs.len(),
    setup_ms,
    bundle.timings.total_ms,
    verify_native_ms,
    verify_solidity_ms,
    bundle.native.len(),
    bundle.solidity.len(),
    solidity_src.len(),
  );
  Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let cli =
    parse_cli().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

  if cli.stage_only {
    let ixa = cli.ixa_path.as_deref().ok_or("--stage-only requires --ixa")?;
    let out = cli.out_dir.as_deref().ok_or("--stage-only requires --out")?;
    match cli.curve {
      CurveChoice::Bn254 => execute_ixa_stage::<Bn254Aiur, Bn254>(
        Bn254Aiur,
        ixa,
        cli.entry.as_deref(),
        &cli.args,
        cli.advice_path.as_deref(),
        out,
      )?,
      CurveChoice::Bls12381 => execute_ixa_stage::<Bls12381Aiur, Bls12381>(
        Bls12381Aiur,
        ixa,
        cli.entry.as_deref(),
        &cli.args,
        cli.advice_path.as_deref(),
        out,
      )?,
      CurveChoice::Both => {
        return Err("--stage-only requires --curve bn254 or bls12-381".into());
      },
    }
    return Ok(());
  }

  if cli.self_test {
    if matches!(cli.curve, CurveChoice::Bn254 | CurveChoice::Both) {
      let (bytes0, w0) = build_synthetic_scs::<Bn254>(0);
      let out0 = cli.out_dir.as_ref().map(|d| d.join("bn254-out0"));
      run_prove_verify_pipeline::<Bn254>(
        &bytes0,
        &w0,
        out0.as_deref(),
        cli.use_cuda,
      )?;
      let (bytes18, w18) = build_synthetic_scs::<Bn254>(18);
      let out18 = cli.out_dir.as_ref().map(|d| d.join("bn254-out18"));
      run_prove_verify_pipeline::<Bn254>(
        &bytes18,
        &w18,
        out18.as_deref(),
        cli.use_cuda,
      )?;
    }
    if matches!(cli.curve, CurveChoice::Bls12381 | CurveChoice::Both) {
      let (bytes0, w0) = build_synthetic_scs::<Bls12381>(0);
      let out0 = cli.out_dir.as_ref().map(|d| d.join("bls12-381-out0"));
      run_prove_verify_pipeline::<Bls12381>(
        &bytes0,
        &w0,
        out0.as_deref(),
        cli.use_cuda,
      )?;
      let (bytes22, w22) = build_synthetic_scs::<Bls12381>(22);
      let out22 = cli.out_dir.as_ref().map(|d| d.join("bls12-381-out22"));
      run_prove_verify_pipeline::<Bls12381>(
        &bytes22,
        &w22,
        out22.as_deref(),
        cli.use_cuda,
      )?;
    }
    return Ok(());
  }

  let scs_path =
    cli.scs_path.as_deref().ok_or("missing SCS_PATH (or pass --self-test)")?;
  let scs_bytes = fs::read(scs_path)?;

  match cli.curve {
    CurveChoice::Bn254 => {
      let scs = ScsFile::<Bn254>::parse(&scs_bytes)?;
      let inputs = if let Some(w_path) = cli.witness_path.as_deref() {
        let w_bytes = fs::read(w_path)?;
        parse_binary_witness::<Bn254>(&w_bytes, scs.publics, scs.cells)?
      } else if let Some(ixa) = cli.ixa_path.as_deref() {
        build_ixa_witness::<Bn254Aiur, Bn254>(
          Bn254Aiur,
          ixa,
          cli.entry.as_deref(),
          &cli.args,
          cli.advice_path.as_deref(),
          &scs,
        )?
      } else {
        return Err("provide --witness FILE.bin or --ixa FILE.ixa".into());
      };
      run_prove_verify_pipeline::<Bn254>(
        &scs_bytes,
        &inputs,
        cli.out_dir.as_deref(),
        cli.use_cuda,
      )?;
    },
    CurveChoice::Bls12381 => {
      let scs = ScsFile::<Bls12381>::parse(&scs_bytes)?;
      let inputs = if let Some(w_path) = cli.witness_path.as_deref() {
        let w_bytes = fs::read(w_path)?;
        parse_binary_witness::<Bls12381>(&w_bytes, scs.publics, scs.cells)?
      } else if let Some(ixa) = cli.ixa_path.as_deref() {
        build_ixa_witness::<Bls12381Aiur, Bls12381>(
          Bls12381Aiur,
          ixa,
          cli.entry.as_deref(),
          &cli.args,
          cli.advice_path.as_deref(),
          &scs,
        )?
      } else {
        return Err("provide --witness FILE.bin or --ixa FILE.ixa".into());
      };
      run_prove_verify_pipeline::<Bls12381>(
        &scs_bytes,
        &inputs,
        cli.out_dir.as_deref(),
        cli.use_cuda,
      )?;
    },
    CurveChoice::Both => {
      return Err(
        "specify --curve bn254 or --curve bls12-381 for an SCS file".into(),
      );
    },
  }
  Ok(())
}
