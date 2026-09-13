use super::*;
use ixby_flock::ixby::{
  control::ControlCapacities,
  decode::{InputCapacities, PrimitiveSet, ProgramCapacities},
  exec::{SemanticProfile, compile_exec_profile, expected_statement},
  machine::MachineCapacities,
};
use std::time::Instant;

const CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 2,
    blocks: 4,
    operands: 2,
  },
  control: ControlCapacities { locals: 4, continuations: 2, arguments: 2 },
  input: InputCapacities { bytes: 64, values: 2 },
  output_bytes: 64,
  steps: 24,
};

fn setup() -> CompiledExec {
  compile_exec_profile(
    SemanticProfile::scalar(CAPACITY).unwrap(),
    CAPACITY,
    PrimitiveSet::scalar(),
  )
  .unwrap()
}

// Hand-authored first-order IxBy programs, with explicit canonical byte order.
// Guest construction is used by the proof producer only, never replay/setup.
fn program(branch: bool) -> Vec<u8> {
  let mut bytes = b"IXBY\0\0\0\0".to_vec();
  for value in [0u32, 0, 1, 1, 0, if branch { 3 } else { 1 }] {
    bytes.extend(value.to_le_bytes());
  }
  bytes.extend(1u32.to_le_bytes());
  if branch {
    bytes.extend([6, 0]); // branch (local 0), blocks 1 and 2
    for value in [0u32, 1, 2] {
      bytes.extend(value.to_le_bytes());
    }
    for value in [true, false] {
      bytes.extend(1u32.to_le_bytes());
      bytes.extend([1, 1, 0, u8::from(value)]); // ret literal Bool
    }
  } else {
    bytes.extend([1, 0]); // ret local 0
    bytes.extend(0u32.to_le_bytes());
  }
  bytes
}

fn input(value: bool) -> Vec<u8> {
  let mut bytes = b"IXBI\0\0\0\0".to_vec();
  bytes.extend(1u32.to_le_bytes());
  bytes.extend([0, 0, u8::from(value)]);
  bytes
}

fn output(value: bool) -> Vec<u8> {
  [b"IXBO\0\0\0\0".as_slice(), &[0, 0, u8::from(value)]].concat()
}

fn hash(tag: u8, parent: &[u8], bytes: &[u8]) -> [u8; 32] {
  let mut hash = blake3::Hasher::new();
  hash.update(b"IxBy/commit/v0\0");
  hash.update(&[tag]);
  hash.update(parent);
  hash.update(bytes);
  *hash.finalize().as_bytes()
}

fn prove(
  setup: &CompiledExec,
  branch: bool,
  value: bool,
) -> (ExecCommitmentsV0, Vec<u8>) {
  let code = program(branch);
  let input = input(value);
  let output = output(value);
  let program = hash(1, &setup.identities().profile, &code);
  let commitments = ExecCommitmentsV0 {
    program,
    input: hash(2, &program, &input),
    output: hash(3, &program, &output),
  };
  let expected = expected_statement(setup.profile(), &code, &input, &output);
  assert_eq!(
    expected.0,
    commitments.statement_digest(setup.identities().profile)
  );
  (commitments, setup.prove(expected, &code, &input).unwrap())
}

fn topology(w: &ExecReplayWitness<'_>) -> Vec<[u8; 32]> {
  let tape = w.transcript();
  let fold = w.matrix_accumulator();
  vec![
    w.binding().topology_digest(),
    *tape.shape_digest(),
    tape.chained_blake3().topology_digest(),
    tape.f128_algebra().topology_digest(),
    w.wiring().trace().topology_digest(),
    w.merged_pcs().trace().topology_digest(),
    w.multipoint_assist().trace().topology_digest(),
    w.inner_ligerito().trace().topology_digest(),
    *fold.shape_digest(),
    fold.chained_blake3().topology_digest(),
    fold.trace().topology_digest(),
    fold.circuit_structure_trace().topology_digest(),
    fold.jagged_trace().topology_digest(),
  ]
}

#[test]
#[ignore = "real generic Exec proofs and complete native replay; no terminal FFLONK proof"]
fn different_guests_have_identical_complete_replay_topology() {
  let setup = setup();
  let binding = compile_exec_binding(&setup).unwrap();
  let identity = setup.identities();
  let mut first_topology = None;
  for (branch, value) in [(false, false), (true, false), (true, true)] {
    let start = Instant::now();
    let (commitments, bytes) = prove(&setup, branch, value);
    let witness = replay_exec(&setup, commitments, &bytes).unwrap();
    eprintln!(
      "Exec replay branch={branch} value={value}: {:.3}s; {:?}",
      start.elapsed().as_secs_f64(),
      witness.census()
    );
    let actual = topology(&witness);
    if let Some(expected) = &first_topology {
      assert_eq!(&actual, expected);
    } else {
      first_topology = Some(actual);
    }
    assert_eq!(&binding, witness.binding());
    assert_eq!(setup.identities(), identity);
    assert_eq!(compile_exec_binding(&setup).unwrap(), binding);
    assert!(witness.census().matrix_accumulator.root_claims > 0);
    assert!(witness.census().inner_ligerito.path_digests > 0);
    // Strict rejection is at the generic Exec boundary, with no fallback.
    if !branch {
      for at in [0, 7, 8, 39, 40, bytes.len() / 2, bytes.len() - 1] {
        let mut bad = bytes.clone();
        bad[at] ^= 1;
        assert!(replay_exec(&setup, commitments, &bad).is_err());
      }
      for tag in [*b"IXFLK301", *b"IXFLK302"] {
        let mut bad = bytes.clone();
        bad[..8].copy_from_slice(&tag);
        assert!(replay_exec(&setup, commitments, &bad).is_err());
      }
      let mut bad = commitments;
      bad.input[0] ^= 1;
      assert!(replay_exec(&setup, bad, &bytes).is_err());
      let mut trailing = bytes.clone();
      trailing.push(0);
      assert!(replay_exec(&setup, commitments, &trailing).is_err());
      assert!(
        replay_exec(&setup, commitments, &bytes[..bytes.len() - 1]).is_err()
      );
    }
  }
}

#[test]
#[ignore = "matrix-free complete generic Exec R1CS/PLONK census, diagnostic roots still public"]
fn complete_generic_exec_constraint_census() {
  let setup = setup();
  let start = Instant::now();
  let (commitments, bytes) = prove(&setup, false, false);
  let witness = replay_exec(&setup, commitments, &bytes).unwrap();
  eprintln!(
    "Exec native replay ready in {:.3}s; starting complete matrix-free census",
    start.elapsed().as_secs_f64()
  );
  let census = crate::census_exec_replay_observed(&witness, move |progress| {
    eprintln!(
      "Exec census {:.3}s: {progress:?}; {}",
      start.elapsed().as_secs_f64(),
      memory_summary()
    );
  })
  .unwrap();
  eprintln!(
    "Exec complete root-conditional census in {:.3}s: {census:#?}",
    start.elapsed().as_secs_f64()
  );
  let capacity = ix_fflonk::plan_fflonk_capacity(&census.plonk).unwrap();
  eprintln!(
    "Exec root-conditional FFLONK capacity (not a proof): {capacity:#?}"
  );
  assert!(census.r1cs.census().constraints > 1_000_000);
  assert_eq!(census.r1cs.census().constraints_by_phase.len(), 7);
  assert!(census.root_conditional_public_scalar_bytes > 64);
}

fn memory_summary() -> String {
  std::fs::read_to_string("/proc/self/status")
    .map(|status| {
      status
        .lines()
        .filter(|line| {
          line.starts_with("VmHWM:") || line.starts_with("VmPeak:")
        })
        .collect::<Vec<_>>()
        .join("; ")
    })
    .unwrap_or_else(|_| "process memory counters unavailable".into())
}
