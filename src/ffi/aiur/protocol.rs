use multi_stark::{
  p3_field::PrimeField64,
  prover::Proof,
  types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::sync::LazyLock;

use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExcept,
  LeanExternal, LeanNat, LeanOwned, LeanProd, LeanRef, LeanString,
};

use crate::{
  aiur::{
    G,
    execute::{IOBuffer, IOKeyInfo},
    synthesis::AiurSystem,
  },
  ffi::aiur::{
    lean_unbox_g, lean_unbox_nat_as_usize, toplevel::decode_toplevel,
  },
  lean::{
    LeanAiurCommitmentParameters, LeanAiurFriParameters, LeanAiurToplevel,
  },
};

// =============================================================================
// External class registration
// =============================================================================

static AIUR_PROOF_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<Proof>);
static AIUR_SYSTEM_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<AiurSystem>);

// =============================================================================
// Lean FFI functions
// =============================================================================

/// `Aiur.Proof.toBytes : @& Proof → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_bytes(
  proof_obj: LeanExternal<Proof, LeanBorrowed<'_>>,
) -> LeanByteArray<LeanOwned> {
  let bytes = proof_obj.get().to_bytes().expect("Serialization error");
  LeanByteArray::from_bytes(&bytes)
}

/// `Aiur.Proof.ofBytes : @& ByteArray → Proof`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_of_bytes(
  byte_array: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<Proof, LeanOwned> {
  let proof =
    Proof::from_bytes(byte_array.as_bytes()).expect("Deserialization error");
  LeanExternal::alloc(&AIUR_PROOF_CLASS, proof)
}

/// `AiurSystem.build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_build(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  commitment_parameters: LeanAiurCommitmentParameters<LeanBorrowed<'_>>,
) -> LeanExternal<AiurSystem, LeanOwned> {
  let system = AiurSystem::build(
    decode_toplevel(&toplevel),
    decode_commitment_parameters(&commitment_parameters),
  );
  LeanExternal::alloc(&AIUR_SYSTEM_CLASS, system)
}

/// `AiurSystem.verify : @& AiurSystem → @& FriParameters → @& Array G → @& Proof → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_verify(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  proof_obj: LeanExternal<Proof, LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let fri_parameters = decode_fri_parameters(&fri_parameters);
  let claim = claim.map(|x| lean_unbox_g(&x));
  match aiur_system_obj.get().verify(fri_parameters, &claim, proof_obj.get()) {
    Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
    Err(err) => LeanExcept::error_string(&format!("{err:?}")),
  }
}

/// `Bytecode.Toplevel.execute`: runs execution only (no proof) and returns
/// `Except String (Array G × (Array G × Array (Array G × IOKeyInfo))
///   × (Array (Array (String × Nat × Nat × Nat)) × Array (Nat × Nat)))`.
/// The function side is per-function array of per-split
/// `(group, width, uniqueRows, totalHits)` quadruples. The memory side is
/// per-memory-size `(uniqueRows, totalHits)` pairs.
/// On execution failure (e.g. assertion mismatch from a typechecker
/// rejecting a constant), returns `Except.error msg` instead of panicking
/// — letting Lean test runners (`KernelArena.lean`) classify failures.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_execute(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (query_record, output) = match toplevel.execute(
    fun_idx,
    args.map(|x| lean_unbox_g(&x)),
    &mut io_buffer,
  ) {
    Ok(pair) => pair,
    Err(err) => return LeanExcept::error_string(&err.to_string()),
  };

  // Summarize a query map into `(unique_rows, total_hits)`. `unique_rows` is
  // the trace height (number of distinct queries with nonzero multiplicity);
  // `total_hits` is the sum of multiplicities (how often those rows were
  // hit).
  let summarize_pair = |q: &crate::aiur::execute::QueryMap| -> (usize, usize) {
    let mut rows = 0usize;
    let mut hits = 0usize;
    for (_, res) in q.iter() {
      let m = usize::try_from(res.multiplicity.as_canonical_u64())
        .expect("multiplicity exceeds usize");
      if m != 0 {
        rows += 1;
        hits += m;
      }
    }
    (rows, hits)
  };

  // Per-function array of `(group, width, unique_rows, total_hits)` quadruples,
  // one per split. Queries within a function are partitioned by return group.
  let function_stats: Vec<Vec<(String, usize, usize, usize)>> = (0..toplevel
    .functions
    .len())
    .map(|i| {
      let queries = &query_record.function_queries[i];
      let mut stats: Vec<(String, usize, usize, usize)> = toplevel
        .filtered_functions[i]
        .iter()
        .map(|(group, func)| {
          let (rows, hits) = queries
            .iter()
            .filter(|(_, res)| res.return_group == *group)
            .fold((0usize, 0usize), |(r, h), (_, res)| {
              let m = usize::try_from(res.multiplicity.as_canonical_u64())
                .expect("multiplicity exceeds usize");
              if m != 0 { (r + 1, h + m) } else { (r, h) }
            });
          let l = func.layout;
          let width = l.input_size
            + l.selectors
            + l.auxiliaries
            + 4 * (1 + l.lookups);
          (group.clone(), width, rows, hits)
        })
        .collect();
      stats.sort_by(|a, b| a.0.cmp(&b.0));
      stats
    })
    .collect();

  let memory_counts: Vec<(usize, usize)> = toplevel
    .memory_sizes
    .iter()
    .map(|size| {
      query_record.memory_queries.get(size).map_or((0, 0), summarize_pair)
    })
    .collect();

  let lean_function_stats = {
    let outer = LeanArray::alloc(function_stats.len());
    for (i, per_fn) in function_stats.iter().enumerate() {
      let inner = LeanArray::alloc(per_fn.len());
      for (j, (group, width, rows, hits)) in per_fn.iter().enumerate() {
        // (String × Nat × Nat × Nat) — right-nested pair encoding
        let quad = LeanProd::new(
          LeanString::new(group),
          LeanProd::new(
            LeanOwned::box_usize(*width),
            LeanProd::new(
              LeanOwned::box_usize(*rows),
              LeanOwned::box_usize(*hits),
            ),
          ),
        );
        inner.set(j, quad);
      }
      outer.set(i, inner);
    }
    outer
  };
  let lean_memory_counts = {
    let arr = LeanArray::alloc(memory_counts.len());
    for (i, &(rows, hits)) in memory_counts.iter().enumerate() {
      let pair =
        LeanProd::new(LeanOwned::box_usize(rows), LeanOwned::box_usize(hits));
      arr.set(i, pair);
    }
    arr
  };
  let lean_query_counts =
    LeanProd::new(lean_function_stats, lean_memory_counts);

  let lean_io = build_lean_io_buffer(&io_buffer);
  // (Array G, (Array G × Array (Array G × IOKeyInfo),
  //   Array (Array (String × Nat × Nat × Nat)) × Array (Nat × Nat)))
  let io_counts = LeanProd::new(lean_io, lean_query_counts);
  let result = LeanProd::new(build_g_array(&output), io_counts);
  LeanExcept::ok(result)
}

/// `AiurSystem.prove`: runs the prover and returns
/// `Array G × Proof × Array G × Array (Array G × IOKeyInfo)`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanOwned {
  let fri_parameters = decode_fri_parameters(&fri_parameters);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let args = args.map(|x| lean_unbox_g(&x));
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (claim, proof) =
    aiur_system_obj.get().prove(fri_parameters, fun_idx, &args, &mut io_buffer);

  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  let lean_io = build_lean_io_buffer(&io_buffer);
  // Proof × Array G × Array (Array G × IOKeyInfo)
  let proof_io_tuple = LeanProd::new(lean_proof, lean_io);
  // Array G × Proof × Array G × Array (Array G × IOKeyInfo)
  let result = LeanProd::new(build_g_array(&claim), proof_io_tuple);
  result.into()
}

// =============================================================================
// Helpers
// =============================================================================

/// Build a Lean `Array G` from a slice of field elements.
fn build_g_array(values: &[G]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(values.len());
  for (i, g) in values.iter().enumerate() {
    arr.set(i, LeanOwned::box_u64(g.as_canonical_u64()));
  }
  arr
}

fn decode_io_buffer(
  io_data_arr: &LeanArray<LeanBorrowed<'_>>,
  io_map_arr: &LeanArray<LeanBorrowed<'_>>,
) -> IOBuffer {
  let data = io_data_arr.map(|x| lean_unbox_g(&x));
  let map = decode_io_buffer_map(io_map_arr);
  IOBuffer { data, map }
}

/// Build a Lean `Array G × Array (Array G × IOKeyInfo)` from an `IOBuffer`.
fn build_lean_io_buffer(io_buffer: &IOBuffer) -> LeanOwned {
  let lean_io_data = build_g_array(&io_buffer.data);
  let lean_io_map = {
    let arr = LeanArray::alloc(io_buffer.map.len());
    for (i, (key, info)) in io_buffer.map.iter().enumerate() {
      let key_arr = build_g_array(key);
      let key_info = LeanProd::new(
        LeanOwned::box_usize(info.idx),
        LeanOwned::box_usize(info.len),
      );
      let map_elt = LeanProd::new(key_arr, key_info);
      arr.set(i, map_elt);
    }
    arr
  };
  let io_tuple = LeanProd::new(lean_io_data, lean_io_map);
  io_tuple.into()
}

fn decode_commitment_parameters(
  obj: &LeanAiurCommitmentParameters<impl LeanRef>,
) -> CommitmentParameters {
  let ctor = obj.as_ctor();
  CommitmentParameters {
    log_blowup: lean_unbox_nat_as_usize(&ctor.get(0)),
    cap_height: lean_unbox_nat_as_usize(&ctor.get(1)),
  }
}

fn decode_fri_parameters(
  obj: &LeanAiurFriParameters<impl LeanRef>,
) -> FriParameters {
  let ctor = obj.as_ctor();
  FriParameters {
    log_final_poly_len: lean_unbox_nat_as_usize(&ctor.get(0)),
    max_log_arity: lean_unbox_nat_as_usize(&ctor.get(1)),
    num_queries: lean_unbox_nat_as_usize(&ctor.get(2)),
    commit_proof_of_work_bits: lean_unbox_nat_as_usize(&ctor.get(3)),
    query_proof_of_work_bits: lean_unbox_nat_as_usize(&ctor.get(4)),
  }
}

fn decode_io_buffer_map(
  arr: &LeanArray<LeanBorrowed<'_>>,
) -> FxHashMap<Vec<G>, IOKeyInfo> {
  let mut map = FxHashMap::with_capacity_and_hasher(arr.len(), FxBuildHasher);
  for elt in arr.iter() {
    let pair = elt.as_ctor();
    let key = pair.get(0).as_array().map(|x| lean_unbox_g(&x));
    let info_ctor = pair.get(1).as_ctor();
    let info = IOKeyInfo {
      idx: lean_unbox_nat_as_usize(&info_ctor.get(0)),
      len: lean_unbox_nat_as_usize(&info_ctor.get(1)),
    };
    map.insert(key, info);
  }
  map
}
