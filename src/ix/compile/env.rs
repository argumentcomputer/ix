//! Top-level environment compilation with work-stealing parallelism.
//!
//! Extracted from `compile.rs` to keep the scheduler independently readable.

use std::sync::{
  Arc, Mutex,
  atomic::{AtomicUsize, Ordering as AtomicOrdering},
};
use std::thread;

use dashmap::DashMap;
use rustc_hash::FxHashSet;

use crate::ix::address::Address;
use crate::ix::compile::{
  BlockCache, CompileState, compile_const, compile_const_no_aux,
};
use crate::ix::condense::compute_sccs;
use crate::ix::env::{Env as LeanEnv, Name};
use crate::ix::graph::{NameSet, build_ref_graph};
use crate::ix::ground::ground_consts;
use crate::ix::ixon::CompileError;

/// Compile an entire Lean environment to Ixon format.
/// Work-stealing compilation using crossbeam channels.
///
/// Instead of processing blocks in waves (which underutilizes cores when wave sizes vary),
/// we use a work queue. When a block completes, it immediately unlocks dependent blocks.
pub fn compile_env(
  lean_env: &Arc<LeanEnv>,
) -> Result<CompileState, CompileError> {
  let graph = build_ref_graph(lean_env.as_ref());

  let ungrounded = ground_consts(lean_env.as_ref(), &graph.in_refs);
  if !ungrounded.is_empty() {
    for (n, e) in &ungrounded {
      eprintln!("Ungrounded {:?}: {:?}", n, e);
    }
    return Err(CompileError::InvalidMutualBlock {
      reason: "ungrounded environment".into(),
    });
  }

  let condensed = compute_sccs(&graph.out_refs);

  let stt =
    CompileState { lean_env: Some(lean_env.clone()), ..Default::default() };

  // The kenv is populated on-demand via ensure_in_kenv as constants are
  // compiled. Precompiles (PUnit, PProd, Eq, True) are added below.

  // Pre-compile the builtins that aux_gen is known to reference, so the
  // scheduler has their addresses in `aux_name_to_addr` before any block
  // with `.below` / `.brecOn` / `.brecOn.eq` regeneration fires.
  //
  // Rationale: `build_ref_graph` scans only the *original* Lean env, so
  // refs that aux_gen introduces (e.g., `.brecOn.eq` using `Eq.symm`)
  // aren't visible to the scheduler's topological ordering. Without
  // these pre-compiles, a block's aux_gen could run before the
  // dep's own SCC does, producing a nondeterministic `MissingConstant`
  // error (race depends on work-stealing order).
  //
  // Seed names (exact Const refs aux_gen emits — grep `mk_const` in
  // `src/ix/compile/aux_gen/**`):
  //   - `.below` (Type-level): PUnit, PProd (+ ctors via SCC)
  //   - `.brecOn.eq`: Eq, Eq.refl, Eq.symm, Eq.ndrec, HEq, HEq.refl, True
  //
  // From these seeds we compute the **transitive SCC closure** using
  // `condensed.block_refs` (each SCC's out-edges) and compile the closure
  // in reverse topological order — so every SCC's deps are already in
  // `aux_name_to_addr` by the time its own compilation runs.
  //
  // Any pre-compile failure is a hard error: silent fallback would leave
  // the name unresolved and race with the main scheduler, reintroducing
  // the bug this exists to prevent.
  //
  // Names absent from `lean_env` (e.g., unit-test fixtures) are silently
  // skipped at seeding time — the initial `condensed.low_links.get` is
  // optional. Transitive deps of surviving seeds are assumed present.
  precompile_aux_gen_prereqs(&condensed, lean_env, &stt)?;

  // Build work-stealing data structures
  let total_blocks = condensed.blocks.len();

  // For each block: (all names in block, original deps, remaining deps).
  // Using an explicit HashSet instead of an atomic counter prevents silent
  // corruption from double-decrements — removing an already-removed name
  // is a no-op.
  let block_info: DashMap<
    Name,
    (NameSet, FxHashSet<Name>, Mutex<FxHashSet<Name>>),
  > = DashMap::default();

  // Reverse deps: name -> set of block leaders that depend on this name
  let reverse_deps: DashMap<Name, Vec<Name>> = DashMap::default();

  // Initialize block info and reverse deps
  for (lo, all) in &condensed.blocks {
    let deps =
      condensed.block_refs.get(lo).ok_or(CompileError::InvalidMutualBlock {
        reason: "missing block refs".into(),
      })?;

    block_info.insert(
      lo.clone(),
      (all.clone(), deps.clone(), Mutex::new(deps.clone())),
    );

    // Register reverse dependencies
    for dep_name in deps {
      reverse_deps.entry(dep_name.clone()).or_default().push(lo.clone());
    }
  }

  // Shared ready queue: blocks that are ready to compile
  let ready_queue: Mutex<Vec<(Name, NameSet)>> = Mutex::new(Vec::new());

  // Initialize with blocks that have zero remaining dependencies
  {
    let mut queue = ready_queue.lock().unwrap();
    for entry in block_info.iter() {
      let lo = entry.key();
      let (all, _, remaining) = entry.value();
      if remaining.lock().unwrap().is_empty() {
        queue.push((lo.clone(), all.clone()));
      }
    }
  }

  // Track completed count for termination
  let completed = AtomicUsize::new(0);

  // Guard against duplicate processing: a block leader that's already been
  // handled is skipped. This prevents infinite loops from double-enqueuing.
  let processed: dashmap::DashSet<Name> = dashmap::DashSet::new();

  // Error storage for propagating errors from workers
  let error: Mutex<Option<CompileError>> = Mutex::new(None);

  // Condvar for signaling workers when new work is available or completion
  let work_available = std::sync::Condvar::new();

  // Use scoped threads to borrow from parent scope
  let num_threads =
    thread::available_parallelism().map(|n| n.get()).unwrap_or(4);

  // Take references to shared data outside the loop
  let error_ref = &error;
  let stt_ref = &stt;
  let reverse_deps_ref = &reverse_deps;
  let block_info_ref = &block_info;
  let completed_ref = &completed;
  let processed_ref = &processed;
  let ready_queue_ref = &ready_queue;
  let condvar_ref = &work_available;

  thread::scope(|s| {
    // Spawn worker threads
    for _ in 0..num_threads {
      s.spawn(move || {
        loop {
          // Try to get work from the ready queue
          let work = {
            let mut queue = ready_queue_ref.lock().unwrap();
            queue.pop()
          };

          match work {
            Some((lo, all)) => {
              // Check if we should stop due to error
              if error_ref.lock().unwrap().is_some() {
                return;
              }

              // Skip if already processed (prevents double-counting from
              // duplicate enqueuing)
              if !processed_ref.insert(lo.clone()) {
                continue;
              }

              // Track time for slow block detection
              let block_start = std::time::Instant::now();

              // Check if this block was pre-compiled into aux_name_to_addr.
              // Promote to name_to_addr without re-compiling.
              let _cc_start = std::time::Instant::now();
              let _is_precompiled = stt_ref.resolve_addr(&lo).is_some();
              if _is_precompiled {
                // Check if any names in this block are aux_gen-rewritten.
                let any_aux_gen =
                  all.iter().any(|n| stt_ref.aux_gen_extra_names.contains(n));

                // Compile cross-SCC unresolved names FIRST so they're in
                // name_to_addr before compile_const_no_aux runs.
                // Only compile — don't promote other names yet (promote_aux
                // inside compile_const_no_aux needs names to still be in
                // aux_name_to_addr, not yet in name_to_addr).
                {
                  let mut unresolved_names = Vec::new();
                  for name in &all {
                    if stt_ref.name_to_addr.contains_key(name) {
                      continue;
                    }
                    if stt_ref.resolve_addr(name).is_some() {
                      // In aux_name_to_addr — will be promoted later.
                      continue;
                    }
                    unresolved_names.push(name.clone());
                  }
                  if !unresolved_names.is_empty() {
                    let unresolved_set: NameSet =
                      unresolved_names.iter().cloned().collect();
                    let mut cache = BlockCache::default();
                    if let Err(e) = compile_const(
                      &unresolved_names[0],
                      &unresolved_set,
                      lean_env,
                      &mut cache,
                      stt_ref,
                    ) {
                      eprintln!(
                        "[compile_env] cross-SCC compile failed for {}: {}",
                        unresolved_names[0].pretty(),
                        e,
                      );
                      // Don't register failed names — downstream blocks
                      // will get MissingConstant rather than silently
                      // referencing broken data.
                    } else {
                      for name in &unresolved_names {
                        stt_ref.aux_gen_extra_names.insert(name.clone());
                      }
                      stt_ref
                        .aux_gen_pending
                        .lock()
                        .unwrap()
                        .extend(unresolved_names);
                    }
                  }
                }

                if any_aux_gen {
                  // Compile the original Lean form (without aux_gen).
                  // compile_mutual with aux=false calls promote_aux for
                  // each constant, setting Named.original with the
                  // original (addr, meta) for decompilation roundtrip.
                  let mut orig_cache = BlockCache::default();
                  if let Err(e) = compile_const_no_aux(
                    &lo,
                    &all,
                    lean_env,
                    &mut orig_cache,
                    stt_ref,
                  ) {
                    let mut err_guard = error_ref.lock().unwrap();
                    if err_guard.is_none() {
                      eprintln!(
                        "[compile_env] compile_const_no_aux failed for {}: {}",
                        lo.pretty(),
                        e,
                      );
                      *err_guard = Some(e);
                    }
                    return;
                  }
                }

                // Promote remaining names from aux_name_to_addr.
                for name in &all {
                  if stt_ref.name_to_addr.contains_key(name) {
                    continue;
                  }
                  if let Some(addr) = stt_ref.resolve_addr(name) {
                    stt_ref.name_to_addr.insert(name.clone(), addr);
                  }
                }
              } else {
                // Compile this block
                let mut cache = BlockCache::default();
                if let Err(e) =
                  compile_const(&lo, &all, lean_env, &mut cache, stt_ref)
                {
                  let mut err_guard = error_ref.lock().unwrap();
                  if err_guard.is_none() {
                    eprintln!(
                      "[compile_env] ERROR in block {} ({} members): {}",
                      lo.pretty(),
                      all.len(),
                      e,
                    );
                    for member in &all {
                      eprintln!("    member: {}", member.pretty());
                    }
                    // Print dep status for MissingConstant errors
                    if let CompileError::MissingConstant {
                      ref name,
                      ref caller,
                    } = e
                    {
                      eprintln!(
                        "[compile_env] MissingConstant: {name} (from {caller})"
                      );
                      eprintln!(
                        "  block: {} ({} members)",
                        lo.pretty(),
                        all.len()
                      );
                      for member in &all {
                        let in_main = stt_ref.name_to_addr.contains_key(member);
                        let in_aux =
                          stt_ref.aux_name_to_addr.contains_key(member);
                        let status = if in_main {
                          "name_to_addr"
                        } else if in_aux {
                          "aux_name_to_addr"
                        } else {
                          "pending"
                        };
                        eprintln!("    {} [{}]", member.pretty(), status);
                      }
                      if let Some(entry) = block_info_ref.get(&lo) {
                        let (_, orig_deps, remaining) = entry.value();
                        // Print all original deps with their resolution status
                        eprintln!("  deps ({}):", orig_deps.len());
                        for d in orig_deps.iter() {
                          let in_main = stt_ref.name_to_addr.contains_key(d);
                          let in_aux = stt_ref.aux_name_to_addr.contains_key(d);
                          let status = if in_main {
                            "name_to_addr"
                          } else if in_aux {
                            "aux_name_to_addr"
                          } else {
                            "UNRESOLVED"
                          };
                          eprintln!("    {} [{}]", d.pretty(), status);
                        }
                        let rem = remaining.lock().unwrap();
                        if !rem.is_empty() {
                          eprintln!("  unsatisfied ({}):", rem.len());
                          for d in rem.iter() {
                            eprintln!("    {}", d.pretty());
                          }
                        }
                      }
                    }
                    *err_guard = Some(e);
                  }
                  return;
                }
              }

              // Check for slow blocks
              let elapsed = block_start.elapsed();
              if *crate::ix::compile::IX_TIMING && elapsed.as_secs_f32() > 1.0 {
                let cc_time = _cc_start.elapsed().as_secs_f32();
                eprintln!(
                  "Slow block {:?} ({} consts): {:.2}s path={} cc={:.2}s",
                  lo.pretty(),
                  all.len(),
                  elapsed.as_secs_f32(),
                  if _is_precompiled { "precompiled" } else { "compile" },
                  cc_time,
                );
              }

              // Collect newly-ready blocks by removing satisfied deps.
              // HashSet::remove is idempotent — no double-decrement risk.
              let mut newly_ready = Vec::new();

              let resolve_name =
                |name: &Name, newly_ready: &mut Vec<(Name, NameSet)>| {
                  if let Some(dependents) = reverse_deps_ref.get(name) {
                    for dependent_lo in dependents.value() {
                      if let Some(entry) = block_info_ref.get(dependent_lo) {
                        let (dep_all, _, remaining) = entry.value();
                        let mut deps = remaining.lock().unwrap();
                        let was_present = deps.remove(name);
                        if was_present && deps.is_empty() {
                          newly_ready
                            .push((dependent_lo.clone(), dep_all.clone()));
                        }
                      }
                    }
                  }
                };

              // For each name in this block, resolve deps
              for name in &all {
                resolve_name(name, &mut newly_ready);
              }

              // Drain pending aux_gen names and resolve their deps.
              // Only processes names added since the last drain, not the
              // full accumulated set (which is kept in aux_gen_extra_names
              // for persistent membership checks).
              {
                let extra: Vec<Name> =
                  std::mem::take(&mut *stt_ref.aux_gen_pending.lock().unwrap());
                for name in &extra {
                  resolve_name(name, &mut newly_ready);
                }
              }

              // Add newly-ready blocks to the queue and notify waiting workers
              if !newly_ready.is_empty() {
                let mut queue = ready_queue_ref.lock().unwrap();
                queue.extend(newly_ready);
                condvar_ref.notify_all();
              }

              let done = completed_ref.fetch_add(1, AtomicOrdering::SeqCst) + 1;
              // Wake all workers only when all blocks are done (so they
              // can exit), otherwise just wake one to avoid thundering herd.
              if done == total_blocks {
                condvar_ref.notify_all();
              } else {
                condvar_ref.notify_one();
              }
            },
            None => {
              // No work available - check if we're done
              if completed_ref.load(AtomicOrdering::SeqCst) == total_blocks {
                return;
              }
              // Check for errors
              if error_ref.lock().unwrap().is_some() {
                return;
              }
              // Wait for new work to become available
              let queue = ready_queue_ref.lock().unwrap();
              let _ = condvar_ref
                .wait_timeout(queue, std::time::Duration::from_millis(10))
                .unwrap();
            },
          }
        }
      });
    }
  });

  // Check for errors
  if let Some(e) = error.into_inner().unwrap() {
    return Err(e);
  }

  // Verify completion
  let final_completed = completed.load(AtomicOrdering::SeqCst);
  if final_completed != total_blocks {
    // Find what's still blocked
    let mut blocked_count = 0;
    for entry in block_info.iter() {
      let (_, _, remaining) = entry.value();
      let deps = remaining.lock().unwrap();
      if !deps.is_empty() {
        blocked_count += 1;
        if blocked_count <= 5 {
          eprintln!(
            "Still blocked: {:?} with {} deps remaining: {:?}",
            entry.key().pretty(),
            deps.len(),
            deps.iter().map(|n| n.pretty()).collect::<Vec<_>>()
          );
        }
      }
    }
    return Err(CompileError::InvalidMutualBlock {
      reason: "circular dependency or missing constant".into(),
    });
  }

  Ok(stt)
}

/// Seed names for the aux_gen prereq closure.
///
/// These are the exact `Const` refs that `aux_gen` emits in generated
/// `.below` / `.brecOn` / `.brecOn.eq` bodies — grep for `mk_const` in
/// `src/ix/compile/aux_gen/**` to verify. They must all be compiled and
/// registered in `aux_name_to_addr` before any block's aux_gen runs, or
/// else `compile_expr` raises `MissingConstant`.
fn aux_gen_seed_names() -> Vec<Name> {
  let root = Name::anon();
  let eq = Name::str(root.clone(), "Eq".into());
  let heq = Name::str(root.clone(), "HEq".into());
  vec![
    // .below (Type-level): PUnit, PProd — ctors in same SCC
    Name::str(root.clone(), "PUnit".into()),
    Name::str(root.clone(), "PProd".into()),
    // .brecOn.eq — Eq family
    eq.clone(),
    Name::str(eq.clone(), "refl".into()),
    Name::str(eq.clone(), "symm".into()),
    Name::str(eq.clone(), "ndrec".into()),
    // `rfl` is a separate constant (`def rfl : a = a := Eq.refl a` in
    // Init.Prelude), used by `Eq.symm`'s body. The transitive-closure
    // walker should find it via Eq.symm's block_refs, but listing it
    // explicitly guards against ref-graph regressions.
    Name::str(root.clone(), "rfl".into()),
    // .brecOn.eq — HEq family
    heq.clone(),
    Name::str(heq, "refl".into()),
    // .brecOn.eq — heterogeneous-to-homogeneous coercion
    // (used in the indexed-eq path's major-continuation discharge)
    Name::str(root.clone(), "eq_of_heq".into()),
    // .brecOn.eq dummy motive
    Name::str(root, "True".into()),
  ]
}

/// Build the transitive SCC closure of `seeds` using `condensed.block_refs`,
/// then compile each SCC in **reverse topological order** (deps first) into
/// `aux_name_to_addr`. Fails immediately if any SCC fails to compile.
///
/// The reverse-topo order is computed via iterative DFS post-order on the
/// condensed graph. `block_refs` maps each SCC-rep to the names it
/// references; we resolve each referenced name back to its own SCC-rep via
/// `condensed.low_links`.
fn precompile_aux_gen_prereqs(
  condensed: &crate::ix::condense::CondensedBlocks,
  lean_env: &Arc<LeanEnv>,
  stt: &CompileState,
) -> Result<(), CompileError> {
  // Resolve seeds to their SCC reps. Silently skip seeds not in the env
  // (unit-test fixtures, minimal test envs).
  let seed_reps: Vec<Name> = aux_gen_seed_names()
    .into_iter()
    .filter_map(|n| condensed.low_links.get(&n).cloned())
    .collect();

  if seed_reps.is_empty() {
    return Ok(());
  }

  // Iterative DFS post-order: visit each SCC exactly once, emitting after
  // all its dependencies have been emitted. Result is a reverse-topo
  // (dep-first) order.
  let mut order: Vec<Name> = Vec::new();
  let mut visited: FxHashSet<Name> = FxHashSet::default();

  enum Frame {
    Enter(Name),
    Exit(Name),
  }
  let mut stack: Vec<Frame> = seed_reps.into_iter().map(Frame::Enter).collect();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Enter(rep) => {
        if !visited.insert(rep.clone()) {
          continue;
        }
        // Push Exit *before* neighbor Enters so Exit fires after them.
        stack.push(Frame::Exit(rep.clone()));
        // Enqueue SCC deps (the external refs of this SCC, resolved to
        // their SCC reps).
        if let Some(out_refs) = condensed.block_refs.get(&rep) {
          for referenced in out_refs {
            if let Some(dep_rep) = condensed.low_links.get(referenced) {
              if !visited.contains(dep_rep) {
                stack.push(Frame::Enter(dep_rep.clone()));
              }
            }
          }
        }
      },
      Frame::Exit(rep) => {
        order.push(rep);
      },
    }
  }

  // Compile each SCC in dep-first order, moving compiled names to
  // `aux_name_to_addr` so later SCCs can resolve their Const refs.
  for rep in order {
    if stt.aux_name_to_addr.contains_key(&rep) {
      continue; // Already compiled (e.g., via a prior prereq run).
    }
    let all = match condensed.blocks.get(&rep) {
      Some(a) => a.clone(),
      None => continue,
    };
    let mut cache = BlockCache::default();
    compile_const(&rep, &all, lean_env, &mut cache, stt).map_err(|e| {
      CompileError::InvalidMutualBlock {
        reason: format!(
          "aux_gen prereq pre-compile failed for SCC '{}' ({} members): \
           {:?}. The SCC closure is traversed in reverse-topological \
           order starting from the aux_gen seed names (see \
           `aux_gen_seed_names`), so all transitive deps *should* be \
           compiled before this — if you're hitting this, a dep \
           relationship isn't captured in the ref graph, or the source \
           env is inconsistent.",
          rep.pretty(),
          all.len(),
          e,
        ),
      }
    })?;
    // Move compiled names → aux_name_to_addr. The scheduler can still
    // re-encounter this SCC later; the entries will just be no-ops.
    let just_compiled: Vec<(Name, Address)> = stt
      .name_to_addr
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    for (n, addr) in just_compiled {
      stt.name_to_addr.remove(&n);
      stt.aux_name_to_addr.insert(n, addr);
    }
    // Defensive: move any aux_gen extras generated during pre-compile.
    let extras: Vec<Name> =
      stt.aux_gen_extra_names.iter().map(|r| r.clone()).collect();
    for name in extras {
      if let Some((n, addr)) = stt.name_to_addr.remove(&name) {
        stt.aux_name_to_addr.insert(n, addr);
      }
    }
  }

  Ok(())
}
