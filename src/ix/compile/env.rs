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

  // Pre-compile PUnit, PProd, Eq, and True so aux_gen can reference them.
  // .below uses PUnit/PProd (for Type-level), .brecOn.eq uses Eq and True.
  // True is used as a dummy motive for non-target classes in the .brecOn.eq
  // recursor-based proof (any Prop type suffices; True has no dependencies).
  // These get compiled into aux_name_to_addr; the scheduler's promotion
  // path in the work loop moves them to name_to_addr when encountered.
  {
    let prereqs = [
      Name::str(Name::anon(), "PUnit".to_string()),
      Name::str(Name::anon(), "PProd".to_string()),
      Name::str(Name::anon(), "Eq".to_string()),
      Name::str(Name::anon(), "True".to_string()),
    ];
    for prereq in &prereqs {
      if let Some((lo, all)) =
        condensed.blocks.iter().find(|(_, all)| all.contains(prereq))
      {
        let lo = lo.clone();
        let all = all.clone();
        let mut cache = BlockCache::default();
        if compile_const(&lo, &all, lean_env, &mut cache, &stt).is_ok() {
          // Move compiled names from name_to_addr → aux_name_to_addr.
          // This prevents the scheduler from treating them as "already done"
          // while still making them available for aux_gen reference resolution.
          let just_compiled: Vec<(Name, Address)> = stt
            .name_to_addr
            .iter()
            .map(|e| (e.key().clone(), e.value().clone()))
            .collect();
          for (n, addr) in just_compiled {
            stt.name_to_addr.remove(&n);
            stt.aux_name_to_addr.insert(n, addr);
          }
          // Also move any aux_gen extras that were generated during
          // pre-compilation (unlikely but defensive).
          let extras: Vec<Name> =
            stt.aux_gen_extra_names.iter().map(|r| r.clone()).collect();
          for name in extras {
            if let Some((n, addr)) = stt.name_to_addr.remove(&name) {
              stt.aux_name_to_addr.insert(n, addr);
            }
          }
        }
      }
    }
  }

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
              if stt_ref.resolve_addr(&lo).is_some() {
                // Check if any names in this block are aux_gen-rewritten.
                let any_aux_gen =
                  all.iter().any(|n| stt_ref.aux_gen_extra_names.contains(n));

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
                    eprintln!(
                      "[compile_env] compile_const_no_aux failed for {}: {}",
                      lo.pretty(),
                      e,
                    );
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
              if elapsed.as_secs_f32() > 1.0 {
                eprintln!(
                  "Slow block {:?} ({} consts): {:.2}s",
                  lo.pretty(),
                  all.len(),
                  elapsed.as_secs_f32()
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

              // Resolve deps for aux_gen "bonus" names compiled during this
              // block (e.g., .below, .below.mk). Don't drain the set — it's
              // used as a persistent marker.
              {
                let extra: Vec<Name> = stt_ref
                  .aux_gen_extra_names
                  .iter()
                  .map(|r| r.clone())
                  .collect();
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

              completed_ref.fetch_add(1, AtomicOrdering::SeqCst);
              // Wake all workers so they can check for completion
              condvar_ref.notify_all();
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
