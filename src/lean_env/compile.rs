use indexmap::IndexSet;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet, FxHasher};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    sync::{Arc, Mutex},
};

use crate::lean_env::{
    ConstMap, Name,
    ref_graph::{NameSet, RefMap},
};

/// The size of the SCC chunks in which parallel compilation will occur.
/// This constant regulates the maximum recursion depth that can happen
/// in the worst-case scenario when there's a linear dependency between SCCs.
const PAR_CHUNK_SIZE: usize = 1024;

pub fn compile(
    sccs: &RefMap,
    out_refs: &RefMap,
    const_map: &ConstMap,
) -> FxHashMap<Arc<Name>, u64> {
    // The compilation process involves:
    // 1. Finding root SCCs (those with no external dependencies)
    // 2. Building a dependency DAG and sequencing it
    // 3. Compiling SCCs in parallel chunks from leaves to roots
    // 4. Collecting and validating the resulting data

    // Internal macro for safe access to SCC and dependency data.
    macro_rules! get {
        (SCC, $name:expr) => {
            sccs.get($name).expect("Missing SCC")
        };
        (DEPS, $name:expr) => {
            out_refs.get($name).expect("Missing dependencies")
        };
    }

    // Find root SCCs - those that no other SCC depends on.
    let mut roots: FxHashSet<_> = sccs.values().map(NameSetWrap).collect();
    for (name, deps) in out_refs {
        for dep in deps {
            let dep_scc = get!(SCC, dep);
            // Don't remove SCCs due to circular dependencies within the same SCC.
            if !dep_scc.contains(name) {
                roots.remove(&NameSetWrap(dep_scc));
            }
        }
    }

    // Build a sequenced DAG of SCCs with roots on the left and transitive
    // dependencies to the right, reached via DFS.
    let mut dag = IndexSet::with_capacity_and_hasher(sccs.len(), FxBuildHasher);
    for scc_wrap in roots {
        if dag.contains(&scc_wrap) {
            continue;
        }
        dag.insert(scc_wrap.clone());

        // Initiate the stack with the immediate children of the current SCC.
        let mut scc_stack = vec![];
        for name in scc_wrap.0 {
            for dep in get!(DEPS, name) {
                let dep_scc = get!(SCC, dep);
                if !dag.contains(&NameSetWrap(dep_scc)) {
                    scc_stack.push(dep_scc);
                }
            }
        }

        // Pop the last SCC from the stack, add it to the sequenced DAG and push
        // its unvisited children to the stack.
        while let Some(popped_scc) = scc_stack.pop() {
            dag.insert(NameSetWrap(popped_scc));
            for name in popped_scc {
                for dep in get!(DEPS, name) {
                    let dep_scc = get!(SCC, dep);
                    if !dag.contains(&NameSetWrap(dep_scc)) {
                        scc_stack.push(dep_scc);
                    }
                }
            }
        }
    }

    // Reverse the DAG so we process from leaves to roots.
    // This order enables efficient compilation with caching while avoiding the
    // recursion depth limit.
    let dag_rev: Vec<_> = dag.into_iter().rev().collect();

    // Pre-populate hash storage with mutexes for thread-safe updates.
    let mut hashes = HashMap::with_capacity_and_hasher(dag_rev.len(), FxBuildHasher);
    for scc in &dag_rev {
        hashes.insert(scc, Mutex::new(None));
    }

    // Compile SCCs in parallel chunks.
    dag_rev.chunks(PAR_CHUNK_SIZE).for_each(|sccs_chunk| {
        sccs_chunk.par_iter().for_each(|scc_wrap| {
            compile_scc(scc_wrap, sccs, const_map, &hashes);
        });
    });

    // Collect results and validate disjoint SCCs.
    let mut map = FxHashMap::default();
    for mutex in hashes.values() {
        let mutex_lock = mutex.lock().unwrap();
        let scc_hashes = mutex_lock.as_ref().expect("Missing computed hash");
        for (name, hash) in scc_hashes.as_ref() {
            // SCCs are disjoint so there should be no duplicates.
            assert!(map.insert(name.clone(), *hash).is_none());
        }
    }

    // Verify that we computed hashes for all nodes in the dependency graph.
    assert_eq!(map.len(), out_refs.len());
    map
}

/// Wrapper for [`NameSet`] to provide concrete [`Hash`] and [`Eq`] implementations.
#[derive(PartialEq, Eq, Clone)]
struct NameSetWrap<'a>(&'a NameSet);

impl Hash for NameSetWrap<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for name in self.0 {
            name.get_hash().hash(state);
        }
    }
}

/// Thread-safe storage for computed hashes of SCCs.
///
/// This is a specialized hashmap where each value is protected by a mutex,
/// allowing concurrent access to different SCCs without contention.
type HashedEntries<'a> =
    FxHashMap<&'a NameSetWrap<'a>, Mutex<Option<Arc<FxHashMap<Arc<Name>, u64>>>>>;

fn compile_scc(
    scc_wrap: &NameSetWrap<'_>,
    _sccs: &RefMap,
    _const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
) -> Arc<FxHashMap<Arc<Name>, u64>> {
    let mutex = hashes.get(scc_wrap).expect("Missing SCC");
    let scc = scc_wrap.0;
    let mut mutex_lock = mutex.lock().unwrap();

    // Return cached result if already computed.
    if let Some(scc_hashes) = mutex_lock.as_ref() {
        return scc_hashes.clone();
    }

    // Compute hashes based on SCC size.
    let hashes_arc = match scc.len() {
        0 => panic!("Empty SCC"),
        1 => {
            let mut hashes_map = HashMap::with_capacity_and_hasher(1, FxBuildHasher);
            for name in scc {
                let hash = name.get_hash();
                hashes_map.insert(name.clone(), hash);
            }
            Arc::new(hashes_map)
        }
        _ => {
            let mut scc_hasher = FxHasher::default();
            for name in scc {
                name.hash(&mut scc_hasher);
            }
            let scc_hash = scc_hasher.finish();

            let mut hashes_map = HashMap::with_capacity_and_hasher(scc.len(), FxBuildHasher);
            for name in scc {
                let mut name_hasher = FxHasher::default();
                scc_hash.hash(&mut name_hasher);
                name.hash(&mut name_hasher);
                let hash = name_hasher.finish();
                hashes_map.insert(name.clone(), hash);
            }
            Arc::new(hashes_map)
        }
    };

    // Cache and return the result
    *mutex_lock = Some(hashes_arc.clone());
    hashes_arc
}
