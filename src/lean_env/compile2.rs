use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    hash::{Hash, Hasher},
    sync::{
        Arc, Mutex,
        mpsc::{self, Sender},
    },
};

use crate::lean_env::{
    ConstMap, Name,
    ref_graph::{NameSet, RefMap},
};

pub fn compile(
    sccs: &RefMap,
    out_refs: &RefMap,
    const_map: Arc<ConstMap>,
) -> FxHashMap<Arc<Name>, u64> {
    // Internal macro for safe access to SCC and dependency data.
    macro_rules! get {
        (SCC, $name:expr) => {
            sccs.get($name).expect("Missing SCC")
        };
        (DEPS, $name:expr) => {
            out_refs.get($name).expect("Missing dependencies")
        };
    }

    let (sx, rx) = mpsc::channel();

    let mut scc_blocked_map = FxHashMap::default();
    for scc in sccs.values() {
        let scc_arc = Arc::new(scc.clone());
        let mut scc_blocked_by = FxHashSet::default();
        for name in scc {
            for dep in get!(DEPS, name) {
                if !scc.contains(dep) {
                    let dep_scc = get!(SCC, dep);
                    scc_blocked_by.insert(NameSetWrap(dep_scc.clone().into()));
                }
            }
        }

        if scc_blocked_by.is_empty() {
            let unblocked = NameSetWrap(scc_arc);
            let const_map_clone = const_map.clone();
            let sx_clone = sx.clone();
            std::thread::spawn(|| compile_scc(unblocked, const_map_clone, sx_clone));
        } else {
            scc_blocked_map.insert(NameSetWrap(scc_arc), scc_blocked_by);
        }
    }

    for compiled_scc_wrap in rx {
        let mut unblocked_sccs = Vec::new();
        for (maybe_unblocked, blocked_by) in &mut scc_blocked_map {
            blocked_by.remove(&compiled_scc_wrap);
            if blocked_by.is_empty() {
                unblocked_sccs.push(maybe_unblocked.clone());
                let unblocked = maybe_unblocked.clone();
                let const_map_clone = const_map.clone();
                let sx_clone = sx.clone();
                std::thread::spawn(|| compile_scc(unblocked, const_map_clone, sx_clone));
            }
        }
        for unblocked_scc in unblocked_sccs {
            scc_blocked_map.remove(&unblocked_scc);
        }
    }

    todo!()
}

fn compile_scc(scc: NameSetWrap, _const_map: Arc<ConstMap>, sx: Sender<NameSetWrap>) {
    sx.send(scc).unwrap();
}

/// Wrapper for [`NameSet`] to provide concrete [`Hash`] and [`Eq`] implementations.
#[derive(PartialEq, Eq, Clone)]
struct NameSetWrap(Arc<NameSet>);

impl Hash for NameSetWrap {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for name in self.0.as_ref() {
            name.get_hash().hash(state);
        }
    }
}

/// Thread-safe storage for computed hashes of SCCs.
///
/// This is a specialized hashmap where each value is protected by a mutex,
/// allowing concurrent access to different SCCs without contention.
type HashedEntries = FxHashMap<NameSetWrap, Mutex<Option<Arc<FxHashMap<Arc<Name>, u64>>>>>;
