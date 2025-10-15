use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

use crate::{FxIndexSet, lean_env::Name};

pub type NameSet = FxHashSet<Arc<Name>>;

/// A map from names to name sets.
pub type RefMap = FxHashMap<Arc<Name>, NameSet>;

pub fn merge_name_sets(mut a: NameSet, mut b: NameSet) -> NameSet {
    if a.len() < b.len() {
        b.extend(a);
        b
    } else {
        a.extend(b);
        a
    }
}

/// Compute strongly connected components using an iterative Tarjan’s algorithm.
/// Returns a map from each node to the set of nodes in its SCC.
pub fn compute_sccs(ref_map: &RefMap) -> RefMap {
    macro_rules! neighbors {
        ($name:expr) => {
            ref_map.get($name).unwrap().iter().cloned().collect()
        };
    }

    struct Frame {
        node: Arc<Name>,
        neighbors: Vec<Arc<Name>>,
        /// Index of the next neighbor to visit.
        idx: usize,
    }

    let mut index = FxHashMap::default();
    let mut lowlink = FxHashMap::default();
    let mut stack = FxIndexSet::default();
    let mut next_index = 0usize;
    let mut result = RefMap::default();

    let mut work = Vec::<Frame>::new();

    for start in ref_map.keys() {
        if index.contains_key(start) {
            continue;
        }

        work.push(Frame {
            node: start.clone(),
            neighbors: neighbors!(start),
            idx: 0,
        });

        while let Some(frame) = work.last_mut() {
            let v = &frame.node;

            if !index.contains_key(v) {
                index.insert(v.clone(), next_index);
                lowlink.insert(v.clone(), next_index);
                next_index += 1;
                stack.insert(v.clone());
            }

            if frame.idx < frame.neighbors.len() {
                let w = frame.neighbors[frame.idx].clone();
                frame.idx += 1;

                if !index.contains_key(&w) {
                    // Explore new neighbor.
                    work.push(Frame {
                        neighbors: neighbors!(&w),
                        node: w,
                        idx: 0,
                    });
                } else if stack.contains(&w) {
                    // w is on stack.
                    let low_v = *lowlink.get(v).unwrap();
                    let idx_w = *index.get(&w).unwrap();
                    lowlink.insert(v.clone(), low_v.min(idx_w));
                }
            } else {
                // All neighbors processed. Pop and process.
                let frame = work.pop().unwrap();
                let v = frame.node;

                // Update parent's lowlink.
                if let Some(parent) = work.last_mut() {
                    let low_parent = *lowlink.get(&parent.node).unwrap();
                    let low_v = *lowlink.get(&v).unwrap();
                    lowlink.insert(parent.node.clone(), low_parent.min(low_v));
                }

                // Root of SCC?
                if lowlink[&v] == index[&v] {
                    let mut component = NameSet::default();

                    // Pop nodes from stack until we reach v.
                    while let Some(node) = stack.pop() {
                        component.insert(node.clone());
                        if Arc::ptr_eq(&node, &v) {
                            break;
                        }
                    }

                    // Insert all nodes in the component directly into the result.
                    for node in &component {
                        result.insert(node.clone(), component.clone());
                    }
                }
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Arc<Name> {
        Name::mk_str(Name::Anonymous.into(), s.to_string()).into()
    }

    fn map_of(pairs: &[(&Arc<Name>, &[Arc<Name>])]) -> RefMap {
        let mut map = RefMap::default();
        for (k, vs) in pairs {
            map.insert((*k).clone(), vs.iter().cloned().collect());
        }
        map
    }

    fn scc_to_vec(map: &FxHashMap<Arc<Name>, NameSet>) -> Vec<Vec<Arc<Name>>> {
        let mut seen = FxIndexSet::default();
        let mut sccs = Vec::new();
        for (k, set) in map {
            if !seen.contains(k) {
                let mut names: Vec<_> = set.iter().cloned().collect();
                names.sort();
                sccs.push(names);
                seen.extend(set.iter().cloned());
            }
        }
        sccs.sort();
        sccs
    }

    #[test]
    fn single_node() {
        let a = n("A");
        let g = map_of(&[(&a, &[])]);
        let sccs = compute_sccs(&g);
        assert_eq!(scc_to_vec(&sccs), vec![vec![n("A")]]);
    }

    #[test]
    fn simple_cycle() {
        let a = n("A");
        let b = n("B");
        let g = map_of(&[(&a, &[b.clone()]), (&b, &[a.clone()])]);
        let sccs = compute_sccs(&g);
        assert_eq!(scc_to_vec(&sccs), vec![vec![n("A"), n("B")]]);
    }

    #[test]
    fn chain_no_cycle() {
        let a = n("A");
        let b = n("B");
        let c = n("C");
        let g = map_of(&[(&a, &[b.clone()]), (&b, &[c.clone()]), (&c, &[])]);
        let sccs = compute_sccs(&g);
        assert_eq!(
            scc_to_vec(&sccs),
            vec![vec![n("A")], vec![n("B")], vec![n("C")]]
        );
    }

    #[test]
    fn two_cycles_connected() {
        let a = n("A");
        let b = n("B");
        let c = n("C");
        let d = n("D");
        let g = map_of(&[
            (&a, &[b.clone()]),
            (&b, &[a.clone(), c.clone()]),
            (&c, &[d.clone()]),
            (&d, &[c.clone()]),
        ]);
        let sccs = compute_sccs(&g);
        assert_eq!(
            scc_to_vec(&sccs),
            vec![vec![n("A"), n("B")], vec![n("C"), n("D")]]
        );
    }

    #[test]
    fn complex_graph() {
        let a = n("A");
        let b = n("B");
        let c = n("C");
        let d = n("D");
        let e = n("E");
        let f = n("F");
        let g = n("G");
        let h = n("H");

        let graph = map_of(&[
            (&a, &[b.clone()]),
            (&b, &[c.clone(), e.clone(), f.clone()]),
            (&c, &[d.clone(), g.clone()]),
            (&d, &[c.clone(), h.clone()]),
            (&e, &[a.clone(), f.clone()]),
            (&f, &[g.clone()]),
            (&g, &[f.clone()]),
            (&h, &[d.clone(), g.clone()]),
        ]);

        let sccs = compute_sccs(&graph);
        assert_eq!(
            scc_to_vec(&sccs),
            vec![
                vec![n("A"), n("B"), n("E")],
                vec![n("C"), n("D"), n("H")],
                vec![n("F"), n("G")],
            ]
        );
    }
}
