//! Concurrency stress for the shared `QueryMap` as an insert-once SET:
//! 63 threads hammer one map over a shared key space with duplicate
//! inserts, races, and keys whose "body" fails (and therefore never
//! inserts). Regression coverage for the design-B contract: the
//! unique-query set is confluent under racing duplicate execution
//! (first publish wins, every probe sees a complete entry with the
//! right output), runtime multiplicities stay untouched on the
//! concurrent path (they are derived at seal, not accumulated), and
//! dedup holds exactly (len == unique inserted keys).

use aiur::G;
use aiur::querymap::QueryMap;
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use std::sync::atomic::{AtomicUsize, Ordering};

/// Worker width of the production box (63 exec threads + watcher).
const THREADS: usize = 63;
/// Shared key space — small enough that every key is heavily contended.
const KEYS: usize = 20_000;
/// Keys whose "body" deterministically fails: they are probed but never
/// inserted, mirroring a kernel reject (an erroring body never reaches
/// its return-insert; nothing marks anything — errors just propagate).
const BAD_EVERY: usize = 97;

fn key(i: usize) -> Vec<G> {
  vec![G::from_usize(i), G::from_usize(i.wrapping_mul(31))]
}

fn out(i: usize) -> G {
  G::from_usize(i + 7)
}

fn is_bad(i: usize) -> bool {
  i % BAD_EVERY == 0
}

/// Sparse-len/marker contract: a pointer RETURNED by `store_cc` is
/// immediately loadable from any thread (its completion marker is
/// Release-published before the pointer exists anywhere); unbound or
/// garbage pointers — any field element — return `None` instead of
/// reading a mid-write slot or walking off the segment table; dedup
/// still yields exactly one pointer per unique value.
#[test]
fn concurrent_store_load_marker_stress() {
  let map = QueryMap::new(2, 1);
  // Published pointers, ptr+1 so 0 means "not yet stored".
  let ptrs: Vec<AtomicUsize> =
    (0..KEYS).map(|_| AtomicUsize::new(0)).collect();
  std::thread::scope(|s| {
    for t in 0..THREADS {
      let (map, ptrs) = (&map, &ptrs);
      s.spawn(move || {
        for step in 0..KEYS {
          let i = (step + t * 41) % KEYS;
          let ptr = map.store_cc(&key(i), true);
          let p = usize::try_from(ptr.as_canonical_u64()).unwrap();
          // Our own returned pointer must load our value, NOW.
          let v = map.load_bump(p, false).expect("own pointer must load");
          assert_eq!(v, key(i).as_slice(), "own load mismatch key {i}");
          ptrs[i].store(p + 1, Ordering::Release);
          // Any pointer another thread has published must also load.
          let j = (i * 7 + t) % KEYS;
          let pj = ptrs[j].load(Ordering::Acquire);
          if pj != 0 {
            let vj = map.load_bump(pj - 1, false).expect("published ptr");
            assert_eq!(vj, key(j).as_slice(), "cross-thread load key {j}");
          }
          // Garbage pointers (arbitrary field elements) never read a
          // slot: far out of range, and just past the frontier.
          assert!(map.load_bump(usize::MAX - t, false).is_none());
          assert!(map.load_bump(1 << 40, false).is_none());
        }
      });
    }
  });
  assert_eq!(map.len(), KEYS, "one entry per unique value");
  let mut seen: Vec<usize> =
    ptrs.iter().map(|p| p.load(Ordering::Acquire) - 1).collect();
  seen.sort_unstable();
  seen.dedup();
  assert_eq!(seen.len(), KEYS, "pointers must be distinct");
}

#[test]
fn concurrent_insert_once_stress() {
  let map = QueryMap::new(2, 1);
  let duplicate_inserts = AtomicUsize::new(0);
  std::thread::scope(|s| {
    for t in 0..THREADS {
      let map = &map;
      let duplicate_inserts = &duplicate_inserts;
      s.spawn(move || {
        // Every thread visits every key in a thread-specific rotation,
        // so racing duplicate "executions" of the same key are common
        // (the design makes them wall-cost only, never wrong).
        for step in 0..KEYS {
          let i = (step + t * 37) % KEYS;
          match map.probe_bump(&key(i), false) {
            Some(o) => {
              // A hit must NEVER surface a wrong or partial output:
              // entries publish complete in a single step.
              assert_eq!(o[0], out(i), "wrong output for key {i}");
            },
            None => {
              // Miss: "execute the body". Bad keys error before their
              // return-insert; everyone else inserts — racers
              // included, exercising first-publish-wins dedup.
              if !is_bad(i) {
                if map.get_index_of(&key(i)).is_some() {
                  duplicate_inserts.fetch_add(1, Ordering::Relaxed);
                }
                map.insert_cc(&key(i), &[out(i)], false);
              }
            },
          }
        }
      });
    }
  });
  // Set invariants at quiescence:
  // 1. Exact dedup — one entry per unique inserted key, none for the
  //    failing keys (they never insert).
  let unique_good = (0..KEYS).filter(|&i| !is_bad(i)).count();
  assert_eq!(map.len(), unique_good, "dedup must be exact");
  // 2. Every good key present with the right output; bad keys absent.
  for i in 0..KEYS {
    match map.get(&key(i)) {
      Some(q) if !is_bad(i) => {
        assert_eq!(q.output[0], out(i), "wrong output for key {i}");
        // 3. The concurrent set path never touches multiplicities —
        //    they are derived at seal, so runtime words must still be
        //    exactly zero no matter how many hits raced.
        assert_eq!(
          q.multiplicity.as_canonical_u64(),
          0,
          "set path must not accumulate multiplicity (key {i})"
        );
      },
      Some(_) => panic!("failing key {i} must never be inserted"),
      None if is_bad(i) => {},
      None => panic!("good key {i} missing"),
    }
  }
  eprintln!(
    "stress: {} entries, {} racing duplicate inserts absorbed",
    map.len(),
    duplicate_inserts.load(Ordering::Relaxed)
  );
}
