//! Count-only compositions of validated legacy address captures. These omit
//! values and never enter witness generation or establish an execution proof.
use super::*;
use crate::{
  ixby::{
    auth_memory::MemoryDepth,
    memory_log::{MemoryLogSlots, shared_parent_count},
  },
  sizing::CountingEmitter,
};
use batch::BatchShape;
use flock_prover::union::UnionInstance;
use quota_tests::CountedRow;
use std::{collections::BTreeSet, path::PathBuf};

pub(super) fn fuse(rows: &[CountedRow]) -> Vec<CountedRow> {
  let mut out = Vec::new();
  let mut at = 0;
  while at < rows.len() {
    let tail = &rows[at..];
    let starts = |chips: &[Chip]| {
      tail.len() >= chips.len()
        && tail.iter().zip(chips).all(|(r, c)| r.chip == *c)
    };
    let call_arity = (0..Chip::FUSED_CALLS.len()).find(|&arity| {
      let mut chips = vec![Chip::Fetch];
      chips.extend(std::iter::repeat_n(Chip::Resolve, arity));
      chips.push(Chip::Call);
      chips.extend(std::iter::repeat_n(Chip::Resume, arity));
      starts(&chips)
        && tail[2 + arity..2 + 2 * arity]
          .iter()
          .all(|row| row.logical_before == row.logical_after)
    });
    let (chip, len) = if let Some(arity) = call_arity {
      (Chip::FUSED_CALLS[arity], 2 + 2 * arity)
    } else if starts(&[Chip::Fetch, Chip::Resolve, Chip::Control]) {
      (Chip::FusedControl, 3)
    } else if starts(&[
      Chip::Fetch,
      Chip::Resolve,
      Chip::Resolve,
      Chip::Numeric,
    ]) {
      (Chip::FusedNumeric, 4)
    } else if starts(&[Chip::Resume, Chip::Resume])
      && tail[..2].iter().all(|r| r.logical_before == r.logical_after)
    {
      (Chip::CopyPair, 2)
    } else {
      (tail[0].chip, 1)
    };
    let mut addresses = Vec::new();
    for (i, row) in tail[..len].iter().enumerate() {
      if let Some(arity) = chip.call_arity() {
        if i == 1 + arity {
          addresses.extend([row.addresses[0], row.addresses[2]]);
        } else if i > 1 + arity {
          addresses.push(row.addresses[2]);
        } else {
          addresses.extend(&row.addresses);
        }
        continue;
      }
      match chip {
        Chip::FusedControl if i == 2 => addresses.extend(&row.addresses[1..]),
        Chip::FusedNumeric if i == 3 => addresses.extend(&row.addresses[3..]),
        Chip::CopyPair => {
          addresses.extend([row.addresses[0], row.addresses[2]])
        },
        _ => addresses.extend(&row.addresses),
      }
    }
    assert_eq!(addresses.len(), chip.accesses());
    out.push(CountedRow {
      chip,
      logical_before: tail[0].logical_before,
      logical_after: tail[len - 1].logical_after,
      addresses,
    });
    at += len;
  }
  out
}

fn sample(
  name: &str,
  start_clock: u64,
  rows: &[CountedRow],
  shape: BatchShape,
  label: &str,
) {
  let mut quotas = [0; Chip::COUNT];
  for (chip, quota) in shape.chip_quotas() {
    quotas[chip as usize] = quota;
  }
  let mut at = 0;
  let mut clock = start_clock;
  let mut leaves = 0;
  let mut stops = [0; Chip::COUNT + 2];
  while at < rows.len() {
    let first = at;
    let start = clock;
    let mut counts = [0; Chip::COUNT];
    let mut addresses = BTreeSet::new();
    if shape.fused.iter().any(|n| *n > 0) {
      addresses.insert(0); // The circuit authenticates the reserved zero cell.
    }
    let mut parents = shared_parent_count(
      MemoryDepth::new(40).unwrap(),
      addresses.iter().copied().collect(),
      shape.cells,
    )
    .unwrap();
    assert!(parents <= shape.parents.unwrap(), "class cannot fit its padding");
    while let Some(row) = rows.get(at) {
      if counts[row.chip as usize] == quotas[row.chip as usize] {
        stops[row.chip as usize] += 1;
        break;
      }
      let added = row
        .addresses
        .iter()
        .copied()
        .filter(|a| !addresses.contains(a))
        .collect::<BTreeSet<_>>();
      if addresses.len() + added.len() > shape.cells {
        stops[Chip::COUNT] += 1;
        break;
      }
      if !added.is_empty() {
        let next = shared_parent_count(
          MemoryDepth::new(40).unwrap(),
          addresses.iter().chain(&added).copied().collect(),
          shape.cells,
        )
        .unwrap();
        if next > shape.parents.unwrap() {
          stops[Chip::COUNT + 1] += 1;
          break;
        }
        parents = next;
        addresses.extend(added);
      }
      counts[row.chip as usize] += 1;
      clock += u64::from(row.chip.span());
      at += 1;
    }
    assert!(at > first, "class cannot make progress");
    eprintln!(
      "fusion_batch,{label},{name},{leaves},{start},{clock},{},{},{},{},{parents},{counts:?}",
      rows[first].logical_before,
      rows[at - 1].logical_after,
      at - first,
      addresses.len()
    );
    leaves += 1;
  }
  eprintln!("fusion_sample,{label},{name},{leaves},{stops:?}");
}

fn census(shape: BatchShape, label: &str) {
  let mut counter = CountingEmitter::new();
  let class = if shape.fused.iter().any(|n| *n > 0) {
    BatchClass::CslibFused
  } else {
    BatchClass::Cslib2048
  };
  batch::emit_shape(&mut counter, class, shape).unwrap();
  let nu = counter.required_nu(3).unwrap();
  let (registry, counts) = counter.registry(nu);
  let union = UnionInstance::new(&registry, counts);
  eprintln!(
    "fusion_shape,{label},{},{},{},{},{nu},{},{},{},{},{},{:?},{:?}",
    shape.transitions(),
    shape.accesses(),
    shape.cells,
    shape.parents.unwrap(),
    union.dense_m(),
    union.dense_words(),
    union.committed_words(),
    crate::ixby::execution_order::StateChainSlots::linked_plan(
      shape.transitions()
    )
    .unwrap()
    .lanes(),
    MemoryLogSlots::plan(shape.accesses(), shape.cells).unwrap().lanes(),
    shape.quotas,
    shape.fused
  );
}

#[test]
#[ignore = "address-only original captures; counts and exact compiled shapes, no proofs"]
fn captured_fusion_quota_census() {
  let fixture = PathBuf::from(std::env::var_os("IXBY_FUSION_FIXTURE").unwrap());
  let directory =
    PathBuf::from(std::env::var_os("IXBY_FUSION_WINDOWS").unwrap());
  let sources = ["program.ixby", "input.ixbi"].map(|file| {
    *blake3::hash(&std::fs::read(fixture.join(file)).unwrap()).as_bytes()
  });
  let starts = std::env::var("IXBY_FUSION_STARTS")
    .unwrap()
    .split(',')
    .map(|s| s.parse::<u64>().unwrap())
    .collect::<Vec<_>>();
  assert!((1..=64).contains(&starts.len()));
  let scales = std::env::var("IXBY_FUSION_SCALES")
    .unwrap_or_else(|_| "2048".into())
    .split(',')
    .map(|s| s.parse::<usize>().unwrap())
    .collect::<Vec<_>>();
  assert!(scales.iter().all(|s| (512..=4096).contains(s)));
  let base = tuning::fused_reference_shape();
  let mut shapes = vec![(
    "cslib-2048".to_owned(),
    BatchShape::from_class(BatchClass::Cslib2048),
  )];
  shapes.push((
    BatchClass::CslibFused.name().to_owned(),
    BatchShape::from_class(BatchClass::CslibFused),
  ));
  // A candidate file is count-only input: cells, parents, then one positive
  // quota per original and fused chip. It never changes production policy.
  if let Some(path) = std::env::var_os("IXBY_FUSION_CANDIDATE") {
    let words = std::fs::read_to_string(path)
      .unwrap()
      .split_whitespace()
      .map(|s| s.parse::<usize>().unwrap())
      .collect::<Vec<_>>();
    assert_eq!(words.len(), 2 + Chip::COUNT);
    assert!(words.iter().all(|n| (1..=16383).contains(n)));
    shapes.push((
      "candidate".to_owned(),
      BatchShape {
        quotas: words[2..2 + Chip::ALL.len()].try_into().unwrap(),
        fused: words[2 + Chip::ALL.len()..].try_into().unwrap(),
        cells: words[0],
        parents: Some(words[1]),
        nu: 19,
      },
    ));
  }
  for scale in scales {
    if std::env::var_os("IXBY_FUSION_NAMED_ONLY").is_some() {
      break;
    }
    let resize = |n: usize| (n * scale).div_ceil(2048);
    let mut shape = base;
    shape.quotas = shape.quotas.map(resize);
    shape.fused = shape.fused.map(resize);
    shape.nu = 19; // Only the count pass determines the required row domain.
    for (cells, parents) in [(1024, 4095), (1536, 4095), (2048, 6143)] {
      if std::env::var_os("IXBY_FUSION_SWEEP").is_none()
        && (cells, parents) != (1536, 4095)
      {
        continue;
      }
      shape.cells = cells;
      shape.parents = Some(parents);
      shapes.push((format!("fused-{scale}-{cells}-{parents}"), shape));
    }
  }
  for (label, shape) in &shapes {
    census(*shape, label);
  }
  for start in starts {
    let (actual, trace) = profile_tests::read_window(
      &directory.join(format!("window-{start:012}.ixqp")),
      sources,
    )
    .unwrap();
    assert_eq!(actual, start);
    let limit = std::env::var("IXBY_FUSION_WINDOW_LIMIT")
      .map_or(trace.rows.len(), |s| s.parse::<usize>().unwrap());
    assert!((1..=trace.rows.len()).contains(&limit));
    let original = &trace.rows[..limit];
    let fused = fuse(original);
    let mut counts = [0; Chip::COUNT];
    for row in &fused {
      counts[row.chip as usize] += 1;
    }
    let events = |rows: &[CountedRow]| {
      rows.iter().map(|r| r.addresses.len()).sum::<usize>()
    };
    eprintln!(
      "fusion_trace,{},{start},{},{},{},{},{},{},{counts:?}",
      trace.name,
      start + limit as u64,
      original[0].logical_before,
      original.last().unwrap().logical_after,
      fused.len(),
      events(original),
      events(&fused)
    );
    for (label, shape) in &shapes {
      sample(
        &trace.name,
        start,
        if shape.fused == [0; Chip::FUSED.len()] { original } else { &fused },
        *shape,
        label,
      );
    }
  }
}
