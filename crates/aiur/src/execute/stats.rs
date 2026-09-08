//! Optional final-only scans. No per-query instrumentation, unbounded term
//! maps, change to execution results, or use as an admission/prover bound.

use std::{io::Write, sync::LazyLock, time::Instant};

use super::QueryRecord;
use crate::querymap::MultiplicityStats;

static ENABLED: LazyLock<bool> = LazyLock::new(|| {
  std::env::var_os("IX_AIUR_MULTIPLICITY_STATS").is_some_and(|s| s == "1")
});
const TOP_MAPS: usize = 32;

struct MapStats {
  kind: &'static str,
  id: usize,
  counts: MultiplicityStats,
}

struct Snapshot {
  functions: MultiplicityStats,
  memory: MultiplicityStats,
  maps: Vec<MapStats>,
}

impl Snapshot {
  fn collect(record: &QueryRecord) -> Self {
    let mut snapshot = Self {
      functions: MultiplicityStats::default(),
      memory: MultiplicityStats::default(),
      maps: Vec::new(),
    };
    for (kind, id, map) in record
      .function_queries
      .iter()
      .enumerate()
      .map(|(i, m)| ("fn", i, m))
      .chain(record.memory_queries.iter().map(|(&w, m)| ("mem", w, m)))
      .filter(|(_, _, m)| !m.is_empty())
    {
      let counts = map.multiplicity_stats();
      if kind == "fn" {
        snapshot.functions.merge(&counts);
      } else {
        snapshot.memory.merge(&counts);
      }
      snapshot.maps.push(MapStats { kind, id, counts });
    }
    snapshot.maps.sort_unstable_by(|a, b| {
      b.counts
        .rows()
        .cmp(&a.counts.rows())
        .then_with(|| a.kind.cmp(b.kind))
        .then_with(|| a.id.cmp(&b.id))
    });
    snapshot
  }

  fn write(&self, out: &mut impl Write, label: &str) -> std::io::Result<()> {
    write_counts(out, label, "functions", &self.functions)?;
    write_counts(out, label, "memory", &self.memory)?;
    for map in self.maps.iter().take(TOP_MAPS) {
      write_counts(
        out,
        label,
        &format!("{}{}", map.kind, map.id),
        &map.counts,
      )?;
    }
    Ok(())
  }
}

fn write_counts(
  out: &mut impl Write,
  label: &str,
  map: &str,
  counts: &MultiplicityStats,
) -> std::io::Result<()> {
  writeln!(
    out,
    "[aiur-multiplicity] label={label:?} map={map} rows={} counts={:?} segment_maxima={:?} segment_rows={:?} max={} canonical_sum={} full_payload_bytes={} adaptive_payload_lower_bound={} u32_payload_lower_bound={} stored_payload_bytes={} stored_segments_u32_field={:?}",
    counts.rows(),
    counts.counts,
    counts.segments,
    counts.segment_rows,
    counts.max,
    counts.canonical_sum,
    counts.full_payload_bytes(),
    counts.adaptive_payload_bytes(),
    counts.u32_payload_bytes(),
    counts.stored_payload_bytes,
    counts.stored_segments
  )
}

impl QueryRecord {
  /// `IX_AIUR_MULTIPLICITY_STATS=1`: scan initialized counter rows once on
  /// execution return or rejection, while the record still exists. Scratch
  /// is O(function/memory-map count), output is capped at 32 maps plus totals.
  /// "returned" means execution returned, not that a proof was constructed.
  pub fn log_multiplicity_stats(&self, status: &str) {
    if !*ENABLED {
      return;
    }
    let started = Instant::now();
    let snapshot = Snapshot::collect(self);
    let scan_us = started.elapsed().as_micros();
    let label = self.budget.as_ref().map_or("unbudgeted", |b| b.label.as_str());
    // Keep these few lines together, but never hold stderr during the scan.
    // Diagnostics are best effort: a broken output pipe cannot change checking.
    let mut out = std::io::stderr().lock();
    let _ = writeln!(
      out,
      "[aiur-multiplicity] label={label:?} status={status} scan_us={scan_us} maps={} shown={} omitted={} count_bins=0,1,2..255,256..65535,65536..u32max,larger segment_widths=1,2,4,8 snapshot_only=true",
      snapshot.maps.len(),
      snapshot.maps.len().min(TOP_MAPS),
      snapshot.maps.len().saturating_sub(TOP_MAPS)
    );
    if let Some(budget) = &self.budget {
      // Budget peak includes transient reservations, including a local
      // reservation rolled back if the shared parent then refused it.
      let _ = writeln!(
        out,
        "[aiur-multiplicity] label={label:?} accounted_bytes={} reservation_peak_bytes={} record_limit_bytes={}",
        budget.used(),
        budget.peak(),
        budget.limit()
      );
    }
    let _ = snapshot.write(&mut out, label);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{G, bytecode::Toplevel, querymap::QueryMap};
  use multi_stark::p3_field::PrimeCharacteristicRing;

  #[test]
  fn totals_include_memory_hint_rows_and_leave_records_unchanged() {
    let mut record = QueryRecord::new(&Toplevel {
      functions: vec![],
      memory_sizes: vec![1],
      circuits: vec![],
    });
    record.function_queries.push(QueryMap::new(1));
    record.function_queries[0].insert(&[G::ONE], &[], G::TWO).unwrap();
    record.memory_queries[&1].insert(&[G::ONE], &[G::ZERO], G::ZERO).unwrap();
    let snapshot = Snapshot::collect(&record);
    assert_eq!(snapshot.functions.counts, [0, 0, 1, 0, 0, 0]);
    assert_eq!(snapshot.memory.counts, [1, 0, 0, 0, 0, 0]);
    let mut output = Vec::new();
    snapshot.write(&mut output, "shard 0").unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.contains("map=memory rows=1 counts=[1, 0, 0, 0, 0, 0]"));
    assert_eq!(record.function_queries[0].mult_at(0), G::TWO);
    assert_eq!(record.memory_queries[&1].mult_at(0), G::ZERO);
  }

  #[test]
  fn output_is_capped_and_labels_cannot_inject_lines() {
    let counts =
      MultiplicityStats { counts: [0, 1, 0, 0, 0, 0], ..Default::default() };
    let snapshot = Snapshot {
      functions: counts.clone(),
      memory: MultiplicityStats::default(),
      maps: (0..1000)
        .map(|id| MapStats { kind: "fn", id, counts: counts.clone() })
        .collect(),
    };
    let mut output = Vec::new();
    snapshot.write(&mut output, "shard\nnot another event").unwrap();
    let text = String::from_utf8(output).unwrap();
    assert_eq!(text.lines().count(), TOP_MAPS + 2);
    assert!(text.contains("map=fn31 "));
    assert!(!text.contains("map=fn32 "));
    assert!(text.lines().all(|line| line.starts_with("[aiur-multiplicity]")));
  }
}
