//! Witness population for the depth pass (Track A, H1).
//!
//! The Lean depth pass (`Aiur.Optimized.Depth`) gives every recursive circuit
//! a depth column `d`, provided as the last word of its call message, and
//! every call slot into a recursive callee the callee's depth word: `d - 1`
//! (exact), `d - 1 - gap` with range-checked gap limbs (gap), or a free
//! column (external, option E1). The executor records each query's honest
//! height, the longest call path below it within its SCC
//! ([`crate::execute`]). Population writes `d`, reads each enabled slot's
//! callee height, splits a gap into limbs and counts the limbs' range-table
//! uses, and checks that an exact slot's callee is exactly one below its
//! caller. Like all population it is untrusted: the circuit and the lookup
//! argument check every word.
use super::*;
use crate::execute::Execution;

/// The SCC of a function without a depth word.
pub(crate) const NO_SCC: u32 = u32::MAX;

/// Population's uses of the `Depth::range{w}` tables, one count vector per
/// range table (the distinct limb widths), allocated on first use.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeCounts(pub Vec<Vec<u64>>);

impl RangeCounts {
  #[inline]
  fn add(&mut self, table: usize, size: usize, value: usize) {
    if self.0.len() <= table {
      self.0.resize(table + 1, vec![]);
    }
    let counts = &mut self.0[table];
    if counts.is_empty() {
      counts.resize(size, 0);
    }
    counts[value] += 1;
  }

  /// Element-wise sum.
  pub fn merge(mut self, other: Self) -> Self {
    if self.0.len() < other.0.len() {
      self.0.resize(other.0.len(), vec![]);
    }
    for (mine, theirs) in self.0.iter_mut().zip(other.0) {
      if mine.is_empty() {
        *mine = theirs;
      } else {
        for (a, b) in mine.iter_mut().zip(theirs) {
          *a += b;
        }
      }
    }
    self
  }

  /// Counts from one flat buffer holding every range table in turn.
  #[cfg(feature = "cuda")]
  pub(super) fn from_flat(
    widths: impl Iterator<Item = u32>,
    flat: &[u64],
  ) -> Self {
    let mut start = 0;
    Self(
      widths
        .map(|width| {
          let end = start + (1usize << width);
          let counts = flat[start..end].to_vec();
          start = end;
          counts
        })
        .collect(),
    )
  }

  /// Uses of range table `table`, row by row (empty when unused).
  pub fn table(&self, table: usize) -> &[u64] {
    self.0.get(table).map_or(&[], Vec::as_slice)
  }
}

/// A slot's new columns: the first gap limb, or the external depth word.
pub(super) enum Kind {
  Gap(usize),
  External(usize),
}

pub(super) struct SlotFill {
  pub(super) kind: Kind,
  pub(super) enable: Polynomial,
  /// The send's arguments without its final depth word: the callee query.
  pub(super) args: Vec<Polynomial>,
  /// The functions whose rows the callee circuit holds.
  pub(super) callees: Vec<usize>,
}

/// An exact slot's callee query. Exact slots add no column, but population
/// checks that the callee's recorded height is the caller's minus one, so a
/// slot the Lean planner misclassified fails here, by name, rather than as an
/// unbalanced lookup at verification.
struct ExactCheck {
  channel: String,
  enable: Polynomial,
  /// The send's arguments without its final depth word: the callee query.
  args: Vec<Polynomial>,
  /// The functions whose rows the callee circuit holds.
  callees: Vec<usize>,
}

/// One circuit's depth columns (exact slots need none), and its exact slots.
pub(super) struct DepthFill {
  pub(super) column: Option<usize>,
  pub(super) slots: Vec<SlotFill>,
  exact: Vec<ExactCheck>,
}

impl DepthFill {
  pub(super) fn is_empty(&self) -> bool {
    self.column.is_none() && self.slots.is_empty()
  }
}

/// A range table: the limb width and the map's callable index.
pub(super) struct RangeTable {
  pub width: u32,
  pub map: usize,
}

/// Depth population for every circuit of a trace plan.
pub(super) struct DepthPlan {
  pub fills: Vec<DepthFill>,
  /// Per limb, low first: its width and its range table.
  pub(super) limbs: Vec<(u32, usize)>,
  pub tables: Vec<RangeTable>,
  bits: u32,
}

/// The SCC of every function's circuit, or [`NO_SCC`]: what the executor
/// needs to record honest heights ([`CheckedProgram::track_depth`]).
pub(crate) fn function_sccs(
  artifact: &TraceArtifact,
) -> Result<Vec<u32>, String> {
  let chips: FxHashMap<&str, &Chip> =
    artifact.chips.iter().map(|c| (c.name.as_str(), c)).collect();
  artifact
    .functions
    .iter()
    .map(|f| {
      let chip =
        chips.get(f.chip.as_str()).ok_or("unknown representative chip")?;
      if chip.depth.column.is_none() {
        return Ok(NO_SCC);
      }
      u32::try_from(chip.depth.rank)
        .ok()
        .filter(|&rank| rank != NO_SCC)
        .ok_or_else(|| "depth rank overflow".into())
    })
    .collect()
}

impl DepthPlan {
  /// Validate the depth metadata of `artifact` against its circuits and
  /// compile it. `members[f]` is function `f`'s circuit.
  pub(super) fn compile<B: FieldBackend>(
    artifact: &TraceArtifact,
    chips: &FxHashMap<String, usize>,
    callables: &FxHashMap<String, usize>,
    members: &[usize],
    program: &CheckedProgram<B>,
  ) -> Result<Self, String> {
    let mut tables: Vec<RangeTable> = vec![];
    let mut limbs = vec![];
    let mut bits = 0u32;
    for &width in &artifact.limbs {
      let width = u32::try_from(width)
        .ok()
        .filter(|w| (1..=24).contains(w))
        .ok_or("unsupported depth limb width")?;
      bits += width;
      let table = if let Some(i) = tables.iter().position(|t| t.width == width)
      {
        i
      } else {
        let name = format!("Depth::range{width}");
        let map = *callables.get(&name).ok_or("missing depth range map")?;
        let index = map
          .checked_sub(program.program.functions.len())
          .ok_or("depth range map is a function")?;
        let decl = &program.program.maps[index];
        let input = &program.tables[decl.input];
        if program.inputs[map].width() != 1
          || program.outputs[map].width() != 0
          || input.len() != 1 << width
          || input.iter().enumerate().any(|(n, row)| {
            row.len() != 1 || program.field.to_u64(row[0]) != n as u64
          })
        {
          return Err(format!("malformed depth range map {name}"));
        }
        tables.push(RangeTable { width, map });
        tables.len() - 1
      };
      limbs.push((width, table));
    }
    if bits > 24 {
      return Err("depth gap limbs too wide".into());
    }
    let mut functions = vec![vec![]; artifact.chips.len()];
    for (f, &chip) in members.iter().enumerate() {
      functions[chip].push(f);
    }
    let recursive = |name: &str| {
      chips
        .get(name)
        .map(|&c| &artifact.chips[c])
        .and_then(|c| c.depth.column.map(|_| c))
    };
    let mut fills = vec![];
    for chip in &artifact.chips {
      let depth = &chip.depth;
      if let Some(column) = depth.column
        && (column >= chip.activation || chip.inputs.last() != Some(&column))
      {
        return Err(format!("{}: invalid depth column", chip.name));
      }
      if depth.slots.len() > chip.sends.len() {
        return Err(format!("{}: more depth slots than sends", chip.name));
      }
      let mut slots = vec![];
      let mut exact = vec![];
      for (send, slot) in chip.sends.iter().zip(&depth.slots) {
        let kind = match *slot {
          DepthSlot::Plain => continue,
          DepthSlot::Exact => None,
          DepthSlot::Gap { column } => {
            if column
              .checked_add(limbs.len())
              .is_none_or(|e| e > chip.activation)
            {
              return Err(format!("{}: gap limbs out of bounds", chip.name));
            }
            Some(Kind::Gap(column))
          },
          DepthSlot::External { column } => {
            if column >= chip.activation {
              return Err(format!(
                "{}: external depth out of bounds",
                chip.name
              ));
            }
            Some(Kind::External(column))
          },
        };
        let callee = recursive(&send.channel).ok_or_else(|| {
          format!("{}: depth slot into a circuit without depth", chip.name)
        })?;
        let intra = !matches!(kind, Some(Kind::External(_)));
        if intra && (depth.column.is_none() || callee.depth.rank != depth.rank)
        {
          return Err(format!("{}: intra-SCC slot across SCCs", chip.name));
        }
        let Some((_, args)) = send.args.split_last() else {
          return Err(format!(
            "{}: depth slot without a depth word",
            chip.name
          ));
        };
        let (enable, args) = (send.enable.clone(), args.to_vec());
        let callees = functions[chips[&send.channel]].clone();
        match kind {
          Some(kind) => slots.push(SlotFill { kind, enable, args, callees }),
          None => exact.push(ExactCheck {
            channel: send.channel.clone(),
            enable,
            args,
            callees,
          }),
        }
      }
      fills.push(DepthFill { column: depth.column, slots, exact });
    }
    Ok(Self { fills, limbs, tables, bits })
  }

  /// Fill circuit `chip`'s depth columns in `row`, a populated row of the
  /// query whose height is `depth`, and count its range-table uses.
  #[allow(clippy::too_many_arguments)]
  pub(super) fn fill<B: FieldBackend>(
    &self,
    chip: usize,
    record: &Execution<B>,
    depth: u64,
    row: &mut [B::Element],
    field: B,
    buffer: &mut Vec<B::Element>,
    counts: &mut RangeCounts,
  ) -> Result<(), String> {
    let fill = &self.fills[chip];
    if let Some(column) = fill.column {
      row[column] = field.from_u64(depth);
    }
    for check in &fill.exact {
      if check.enable.eval(row, field) != field.one() {
        continue;
      }
      buffer.clear();
      buffer.extend(check.args.iter().map(|p| p.eval(row, field)));
      let callee = callee_depth(record, &check.callees, buffer)?;
      if callee.checked_add(1) != Some(depth) {
        return Err(format!(
          "exact depth slot into {}: callee height {callee}, caller height \
           {depth}",
          check.channel
        ));
      }
    }
    for slot in &fill.slots {
      if slot.enable.eval(row, field) != field.one() {
        continue;
      }
      buffer.clear();
      buffer.extend(slot.args.iter().map(|p| p.eval(row, field)));
      let callee = callee_depth(record, &slot.callees, buffer)?;
      match slot.kind {
        Kind::External(column) => row[column] = field.from_u64(callee),
        Kind::Gap(column) => {
          let gap = depth
            .checked_sub(callee)
            .and_then(|n| n.checked_sub(1))
            .ok_or("callee is not below its caller")?;
          if gap >> self.bits != 0 {
            return Err(format!("depth gap {gap} exceeds 2^{}", self.bits));
          }
          let mut rest = gap;
          for (i, &(width, table)) in self.limbs.iter().enumerate() {
            let limb = rest & ((1 << width) - 1);
            rest >>= width;
            row[column + i] = field.from_u64(limb);
            counts.add(
              table,
              1 << width,
              usize::try_from(limb).map_err(|e| e.to_string())?,
            );
          }
        },
      }
    }
    Ok(())
  }
}

/// The recorded height of the callee query `args` of a slot: from whichever
/// of the callee circuit's functions recorded it, or from the deferred
/// heights when another record owns it.
fn callee_depth<B: FieldBackend>(
  record: &Execution<B>,
  callees: &[usize],
  args: &[B::Element],
) -> Result<u64, String> {
  for &f in callees {
    let table = &record.queries.tables[f];
    if let Some(id) = table.lookup(args).1 {
      if table.count(id) == 0 {
        return Err("pending recorded callee".into());
      }
      return Ok(table.depth(id));
    }
  }
  callees
    .iter()
    .find_map(|&f| record.deferred_height(f, args))
    .ok_or_else(|| "missing recorded callee height".into())
}

/// One SCC of recursive circuits in a record (follow-ups G1/G2).
#[derive(Clone, Debug, Serialize)]
pub struct SccStatistics {
  pub rank: u64,
  pub circuits: Vec<String>,
  pub rows: usize,
  /// The highest honest height: the longest call path within the SCC.
  pub max_height: u64,
}

/// Depth-pass statistics of a record and its population: heights per SCC,
/// and the largest gap limbs, whose widths bound a gap (`[16, 8]`: the gap
/// is `lo + 2^16 hi`).
#[derive(Clone, Debug, Default, Serialize)]
pub struct DepthStatistics {
  pub sccs: Vec<SccStatistics>,
  pub limbs: Vec<usize>,
  /// Per range table: its width and the largest limb counted in it.
  pub max_limbs: Vec<(u32, Option<usize>)>,
  pub gap_slot_uses: u64,
}

impl<B: FieldBackend> TracePlan<'_, B> {
  /// Heights per SCC in `record` and the largest gap limbs `ranges` counted.
  pub fn depth_statistics(
    &self,
    record: &Execution<B>,
    ranges: &RangeCounts,
  ) -> DepthStatistics {
    let mut sccs: Vec<SccStatistics> = vec![];
    for (f, &chip) in self.members.iter().enumerate() {
      let chip = &self.artifact.chips[chip];
      if chip.depth.column.is_none() {
        continue;
      }
      let table = &record.queries.tables[f];
      let max = (0..table.len()).map(|q| table.depth(q)).max().unwrap_or(0);
      let scc =
        if let Some(i) = sccs.iter().position(|s| s.rank == chip.depth.rank) {
          &mut sccs[i]
        } else {
          sccs.push(SccStatistics {
            rank: chip.depth.rank,
            circuits: vec![],
            rows: 0,
            max_height: 0,
          });
          sccs.last_mut().unwrap()
        };
      if !scc.circuits.contains(&chip.name) {
        scc.circuits.push(chip.name.clone());
      }
      scc.rows += table.len();
      scc.max_height = scc.max_height.max(max);
    }
    sccs.sort_by_key(|s| std::cmp::Reverse(s.max_height));
    let max_limbs = self
      .depth
      .tables
      .iter()
      .enumerate()
      .map(|(t, table)| {
        (table.width, ranges.table(t).iter().rposition(|&n| n != 0))
      })
      .collect();
    let table0_limbs =
      self.depth.limbs.iter().filter(|&&(_, t)| t == 0).count().max(1) as u64;
    DepthStatistics {
      sccs,
      limbs: self.artifact.limbs.clone(),
      max_limbs,
      gap_slot_uses: ranges.table(0).iter().sum::<u64>() / table0_limbs,
    }
  }
}
