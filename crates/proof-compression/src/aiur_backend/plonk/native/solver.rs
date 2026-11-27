//! Two-phase witness solver for `ix-aiur-scs-v1` constraint systems over both
//! `Bn254` and `Bls12381`.
//!
//! Mirrors the exact semantics of `tools/gnark/aiur_plonk_scs_wires.go` without
//! Go or `big.Int` overhead:
//! - Phase 1 assigns input wires (`kind == 0`), solves all pre-commitment wires
//!   needed by gates `0..scs.pre`, verifies all pre-commitment gates, and
//!   extracts the committed wire values for the BSB22 commitment.
//! - Phase 2 injects `wires[scs.gamma] = gamma_challenge`, solves all remaining
//!   post-commitment wires using Montgomery batch inversion for quotient batches
//!   (`u * d = n`) and fast linear chain evaluation (`u_k = u_{k-1} + t_k`),
//!   and verifies 100% of gates satisfy `qL·a + qR·b + qO·c + qM·a·b + qC == 0`.

use super::scs_file::{
  SEL_L, SEL_M, SEL_O, SEL_R, ScsFile, WireHint, i8_to_fr,
};
use super::transcript::decode_fr_be_canonical;
use crate::kzg::curve::KzgCurve;
use ark_ff::{Field, PrimeField, Zero};
use p3_maybe_rayon::prelude::*;
use std::collections::{HashMap, HashSet};

const DIV_BATCH: usize = 1024;
const CHAIN_SEGMENT: usize = 1 << 14;

/// Parse a gnark-compatible binary witness (`pub_count: u32 BE`,
/// `sec_count: u32 BE`, `total: u32 BE`, followed by `total` canonical 32-byte
/// big-endian `C::Fr` values).
pub fn parse_binary_witness<C: KzgCurve>(
  data: &[u8],
  expected_publics: usize,
  expected_cells: usize,
) -> Result<Vec<C::Fr>, String> {
  if data.len() < 12 {
    return Err("binary witness shorter than 12-byte header".into());
  }
  let publics =
    u32::from_be_bytes(data[0..4].try_into().expect("4 bytes")) as usize;
  let secrets =
    u32::from_be_bytes(data[4..8].try_into().expect("4 bytes")) as usize;
  let total =
    u32::from_be_bytes(data[8..12].try_into().expect("4 bytes")) as usize;
  if publics != expected_publics
    || total != expected_cells
    || publics.checked_add(secrets) != Some(total)
  {
    return Err(format!(
      "binary witness header ({publics} pub, {secrets} sec, {total} total) \
       differs from SCS ({expected_publics} pub, {expected_cells} cells)"
    ));
  }
  let expected_len = 12usize
    .checked_add(total.checked_mul(32).ok_or("witness byte length overflow")?)
    .ok_or("witness byte length overflow")?;
  if data.len() != expected_len {
    return Err(format!(
      "binary witness length {} differs from expected {expected_len}",
      data.len()
    ));
  }
  let mut wires = Vec::with_capacity(total);
  for i in 0..total {
    let off = 12 + 32 * i;
    let word: &[u8; 32] = data[off..off + 32].try_into().expect("32 bytes");
    let val = decode_fr_be_canonical::<C>(word)
      .map_err(|e| format!("witness wire {i}: {e}"))?;
    wires.push(val);
  }
  Ok(wires)
}

/// Intermediate state between Phase 1 (pre-commitment) and Phase 2
/// (post-commitment) witness solving.
#[derive(Clone, Debug)]
pub struct PreCommitmentState<C: KzgCurve> {
  pub wires: Vec<C::Fr>,
  assigned: Vec<bool>,
  pub committed_values: Vec<C::Fr>,
}

/// Gate solved algebraically for one wire `u`.
/// - When `!div`: `u = Σ terms[i].1 * w[terms[i].0] + (if prod { pc * w[pa] * w[pb] } else { 0 }) + k`.
/// - When `div`:  `u * (d0 + dc * w[dw]) = Σ terms[i].1 * w[terms[i].0] + k`.
#[derive(Clone, Copy, Debug)]
struct SolveForm<C: KzgCurve> {
  terms: [(u32, C::Fr); 3],
  n_terms: usize,
  prod: bool,
  pa: u32,
  pb: u32,
  pc: C::Fr,
  k: C::Fr,
  div: bool,
  dw: u32,
  d0: C::Fr,
  dc: C::Fr,
}

impl<C: KzgCurve> SolveForm<C> {
  fn from_gate(
    scs: &ScsFile<C>,
    gate_idx: usize,
    u: u32,
  ) -> Result<Self, String> {
    let g = scs.gate(gate_idx);
    let al = scs.coeffs[g.alpha_id as usize];
    let be = scs.coeffs[g.beta_id as usize];
    let om = scs.coeffs[g.omega_id as usize];
    let sl = g.sel & SEL_L != 0;
    let sr = g.sel & SEL_R != 0;
    let so = g.sel & SEL_O != 0;
    let sm = g.sel & SEL_M != 0;
    let ua = g.a == u;
    let ub = g.b == u;
    let uc = g.c == u;
    if !ua && !ub && !uc {
      return Err(format!("gate {gate_idx} does not contain solved wire {u}"));
    }
    if sm && ua && ub {
      return Err(format!("gate {gate_idx} is quadratic in solved wire {u}"));
    }

    let mut a_coeff = C::FR_ZERO;
    if ua && sl {
      a_coeff += al;
    }
    if ub && sr {
      a_coeff += be;
    }
    if uc && so {
      a_coeff += om;
    }
    let qm = if sm { al * be } else { C::FR_ZERO };

    let mut terms = [(0u32, C::FR_ZERO); 3];
    let mut n_terms = 0usize;
    if !ua && sl {
      terms[n_terms] = (g.a, al);
      n_terms += 1;
    }
    if !ub && sr {
      terms[n_terms] = (g.b, be);
      n_terms += 1;
    }
    if !uc && so {
      terms[n_terms] = (g.c, om);
      n_terms += 1;
    }
    let mut k = i8_to_fr::<C>(g.qc);

    let mut form = Self {
      terms,
      n_terms,
      prod: false,
      pa: 0,
      pb: 0,
      pc: C::FR_ZERO,
      k,
      div: false,
      dw: 0,
      d0: C::FR_ZERO,
      dc: C::FR_ZERO,
    };

    let scale = if sm && (ua != ub) {
      form.div = true;
      form.d0 = a_coeff;
      form.dc = qm;
      form.dw = if ua { g.b } else { g.a };
      -C::FR_ONE
    } else {
      let inv_a = a_coeff.inverse().ok_or_else(|| {
        format!("gate {gate_idx} does not determine wire {u} (zero coeff)")
      })?;
      let neg_inv = -inv_a;
      if sm && !ua && !ub {
        form.prod = true;
        form.pa = g.a;
        form.pb = g.b;
        form.pc = qm * neg_inv;
      }
      neg_inv
    };

    for item in &mut form.terms[..form.n_terms] {
      item.1 *= scale;
    }
    k *= scale;
    form.k = k;
    Ok(form)
  }

  #[inline]
  fn is_quotient(&self) -> bool {
    self.div && self.d0.is_zero() && self.n_terms == 1 && self.k.is_zero()
  }

  /// If this gate is a chain link `u = w[pred] + c * w[other]`, return the
  /// index (`0` or `1`) of `pred` in `self.terms`.
  #[inline]
  fn link_index(&self) -> Option<usize> {
    if self.div || self.prod || self.n_terms != 2 || !self.k.is_zero() {
      return None;
    }
    (0..2).find(|&i| self.terms[i].1 == C::FR_ONE)
  }

  #[inline]
  fn push_reads(&self, out: &mut Vec<u32>) {
    for &(w, _) in &self.terms[..self.n_terms] {
      out.push(w);
    }
    if self.prod {
      out.push(self.pa);
      out.push(self.pb);
    }
    if self.div {
      out.push(self.dw);
    }
  }

  #[inline]
  fn eval_single(
    &self,
    wires: &[C::Fr],
    gate_idx: usize,
  ) -> Result<C::Fr, String> {
    let mut rhs = self.k;
    for &(w, c) in &self.terms[..self.n_terms] {
      rhs += c * wires[w as usize];
    }
    if self.div {
      let denom = self.d0 + self.dc * wires[self.dw as usize];
      let inv = denom.inverse().ok_or_else(|| {
        format!("gate {gate_idx} division by zero while solving wire")
      })?;
      Ok(rhs * inv)
    } else {
      if self.prod {
        rhs += self.pc * wires[self.pa as usize] * wires[self.pb as usize];
      }
      Ok(rhs)
    }
  }
}

/// Montgomery batch inversion in place, failing cleanly if any entry is zero.
pub fn batch_invert_in_place<C: KzgCurve>(
  values: &mut [C::Fr],
) -> Result<(), String> {
  let n = values.len();
  if n == 0 {
    return Ok(());
  }
  let mut prefix = Vec::with_capacity(n);
  let mut acc = C::FR_ONE;
  for (i, &v) in values.iter().enumerate() {
    if v.is_zero() {
      return Err(format!("zero denominator at batch index {i}"));
    }
    prefix.push(acc);
    acc *= v;
  }
  let mut inv_acc = acc
    .inverse()
    .ok_or_else(|| "zero product in batch inversion".to_owned())?;
  for i in (0..n).rev() {
    let orig = values[i];
    values[i] = inv_acc * prefix[i];
    inv_acc *= orig;
  }
  Ok(())
}

#[inline]
fn extract_bit<C: KzgCurve>(value: C::Fr, bit: u32) -> C::Fr {
  let limbs = value.into_bigint().0;
  let word = (bit / 64) as usize;
  let shift = bit % 64;
  let bit_val = if word < limbs.len() { (limbs[word] >> shift) & 1 } else { 0 };
  C::Fr::from(bit_val)
}

fn wire_reads<C: KzgCurve>(
  scs: &ScsFile<C>,
  wire: u32,
  out: &mut Vec<u32>,
) -> Result<(), String> {
  match scs.hint(wire) {
    WireHint::Input | WireHint::Challenge | WireHint::Free => Ok(()),
    WireHint::Bit { wire: src, .. } => {
      out.push(src);
      Ok(())
    },
    WireHint::Solve { gate } => {
      let form = SolveForm::from_gate(scs, gate as usize, wire)?;
      form.push_reads(out);
      Ok(())
    },
  }
}

fn eval_single_wire<C: KzgCurve>(
  scs: &ScsFile<C>,
  wire: u32,
  wires: &mut [C::Fr],
  assigned: &mut [bool],
) -> Result<(), String> {
  let val = match scs.hint(wire) {
    WireHint::Free => C::FR_ZERO,
    WireHint::Bit { wire: src, bit } => {
      extract_bit::<C>(wires[src as usize], bit)
    },
    WireHint::Solve { gate } => {
      let form = SolveForm::from_gate(scs, gate as usize, wire)?;
      form.eval_single(wires, gate as usize)?
    },
    WireHint::Input | WireHint::Challenge => {
      return Err(format!("wire {wire} unexpectedly unassigned"));
    },
  };
  wires[wire as usize] = val;
  assigned[wire as usize] = true;
  Ok(())
}

/// Phase 1: assign all input wires, solve every wire read by pre-commitment
/// gates `0..scs.pre`, verify all pre-commitment gates hold, and extract the
/// committed wire values for the BSB22 commitment.
pub fn solve_pre_commitment<C: KzgCurve>(
  scs: &ScsFile<C>,
  input_wires: &[C::Fr],
) -> Result<PreCommitmentState<C>, String> {
  if input_wires.len() != scs.cells {
    return Err(format!(
      "expected {} input wires (cells), got {}",
      scs.cells,
      input_wires.len()
    ));
  }
  let mut wires = vec![C::FR_ZERO; scs.wires];
  let mut assigned = vec![false; scs.wires];
  wires[..scs.cells].copy_from_slice(input_wires);
  assigned[..scs.cells].fill(true);

  let mut stack: Vec<u32> = Vec::new();
  let mut active: HashSet<u32> = HashSet::new();
  let mut reads: Vec<u32> = Vec::new();

  for gate_idx in 0..scs.pre {
    let g = scs.gate(gate_idx);
    for w in [g.a, g.b, g.c] {
      if assigned[w as usize] {
        continue;
      }
      stack.push(w);
      while let Some(&y) = stack.last() {
        if assigned[y as usize] {
          stack.pop();
          continue;
        }
        match scs.hint(y) {
          WireHint::Free => {
            wires[y as usize] = C::FR_ZERO;
            assigned[y as usize] = true;
            stack.pop();
            continue;
          },
          WireHint::Challenge => {
            return Err(format!(
              "pre-commitment gate {gate_idx} depends on commitment challenge gamma (wire {y})"
            ));
          },
          WireHint::Input => {
            return Err(format!("input wire {y} unassigned"));
          },
          WireHint::Solve { gate } => {
            if (gate as usize) >= scs.pre {
              return Err(format!(
                "pre-commitment gate {gate_idx} reads post-commitment wire {y} (gate {gate})"
              ));
            }
          },
          WireHint::Bit { .. } => {},
        }
        reads.clear();
        wire_reads(scs, y, &mut reads)?;
        let mut pushed = false;
        for &dep in &reads {
          if !assigned[dep as usize] {
            if !pushed {
              if active.contains(&y) {
                return Err(format!(
                  "cyclic pre-commitment dependency on wire {y}"
                ));
              }
              active.insert(y);
              pushed = true;
            }
            stack.push(dep);
          }
        }
        if !pushed {
          active.remove(&y);
          eval_single_wire(scs, y, &mut wires, &mut assigned)?;
          stack.pop();
        }
      }
    }
  }

  // Verify every pre-commitment gate holds.
  let failed = (0..scs.pre)
    .into_par_iter()
    .find_any(|&i| !scs.eval_gate(i, &wires).is_zero());
  if let Some(i) = failed {
    return Err(format!("pre-commitment gate {i} unsatisfied"));
  }

  let committed_values =
    scs.commits.iter().map(|&w| wires[w as usize]).collect();
  Ok(PreCommitmentState { wires, assigned, committed_values })
}

struct ChainInfo {
  base: u32,
  units: Vec<usize>,
}

enum UnitKind {
  Quotients,
  Chain { chain_idx: usize, seg_idx: usize },
}

struct PostUnit {
  ws: Vec<u32>,
  kind: UnitKind,
  active: bool,
  dissolved: bool,
}

/// Phase 2: inject `gamma_challenge` at `scs.gamma`, solve all remaining
/// post-commitment wires using batched Montgomery inversions for quotients and
/// segmented chains for running sums, and verify 100% of gates `0..scs.gates`.
pub fn solve_post_commitment<C: KzgCurve>(
  scs: &ScsFile<C>,
  state: PreCommitmentState<C>,
  gamma_challenge: C::Fr,
) -> Result<Vec<C::Fr>, String> {
  let mut wires = state.wires;
  let mut assigned = state.assigned;
  wires[scs.gamma as usize] = gamma_challenge;
  assigned[scs.gamma as usize] = true;

  let post_gates = scs.gates_count - scs.pre;
  let mut solved_by = vec![u32::MAX; post_gates];
  for w_idx in 0..scs.wires {
    let w = u32::try_from(w_idx).expect("wire fits u32");
    if let WireHint::Solve { gate } = scs.hint(w) {
      let g_idx = gate as usize;
      if g_idx >= scs.pre {
        let slot = g_idx - scs.pre;
        if solved_by[slot] != u32::MAX {
          return Err(format!("gate {gate} solves two wires"));
        }
        solved_by[slot] = w;
      }
    }
  }

  // Classify post-commitment solved wires into quotient batches and chains.
  let mut quotients: Vec<u32> = Vec::new();
  let mut links: Vec<u32> = Vec::new();
  let mut next_map: HashMap<u32, u32> = HashMap::new();
  let mut pred_map: HashMap<u32, u32> = HashMap::new();

  for (rel, &w) in solved_by.iter().enumerate() {
    if w == u32::MAX {
      continue;
    }
    let gate_idx = scs.pre + rel;
    let form = SolveForm::from_gate(scs, gate_idx, w)?;
    if form.is_quotient() {
      quotients.push(w);
      continue;
    }
    if let Some(link_idx) = form.link_index() {
      let pred = form.terms[link_idx].0;
      next_map.entry(pred).or_insert(w);
      pred_map.insert(w, pred);
      links.push(w);
    }
  }

  let mut unit_of = vec![u32::MAX; scs.wires];
  let mut units: Vec<PostUnit> = Vec::new();
  let mut chains: Vec<ChainInfo> = Vec::new();

  for chunk in quotients.chunks(DIV_BATCH) {
    let u_idx = units.len();
    let u_u32 = u32::try_from(u_idx).expect("unit count fits u32");
    for &w in chunk {
      unit_of[w as usize] = u_u32;
    }
    units.push(PostUnit {
      ws: chunk.to_vec(),
      kind: UnitKind::Quotients,
      active: false,
      dissolved: false,
    });
  }

  for &x in &links {
    let base = pred_map[&x];
    if pred_map.contains_key(&base) && next_map.get(&base) == Some(&x) {
      continue;
    }
    let mut ws = Vec::new();
    let mut cur = x;
    loop {
      ws.push(cur);
      match next_map.get(&cur) {
        Some(&nxt) => cur = nxt,
        None => break,
      }
    }
    let chain_idx = chains.len();
    let mut chain_units = Vec::new();
    for (seg_idx, seg) in ws.chunks(CHAIN_SEGMENT).enumerate() {
      let u_idx = units.len();
      let u_u32 = u32::try_from(u_idx).expect("unit count fits u32");
      for &w in seg {
        unit_of[w as usize] = u_u32;
      }
      chain_units.push(u_idx);
      units.push(PostUnit {
        ws: seg.to_vec(),
        kind: UnitKind::Chain { chain_idx, seg_idx },
        active: false,
        dissolved: false,
      });
    }
    chains.push(ChainInfo { base, units: chain_units });
  }

  let mut active_single: HashSet<u32> = HashSet::new();
  let mut stack: Vec<u32> = Vec::new();
  let mut deps: Vec<u32> = Vec::new();
  let mut reads: Vec<u32> = Vec::new();

  for gate_idx in scs.pre..scs.gates_count {
    let g = scs.gate(gate_idx);
    for root in [g.a, g.b, g.c] {
      if assigned[root as usize] {
        continue;
      }
      stack.push(root);
      while let Some(&y) = stack.last() {
        if assigned[y as usize] {
          stack.pop();
          continue;
        }
        match scs.hint(y) {
          WireHint::Free => {
            wires[y as usize] = C::FR_ZERO;
            assigned[y as usize] = true;
            stack.pop();
            continue;
          },
          WireHint::Solve { .. } | WireHint::Bit { .. } => {},
          WireHint::Input | WireHint::Challenge => {
            return Err(format!("wire {y} read before assignment"));
          },
        }

        // Gather unresolved external dependencies for y (or its unit).
        deps.clear();
        let u_id = unit_of[y as usize];
        if u_id == u32::MAX {
          reads.clear();
          wire_reads(scs, y, &mut reads)?;
          for &d in &reads {
            if !assigned[d as usize] {
              deps.push(d);
            }
          }
        } else {
          let u_idx = u_id as usize;
          for &w in &units[u_idx].ws {
            reads.clear();
            wire_reads(scs, w, &mut reads)?;
            for &d in &reads {
              if !assigned[d as usize] && unit_of[d as usize] != u_id {
                deps.push(d);
              }
            }
          }
          if let UnitKind::Chain { chain_idx, seg_idx } = units[u_idx].kind {
            let base = chains[chain_idx].base;
            if !assigned[base as usize] {
              deps.push(base);
            }
            if seg_idx > 0 {
              let prev_unit = chains[chain_idx].units[seg_idx - 1];
              let prev_last = *units[prev_unit].ws.last().expect("non-empty");
              if !assigned[prev_last as usize] {
                deps.push(prev_last);
              }
            }
          }
        }

        if !deps.is_empty() {
          let is_act = if u_id == u32::MAX {
            active_single.contains(&y)
          } else {
            units[u_id as usize].active
          };
          if is_act {
            if u_id == u32::MAX {
              return Err(format!("wire {y} has a cyclic self-dependency"));
            }
            // Dissolve this group (and remaining segments of its chain) into
            // singletons to break false group-level cycles.
            let u_idx = u_id as usize;
            let to_dissolve: Vec<usize> = match units[u_idx].kind {
              UnitKind::Quotients => vec![u_idx],
              UnitKind::Chain { chain_idx, seg_idx } => {
                let tail = chains[chain_idx].units[seg_idx..].to_vec();
                chains[chain_idx].units.truncate(seg_idx);
                tail
              },
            };
            for k in to_dissolve {
              for &w in &units[k].ws {
                unit_of[w as usize] = u32::MAX;
              }
              units[k].ws.clear();
              units[k].active = false;
              units[k].dissolved = true;
            }
            continue;
          }
          if u_id == u32::MAX {
            active_single.insert(y);
          } else {
            units[u_id as usize].active = true;
          }
          stack.extend_from_slice(&deps);
          continue;
        }

        // All dependencies are ready: evaluate singleton or unit.
        if u_id == u32::MAX {
          active_single.remove(&y);
          eval_single_wire(scs, y, &mut wires, &mut assigned)?;
        } else {
          let u_idx = u_id as usize;
          units[u_idx].active = false;
          match units[u_idx].kind {
            UnitKind::Quotients => {
              let ws = &units[u_idx].ws;
              let mut nums = Vec::with_capacity(ws.len());
              let mut dens = Vec::with_capacity(ws.len());
              for &w in ws {
                let WireHint::Solve { gate } = scs.hint(w) else {
                  return Err(format!("quotient wire {w} missing solve hint"));
                };
                let form = SolveForm::from_gate(scs, gate as usize, w)?;
                let num = form.terms[0].1 * wires[form.terms[0].0 as usize];
                let den = form.dc * wires[form.dw as usize];
                nums.push(num);
                dens.push(den);
              }
              batch_invert_in_place::<C>(&mut dens).map_err(|e| {
                format!("post-commitment quotient batch inversion failed: {e}")
              })?;
              for ((&w, num), inv_den) in ws.iter().zip(nums).zip(dens) {
                wires[w as usize] = num * inv_den;
                assigned[w as usize] = true;
              }
            },
            UnitKind::Chain { chain_idx, seg_idx } => {
              let mut acc = if seg_idx == 0 {
                wires[chains[chain_idx].base as usize]
              } else {
                let prev_u = chains[chain_idx].units[seg_idx - 1];
                let prev_last = *units[prev_u].ws.last().expect("non-empty");
                wires[prev_last as usize]
              };
              for &w in &units[u_idx].ws {
                let WireHint::Solve { gate } = scs.hint(w) else {
                  return Err(format!("chain wire {w} missing solve hint"));
                };
                let form = SolveForm::from_gate(scs, gate as usize, w)?;
                let link_idx = form
                  .link_index()
                  .ok_or_else(|| format!("wire {w} lost chain link form"))?;
                let (other_w, other_c) = form.terms[1 - link_idx];
                acc += other_c * wires[other_w as usize];
                wires[w as usize] = acc;
                assigned[w as usize] = true;
              }
            },
          }
        }
        stack.pop();
      }
    }
  }

  // Verify 100% of all gates in parallel.
  let failed = (0..scs.gates_count)
    .into_par_iter()
    .find_any(|&i| !scs.eval_gate(i, &wires).is_zero());
  if let Some(i) = failed {
    return Err(format!("gate {i} unsatisfied after witness solve"));
  }

  Ok(wires)
}
