//! Fixed opening layouts and scalar arithmetic for authenticated profiles.

use super::{
  KzgConfig, Result, Scalar, System, VerifierProfile, hex_json, scalar,
};
use ark_ff::{BigInteger, PrimeField};
use multi_stark::{
  config::ProofConfig,
  expr::Source,
  traits::{Algebra, Field, Pcs},
};
use std::{collections::BTreeSet, fmt::Write as _};

#[derive(Clone, Copy)]
struct CircuitShape {
  height: usize,
  // Main, LogUp, quotient, preprocessed.
  widths: [usize; 4],
  main_next: bool,
  preprocessed_next: bool,
  lookup_group_size: usize,
  omega: Scalar,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MatrixLayout {
  width: usize,
  rows: usize,
  point_offset: usize,
  value_offset: usize,
  groups: [usize; 2],
}

pub(super) struct OpeningLayout {
  matrices: Vec<MatrixLayout>,
  factors: Vec<Scalar>,
  commitment_count: usize,
  point_count: usize,
  field_count: usize,
  fixed_count: usize,
  generator_index: usize,
  coefficient_count: usize,
}

fn add(a: usize, b: usize) -> Result<usize> {
  a.checked_add(b).ok_or_else(|| "Solidity opening offset overflow".into())
}

fn mul(a: usize, b: usize) -> Result<usize> {
  a.checked_mul(b).ok_or_else(|| "Solidity opening offset overflow".into())
}

fn word_offset(index: usize) -> Result<usize> {
  mul(add(index, 1)?, 32)
}

fn log_degree(height: usize) -> Result<usize> {
  if height < 2 || !height.is_power_of_two() {
    return Err(
      "Solidity trace height must be a power of two above one".into(),
    );
  }
  let log = usize::try_from(height.ilog2())?;
  if log > 28 {
    return Err("Solidity trace log degree exceeds 28".into());
  }
  Ok(log)
}

fn quotient_width(max_degree: usize) -> Result<usize> {
  (max_degree.max(2) - 1)
    .checked_next_power_of_two()
    .ok_or_else(|| "Solidity quotient width overflow".into())
}

impl OpeningLayout {
  pub(super) fn new(
    profile: &VerifierProfile,
    system: &System<KzgConfig>,
  ) -> Result<Self> {
    if system.circuits.len() != 2 {
      return Err("Solidity opening layout requires two circuits".into());
    }
    let mut shapes = Vec::with_capacity(2);
    for (ci, circuit) in system.circuits.iter().enumerate() {
      let height = profile.heights[ci];
      log_degree(height)?;
      let domain = system.config.pcs().natural_domain_for_degree(height);
      shapes.push(CircuitShape {
        height,
        widths: [
          circuit.main_width,
          circuit.stage_2_width,
          quotient_width(circuit.max_constraint_degree())?,
          circuit.preprocessed_width,
        ],
        main_next: system.opens_next_row(ci, Source::Main),
        preprocessed_next: system.opens_next_row(ci, Source::Preprocessed),
        lookup_group_size: circuit.lookup_group_size,
        omega: domain.generator(),
      });
    }
    Self::from_shapes(&shapes)
  }

  fn from_shapes(shapes: &[CircuitShape]) -> Result<Self> {
    if shapes.len() != 2 {
      return Err("Solidity opening layout requires two circuits".into());
    }
    for shape in shapes {
      let log = log_degree(shape.height)?;
      if shape.widths[1] == 0
        || shape.widths[3] == 0
        || !(1..=8).contains(&shape.lookup_group_size)
      {
        return Err("invalid Solidity circuit opening shape".into());
      }
      if shape.omega.exp_power_of_2(log) != Scalar::ONE
        || shape.omega.exp_power_of_2(log - 1) == Scalar::ONE
      {
        return Err("Solidity domain generator has incorrect order".into());
      }
    }
    let mut matrices = Vec::with_capacity(8);
    let mut factors = Vec::with_capacity(3);
    let mut commitment_count = 0;
    let mut fixed_count = 0;
    let mut field_count = 1;
    for round in 0..4 {
      for shape in shapes {
        let width = shape.widths[round];
        let rows = match round {
          0 => 1 + usize::from(shape.main_next),
          1 => 2,
          2 => 1,
          _ => 1 + usize::from(shape.preprocessed_next),
        };
        let mut groups = [0; 2];
        // Nonzero zeta preserves equality and first-occurrence order of
        // the row factors, including rows belonging to zero-width matrices.
        for (row, group) in groups.iter_mut().enumerate().take(rows) {
          let factor = if row == 0 { Scalar::ONE } else { shape.omega };
          *group = match factors.iter().position(|&value| value == factor) {
            Some(index) => index,
            None => {
              let index = factors.len();
              factors.push(factor);
              index
            },
          };
        }
        matrices.push(MatrixLayout {
          width,
          rows,
          point_offset: if round == 3 { fixed_count } else { commitment_count },
          value_offset: field_count,
          groups,
        });
        field_count = add(field_count, mul(width, rows)?)?;
        if round == 3 {
          fixed_count = add(fixed_count, width)?;
        } else {
          commitment_count = add(commitment_count, width)?;
        }
      }
    }
    if !(2..=3).contains(&factors.len()) {
      return Err("invalid Solidity evaluation-point count".into());
    }
    let point_count = add(commitment_count, factors.len())?;
    for matrix in &mut matrices[6..] {
      matrix.point_offset = add(matrix.point_offset, point_count)?;
    }
    let generator_index = add(point_count, fixed_count)?;
    let coefficient_count = add(generator_index, 1)?;
    // Include the array length word and the final element's full extent.
    word_offset(field_count)?;
    word_offset(coefficient_count)?;
    word_offset(factors.len())?;
    Ok(Self {
      matrices,
      factors,
      commitment_count,
      point_count,
      field_count,
      fixed_count,
      generator_index,
      coefficient_count,
    })
  }

  pub(super) fn write_functions(&self, out: &mut String) -> Result<()> {
    let count = self.factors.len();
    out.push_str(concat!(
      "\n    function _proofLayout(Profile memory, Proof memory proof)\n",
      "        internal pure override returns (uint256 fieldCount, uint256 fixedCount)\n",
      "    {\n",
    ));
    writeln!(
      out,
      "        if (proof.openingCount != {count}) revert InvalidPacket();"
    )?;
    for (index, matrix) in self.matrices.iter().enumerate() {
      writeln!(
        out,
        "        proof.matrices[{index}] = Matrix({}, {}, {}, {});",
        matrix.width, matrix.rows, matrix.point_offset, matrix.value_offset,
      )?;
    }
    writeln!(out, "        proof.witnessOffset = {};", self.commitment_count)?;
    writeln!(out, "        proof.pointCount = {};", self.point_count)?;
    writeln!(
      out,
      "        return ({}, {});",
      self.field_count, self.fixed_count
    )?;
    out.push_str(concat!(
      "    }\n\n",
      "    function _openingCoefficients(Profile memory, Proof memory proof, uint256[6] memory ch)\n",
      "        internal pure override returns (uint256[] memory coefficients, uint256[] memory witnessCoefficients)\n",
      "    {\n",
      "        if (ch[3] == 0) revert InvalidChallenge();\n",
    ));
    writeln!(
      out,
      "        if (proof.openingCount != {count} || proof.values.length != {}) revert InvalidPacket();",
      self.field_count,
    )?;
    writeln!(
      out,
      "        coefficients = new uint256[]({});",
      self.coefficient_count
    )?;
    writeln!(out, "        witnessCoefficients = new uint256[]({count});")?;
    out.push_str(concat!(
      "        uint256[] memory values = proof.values;\n",
      "        assembly (\"memory-safe\") {\n",
    ));
    let modulus = hex_json(&ark_bls12_381::Fr::MODULUS.to_bytes_be());
    writeln!(out, "            let modulus := {modulus}")?;
    out.push_str(concat!(
      "            let zeta := mload(add(ch, 96))\n",
      "            let v := mload(add(ch, 128))\n",
      "            let r := mload(add(ch, 160))\n",
      "            let generatorSum := 0\n",
    ));
    if count == 3 {
      out.push_str("            let rSquared := mulmod(r, r, modulus)\n");
    }
    let powers = ["1", "r", "rSquared"];
    for (group, power) in powers.iter().enumerate().take(count) {
      writeln!(out, "            let weight{group} := {power}")?;
    }
    let mut remaining = vec![0; count];
    for matrix in &self.matrices {
      for &group in &matrix.groups[..matrix.rows] {
        remaining[group] = add(remaining[group], matrix.width)?;
      }
    }
    let mut seen = BTreeSet::new();
    for matrix in &self.matrices {
      for (row, &group) in matrix.groups[..matrix.rows].iter().enumerate() {
        for column in 0..matrix.width {
          let point = add(matrix.point_offset, column)?;
          let value =
            add(add(matrix.value_offset, mul(row, matrix.width)?)?, column)?;
          let destination =
            format!("add(coefficients, {})", word_offset(point)?);
          let expression = if seen.insert(point) {
            format!("weight{group}")
          } else {
            format!("addmod(mload({destination}), weight{group}, modulus)")
          };
          writeln!(out, "            mstore({destination}, {expression})")?;
          writeln!(
            out,
            "            generatorSum := addmod(generatorSum, mulmod(weight{group}, mload(add(values, {})), modulus), modulus)",
            word_offset(value)?,
          )?;
          remaining[group] -= 1;
          if remaining[group] != 0 {
            writeln!(
              out,
              "            weight{group} := mulmod(weight{group}, v, modulus)"
            )?;
          }
        }
      }
    }
    writeln!(
      out,
      "            mstore(add(coefficients, {}), mod(sub(modulus, generatorSum), modulus))",
      word_offset(self.generator_index)?,
    )?;
    for (group, &factor) in self.factors.iter().enumerate() {
      let point = if factor == Scalar::ONE {
        "zeta".to_owned()
      } else {
        format!("mulmod(zeta, {}, modulus)", scalar(factor))
      };
      let coefficient = if group == 0 {
        point
      } else {
        format!("mulmod({}, {point}, modulus)", powers[group])
      };
      writeln!(
        out,
        "            mstore(add(coefficients, {}), {coefficient})",
        word_offset(add(self.commitment_count, group)?)?,
      )?;
      writeln!(
        out,
        "            mstore(add(witnessCoefficients, {}), {})",
        word_offset(group)?,
        powers[group],
      )?;
    }
    out.push_str("        }\n    }\n");
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::traits::TwoAdicField;

  fn shapes() -> [CircuitShape; 2] {
    [
      CircuitShape {
        height: 32,
        widths: [3, 4, 2, 15],
        main_next: false,
        preprocessed_next: false,
        lookup_group_size: 2,
        omega: Scalar::two_adic_generator(5),
      },
      CircuitShape {
        height: 16,
        widths: [1, 1, 1, 4],
        main_next: false,
        preprocessed_next: false,
        lookup_group_size: 1,
        omega: Scalar::two_adic_generator(4),
      },
    ]
  }

  #[test]
  fn opening_counts_offsets_and_equal_domains() -> Result<()> {
    let mut shapes = shapes();
    let layout = OpeningLayout::from_shapes(&shapes)?;
    assert_eq!(layout.field_count, 37);
    assert_eq!(layout.commitment_count, 12);
    assert_eq!(layout.point_count, 15);
    assert_eq!(layout.fixed_count, 19);
    assert_eq!(layout.generator_index, 34);
    assert_eq!(layout.matrices[6].point_offset, 15);
    assert_eq!(layout.matrices[7].value_offset, 33);
    shapes[1].height = shapes[0].height;
    shapes[1].omega = shapes[0].omega;
    let layout = OpeningLayout::from_shapes(&shapes)?;
    assert_eq!(layout.factors.len(), 2);
    assert_eq!(layout.point_count, 14);
    assert_eq!(layout.generator_index, 33);
    assert_eq!(layout.matrices[2].groups[1], layout.matrices[3].groups[1]);
    Ok(())
  }

  #[test]
  fn grouping_preserves_first_occurrence_and_zero_width_rows() -> Result<()> {
    let mut shapes = shapes();
    shapes[1].main_next = true;
    let layout = OpeningLayout::from_shapes(&shapes)?;
    assert_eq!(
      layout.factors,
      vec![Scalar::ONE, shapes[1].omega, shapes[0].omega]
    );
    assert_eq!(layout.matrices[1].groups[1], 1);
    assert_eq!(layout.matrices[2].groups[1], 2);
    shapes[0].widths[0] = 0;
    shapes[0].main_next = true;
    let layout = OpeningLayout::from_shapes(&shapes)?;
    assert_eq!(
      layout.factors,
      vec![Scalar::ONE, shapes[0].omega, shapes[1].omega]
    );
    assert_eq!(
      layout.matrices[0].value_offset,
      layout.matrices[1].value_offset
    );
    Ok(())
  }

  #[test]
  fn grouping_matches_runtime_points_for_all_row_flags() -> Result<()> {
    for equal in [false, true] {
      for flags in 0..16 {
        let mut shapes = shapes();
        if equal {
          shapes[1].height = shapes[0].height;
          shapes[1].omega = shapes[0].omega;
        }
        shapes[0].main_next = flags & 1 != 0;
        shapes[1].main_next = flags & 2 != 0;
        shapes[0].preprocessed_next = flags & 4 != 0;
        shapes[1].preprocessed_next = flags & 8 != 0;
        let layout = OpeningLayout::from_shapes(&shapes)?;
        for zeta in [Scalar::ONE, Scalar::from_u8(7), -Scalar::ONE] {
          let mut points = Vec::new();
          for (index, matrix) in layout.matrices.iter().enumerate() {
            for (row, &expected_group) in
              matrix.groups[..matrix.rows].iter().enumerate()
            {
              let point =
                if row == 0 { zeta } else { zeta * shapes[index % 2].omega };
              let group = match points.iter().position(|&value| value == point)
              {
                Some(group) => group,
                None => {
                  points.push(point);
                  points.len() - 1
                },
              };
              assert_eq!(expected_group, group);
            }
          }
          assert_eq!(
            points,
            layout
              .factors
              .iter()
              .map(|&factor| zeta * factor)
              .collect::<Vec<_>>()
          );
        }
      }
    }
    Ok(())
  }

  #[test]
  fn rejects_malformed_and_overflowing_shapes() {
    let valid = shapes();
    assert!(OpeningLayout::from_shapes(&valid[..1]).is_err());
    for height in [0, 1, 3, 1 << 29] {
      let mut bad = valid;
      bad[0].height = height;
      assert!(OpeningLayout::from_shapes(&bad).is_err());
    }
    for width in [1, 3] {
      let mut bad = valid;
      bad[0].widths[width] = 0;
      assert!(OpeningLayout::from_shapes(&bad).is_err());
    }
    for group in [0, 9] {
      let mut bad = valid;
      bad[0].lookup_group_size = group;
      assert!(OpeningLayout::from_shapes(&bad).is_err());
    }
    for omega in [Scalar::ZERO, Scalar::ONE, valid[1].omega] {
      let mut bad = valid;
      bad[0].omega = omega;
      assert!(OpeningLayout::from_shapes(&bad).is_err());
    }
    for width in [usize::MAX, usize::MAX / 16] {
      let mut bad = valid;
      bad[0].widths[0] = width;
      assert!(OpeningLayout::from_shapes(&bad).is_err());
    }
    assert!(quotient_width(usize::MAX).is_err());
    assert!(word_offset(usize::MAX).is_err());
    assert_eq!(quotient_width(0).unwrap(), 1);
    assert_eq!(quotient_width(3).unwrap(), 2);
  }
}
