use super::*;
use crate::polynomial_storage::FFLONK_POLYNOMIAL_CHUNK_FIELDS;
use ark_ff::Zero;

#[test]
fn derived_sigma_reads_match_every_literal_domain_power_and_coset() {
  for n in [1usize, 2, 4, 8, 16, 32, 64, 256, 512, 1024, 2048, 1 << 17] {
    let domain = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let powers = SigmaEvaluationPowers::new(&domain).unwrap();
    assert_eq!(
      u64::try_from(powers.heap_bytes()).unwrap(),
      sigma_power_table_fields(n as u64).unwrap() * 32
    );
    let literal_powers = domain.elements().collect::<Vec<_>>();
    let cosets = [Fr::ONE, Fr::GENERATOR, Fr::GENERATOR.square()];
    for (column, coset) in cosets.into_iter().enumerate() {
      // Odd multiplication permutes every power; the offset/reversal make
      // reads nonsequential across low/high window boundaries.
      let targets = (0..n)
        .map(|index| PlonkCellV1 {
          row: ((73 * (n - 1 - index) + 17 * column) % n) as u64,
          column: u8::try_from(column).unwrap(),
        })
        .collect::<Vec<_>>();
      let source = powers.source(&targets);
      let expected = targets
        .iter()
        .map(|cell| coset * literal_powers[usize::try_from(cell.row).unwrap()])
        .collect::<Vec<_>>();
      let mut whole = vec![Fr::zero(); n];
      source.read_fields(0, &mut whole).unwrap();
      assert_eq!(whole, expected, "n={n}, coset={column}");
      assert_eq!(source.nonzero_len().unwrap(), n);
      for start in [
        0,
        1,
        powers.low.len().saturating_sub(1),
        powers.low.len(),
        FFLONK_POLYNOMIAL_CHUNK_FIELDS - 1,
        n.saturating_sub(7),
        n,
      ] {
        if start <= n {
          let len = (n - start).min(71);
          let mut values = vec![Fr::zero(); len];
          source.read_fields(start, &mut values).unwrap();
          assert_eq!(values, expected[start..start + len]);
        }
      }
    }
  }
}

#[test]
fn maximum_domain_power_windows_are_bounded_and_match_independent_powers() {
  // No size-n allocation: only the split power windows are constructed.
  for log_n in [29, 30, 31, Fr::TWO_ADICITY] {
    let n = 1usize << log_n;
    let domain = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let powers = SigmaEvaluationPowers::new(&domain).unwrap();
    assert_eq!(
      u64::try_from(powers.heap_bytes()).unwrap(),
      sigma_power_table_fields(n as u64).unwrap() * 32
    );
    assert!(powers.heap_bytes() <= 8 * 1024 * 1024);
    if log_n == 30 {
      assert_eq!(powers.heap_bytes(), 4 * 1024 * 1024);
    }
    let low = powers.low.len();
    let rows = [0, 1, low - 1, low, low + 1, n / 2, n - 2, n - 1]
      .into_iter()
      .chain((0..64usize).map(|index| {
        index.wrapping_mul(0x3841_9a51).wrapping_add(0x7158_2014) % n
      }));
    for row in rows {
      for (column, coset) in
        [Fr::ONE, Fr::GENERATOR, Fr::GENERATOR.square()].into_iter().enumerate()
      {
        let actual = powers.low[row % low] * powers.high[column][row / low];
        assert_eq!(actual, coset * domain.group_gen().pow([row as u64]));
      }
    }
  }
  assert_eq!(sigma_power_table_fields(0), None);
  assert_eq!(sigma_power_table_fields(3), None);
  assert_eq!(sigma_power_table_fields(u64::MAX), None);
}

#[test]
fn sigma_ranges_wrong_dimensions_and_invalid_targets_fail_before_output() {
  let domain = Radix2EvaluationDomain::<Fr>::new(8).unwrap();
  let powers = SigmaEvaluationPowers::new(&domain).unwrap();
  let targets = (0..8)
    .map(|row| PlonkCellV1 {
      row: 7 - row,
      column: u8::try_from(row % 3).unwrap(),
    })
    .collect::<Vec<_>>();
  let source = powers.source(&targets);
  assert_eq!(source.read_fields(8, &mut []), Ok(()));
  for (start, len) in [(8, 1), (9, 0), (usize::MAX, 0), (usize::MAX, 2), (7, 2)]
  {
    let mut output = vec![Fr::from(19u64); len];
    assert_eq!(
      source.read_fields(start, &mut output),
      Err(FflonkStorageError::Range)
    );
    assert_eq!(output, vec![Fr::from(19u64); len]);
  }
  for index in [0, 3, 7] {
    for bad in [
      PlonkCellV1 { row: 8, column: 0 },
      PlonkCellV1 { row: u64::MAX, column: 0 },
      PlonkCellV1 { row: 0, column: 3 },
      PlonkCellV1 { row: 0, column: u8::MAX },
    ] {
      let mut bad_targets = targets.clone();
      bad_targets[index] = bad;
      let mut output = [Fr::from(19u64); 8];
      assert_eq!(
        powers.source(&bad_targets).read_fields(0, &mut output),
        Err(FflonkStorageError::Range)
      );
      assert_eq!(output, [Fr::from(19u64); 8]);
    }
  }
  for bad_targets in [&targets[..7], &[]] {
    assert_eq!(
      powers.source(bad_targets).read_fields(0, &mut []),
      Err(FflonkStorageError::Range)
    );
  }
}
