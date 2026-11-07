//! Accelerators for the shared checked byte tables.
use crate::{
  bytecode::CheckedProgram, field::FieldBackend, maps::MapOverrides,
};

#[cfg(test)]
mod tests;

/// Optional host implementations for maps retained from `Aiur.Library.U8`.
/// Only present maps are registered, so this also works with tree-shaken
/// programs. The immutable Aiur tables still certify their byte domains and
/// answers. The fast row numbers require the library's input order; tables
/// with another domain or order retain the ordinary table implementation.
pub fn register_maps<B: FieldBackend>(
  program: &CheckedProgram<B>,
  overrides: &mut MapOverrides<B::Element>,
) -> Result<(), String> {
  let field = program.field();
  for map in &program.program().maps {
    macro_rules! bind {
      ($inputs:expr, $outputs:expr, $rows:expr, $body:expr) => {
        if standard_order(
          &program.program().tables[map.input].rows,
          $inputs,
          $rows,
        ) {
          overrides
            .insert_fixed::<$inputs, $outputs>(map.name.clone(), $body)?;
        }
      };
    }
    match map.name.as_str() {
      "UInt8::from_field" => bind!(1, 1, 256, move |input| {
        let row = unary::<256, _>(field, &input)?;
        Ok((row, input))
      }),
      "UInt8::raw_bit_decomposition" => bind!(1, 8, 256, move |input| {
        let row = unary::<256, _>(field, &input)?;
        Ok((
          row,
          std::array::from_fn(|i| field.from_u64(((row >> i) & 1) as u64)),
        ))
      }),
      "UInt8::range_pair" => {
        bind!(2, 0, 65536, move |input| { Ok((pair(field, &input)?.2, [])) })
      },
      "UInt8::raw_xor" => bind!(2, 1, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        Ok((row, [field.from_u64(a ^ b)]))
      }),
      "UInt8::raw_and" => bind!(2, 1, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        Ok((row, [field.from_u64(a & b)]))
      }),
      "UInt8::raw_or" => bind!(2, 1, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        Ok((row, [field.from_u64(a | b)]))
      }),
      "UInt8::raw_lt" => bind!(2, 1, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        Ok((row, [field.from_u64(u64::from(a < b))]))
      }),
      "UInt8::raw_add" => bind!(2, 2, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        let sum = a + b;
        Ok((row, [field.from_u64(sum & 255), field.from_u64(sum >> 8)]))
      }),
      "UInt8::raw_sub" => bind!(2, 2, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        Ok((
          row,
          [
            field.from_u64(a.wrapping_sub(b) & 255),
            field.from_u64(u64::from(a < b)),
          ],
        ))
      }),
      "UInt8::raw_mul" => bind!(2, 2, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        let product = a * b;
        Ok((row, [field.from_u64(product & 255), field.from_u64(product >> 8)]))
      }),
      "UInt8::raw_xor_split4" => bind!(2, 2, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        let xor = a ^ b;
        Ok((row, [field.from_u64(xor >> 4), field.from_u64((xor & 15) << 4)]))
      }),
      "UInt8::raw_xor_split7" => bind!(2, 2, 65536, move |input| {
        let (a, b, row) = pair(field, &input)?;
        let xor = a ^ b;
        Ok((row, [field.from_u64(xor >> 7), field.from_u64((xor & 127) << 1)]))
      }),
      "UInt8::raw_sum_byte" => bind!(1, 1, 768, move |input| {
        let row = unary::<768, _>(field, &input)?;
        Ok((row, [field.from_u64((row & 255) as u64)]))
      }),
      _ => (),
    }
  }
  Ok(())
}

fn standard_order(rows: &[Vec<u64>], width: usize, count: usize) -> bool {
  rows.len() == count
    && rows.iter().enumerate().all(|(i, row)| match width {
      1 => row.as_slice() == [i as u64],
      2 => row.as_slice() == [(i >> 8) as u64, (i & 255) as u64],
      _ => false,
    })
}

#[inline]
fn unary<const LIMIT: u64, B: FieldBackend>(
  field: B,
  input: &[B::Element],
) -> Result<usize, String> {
  let value = field.to_u64(input[0]);
  if value >= LIMIT {
    return Err("no table entry for map input".into());
  }
  Ok(value as usize)
}

#[inline]
fn pair<B: FieldBackend>(
  field: B,
  input: &[B::Element],
) -> Result<(u64, u64, usize), String> {
  let a = field.to_u64(input[0]);
  let b = field.to_u64(input[1]);
  if (a | b) > 255 {
    return Err("no table entry for map input".into());
  }
  Ok((a, b, ((a << 8) | b) as usize))
}
