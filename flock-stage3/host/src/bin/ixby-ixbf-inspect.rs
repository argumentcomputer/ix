//! Read-only diagnostic intake. This command cannot generate or admit proofs.
use anyhow::{Context, Result, ensure};
use ixby_flock::ixby::ixbf::{self, DecodeLimits, ValueForest, ValueKind};
use std::{fs::File, io::Read, path::Path};

fn read(path: &Path, limit: usize) -> Result<Vec<u8>> {
  let mut bytes = Vec::new();
  File::open(path)
    .with_context(|| format!("opening {}", path.display()))?
    .take(u64::try_from(limit)?.checked_add(1).context("file limit overflow")?)
    .read_to_end(&mut bytes)?;
  ensure!(bytes.len() <= limit, "input exceeds host file byte limit");
  Ok(bytes)
}

fn forest(label: &str, bytes: &[u8], values: &ValueForest<'_>) {
  let maximum_array = values
    .nodes()
    .iter()
    .filter_map(|node| match &node.kind {
      ValueKind::Scalar(ixbf::Scalar::Bytes(bytes)) => Some(bytes.len()),
      _ => None,
    })
    .max()
    .unwrap_or(0);
  println!(
    "  \"{label}\": {{\"bytes\": {}, \"raw_blake3\": \"{}\", \"values\": {}, \"nodes\": {}, \"depth\": {}, \"maximum_byte_array\": {maximum_array}}},",
    bytes.len(),
    blake3::hash(bytes).to_hex(),
    values.roots().len(),
    values.nodes().len(),
    values.depth()
  );
}

fn main() -> Result<()> {
  let paths: Vec<_> = std::env::args_os().skip(1).collect();
  ensure!(
    (1..=3).contains(&paths.len()),
    "usage: ixby-ixbf-inspect <program.ixby> [input.ixbi [output.ixbo]]"
  );
  let loader = DecodeLimits::default();
  let program_bytes = read(Path::new(&paths[0]), loader.bytes)?;
  let artifact = ixbf::decode_program(&program_bytes, loader)?;
  let input_bytes =
    paths.get(1).map(|p| read(Path::new(p), loader.bytes)).transpose()?;
  let output_bytes =
    paths.get(2).map(|p| read(Path::new(p), loader.bytes)).transpose()?;
  // Complete every requested validation before printing any result.
  let input = input_bytes
    .as_deref()
    .map(|bytes| ixbf::decode_input(&artifact, bytes, loader))
    .transpose()?;
  let output = output_bytes
    .as_deref()
    .map(|bytes| ixbf::decode_output(&artifact, bytes, loader))
    .transpose()?;
  let inventory = artifact.inventory();
  println!("{{");
  println!("  \"format\": \"ixby-functional-intake/1\",");
  println!("  \"canonical_host_intake\": true,");
  println!("  \"proving_admitted\": false,");
  println!("  \"constraint_refinement_certified\": false,");
  println!("  \"source_certified\": false,");
  println!(
    "  \"program\": {{\"bytes\": {}, \"raw_blake3\": \"{}\", \"wire_format\": 1, \"semantics\": 0}},",
    inventory.program_bytes,
    blake3::hash(&program_bytes).to_hex()
  );
  println!("  \"entry\": {},", artifact.entry());
  println!("  \"max_steps_decimal\": \"{}\",", artifact.max_steps());
  println!(
    "  \"max_steps_exceeds_u32\": {},",
    artifact.max_steps().bits() > 32
  );
  println!("  \"max_steps_fits_u64\": {},", artifact.max_steps().bits() <= 64);
  let limits = artifact.limits();
  let limits = [
    ("functions", &limits.functions),
    ("constructors", &limits.constructors),
    ("blocks", &limits.blocks),
    ("locals", &limits.locals),
    ("operands", &limits.operands),
    ("continuations", &limits.continuations),
    ("input_nodes", &limits.input_nodes),
    ("nat_bits", &limits.nat_bits),
    ("string_bytes", &limits.string_bytes),
    ("byte_array_bytes", &limits.byte_array_bytes),
  ];
  println!("  \"reference_limits_decimal\": {{");
  for (index, (name, value)) in limits.iter().enumerate() {
    println!(
      "    \"{name}\": \"{value}\"{}",
      if index + 1 == limits.len() { "" } else { "," }
    );
  }
  println!("  }},");
  println!("  \"functions\": {},", inventory.functions);
  println!("  \"blocks\": {},", inventory.blocks);
  println!("  \"constructors\": {},", inventory.constructors);
  println!(
    "  \"maximum_function_blocks\": {},",
    inventory.maximum_function_blocks
  );
  println!(
    "  \"maximum_function_arity_decimal\": \"{}\",",
    inventory.maximum_function_arity
  );
  println!(
    "  \"maximum_frame_locals_decimal\": \"{}\",",
    inventory.maximum_frame_locals
  );
  println!(
    "  \"maximum_constructor_fields_decimal\": \"{}\",",
    inventory.maximum_constructor_fields
  );
  println!(
    "  \"maximum_operand_vector\": {},",
    inventory.maximum_operand_vector
  );
  println!("  \"instruction_sites\": {:?},", inventory.instructions);
  println!("  \"operation_sites\": {:?},", inventory.operations);
  println!("  \"primitive_kinds\": {},", inventory.primitives.len());
  println!("  \"primitives\": [");
  for (index, primitive) in inventory.primitives.iter().enumerate() {
    let native = primitive
      .native_opcode
      .map_or_else(|| "null".to_owned(), |value| value.to_string());
    println!(
      "    {{\"name\": \"{:?}\", \"functional_opcode\": {}, \"native_opcode_name_only\": {native}, \"sites\": {}}}{}",
      primitive.primitive,
      primitive.primitive.opcode(),
      primitive.sites,
      if index + 1 == inventory.primitives.len() { "" } else { "," }
    );
  }
  println!("  ],");
  println!("  \"scalar_literals\": [");
  for (index, scalar) in inventory.scalars.iter().enumerate() {
    println!(
      "    {{\"kind\": \"{}\", \"count\": {}, \"maximum_bytes\": {}, \"maximum_bits\": {}}}{}",
      scalar.kind,
      scalar.literals,
      scalar.maximum_bytes,
      scalar.maximum_bits,
      if index + 1 == inventory.scalars.len() { "" } else { "," }
    );
  }
  println!("  ],");
  if let Some(input) = &input {
    forest("input", input.source(), input.values());
  }
  if let Some(output) = &output {
    forest("output", output.source(), output.values());
  }
  println!(
    "  \"scope\": \"host admission and static census only; no execution, trace, circuit admission, or proof\""
  );
  println!("}}");
  Ok(())
}
