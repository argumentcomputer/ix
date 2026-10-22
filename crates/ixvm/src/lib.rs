//! IxVM-specific host advice. The Aiur runtime knows no scalar operations or
//! field-specific hint algorithms; these are supplied by the embedding program.
use aiur::{
  bytecode::CheckedProgram,
  field::FieldBackend,
  hints::{HintChannels, HintEntry, PreparedHints},
  maps::MapOverrides,
};

mod io;

/// Prepare a production claim witness using immutable IO arenas.
pub fn prepare_streams<'a, B: FieldBackend>(
  program: &'a CheckedProgram<B>,
  streams: &aiur::library::io::Streams,
) -> Result<PreparedHints<'a, B>, String> {
  use aiur::bytecode::Type;
  let arenas = streams.prepare(program.field())?;
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, program.field())?;
  aiur::library::u64::register(&mut channels, program.field())?;
  arenas.register_read::<1>(io::READ_CHANNEL, true, &mut channels)?;
  let address = Type::Tuple { items: vec![Type::Field; 32] };
  let address_key = Type::Tuple { items: vec![Type::Field, address] };
  let mut data = arenas.metadata(
    "ixvm.io.info",
    address_key.clone(),
    None,
    |s| [1, 2, 4].contains(&s.channel),
    false,
  )?;
  data.extend(arenas.metadata(
    "ixvm.io.claim",
    Type::Tuple { items: vec![Type::Field; 8] },
    Some(0),
    |s| s.channel == 0,
    false,
  )?);
  data.extend(arenas.metadata(
    "ixvm.io.tag",
    address_key,
    None,
    |s| s.channel == 3,
    true,
  )?);
  let hints = program.prepare_hint_channels(&data, &channels)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(program, &mut maps)?;
  hints.with_map_overrides(&maps)
}

pub fn prepare<'a, B: FieldBackend>(
  program: &'a CheckedProgram<B>,
  entries: &[HintEntry],
) -> Result<PreparedHints<'a, B>, String> {
  let hints = if std::env::var_os("AIUR_IXVM_DATA_HINTS").is_some() {
    program.prepare_hints(entries)?
  } else {
    let mut channels = HintChannels::new();
    aiur::library::u32::register(&mut channels, program.field())?;
    aiur::library::u64::register(&mut channels, program.field())?;
    // Metadata remains keyed by address. Dense byte arenas are captured by
    // the bound read closure, shared by execution and witness replay.
    let vector_io = std::env::var_os("AIUR_IXVM_DATA_IO").is_none()
      && io::register(program.field(), entries, &mut channels)?;
    let data: Vec<_> = entries
      .iter()
      .filter(|e| {
        e.channel != "bytes_le" && !(vector_io && e.channel == io::READ_CHANNEL)
      })
      .cloned()
      .collect();
    program.prepare_hint_channels(&data, &channels)?
  };
  let mut maps = MapOverrides::new();
  // Benchmark ablation: keep row-count recording, but use original tables
  // for execution and population instead of native byte calculations.
  if std::env::var_os("AIUR_IXVM_TABLE_MAPS").is_none() {
    aiur::library::u8::register_maps(program, &mut maps)?;
  }
  hints.with_map_overrides(&maps)
}
