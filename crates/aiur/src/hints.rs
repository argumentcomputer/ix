//! Host advice has a static channel and constant input/output types. Preparation
//! resolves channel names once; execution calls the bound closure at each site.
use crate::bytecode::{CheckedProgram, Instruction, Layout, Program, Type};
use crate::field::{FieldBackend, PrimeField};
use crate::host::{self, HintBinder, RegisterHint};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HintEntry {
  #[serde(default)]
  pub channel: String,
  pub r#type: Type,
  pub key_type: Type,
  pub key: Vec<u64>,
  pub output: Vec<u64>,
}

/// Flat encodings of constants, with their nominal types fixed at registration.
/// The output buffer has the declared width and starts zeroed. The runtime
/// validates every returned word, enum tag and padding slot before consuming it.
/// Closures may capture configuration; no addresses or VM internals are exposed.
/// Providers must return the same answer for the same key throughout execution
/// and trace generation, independently of call order and concurrent invocations.
/// Trace generation calls the provider again instead of retaining its answers.
/// Rust's `Fn + Send + Sync` bounds do not enforce this repeatability contract.
pub type HintFunction<F = u64> =
  dyn Fn(&[F], &mut [F]) -> Result<(), String> + Send + Sync;

struct Channel<F> {
  key_type: Type,
  output_type: Type,
  function: Arc<HintFunction<F>>,
  fixed: Option<(usize, usize, Arc<HintBinder<F>>)>,
}

/// Host-defined code providers. Names are resolved only by `prepare_hint_channels`.
/// Data-only channels remain available through `HintEntry`.
pub struct HintChannels<F = u64> {
  channels: HashMap<String, Channel<F>>,
}
impl<F> Default for HintChannels<F> {
  fn default() -> Self {
    Self { channels: HashMap::new() }
  }
}
impl<F> HintChannels<F> {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn insert(
    &mut self,
    name: impl Into<String>,
    key_type: Type,
    output_type: Type,
    function: impl Fn(&[F], &mut [F]) -> Result<(), String> + Send + Sync + 'static,
  ) -> Result<(), String> {
    let name = name.into();
    if self.channels.contains_key(&name) {
      return Err(format!("duplicate hint channel {name:?}"));
    }
    self.channels.insert(
      name,
      Channel {
        key_type,
        output_type,
        function: Arc::new(function),
        fixed: None,
      },
    );
    Ok(())
  }

  /// Fixed-width counterpart of `insert`. The complete register handler is
  /// specialized around this concrete closure before its type is erased.
  /// The nominal types are still checked, and output canonicality/tag checks
  /// are retained. All outputs must be returned, rather than partially filled.
  pub fn insert_fixed<const INPUTS: usize, const OUTPUTS: usize>(
    &mut self,
    name: impl Into<String>,
    key_type: Type,
    output_type: Type,
    function: impl Fn([F; INPUTS]) -> Result<[F; OUTPUTS], String>
    + Send
    + Sync
    + 'static,
  ) -> Result<(), String>
  where
    F: Copy + Send + Sync + 'static,
  {
    let name = name.into();
    if self.channels.contains_key(&name) {
      return Err(format!("duplicate hint channel {name:?}"));
    }
    let function = Arc::new(function);
    let binder = host::hint_binder(function.clone());
    self.channels.insert(
      name,
      Channel {
        key_type,
        output_type,
        function: Arc::new(move |key, output| {
          let input =
            key.try_into().map_err(|_| "hint input width mismatch")?;
          output.copy_from_slice(&function(input)?);
          Ok(())
        }),
        fixed: Some((INPUTS, OUTPUTS, binder)),
      },
    );
    Ok(())
  }
}

pub(crate) struct HintSite<F = u64> {
  pub(crate) function: Arc<HintFunction<F>>,
  // Data answers have already passed validation; code answers have not.
  pub(crate) output_layout: Option<Layout>,
  pub(crate) registers: Option<Arc<RegisterHint<F>>>,
}

impl<F: Copy> HintSite<F> {
  #[inline]
  pub(crate) fn evaluate<B: FieldBackend<Element = F>>(
    &self,
    key: &[F],
    output: &mut [F],
    field: B,
  ) -> Result<(), String> {
    output.fill(field.zero());
    (self.function)(key, output)?;
    if let Some(layout) = &self.output_layout {
      layout.validate(output, field)?;
    }
    Ok(())
  }
}

/// Shared once per prepared session, including the immutable data captured by
/// data-backed providers. Records keep this alive for later or parallel replay.
pub(crate) struct BoundHints<F> {
  pub(crate) program: Arc<Program>,
  pub(crate) sites: Vec<Vec<Option<HintSite<F>>>>,
}

impl<F> std::fmt::Debug for BoundHints<F> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("BoundHints")
      .field("functions", &self.sites.len())
      .finish_non_exhaustive()
  }
}

/// Providers bound to bytecode sites. Reusing this object does not reuse query
/// caches or ROM pointers. It owns the closures and their captured environment.
pub struct PreparedHints<'a, B: FieldBackend = PrimeField> {
  pub(crate) program: &'a CheckedProgram<B>,
  pub(crate) bindings: Arc<BoundHints<B::Element>>,
  pub(crate) maps: Vec<Arc<crate::maps::PreparedMap<B>>>,
  pub(crate) dispatch: Vec<Vec<crate::execute::dispatch::Dispatch<B::Element>>>,
}

impl<B: FieldBackend> PreparedHints<'_, B> {
  /// Bind optional static-map implementations once. The resulting execution
  /// records retain these same closures for witness population. No source
  /// syntax, function implementation, or certifying table is replaced.
  pub fn with_map_overrides(
    mut self,
    overrides: &crate::maps::MapOverrides<B::Element>,
  ) -> Result<Self, String> {
    self.maps = overrides.bind(self.program)?;
    let maps = overrides.bind_registers(self.program);
    self.dispatch = crate::execute::dispatch::prepare(
      self.program,
      &self.bindings.sites,
      Some(&maps),
    );
    Ok(self)
  }
}

type DataIndex<F> =
  HashMap<(String, Type), Arc<HashMap<Vec<F>, (Type, Vec<F>)>>>;

impl<B: FieldBackend> CheckedProgram<B> {
  pub fn prepare_hints(
    &self,
    entries: &[HintEntry],
  ) -> Result<PreparedHints<'_, B>, String> {
    self.prepare_hint_channels(entries, &HintChannels::new())
  }

  /// Code providers override data for their channel. All supplied data is
  /// still checked, including unused rows. Unbound channels fail only when
  /// executed, so an inactive hint requires no provider.
  pub fn prepare_hint_channels(
    &self,
    entries: &[HintEntry],
    channels: &HintChannels<B::Element>,
  ) -> Result<PreparedHints<'_, B>, String> {
    let data = prepare_data(self, entries)?;
    // Validate registrations even when there are no sites for them.
    for (name, channel) in &channels.channels {
      let key = channel.key_type.layout(&self.program.enums, &mut vec![])?;
      let output =
        channel.output_type.layout(&self.program.enums, &mut vec![])?;
      if !key.pointer_free() || !output.pointer_free() {
        return Err(format!("hint channel {name:?} cannot contain pointers"));
      }
      if let Some((inputs, outputs, _)) = &channel.fixed
        && (key.width() != *inputs || output.width() != *outputs)
      {
        return Err(format!("hint channel {name:?} fixed arity mismatch"));
      }
    }
    let sites = self
      .program
      .functions
      .iter()
      .enumerate()
      .map(|(function_id, function)| {
        function
          .code
          .iter()
          .enumerate()
          .map(|(pc, op)| {
            let Instruction::Hint { channel, key_type, r#type, .. } = op else {
              return Ok(None);
            };
            let site = if let Some(provider) = channels.channels.get(channel) {
              if &provider.key_type != key_type
                || &provider.output_type != r#type
              {
                return Err(format!(
                  "hint channel {channel:?} signature mismatch"
                ));
              }
              let layout = r#type.layout(&self.program.enums, &mut vec![])?;
              let registers =
                provider.fixed.as_ref().and_then(|(_, _, binder)| {
                  let Instruction::Hint { key, dest, .. } =
                    &self.execution_functions[function_id].code[pc]
                  else {
                    return None;
                  };
                  binder(key, dest, host::output_check(&layout, self.field))
                });
              HintSite {
                function: provider.function.clone(),
                output_layout: Some(layout),
                registers,
              }
            } else if let Some(rows) =
              data.get(&(channel.clone(), key_type.clone()))
            {
              let rows = rows.clone();
              let expected = r#type.clone();
              HintSite {
                function: Arc::new(move |key, output| {
                  let (actual, answer) =
                    rows.get(key).ok_or("missing hint data")?;
                  if actual != &expected {
                    return Err("hint output type mismatch".into());
                  }
                  output.copy_from_slice(answer);
                  Ok(())
                }),
                output_layout: None,
                registers: None,
              }
            } else {
              HintSite {
                function: Arc::new(|_, _| Err("missing hint provider".into())),
                output_layout: None,
                registers: None,
              }
            };
            Ok(Some(site))
          })
          .collect::<Result<Vec<_>, String>>()
      })
      .collect::<Result<Vec<_>, String>>()?;
    let dispatch = crate::execute::dispatch::prepare(self, &sites, None);
    Ok(PreparedHints {
      program: self,
      bindings: Arc::new(BoundHints { program: self.program.clone(), sites }),
      maps: crate::maps::MapOverrides::new().bind(self)?,
      dispatch,
    })
  }
}

fn prepare_data<B: FieldBackend>(
  program: &CheckedProgram<B>,
  entries: &[HintEntry],
) -> Result<DataIndex<B::Element>, String> {
  let mut layouts = HashMap::new();
  let mut index: DataIndex<B::Element> = HashMap::new();
  for (row, entry) in entries.iter().enumerate() {
    let check = |ty: &Type, words: &[u64], layouts: &mut HashMap<_, _>| {
      if !layouts.contains_key(ty) {
        let layout = ty.layout(&program.program.enums, &mut vec![])?;
        if !layout.pointer_free() {
          return Err("supplied hint data cannot contain pointers".to_owned());
        }
        layouts.insert(ty.clone(), layout);
      }
      let words = program.field.decode(words)?;
      layouts[ty].validate(&words, program.field)?;
      Ok::<_, String>(words)
    };
    let key = check(&entry.key_type, &entry.key, &mut layouts)
      .map_err(|e| format!("hint entry {row} key: {e}"))?;
    let output = check(&entry.r#type, &entry.output, &mut layouts)
      .map_err(|e| format!("hint entry {row} output: {e}"))?;
    let rows =
      index.entry((entry.channel.clone(), entry.key_type.clone())).or_default();
    let rows = Arc::get_mut(rows).unwrap();
    match rows.entry(key) {
      std::collections::hash_map::Entry::Vacant(slot) => {
        slot.insert((entry.r#type.clone(), output));
      },
      std::collections::hash_map::Entry::Occupied(slot) => {
        let (ty, existing) = slot.get();
        if ty != &entry.r#type || existing != &output {
          return Err(format!("conflicting hint entries at row {row}"));
        }
      },
    }
  }
  Ok(index)
}
