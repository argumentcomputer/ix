//! Optional host implementations of static maps. Bindings affect candidate
//! execution/witness generation only; the original tables certify every result.
use crate::bytecode::{CheckedProgram, Instruction, Layout, Program};
use crate::field::{FieldBackend, PrimeField};
use crate::host::{self, MapBinder, MapCalls};
use crate::table::TableIndex;
use std::{collections::HashMap, fmt, sync::Arc};

/// Flat inputs and a zeroed, fixed-width output buffer. Returns the row index
/// in the map's original tables. Providers must reject inputs outside their
/// domain, be deterministic, and may capture configuration. They never define
/// table data. Inputs and outputs use the executor's field elements directly.
pub type MapFunction<F = u64> =
  dyn Fn(&[F], &mut [F]) -> Result<usize, String> + Send + Sync;

struct Override<F> {
  inputs: usize,
  outputs: usize,
  function: Arc<MapFunction<F>>,
  bind_registers: Option<Arc<MapBinder<F>>>,
}

/// Names, flat arities, and row numbering are checked once when preparing an
/// executor. Maps without an override use their immutable input/output tables.
pub struct MapOverrides<F = u64> {
  entries: HashMap<String, Override<F>>,
}

impl<F> Default for MapOverrides<F> {
  fn default() -> Self {
    Self { entries: HashMap::new() }
  }
}
impl<F> MapOverrides<F> {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn insert(
    &mut self,
    name: impl Into<String>,
    inputs: usize,
    outputs: usize,
    function: impl Fn(&[F], &mut [F]) -> Result<usize, String>
    + Send
    + Sync
    + 'static,
  ) -> Result<(), String> {
    let name = name.into();
    if self.entries.contains_key(&name) {
      return Err(format!("duplicate map override {name:?}"));
    }
    self.entries.insert(
      name,
      Override {
        inputs,
        outputs,
        function: Arc::new(function),
        bind_registers: None,
      },
    );
    Ok(())
  }

  /// Register a fixed-arity provider returning every output by value. The
  /// executor specializes a complete register/counter handler around C,
  /// retaining one indirect call per invocation. Trace replay uses the same C.
  /// This has the same domain, row-index and determinism contract as `insert`.
  pub fn insert_fixed<const INPUTS: usize, const OUTPUTS: usize>(
    &mut self,
    name: impl Into<String>,
    function: impl Fn([F; INPUTS]) -> Result<(usize, [F; OUTPUTS]), String>
    + Send
    + Sync
    + 'static,
  ) -> Result<(), String>
  where
    F: Copy + Send + Sync + 'static,
  {
    let name = name.into();
    if self.entries.contains_key(&name) {
      return Err(format!("duplicate map override {name:?}"));
    }
    let function = Arc::new(function);
    let bind_registers = host::map_binder(function.clone());
    self.entries.insert(
      name,
      Override {
        inputs: INPUTS,
        outputs: OUTPUTS,
        function: Arc::new(move |args, output| {
          let input =
            args.try_into().map_err(|_| "map input width mismatch")?;
          let (row, answer) = function(input)?;
          output.copy_from_slice(&answer);
          Ok(row)
        }),
        bind_registers: Some(bind_registers),
      },
    );
    Ok(())
  }

  pub(crate) fn bind_registers<B: FieldBackend<Element = F>>(
    &self,
    checked: &CheckedProgram<B>,
  ) -> Vec<MapCalls<F>> {
    checked
      .execution_functions
      .iter()
      .map(|f| {
        f.code
          .iter()
          .map(|instruction| {
            let Instruction::Call { function, args, dest } = instruction else {
              return None;
            };
            let id = function.checked_sub(checked.program.functions.len())?;
            let map = checked.program.maps.get(id)?;
            let binder =
              self.entries.get(&map.name)?.bind_registers.as_ref()?;
            binder(
              args,
              dest,
              host::output_check(&checked.outputs[*function], checked.field),
            )
          })
          .collect()
      })
      .collect()
  }

  pub(crate) fn bind<B: FieldBackend<Element = F>>(
    &self,
    checked: &CheckedProgram<B>,
  ) -> Result<Vec<Arc<PreparedMap<B>>>, String>
  where
    F: Copy,
  {
    for name in self.entries.keys() {
      if !checked.program.maps.iter().any(|map| &map.name == name) {
        return Err(format!("unknown map override {name:?}"));
      }
    }
    checked
            .program
            .maps
            .iter()
            .enumerate()
            .map(|(i, map)| {
                let callable = checked.program.functions.len() + i;
                let provider = self.entries.get(&map.name);
                if provider.is_some_and(|p| {
                    p.inputs != checked.inputs[callable].width()
                        || p.outputs != checked.outputs[callable].width()
                }) {
                    return Err(format!("map override {:?} signature mismatch", map.name));
                }
                if let Some(provider) = provider {
                    // Verify the numbering once, outside execution/population.
                    // Answers remain untrusted witnesses certified by the tables.
                    let mut output = vec![checked.field.zero(); provider.outputs];
                    for (row, args) in checked.tables[map.input].iter().enumerate() {
                        output.fill(checked.field.zero());
                        let actual = (provider.function)(args, &mut output).map_err(|e| {
                            format!("map override {:?} at row {row}: {e}", map.name)
                        })?;
                        if actual != row {
                            return Err(format!(
                                "map override {:?} row index mismatch: expected {row}, got {actual}",
                                map.name
                            ));
                        }
                    }
                }
                Ok(Arc::new(PreparedMap {
                    program: checked.program.clone(),
                    tables: checked.tables.clone(),
                    id: i,
                    input_width: checked.inputs[callable].width(),
                    input: map.input,
                    output: map.output,
                    index: checked.map_indexes[map.input].as_ref().unwrap().clone(),
                    output_layout: checked.outputs[callable].clone(),
                    field: checked.field,
                    function: provider.map(|p| p.function.clone()),
                }))
            })
            .collect()
  }
}

pub(crate) struct PreparedMap<B: FieldBackend = PrimeField> {
  pub(crate) program: Arc<Program>,
  tables: Arc<Vec<Vec<Vec<B::Element>>>>,
  pub(crate) id: usize,
  input_width: usize,
  input: usize,
  output: usize,
  index: Arc<TableIndex<B>>,
  output_layout: Layout,
  field: B,
  function: Option<Arc<MapFunction<B::Element>>>,
}

impl<B: FieldBackend> fmt::Debug for PreparedMap<B> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("PreparedMap")
      .field("input", &self.input)
      .field("output", &self.output)
      .field("overridden", &self.function.is_some())
      .finish()
  }
}

impl<B: FieldBackend> PreparedMap<B> {
  pub(crate) fn rows(&self) -> usize {
    self.tables[self.input].len()
  }
  pub(crate) fn input(&self, row: usize) -> &[B::Element] {
    &self.tables[self.input][row]
  }
  pub(crate) fn output(&self, row: usize) -> &[B::Element] {
    &self.tables[self.output][row]
  }
  pub(crate) fn row(&self, args: &[B::Element]) -> Result<usize, String> {
    self.index.get(args).ok_or_else(|| "no table entry for map input".into())
  }
  pub(crate) fn evaluate(
    &self,
    args: &[B::Element],
    output: &mut [B::Element],
  ) -> Result<usize, String> {
    if args.len() != self.input_width
      || output.len() != self.output_layout.width()
    {
      return Err("map argument/output width mismatch".into());
    }
    if let Some(function) = &self.function {
      output.fill(self.field.zero());
      let row = function(args, output)?;
      // Representation checks are not table membership checks. In
      // particular, a canonical field word need not be a valid byte.
      self.output_layout.validate(output, self.field)?;
      Ok(row)
    } else {
      let row = self.row(args)?;
      output.copy_from_slice(self.output(row));
      Ok(row)
    }
  }
}

/// Fixed-size multiplicities are the only per-execution table state. Inputs,
/// outputs, indexes, and closures are shared with the prepared executor.
#[derive(Clone, Debug)]
pub(crate) struct MapRecord<B: FieldBackend = PrimeField> {
  pub(crate) binding: Arc<PreparedMap<B>>,
  pub(crate) counts: Box<[u64]>,
}

impl<B: FieldBackend> MapRecord<B> {
  pub(crate) fn new(binding: Arc<PreparedMap<B>>) -> Self {
    Self { counts: vec![0; binding.rows()].into_boxed_slice(), binding }
  }
  pub(crate) fn call(
    &mut self,
    args: &[B::Element],
    output: &mut [B::Element],
  ) -> Result<(), String> {
    let row = self.binding.evaluate(args, output)?;
    host::bump(&mut self.counts, row)
  }
}
