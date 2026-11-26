//! Advice for programs lowered from IxCC's first-order IR (Lean package
//! `IxCCAiur`, `IxCCAiur/IxCCAiur/Lower.lean` and `GuessLower.lean`):
//!
//! 1. `ixcc.divmod`: quotient and remainder `(x / y, x % y)`. The lowered
//!    program range-checks both words and asserts `q * y + r = x` and `r < y`.
//! 2. `ixcc.guess.<fn>`: universal Tier-2 `guess` host advice channel. Given
//!    the unmodified pre-guess advice package (`--advice ADVICE.ixa`),
//!    [`register_advice_program`] automatically scans every `"ixcc.guess.*"`
//!    hint site in the circuit program and binds each channel to the matching
//!    `Prog::<fn>` (or `Prog::<fn>_advice`) entrypoint in the advice program,
//!    with zero per-function hardcoding. Every answer is memoized per key so
//!    execution and witness-generation replay are identical and fast; the
//!    circuit itself enforces U4 bounds and runs the verified checker `c`.
use crate::{
  bytecode::{CheckedProgram, Instruction, Type},
  field::FieldBackend,
  hints::HintChannels,
};
use std::{
  collections::{BTreeMap, HashMap},
  sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
  },
};

pub const DIVMOD: &str = "ixcc.divmod";

/// Channel prefix for Tier-2 `guess` advice (`IxCCAiur.GuessLower`).
pub const GUESS_PREFIX: &str = "ixcc.guess.";

/// `(x, y) -> (x / y, x % y)` on canonical values that fit in a `u64`, with
/// Lean's conventions at `y = 0` (quotient `0`, remainder `x`), as the Lean
/// provider answers (`IxCC.AiurBackend.Hints.dispatcher`).
pub fn register<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  field: B,
) -> Result<(), String> {
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  channels.insert_fixed::<2, 2>(DIVMOD, pair.clone(), pair, move |input| {
    let x = field.try_to_u64(input[0])?;
    let y = field.try_to_u64(input[1])?;
    let q = x.checked_div(y).unwrap_or(0);
    let r = x.checked_rem(y).unwrap_or(x);
    Ok([field.from_u64(q), field.from_u64(r)])
  })
}

/// Scan `main_program` for all distinct `"ixcc.guess.*"` hint channels and
/// verify that repeated sites for the same channel agree on `(key_type, r#type)`.
pub fn collect_guess_channels<B: FieldBackend>(
  main_program: &CheckedProgram<B>,
) -> Result<BTreeMap<String, (Type, Type)>, String> {
  let mut found: BTreeMap<String, (Type, Type)> = BTreeMap::new();
  for function in &main_program.program().functions {
    for op in &function.code {
      let Instruction::Hint { channel, key_type, r#type, .. } = op else {
        continue;
      };
      if !channel.starts_with(GUESS_PREFIX) {
        continue;
      }
      if let Some((prev_key, prev_out)) = found.get(channel) {
        if prev_key != key_type || prev_out != r#type {
          return Err(format!(
            "inconsistent hint signature for channel {channel:?}"
          ));
        }
      } else {
        found.insert(channel.clone(), (key_type.clone(), r#type.clone()));
      }
    }
  }
  Ok(found)
}

fn register_advice_program_inner<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  main_program: &CheckedProgram<B>,
  advice_program: CheckedProgram<B>,
  tamper_channel: Option<&str>,
) -> Result<(Vec<String>, Arc<AtomicUsize>), String> {
  let field = main_program.field();
  if advice_program.field().modulus() != field.modulus() {
    return Err("advice program field modulus mismatch".into());
  }
  let guess_channels = collect_guess_channels(main_program)?;
  let tamper_hits = Arc::new(AtomicUsize::new(0));
  if let Some(target) = tamper_channel
    && !guess_channels.contains_key(target)
  {
    return Err(format!(
      "cannot tamper channel {target:?}: not referenced by circuit program"
    ));
  }
  if guess_channels.is_empty() {
    return Ok((Vec::new(), tamper_hits));
  }

  let mut base_channels = HintChannels::new();
  crate::library::u32::register(&mut base_channels, field)?;
  crate::library::u64::register(&mut base_channels, field)?;
  register(&mut base_channels, field)?;
  // Validate the advice program's own hint bindings upfront.
  advice_program.prepare_hint_channels(&[], &base_channels)?;

  let advice_program = Arc::new(advice_program);
  let base_channels = Arc::new(base_channels);
  let mut registered = Vec::with_capacity(guess_channels.len());

  for (channel, (key_type, output_type)) in guess_channels {
    let fn_name = channel
      .strip_prefix(GUESS_PREFIX)
      .ok_or_else(|| format!("invalid guess channel {channel:?}"))?;
    let adapter = format!("Prog::{fn_name}_advice");
    let direct = format!("Prog::{fn_name}");
    let entry_name = if advice_program.entry(&adapter).is_ok() {
      adapter
    } else if advice_program.entry(&direct).is_ok() {
      direct
    } else {
      return Err(format!(
        "advice program missing entrypoint for guess channel {channel:?} \
         (expected {direct:?} or {adapter:?})"
      ));
    };

    let advice = Arc::clone(&advice_program);
    let advice_channels = Arc::clone(&base_channels);
    let cache: Arc<Mutex<HashMap<Vec<B::Element>, Vec<B::Element>>>> =
      Arc::new(Mutex::new(HashMap::new()));
    let should_tamper = tamper_channel == Some(channel.as_str());
    let hits = Arc::clone(&tamper_hits);
    let channel_label = channel.clone();

    channels.insert(
      channel.clone(),
      key_type,
      output_type,
      move |key, output| {
        if should_tamper {
          hits.fetch_add(1, Ordering::Relaxed);
        }
        if let Some(cached) = {
          let guard = cache.lock().map_err(|e| {
            format!("advice cache poisoned on {channel_label}: {e}")
          })?;
          guard.get(key).cloned()
        } {
          if cached.len() != output.len() {
            return Err(format!(
              "advice width mismatch on {channel_label}: got {}, expected {}",
              cached.len(),
              output.len()
            ));
          }
          output.copy_from_slice(&cached);
          return Ok(());
        }

        let prepared =
          advice.prepare_hint_channels(&[], &advice_channels)?;
        let record = prepared
          .execute(&entry_name, key.to_vec())
          .map_err(|e| e.to_string())?;
        let mut answer = record.output;
        if answer.len() != output.len() {
          return Err(format!(
            "advice entrypoint {entry_name:?} returned {} words, expected {}",
            answer.len(),
            output.len()
          ));
        }
        if should_tamper
          && let Some(word) = answer.last_mut()
        {
          // Perturb the last payload word (+1 mod p) so enum tags remain valid
          // while the mathematical witness fails the circuit's verified checker.
          *word = field.add(*word, field.one());
        }
        {
          let mut guard = cache.lock().map_err(|e| {
            format!("advice cache poisoned on {channel_label}: {e}")
          })?;
          guard.insert(key.to_vec(), answer.clone());
        }
        output.copy_from_slice(&answer);
        Ok(())
      },
    )?;
    registered.push(channel);
  }

  Ok((registered, tamper_hits))
}

/// Automatically discover every `"ixcc.guess.<fn>"` hint channel in
/// `main_program` and bind it to the matching `Prog::<fn>` (or
/// `Prog::<fn>_advice`) entrypoint in the unmodified pre-guess
/// `advice_program`. Returns the sorted list of registered channel names.
pub fn register_advice_program<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  main_program: &CheckedProgram<B>,
  advice_program: CheckedProgram<B>,
) -> Result<Vec<String>, String> {
  register_advice_program_inner(channels, main_program, advice_program, None)
    .map(|(registered, _)| registered)
}

/// Like [`register_advice_program`], but deterministically corrupts the
/// returned witness for `tamper_channel` (`+1 mod p` on the last word) for
/// negative-control testing that the circuit rejects wrong advice.
/// Returns `(registered_channels, tampered_call_counter)`.
pub fn register_tampered_advice_program<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  main_program: &CheckedProgram<B>,
  advice_program: CheckedProgram<B>,
  tamper_channel: &str,
) -> Result<(Vec<String>, Arc<AtomicUsize>), String> {
  register_advice_program_inner(
    channels,
    main_program,
    advice_program,
    Some(tamper_channel),
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    bytecode::{Binary, Entry, Function, Program, VERSION},
    field::PrimeField,
    value::IoType,
  };

  const GOLDILOCKS: u64 = 0xffff_ffff_0000_0001;

  fn sample_guess_and_advice() -> (CheckedProgram<PrimeField>, CheckedProgram<PrimeField>) {
    // Main circuit: hints y = x + 7 on "ixcc.guess.f1", checks y == x + 7, returns y.
    let main_prog = Program {
      version: VERSION,
      modulus: GOLDILOCKS,
      functions: vec![Function {
        name: "Prog::main0".into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers: 4,
        code: vec![
          Instruction::Hint {
            channel: "ixcc.guess.f1".into(),
            r#type: Type::Field,
            key_type: Type::Field,
            key: vec![0],
            dest: vec![1],
          },
          Instruction::Literal { dest: 2, value: 7 },
          Instruction::Binary {
            dest: 3,
            operator: Binary::Add,
            left: 0,
            right: 2,
          },
          Instruction::AssertEq {
            left: vec![1],
            right: vec![3],
            message: Some("guess checker mismatch".into()),
            runtime_check: true,
          },
          Instruction::Ret { value: vec![1] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Prog::main0".into(),
        function: 0,
        inputs: vec![IoType::Field],
        output: Some(IoType::Field),
      }],
    };
    // Advice program: computes f1(x) = x + 7.
    let advice_prog = Program {
      version: VERSION,
      modulus: GOLDILOCKS,
      functions: vec![Function {
        name: "Prog::f1".into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers: 3,
        code: vec![
          Instruction::Literal { dest: 1, value: 7 },
          Instruction::Binary {
            dest: 2,
            operator: Binary::Add,
            left: 0,
            right: 1,
          },
          Instruction::Ret { value: vec![2] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Prog::f1".into(),
        function: 0,
        inputs: vec![IoType::Field],
        output: Some(IoType::Field),
      }],
    };
    (main_prog.check().unwrap(), advice_prog.check().unwrap())
  }

  #[test]
  fn universal_advice_executes_and_rejects_tampered_hint() {
    let (main_prog, advice_prog) = sample_guess_and_advice();
    let mut channels = HintChannels::new();
    let registered =
      register_advice_program(&mut channels, &main_prog, advice_prog).unwrap();
    assert_eq!(registered, vec!["ixcc.guess.f1".to_string()]);
    let hints = main_prog.prepare_hint_channels(&[], &channels).unwrap();
    let rec = hints.execute("Prog::main0", vec![35]).unwrap();
    assert_eq!(rec.output, vec![42]);

    // Tampered advice (+1 mod p) must fail the circuit assertion!
    let (main_prog2, advice_prog2) = sample_guess_and_advice();
    let mut bad_channels = HintChannels::new();
    let (_, hits) = register_tampered_advice_program(
      &mut bad_channels,
      &main_prog2,
      advice_prog2,
      "ixcc.guess.f1",
    )
    .unwrap();
    let bad_hints =
      main_prog2.prepare_hint_channels(&[], &bad_channels).unwrap();
    let err = bad_hints.execute("Prog::main0", vec![35]).unwrap_err().to_string();
    assert!(hits.load(Ordering::Relaxed) > 0);
    assert!(
      err.contains("guess checker mismatch") || err.contains("assert"),
      "unexpected error: {err}"
    );
  }
}
