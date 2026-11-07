//! A small C ABI transports an Ixon package (execution bytecode and an
//! optional companion trace plan), Ixon data hints and a JSON request, and
//! returns the execution record (and trace) in Ixon:
//!
//! ```text
//! response = 0 string(error) | 1 record
//! record   = nats(output) option(string(pretty_output)) list(query)
//!            list(memory) list(type nat(width)) nat(instructions)
//!            option(list(matrix))
//! query    = nat(function) string(name) nats(args) nats(output)
//!            nat(multiplicity)
//! memory   = nat(address) type nats(value) nat(multiplicity)
//! matrix   = string(chip) nat(width) nat(height) nat(unpadded_height)
//!            nats(values) nats(multiplicities)
//! ```
//! Lean's object ABI is confined to c/execution.c; Rust owns execution and tracing.
use crate::artifact::{Package, decode_hints, put_type};
use crate::bytecode::Program;
use crate::field::{FieldBackend, NativeField, PrimeField, PrimeField64};
use crate::hints::HintEntry;
use crate::ixon::Writer;
use crate::trace::TraceArtifact;
use serde::Deserialize;
use serde_json::Value as Json;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
  entry: String,
  args: Option<Vec<Json>>,
  flat_args: Option<Vec<u64>>,
  #[serde(default)]
  pad_trace: bool,
  #[serde(default)]
  compare_reference: bool,
}
fn execute_request(
  package: &[u8],
  hints: &[u8],
  request: &[u8],
) -> Result<Vec<u8>, String> {
  let Package { program, trace } = Package::decode(package)
    .map_err(|e| format!("invalid execution package: {e}"))?;
  let hints =
    decode_hints(hints).map_err(|e| format!("invalid execution hints: {e}"))?;
  let request: Request = serde_json::from_slice(request)
    .map_err(|e| format!("invalid execution request: {e}"))?;
  // This embedding chooses multi-stark's reference field once, before
  // preparation. Other runtime primes retain the generic integer fallback.
  if program.modulus == multi_stark::types::Val::ORDER_U64 {
    let field = NativeField::<multi_stark::types::Val>::new();
    run_request(program, trace, &hints, request, field)
  } else {
    let field = PrimeField::new(program.modulus)?;
    run_request(program, trace, &hints, request, field)
  }
}

fn run_request<B: FieldBackend>(
  program: Program,
  trace: Option<TraceArtifact>,
  hints: &[HintEntry],
  request: Request,
  field: B,
) -> Result<Vec<u8>, String> {
  let program = program.check_with(field)?;
  let record = match (request.args, request.flat_args) {
    (Some(args), None) => {
      let entry = program.entry(&request.entry)?;
      if args.len() != entry.inputs.len() {
        return Err("entry argument count mismatch".into());
      }
      let values = entry
        .inputs
        .iter()
        .zip(&args)
        .map(|(t, v)| t.read_json(v))
        .collect::<Result<Vec<_>, _>>()?;
      program.execute_values_with_hints(&request.entry, &values, hints)
    },
    (None, Some(args)) => {
      let args = field.decode(&args)?;
      program.execute_with_hints(&request.entry, args, hints)
    },
    _ => return Err("supply exactly one of args and flat_args".into()),
  }
  .map_err(|e| e.to_string())?;
  let entry = program.entry(&request.entry)?;
  let trace = if let Some(artifact) = trace {
    let plan = crate::trace::TracePlan::new(&program, artifact)?;
    // Recover the flat root input from the execution record. Public callers
    // needing to reuse one record should use TracePlan directly.
    let root = record
      .queries
      .iter()
      .find(|(input, _)| input.function == entry.function)
      .ok_or("missing root query")?
      .0;
    let trace =
      plan.generate(&record, &request.entry, root.args, request.pad_trace)?;
    if request.compare_reference
      && trace
        != plan.generate_reference(
          &record,
          &request.entry,
          root.args,
          request.pad_trace,
        )?
    {
      return Err("compiled population differs from reference writer".into());
    }
    plan.check(&record, &trace, &request.entry, root.args)?;
    Some(trace)
  } else {
    None
  };
  let pretty_output = if entry.output.is_some() {
    Some(program.output_value(&request.entry, &record)?.to_string())
  } else {
    None
  };
  let mut queries = record.queries.iter().collect::<Vec<_>>();
  queries.sort_by(|(a, _), (b, _)| {
    a.function.cmp(&b.function).then_with(|| {
      a.args
        .iter()
        .map(|&x| field.to_u64(x))
        .cmp(b.args.iter().map(|&x| field.to_u64(x)))
    })
  });
  let words = |w: &mut Writer, xs: &[B::Element]| {
    w.list(xs, |w, &x| w.nat(field.to_u64(x)));
  };
  let mut w = Writer::new();
  words(&mut w, &record.output);
  w.option(pretty_output.as_ref(), |w, s| w.str(s));
  w.list(&queries, |w, (input, output)| {
    w.usize(input.function);
    w.str(program.callable_name(input.function).unwrap_or_default());
    words(w, input.args);
    words(w, output.output);
    w.nat(output.multiplicity);
  });
  let memory: Vec<_> = record.memory.iter().collect();
  w.list(&memory, |w, entry| {
    w.usize(entry.address);
    put_type(w, entry.cell.r#type);
    words(w, entry.cell.value);
    w.nat(entry.multiplicity);
  });
  w.list(&program.memory_types, |w, (ty, layout)| {
    put_type(w, ty);
    w.usize(layout.width());
  });
  w.nat(record.instructions);
  w.option(trace.as_ref(), |w, trace| {
    w.list(&trace.matrices, |w, m| {
      w.str(&m.chip);
      w.usize(m.width);
      w.usize(m.height);
      w.usize(m.unpadded_height);
      words(w, &m.values);
      w.nats(&m.multiplicities);
    });
  });
  Ok(w.into_bytes())
}

/// # Safety
/// Each pointer must address its length in readable bytes for the duration of
/// this call (a null pointer only with length zero), and `response_length`
/// must be writable. The returned buffer of `*response_length` bytes must be
/// released exactly once with `aiur_free_bytes`.
#[unsafe(no_mangle)]
#[allow(unreachable_pub)] // Exported through the C ABI, not Rust paths.
pub unsafe extern "C" fn aiur_execute(
  package: *const u8,
  package_length: usize,
  hints: *const u8,
  hints_length: usize,
  request: *const u8,
  request_length: usize,
  response_length: *mut usize,
) -> *mut u8 {
  // SAFETY: the caller guarantees the buffer's validity; it is only borrowed.
  let borrow = |data: *const u8, length: usize| unsafe {
    if data.is_null() {
      (length == 0).then_some(&[][..])
    } else {
      Some(std::slice::from_raw_parts(data, length))
    }
  };
  let response = std::panic::catch_unwind(|| {
    match (
      borrow(package, package_length),
      borrow(hints, hints_length),
      borrow(request, request_length),
    ) {
      (Some(package), Some(hints), Some(request)) => {
        execute_request(package, hints, request)
      },
      _ => Err("null execution input".into()),
    }
  });
  let mut w = Writer::new();
  match response {
    Ok(Ok(record)) => {
      w.u8(1);
      w.raw(&record);
    },
    Ok(Err(error)) => {
      w.u8(0);
      w.str(&error);
    },
    Err(panic) => {
      let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("Rust execution panic");
      w.u8(0);
      w.str(message);
    },
  }
  let bytes = w.into_bytes().into_boxed_slice();
  // SAFETY: the caller supplies a writable length slot.
  unsafe { *response_length = bytes.len() };
  Box::into_raw(bytes).cast::<u8>()
}

/// # Safety
/// `bytes` must be a live buffer of `length` bytes returned by
/// `aiur_execute`.
#[unsafe(no_mangle)]
#[allow(unreachable_pub)] // Exported through the C ABI, not Rust paths.
pub unsafe extern "C" fn aiur_free_bytes(bytes: *mut u8, length: usize) {
  // SAFETY: ownership of precisely this boxed slice is returned.
  drop(unsafe {
    Box::from_raw(std::ptr::slice_from_raw_parts_mut(bytes, length))
  });
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::artifact::encode_hints;
  use crate::ixon::Reader;
  use serde_json::json;

  /// The output words of a successful execution, or its error.
  fn call_raw(
    package: &[u8],
    hints: &[u8],
    request: &Json,
  ) -> Result<Vec<u64>, String> {
    let request = request.to_string().into_bytes();
    let mut length = 0;
    // SAFETY: the input buffers outlive the call. The returned buffer is
    // read before it is released once with its length.
    let response = unsafe {
      let bytes = aiur_execute(
        package.as_ptr(),
        package.len(),
        hints.as_ptr(),
        hints.len(),
        request.as_ptr(),
        request.len(),
        &raw mut length,
      );
      let response = std::slice::from_raw_parts(bytes, length).to_vec();
      aiur_free_bytes(bytes, length);
      response
    };
    let mut r = Reader::new(&response);
    if r.tag("response", 2).unwrap() == 0 {
      let error = r.string().unwrap();
      r.finish().unwrap();
      return Err(error);
    }
    Ok(r.nats().unwrap())
  }

  fn call(program: Json, request: &Json) -> Result<Vec<u64>, String> {
    let program: Program = serde_json::from_value(program).unwrap();
    let package = Package { program, trace: None }.encode();
    call_raw(&package, &encode_hints(&[]), request)
  }

  #[test]
  fn missing_hint_is_an_error_at_the_ffi_boundary() {
    let field = json!({"kind":"field"});
    let error = call(
      json!({
          "version":1, "modulus":97, "enums":[], "maps":[], "tables":[],
          "functions":[{"name":"hinted", "params":[field], "result":field, "registers":2,
              "code":[{"op":"hint", "type":field, "key_type":field, "key":[0], "dest":[1]},
                  {"op":"ret", "value":[1]}]}],
          "entries":[{"name":"main", "function":0, "inputs":[field], "output":field}]
      }),
      &json!({"entry":"main", "args":[7]}),
    )
    .unwrap_err();
    assert!(error.contains("missing hint"), "{error}");
  }

  #[test]
  fn malformed_inputs_return_owned_error_text() {
    let empty = encode_hints(&[]);
    let error = call_raw(&[], &empty, &json!({"entry":"missing"})).unwrap_err();
    assert!(error.contains("invalid execution package"), "{error}");
    let program = json!({"version":2, "modulus":97, "enums":[], "maps":[],
      "tables":[], "functions":[], "entries":[]});
    for (request, expected) in [
      (json!({"entry":"main", "extra":1}), "unknown field"),
      (json!({"flat_args":[]}), "missing field"),
    ] {
      let error = call(program.clone(), &request).unwrap_err();
      assert!(error.contains("invalid execution request"), "{error}");
      assert!(error.contains(expected), "{error}");
    }
    let package: Program = serde_json::from_value(program).unwrap();
    let package = Package { program: package, trace: None }.encode();
    let error = call_raw(&package, &[1], &json!({"entry":"main"})).unwrap_err();
    assert!(error.contains("invalid execution hints"), "{error}");
  }

  #[test]
  fn native_ffi_preserves_integer_encoding_and_rejects_noncanonical_inputs() {
    let p = multi_stark::types::Val::ORDER_U64;
    let f = json!({"kind":"field"});
    let program = json!({
        "version":2, "modulus":p, "enums":[], "maps":[], "tables":[],
        "functions":[{"name":"identity", "params":[f], "result":f, "registers":1,
            "code":[{"op":"ret", "value":[0]}]}],
        "entries":[{"name":"main", "function":0, "inputs":[f], "output":f}]
    });
    let mut request = json!({"entry":"main", "flat_args":[p-1]});
    assert_eq!(call(program.clone(), &request), Ok(vec![p - 1]));
    request["flat_args"] = json!([p]);
    let error = call(program, &request).unwrap_err();
    assert!(error.contains("noncanonical"), "{error}");
  }
}
