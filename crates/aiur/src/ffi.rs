//! A small C ABI transports an Ixon package (execution bytecode and an
//! optional companion trace plan), Ixon data hints and a JSON request.
//! Lean's object ABI is confined to c/execution.c; Rust owns execution and tracing.
use crate::artifact::{Package, decode_hints};
use crate::bytecode::Program;
use crate::field::{FieldBackend, NativeField, PrimeField, PrimeField64};
use crate::hints::HintEntry;
use crate::trace::TraceArtifact;
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::ffi::{CString, c_char};

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
) -> Result<Json, String> {
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
) -> Result<Json, String> {
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
  let queries = queries
        .into_iter()
        .map(|(input, output)| {
            json!({
                "function": input.function, "name": program.callable_name(input.function),
                "args": input.args, "output": output.output, "multiplicity": output.multiplicity,
            })
        })
        .collect::<Vec<_>>();
  Ok(
    json!({ "output": record.output, "pretty_output": pretty_output, "queries": queries,
        "memory": record.memory, "memory_types": program.memory_types.iter()
            .map(|(ty, layout)| (ty, layout.width())).collect::<Vec<_>>(),
        "instructions": record.instructions, "trace": trace }),
  )
}

/// # Safety
/// Each pointer must address its length in readable bytes for the duration of
/// this call (a null pointer only with length zero). The returned allocation
/// must be released exactly once with `aiur_free_string`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn aiur_execute(
  package: *const u8,
  package_length: usize,
  hints: *const u8,
  hints_length: usize,
  request: *const u8,
  request_length: usize,
) -> *mut c_char {
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
  let value = match response {
    Ok(Ok(value)) => json!({"ok": value}),
    Ok(Err(error)) => json!({"error": error}),
    Err(panic) => {
      let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("Rust execution panic");
      json!({"error": message})
    },
  };
  // JSON escapes all embedded NULs. No unwind may cross the C boundary.
  CString::new(value.to_string())
    .expect("JSON cannot contain a NUL byte")
    .into_raw()
}

/// # Safety
/// `string` must be null or a live pointer returned by `aiur_execute`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn aiur_free_string(string: *mut c_char) {
  if !string.is_null() {
    // SAFETY: ownership of precisely this CString allocation is returned.
    drop(unsafe { CString::from_raw(string) });
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::artifact::encode_hints;
  use std::ffi::CStr;

  fn call_raw(package: &[u8], hints: &[u8], request: &Json) -> Json {
    let request = request.to_string().into_bytes();
    // SAFETY: the input buffers outlive the call. The returned string is
    // read before it is released once with the matching allocator.
    unsafe {
      let response = aiur_execute(
        package.as_ptr(),
        package.len(),
        hints.as_ptr(),
        hints.len(),
        request.as_ptr(),
        request.len(),
      );
      let json =
        serde_json::from_slice(CStr::from_ptr(response).to_bytes()).unwrap();
      aiur_free_string(response);
      json
    }
  }

  fn call(program: Json, request: &Json) -> Json {
    let program: Program = serde_json::from_value(program).unwrap();
    let package = Package { program, trace: None }.encode();
    call_raw(&package, &encode_hints(&[]), request)
  }

  #[test]
  fn missing_hint_is_an_error_at_the_ffi_boundary() {
    let field = json!({"kind":"field"});
    let response = call(
      json!({
          "version":1, "modulus":97, "enums":[], "maps":[], "tables":[],
          "functions":[{"name":"hinted", "params":[field], "result":field, "registers":2,
              "code":[{"op":"hint", "type":field, "key_type":field, "key":[0], "dest":[1]},
                  {"op":"ret", "value":[1]}]}],
          "entries":[{"name":"main", "function":0, "inputs":[field], "output":field}]
      }),
      &json!({"entry":"main", "args":[7]}),
    );
    assert!(response["error"].as_str().unwrap().contains("missing hint"));
  }

  #[test]
  fn malformed_inputs_return_owned_error_text() {
    let empty = encode_hints(&[]);
    let response = call_raw(&[], &empty, &json!({"entry":"missing"}));
    let error = response["error"].as_str().unwrap();
    assert!(error.contains("invalid execution package"), "{error}");
    let program = json!({"version":2, "modulus":97, "enums":[], "maps":[],
      "tables":[], "functions":[], "entries":[]});
    for (request, expected) in [
      (json!({"entry":"main", "extra":1}), "unknown field"),
      (json!({"flat_args":[]}), "missing field"),
    ] {
      let response = call(program.clone(), &request);
      let error = response["error"].as_str().unwrap();
      assert!(error.contains("invalid execution request"), "{error}");
      assert!(error.contains(expected), "{error}");
    }
    let package: Program = serde_json::from_value(program).unwrap();
    let package = Package { program: package, trace: None }.encode();
    let response = call_raw(&package, &[1], &json!({"entry":"main"}));
    let error = response["error"].as_str().unwrap();
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
    assert_eq!(call(program.clone(), &request)["ok"]["output"], json!([p - 1]));
    request["flat_args"] = json!([p]);
    let response = call(program, &request);
    assert!(response["error"].as_str().unwrap().contains("noncanonical"));
  }
}
