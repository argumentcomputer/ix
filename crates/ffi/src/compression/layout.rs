//! User-facing bounds, resolved to the aggregate backend's circuit order.
use super::*;
use serde_json::{Value, json};

pub(super) fn template(system: &AiurSystem, log: u8) -> Value {
  json!({
    "functions": vec![log; system.toplevel().circuits.len()],
    "memory": system.toplevel().memory_sizes.iter().map(|w| (w.to_string(), json!(log))).collect::<serde_json::Map<_, _>>()
  })
}

pub(super) fn resolve(
  system: &AiurSystem,
  input: &str,
  default: u8,
) -> pipeline::Result<Vec<u8>> {
  let value = if input.is_empty() {
    template(system, default)
  } else {
    serde_json::from_str(input)?
  };
  resolve_for(
    &value,
    system.toplevel().circuits.len(),
    &system.toplevel().memory_sizes,
  )
}

fn resolve_for(
  value: &Value,
  functions: usize,
  widths: &[usize],
) -> pipeline::Result<Vec<u8>> {
  let object = value.as_object().ok_or("root layout must be a JSON object")?;
  if object.len() != 2
    || !object.contains_key("functions")
    || !object.contains_key("memory")
  {
    return Err("root layout requires exactly 'functions' and 'memory'".into());
  }
  let logs = value["functions"]
    .as_array()
    .ok_or("root layout functions must be an array")?;
  let memories = value["memory"]
    .as_object()
    .ok_or("root layout memory must map widths to log-heights")?;
  if logs.len() != functions || memories.len() != widths.len() {
    return Err(format!("root layout requires {functions} function circuits and {} memory widths; use `ix compression layout` for a template", widths.len()).into());
  }
  let log = |v: &Value| -> pipeline::Result<u8> {
    match v.as_u64() {
      Some(n @ 1..=26) => Ok(u8::try_from(n)?),
      _ => Err("root layout log-heights must be integers in 1–26".into()),
    }
  };
  let mut result =
    logs.iter().map(log).collect::<pipeline::Result<Vec<_>>>()?;
  for width in widths {
    let v = memories
      .get(&width.to_string())
      .ok_or_else(|| format!("root layout missing memory width {width}"))?;
    result.push(log(v)?);
  }
  // Native preprocessed byte tables are never resized.
  result.extend([8, 16]);
  Ok(result)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn layout_resolves_memory_widths_in_backend_order() -> pipeline::Result<()> {
    let value = json!({"functions": [12, 6], "memory": {"1": 3, "8": 7}});
    assert_eq!(resolve_for(&value, 2, &[8, 1])?, [12, 6, 7, 3, 8, 16]);
    for bad in [
      json!({"functions": [12], "memory": {"1": 3, "8": 7}}),
      json!({"functions": [12, 6], "memory": {"2": 3, "8": 7}}),
      json!({"functions": [12, 6], "memory": {"1": 0, "8": 7}}),
      json!({"functions": [27, 6], "memory": {"1": 3, "8": 7}}),
      json!({"functions": [256, 6], "memory": {"1": 3, "8": 7}}),
      json!({"functions": [1.5, 6], "memory": {"1": 3, "8": 7}}),
      json!({"functions": [12, 6], "memory": {"1": 3, "8": 7}, "extra": 1}),
    ] {
      assert!(resolve_for(&bad, 2, &[8, 1]).is_err(), "{bad}");
    }
    Ok(())
  }
}
