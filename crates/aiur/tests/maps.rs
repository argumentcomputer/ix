use aiur::{
  Program, bytecode::CheckedProgram, execute::QueryInput, maps::MapOverrides,
};
use serde_json::json;
use std::sync::{
  Arc,
  atomic::{AtomicUsize, Ordering},
};

fn fixture(rows: &[u64]) -> CheckedProgram {
  let f = json!({"kind":"field"});
  let unit = json!({"kind":"tuple","items":[]});
  serde_json::from_value::<Program>(json!({
        "version":1,"modulus":97,"enums":[],
        "functions":[{"name":"main","params":[f],"result":f,"registers":5,"code":[
            {"op":"call","function":1,"args":[0],"dest":[1]},
            {"op":"call","function":1,"args":[0],"dest":[2]},
            {"op":"call","function":2,"args":[0],"dest":[3]},
            {"op":"call","function":3,"args":[],"dest":[]},
            {"op":"binary","operator":"add","left":1,"right":2,"dest":4},
            {"op":"binary","operator":"add","left":4,"right":3,"dest":4},
            {"op":"ret","value":[4]}]}],
        "maps":[
            {"name":"square","params":[f],"result":f,"input":0,"output":1},
            {"name":"cube","params":[f],"result":f,"input":0,"output":2},
            {"name":"unit","params":[],"result":unit,"input":3,"output":3}],
        "tables":[
            {"name":"xs","type":{"kind":"tuple","items":[f]},"rows":rows.iter().map(|&x| vec![x]).collect::<Vec<_>>()},
            {"name":"squares","type":f,"rows":rows.iter().map(|&x| vec![x*x%97]).collect::<Vec<_>>()},
            {"name":"cubes","type":f,"rows":rows.iter().map(|&x| vec![x*x*x%97]).collect::<Vec<_>>()},
            {"name":"unit","type":unit,"rows":[[]]}],
        "entries":[
            {"name":"main","function":0,"inputs":[f],"output":f},
            {"name":"square","function":1,"inputs":[f],"output":f}]
    })).unwrap().check().unwrap()
}

#[test]
fn rebinding_a_fixed_map_to_a_slice_provider_replaces_prepared_calls() {
  let p = fixture(&[0, 1, 2]);
  let fixed_calls = Arc::new(AtomicUsize::new(0));
  let slice_calls = Arc::new(AtomicUsize::new(0));
  let mut fixed = MapOverrides::new();
  let calls = fixed_calls.clone();
  fixed
    .insert_fixed::<1, 1>("square", move |[x]| {
      calls.fetch_add(1, Ordering::Relaxed);
      Ok((x as usize, [x * x]))
    })
    .unwrap();
  let prepared =
    p.prepare_hints(&[]).unwrap().with_map_overrides(&fixed).unwrap();
  // Binding validates the provider against every immutable table row.
  fixed_calls.store(0, Ordering::Relaxed);
  let before = prepared.execute("main", vec![2]).unwrap();
  assert_eq!(fixed_calls.load(Ordering::Relaxed), 2);
  let mut fallback = MapOverrides::new();
  let calls = slice_calls.clone();
  fallback
    .insert("square", 1, 1, move |input, output| {
      calls.fetch_add(1, Ordering::Relaxed);
      output[0] = input[0] * input[0];
      Ok(input[0] as usize)
    })
    .unwrap();
  let prepared = prepared.with_map_overrides(&fallback).unwrap();
  slice_calls.store(0, Ordering::Relaxed);
  drop(fixed);
  drop(fallback);
  let after = prepared.execute("main", vec![2]).unwrap();
  assert_eq!(fixed_calls.load(Ordering::Relaxed), 2);
  assert_eq!(slice_calls.load(Ordering::Relaxed), 2);
  assert_eq!(before.output, after.output);
  assert_eq!(before.queries, after.queries);
  assert_eq!(before.instructions, after.instructions);
}

#[test]
fn overrides_preserve_sparse_and_permuted_tables_counts_and_fresh_sessions() {
  for rows in [&[2, 0, 1][..], &[9, 2, 5][..]] {
    let program = fixture(rows);
    let calls = Arc::new(AtomicUsize::new(0));
    let mut maps = MapOverrides::new();
    let captured = calls.clone();
    let row_order = rows.to_vec();
    maps
      .insert("square", 1, 1, move |args, out| {
        captured.fetch_add(1, Ordering::Relaxed);
        assert_eq!(out, [0]);
        out[0] = args[0] * args[0] % 97;
        row_order
          .iter()
          .position(|&x| x == args[0])
          .ok_or_else(|| "no table entry for map input".into())
      })
      .unwrap();
    maps
      .insert("unit", 0, 0, |args, out| {
        assert!(args.is_empty() && out.is_empty());
        Ok(0)
      })
      .unwrap();
    let prepared =
      program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).unwrap();
    drop(maps);
    for _ in 0..2 {
      for &x in rows {
        let native = prepared.execute("main", vec![x]).unwrap();
        let fallback = program.execute("main", vec![x]).unwrap();
        assert_eq!(native.output, [(2 * x * x + x * x * x) % 97]);
        assert_eq!(native.output, fallback.output);
        assert_eq!(native.queries, fallback.queries);
        assert_eq!(native.instructions, fallback.instructions);
        assert_eq!(native.queries.len(), 4);
        assert!(!native.queries.is_empty());
        assert_eq!(native.queries.iter().count(), 4);
        let square = native
          .queries
          .get(&QueryInput { function: 1, args: vec![x] })
          .unwrap();
        assert_eq!(square.multiplicity, 2);
        assert_eq!(square.output, [x * x % 97]);
        assert_eq!(
          native
            .queries
            .get(&QueryInput { function: 2, args: vec![x] })
            .unwrap()
            .multiplicity,
          1
        );
        assert!(
          native
            .queries
            .get(&QueryInput { function: 1, args: vec![90] })
            .is_none()
        );
        for &unused in rows.iter().filter(|&&other| other != x) {
          assert!(
            native
              .queries
              .get(&QueryInput { function: 1, args: vec![unused] })
              .is_none()
          );
        }
      }
    }
    assert_eq!(calls.load(Ordering::Relaxed), 5 * rows.len());
    let square_only = prepared.execute("square", vec![2]).unwrap();
    assert_eq!(square_only.output, [4]);
    // Preallocated rows in the unused cube/unit tables are not queries.
    assert_eq!(square_only.queries.len(), 1);
    assert_eq!(square_only.queries.iter().count(), 1);
    assert_eq!(square_only.queries.keys().next().unwrap().function, 1);
    assert!(
      prepared
        .execute("main", vec![90])
        .unwrap_err()
        .message
        .contains("no table entry")
    );
  }
}

#[test]
fn bindings_reject_unknown_functions_wrong_arities_and_duplicates() {
  let program = fixture(&[0, 1, 2]);
  for (name, inputs, outputs) in
    [("missing", 1, 1), ("main", 1, 1), ("square", 2, 1), ("square", 1, 2)]
  {
    let mut maps = MapOverrides::new();
    maps.insert(name, inputs, outputs, |_, _| Ok(0)).unwrap();
    assert!(
      program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).is_err()
    );
    assert!(
      maps
        .insert(name, inputs, outputs, |_, _| Ok(0))
        .unwrap_err()
        .contains("duplicate")
    );
  }
}

#[test]
fn provider_errors_and_noncanonical_outputs_fail_execution() {
  let program = fixture(&[0, 1, 2]);
  let mut maps = MapOverrides::new();
  maps.insert("square", 1, 1, |_, _| Err("provider failure".into())).unwrap();
  let result = program.prepare_hints(&[]).unwrap().with_map_overrides(&maps);
  assert!(result.err().unwrap().contains("provider failure"));
  let mut maps = MapOverrides::new();
  maps
    .insert("square", 1, 1, |args, out| {
      out[0] = 97;
      Ok(args[0] as usize)
    })
    .unwrap();
  let prepared =
    program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).unwrap();
  assert!(prepared.execute("main", vec![2]).is_err());
}

#[test]
fn binding_checks_actual_row_order_and_runtime_rejects_invalid_indices() {
  for bad_index in [0, 3, usize::MAX] {
    let program = fixture(&[2, 0, 1]);
    let mut maps = MapOverrides::new();
    maps.insert("square", 1, 1, move |_, _| Ok(bad_index)).unwrap();
    let result = program.prepare_hints(&[]).unwrap().with_map_overrides(&maps);
    assert!(result.err().unwrap().contains("row index mismatch"));
  }
  let program = fixture(&[0, 1, 2]);
  let mut maps = MapOverrides::new();
  maps
    .insert("square", 1, 1, |args, out| {
      if args[0] == 90 {
        return Err("provider failure".into());
      }
      out[0] = args[0] * args[0] % 97;
      // Valid on table inputs, but deliberately returns invalid row indices
      // outside its domain. The runtime must report an error without panicking.
      Ok(if args[0] == 91 { usize::MAX } else { args[0] as usize })
    })
    .unwrap();
  let prepared =
    program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).unwrap();
  for x in [3, 91] {
    assert!(
      prepared
        .execute("main", vec![x])
        .unwrap_err()
        .message
        .contains("out of bounds")
    );
  }
  assert!(
    prepared
      .execute("main", vec![90])
      .unwrap_err()
      .message
      .contains("provider failure")
  );
}

#[test]
fn fixed_providers_match_tables_with_captured_order_and_empty_outputs() {
  let rows = [9, 2, 5];
  let program = fixture(&rows);
  let mut maps = MapOverrides::new();
  maps
    .insert_fixed::<1, 1>("square", move |[x]| {
      let row = rows.iter().position(|&v| v == x).ok_or("outside domain")?;
      Ok((row, [x * x % 97]))
    })
    .unwrap();
  maps.insert_fixed::<0, 0>("unit", |[]| Ok((0, []))).unwrap();
  let prepared =
    program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).unwrap();
  drop(maps);
  for _ in 0..2 {
    for x in rows {
      for entry in ["main", "square"] {
        let actual = prepared.execute(entry, vec![x]).unwrap();
        let expected = program.execute(entry, vec![x]).unwrap();
        assert_eq!(actual.output, expected.output);
        assert_eq!(actual.queries, expected.queries);
        assert_eq!(actual.instructions, expected.instructions);
      }
    }
  }
  assert!(
    prepared
      .execute("main", vec![90])
      .unwrap_err()
      .message
      .contains("outside domain")
  );
}

#[test]
fn fixed_providers_preserve_runtime_validation_and_binding_errors() {
  let program = fixture(&[0, 1, 2]);
  let mut maps = MapOverrides::new();
  maps
    .insert_fixed::<1, 1>("square", |[x]| {
      Ok((
        if x == 90 { usize::MAX } else { x as usize },
        [if x == 2 { 97 } else { 0 }],
      ))
    })
    .unwrap();
  assert!(
    maps
      .insert_fixed::<1, 1>("square", |[x]| Ok((0, [x])))
      .unwrap_err()
      .contains("duplicate")
  );
  let prepared =
    program.prepare_hints(&[]).unwrap().with_map_overrides(&maps).unwrap();
  for entry in ["main", "square"] {
    for (x, error) in [(2, "noncanonical"), (90, "out of bounds")] {
      assert!(
        prepared.execute(entry, vec![x]).unwrap_err().message.contains(error)
      );
    }
  }
  let mut maps = MapOverrides::new();
  maps.insert_fixed::<2, 1>("square", |[a, _]| Ok((0, [a]))).unwrap();
  assert!(
    program
      .prepare_hints(&[])
      .unwrap()
      .with_map_overrides(&maps)
      .err()
      .unwrap()
      .contains("signature mismatch")
  );
}
