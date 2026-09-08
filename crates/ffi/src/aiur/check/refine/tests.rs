use super::super::tests::{axiom, manifest, store};
use super::*;
use std::sync::Mutex;

// Keep the existing outcome fixtures, now driven one attempt at a time by
// the real completion dispatcher. Parallel scheduling is exercised below.
fn run(
  env: &Env,
  manifest: &ShardManifest,
  owned: &[Vec<Address>],
  selection: Option<&[usize]>,
  execute: impl FnMut(
    &[Vec<Address>],
    &[String],
  ) -> Result<Vec<ShardCheckResult>, String>
  + Send,
) -> Result<Runs, String> {
  let gate = Admission::for_test(1);
  let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
  let execute = Mutex::new(execute);
  super::run(
    env,
    manifest,
    owned,
    selection,
    &gate,
    &pool,
    |_| 1024,
    |owned, label| {
      let mut results =
        execute.lock().unwrap()(&[owned.to_vec()], &[label.to_owned()])?;
      if results.len() != 1 {
        return Err("missing attempt result".into());
      }
      Ok(results.remove(0))
    },
  )
}

fn outcome(status: usize) -> ShardCheckResult {
  ShardCheckResult {
    error: if status == 0 { String::new() } else { "resource limit".into() },
    peak_bytes: if status == 0 { 42 } else { 0 },
    suggested_parts: if status == 0 { 1 } else { 2 },
    resource_status: status,
    claim: None,
  }
}

#[test]
fn recursive_retry_checks_all_final_parts_and_keeps_mutual_projections_together()
 {
  let env = Env::new();
  let a = axiom(&env, 0);
  let b = axiom(&env, 1);
  let c = axiom(&env, 2);
  let projection =
    store(&env, &ixon::constant::defn_proj_constant(0, a.clone()));
  let m = manifest(vec![vec![a.clone(), b.clone(), c.clone()]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let mut passed = Vec::new();
  let runs = run(&env, &m, &owned, None, |batch, _| {
    Ok(
      batch
        .iter()
        .map(|p| {
          assert_eq!(p.contains(&a), p.contains(&projection));
          if p.contains(&b) && p.contains(&c)
            || p.contains(&a) && p.contains(&b)
          {
            outcome(1)
          } else {
            passed.extend(p.clone());
            outcome(0)
          }
        })
        .collect(),
    )
  })
  .unwrap();
  passed.sort_unstable();
  assert_eq!(passed, owned[0]);
  assert_eq!(runs.parts[0].len(), 3);
  assert_eq!(runs.attempts, 5);
  assert!(runs.results[0].as_ref().unwrap().error.is_empty());
  assert_eq!(
    runs.results[0].as_ref().unwrap().peak_bytes,
    0,
    "aborted parent has no measured peak"
  );
}

#[test]
fn single_block_limit_is_a_failure_not_an_infinite_retry_or_success() {
  let env = Env::new();
  let a = axiom(&env, 0);
  let m = manifest(vec![vec![a]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let runs = run(&env, &m, &owned, None, |batch, _| {
    Ok(batch.iter().map(|_| outcome(1)).collect())
  })
  .unwrap();
  assert_eq!(runs.attempts, 1);
  assert!(
    runs.results[0]
      .as_ref()
      .unwrap()
      .error
      .contains("single block cannot be split")
  );
}

#[test]
fn aggregate_limit_retries_without_changing_claim_and_is_bounded() {
  let env = Env::new();
  let a = axiom(&env, 0);
  let m = manifest(vec![vec![a]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let mut wave = 0;
  let runs = run(&env, &m, &owned, None, |batch, labels| {
    assert_eq!(batch, owned);
    assert_eq!(labels, &["0"]);
    wave += 1;
    Ok(vec![outcome(if wave == 1 { 2 } else { 0 })])
  })
  .unwrap();
  assert_eq!(runs.attempts, 2);
  assert!(runs.results[0].as_ref().unwrap().error.is_empty());
  assert_eq!(runs.results[0].as_ref().unwrap().peak_bytes, 42);
  let limited =
    run(&env, &m, &owned, None, |_, _| Ok(vec![outcome(2)])).unwrap();
  assert_eq!(limited.attempts, 3);
  assert!(!limited.results[0].as_ref().unwrap().error.is_empty());
}

#[test]
fn semantic_failures_are_not_retried_and_missing_results_are_rejected() {
  let env = Env::new();
  let m = manifest(vec![vec![axiom(&env, 0), axiom(&env, 1)]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let runs = run(&env, &m, &owned, None, |_, _| {
    let mut failed = outcome(0);
    failed.error = "ill typed".into();
    Ok(vec![failed])
  })
  .unwrap();
  assert_eq!(runs.attempts, 1);
  assert!(runs.results[0].as_ref().unwrap().error.contains("ill typed"));
  assert!(run(&env, &m, &owned, None, |_, _| Ok(Vec::new())).is_err());
}

#[test]
fn reports_do_not_claim_an_aborted_parent_was_measured() {
  let env = Env::new();
  let m = manifest(vec![vec![axiom(&env, 0), axiom(&env, 1)]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let runs = run(&env, &m, &owned, None, |batch, _| {
    Ok(batch.iter().map(|p| outcome(usize::from(p.len() > 1))).collect())
  })
  .unwrap();
  let mut report =
    json!({"leaves": [{"status": "measured", "predicted_peak_bytes": 0}]});
  extend_report(&mut report, &runs);
  assert_eq!(report["leaves"][0]["status"], "refined");
  assert!(report["leaves"][0]["predicted_peak_bytes"].is_null());
  assert_eq!(report["leaves"][0]["parts"].as_array().unwrap().len(), 2);
  assert_eq!(report["executed"], 3);
}

#[test]
fn selected_refinement_preserves_original_ids_and_never_executes_skipped_leaves()
 {
  let env = Env::new();
  let skipped_a = axiom(&env, 0);
  let selected_a = axiom(&env, 1);
  let skipped_b = axiom(&env, 2);
  let selected_b = axiom(&env, 3);
  let selected_c = axiom(&env, 4);
  let m = manifest(vec![
    vec![skipped_a.clone()],
    vec![selected_a],
    vec![skipped_b.clone()],
    vec![selected_b, selected_c],
  ]);
  let owned = prepare_owned(&env, &m).unwrap();
  let mut waves = Vec::new();
  let runs = run(&env, &m, &owned, Some(&[3, 1, 3]), |batch, labels| {
    waves.push(labels.to_vec());
    for addresses in batch {
      assert!(!addresses.contains(&skipped_a));
      assert!(!addresses.contains(&skipped_b));
    }
    Ok(batch.iter().map(|p| outcome(usize::from(p.len() > 1))).collect())
  })
  .unwrap();
  assert_eq!(waves, vec![vec!["1"], vec!["3"], vec!["3.0"], vec!["3.1"]]);
  assert_eq!(runs.attempts, 4);
  for id in [0, 2] {
    assert!(runs.results[id].is_none());
    assert!(runs.parts[id].is_empty());
  }
  for id in [1, 3] {
    assert!(runs.results[id].as_ref().unwrap().error.is_empty());
    let mut checked: Vec<_> =
      runs.parts[id].iter().flat_map(|p| p.owned.clone()).collect();
    checked.sort_unstable();
    assert_eq!(checked, owned[id]);
  }
  let mut report = json!({"leaves": [
    {"status": "unchanged"}, {"status": "measured"},
    {"status": "unchanged"}, {"status": "measured"}
  ]});
  extend_report(&mut report, &runs);
  assert_eq!(report["leaves"][0], json!({"status": "unchanged"}));
  assert_eq!(report["leaves"][2], json!({"status": "unchanged"}));
  assert_eq!(report["leaves"][3]["status"], "refined");
  assert_eq!(report["leaves"][3]["parts"][0]["label"], "3.0");
}

#[test]
fn invalid_selection_never_reaches_the_executor() {
  let env = Env::new();
  let m = manifest(vec![vec![axiom(&env, 0)]]);
  let owned = prepare_owned(&env, &m).unwrap();
  for selected in [vec![], vec![1], vec![usize::MAX]] {
    assert!(
      run(&env, &m, &owned, Some(&selected), |_, _| {
        panic!("invalid selection reached execution")
      })
      .is_err()
    );
  }
}

#[test]
fn a_split_child_executes_while_an_unrelated_original_is_still_active() {
  use std::{sync::mpsc, time::Duration};
  let env = Env::new();
  let m =
    manifest(vec![vec![axiom(&env, 0), axiom(&env, 1)], vec![axiom(&env, 2)]]);
  let owned = prepare_owned(&env, &m).unwrap();
  let gate = Admission::for_test(2);
  let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
  let (slow_tx, slow_rx) = mpsc::channel();
  let (child_tx, child_rx) = mpsc::channel();
  let slow_rx = Mutex::new(slow_rx);
  let child_rx = Mutex::new(child_rx);
  let runs = super::run(
    &env,
    &m,
    &owned,
    None,
    &gate,
    &pool,
    |_| 1024,
    |_, label| {
      match label {
        "0" => {
          slow_rx.lock().unwrap().recv_timeout(Duration::from_secs(3)).unwrap();
          return Ok(outcome(1));
        },
        "1" => {
          slow_tx.send(()).unwrap();
          child_rx
            .lock()
            .unwrap()
            .recv_timeout(Duration::from_secs(3))
            .unwrap();
        },
        "0.0" => child_tx.send(()).unwrap(),
        "0.1" => {},
        _ => panic!("unexpected attempt {label}"),
      }
      Ok(outcome(0))
    },
  )
  .unwrap();
  assert_eq!(runs.attempts, 4);
  assert_eq!(runs.max_generation, 1);
  assert_eq!(
    runs.parts[0].iter().map(|p| p.label.as_str()).collect::<Vec<_>>(),
    ["0.0", "0.1"]
  );
  for (id, parts) in runs.parts.iter().enumerate() {
    let mut checked: Vec<_> =
      parts.iter().flat_map(|p| p.owned.clone()).collect();
    checked.sort_unstable();
    assert_eq!(checked, owned[id]);
    assert!(runs.results[id].as_ref().unwrap().error.is_empty());
  }
}

#[test]
fn report_ownership_and_claims_are_stable_across_completion_orders() {
  let env = Env::new();
  let addresses: Vec<_> = (0..12).map(|i| axiom(&env, i)).collect();
  let projection =
    store(&env, &ixon::constant::defn_proj_constant(0, addresses[1].clone()));
  let m = manifest(vec![
    vec![addresses[0].clone()],
    addresses[1..8].to_vec(),
    addresses[8..].to_vec(),
  ]);
  let owned = prepare_owned(&env, &m).unwrap();
  let mut reference = None;
  for workers in [1, 2, 64] {
    let gate = Admission::for_test(workers);
    let pool =
      rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
    let runs = super::run(
      &env,
      &m,
      &owned,
      Some(&[2, 1]),
      &gate,
      &pool,
      |_| 1024,
      |owned, _| {
        assert!(!owned.contains(&addresses[0]));
        assert_eq!(owned.contains(&addresses[1]), owned.contains(&projection));
        let blocks = owned.len() - usize::from(owned.contains(&projection));
        let mut result = outcome(usize::from(blocks > 1));
        let (claim, _) =
          ixon::shard_claim::shard_check_env_claim(&env, owned).unwrap();
        let mut bytes = Vec::new();
        claim.put(&mut bytes);
        result.claim = Some(Address::hash(&bytes));
        Ok(result)
      },
    )
    .unwrap();
    assert_eq!(runs.attempts, 20);
    assert!(runs.results[0].is_none());
    for id in [1, 2] {
      let mut checked: Vec<_> =
        runs.parts[id].iter().flat_map(|p| p.owned.clone()).collect();
      checked.sort_unstable();
      assert_eq!(checked, owned[id]);
    }
    let mut report = json!({"leaves": [{"status":"unchanged"}, {}, {}]});
    extend_report(&mut report, &runs);
    assert_eq!(report["scheduler"], "completion-driven");
    assert!(report["waves"].is_null());
    if let Some(reference) = &reference {
      assert_eq!(&report, reference);
    } else {
      reference = Some(report);
    }
  }
}

#[test]
fn malformed_resource_outcomes_are_not_retried_or_reported_as_success() {
  let env = Env::new();
  let m = manifest(vec![vec![axiom(&env, 0), axiom(&env, 1)]]);
  let owned = prepare_owned(&env, &m).unwrap();
  for malformed in 0..3 {
    assert!(
      run(&env, &m, &owned, None, |_, _| {
        let mut result = outcome(1);
        match malformed {
          0 => result.resource_status = 3,
          1 => result.error.clear(),
          _ => result.peak_bytes = 1,
        }
        Ok(vec![result])
      })
      .err()
      .unwrap()
      .contains("invalid resource-limited")
    );
  }
}
