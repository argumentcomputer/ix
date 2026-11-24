//! Cross-language Ixon v5 / `Claim.de` / BLAKE3 parity test vector generator
//! and verifier (`Workstream 2B-3`).
//!
//! Covers:
//! - All 7 `Claim` variants (`eval`, `check`, `checkEnv`, `reveal`, `contains`,
//!   `catalog`, `binding`), including `bindingAssumed`, `literalClass`,
//!   `axioms = some/none`, `assumptions = some/none`, and all 9
//!   `RevealConstantInfo` + 3 `RevealMutConstInfo` variants.
//! - All 7 `Proof` envelope variants (`0xF` flag).
//! - `AssumptionTree` (`Leaf`, `Padding`, canonical 2-leaf, canonical 3-leaf
//!   padded, joined) with both wire bytes and Merkle root hashes.
//! - `Comm` (untagged and `0xE1` tagged + commitment hash).
//! - `Univ` (all 5 constructors + `Succ` telescope).
//! - `Expr` (all 12 constructors: `sort`, `var`, `ref`, `rec`, `prj`, `str`,
//!   `nat`, `app`, `lam`, `all`, `let` with modes & `non_dep`, `share`, plus
//!   multi-level telescopes).
//! - `Constant` (all 9 variants: `defn`, `recr`, `axio`, `quot`, `cPrj`,
//!   `rPrj`, `iPrj`, `dPrj`, `muts`, verified with `Constant::get_canonical`
//!   and `binders_complete()`).
//! - Raw BLAKE3 boundary vectors (0B, 3B, 64B, 65B, 1024B, 1025B).
//! - `DynamicLink` & retired/reserved negative controls: verifies `Claim::from_bytes`
//!   strictly REJECTS tags `0xE8 0x0D` (21), `0xE8 0x0E` (22), validators
//!   `10`/`11`, retired resource tag `0xE8 0x01`, and retired/reserved
//!   validators `1`, `2`, `6`, `7`, `8`, `9`.
//!
//! Writes (or checks byte-for-byte parity against)
//! `Tests/Fixtures/IxonParity/vectors.json`.

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind};
use ixon::assumption_tree::AssumptionTree;
use ixon::comm::Comm;
use ixon::constant::{
  Axiom, BinderBlock, BinderNode, Constant, ConstantInfo, Constructor,
  ConstructorProj, DefKind, Definition, DefinitionProj, Inductive,
  InductiveProj, MutConst, Quotient, Recursor, RecursorProj, RecursorRule,
};
use ixon::env::Env;
use ixon::expr::Expr;
use ixon::modes::{
  AllMode, AllocAssert, BinderMode, DefAsserts, FieldMode, FieldModes, LetMode,
  ResultMode,
};
use ixon::proof::{
  Claim, ClaimContext, FLAG_CLAIM, Proof, RevealConstantInfo,
  RevealConstructorInfo, RevealMutConstInfo, RevealRecursorRule,
  VARIANT_CHECK_CLAIM, VARIANT_CHECK_ENV_CLAIM, VARIANT_RESOURCE_CLAIM_RETIRED,
  spec_digest,
};
use ixon::serialize::{get_expr, put_expr};
use ixon::tag::TagN;
use ixon::univ::{Univ, get_univ, put_univ};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

fn addr(label: &str) -> Address {
  Address::hash(format!("ix-parity-v5:{label}").as_bytes())
}

fn hex_encode(bytes: &[u8]) -> String {
  let mut out = String::with_capacity(bytes.len() * 2);
  for &b in bytes {
    let _ = write!(out, "{b:02x}");
  }
  out
}

fn blake3_hex(bytes: &[u8]) -> String {
  let h = blake3::hash(bytes);
  let a = Address::hash(bytes);
  assert_eq!(h.as_bytes(), a.as_bytes());
  a.hex()
}

fn json_escape(s: &str) -> String {
  let mut out = String::with_capacity(s.len() + 2);
  out.push('"');
  for ch in s.chars() {
    match ch {
      '"' => out.push_str("\\\""),
      '\\' => out.push_str("\\\\"),
      '\n' => out.push_str("\\n"),
      '\r' => out.push_str("\\r"),
      '\t' => out.push_str("\\t"),
      c if c.is_control() => {
        let _ = write!(out, "\\u{:04x}", u32::from(c));
      },
      c => out.push(c),
    }
  }
  out.push('"');
  out
}

fn repo_root() -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .and_then(Path::parent)
    .expect("workspace root")
    .to_path_buf()
}

fn put_u32_le(n: u32, buf: &mut Vec<u8>) {
  buf.extend_from_slice(&n.to_le_bytes());
}

fn put_u64_le(n: u64, buf: &mut Vec<u8>) {
  buf.extend_from_slice(&n.to_le_bytes());
}

fn put_u64_array(xs: &[u64], buf: &mut Vec<u8>) {
  put_u32_le(u32::try_from(xs.len()).unwrap(), buf);
  for &x in xs {
    put_u64_le(x, buf);
  }
}

/// Canonical `Ix.DynamicLink.Codec.serDynamicLink` (`0xE8 0x0D`, variant 21).
fn build_dynamic_link_statement(
  vk: &Address,
  entry_idx: u64,
  pub_inputs: &[u64],
  pub_outputs: &[u64],
  bridge: Option<(&Address, &Address, &Address, u64, &Address)>,
) -> Vec<u8> {
  let mut buf = Vec::new();
  TagN::put(4, FLAG_CLAIM, 21, &mut buf);
  assert_eq!(&buf[..2], &[0xE8, 0x0D]);
  buf.extend_from_slice(vk.as_bytes());
  put_u64_le(entry_idx, &mut buf);
  put_u64_array(pub_inputs, &mut buf);
  put_u64_array(pub_outputs, &mut buf);
  match bridge {
    None => buf.push(0x00),
    Some((spec, binding, target, codec, cert)) => {
      buf.push(0x01);
      buf.extend_from_slice(spec.as_bytes());
      buf.extend_from_slice(binding.as_bytes());
      buf.extend_from_slice(target.as_bytes());
      put_u64_le(codec, &mut buf);
      buf.extend_from_slice(cert.as_bytes());
    },
  }
  buf
}

/// Canonical `Ix.DynamicLink.Codec.serLinkedCircuitEntry` (`0xE8 0x0F`, variant 23).
#[allow(clippy::too_many_arguments)]
fn build_linked_circuit_entry(
  vk: &Address,
  entry_idx: u64,
  codec: u64,
  target: &Address,
  cert: &Address,
  eval_type: &Address,
  spec: &Address,
  binding: &Address,
) -> Vec<u8> {
  let mut buf = Vec::new();
  TagN::put(4, FLAG_CLAIM, 23, &mut buf);
  assert_eq!(&buf[..2], &[0xE8, 0x0F]);
  buf.extend_from_slice(vk.as_bytes());
  put_u64_le(entry_idx, &mut buf);
  put_u64_le(codec, &mut buf);
  buf.extend_from_slice(target.as_bytes());
  buf.extend_from_slice(cert.as_bytes());
  buf.extend_from_slice(eval_type.as_bytes());
  buf.extend_from_slice(spec.as_bytes());
  buf.extend_from_slice(binding.as_bytes());
  buf
}

/// Canonical `Ix.DynamicLink.Codec.serLinkedClaim` (validator 12 or 13).
#[allow(clippy::too_many_arguments)]
fn build_linked_claim(
  variant: u64,
  validator: u8,
  spec: &Address,
  binding: &Address,
  axioms: Option<&Address>,
  target: &Address,
  assumptions: Option<&Address>,
  eval_assumptions: Option<&Address>,
  linked_circuits: &Address,
) -> Vec<u8> {
  let mut buf = Vec::new();
  TagN::put(4, FLAG_CLAIM, variant, &mut buf);
  buf.push(Env::OBJECT_FORMAT);
  buf.push(validator);
  buf.extend_from_slice(spec.as_bytes());
  buf.extend_from_slice(binding.as_bytes());
  match axioms {
    None => buf.push(0x00),
    Some(a) => {
      buf.push(0x01);
      buf.extend_from_slice(a.as_bytes());
    },
  }
  buf.extend_from_slice(target.as_bytes());
  match assumptions {
    None => buf.push(0x00),
    Some(a) => {
      buf.push(0x01);
      buf.extend_from_slice(a.as_bytes());
    },
  }
  match eval_assumptions {
    None => buf.push(0x00),
    Some(a) => {
      buf.push(0x01);
      buf.extend_from_slice(a.as_bytes());
    },
  }
  buf.extend_from_slice(linked_circuits.as_bytes());
  buf
}

/// Canonical `Ix.DynamicLink.Codec.serEvalAssumption` (`0xE8 0x0E`, variant 22).
fn build_eval_assumption(
  lhs: &Address,
  rhs: &Address,
  typ: &Address,
  circuit: Option<(&Address, u64)>,
) -> Vec<u8> {
  let mut buf = Vec::new();
  TagN::put(4, FLAG_CLAIM, 22, &mut buf);
  assert_eq!(&buf[..2], &[0xE8, 0x0E]);
  buf.extend_from_slice(lhs.as_bytes());
  buf.extend_from_slice(rhs.as_bytes());
  buf.extend_from_slice(typ.as_bytes());
  match circuit {
    None => buf.push(0x00),
    Some((vk, entry_idx)) => {
      buf.push(0x01);
      buf.extend_from_slice(vk.as_bytes());
      put_u64_le(entry_idx, &mut buf);
    },
  }
  buf
}

/// Canonical `Ix.DynamicLink.Codec.serEvalAssumedClaim` (validator 10 or 11).
fn build_eval_assumed_claim(
  variant: u64,
  validator: u8,
  spec: &Address,
  binding: &Address,
  axioms: Option<&Address>,
  target: &Address,
  assumptions: Option<&Address>,
  eval_assumptions: &Address,
) -> Vec<u8> {
  let mut buf = Vec::new();
  TagN::put(4, FLAG_CLAIM, variant, &mut buf);
  buf.push(Env::OBJECT_FORMAT);
  buf.push(validator);
  buf.extend_from_slice(spec.as_bytes());
  buf.extend_from_slice(binding.as_bytes());
  match axioms {
    None => buf.push(0x00),
    Some(a) => {
      buf.push(0x01);
      buf.extend_from_slice(a.as_bytes());
    },
  }
  buf.extend_from_slice(target.as_bytes());
  match assumptions {
    None => buf.push(0x00),
    Some(a) => {
      buf.push(0x01);
      buf.extend_from_slice(a.as_bytes());
    },
  }
  buf.extend_from_slice(eval_assumptions.as_bytes());
  buf
}

fn claim_variant_name(claim: &Claim) -> &'static str {
  match claim {
    Claim::Eval { .. } => "eval",
    Claim::Check { .. } => "check",
    Claim::CheckEnv { .. } => "checkEnv",
    Claim::Reveal { .. } => "reveal",
    Claim::Contains { .. } => "contains",
    Claim::Catalog { .. } => "catalog",
    Claim::Binding { .. } => "binding",
  }
}

fn const_variant_name(info: &ConstantInfo) -> &'static str {
  match info {
    ConstantInfo::Defn(_) => "defn",
    ConstantInfo::Recr(_) => "recr",
    ConstantInfo::Axio(_) => "axio",
    ConstantInfo::Quot(_) => "quot",
    ConstantInfo::CPrj(_) => "cPrj",
    ConstantInfo::RPrj(_) => "rPrj",
    ConstantInfo::IPrj(_) => "iPrj",
    ConstantInfo::DPrj(_) => "dPrj",
    ConstantInfo::Muts(_) => "muts",
  }
}

#[test]
fn ixon_v5_cross_language_parity_vectors() {
  let spec = spec_digest();
  let binding = addr("role-binding-0");
  let lit_class = addr("literal-class-0");
  let ax0 = addr("user-axiom-0");
  let ax1 = addr("user-axiom-1");
  let ax2 = addr("user-axiom-2");
  let axioms_tree =
    AssumptionTree::canonical(&[ax0.clone(), ax1.clone(), ax2.clone()])
      .unwrap();
  let axioms_root = axioms_tree.root();
  let asm_tree =
    AssumptionTree::canonical(&[addr("asm-leaf-0"), addr("asm-leaf-1")])
      .unwrap();
  let asm_root = asm_tree.root();

  let ctx_base = ClaimContext {
    spec: spec.clone(),
    binding: binding.clone(),
    axioms: None,
    binding_assumed: false,
    literal_class: false,
  };
  let ctx_axioms = ClaimContext {
    spec: spec.clone(),
    binding: binding.clone(),
    axioms: Some(axioms_root.clone()),
    binding_assumed: false,
    literal_class: false,
  };
  let ctx_assumed_axioms = ClaimContext {
    spec: spec.clone(),
    binding: binding.clone(),
    axioms: Some(axioms_root.clone()),
    binding_assumed: true,
    literal_class: false,
  };
  let ctx_class = ClaimContext {
    spec: spec.clone(),
    binding: lit_class.clone(),
    axioms: None,
    binding_assumed: false,
    literal_class: true,
  };
  let ctx_class_axioms = ClaimContext {
    spec: spec.clone(),
    binding: lit_class,
    axioms: Some(axioms_root.clone()),
    binding_assumed: false,
    literal_class: true,
  };

  // =========================================================================
  // 1. Claims (all 7 variants + all flag/option combinations + all Reveal arms)
  // =========================================================================
  let claim_cases: Vec<(&str, Claim)> = vec![
    (
      "eval_unconditional_no_axioms",
      Claim::Eval {
        ctx: ctx_base.clone(),
        input: addr("eval-in-0"),
        output: addr("eval-out-0"),
        assumptions: None,
      },
    ),
    (
      "eval_conditional_with_axioms",
      Claim::Eval {
        ctx: ctx_axioms.clone(),
        input: addr("eval-in-1"),
        output: addr("eval-out-1"),
        assumptions: Some(asm_root.clone()),
      },
    ),
    (
      "check_standard",
      Claim::Check {
        ctx: ctx_base.clone(),
        const_addr: addr("const-0"),
        assumptions: None,
      },
    ),
    (
      "check_binding_assumed_with_axioms_and_assumptions",
      Claim::Check {
        ctx: ctx_assumed_axioms.clone(),
        const_addr: addr("const-1"),
        assumptions: Some(asm_root.clone()),
      },
    ),
    (
      "check_env_standard",
      Claim::CheckEnv {
        ctx: ctx_base.clone(),
        root: addr("env-root-0"),
        assumptions: None,
      },
    ),
    (
      "check_env_binding_assumed_with_axioms_and_assumptions",
      Claim::CheckEnv {
        ctx: ctx_assumed_axioms,
        root: addr("env-root-1"),
        assumptions: Some(asm_root.clone()),
      },
    ),
    (
      "check_env_literal_class",
      Claim::CheckEnv {
        ctx: ctx_class.clone(),
        root: addr("env-root-2"),
        assumptions: None,
      },
    ),
    (
      "check_env_literal_class_with_axioms_and_assumptions",
      Claim::CheckEnv {
        ctx: ctx_class_axioms,
        root: addr("env-root-3"),
        assumptions: Some(asm_root.clone()),
      },
    ),
    (
      "reveal_defn_full",
      Claim::Reveal {
        comm: addr("comm-defn"),
        info: RevealConstantInfo::Defn {
          kind: Some(DefKind::Definition),
          safety: Some(DefinitionSafety::Safe),
          lvls: Some(2),
          typ: Some(addr("defn-typ")),
          value: Some(addr("defn-val")),
          asserts: Some(DefAsserts {
            alloc: AllocAssert::NoAlloc,
            bounded_stack: true,
          }),
        },
        binders: Some(addr("defn-binders")),
      },
    ),
    (
      "reveal_recr",
      Claim::Reveal {
        comm: addr("comm-recr"),
        info: RevealConstantInfo::Recr {
          k: Some(true),
          is_unsafe: Some(false),
          lvls: Some(1),
          params: Some(1),
          indices: Some(0),
          motives: Some(1),
          minors: Some(2),
          typ: Some(addr("recr-typ")),
          rules: Some(vec![
            RevealRecursorRule {
              rule_idx: 0,
              fields: 0,
              rhs: addr("recr-rhs-0"),
            },
            RevealRecursorRule {
              rule_idx: 1,
              fields: 2,
              rhs: addr("recr-rhs-1"),
            },
          ]),
        },
        binders: None,
      },
    ),
    (
      "reveal_axio",
      Claim::Reveal {
        comm: addr("comm-axio"),
        info: RevealConstantInfo::Axio {
          is_unsafe: Some(false),
          lvls: Some(1),
          typ: Some(addr("axio-typ")),
        },
        binders: None,
      },
    ),
    (
      "reveal_quot",
      Claim::Reveal {
        comm: addr("comm-quot"),
        info: RevealConstantInfo::Quot {
          kind: Some(QuotKind::Lift),
          lvls: Some(2),
          typ: Some(addr("quot-typ")),
        },
        binders: None,
      },
    ),
    (
      "reveal_cprj",
      Claim::Reveal {
        comm: addr("comm-cprj"),
        info: RevealConstantInfo::CPrj {
          idx: Some(0),
          cidx: Some(1),
          block: Some(addr("muts-block")),
        },
        binders: None,
      },
    ),
    (
      "reveal_rprj",
      Claim::Reveal {
        comm: addr("comm-rprj"),
        info: RevealConstantInfo::RPrj {
          idx: Some(2),
          block: Some(addr("muts-block")),
        },
        binders: None,
      },
    ),
    (
      "reveal_iprj",
      Claim::Reveal {
        comm: addr("comm-iprj"),
        info: RevealConstantInfo::IPrj {
          idx: Some(0),
          block: Some(addr("muts-block")),
        },
        binders: None,
      },
    ),
    (
      "reveal_dprj",
      Claim::Reveal {
        comm: addr("comm-dprj"),
        info: RevealConstantInfo::DPrj {
          idx: Some(1),
          block: Some(addr("muts-block")),
        },
        binders: None,
      },
    ),
    (
      "reveal_muts_all_components",
      Claim::Reveal {
        comm: addr("comm-muts"),
        info: RevealConstantInfo::Muts {
          components: vec![
            (
              0,
              RevealMutConstInfo::Indc {
                is_unsafe: Some(false),
                lvls: Some(1),
                params: Some(1),
                indices: Some(0),
                typ: Some(addr("mut-indc-typ")),
                ctors: Some(vec![
                  (
                    0,
                    RevealConstructorInfo {
                      is_unsafe: Some(false),
                      lvls: Some(1),
                      cidx: Some(0),
                      params: Some(1),
                      fields: Some(0),
                      typ: Some(addr("mut-ctor-0")),
                      field_modes: Some(vec![]),
                    },
                  ),
                  (
                    1,
                    RevealConstructorInfo {
                      is_unsafe: Some(false),
                      lvls: Some(1),
                      cidx: Some(1),
                      params: Some(1),
                      fields: Some(2),
                      typ: Some(addr("mut-ctor-1")),
                      field_modes: Some(vec![
                        FieldMode::Inherited,
                        FieldMode::Shared,
                      ]),
                    },
                  ),
                ]),
              },
            ),
            (
              1,
              RevealMutConstInfo::Recr {
                k: Some(false),
                is_unsafe: Some(false),
                lvls: Some(1),
                params: Some(1),
                indices: Some(0),
                motives: Some(1),
                minors: Some(2),
                typ: Some(addr("mut-recr-typ")),
                rules: Some(vec![RevealRecursorRule {
                  rule_idx: 0,
                  fields: 0,
                  rhs: addr("mut-recr-rhs-0"),
                }]),
              },
            ),
            (
              2,
              RevealMutConstInfo::Defn {
                kind: Some(DefKind::Opaque),
                safety: Some(DefinitionSafety::Partial),
                lvls: Some(0),
                typ: Some(addr("mut-defn-typ")),
                value: Some(addr("mut-defn-val")),
                asserts: Some(DefAsserts {
                  alloc: AllocAssert::NoRc,
                  bounded_stack: false,
                }),
              },
            ),
          ],
        },
        binders: Some(addr("muts-binders")),
      },
    ),
    (
      "contains",
      Claim::Contains {
        tree: addr("merkle-tree-root"),
        const_addr: addr("merkle-leaf"),
      },
    ),
    ("catalog", Claim::Catalog { members: addr("catalog-members-root") }),
    (
      "binding",
      Claim::Binding { spec: spec.clone(), binding: binding.clone() },
    ),
  ];

  let mut claims_json = Vec::new();
  for (name, claim) in &claim_cases {
    let (commit_addr, bytes) = claim.commit();
    let decoded = Claim::from_bytes(&bytes)
      .unwrap_or_else(|e| panic!("claim {name} failed Claim::from_bytes: {e}"));
    assert_eq!(&decoded, claim, "claim {name} round-trip mismatch");
    let mut reencoded = Vec::new();
    decoded.put(&mut reencoded);
    assert_eq!(reencoded, bytes, "claim {name} re-encode mismatch");
    assert_eq!(commit_addr.hex(), blake3_hex(&bytes));

    let (binding_assumed, literal_class, has_axioms) = match claim.context() {
      Some(c) => (c.binding_assumed, c.literal_class, c.axioms.is_some()),
      None => (false, false, false),
    };
    let has_assumptions = matches!(
      claim,
      Claim::Eval { assumptions: Some(_), .. }
        | Claim::Check { assumptions: Some(_), .. }
        | Claim::CheckEnv { assumptions: Some(_), .. }
    );
    claims_json.push(format!(
      "    {{\"name\": {}, \"variant\": {}, \"validator\": {}, \
       \"binding_assumed\": {}, \"literal_class\": {}, \"has_axioms\": {}, \
       \"has_assumptions\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      json_escape(claim_variant_name(claim)),
      claim.validator(),
      binding_assumed,
      literal_class,
      has_axioms,
      has_assumptions,
      bytes.len(),
      json_escape(&hex_encode(&bytes)),
      json_escape(&commit_addr.hex()),
    ));
  }

  // =========================================================================
  // 2. Proofs (all 7 variants under 0xF flag)
  // =========================================================================
  let proof_cases: Vec<(&str, Proof)> = vec![
    (
      "proof_eval",
      Proof::new(claim_cases[0].1.clone(), vec![0xDE, 0xAD, 0xBE, 0xEF]),
    ),
    (
      "proof_check_assumed",
      Proof::new(claim_cases[3].1.clone(), vec![0x01, 0x02, 0x03]),
    ),
    ("proof_check_env_class", Proof::new(claim_cases[6].1.clone(), vec![])),
    ("proof_reveal", Proof::new(claim_cases[8].1.clone(), vec![0xAA; 16])),
    ("proof_contains", Proof::new(claim_cases[17].1.clone(), vec![0x55; 8])),
    ("proof_catalog", Proof::new(claim_cases[18].1.clone(), vec![0x42])),
    ("proof_binding", Proof::new(claim_cases[19].1.clone(), vec![0x77; 4])),
  ];

  let mut proofs_json = Vec::new();
  for (name, proof) in &proof_cases {
    let (commit_addr, bytes) = proof.commit();
    let mut slice = bytes.as_slice();
    let decoded = Proof::get(&mut slice)
      .unwrap_or_else(|e| panic!("proof {name} failed Proof::get: {e}"));
    assert!(slice.is_empty(), "proof {name} had trailing bytes");
    assert_eq!(&decoded, proof, "proof {name} round-trip mismatch");
    assert_eq!(commit_addr.hex(), blake3_hex(&bytes));
    proofs_json.push(format!(
      "    {{\"name\": {}, \"variant\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      json_escape(claim_variant_name(&proof.claim)),
      bytes.len(),
      json_escape(&hex_encode(&bytes)),
      json_escape(&commit_addr.hex()),
    ));
  }

  // =========================================================================
  // 3. AssumptionTree vectors
  // =========================================================================
  let tree_cases: Vec<(&str, AssumptionTree)> = vec![
    ("leaf", AssumptionTree::Leaf(ax0.clone())),
    ("padding", AssumptionTree::Padding),
    ("canonical_2", asm_tree.clone()),
    ("canonical_3_padded", axioms_tree.clone()),
    (
      "joined_freeform",
      AssumptionTree::join(
        AssumptionTree::Leaf(ax2.clone()),
        AssumptionTree::join(
          AssumptionTree::Leaf(ax0.clone()),
          AssumptionTree::Padding,
        ),
      ),
    ),
  ];

  let mut trees_json = Vec::new();
  for (name, tree) in &tree_cases {
    let bytes = tree.ser();
    let mut slice = bytes.as_slice();
    let decoded = AssumptionTree::get(&mut slice).unwrap_or_else(|e| {
      panic!("tree {name} failed AssumptionTree::get: {e}")
    });
    assert!(slice.is_empty(), "tree {name} had trailing bytes");
    assert_eq!(&decoded, tree, "tree {name} round-trip mismatch");
    assert_eq!(decoded.root(), tree.root());
    trees_json.push(format!(
      "    {{\"name\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}, \"root_blake3\": {}}}",
      json_escape(name),
      bytes.len(),
      json_escape(&hex_encode(&bytes)),
      json_escape(&blake3_hex(&bytes)),
      json_escape(&tree.root().hex()),
    ));
  }

  // =========================================================================
  // 4. Comm vectors (untagged + 0xE1 tagged)
  // =========================================================================
  let comm_cases: Vec<(&str, Comm)> = vec![
    ("comm_0", Comm::new(addr("comm-secret-0"), addr("comm-payload-0"))),
    ("comm_1", Comm::new(addr("comm-secret-1"), addr("comm-payload-1"))),
  ];

  let mut comms_json = Vec::new();
  for (name, comm) in &comm_cases {
    let mut untagged = Vec::new();
    comm.put(&mut untagged);
    let mut s = untagged.as_slice();
    assert_eq!(Comm::get(&mut s).unwrap(), *comm);
    assert!(s.is_empty());

    let mut tagged = Vec::new();
    comm.put_tagged(&mut tagged);
    assert_eq!(tagged[0], 0xE1);
    let mut ts = tagged.as_slice();
    assert_eq!(Comm::get_tagged(&mut ts).unwrap(), *comm);
    assert!(ts.is_empty());

    let commit = comm.commit();
    assert_eq!(commit.hex(), blake3_hex(&tagged));
    comms_json.push(format!(
      "    {{\"name\": {}, \"secret\": {}, \"payload\": {}, \"untagged_hex\": {}, \
       \"tagged_hex\": {}, \"untagged_blake3\": {}, \"commit_blake3\": {}}}",
      json_escape(name),
      json_escape(&comm.secret.hex()),
      json_escape(&comm.payload.hex()),
      json_escape(&hex_encode(&untagged)),
      json_escape(&hex_encode(&tagged)),
      json_escape(&blake3_hex(&untagged)),
      json_escape(&commit.hex()),
    ));
  }

  // =========================================================================
  // 5. Univ vectors (all 5 constructors + Succ telescope)
  // =========================================================================
  let univ_cases: Vec<(&str, Arc<Univ>)> = vec![
    ("zero", Univ::zero()),
    ("succ_1", Univ::succ(Univ::zero())),
    ("succ_3_var_0", Univ::succ(Univ::succ(Univ::succ(Univ::var(0))))),
    ("var_0", Univ::var(0)),
    ("var_large", Univ::var(300)),
    ("max", Univ::max(Univ::var(0), Univ::succ(Univ::var(1)))),
    ("imax", Univ::imax(Univ::succ(Univ::zero()), Univ::var(2))),
  ];

  let mut univs_json = Vec::new();
  for (name, univ) in &univ_cases {
    let mut bytes = Vec::new();
    put_univ(univ, &mut bytes);
    let mut slice = bytes.as_slice();
    let decoded = get_univ(&mut slice)
      .unwrap_or_else(|e| panic!("univ {name} failed get_univ: {e}"));
    assert!(slice.is_empty(), "univ {name} had trailing bytes");
    assert_eq!(&decoded, univ, "univ {name} round-trip mismatch");
    univs_json.push(format!(
      "    {{\"name\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      bytes.len(),
      json_escape(&hex_encode(&bytes)),
      json_escape(&blake3_hex(&bytes)),
    ));
  }

  // =========================================================================
  // 6. Expr vectors (all 12 constructors + telescopes + LetMode variants)
  // =========================================================================
  let expr_cases: Vec<(&str, &str, Arc<Expr>)> = vec![
    ("sort_0", "sort", Expr::sort(0)),
    ("sort_42", "sort", Expr::sort(42)),
    ("var_0", "var", Expr::var(0)),
    ("var_300", "var", Expr::var(300)),
    ("ref_no_univs", "ref", Expr::reference(0, vec![])),
    ("ref_with_univs", "ref", Expr::reference(2, vec![0, 1, 3])),
    ("rec_no_univs", "rec", Expr::rec(0, vec![])),
    ("rec_with_univs", "rec", Expr::rec(1, vec![2, 0])),
    ("prj", "prj", Expr::prj(0, 2, Expr::var(0))),
    ("str", "str", Expr::str(5)),
    ("nat", "nat", Expr::nat(7)),
    ("app_single", "app", Expr::app(Expr::var(0), Expr::var(1))),
    (
      "app_telescope_3",
      "app",
      Expr::app(
        Expr::app(
          Expr::app(Expr::reference(0, vec![0]), Expr::var(2)),
          Expr::var(1),
        ),
        Expr::var(0),
      ),
    ),
    ("lam_single", "lam", Expr::lam(Expr::sort(0), Expr::var(0))),
    (
      "lam_telescope_3",
      "lam",
      Expr::lam(
        Expr::sort(0),
        Expr::lam(Expr::var(0), Expr::lam(Expr::var(1), Expr::var(0))),
      ),
    ),
    ("all_single", "all", Expr::all(Expr::sort(0), Expr::var(0))),
    (
      "all_telescope_3",
      "all",
      Expr::all(
        Expr::sort(0),
        Expr::all(Expr::var(0), Expr::all(Expr::var(1), Expr::sort(1))),
      ),
    ),
    (
      "let_dep_default",
      "let",
      Expr::let_(false, Expr::sort(0), Expr::var(1), Expr::var(0)),
    ),
    (
      "let_nondep_unique",
      "let",
      Expr::let_mode(
        true,
        LetMode::Value(BinderMode::Unique),
        Expr::sort(0),
        Expr::var(1),
        Expr::var(0),
      ),
    ),
    (
      "let_dep_borrow",
      "let",
      Expr::let_mode(
        false,
        LetMode::Borrow,
        Expr::sort(0),
        Expr::var(1),
        Expr::var(0),
      ),
    ),
    ("share_0", "share", Expr::share(0)),
    ("share_12", "share", Expr::share(12)),
  ];

  let mut exprs_json = Vec::new();
  for (name, ctor, expr) in &expr_cases {
    let mut bytes = Vec::new();
    put_expr(expr, &mut bytes);
    let mut slice = bytes.as_slice();
    let decoded = get_expr(&mut slice)
      .unwrap_or_else(|e| panic!("expr {name} failed get_expr: {e}"));
    assert!(slice.is_empty(), "expr {name} had trailing bytes");
    assert_eq!(&decoded, expr, "expr {name} round-trip mismatch");
    let mut reencoded = Vec::new();
    put_expr(&decoded, &mut reencoded);
    assert_eq!(reencoded, bytes, "expr {name} re-encode mismatch");
    exprs_json.push(format!(
      "    {{\"name\": {}, \"ctor\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      json_escape(ctor),
      bytes.len(),
      json_escape(&hex_encode(&bytes)),
      json_escape(&blake3_hex(&bytes)),
    ));
  }

  // =========================================================================
  // 7. Constant vectors (all 9 ConstantInfo variants, canonical + complete binders)
  // =========================================================================
  let shared_lam = Expr::lam(Expr::sort(0), Expr::var(0));
  let const_defn_safe = Constant::with_tables(
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      asserts: DefAsserts { alloc: AllocAssert::NoAlloc, bounded_stack: true },
      lvls: 2,
      // Root 0: All(Sort(0), All(Var(0), Var(1))) -> 2 All binders
      typ: Expr::all(Expr::sort(0), Expr::all(Expr::var(0), Expr::var(1))),
      // Root 1: Lam(Sort(0), Share(0)) -> 1 Lam + 1 Share(0)
      value: Expr::lam(Expr::sort(0), Expr::share(0)),
    }),
    vec![shared_lam],
    vec![addr("ref-0")],
    vec![Univ::zero(), Univ::var(0), Univ::succ(Univ::var(1))],
  )
  .with_binders(vec![
    // Root 0 (typ): 2 binders
    BinderBlock {
      shared: false,
      index: 0,
      variant: 0,
      nodes: vec![
        BinderNode::Never(AllMode::default()),
        BinderNode::IfAllZero(
          vec![0, 1],
          AllMode::new(BinderMode::Borrowed, ResultMode::Unique),
        ),
      ],
    },
    // Root 1 (value): Lam + Share(0)
    BinderBlock {
      shared: false,
      index: 1,
      variant: 0,
      nodes: vec![
        BinderNode::Zero(AllMode::new(BinderMode::Once, ResultMode::Shared)),
        BinderNode::Share(0),
      ],
    },
    // Shared entry 0, variant 0: 1 Lam binder
    BinderBlock {
      shared: true,
      index: 0,
      variant: 0,
      nodes: vec![BinderNode::Never(AllMode::default())],
    },
  ]);

  let const_defn_opaque_partial = Constant::with_tables(
    ConstantInfo::Defn(Definition {
      kind: DefKind::Opaque,
      safety: DefinitionSafety::Partial,
      asserts: DefAsserts { alloc: AllocAssert::NoRc, bounded_stack: false },
      lvls: 0,
      typ: Expr::all(Expr::sort(0), Expr::sort(0)),
      value: Expr::lam(Expr::sort(0), Expr::var(0)),
    }),
    vec![],
    vec![],
    vec![Univ::zero()],
  )
  .with_binders(vec![
    BinderBlock {
      shared: false,
      index: 0,
      variant: 0,
      nodes: vec![BinderNode::Undecided(AllMode::default())],
    },
    BinderBlock {
      shared: false,
      index: 1,
      variant: 0,
      nodes: vec![BinderNode::Undecided(AllMode::default())],
    },
  ]);

  let const_defn_theorem = Constant::with_tables(
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      asserts: DefAsserts::default(),
      lvls: 0,
      typ: Expr::sort(0),
      value: Expr::reference(0, vec![]),
    }),
    vec![],
    vec![addr("thm-proof-ref")],
    vec![Univ::zero()],
  );

  let const_recr = Constant::with_tables(
    ConstantInfo::Recr(Recursor {
      k: true,
      is_unsafe: false,
      lvls: 1,
      params: 1,
      indices: 0,
      motives: 1,
      minors: 2,
      typ: Expr::all(Expr::sort(0), Expr::sort(1)),
      rules: vec![
        RecursorRule { fields: 0, rhs: Expr::var(0) },
        RecursorRule { fields: 2, rhs: Expr::lam(Expr::sort(0), Expr::var(0)) },
      ],
    }),
    vec![],
    vec![],
    vec![Univ::zero(), Univ::var(0)],
  )
  .with_binders(vec![
    // Root 0 (typ): 1 All
    BinderBlock {
      shared: false,
      index: 0,
      variant: 0,
      nodes: vec![BinderNode::Never(AllMode::default())],
    },
    // Root 2 (rules[1].rhs): 1 Lam (Root 1 = rules[0].rhs has no binders)
    BinderBlock {
      shared: false,
      index: 2,
      variant: 0,
      nodes: vec![BinderNode::Zero(AllMode::default())],
    },
  ]);

  let const_axio = Constant::with_tables(
    ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 1,
      typ: Expr::all(Expr::sort(0), Expr::var(0)),
    }),
    vec![],
    vec![],
    vec![Univ::var(0)],
  )
  .with_binders(vec![BinderBlock {
    shared: false,
    index: 0,
    variant: 0,
    nodes: vec![BinderNode::IfAllZero(vec![0], AllMode::default())],
  }]);

  let const_quot = Constant::with_tables(
    ConstantInfo::Quot(Quotient {
      kind: QuotKind::Lift,
      lvls: 2,
      typ: Expr::sort(0),
    }),
    vec![],
    vec![],
    vec![Univ::succ(Univ::max(Univ::var(0), Univ::var(1)))],
  );

  let block_addr = addr("muts-block-target");
  let const_cprj = Constant::new(ConstantInfo::CPrj(ConstructorProj {
    idx: 0,
    cidx: 1,
    block: block_addr.clone(),
  }));
  let const_rprj = Constant::new(ConstantInfo::RPrj(RecursorProj {
    idx: 1,
    block: block_addr.clone(),
  }));
  let const_iprj = Constant::new(ConstantInfo::IPrj(InductiveProj {
    idx: 0,
    block: block_addr.clone(),
  }));
  let const_dprj = Constant::new(ConstantInfo::DPrj(DefinitionProj {
    idx: 2,
    block: block_addr,
  }));

  let const_muts = Constant::with_tables(
    ConstantInfo::Muts(vec![
      MutConst::Indc(Inductive {
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        typ: Expr::all(Expr::sort(0), Expr::sort(1)),
        ctors: vec![
          Constructor {
            is_unsafe: false,
            lvls: 1,
            cidx: 0,
            params: 1,
            fields: 0,
            field_modes: FieldModes::Inherited,
            typ: Expr::rec(0, vec![0]),
          },
          Constructor {
            is_unsafe: false,
            lvls: 1,
            cidx: 1,
            params: 1,
            fields: 2,
            field_modes: FieldModes::listed(
              vec![FieldMode::Inherited, FieldMode::Shared],
              2,
            )
            .unwrap(),
            typ: Expr::all(Expr::sort(0), Expr::rec(0, vec![0])),
          },
        ],
      }),
      MutConst::Recr(Recursor {
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 2,
        typ: Expr::sort(1),
        rules: vec![RecursorRule { fields: 0, rhs: Expr::var(0) }],
      }),
      MutConst::Defn(Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        asserts: DefAsserts::default(),
        lvls: 1,
        typ: Expr::rec(0, vec![0]),
        value: Expr::reference(0, vec![0]),
      }),
    ]),
    vec![],
    vec![addr("muts-ext-ref-0")],
    vec![Univ::zero(), Univ::succ(Univ::var(0))],
  )
  .with_binders(vec![
    // Root 0 = indc.typ (1 All)
    BinderBlock {
      shared: false,
      index: 0,
      variant: 0,
      nodes: vec![BinderNode::Never(AllMode::default())],
    },
    // Root 2 = indc.ctors[1].typ (1 All); Root 1 (ctor 0) has no binders
    BinderBlock {
      shared: false,
      index: 2,
      variant: 0,
      nodes: vec![BinderNode::Never(AllMode::default())],
    },
  ]);

  let constant_cases: Vec<(&str, Constant)> = vec![
    ("defn_safe_binders_asserts", const_defn_safe),
    ("defn_opaque_partial", const_defn_opaque_partial),
    ("defn_theorem", const_defn_theorem),
    ("recr", const_recr),
    ("axio", const_axio),
    ("quot", const_quot),
    ("cprj", const_cprj),
    ("rprj", const_rprj),
    ("iprj", const_iprj),
    ("dprj", const_dprj),
    ("muts", const_muts),
  ];

  let mut constants_json = Vec::new();
  for (name, constant) in &constant_cases {
    assert!(
      constant.binders_canonical(),
      "constant {name} binders not canonical"
    );
    assert!(
      constant.binders_complete(),
      "constant {name} binders not complete"
    );
    assert!(constant.modes_canonical(), "constant {name} modes not canonical");

    let (commit_addr, bytes) = constant.commit();
    let decoded = Constant::get_canonical(&bytes)
      .unwrap_or_else(|e| panic!("constant {name} failed get_canonical: {e}"));
    assert_eq!(&decoded, constant, "constant {name} round-trip mismatch");
    assert_eq!(commit_addr.hex(), blake3_hex(&bytes));
    constants_json.push(format!(
      "    {{\"name\": {}, \"variant\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      json_escape(const_variant_name(&constant.info)),
      bytes.len(),
      json_escape(&hex_encode(&bytes)),
      json_escape(&commit_addr.hex()),
    ));
  }

  // =========================================================================
  // 8. Raw BLAKE3 boundary vectors
  // =========================================================================
  let b64: Vec<u8> = (0u8..64).collect();
  let b65: Vec<u8> = (0u8..65).collect();
  let b1024: Vec<u8> =
    (0usize..1024).map(|i| u8::try_from(i % 251).unwrap()).collect();
  let b1025: Vec<u8> =
    (0usize..1025).map(|i| u8::try_from(i % 251).unwrap()).collect();
  let blake3_cases: Vec<(&str, &[u8])> = vec![
    ("empty", b""),
    ("abc", b"abc"),
    ("block_64", &b64),
    ("cross_block_65", &b65),
    ("chunk_1024", &b1024),
    ("cross_chunk_1025", &b1025),
  ];

  let mut blake3_json = Vec::new();
  for (name, input) in &blake3_cases {
    blake3_json.push(format!(
      "    {{\"name\": {}, \"byte_len\": {}, \"input_hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      input.len(),
      json_escape(&hex_encode(input)),
      json_escape(&blake3_hex(input)),
    ));
  }

  // =========================================================================
  // 9. DynamicLink & negative Claim::de controls
  // =========================================================================
  let dl_vk = addr("dl-vk-0");
  let dl_target = addr("dl-target-const");
  let dl_cert = addr("dl-cert-const");
  let ea_lhs = addr("ea-lhs");
  let ea_rhs = addr("ea-rhs");
  let ea_typ = addr("ea-typ");
  let eval_asmp_root = addr("eval-assumptions-root");

  let dl_stmt_no_bridge =
    build_dynamic_link_statement(&dl_vk, 7, &[1, 2, 3], &[42], None);
  let dl_stmt_with_bridge = build_dynamic_link_statement(
    &dl_vk,
    7,
    &[1, 2],
    &[3, 4],
    Some((&spec, &binding, &dl_target, 1, &dl_cert)),
  );
  let linked_circuits_root = addr("linked-circuits-root");
  let linked_circuit_entry = build_linked_circuit_entry(
    &dl_vk, 7, 1, &dl_target, &dl_cert, &ea_typ, &spec, &binding,
  );
  let linked_check_v12 = build_linked_claim(
    VARIANT_CHECK_CLAIM,
    12,
    &spec,
    &binding,
    None,
    &addr("const-lc-0"),
    None,
    None,
    &linked_circuits_root,
  );
  let binding_linked_check_env_v13 = build_linked_claim(
    VARIANT_CHECK_ENV_CLAIM,
    13,
    &spec,
    &binding,
    Some(&axioms_root),
    &addr("env-lc-1"),
    Some(&asm_root),
    Some(&eval_asmp_root),
    &linked_circuits_root,
  );
  // Adversarial address starting with `[OBJECT_FORMAT (0x04), VALIDATOR_ERASED_LEAN (0x03)]`
  // so `get_scope` succeeds and rejection is proven at `get_payload` for variants 21 & 22!
  let mut scope_prefix_bytes = [0x11u8; 32];
  scope_prefix_bytes[0] = Env::OBJECT_FORMAT;
  scope_prefix_bytes[1] = 3;
  let scope_prefix_addr = Address::from_slice(&scope_prefix_bytes).unwrap();
  let dl_stmt_scope_prefix =
    build_dynamic_link_statement(&scope_prefix_addr, 0, &[], &[], None);
  let eval_asmp_no_circuit =
    build_eval_assumption(&ea_lhs, &ea_rhs, &ea_typ, None);
  let eval_asmp_with_circuit =
    build_eval_assumption(&ea_lhs, &ea_rhs, &ea_typ, Some((&dl_vk, 3)));
  let eval_asmp_scope_prefix =
    build_eval_assumption(&scope_prefix_addr, &ea_rhs, &ea_typ, None);
  let eval_assumed_check_v10 = build_eval_assumed_claim(
    VARIANT_CHECK_CLAIM,
    10,
    &spec,
    &binding,
    None,
    &addr("const-ea-0"),
    None,
    &eval_asmp_root,
  );
  let eval_assumed_check_env_v10 = build_eval_assumed_claim(
    VARIANT_CHECK_ENV_CLAIM,
    10,
    &spec,
    &binding,
    Some(&axioms_root),
    &addr("env-ea-0"),
    Some(&asm_root),
    &eval_asmp_root,
  );
  let binding_eval_assumed_check_v11 = build_eval_assumed_claim(
    VARIANT_CHECK_CLAIM,
    11,
    &spec,
    &binding,
    None,
    &addr("const-ea-1"),
    Some(&asm_root),
    &eval_asmp_root,
  );
  let binding_eval_assumed_check_env_v11 = build_eval_assumed_claim(
    VARIANT_CHECK_ENV_CLAIM,
    11,
    &spec,
    &binding,
    Some(&axioms_root),
    &addr("env-ea-1"),
    None,
    &eval_asmp_root,
  );

  let mut retired_resource = Vec::new();
  TagN::put(
    4,
    FLAG_CLAIM,
    VARIANT_RESOURCE_CLAIM_RETIRED,
    &mut retired_resource,
  );
  assert_eq!(&retired_resource[..2], &[0xE8, 0x01]);
  retired_resource.extend_from_slice(&[Env::OBJECT_FORMAT, 2]);
  retired_resource.extend_from_slice(addr("res-target").as_bytes());

  let make_bad_validator_check = |validator: u8| -> Vec<u8> {
    let mut b = Vec::new();
    TagN::put(4, FLAG_CLAIM, VARIANT_CHECK_CLAIM, &mut b);
    b.push(Env::OBJECT_FORMAT);
    b.push(validator);
    ctx_base.put(&mut b);
    b.extend_from_slice(addr("bad-val-const").as_bytes());
    b.push(0x00);
    b
  };

  let negative_cases: Vec<(&str, &str, &str, Vec<u8>)> = vec![
    (
      "dynamic_link_tag_21_0xE80D_no_bridge",
      "DynamicLinkStatement (tag 0xE8 0x0D / variant 21) must be rejected by Claim.de",
      "dynamic_link",
      dl_stmt_no_bridge,
    ),
    (
      "dynamic_link_tag_21_0xE80D_with_bridge",
      "DynamicLinkStatement with bridge (tag 0xE8 0x0D / variant 21) must be rejected by Claim.de",
      "dynamic_link",
      dl_stmt_with_bridge,
    ),
    (
      "dynamic_link_tag_21_0xE80D_scope_prefix_0403",
      "DynamicLinkStatement (tag 0xE8 0x0D / variant 21) with 0x0403 prefix must still be rejected at get_payload",
      "dynamic_link",
      dl_stmt_scope_prefix,
    ),
    (
      "eval_assumption_tag_22_0xE80E_no_circuit",
      "EvalAssumption leaf (tag 0xE8 0x0E / variant 22) must be rejected by Claim.de",
      "eval_assumption",
      eval_asmp_no_circuit,
    ),
    (
      "eval_assumption_tag_22_0xE80E_with_circuit",
      "EvalAssumption leaf with circuit (tag 0xE8 0x0E / variant 22) must be rejected by Claim.de",
      "eval_assumption",
      eval_asmp_with_circuit,
    ),
    (
      "eval_assumption_tag_22_0xE80E_scope_prefix_0403",
      "EvalAssumption leaf (tag 0xE8 0x0E / variant 22) with 0x0403 prefix must still be rejected at get_payload",
      "eval_assumption",
      eval_asmp_scope_prefix,
    ),
    (
      "eval_assumed_check_validator_10",
      "EvalAssumedClaim check (validator 10) must be rejected by Claim.de",
      "eval_assumed_claim",
      eval_assumed_check_v10,
    ),
    (
      "eval_assumed_check_env_validator_10",
      "EvalAssumedClaim checkEnv (validator 10) must be rejected by Claim.de",
      "eval_assumed_claim",
      eval_assumed_check_env_v10,
    ),
    (
      "binding_eval_assumed_check_validator_11",
      "EvalAssumedClaim check (validator 11) must be rejected by Claim.de",
      "eval_assumed_claim",
      binding_eval_assumed_check_v11,
    ),
    (
      "binding_eval_assumed_check_env_validator_11",
      "EvalAssumedClaim checkEnv (validator 11) must be rejected by Claim.de",
      "eval_assumed_claim",
      binding_eval_assumed_check_env_v11,
    ),
    (
      "linked_circuit_entry_tag_23_0xE80F",
      "LinkedCircuitEntry leaf (tag 0xE8 0x0F / variant 23) must be rejected by Claim.de",
      "linked_circuit_entry",
      linked_circuit_entry,
    ),
    (
      "linked_check_validator_12",
      "LinkedClaim check (validator 12) must be rejected by Claim.de",
      "linked_claim",
      linked_check_v12,
    ),
    (
      "binding_linked_check_env_validator_13",
      "LinkedClaim checkEnv (validator 13) must be rejected by Claim.de",
      "linked_claim",
      binding_linked_check_env_v13,
    ),
    (
      "retired_resource_claim_0xE801",
      "Retired resource claim (tag 0xE8 0x01 / variant 9) must be rejected",
      "none",
      retired_resource,
    ),
    (
      "retired_validator_1_erased_lean_v1",
      "Retired validator 1 must be rejected",
      "none",
      make_bad_validator_check(1),
    ),
    (
      "retired_validator_2_resource_v1",
      "Retired validator 2 must be rejected",
      "none",
      make_bad_validator_check(2),
    ),
    (
      "reserved_validator_6_compile_v1",
      "Reserved validator 6 must be rejected",
      "none",
      make_bad_validator_check(6),
    ),
    (
      "reserved_validator_7_compile_v2",
      "Reserved validator 7 must be rejected",
      "none",
      make_bad_validator_check(7),
    ),
    (
      "reserved_validator_8_modes",
      "Reserved validator 8 must be rejected",
      "none",
      make_bad_validator_check(8),
    ),
    (
      "reserved_validator_9_compile_v3",
      "Reserved validator 9 must be rejected",
      "none",
      make_bad_validator_check(9),
    ),
  ];

  let mut negative_json = Vec::new();
  for (name, reason, dl_kind, bytes) in &negative_cases {
    let err = Claim::from_bytes(bytes).expect_err(&format!(
      "negative claim control {name} was unexpectedly accepted by Claim::from_bytes!"
    ));
    negative_json.push(format!(
      "    {{\"name\": {}, \"reason\": {}, \"dynamic_link_kind\": {}, \
       \"rust_error\": {}, \"byte_len\": {}, \"hex\": {}, \"blake3\": {}}}",
      json_escape(name),
      json_escape(reason),
      json_escape(dl_kind),
      json_escape(&err),
      bytes.len(),
      json_escape(&hex_encode(bytes)),
      json_escape(&blake3_hex(bytes)),
    ));
  }

  // =========================================================================
  // Assemble deterministic JSON and write / compare fixture file
  // =========================================================================
  let json = format!(
    "{{\n\
       \"schema_version\": 1,\n\
       \"object_format\": {},\n\
       \"spec_digest\": {},\n\
       \"claims\": [\n{}\n  ],\n\
       \"proofs\": [\n{}\n  ],\n\
       \"assumption_trees\": [\n{}\n  ],\n\
       \"comms\": [\n{}\n  ],\n\
       \"univs\": [\n{}\n  ],\n\
       \"exprs\": [\n{}\n  ],\n\
       \"constants\": [\n{}\n  ],\n\
       \"blake3\": [\n{}\n  ],\n\
       \"negative_claims\": [\n{}\n  ]\n\
     }}\n",
    Env::OBJECT_FORMAT,
    json_escape(&spec.hex()),
    claims_json.join(",\n"),
    proofs_json.join(",\n"),
    trees_json.join(",\n"),
    comms_json.join(",\n"),
    univs_json.join(",\n"),
    exprs_json.join(",\n"),
    constants_json.join(",\n"),
    blake3_json.join(",\n"),
    negative_json.join(",\n"),
  );

  let out_path = repo_root().join("Tests/Fixtures/IxonParity/vectors.json");
  let regen = std::env::var_os("IX_REGEN_FIXTURES").is_some();
  if !regen && out_path.exists() {
    let existing =
      std::fs::read_to_string(&out_path).expect("read existing vectors.json");
    assert_eq!(
      existing,
      json,
      "fixture {} drifted from deterministic Rust output (re-run with IX_REGEN_FIXTURES=1 to update)",
      out_path.display()
    );
  } else {
    std::fs::create_dir_all(out_path.parent().unwrap())
      .expect("create IxonParity dir");
    std::fs::write(&out_path, &json).expect("write vectors.json");
  }
}
