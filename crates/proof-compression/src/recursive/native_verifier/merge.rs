//! Recursive certificates verified in one circuit and joined into one: each
//! child's outer KZG proof is checked except for its final pairing, the
//! children's claims are opened and combined, and every pending pairing (each
//! child's outer opening and the deferred pair it inherited) is folded into
//! one deferred pair.
//!
//! A child statement is eighteen words: a ten-word prefix, then the packed
//! BLAKE3 digest of its claim. Its outer proof's public values are that
//! statement followed by its deferred pair's four limbs. Every claim is
//! `checkEnv(root, assumptions)`, encoded as the fixed header, the root, and
//! the assumptions option.
//!
//! Merge circuits form a family of verifying keys that verify each other.
//! A circuit cannot contain its own key, so a merge statement's prefix is two
//! constant words followed by the packed family digest, a public input: the
//! BLAKE3 digest of the family members' key digests. A family child is
//! verified under fixed commitments supplied with the request, whose key
//! digest must be one of the family's, and its statement must carry the same
//! family digest as its parent's. The verifier of the outermost certificate
//! checks that digest against the family it trusts. Every other part of a
//! family member's verifier (its heights, its parameters and its lowered
//! constraints, which this lowering shares across circuits) is fixed in the
//! circuit and must be the same for every member.
use super::*;
#[cfg(test)]
use ark_ec::CurveGroup;
use multi_stark::plonkish::gadgets::blake3;
use std::ops::Range;

const MERGE_VERSION: &[u8] = b"ix-kzg-merge/bn254/frontend/v2";
/// Domain separator of the transcript the fold weights are sampled from.
const FOLD_SEED: &[u8] = b"ix-kzg-merge/bn254/fold/v1";
const KEY_DOMAIN: &[u8] = b"ix-kzg-merge/bn254/key/v1";
const FAMILY_DOMAIN: &[u8] = b"ix-kzg-merge/bn254/family/v1";
pub(crate) const PREFIX_WORDS: usize = 10;
/// The constant words of a merge statement's prefix, before the family digest.
pub(crate) const HEAD_WORDS: usize = PREFIX_WORDS - 8;
pub(crate) const STATEMENT_WORDS: usize = PREFIX_WORDS + 8;
pub(crate) const CHILD_PUBLIC_VALUES: usize =
  STATEMENT_WORDS + pairing::PUBLIC_VALUES;

/// How a child's verifying key is bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildKey {
  /// The plan's key, fixed in the circuit, with a constant statement prefix.
  Fixed([u64; PREFIX_WORDS]),
  /// A member of this circuit's family: the fixed commitments are request
  /// inputs of the plan key's shape, and the statement prefix is the merge
  /// head and the parent's family digest.
  Family,
}

/// What a child's kind fixes: the verifier its outer proof is checked
/// against, how its key is bound, and the G2 keys its inherited deferred
/// pair is checked against.
pub(crate) struct ChildPlan<'a> {
  pub plan: Plan<'a>,
  pub key: ChildKey,
  pub inherited_keys: [G2Affine; 2],
}

/// How the output claim follows from the children's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Output {
  /// Two children whose `checkEnv` claims, under `claim_header`, join into
  /// the Merkle node of their roots.
  Join { claim_header: Vec<u8> },
  /// One child whose claim is passed through unchanged.
  Relay,
}

impl Output {
  fn children(&self) -> usize {
    match self {
      Self::Join { .. } => 2,
      Self::Relay => 1,
    }
  }
}

/// The merge rule's constants: the output rule, the merge statement's
/// constant head, the number of keys in the family, and the computation
/// height the circuit is padded to, so that every family member shares it.
pub(crate) struct MergeRule {
  pub output: Output,
  pub head: [u64; HEAD_WORDS],
  pub family_size: usize,
  pub height: usize,
}

/// The private claim opening: both roots and whether the right claim assumes
/// the left root. The left claim is always closed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ClaimOpening {
  pub left_root: [u8; 32],
  pub right_root: [u8; 32],
  pub right_conditional: bool,
}

/// The private claim data of one request, matching the rule's output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClaimWitness {
  Join(ClaimOpening),
  /// The relayed claim's BLAKE3 digest.
  Relay([u8; 32]),
}

/// One child certificate: its outer proof, the public values it was proved
/// with (its statement followed by its deferred pair's limbs), and for a
/// family child the fixed commitments of the key it was proved under.
pub(crate) struct ChildRequest<'p> {
  pub proof: &'p Proof<KzgConfig>,
  pub public: &'p [Scalar],
  pub key: Option<&'p KzgCommitment>,
}

/// One merge request: its children, claim data, and the family's key
/// digests in family order.
pub(crate) struct MergeRequest<'p> {
  pub children: &'p [ChildRequest<'p>],
  pub claims: ClaimWitness,
  pub family: &'p [[u8; 32]],
}

pub(crate) struct MergePlan<'a> {
  children: Vec<ChildPlan<'a>>,
  rule: MergeRule,
  keys: [G2Affine; 2],
  identity: [u8; 32],
}

struct ChildBindings {
  points: Range<usize>,
  scalars: Range<usize>,
  selectors: Vec<Value>,
}

/// A merge circuit compiled once, with what binds one request to it.
pub(crate) struct MergeCompiled {
  pub circuit: Circuit<Scalar>,
  identity: [u8; 32],
  children: Vec<ChildBindings>,
  points: Vec<PointBinding>,
  scalars: Vec<(Value, ScalarSource)>,
  claim_inputs: Vec<Value>,
  family_inputs: Vec<Value>,
  pairing_outputs: Vec<PointInput>,
  pairing_keys: Vec<G2Affine>,
  msm_terms: Vec<usize>,
  #[cfg(test)]
  terms: Vec<Vec<(usize, Value)>>,
}

/// The digest binding a verifying key's fixed commitments, in row order.
pub(crate) fn key_digest(fixed: &KzgCommitment) -> Result<[u8; 32], String> {
  let mut hash = ::blake3::Hasher::new();
  hash.update(KEY_DOMAIN);
  for point in fixed.0.iter().flatten() {
    let mut encoded = vec![];
    point.serialize_compressed(&mut encoded).map_err(|e| e.to_string())?;
    hash.update(&encoded);
  }
  Ok(*hash.finalize().as_bytes())
}

/// The digest of a family of key digests, in family order.
pub(crate) fn family_digest(keys: &[[u8; 32]]) -> [u8; 32] {
  let mut hash = ::blake3::Hasher::new();
  hash.update(FAMILY_DOMAIN);
  for key in keys {
    hash.update(key);
  }
  *hash.finalize().as_bytes()
}

impl<'a> MergePlan<'a> {
  /// Folding needs every pending pairing to share G2 keys: every child's
  /// outer verifier and the keys of the pairs they inherit.
  pub(crate) fn new(
    children: Vec<ChildPlan<'a>>,
    rule: MergeRule,
  ) -> Result<Self, String> {
    if children.len() != rule.output.children() {
      return Err("child count differs from the merge rule".into());
    }
    if rule.family_size == 0 {
      return Err("empty merge family".into());
    }
    if let Output::Join { claim_header } = &rule.output
      && claim_header.is_empty()
    {
      return Err("empty claim header".into());
    }
    let locations: Vec<_> =
      (1..=CHILD_PUBLIC_VALUES).map(|row| (row, 3)).collect();
    let keys = [children[0].plan.vk.g2, children[0].plan.vk.tau_g2];
    for child in &children {
      if child.plan.claims.public_locations != locations
        || child.plan.claims.rows.len() != CHILD_PUBLIC_VALUES + 1
      {
        return Err("merge child must expose a recursive statement".into());
      }
      if [child.plan.vk.g2, child.plan.vk.tau_g2] != keys
        || child.inherited_keys != keys
      {
        return Err(
          "merge children do not share one pairing basis; their pairings \
           cannot be folded"
            .into(),
        );
      }
    }
    let identity = merge_identity(&children, &rule)?;
    Ok(Self { children, rule, keys, identity })
  }

  pub(crate) fn identity(&self) -> [u8; 32] {
    self.identity
  }

  pub(crate) fn compile(&self) -> Result<MergeCompiled, String> {
    let compiled = construct_merge(self, Builder::new(), true)?;
    for child in &self.children {
      child.plan.layout.admit(&compiled.circuit)?;
    }
    Ok(compiled)
  }

  /// The computation and merged-table heights the circuit lowers to before
  /// padding.
  pub(crate) fn natural_heights(&self) -> Result<[usize; 2], String> {
    let circuit = construct_merge(self, Builder::new(), false)?.circuit;
    let main = circuit
      .multi_stark_layout()
      .map_err(|error| error.to_string())?
      .main_height;
    let rows: usize =
      circuit.tables().iter().map(|table| table.rows().len()).sum();
    Ok([main, rows.max(2).next_power_of_two()])
  }

  /// The merge circuit and its deferred pairing keys, without a request.
  pub(crate) fn circuit(
    &self,
  ) -> Result<(Circuit<Scalar>, Vec<G2Affine>), String> {
    let compiled = self.compile()?;
    Ok((compiled.circuit, compiled.pairing_keys))
  }

  pub(crate) fn build(
    &self,
    request: &MergeRequest<'_>,
  ) -> Result<Built, String> {
    let compiled = self.compile()?;
    let inputs = compiled.request_inputs(self, request)?;
    Ok(Built {
      circuit: compiled.circuit,
      inputs: inputs.inputs,
      #[cfg(test)]
      points: inputs.points,
      pairing_outputs: compiled.pairing_outputs,
      pairing_keys: compiled.pairing_keys,
      msm_terms: compiled.msm_terms,
      #[cfg(test)]
      terms: compiled.terms,
    })
  }
}

impl MergeCompiled {
  fn request_inputs(
    &self,
    plan: &MergePlan<'_>,
    request: &MergeRequest<'_>,
  ) -> Result<bindings::RequestInputs, String> {
    if plan.identity != self.identity {
      return Err("request uses a different merge frontend".into());
    }
    if request.children.len() != plan.children.len()
      || request.family.len() != plan.rule.family_size
    {
      return Err("merge request differs from its plan".into());
    }
    let mut inputs = Vec::new();
    #[cfg(test)]
    let mut points = Vec::with_capacity(self.points.len());
    for ((child, request_child), bound) in
      plan.children.iter().zip(request.children).zip(&self.children)
    {
      child.plan.shape.validate(request_child.proof)?;
      let inherited = inherited_pair(request_child.public)?;
      let key = match (child.key, request_child.key) {
        (ChildKey::Fixed(_), None) => None,
        (ChildKey::Family, Some(key)) => {
          if key.0.len() != child.plan.vk.fixed.0.len()
            || key
              .0
              .iter()
              .zip(&child.plan.vk.fixed.0)
              .any(|(a, b)| a.len() != b.len())
          {
            return Err("family child key has the wrong shape".into());
          }
          Some(key)
        },
        _ => return Err("merge child key differs from its kind".into()),
      };
      for binding in &self.points[bound.points.clone()] {
        let value = match (binding.source, key) {
          (PointSource::Supplied(index), _) => inherited[index % 2],
          (PointSource::Key { matrix, column }, Some(key)) => {
            key.0[matrix][column]
          },
          (PointSource::Key { .. }, None) => unreachable!("validated key"),
          (source, _) => source.value(request_child.proof),
        };
        if !value.is_on_curve()
          || !value.is_in_correct_subgroup_assuming_on_curve()
        {
          return Err("invalid merge child proof point".into());
        }
        if !matches!(binding.source, PointSource::Fixed(_)) {
          inputs.extend(binding.point.inputs(value));
        }
        #[cfg(test)]
        points.push(value);
      }
      inputs.extend(self.scalars[bound.scalars.clone()].iter().map(
        |(handle, source)| (*handle, source.value(request_child.proof, &[])),
      ));
      if let Some(key) = key {
        let digest = key_digest(key)?;
        let member = request
          .family
          .iter()
          .position(|&candidate| candidate == digest)
          .ok_or("family child key is not a member of the family")?;
        inputs.extend(
          bound
            .selectors
            .iter()
            .enumerate()
            .map(|(index, &v)| (v, Scalar::from_bool(index == member))),
        );
      }
    }
    let claim_bytes: Vec<_> = match (&plan.rule.output, request.claims) {
      (Output::Join { .. }, ClaimWitness::Join(opening)) => opening
        .left_root
        .iter()
        .chain(&opening.right_root)
        .map(|&byte| Scalar::from_u8(byte))
        .chain([Scalar::from_bool(opening.right_conditional)])
        .collect(),
      (Output::Relay, ClaimWitness::Relay(digest)) => {
        digest.iter().map(|&byte| Scalar::from_u8(byte)).collect()
      },
      _ => return Err("claim witness differs from the merge rule".into()),
    };
    inputs.extend(self.claim_inputs.iter().copied().zip(claim_bytes));
    inputs.extend(
      self.family_inputs.iter().copied().zip(
        request.family.iter().flatten().map(|&byte| Scalar::from_u8(byte)),
      ),
    );
    Ok(bindings::RequestInputs {
      inputs,
      #[cfg(test)]
      points,
    })
  }
}

/// A child's inherited deferred pair, from the last limbs of its public values.
fn inherited_pair(public: &[Scalar]) -> Result<[G1Affine; 2], String> {
  if public.len() != CHILD_PUBLIC_VALUES {
    return Err("merge child public values have the wrong length".into());
  }
  pairing::decode(&public[STATEMENT_WORDS..])
    .map_err(|_error| "invalid merge child deferred pair".to_string())
}

/// The fold of pending pairings with weights `1, ρ, ρ², …`: each holds when
/// the fold does, except with probability about `(n - 1)/|Fr|` over ρ.
#[cfg(test)]
fn fold(pairs: &[[G1Affine; 2]], rho: Scalar) -> [G1Affine; 2] {
  use crate::kzg::curve::G1Projective;
  let mut sums = [G1Projective::zero(); 2];
  let mut weight = Scalar::ONE;
  for pair in pairs {
    for (sum, point) in sums.iter_mut().zip(pair) {
      *sum += *point * weight.0;
    }
    weight *= rho;
  }
  sums.map(|sum| sum.into_affine())
}

fn merge_identity(
  children: &[ChildPlan<'_>],
  rule: &MergeRule,
) -> Result<[u8; 32], String> {
  let mut hash = ::blake3::Hasher::new();
  hash.update(MERGE_VERSION);
  hash.update(FOLD_SEED);
  hash.update(KEY_DOMAIN);
  hash.update(FAMILY_DOMAIN);
  hash.update(&(children.len() as u64).to_le_bytes());
  for child in children {
    hash.update(&child.plan.identity);
    match child.key {
      ChildKey::Fixed(prefix) => {
        hash.update(&[0]);
        for word in prefix {
          hash.update(&word.to_le_bytes());
        }
      },
      ChildKey::Family => {
        hash.update(&[1]);
      },
    }
    let mut keys = vec![];
    child
      .inherited_keys
      .to_vec()
      .serialize_compressed(&mut keys)
      .map_err(|error| error.to_string())?;
    hash.update(&keys);
  }
  match &rule.output {
    Output::Join { claim_header } => {
      hash.update(&[0]);
      hash.update(&(claim_header.len() as u64).to_le_bytes());
      hash.update(claim_header);
    },
    Output::Relay => {
      hash.update(&[1]);
    },
  }
  for word in rule.head {
    hash.update(&word.to_le_bytes());
  }
  hash.update(&(rule.family_size as u64).to_le_bytes());
  hash.update(&(rule.height as u64).to_le_bytes());
  Ok(*hash.finalize().as_bytes())
}

/// The eight packed little-endian `u32` words of a digest, as a statement
/// carries it.
fn digest_words(b: &mut Builder, digest: &[ByteValue; 32]) -> Vec<Value> {
  digest.as_chunks::<4>().0.iter().map(|word| pack_bytes(b, word)).collect()
}

/// Add unconstrained squares of `value` until the computation trace lowers
/// to `height` rows: one row per gate, public, lookup and the zero anchor.
/// `value` must not be a constant, whose products fold away.
fn pad_rows(
  b: &mut Builder,
  value: Value,
  height: usize,
) -> Result<(), String> {
  let rows = |b: &Builder| {
    let stats = b.stats();
    stats.gates + stats.lookups + stats.publics + 1
  };
  if !height.is_power_of_two() || rows(b) > height {
    return Err("merge circuit exceeds its family height".into());
  }
  for _ in rows(b)..=height / 2 {
    b.mul(value, value);
  }
  Ok(())
}

fn byte_inputs(
  c: &mut Context,
  name: &str,
  inputs: &mut Vec<Value>,
) -> [ByteValue; 32] {
  std::array::from_fn(|i| {
    let value = c.b.input(format!("{name}.{i}"));
    inputs.push(value);
    c.bytes.constrain_byte(&mut c.b, value)
  })
}

/// The claim digests a merge links: both children's and the output's.
struct LinkedClaims {
  inputs: Vec<Value>,
  left: [ByteValue; 32],
  right: [ByteValue; 32],
  output: [ByteValue; 32],
}

/// Open both children's claims and build the output claim. The left claim
/// is closed and the right one assumes nothing or the left root, so each
/// claim is rebuilt from the two roots and one flag rather than parsed: no
/// other assumption has an encoding here. The inputs are the left root's
/// bytes, the right root's, then the flag.
fn link_claims(c: &mut Context, claim_header: &[u8]) -> LinkedClaims {
  let mut claim_inputs = vec![];
  let mut root = |c: &mut Context, name: &str| -> [ByteValue; 32] {
    std::array::from_fn(|i| {
      let value = c.b.input(format!("{name}.{i}"));
      claim_inputs.push(value);
      c.bytes.constrain_byte(&mut c.b, value)
    })
  };
  let left = root(c, "left.root");
  let right = root(c, "right.root");
  let flag = c.b.input("right.conditional");
  claim_inputs.push(flag);
  let conditional = c.b.assert_bool(flag);
  let header: Vec<_> =
    claim_header.iter().map(|&byte| c.bytes.constant(&mut c.b, byte)).collect();
  let none = c.bytes.constant(&mut c.b, 0);
  let some = c.bytes.constant(&mut c.b, 1);
  let claim = |root: &[ByteValue; 32],
               assumptions: Option<&[ByteValue; 32]>| {
    let mut bytes = header.clone();
    bytes.extend_from_slice(root);
    match assumptions {
      None => bytes.push(none),
      Some(assumptions) => {
        bytes.push(some);
        bytes.extend_from_slice(assumptions);
      },
    }
    bytes
  };
  let left_digest = blake3(&mut c.b, &c.bytes, &claim(&left, None));
  let right_closed = blake3(&mut c.b, &c.bytes, &claim(&right, None));
  let right_open = blake3(&mut c.b, &c.bytes, &claim(&right, Some(&left)));
  let right_digest: [ByteValue; 32] = std::array::from_fn(|i| {
    c.bytes.select(&mut c.b, conditional, right_open[i], right_closed[i])
  });
  let mut node = vec![some];
  node.extend_from_slice(&left);
  node.extend_from_slice(&right);
  let node = blake3(&mut c.b, &c.bytes, &node);
  let output_digest = blake3(&mut c.b, &c.bytes, &claim(&node, None));
  LinkedClaims {
    inputs: claim_inputs,
    left: left_digest,
    right: right_digest,
    output: output_digest,
  }
}

/// Constrain a family child's key: the BLAKE3 digest of its fixed
/// commitments' encodings is the family member a one-hot selector picks.
/// Returns the selector inputs.
fn bind_family_key(
  c: &mut Context,
  name: &str,
  fixed: &Commitment,
  members: &[[ByteValue; 32]],
) -> Vec<Value> {
  let mut bytes: Vec<_> =
    KEY_DOMAIN.iter().map(|&byte| c.bytes.constant(&mut c.b, byte)).collect();
  for &id in fixed.iter().flatten() {
    bytes.extend_from_slice(&c.encodings[id]);
  }
  let digest = blake3(&mut c.b, &c.bytes, &bytes);
  let selectors: Vec<_> = (0..members.len())
    .map(|j| {
      let selector = c.b.input(format!("{name}.member.{j}"));
      c.b.assert_bool(selector);
      selector
    })
    .collect();
  let terms: Vec<_> = selectors.iter().map(|&s| (Scalar::ONE, s)).collect();
  let count = c.b.linear_combination(&terms, Scalar::NEG_ONE);
  c.b.assert_zero(count);
  for (k, byte) in digest.iter().enumerate() {
    let mut selected = c.b.constant(Scalar::ZERO);
    for (&selector, member) in selectors.iter().zip(members) {
      selected = c.b.mul_add(selector, member[k].value(), selected);
    }
    c.b.assert_equal(selected, byte.value());
  }
  selectors
}

fn construct_merge(
  plan: &MergePlan<'_>,
  builder: Builder,
  pad: bool,
) -> Result<MergeCompiled, String> {
  let mut c = Context::new(builder);
  let mut points = vec![];
  let mut point_ranges = vec![];
  let mut inherited = vec![];
  for (index, child) in plan.children.iter().enumerate() {
    let start = c.points.len();
    points.push(c.proof_points(
      &child.plan.vk,
      &child.plan.shape,
      child.key == ChildKey::Family,
    ));
    inherited.push([
      c.point(PointSource::Supplied(2 * index)),
      c.point(PointSource::Supplied(2 * index + 1)),
    ]);
    point_ranges.push(start..c.points.len());
  }
  let mut phases = c.seal_curve_inputs();
  let mut scalars = vec![];
  let mut scalar_ranges = vec![];
  for child in &plan.children {
    let start = c.inputs.len();
    scalars.push(c.proof_scalars(&child.plan.shape)?);
    scalar_ranges.push(start..c.inputs.len());
  }

  let mut claim_inputs = vec![];
  let (child_digests, output_digest) = match &plan.rule.output {
    Output::Join { claim_header } => {
      let linked = link_claims(&mut c, claim_header);
      claim_inputs = linked.inputs;
      (vec![linked.left, linked.right], linked.output)
    },
    Output::Relay => {
      let digest = byte_inputs(&mut c, "relay.claim", &mut claim_inputs);
      (vec![digest], digest)
    },
  };
  let mut family_inputs = vec![];
  let members: Vec<_> = (0..plan.rule.family_size)
    .map(|j| byte_inputs(&mut c, &format!("family.{j}"), &mut family_inputs))
    .collect();
  let mut family: Vec<_> = FAMILY_DOMAIN
    .iter()
    .map(|&byte| c.bytes.constant(&mut c.b, byte))
    .collect();
  family.extend(members.iter().flatten());
  let family = blake3(&mut c.b, &c.bytes, &family);
  let family_words = digest_words(&mut c.b, &family);
  let head: Vec<_> = plan
    .rule
    .head
    .iter()
    .map(|&word| c.b.constant(Scalar::from_u64(word)))
    .collect();
  phases.push(PhaseCounts { name: "claims", stats: c.b.stats() });

  // Each child's claim rows: its prefix, its claim digest and the encoding
  // of the deferred pair it inherited.
  let mut openings = vec![];
  let mut selectors = vec![];
  for (index, (((child, digest), pair), (points, scalars))) in plan
    .children
    .iter()
    .zip(&child_digests)
    .zip(&inherited)
    .zip(points.iter().zip(&scalars))
    .enumerate()
  {
    let mut public: Vec<_> = match child.key {
      ChildKey::Fixed(prefix) => prefix
        .iter()
        .map(|&word| c.b.constant(Scalar::from_u64(word)))
        .collect(),
      ChildKey::Family => head.iter().chain(&family_words).copied().collect(),
    };
    selectors.push(match child.key {
      ChildKey::Fixed(_) => vec![],
      ChildKey::Family => bind_family_key(
        &mut c,
        &format!("child{index}"),
        &points.fixed,
        &members,
      ),
    });
    public.extend(digest_words(&mut c.b, digest));
    for &id in pair {
      let encoded = c.encodings[id];
      for chunk in encoded.as_chunks::<{ pairing::POINT_LIMB_BYTES }>().0 {
        public.push(pack_bytes(&mut c.b, chunk));
      }
    }
    let mut public = public.into_iter();
    let claim_vars: Vec<Vec<_>> = child
      .plan
      .claims
      .rows
      .iter()
      .map(|row| {
        row
          .iter()
          .map(|slot| match slot {
            ClaimSlot::Constant(value) => c.b.constant(*value),
            ClaimSlot::PublicU64 => {
              public.next().expect("validated child statement schema")
            },
          })
          .collect()
      })
      .collect();
    openings.push(verify_opening(
      &mut c,
      &child.plan.vk,
      &child.plan.shape,
      points,
      scalars,
      &claim_vars,
      &mut phases,
    )?);
  }

  // The output statement precedes the folded pair among the public values.
  for &word in head.iter().chain(&family_words) {
    c.b.expose_public(word);
  }
  for word in digest_words(&mut c.b, &output_digest) {
    c.b.expose_public(word);
  }

  // Every byte of each child's proof and claim rows was observed before its
  // last challenge, so the children's final transcript states bind every
  // pending point before the fold weight is sampled.
  let mut fold_transcript = Transcript::new(&mut c.b, &c.bytes, FOLD_SEED);
  let mut child_terms = vec![];
  for Opening { lhs, rhs, transcript } in openings {
    fold_transcript.observe(&transcript.finish());
    child_terms.push(c.opening_terms(lhs, rhs));
  }
  let rho = c.sample(&mut fold_transcript);
  // Child `i`'s outer opening has weight ρ^(2i) and its inherited pair
  // ρ^(2i+1), as in [`fold`].
  let mut terms: [Vec<(usize, Value)>; 2] = [vec![], vec![]];
  let mut weight = None;
  for (child, pair) in child_terms.into_iter().zip(&inherited) {
    for (operand, child_operand) in terms.iter_mut().zip(child) {
      match weight {
        None => operand.extend(child_operand),
        Some(weight) => operand.extend(
          child_operand
            .into_iter()
            .map(|(id, coefficient)| (id, c.b.mul(coefficient, weight))),
        ),
      }
    }
    let inherited_weight = match weight {
      None => rho,
      Some(weight) => c.b.mul(weight, rho),
    };
    for (operand, &id) in terms.iter_mut().zip(pair) {
      operand.push((id, inherited_weight));
    }
    weight = Some(c.b.mul(inherited_weight, rho));
  }
  phases.push(PhaseCounts { name: "scalar_checks", stats: c.b.stats() });
  let pairing_outputs = c.expose_pairing(&terms, &mut phases);
  if pad {
    pad_rows(&mut c.b, rho, plan.rule.height)?;
  }
  eprintln!("Merge circuit complete: {:?}", c.b.stats());
  Ok(MergeCompiled {
    circuit: c.b.finish(),
    identity: plan.identity,
    children: point_ranges
      .into_iter()
      .zip(scalar_ranges)
      .zip(selectors)
      .map(|((points, scalars), selectors)| ChildBindings {
        points,
        scalars,
        selectors,
      })
      .collect(),
    points: c.points,
    scalars: c.inputs,
    claim_inputs,
    family_inputs,
    pairing_outputs,
    pairing_keys: plan.keys.to_vec(),
    msm_terms: terms.iter().map(Vec::len).collect(),
    #[cfg(test)]
    terms: terms.into(),
  })
}
#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::{Srs, curve::Fr};

  fn pair(srs: &Srs, seed: u64) -> [G1Affine; 2] {
    // e(τ·W, g2)·e(−W, τ·g2) = 1 for any W.
    let w = (srs.g1[0] * Fr::from(seed)).into_affine();
    [(srs.g1[1] * Fr::from(seed)).into_affine(), -w]
  }

  fn holds(srs: &Srs, pair: [G1Affine; 2]) -> bool {
    PairingCurve::multi_pairing(pair, [srs.g2, srs.tau_g2]).is_zero()
  }

  #[test]
  fn folded_pairing_holds_exactly_when_every_pair_does() {
    let srs = Srs::unsafe_dev_setup(2, b"merge-fold-test");
    let pairs = [pair(&srs, 3), pair(&srs, 5), pair(&srs, 7), pair(&srs, 11)];
    assert!(pairs.iter().all(|&p| holds(&srs, p)));
    let rho = Scalar::from_u64(0x1234_5678_9abc);
    assert!(holds(&srs, fold(&pairs, rho)));
    for broken in 0..4 {
      let mut changed = pairs;
      changed[broken][0] = (changed[broken][0] * Fr::from(2u8)).into_affine();
      assert!(!holds(&srs, changed[broken]));
      assert!(!holds(&srs, fold(&changed, rho)));
    }
    // Two failing pairs cancel only for the one weight that aligns them.
    let mut swapped = pairs;
    swapped[0][0] = (pairs[0][0] + srs.g1[0]).into_affine();
    swapped[1][0] = (pairs[1][0] - srs.g1[0]).into_affine();
    assert!(holds(&srs, fold(&swapped, Scalar::ONE)));
    assert!(!holds(&srs, fold(&swapped, rho)));
  }

  #[test]
  fn fold_weights_are_powers_of_the_challenge() {
    let srs = Srs::unsafe_dev_setup(2, b"merge-fold-weights");
    let g = srs.g1[0];
    let pairs =
      [[g, g], [g, G1Affine::identity()], [G1Affine::identity(), g], [g, g]];
    let rho = Scalar::from_u64(3);
    let folded = fold(&pairs, rho);
    let at = |n: u64| (g * Fr::from(n)).into_affine();
    assert_eq!(folded, [at(1 + 3 + 27), at(1 + 9 + 27)]);
  }

  fn claim(
    header: &[u8],
    root: &[u8; 32],
    assumptions: Option<&[u8; 32]>,
  ) -> Vec<u8> {
    let mut bytes = header.to_vec();
    bytes.extend_from_slice(root);
    match assumptions {
      None => bytes.push(0),
      Some(assumptions) => {
        bytes.push(1);
        bytes.extend_from_slice(assumptions);
      },
    }
    bytes
  }

  #[test]
  fn linked_claims_match_native_digests() {
    let header = [0xe5, 0x04, 0x01];
    let mut c = Context::new(Builder::new());
    let linked = link_claims(&mut c, &header);
    let circuit = c.b.finish();
    let left = [3u8; 32];
    let right: [u8; 32] = std::array::from_fn(|i| u8::try_from(i).unwrap());
    let assign = |flag: u8| {
      let mut witness = circuit.witness();
      let values = left.iter().chain(&right).chain([&flag]);
      for (&input, &byte) in linked.inputs.iter().zip(values) {
        witness.set(input, Scalar::from_u8(byte)).unwrap();
      }
      witness.generate()
    };
    let digest = |assignment: &multi_stark::plonkish::Assignment<Scalar>,
                  bytes: &[ByteValue; 32]| {
      bytes.map(|byte| {
        let value = assignment.value(byte.value()).unwrap();
        u8::try_from(value.canonical_limbs_le()[0]).unwrap()
      })
    };
    let mut node = vec![1];
    node.extend_from_slice(&left);
    node.extend_from_slice(&right);
    let node = *::blake3::hash(&node).as_bytes();
    let output = *::blake3::hash(&claim(&header, &node, None)).as_bytes();
    for conditional in [false, true] {
      let assignment = assign(u8::from(conditional)).unwrap();
      let right_claim = claim(&header, &right, conditional.then_some(&left));
      assert_eq!(
        digest(&assignment, &linked.left),
        *::blake3::hash(&claim(&header, &left, None)).as_bytes()
      );
      assert_eq!(
        digest(&assignment, &linked.right),
        *::blake3::hash(&right_claim).as_bytes()
      );
      assert_eq!(digest(&assignment, &linked.output), output);
    }
    assert!(assign(2).is_err());
  }

  #[test]
  fn family_key_binding_matches_the_native_key_digest() {
    let srs = Srs::unsafe_dev_setup(2, b"merge-family-key");
    let key = KzgCommitment(vec![vec![srs.g1[0], srs.g1[1]], vec![-srs.g1[1]]]);
    let other =
      KzgCommitment(vec![vec![srs.g1[1], srs.g1[0]], vec![-srs.g1[1]]]);
    let family = [key_digest(&other).unwrap(), key_digest(&key).unwrap()];
    let mut c = Context::new(Builder::new());
    let fixed = c.key_commitment(&key);
    let mut family_inputs = vec![];
    let members: Vec<_> = (0..family.len())
      .map(|j| byte_inputs(&mut c, &format!("family.{j}"), &mut family_inputs))
      .collect();
    let selectors = bind_family_key(&mut c, "child", &fixed, &members);
    let bindings = std::mem::take(&mut c.points);
    let circuit = c.b.finish();
    let assign = |values: &KzgCommitment, member: usize| {
      let mut witness = circuit.witness();
      for binding in &bindings {
        let PointSource::Key { matrix, column } = binding.source else {
          unreachable!()
        };
        for (input, value) in binding.point.inputs(values.0[matrix][column]) {
          witness.set(input, value).unwrap();
        }
      }
      for (&input, &byte) in family_inputs.iter().zip(family.iter().flatten()) {
        witness.set(input, Scalar::from_u8(byte)).unwrap();
      }
      for (index, &selector) in selectors.iter().enumerate() {
        witness.set(selector, Scalar::from_bool(index == member)).unwrap();
      }
      witness.generate()
    };
    assert!(assign(&key, 1).is_ok());
    assert!(assign(&key, 0).is_err());
    assert!(assign(&other, 0).is_ok());
    assert_ne!(family_digest(&family), family_digest(&[family[1], family[0]]));
  }
}
