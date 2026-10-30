//! The merge stage. A join takes a left certificate of `checkEnv(R_L, none)`
//! and a right one of `checkEnv(R_R, a)`, where `a` is `none` or `some R_L`,
//! and proves `checkEnv(blake3(0x01 ‖ R_L ‖ R_R), none)`. An import takes one
//! certificate under the pinned 0.1 recursive key and proves the same claim.
//!
//! Each merge shape is its own circuit, and the shapes in [`FAMILY`] form one
//! family: every member verifies a merged child under any member's key. A
//! merged certificate has the recursive certificate's shape (an outer KZG
//! proof whose public values are an eighteen-word statement and one deferred
//! pair), and its statement prefix is the merge head followed by the packed
//! family digest, which the verifier checks against the family it trusts.
use super::{
  CompressConfig, PROOF_TAG, Result, SetupClass, SetupConfig, StageConfig,
  stages::{construct, statement::Statement as StageStatement},
  statement::{self, Statement},
  storage, verifying_keys,
  wrap::{self, VerifyingKey},
};
use crate::{
  kzg::{
    KzgCommitment, KzgConfig, Scalar, TranscriptKind, VerifierParams,
    compact::FixedProofCodec,
    curve::{G2Affine, read_g1_compressed},
  },
  recursive::{
    native_verifier::{
      Built, CHILD_PUBLIC_VALUES, ChildKey, ChildPlan, ChildRequest,
      ClaimOpening, ClaimSchema, ClaimWitness, HEAD_WORDS, MergePlan,
      MergeRequest, MergeRule, Output, PREFIX_WORDS, Plan, family_digest,
      key_digest,
    },
    pairing,
  },
};
use multi_stark::{
  prover::Proof,
  system::{Circuit, System},
  traits::Field,
};
use std::{fs, io, path::Path};
/// The header of every `checkEnv` claim: the claim tag (flag `0xE`, variant
/// 5), the object format and the validator (`Claim.put`, `Ix/Claim.lean`).
pub(crate) const CHECK_ENV_HEADER: [u8; 3] = [0xe5, 0x04, 0x01];

/// A `checkEnv(root, assumptions)` claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CheckEnv {
  pub(crate) root: [u8; 32],
  pub(crate) assumptions: Option<[u8; 32]>,
}

impl CheckEnv {
  pub(crate) fn decode(bytes: &[u8]) -> Result<Self> {
    let body = bytes
      .strip_prefix(CHECK_ENV_HEADER.as_slice())
      .ok_or("claim is not a checkEnv claim of this object format")?;
    let (root, assumptions) =
      body.split_first_chunk::<32>().ok_or("truncated checkEnv root")?;
    let assumptions = match assumptions {
      [0] => None,
      [1, rest @ ..] => Some(
        <[u8; 32]>::try_from(rest)
          .map_err(|_rest| "malformed checkEnv assumptions")?,
      ),
      _ => return Err("malformed checkEnv assumptions".into()),
    };
    Ok(Self { root: *root, assumptions })
  }

  pub(crate) fn encode(&self) -> Vec<u8> {
    let mut bytes = CHECK_ENV_HEADER.to_vec();
    bytes.extend_from_slice(&self.root);
    match &self.assumptions {
      None => bytes.push(0),
      Some(assumptions) => {
        bytes.push(1);
        bytes.extend_from_slice(assumptions);
      },
    }
    bytes
  }
}

/// The Ix Merkle node over two roots (`Ix/Merkle.lean`).
pub(crate) fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
  let mut hash = blake3::Hasher::new();
  hash.update(&[1]);
  hash.update(left);
  hash.update(right);
  *hash.finalize().as_bytes()
}

/// The merge rule on claims: the circuit's private opening and the output
/// claim, or why the two claims do not merge.
pub(crate) fn merge_claims(
  left: &CheckEnv,
  right: &CheckEnv,
) -> Result<(ClaimOpening, CheckEnv)> {
  if left.assumptions.is_some() {
    return Err("the left claim of a merge must be closed".into());
  }
  let right_conditional = match right.assumptions {
    None => false,
    Some(assumptions) if assumptions == left.root => true,
    Some(_) => {
      return Err("the right claim assumes a root other than the left".into());
    },
  };
  Ok((
    ClaimOpening {
      left_root: left.root,
      right_root: right.root,
      right_conditional,
    },
    CheckEnv { root: node(&left.root, &right.root), assumptions: None },
  ))
}

/// What a child certificate is. The kind fixes the key it verifies under and
/// its statement's prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildKind {
  /// A recursive certificate of this version, under its recursive key.
  Fresh,
  /// A merge certificate, under a key of this version's merge family.
  Merged,
  /// A recursive certificate of version 0.1, under its pinned key.
  Imported,
}

/// A merge circuit's shape: the rule and the kind of each child.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MergeShape {
  Join([ChildKind; 2]),
  Relay(ChildKind),
}

impl MergeShape {
  pub(crate) fn kinds(&self) -> &[ChildKind] {
    match self {
      Self::Join(kinds) => kinds,
      Self::Relay(kind) => std::slice::from_ref(kind),
    }
  }
}

/// The merge family, in the order its key digests are hashed.
pub(crate) const FAMILY: [MergeShape; 5] = {
  use ChildKind::{Fresh, Imported, Merged};
  [
    MergeShape::Join([Fresh, Fresh]),
    MergeShape::Join([Merged, Fresh]),
    MergeShape::Join([Fresh, Merged]),
    MergeShape::Join([Merged, Merged]),
    MergeShape::Relay(Imported),
  ]
};

/// The constant head of every merge statement's prefix. Its first word
/// matches an aggregation prefix's backend word, and its second differs
/// from every aggregation entrypoint.
pub(super) const MERGE_HEAD: [u64; HEAD_WORDS] = [0, 0x4d45];

/// The family's key files, in [`FAMILY`] order.
pub(super) const FAMILY_FILES: [&str; 5] = [
  "join-fresh-fresh.bin",
  "join-merged-fresh.bin",
  "join-fresh-merged.bin",
  "join-merged-merged.bin",
  "relay-imported.bin",
];

/// The constant words of the statements merges read and write: the prefix
/// fresh certificates carry, the prefix imported certificates carry, and the
/// head of a merge statement's prefix.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Prefixes {
  pub(crate) fresh: [u64; PREFIX_WORDS],
  pub(crate) imported: [u64; PREFIX_WORDS],
  pub(crate) head: [u64; HEAD_WORDS],
}

/// The packed form of a 32-byte digest, as a statement carries it.
fn digest_words(digest: &[u8; 32]) -> [u64; 8] {
  std::array::from_fn(|i| {
    u64::from(u32::from_le_bytes(digest[4 * i..4 * i + 4].try_into().unwrap()))
  })
}

impl Prefixes {
  /// The prefix of merge statements of the family with digest `family`.
  pub(crate) fn merge(&self, family: &[u8; 32]) -> [u64; PREFIX_WORDS] {
    let mut prefix = [0; PREFIX_WORDS];
    prefix[..HEAD_WORDS].copy_from_slice(&self.head);
    prefix[HEAD_WORDS..].copy_from_slice(&digest_words(family));
    prefix
  }

  fn child(&self, kind: ChildKind, family: &[u8; 32]) -> [u64; PREFIX_WORDS] {
    match kind {
      ChildKind::Fresh => self.fresh,
      ChildKind::Merged => self.merge(family),
      ChildKind::Imported => self.imported,
    }
  }
}

/// The verifying keys merges are checked against: this version's recursive
/// key, the pinned 0.1 recursive key, and the merge family in [`FAMILY`]
/// order.
pub(crate) struct MergeKeys {
  pub(crate) recursive: VerifyingKey,
  pub(crate) imported: VerifyingKey,
  pub(crate) family: Vec<VerifyingKey>,
}

impl MergeKeys {
  /// Each member's key digest and the family digest.
  fn digests(&self) -> Result<(Vec<[u8; 32]>, [u8; 32])> {
    if self.family.len() != FAMILY.len() {
      return Err("merge family has the wrong size".into());
    }
    let keys = self
      .family
      .iter()
      .map(|vk| {
        Ok(key_digest(fixed_commitment(&vk.certificate_verifier()?.0)?)?)
      })
      .collect::<Result<Vec<_>>>()?;
    let family = family_digest(&keys);
    Ok((keys, family))
  }

  fn family_member(&self, packet: &[u8]) -> Result<&VerifyingKey> {
    let id = packet.get(..32).ok_or("truncated certificate")?;
    self
      .family
      .iter()
      .find(|vk| vk.id() == id)
      .ok_or_else(|| "certificate is not under a merge family key".into())
  }
}

fn fixed_commitment(system: &System<KzgConfig>) -> Result<&KzgCommitment> {
  Ok(system.preprocessed_commit.as_ref().ok_or("missing fixed commitment")?)
}

/// One child certificate: its kind, claim bytes and packet.
pub(crate) struct Child<'a> {
  pub(crate) kind: ChildKind,
  pub(crate) claim: &'a [u8],
  pub(crate) packet: &'a [u8],
}

/// The merge's natively computed result.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Reference {
  pub(crate) claims: ClaimWitness,
  pub(crate) claim: Vec<u8>,
  pub(crate) statement: Statement,
}

/// Apply a merge shape's rule to its children's claims natively, as the
/// circuit does, for the family with digest `family`.
pub(crate) fn reference(
  shape: MergeShape,
  prefixes: &Prefixes,
  family: &[u8; 32],
  claims: &[&[u8]],
) -> Result<Reference> {
  let (claims, claim) = match (shape, claims) {
    (MergeShape::Join(_), [left, right]) => {
      let (opening, output) =
        merge_claims(&CheckEnv::decode(left)?, &CheckEnv::decode(right)?)?;
      (ClaimWitness::Join(opening), output.encode())
    },
    (MergeShape::Relay(_), [claim]) => {
      CheckEnv::decode(claim)?;
      (ClaimWitness::Relay(*blake3::hash(claim).as_bytes()), claim.to_vec())
    },
    _ => return Err("child count differs from the merge shape".into()),
  };
  let statement = statement::with_claim(&prefixes.merge(family), &claim);
  Ok(Reference { claims, claim, statement })
}

fn rule(shape: MergeShape, prefixes: &Prefixes, height: usize) -> MergeRule {
  MergeRule {
    output: match shape {
      MergeShape::Join(_) => {
        Output::Join { claim_header: CHECK_ENV_HEADER.to_vec() }
      },
      MergeShape::Relay(_) => Output::Relay,
    },
    head: prefixes.head,
    family_size: FAMILY.len(),
    height,
  }
}

fn logs(system: &System<KzgConfig>) -> Result<Vec<u8>> {
  Ok(
    system
      .circuits
      .iter()
      .map(|circuit| u8::try_from(circuit.preprocessed_height.ilog2()))
      .collect::<std::result::Result<_, _>>()?,
  )
}

/// The in-circuit verifier of certificates under `system`, whose public
/// values are all variable.
fn child_plan<'a>(
  system: &'a System<KzgConfig>,
  key: ChildKey,
  inherited_keys: &[G2Affine; 2],
) -> Result<ChildPlan<'a>> {
  let statement = StageStatement::recursive(CHILD_PUBLIC_VALUES);
  let schema =
    ClaimSchema::from_claims(&statement.template, &statement.locations)?;
  Ok(ChildPlan {
    plan: Plan::new(
      system,
      &logs(system)?,
      schema,
      construct::recursive_layout(),
    )?,
    key,
    inherited_keys: *inherited_keys,
  })
}

/// The constant part of every merge family member's verifier: the lowered
/// constraints of the recursive key's two partitions, which this lowering
/// shares across circuits, at the family's heights, under the outer setup at
/// that height. Its fixed commitment is a placeholder of the right shape;
/// a family child supplies the real one with its request.
pub(crate) struct FamilyLayout {
  pub(crate) heights: [usize; 2],
  system: System<KzgConfig>,
}

impl FamilyLayout {
  pub(crate) fn new(
    recursive: &System<KzgConfig>,
    heights: [usize; 2],
    params: VerifierParams,
  ) -> Result<Self> {
    use ark_ec::AffineRepr;
    if params.max_trace_len() != heights[0]
      || recursive.circuits.len() != 2
      || heights.iter().any(|h| *h < 2 || !h.is_power_of_two())
    {
      return Err("invalid merge family layout".into());
    }
    let circuits = recursive
      .circuits
      .iter()
      .zip(heights)
      .map(|(circuit, height)| {
        let mut circuit = clone_circuit(circuit)?;
        circuit.preprocessed = None;
        circuit.preprocessed_height = height;
        Ok(circuit)
      })
      .collect::<Result<Vec<_>>>()?;
    let placeholder = crate::kzg::curve::G1Affine::generator();
    let fixed = KzgCommitment(
      circuits
        .iter()
        .map(|circuit| vec![placeholder; circuit.preprocessed_width])
        .collect(),
    );
    Ok(Self {
      heights,
      system: System {
        config: KzgConfig::verifier_only(params, 2)
          .with_transcript(TranscriptKind::Blake3),
        circuits,
        preprocessed_commit: Some(fixed),
        preprocessed_indices: vec![Some(0), Some(1)],
      },
    })
  }

  /// The layout under `setup`, from the recursive key's constraints.
  pub(crate) fn derive(
    recursive: &VerifyingKey,
    heights: [usize; 2],
    setup: &SetupConfig,
  ) -> Result<Self> {
    let params = setup
      .for_stage(wrap::OUTER_SEED, heights[0])?
      .verifier_params(heights[0])?;
    Self::new(&recursive.certificate_verifier()?.0, heights, params)
  }

  /// Check a family member's key has this layout.
  fn admit(&self, member: &System<KzgConfig>) -> Result<()> {
    if member.config.transcript_seed() != self.system.config.transcript_seed()
      || member.circuits.len() != self.system.circuits.len()
    {
      return Err("merge family key differs from the family layout".into());
    }
    for (circuit, expected) in member.circuits.iter().zip(&self.system.circuits)
    {
      if circuit_metadata(circuit)? != circuit_metadata(expected)? {
        return Err("merge family key differs from the family layout".into());
      }
    }
    let fixed = fixed_commitment(member)?;
    let expected = fixed_commitment(&self.system)?;
    if fixed.0.len() != expected.0.len()
      || fixed.0.iter().zip(&expected.0).any(|(a, b)| a.len() != b.len())
    {
      return Err("merge family key differs from the family layout".into());
    }
    Ok(())
  }
}

fn clone_circuit(circuit: &Circuit<Scalar>) -> Result<Circuit<Scalar>> {
  let bytes =
    bincode::serde::encode_to_vec(circuit, bincode::config::standard())?;
  Ok(bincode::serde::decode_from_slice(&bytes, bincode::config::standard())?.0)
}

/// Everything about a circuit its verifier depends on except its fixed data.
fn circuit_metadata(circuit: &Circuit<Scalar>) -> Result<Vec<u8>> {
  Ok(bincode::serde::encode_to_vec(
    (
      &circuit.graph,
      circuit.main_width,
      circuit.preprocessed_width,
      circuit.preprocessed_height,
      circuit.num_lookups,
      circuit.stage_2_width,
      circuit.num_publics,
      circuit.lookup_group_size,
      circuit.constraint_count,
      circuit.max_constraint_degree,
    ),
    bincode::config::standard(),
  )?)
}

/// A merge circuit's plan for `shape`, without a request.
fn plan<'a>(
  shape: MergeShape,
  prefixes: &Prefixes,
  recursive: &'a System<KzgConfig>,
  imported: &'a System<KzgConfig>,
  layout: &'a FamilyLayout,
  inherited_keys: &[G2Affine; 2],
) -> Result<MergePlan<'a>> {
  let children = shape
    .kinds()
    .iter()
    .map(|kind| match kind {
      ChildKind::Fresh => {
        child_plan(recursive, ChildKey::Fixed(prefixes.fresh), inherited_keys)
      },
      ChildKind::Imported => {
        child_plan(imported, ChildKey::Fixed(prefixes.imported), inherited_keys)
      },
      ChildKind::Merged => {
        child_plan(&layout.system, ChildKey::Family, inherited_keys)
      },
    })
    .collect::<Result<Vec<_>>>()?;
  Ok(MergePlan::new(children, rule(shape, prefixes, layout.heights[0]))?)
}

/// A child's outer proof and public values, after verifying it natively.
struct Certificate {
  proof: Proof<KzgConfig>,
  public: Vec<Scalar>,
}

fn certificate(
  vk: &VerifyingKey,
  system: &System<KzgConfig>,
  packet: &[u8],
  expected: &Statement,
) -> Result<Certificate> {
  vk.verify(packet, expected)?;
  let mut body =
    packet.get(32 + statement::WORDS * 8..).ok_or("truncated certificate")?;
  let points = [read_g1_compressed(&mut body)?, read_g1_compressed(&mut body)?];
  let mut public: Vec<_> =
    expected.iter().copied().map(Scalar::from_u64).collect();
  public.extend(pairing::encode(points));
  let proof = FixedProofCodec::new(system, &logs(system)?)?.decode(body)?;
  Ok(Certificate { proof, public })
}

/// The merge circuit of `shape` with one request's witness, the natively
/// computed result it must expose, and the circuit's frontend identity. Every child is verified natively first,
/// including its deferred pairing.
pub(crate) fn build(
  shape: MergeShape,
  keys: &MergeKeys,
  layout: &FamilyLayout,
  prefixes: &Prefixes,
  children: &[Child<'_>],
) -> Result<(Built, Reference, [u8; 32])> {
  if children.iter().map(|child| child.kind).ne(shape.kinds().iter().copied()) {
    return Err("children differ from the merge shape".into());
  }
  let (members, family) = keys.digests()?;
  let claims: Vec<_> = children.iter().map(|child| child.claim).collect();
  let expected = reference(shape, prefixes, &family, &claims)?;
  let (recursive, inherited_keys) = keys.recursive.certificate_verifier()?;
  let (imported, imported_keys) = keys.imported.certificate_verifier()?;
  if imported_keys != inherited_keys {
    return Err("imported certificates use another pairing basis".into());
  }
  let mut certificates = vec![];
  let mut systems = vec![];
  for child in children {
    let vk = match child.kind {
      ChildKind::Fresh => &keys.recursive,
      ChildKind::Imported => &keys.imported,
      ChildKind::Merged => keys.family_member(child.packet)?,
    };
    let expected =
      statement::with_claim(&prefixes.child(child.kind, &family), child.claim);
    let (system, _) = vk.certificate_verifier()?;
    if child.kind == ChildKind::Merged {
      layout.admit(&system)?;
    }
    certificates.push(certificate(vk, &system, child.packet, &expected)?);
    systems.push(system);
  }
  let plan =
    plan(shape, prefixes, &recursive, &imported, layout, &inherited_keys)?;
  let requests: Vec<_> = children
    .iter()
    .zip(&certificates)
    .zip(&systems)
    .map(|((child, certificate), system)| {
      Ok(ChildRequest {
        proof: &certificate.proof,
        public: &certificate.public,
        key: match child.kind {
          ChildKind::Merged => Some(fixed_commitment(system)?),
          ChildKind::Fresh | ChildKind::Imported => None,
        },
      })
    })
    .collect::<Result<_>>()?;
  let built = plan.build(&MergeRequest {
    children: &requests,
    claims: expected.claims,
    family: &members,
  })?;
  Ok((built, expected, plan.identity()))
}

/// Derive the merge family's verifying keys, in [`FAMILY`] order, without a
/// proof. Every member is padded to the largest member's heights, which the
/// family's merged children are verified at. Those heights shape the merged
/// children's verifiers and so each member's size; they are found by
/// rebuilding until they repeat.
pub(crate) fn derive_family(
  keys: &MergeKeys,
  prefixes: &Prefixes,
  setup: &SetupConfig,
) -> Result<Vec<Vec<u8>>> {
  let (recursive, inherited_keys) = keys.recursive.certificate_verifier()?;
  let (imported, _) = keys.imported.certificate_verifier()?;
  let mut heights = [
    recursive.circuits[0].preprocessed_height,
    recursive.circuits[1].preprocessed_height,
  ];
  for _ in 0..4 {
    let layout = FamilyLayout::derive(&keys.recursive, heights, setup)?;
    let plans = FAMILY
      .iter()
      .map(|&shape| {
        plan(shape, prefixes, &recursive, &imported, &layout, &inherited_keys)
      })
      .collect::<Result<Vec<_>>>()?;
    let natural = plans
      .iter()
      .map(MergePlan::natural_heights)
      .collect::<std::result::Result<Vec<_>, _>>()?;
    let next = [
      natural.iter().map(|h| h[0]).max().ok_or("empty merge family")?,
      natural.iter().map(|h| h[1]).max().ok_or("empty merge family")?,
    ];
    if natural.iter().any(|h| h[1] != next[1]) {
      return Err("merge family members have different tables".into());
    }
    if next != heights {
      heights = next;
      continue;
    }
    return plans
      .iter()
      .map(|plan| {
        let (circuit, pairing_keys) = plan.circuit()?;
        let vk = wrap::Frontend::new(
          circuit,
          &pairing_keys,
          &plan.identity(),
          wrap::MAX_TRACE_LEN,
        )?
        .verifying_key(setup)?;
        layout.admit(&vk.certificate_verifier()?.0)?;
        vk.to_bytes()
      })
      .collect();
  }
  Err("merge family heights do not settle".into())
}

/// Verify a merge certificate of `claim` under the trusted merge family: its
/// key must be a member, its statement must carry the family digest, and its
/// outer proof and folded deferred pairing must hold. Returns the claim,
/// which is conditional when an imported certificate of a conditional claim
/// was relayed.
pub(crate) fn verify(
  keys: &MergeKeys,
  prefixes: &Prefixes,
  packet: &[u8],
  claim: &[u8],
) -> Result<CheckEnv> {
  let decoded = CheckEnv::decode(claim)?;
  let (_, family) = keys.digests()?;
  keys
    .family_member(packet)?
    .verify(packet, &statement::with_claim(&prefixes.merge(&family), claim))?;
  Ok(decoded)
}

/// Parse a statement prefix written as ten comma-separated words.
pub fn parse_prefix(text: &str) -> Result<[u64; PREFIX_WORDS]> {
  let words = text
    .split(',')
    .map(|word| word.trim().parse::<u64>())
    .collect::<std::result::Result<Vec<_>, _>>()?;
  Ok(
    words
      .try_into()
      .map_err(|_words| "a statement prefix has ten comma-separated words")?,
  )
}

/// Derive this version's merge family keys, in [`FAMILY`] order and encoded
/// as the files [`FAMILY_FILES`] name, from its recursive key and the
/// statement prefix its fresh certificates carry, without a proof.
pub fn derive_merge_family(
  recursive_vk: &[u8],
  statement_prefix: [u64; PREFIX_WORDS],
  setup: &SetupConfig,
) -> Result<Vec<Vec<u8>>> {
  let keys = MergeKeys {
    recursive: VerifyingKey::from_bytes(recursive_vk)?,
    imported: VerifyingKey::from_bytes(verifying_keys::IMPORTED_RECURSIVE_VK)?,
    family: vec![],
  };
  let prefixes = Prefixes {
    fresh: statement_prefix,
    imported: verifying_keys::IMPORTED_STATEMENT_PREFIX,
    head: MERGE_HEAD,
  };
  derive_family(&keys, &prefixes, setup)
}

/// The keys and prefixes merges are proved and verified against.
pub struct Release {
  keys: MergeKeys,
  family: Vec<Vec<u8>>,
  prefixes: Prefixes,
  layout: FamilyLayout,
}

impl Release {
  /// The release this build bundles.
  pub fn bundled() -> Result<Self> {
    let release = Self::new(
      VerifyingKey::from_bytes(verifying_keys::RECURSIVE_VK)?,
      verifying_keys::STATEMENT_PREFIX,
      verifying_keys::MERGE_FAMILY.iter().map(|vk| vk.to_vec()).collect(),
    )?;
    if release.keys.digests()?.1
      != verifying_keys::decode(verifying_keys::MERGE_FAMILY_BLAKE3)?
    {
      return Err("bundled merge family differs from its pin".into());
    }
    Ok(release)
  }

  /// A release from a key directory, for development and testing: the
  /// recursive key fresh certificates verify under (`recursive-vk.bin`),
  /// their statement prefix (`statement-prefix.txt`, ten comma-separated
  /// words) and the family members ([`FAMILY_FILES`]). Imported
  /// certificates verify under the bundled 0.1 key.
  pub fn load(dir: &Path) -> Result<Self> {
    let family = FAMILY_FILES
      .iter()
      .map(|name| fs::read(dir.join(name)))
      .collect::<io::Result<Vec<_>>>()?;
    Self::new(
      VerifyingKey::from_bytes(&fs::read(dir.join("recursive-vk.bin"))?)?,
      parse_prefix(&fs::read_to_string(dir.join("statement-prefix.txt"))?)?,
      family,
    )
  }

  fn new(
    recursive: VerifyingKey,
    fresh: [u64; PREFIX_WORDS],
    family: Vec<Vec<u8>>,
  ) -> Result<Self> {
    if family.len() != FAMILY.len() {
      return Err("merge family has the wrong size".into());
    }
    let members = family
      .iter()
      .map(|bytes| VerifyingKey::from_bytes(bytes))
      .collect::<Result<Vec<_>>>()?;
    let (system, _) = members[0].certificate_verifier()?;
    let heights = [
      system.circuits.first().ok_or("empty merge key")?.preprocessed_height,
      system
        .circuits
        .get(1)
        .ok_or("merge key lacks a table")?
        .preprocessed_height,
    ];
    let layout = FamilyLayout::new(
      &recursive.certificate_verifier()?.0,
      heights,
      members[0].verifier_params()?,
    )?;
    for member in &members {
      layout.admit(&member.certificate_verifier()?.0)?;
    }
    Ok(Self {
      keys: MergeKeys {
        recursive,
        imported: VerifyingKey::from_bytes(
          verifying_keys::IMPORTED_RECURSIVE_VK,
        )?,
        family: members,
      },
      family,
      prefixes: Prefixes {
        fresh,
        imported: verifying_keys::IMPORTED_STATEMENT_PREFIX,
        head: MERGE_HEAD,
      },
      layout,
    })
  }

  /// The kind of a joined child: fresh under the recursive key, merged under
  /// a family key.
  fn join_kind(&self, packet: &[u8]) -> Result<ChildKind> {
    let id = packet.get(..32).ok_or("truncated compressed proof")?;
    if id == self.keys.recursive.id() {
      Ok(ChildKind::Fresh)
    } else if self.keys.family.iter().any(|vk| vk.id() == id) {
      Ok(ChildKind::Merged)
    } else {
      Err(
        "a joined proof must be a compressed proof of this version or a \
         merged proof of its family"
          .into(),
      )
    }
  }
}

/// What a merge does with its inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MergeKind {
  /// Join a closed left certificate with a right one that assumes nothing
  /// or the left root.
  Join,
  /// Carry a version 0.1 certificate into this version's family.
  Import,
}

/// One input certificate: its claim and its compressed proof, as `compress`
/// returns it.
#[derive(Clone, Copy)]
pub struct MergeChild<'a> {
  pub claim: &'a [u8],
  pub proof: &'a [u8],
}

/// The claim a merge of `children` proves, by the merge rule alone.
pub fn merged_claim(kind: MergeKind, children: &[&[u8]]) -> Result<Vec<u8>> {
  match (kind, children) {
    (MergeKind::Join, [left, right]) => {
      let (_, output) =
        merge_claims(&CheckEnv::decode(left)?, &CheckEnv::decode(right)?)?;
      Ok(output.encode())
    },
    (MergeKind::Import, [claim]) => {
      CheckEnv::decode(claim)?;
      Ok(claim.to_vec())
    },
    _ => Err("a join takes two proofs and an import one".into()),
  }
}

/// The merge stage directory under a merge's output directory.
const MERGE_STAGE: &str = "merge";
/// The proof `merge` returns, also left in its output directory.
const MERGED_PROOF: &str = "compressed.bin";
/// The claim of that proof.
const MERGED_CLAIM: &str = "claim.bin";

fn packet(proof: &[u8]) -> Result<&[u8]> {
  Ok(
    proof
      .strip_prefix(PROOF_TAG.as_slice())
      .ok_or("a merge input must be a recursive KZG compressed proof")?,
  )
}

/// The saved merge stage proves `statement` under the family member `index`.
fn check_merge_stage(
  dir: &Path,
  release: &Release,
  index: usize,
  statement: &Statement,
  setup: &SetupConfig,
) -> Result<()> {
  let bytes = fs::read(dir.join("vk.bin"))?;
  if bytes != release.family[index] {
    return Err(
      "the merge key differs from the release family member for this shape; \
       prove under the release setup"
        .into(),
    );
  }
  let vk = VerifyingKey::from_bytes(&bytes)?;
  vk.check_setup_class(setup.class())?;
  vk.verify(&fs::read(dir.join("kzg/packet.bin"))?, statement)?;
  Ok(())
}

/// Merge `children` into one certificate under `release`, keeping the merge
/// stage in `out/merge`, and return the merged claim and its compressed
/// proof, which are also written to `out`. Every child is verified natively
/// first. The stage is reused when its proof verifies for the expected
/// statement under the release key, unless `config.fresh` is set.
pub fn merge(
  kind: MergeKind,
  children: &[MergeChild<'_>],
  release: &Release,
  config: &CompressConfig,
  out: &Path,
) -> Result<(Vec<u8>, Vec<u8>)> {
  let packets = children
    .iter()
    .map(|child| packet(child.proof))
    .collect::<Result<Vec<_>>>()?;
  let shape = match (kind, packets.as_slice()) {
    (MergeKind::Join, [left, right]) => {
      MergeShape::Join([release.join_kind(left)?, release.join_kind(right)?])
    },
    (MergeKind::Import, [packet]) => {
      if packet.get(..32) != Some(release.keys.imported.id().as_slice()) {
        return Err(
          "an imported proof must be under the 0.1 recursive key".into(),
        );
      }
      MergeShape::Relay(ChildKind::Imported)
    },
    _ => return Err("a join takes two proofs and an import one".into()),
  };
  let index = FAMILY
    .iter()
    .position(|member| *member == shape)
    .ok_or("no family member merges these kinds")?;
  let (_, family) = release.keys.digests()?;
  let claims: Vec<_> = children.iter().map(|child| child.claim).collect();
  let expected = reference(shape, &release.prefixes, &family, &claims)?;
  fs::create_dir_all(out)?;
  let dir = out.join(MERGE_STAGE);
  let check = |dir: &Path| {
    check_merge_stage(dir, release, index, &expected.statement, &config.setup)
  };
  let reused = !config.fresh
    && dir.is_dir()
    && match check(&dir) {
      Ok(()) => {
        eprintln!("merge: reusing the verified stage");
        true
      },
      Err(error) => {
        eprintln!("merge: proving again: {error}");
        false
      },
    };
  if !reused {
    match fs::remove_dir_all(&dir) {
      Ok(()) => {},
      Err(error) if error.kind() == io::ErrorKind::NotFound => {},
      Err(error) => return Err(error.into()),
    }
    let inputs: Vec<_> = children
      .iter()
      .zip(&packets)
      .zip(shape.kinds())
      .map(|((child, packet), &kind)| Child {
        kind,
        claim: child.claim,
        packet,
      })
      .collect();
    let (built, _, identity) =
      build(shape, &release.keys, &release.layout, &release.prefixes, &inputs)?;
    let assignment = built.assign()?;
    wrap::stage(
      built,
      assignment,
      &dir,
      &identity,
      &expected.statement,
      &StageConfig::from_config(config),
    )?;
    #[cfg(feature = "cuda")]
    multi_stark::cuda::release_device_memory();
    check(&dir)?;
  }
  let mut proof = PROOF_TAG.to_vec();
  proof.extend(fs::read(dir.join("kzg/packet.bin"))?);
  verify_merged(&proof, &expected.claim, release, true)?;
  storage::write_atomic(&out.join(MERGED_CLAIM), &expected.claim)?;
  storage::write_atomic(&out.join(MERGED_PROOF), &proof)?;
  Ok((expected.claim, proof))
}

/// Verify a merged compressed proof of `claim` under `release`. Development
/// setups are refused unless `allow_development`.
pub fn verify_merged(
  proof: &[u8],
  claim: &[u8],
  release: &Release,
  allow_development: bool,
) -> Result<SetupClass> {
  let packet = packet(proof)?;
  let class =
    SetupClass::of(&release.keys.family_member(packet)?.verifier_params()?);
  if class == SetupClass::Development && !allow_development {
    return Err(
      "development merged proofs are not production-secure; allow them \
       explicitly"
        .into(),
    );
  }
  verify(&release.keys, &release.prefixes, packet, claim)?;
  Ok(class)
}
#[cfg(test)]
mod tests {
  use super::*;
  use crate::pipeline::init_claim::INIT_PUBLIC_WORDS;

  const INIT_CLAIM: &[u8] =
    include_bytes!("../../tests/fixtures/init-fri/claim.bin");

  fn prefixes() -> Prefixes {
    let mut fresh = [0; PREFIX_WORDS];
    fresh.copy_from_slice(&INIT_PUBLIC_WORDS[..PREFIX_WORDS]);
    Prefixes {
      fresh,
      imported: verifying_keys::IMPORTED_STATEMENT_PREFIX,
      head: MERGE_HEAD,
    }
  }

  #[test]
  fn check_env_codec_round_trips_the_init_claim() {
    let claim = CheckEnv::decode(INIT_CLAIM).unwrap();
    assert_eq!(claim.assumptions, None);
    assert_eq!(claim.encode(), INIT_CLAIM);
    statement::bind_claim(INIT_CLAIM, &INIT_PUBLIC_WORDS).unwrap();
    assert_eq!(
      statement::with_claim(
        &prefixes().child(ChildKind::Fresh, &[0; 32]),
        INIT_CLAIM
      ),
      INIT_PUBLIC_WORDS
    );
    let conditional = CheckEnv { root: [7; 32], assumptions: Some([9; 32]) };
    let bytes = conditional.encode();
    assert_eq!(bytes.len(), 68);
    assert_eq!(CheckEnv::decode(&bytes).unwrap(), conditional);
    for bad in [
      &INIT_CLAIM[..INIT_CLAIM.len() - 1],
      &bytes[..bytes.len() - 1],
      &[INIT_CLAIM, &[0]].concat(),
    ] {
      assert!(CheckEnv::decode(bad).is_err());
    }
    for (index, value) in [(0, 0xe4), (1, 0x03), (2, 0x00), (35, 2)] {
      let mut changed = INIT_CLAIM.to_vec();
      changed[index] = value;
      assert!(CheckEnv::decode(&changed).is_err());
    }
  }

  #[test]
  fn merge_rule_links_assumptions_to_the_left_root() {
    let left = CheckEnv { root: [1; 32], assumptions: None };
    let closed = CheckEnv { root: [2; 32], assumptions: None };
    let extension = CheckEnv { root: [2; 32], assumptions: Some([1; 32]) };
    let mut expected = vec![1];
    expected.extend([1; 32]);
    expected.extend([2; 32]);
    let root = *blake3::hash(&expected).as_bytes();
    for (right, conditional) in [(closed, false), (extension, true)] {
      let (opening, output) = merge_claims(&left, &right).unwrap();
      assert_eq!(opening.right_conditional, conditional);
      assert_eq!((opening.left_root, opening.right_root), ([1; 32], [2; 32]));
      assert_eq!(output, CheckEnv { root, assumptions: None });
    }
    assert!(merge_claims(&extension, &closed).is_err());
    let elsewhere = CheckEnv { root: [2; 32], assumptions: Some([3; 32]) };
    assert!(merge_claims(&left, &elsewhere).is_err());
    assert_ne!(node(&[1; 32], &[2; 32]), node(&[2; 32], &[1; 32]));
  }

  #[test]
  fn reference_exposes_the_merged_claim_under_the_family_prefix() {
    let prefixes = prefixes();
    let family = family_digest(&[[3; 32], [4; 32]]);
    let left = CheckEnv::decode(INIT_CLAIM).unwrap();
    let right =
      CheckEnv { root: [5; 32], assumptions: Some(left.root) }.encode();
    let join = MergeShape::Join([ChildKind::Merged, ChildKind::Fresh]);
    let merged =
      reference(join, &prefixes, &family, &[INIT_CLAIM, &right]).unwrap();
    assert!(matches!(
      merged.claims,
      ClaimWitness::Join(ClaimOpening { right_conditional: true, .. })
    ));
    let output = CheckEnv::decode(&merged.claim).unwrap();
    assert_eq!(output.root, node(&left.root, &[5; 32]));
    assert_eq!(output.assumptions, None);
    statement::bind_claim(&merged.claim, &merged.statement).unwrap();
    assert_eq!(merged.statement[..HEAD_WORDS], prefixes.head);
    assert_eq!(
      merged.statement[HEAD_WORDS..PREFIX_WORDS],
      digest_words(&family)
    );
    assert_eq!(
      prefixes.child(ChildKind::Merged, &family),
      merged.statement[..PREFIX_WORDS]
    );
    assert!(
      reference(join, &prefixes, &family, &[&right, INIT_CLAIM]).is_err()
    );
    assert!(reference(join, &prefixes, &family, &[INIT_CLAIM]).is_err());

    let import = MergeShape::Relay(ChildKind::Imported);
    let relayed = reference(import, &prefixes, &family, &[&right]).unwrap();
    assert_eq!(relayed.claim, right);
    assert_eq!(
      relayed.claims,
      ClaimWitness::Relay(*blake3::hash(&right).as_bytes())
    );
    statement::bind_claim(&right, &relayed.statement).unwrap();
    assert_eq!(
      prefixes.child(ChildKind::Imported, &family),
      verifying_keys::IMPORTED_STATEMENT_PREFIX
    );
  }

  #[test]
  fn merge_inputs_and_keys_are_checked_before_proving() {
    let words = [0, 293, 1, 2, 3, 4, 5, 6, 7, 8];
    assert_eq!(parse_prefix(" 0,293,1,2,3,4,5,6,7, 8\n").unwrap(), words);
    assert!(parse_prefix("0,293,1,2,3,4,5,6,7").is_err());
    assert!(parse_prefix("0,293,1,2,3,4,5,6,7,x").is_err());
    assert_ne!(MERGE_HEAD, verifying_keys::STATEMENT_PREFIX[..HEAD_WORDS]);

    let right = CheckEnv {
      root: [5; 32],
      assumptions: Some(CheckEnv::decode(INIT_CLAIM).unwrap().root),
    }
    .encode();
    let joined = merged_claim(MergeKind::Join, &[INIT_CLAIM, &right]).unwrap();
    assert_eq!(
      joined,
      reference(
        MergeShape::Join([ChildKind::Fresh, ChildKind::Fresh]),
        &prefixes(),
        &[0; 32],
        &[INIT_CLAIM, &right]
      )
      .unwrap()
      .claim
    );
    assert!(merged_claim(MergeKind::Join, &[&right, INIT_CLAIM]).is_err());
    assert!(merged_claim(MergeKind::Join, &[INIT_CLAIM]).is_err());
    assert_eq!(merged_claim(MergeKind::Import, &[&right]).unwrap(), right);
    assert!(merged_claim(MergeKind::Import, &[b"not a claim"]).is_err());

    let mut proof = PROOF_TAG.to_vec();
    proof.extend([7; 40]);
    assert_eq!(packet(&proof).unwrap(), [7; 40]);
    assert!(packet(&proof[1..]).is_err());

    Release::bundled().unwrap();
    let missing = std::env::temp_dir()
      .join(format!("ix-merge-missing-keys-{}", std::process::id()));
    assert!(Release::load(&missing).is_err());
  }

  #[test]
  fn development_stages_share_one_pairing_basis() {
    assert_eq!(super::super::setup::FIRST_SEED, wrap::OUTER_SEED);
  }

  #[test]
  fn family_shapes_are_distinct_and_cover_every_join_of_fresh_and_merged() {
    for (i, a) in FAMILY.iter().enumerate() {
      assert!(FAMILY[i + 1..].iter().all(|b| a != b));
    }
    use ChildKind::{Fresh, Merged};
    for left in [Fresh, Merged] {
      for right in [Fresh, Merged] {
        assert!(FAMILY.contains(&MergeShape::Join([left, right])));
      }
    }
  }

  #[test]
  #[ignore = "needs the release recursive key under IX_RECURSIVE_VK, its \
              statement prefix under IX_STATEMENT_PREFIX (ten comma-separated \
              words; default the bundled prefix), the pinned Ignition \
              release under IX_PARAMS_DIR (or IX_DEV_SRS), and commits the \
              fixed columns of five merge circuits; IX_MERGE_KEYS_OUT names \
              a key directory to write"]
  fn merge_family_keys_derive_without_a_proof() {
    let setup =
      SetupConfig::from_env(std::env::var_os("IX_DEV_SRS").is_some()).unwrap();
    let recursive =
      fs::read(std::env::var_os("IX_RECURSIVE_VK").unwrap()).unwrap();
    let prefix = match std::env::var("IX_STATEMENT_PREFIX") {
      Ok(words) => parse_prefix(&words).unwrap(),
      Err(_) => verifying_keys::STATEMENT_PREFIX,
    };
    let family = derive_merge_family(&recursive, prefix, &setup).unwrap();
    assert_eq!(family.len(), FAMILY.len());
    for (shape, vk) in FAMILY.iter().zip(&family) {
      let (verifier, _) =
        VerifyingKey::from_bytes(vk).unwrap().certificate_verifier().unwrap();
      let heights: Vec<_> =
        verifier.circuits.iter().map(|c| c.preprocessed_height).collect();
      eprintln!(
        "{shape:?}: heights {heights:?}, key {} bytes, BLAKE3 {}",
        vk.len(),
        blake3::hash(vk)
      );
    }
    if let Some(dir) = std::env::var_os("IX_MERGE_KEYS_OUT") {
      let dir = Path::new(&dir);
      fs::create_dir_all(dir).unwrap();
      fs::write(dir.join("recursive-vk.bin"), &recursive).unwrap();
      let words: Vec<_> = prefix.iter().map(u64::to_string).collect();
      fs::write(dir.join("statement-prefix.txt"), words.join(",")).unwrap();
      for (name, vk) in FAMILY_FILES.iter().zip(&family) {
        fs::write(dir.join(name), vk).unwrap();
      }
      Release::load(dir).unwrap();
    }
  }
}
