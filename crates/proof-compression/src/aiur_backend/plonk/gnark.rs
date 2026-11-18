//! Compilation through the pinned gnark sparse PLONK backend.

use super::public_bytes;
use crate::kzg::Scalar;
pub use crate::pipeline::gnark::{Artifact, Backend, Proof};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, marker::PhantomData, rc::Rc};
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// Solidity/gnark anchor coordinates for independently authenticated KZG
/// parameters: G1, G2 and tau-G2, each base-field coordinate big-endian.
pub fn anchors(parameters: &crate::kzg::VerifierParams) -> Vec<u8> {
  use ark_ff::{BigInteger, PrimeField};
  let (g1, g2) = crate::aiur_backend::pairing::verifier_anchors(parameters);
  [
    g1[0].x, g1[0].y, g2[0].x.c0, g2[0].x.c1, g2[0].y.c0, g2[0].y.c1,
    g2[1].x.c0, g2[1].x.c1, g2[1].y.c0, g2[1].y.c1,
  ]
  .into_iter()
  .flat_map(|value| value.into_bigint().to_bytes_be())
  .collect()
}
pub use crate::pipeline::gnark::CircuitInfo;
use std::{ffi::c_void, path::Path};

#[allow(
  non_camel_case_types,
  non_snake_case,
  non_upper_case_globals,
  dead_code,
  unreachable_pub
)]
mod raw {
  include!(concat!(env!("OUT_DIR"), "/gnark_bindings.rs"));
}

struct Response(raw::ix_gnark_result);
impl Drop for Response {
  fn drop(&mut self) {
    // All buffers are owned by the archive's C allocator.
    unsafe {
      raw::ix_gnark_free(self.0.data.cast::<c_void>());
      raw::ix_gnark_free(self.0.solidity.cast::<c_void>());
      raw::ix_gnark_free(self.0.error.cast::<c_void>());
    }
  }
}

impl Response {
  fn checked(result: raw::ix_gnark_result) -> Result<Self> {
    let response = Self(result);
    if !response.0.error.is_null() {
      // The response owns the bounded error buffer until it is dropped.
      let bytes = unsafe {
        std::slice::from_raw_parts(response.0.error, response.0.error_len)
      };
      return Err(String::from_utf8_lossy(bytes).into_owned().into());
    }
    Ok(response)
  }
  fn bytes(&self) -> &[u8] {
    if self.0.len == 0 {
      return &[];
    }
    // The C allocation remains alive for this borrow.
    unsafe { std::slice::from_raw_parts(self.0.data, self.0.len) }
  }
}
fn view(data: &[u8]) -> raw::ix_gnark_view {
  raw::ix_gnark_view { data: data.as_ptr(), len: data.len() }
}
fn path(path: &Path) -> Result<&[u8]> {
  Ok(path.to_str().ok_or("gnark paths must be UTF-8")?.as_bytes())
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct Manifest {
  pub format: String,
  #[serde(rename = "ScsSHA256")]
  pub scs_sha256: String,
  #[serde(rename = "PairingSHA256")]
  pub pairing_sha256: String,
  #[serde(rename = "SRSBLAKE3")]
  pub srs_blake3: String,
  pub info: CircuitInfo,
  pub files: BTreeMap<String, Artifact>,
}

/// An `ix-aiur-scs-v1` file and the terminal's pairing configuration, each
/// with the SHA-256 it is pinned to.
#[derive(Serialize)]
#[serde(rename_all = "PascalCase")]
pub struct ScsSource<'a> {
  pub scs: &'a Path,
  #[serde(rename = "ScsSHA256")]
  pub scs_sha256: &'a str,
  pub pairing: &'a Path,
  #[serde(rename = "PairingSHA256")]
  pub pairing_sha256: &'a str,
}

#[derive(Serialize)]
#[serde(rename_all = "PascalCase")]
struct ScsCompile<'a> {
  #[serde(flatten)]
  source: &'a ScsSource<'a>,
  output: &'a Path,
}

/// Compile the Lean-exported constraint system: one gnark constraint per
/// file gate, gnark's pairing gadget on the outputs and the commitment over
/// the file's commit list.
pub fn compile_scs(
  source: &ScsSource<'_>,
  output: &Path,
) -> Result<CircuitInfo> {
  let bytes = serde_json::to_vec(&ScsCompile { source, output })?;
  // The native call retains no pointers into the serialized request.
  let response =
    Response::checked(unsafe { raw::ix_gnark_aiur_scs_compile(view(&bytes)) })?;
  Ok(serde_json::from_slice(response.bytes())?)
}

/// [`Preparation`] of a circuit compiled by [`compile_scs`]. The prepared
/// directory also holds the file's input layout (`inputs.json`, see
/// [`super::scs::Inputs`]) and the pairing configuration.
#[derive(Serialize)]
#[serde(rename_all = "PascalCase")]
pub struct ScsPreparation<'a> {
  #[serde(flatten)]
  pub source: &'a ScsSource<'a>,
  pub circuit: &'a Path,
  pub circuit_hash: &'a Artifact,
  pub info: &'a CircuitInfo,
  #[serde(rename = "SRS")]
  pub srs: &'a Path,
  #[serde(rename = "SRSBLAKE3")]
  pub srs_blake3: &'a str,
  pub lagrange: &'a Path,
  #[serde(rename = "LagrangeSHA256")]
  pub lagrange_sha256: &'a str,
  pub output: &'a Path,
}

pub fn prepare_scs(request: &ScsPreparation<'_>) -> Result<Manifest> {
  let bytes = serde_json::to_vec(request)?;
  // The native call retains no pointers into the serialized request.
  let response =
    Response::checked(unsafe { raw::ix_gnark_aiur_scs_prepare(view(&bytes)) })?;
  Ok(serde_json::from_slice(response.bytes())?)
}

/// A loaded Aiur circuit and proving key. Metadata must come from trusted
/// preparation or an independently authenticated artifact catalog.
pub struct Prover {
  handle: Option<usize>,
  _thread: PhantomData<Rc<()>>,
}
impl Prover {
  pub fn open(
    directory: &Path,
    manifest: &Manifest,
    backend: Backend,
  ) -> Result<Self> {
    let (cuda, device, memory_bytes, mask_msm) = match backend {
      Backend::Cpu => (0, 0, 0, 0),
      Backend::Cuda { device, memory_bytes, mask_msm } => {
        (1, device, memory_bytes, u32::from(mask_msm))
      },
    };
    let options =
      raw::ix_gnark_backend { cuda, device, memory_bytes, mask_msm };
    let metadata = serde_json::to_vec(manifest)?;
    // Go returns an integer handle, never a pointer into its heap.
    let response = Response::checked(unsafe {
      raw::ix_gnark_aiur_open(view(path(directory)?), view(&metadata), options)
    })?;
    if response.0.handle == 0 {
      return Err("gnark returned an empty Aiur prover handle".into());
    }
    Ok(Self { handle: Some(response.0.handle), _thread: PhantomData })
  }
  pub fn prove(
    &mut self,
    witness: &[u8],
    expected: &[Scalar],
  ) -> Result<Proof> {
    let expected = public_bytes(expected)?;
    let handle = self.handle.ok_or("Aiur prover is closed")?;
    // Exclusive access prevents concurrent proof generation or closing.
    let response = Response::checked(unsafe {
      raw::ix_gnark_aiur_prove(handle, view(witness), view(&expected))
    })?;
    let solidity = if response.0.solidity_len == 0 {
      Vec::new()
    } else {
      // Copy native allocations before dropping the response owner.
      unsafe {
        std::slice::from_raw_parts(response.0.solidity, response.0.solidity_len)
      }
      .to_vec()
    };
    Ok(Proof { native: response.bytes().to_vec(), solidity })
  }
  pub fn close(mut self) -> Result<()> {
    self.release()
  }
  fn release(&mut self) -> Result<()> {
    if let Some(handle) = self.handle.take() {
      // Taking the handle makes explicit close and Drop mutually exclusive.
      Response::checked(unsafe { raw::ix_gnark_close(handle) })?;
    }
    Ok(())
  }
}
impl Drop for Prover {
  fn drop(&mut self) {
    let _ = self.release();
  }
}

/// The verifier key digest and setup anchors are independent trust inputs;
/// expected public fields are supplied by the caller, never read from a proof.
pub fn verify(
  key: &[u8],
  trusted_digest: &[u8; 32],
  proof: &[u8],
  expected: &[Scalar],
  anchors: &[u8],
) -> Result<()> {
  let expected = public_bytes(expected)?;
  // Inputs remain borrowed until the synchronous verification call returns.
  Response::checked(unsafe {
    raw::ix_gnark_aiur_verify(
      view(key),
      view(trusted_digest),
      view(proof),
      view(&expected),
      view(anchors),
    )
  })?;
  Ok(())
}
