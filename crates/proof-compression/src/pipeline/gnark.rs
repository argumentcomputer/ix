//! Owned gnark objects behind the gnark archive's C ABI.
use super::Result;
use serde::Deserialize;
#[cfg(feature = "plonk")]
use serde::Serialize;
#[cfg(feature = "plonk")]
use std::collections::BTreeMap;
use std::{ffi::c_void, marker::PhantomData, path::Path, rc::Rc};

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

pub use super::final_proof::Artifact;

#[cfg(feature = "plonk")]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct Manifest {
  #[serde(rename = "InnerVKSHA256")]
  pub inner_vk_sha256: String,
  #[serde(rename = "SRSBLAKE3")]
  pub srs_blake3: String,
  pub keys_ready: bool,
  pub domain: u64,
  pub constraints: usize,
  pub public_inputs: usize,
  pub commitments: usize,
  pub files: BTreeMap<String, Artifact>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct CircuitInfo {
  pub domain: u64,
  pub constraints: usize,
  pub public_inputs: usize,
  pub commitments: usize,
}

#[cfg(feature = "plonk")]
#[derive(Clone, Copy, Debug, Default)]
pub enum Backend {
  #[default]
  Cpu,
  Cuda {
    device: i32,
    memory_bytes: u64,
    mask_msm: bool,
  },
}

pub struct Proof {
  pub native: Vec<u8>,
  pub solidity: Vec<u8>,
}

fn view(data: &[u8]) -> raw::ix_gnark_view {
  raw::ix_gnark_view { data: data.as_ptr(), len: data.len() }
}
fn path(path: &Path) -> Result<&[u8]> {
  Ok(path.to_str().ok_or("gnark paths must be UTF-8")?.as_bytes())
}
struct Response(raw::ix_gnark_result);
impl Drop for Response {
  fn drop(&mut self) {
    // All three buffers come from the Go adapter's C allocator.
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
      // The adapter owns a bounded error buffer until Response drops.
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
    // The response keeps this allocation alive for the returned borrow.
    unsafe { std::slice::from_raw_parts(self.0.data, self.0.len) }
  }
}

#[cfg(feature = "plonk")]
pub fn compile(schema: &[u8], circuit_path: &Path) -> Result<CircuitInfo> {
  // Inputs remain borrowed until the synchronous C call returns.
  let result =
    unsafe { raw::ix_gnark_compile(view(schema), view(path(circuit_path)?)) };
  Ok(serde_json::from_slice(Response::checked(result)?.bytes())?)
}

#[cfg(feature = "plonk")]
pub struct Preparation<'a> {
  pub schema: &'a [u8],
  pub circuit: &'a Path,
  pub circuit_hash: &'a Artifact,
  pub domain: u64,
  pub srs: &'a Path,
  pub srs_digest: &'a str,
  pub lagrange: &'a Path,
  pub lagrange_digest: &'a str,
  pub output: &'a Path,
}

#[cfg(feature = "plonk")]
pub fn prepare(request: &Preparation<'_>) -> Result<()> {
  // The adapter retains no Rust pointers after this call.
  let result = unsafe {
    raw::ix_gnark_prepare(
      view(request.schema),
      view(path(request.circuit)?),
      view(request.circuit_hash.sha256.as_bytes()),
      request.circuit_hash.bytes,
      request.domain,
      view(path(request.srs)?),
      view(request.srs_digest.as_bytes()),
      view(path(request.lagrange)?),
      view(request.lagrange_digest.as_bytes()),
      view(path(request.output)?),
    )
  };
  Response::checked(result)?;
  Ok(())
}

/// A loaded circuit and keys. Calls are exclusive; Drop releases the Go handle.
/// Artifact digests must come from trusted preparation or cache metadata.
pub struct Prover {
  handle: Option<usize>,
  _thread: PhantomData<Rc<()>>,
}
impl Prover {
  #[cfg(feature = "plonk")]
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
    // The handle returned by Go is an integer, never a Go heap pointer.
    let response = Response::checked(unsafe {
      raw::ix_gnark_open(view(path(directory)?), view(&metadata), options)
    })?;
    if response.0.handle == 0 {
      return Err("gnark returned an empty prover handle".into());
    }
    Ok(Self { handle: Some(response.0.handle), _thread: PhantomData })
  }

  pub fn prove(
    &mut self,
    witness: &[u8],
    expected_claim: &[u8; 32],
  ) -> Result<Proof> {
    let handle = self.handle.ok_or("prover is closed")?;
    // &mut self excludes close or another proof while Go uses this handle.
    let response = Response::checked(unsafe {
      raw::ix_gnark_prove(handle, view(witness), view(expected_claim))
    })?;
    let solidity = if response.0.solidity_len == 0 {
      Vec::new()
    } else {
      // Copy both outputs before releasing the C-owned response.
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

#[cfg(feature = "plonk")]
pub fn verify(
  key: &[u8],
  trusted_digest: &[u8; 32],
  proof: &[u8],
  claim: &[u8; 32],
  anchors: &[u8],
) -> Result<()> {
  // All inputs are borrowed only for the duration of the call.
  Response::checked(unsafe {
    raw::ix_gnark_verify(
      view(key),
      view(trusted_digest),
      view(proof),
      view(claim),
      view(anchors),
    )
  })?;
  Ok(())
}

#[cfg(all(test, feature = "plonk"))]
mod tests {
  use super::*;
  use crate::pipeline::final_proof::{decode_hex, digest};
  const KEY: &[u8] =
    include_bytes!("../../tests/fixtures/plonk/verifying-key.bin");
  const PROOF: &[u8] = include_bytes!("../../tests/fixtures/plonk/proof.bin");
  fn fixture() -> ([u8; 32], [u8; 32], Vec<u8>) {
    let p: serde_json::Value = serde_json::from_str(include_str!(
      "../../tests/fixtures/plonk/provenance.json"
    ))
    .unwrap();
    (
      digest(p["key_sha256"].as_str().unwrap()).unwrap(),
      digest(p["claim_digest"].as_str().unwrap()).unwrap(),
      decode_hex(p["anchors"].as_str().unwrap()).unwrap(),
    )
  }
  #[test]
  fn verifies_init_and_rejects_changed_claim_key_and_proof() {
    let (hash, claim, anchors) = fixture();
    verify(KEY, &hash, PROOF, &claim, &anchors).unwrap();
    let mut wrong = claim;
    wrong[0] ^= 1;
    assert!(verify(KEY, &hash, PROOF, &wrong, &anchors).is_err());
    let mut wrong = hash;
    wrong[0] ^= 1;
    assert!(verify(KEY, &wrong, PROOF, &claim, &anchors).is_err());
    let mut proof = PROOF.to_vec();
    proof[0] ^= 1;
    assert!(verify(KEY, &hash, &proof, &claim, &anchors).is_err());
    assert!(
      verify(KEY, &hash, &PROOF[..PROOF.len() - 1], &claim, &anchors).is_err()
    );
    let mut wrong = anchors.clone();
    wrong[0] ^= 1;
    assert!(verify(KEY, &hash, PROOF, &claim, &wrong).is_err());
  }
  #[test]
  fn invalid_handles_and_buffers_return_errors() {
    // Deliberately violate the raw ABI contract to exercise its validation.
    assert!(Response::checked(unsafe { raw::ix_gnark_close(0) }).is_err());
    let invalid = raw::ix_gnark_view { data: std::ptr::null(), len: 1 };
    assert!(
      Response::checked(unsafe {
        raw::ix_gnark_compile(invalid, view(b"unused"))
      })
      .is_err()
    );
    let oversized = raw::ix_gnark_view { data: b"x".as_ptr(), len: usize::MAX };
    assert!(
      Response::checked(unsafe {
        raw::ix_gnark_compile(oversized, view(b"unused"))
      })
      .is_err()
    );
  }
  #[test]
  #[ignore = "compiles the full Init verifier circuit"]
  fn compiles_init_without_changing_constraints() -> Result<()> {
    use sha2::Digest;
    let directory = crate::test_support::TempDir::new("gnark-compile");
    let schema =
      include_bytes!("../../../../tools/gnark/testdata/bn254/vk.json");
    let path = directory.join("circuit.bin");
    let info = compile(schema, &path)?;
    assert_eq!(info.constraints, 14689440);
    assert_eq!(info.domain, 1 << 24);
    assert_eq!(info.public_inputs, 2);
    let digest = sha2::Sha256::digest(std::fs::read(&path)?);
    assert_eq!(
      crate::pipeline::final_proof::hex(&digest),
      "a684964f61296fcda0df427980275764df242590373ce5680f70b0ac5dcfbded"
    );
    Ok(())
  }

  #[test]
  #[ignore = "requires the authenticated Init proving artifacts and tens of GiB of memory"]
  fn loaded_prover_reuses_keys() -> Result<()> {
    let dir =
      std::path::PathBuf::from(std::env::var("IX_GNARK_INIT_ARTIFACTS")?);
    let data = std::fs::read(dir.join("manifest.json"))?;
    let expected = std::env::var("IX_GNARK_INIT_MANIFEST_SHA256")?;
    use sha2::Digest;
    assert_eq!(
      crate::pipeline::final_proof::hex(&sha2::Sha256::digest(&data)),
      expected
    );
    let metadata: Manifest = serde_json::from_slice(&data)?;
    let witness = std::fs::read(std::env::var("IX_GNARK_INIT_WITNESS")?)?;
    let backend = crate::pipeline::plonk::proving_backend()?;
    let (hash, claim, anchors) = fixture();
    let mut prover = Prover::open(&dir, &metadata, backend)?;
    let mut wrong = claim;
    wrong[0] ^= 1;
    assert!(prover.prove(&witness, &wrong).is_err());
    let first = prover.prove(&witness, &claim)?;
    verify(KEY, &hash, &first.native, &claim, &anchors)?;
    let second = prover.prove(&witness, &claim)?;
    verify(KEY, &hash, &second.native, &claim, &anchors)?;
    assert_ne!(first.native, second.native);
    let handle = prover.handle.unwrap();
    prover.close()?;
    assert!(Response::checked(unsafe { raw::ix_gnark_close(handle) }).is_err());
    Ok(())
  }
}

#[cfg(feature = "groth16")]
pub(super) fn compile_groth16(
  schema: &[u8],
  output: &Path,
) -> Result<CircuitInfo> {
  // Both views are borrowed only until the native call returns.
  let response = Response::checked(unsafe {
    raw::ix_gnark_groth16_compile(view(schema), view(path(output)?))
  })?;
  Ok(serde_json::from_slice(response.bytes())?)
}

#[cfg(feature = "groth16")]
#[derive(Clone, Copy)]
pub(super) enum Groth16Setup<'a> {
  Development,
  Ceremony { path: &'a Path, digest: &'a str },
  Import { path: &'a Path, digest: &'a str },
}

#[cfg(feature = "groth16")]
pub(super) fn setup_groth16(
  directory: &Path,
  metadata: &super::groth16::Metadata,
  setup: Groth16Setup<'_>,
) -> Result<super::groth16::Metadata> {
  let (kind, descriptor, pin) = match setup {
    Groth16Setup::Development => (0, b"".as_slice(), ""),
    Groth16Setup::Ceremony { path: file, digest } => (1, path(file)?, digest),
    Groth16Setup::Import { path: file, digest } => (2, path(file)?, digest),
  };
  let encoded = serde_json::to_vec(metadata)?;
  // The adapter retains no Rust pointers while writing native keys.
  let response = Response::checked(unsafe {
    raw::ix_gnark_groth16_setup(
      view(path(directory)?),
      view(&encoded),
      kind,
      view(descriptor),
      view(pin.as_bytes()),
    )
  })?;
  Ok(serde_json::from_slice(response.bytes())?)
}

#[cfg(feature = "groth16")]
#[derive(Debug, Default)]
pub(super) enum Groth16Backend {
  #[default]
  Cpu,
  Cuda {
    device: i32,
    library: String,
  },
}

#[cfg(feature = "groth16")]
impl Prover {
  pub(super) fn open_groth16(
    directory: &Path,
    metadata: &super::groth16::Metadata,
    backend: &Groth16Backend,
  ) -> Result<Self> {
    let (cuda, device, library) = match backend {
      Groth16Backend::Cpu => (0, 0, ""),
      Groth16Backend::Cuda { device, library } => {
        (1, *device, library.as_str())
      },
    };
    let options = raw::ix_gnark_groth16_backend {
      cuda,
      device,
      library: view(library.as_bytes()),
    };
    let encoded = serde_json::to_vec(metadata)?;
    // The native handle owns the circuit, keys, and optional device allocations.
    let response = Response::checked(unsafe {
      raw::ix_gnark_groth16_open(
        view(path(directory)?),
        view(&encoded),
        options,
      )
    })?;
    if response.0.handle == 0 {
      return Err("gnark returned an empty prover handle".into());
    }
    Ok(Self { handle: Some(response.0.handle), _thread: PhantomData })
  }
}

#[cfg(feature = "groth16")]
pub(super) fn verify_groth16(
  key: &[u8],
  trusted: &[u8; 32],
  proof: &[u8],
  claim: &[u8; 32],
) -> Result<()> {
  // Input buffers remain alive throughout native verification.
  Response::checked(unsafe {
    raw::ix_gnark_groth16_verify(
      view(key),
      view(trusted),
      view(proof),
      view(claim),
    )
  })?;
  Ok(())
}
