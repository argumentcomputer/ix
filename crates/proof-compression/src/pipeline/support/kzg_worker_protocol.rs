//! Line-delimited JSON requests on stdin and responses in a file, for a
//! prover process that serves several proofs from one prepared frontend.
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
  collections::HashSet,
  fs::{self, File, OpenOptions},
  io::{self, BufRead, BufReader, BufWriter, Read, Write},
  path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const FORMAT: &str = "ix-compression-worker/v1";
const MAX_REQUEST_BYTES: u64 = 64 << 10;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Request {
  pub id: String,
  pub input: PathBuf,
  pub output: PathBuf,
  pub expected_claims: PathBuf,
}

pub(crate) struct Protocol<R: BufRead> {
  input: R,
  response: BufWriter<File>,
  binary: &'static str,
  seen: HashSet<String>,
  prepared: bool,
}

impl Protocol<BufReader<io::Stdin>> {
  pub(crate) fn open(path: &Path, binary: &'static str) -> Result<Self> {
    Self::with_reader(path, binary, BufReader::new(io::stdin()))
  }
}

impl<R: BufRead> Protocol<R> {
  pub(crate) fn with_reader(
    path: &Path,
    binary: &'static str,
    input: R,
  ) -> Result<Self> {
    let response =
      OpenOptions::new().write(true).create_new(true).open(path)?;
    let mut protocol = Self {
      input,
      response: BufWriter::new(response),
      binary,
      seen: HashSet::new(),
      prepared: false,
    };
    protocol
      .write(json!({"id": null, "status": "listening", "prepared": false}))?;
    Ok(protocol)
  }

  fn write(&mut self, mut response: Value) -> Result<()> {
    response["format"] = FORMAT.into();
    response["binary"] = self.binary.into();
    serde_json::to_writer(&mut self.response, &response)?;
    self.response.write_all(b"\n")?;
    self.response.flush()?;
    Ok(())
  }

  pub(crate) fn next_request(&mut self) -> Result<Option<Request>> {
    let mut bytes = Vec::new();
    Read::take(&mut self.input, MAX_REQUEST_BYTES + 1)
      .read_until(b'\n', &mut bytes)?;
    if bytes.is_empty() {
      return Ok(None);
    }
    if bytes.len() as u64 > MAX_REQUEST_BYTES || bytes.last() != Some(&b'\n') {
      return Err(
        "worker request exceeds its frame limit or is missing a newline".into(),
      );
    }
    let request: Request = serde_json::from_slice(&bytes)?;
    if request.id.is_empty()
      || request.id.len() > 128
      || request.input.as_os_str().is_empty()
      || request.output.as_os_str().is_empty()
      || request.expected_claims.as_os_str().is_empty()
    {
      return Err("worker request has an empty path or invalid id".into());
    }
    if !self.seen.insert(request.id.clone()) {
      return Err("worker request id was already used".into());
    }
    self.write(json!({
      "id": request.id,
      "status": "request_started",
      "prepared": self.prepared,
      "output": request.output,
    }))?;
    Ok(Some(request))
  }

  pub(crate) fn proved(
    &mut self,
    request: &Request,
    frontend_reused: bool,
    loaded_key_reused: bool,
    preparation_seconds: f64,
    request_seconds: f64,
    idle: &Value,
  ) -> Result<()> {
    flush_process_output()?;
    self.write(json!({
      "id": request.id,
      "status": "proved",
      "prepared": true,
      "frontend_reused": frontend_reused,
      "loaded_key_reused": loaded_key_reused,
      "preparation_seconds": preparation_seconds,
      "request_seconds": request_seconds,
      "output": request.output,
      "idle": idle,
    }))?;
    self.prepared = true;
    Ok(())
  }

  pub(crate) fn failed(&mut self, id: Option<&str>, error: &str) -> Result<()> {
    flush_process_output()?;
    self.write(json!({
      "id": id,
      "status": "failed",
      "prepared": self.prepared,
      "error": error,
    }))
  }
}

fn flush_process_output() -> io::Result<()> {
  io::stdout().flush()?;
  io::stderr().flush()?;
  // Native CUDA logging uses C stdio buffers independently of Rust's handles.
  unsafe extern "C" {
    fn fflush(stream: *mut std::ffi::c_void) -> std::ffi::c_int;
  }
  if unsafe { fflush(std::ptr::null_mut()) } != 0 {
    return Err(io::Error::last_os_error());
  }
  Ok(())
}

pub(crate) fn ensure_empty_output(path: &Path) -> Result<()> {
  match fs::read_dir(path) {
    Ok(mut entries) => {
      if entries.next().transpose()?.is_some() {
        Err("worker output must be empty".into())
      } else {
        Ok(())
      }
    },
    Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
    Err(error) => Err(error.into()),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::atomic::{AtomicUsize, Ordering};

  struct Directory(PathBuf);
  impl Directory {
    fn new() -> Self {
      static NEXT: AtomicUsize = AtomicUsize::new(0);
      let path = std::env::temp_dir().join(format!(
        "kzg-worker-protocol-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
      ));
      fs::create_dir(&path).unwrap();
      Self(path)
    }
  }
  impl Drop for Directory {
    fn drop(&mut self) {
      let _ = fs::remove_dir_all(&self.0);
    }
  }

  fn request(id: &str) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(&json!({
      "id": id, "input": "input with spaces", "output": "output", "expected_claims": "claims",
    }))
    .unwrap();
    bytes.push(b'\n');
    bytes
  }

  #[test]
  fn responses_are_flushed_ordered_and_prepared_only_after_proving()
  -> Result<()> {
    let directory = Directory::new();
    let path = directory.0.join("response.jsonl");
    let bytes = [request("a"), request("b"), request("a-again")].concat();
    let mut protocol = Protocol::with_reader(&path, "test", bytes.as_slice())?;
    let rows = || -> Result<Vec<Value>> {
      fs::read_to_string(&path)?
        .lines()
        .map(|line| Ok(serde_json::from_str(line)?))
        .collect()
    };
    assert_eq!(rows()?.len(), 1);
    assert_eq!(rows()?[0]["prepared"], false);
    for (index, id) in ["a", "b", "a-again"].into_iter().enumerate() {
      let request = protocol.next_request()?.unwrap();
      assert_eq!(request.id, id);
      let started = rows()?.pop().unwrap();
      assert_eq!(started["status"], "request_started");
      assert_eq!(started["prepared"], index != 0);
      protocol.proved(
        &request,
        index != 0,
        index != 0,
        0.0,
        1.0,
        &json!({"quiesced": false}),
      )?;
      assert_eq!(rows()?.last().unwrap()["status"], "proved");
    }
    assert!(protocol.next_request()?.is_none());
    protocol.failed(Some("bad"), "wrong statement")?;
    assert_eq!(rows()?.last().unwrap()["error"], "wrong statement");
    assert!(Protocol::with_reader(&path, "test", &b""[..]).is_err());
    Ok(())
  }

  #[test]
  fn rejects_malformed_duplicate_and_oversized_requests() -> Result<()> {
    let directory = Directory::new();
    for (index, bytes) in [
      b"{}\n".to_vec(),
      b"{\"id\":\"x\",\"input\":\"a\",\"output\":\"b\",\"expected_claims\":\"c\",\"extra\":0}\n".to_vec(),
      b"{\"id\":\"x\",\"id\":\"y\",\"input\":\"a\",\"output\":\"b\",\"expected_claims\":\"c\"}\n".to_vec(),
      request(""),
      request(&"x".repeat(129)),
      vec![b' '; usize::try_from(MAX_REQUEST_BYTES).unwrap() + 1],
      request("x")[..request("x").len() - 1].to_vec(),
    ]
    .into_iter()
    .enumerate()
    {
      let mut protocol = Protocol::with_reader(
        &directory.0.join(index.to_string()),
        "test",
        bytes.as_slice(),
      )?;
      assert!(protocol.next_request().is_err(), "case {index}");
    }
    let bytes = [request("repeat"), request("repeat")].concat();
    let mut protocol = Protocol::with_reader(
      &directory.0.join("duplicate"),
      "test",
      bytes.as_slice(),
    )?;
    assert!(protocol.next_request()?.is_some());
    assert!(protocol.next_request().is_err());
    let output = directory.0.join("out");
    ensure_empty_output(&output)?;
    fs::create_dir(&output)?;
    ensure_empty_output(&output)?;
    fs::write(output.join("proof.bin"), b"old proof")?;
    assert!(ensure_empty_output(&output).is_err());
    assert_eq!(fs::read(output.join("proof.bin"))?, b"old proof");
    Ok(())
  }
}
