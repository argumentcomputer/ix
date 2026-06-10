use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use iroh::{
  Endpoint, RelayMode, SecretKey,
  endpoint::{ConnectionError, presets},
};
use n0_error::StdResultExt;
use tracing::{debug, info, warn};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, fmt};

use crate::iroh::common::{ALPN, GetResponse, PutResponse, Request, Response};

// Maximum number of characters to read from the client. Connection automatically closed if this is exceeded
const READ_SIZE_LIMIT: usize = 100_000_000;
// Maximum number of concurrently-served connections. Connections beyond
// this are dropped at accept time so one set of slow/hostile peers cannot
// grow server memory without bound (each stream may buffer up to
// `READ_SIZE_LIMIT`).
const MAX_CONNECTIONS: usize = 64;
// Cap on total bytes pinned in the in-memory store. PUTs past this are
// refused (fail-closed) rather than growing memory unboundedly; eviction
// policy is left for the future file-backed store.
const MAX_STORE_BYTES: usize = 1 << 30; // 1 GiB

// Largely taken from https://github.com/n0-computer/iroh/blob/main/iroh/examples/listen.rs
pub async fn serve() -> n0_error::Result<()> {
  // Initialize the subscriber with `RUST_LOG=info` to preserve some server logging
  tracing_subscriber::registry()
    .with(fmt::layer())
    .with(EnvFilter::new("info"))
    .init();
  let secret_key = {
    let mut bytes = [0u8; 32];
    getrandom::fill(&mut bytes).expect("failed to generate random bytes");
    SecretKey::from(bytes)
  };
  println!("public key: {}", secret_key.public());

  // Build a `Endpoint`, which uses PublicKeys as node identifiers, uses QUIC for directly connecting to other nodes, and uses the relay protocol and relay servers to holepunch direct connections between nodes when there are NATs or firewalls preventing direct connections. If no direct connection can be made, packets are relayed over the relay servers.
  let endpoint = Endpoint::builder(presets::N0)
        // The secret key is used to authenticate with other nodes. The PublicKey portion of this secret key is how we identify nodes, often referred to as the `node_id` in our codebase.
        .secret_key(secret_key)
        // set the ALPN protocols this endpoint will accept on incoming connections
        .alpns(vec![ALPN.to_vec()])
        // `RelayMode::Default` means that we will use the default relay servers to holepunch and relay.
        // Use `RelayMode::Custom` to pass in a `RelayMap` with custom relay urls.
        // Use `RelayMode::Disable` to disable holepunching and relaying over HTTPS
        // If you want to experiment with relaying using your own relay server, you must pass in the same custom relay url to both the `listen` code AND the `connect` code
        .relay_mode(RelayMode::Default)
        // you can choose a port to bind to, but passing in `0` will bind the socket to a random available port
        .bind()
        .await?;

  let me = endpoint.id();
  println!("endpoint id: {me}");
  println!("endpoint listening addresses:");

  // wait for the endpoint to be online
  endpoint.online().await;
  let endpoint_addr = endpoint.addr();

  let local_addrs = endpoint_addr
    .ip_addrs()
    .map(|addr| {
      let addr = addr.to_string();
      println!("\t{addr}");
      addr
    })
    .collect::<Vec<_>>()
    .join(",");
  let relay_url = endpoint_addr.relay_urls().next().expect("missing relay");
  println!("endpoint relay server url: {relay_url}");
  println!("\nin a separate terminal run:");

  println!(
    "\tix connect put --node-id {me} --addrs {local_addrs} --relay-url {relay_url} <--input|--file> <input|/path/to/file>"
  );
  println!(
    "\tix connect get --node-id {me} --addrs {local_addrs} --relay-url {relay_url} <hash>"
  );

  // TODO: Switch to dashmap for performance or elsa/frozen map for safe append-only multithreading
  // TODO: Add a backing local file store rather than keeping data in-memory, and enable garbage
  // collection
  //
  // The map holds pinned blobs; the usize tracks total resident bytes so
  // PUTs can be refused once `MAX_STORE_BYTES` is reached.
  let store: Arc<Mutex<(BTreeMap<String, Vec<u8>>, usize)>> =
    Arc::new(Mutex::new((BTreeMap::new(), 0)));
  // Bounds concurrently-served connections; see `MAX_CONNECTIONS`.
  let conn_permits = Arc::new(tokio::sync::Semaphore::new(MAX_CONNECTIONS));
  // accept incoming connections, returns a normal QUIC connection
  while let Some(incoming) = endpoint.accept().await {
    let mut accepting = match incoming.accept() {
      Ok(accepting) => accepting,
      Err(err) => {
        warn!("incoming connection failed: {err:#}");
        // we can carry on in these cases:
        // this can be caused by retransmitted datagrams
        continue;
      },
    };
    let Ok(permit) = conn_permits.clone().try_acquire_owned() else {
      warn!(
        "connection limit ({MAX_CONNECTIONS}) reached, dropping incoming connection"
      );
      continue;
    };
    let store_clone = store.clone();
    // Spawn a task to handle the handshake plus reading and writing off of
    // the connection. Everything per-peer lives inside the task: an
    // `await?` in the accept loop lets a single failed or slow peer
    // handshake shut down — or head-of-line-block — the whole server.
    tokio::spawn(async move {
      let _permit = permit;
      let alpn = accepting.alpn().await?;
      let conn = accepting.await?;
      let endpoint_id = conn.remote_id();
      info!(
        "new connection from {endpoint_id} with ALPN {}",
        String::from_utf8_lossy(&alpn),
      );
      // accept a bi-directional QUIC connection
      // use the `quinn` APIs to send and recv content
      let (mut send, mut recv) = conn.accept_bi().await.anyerr()?;
      debug!("accepted bi stream, waiting for data...");
      let message = recv.read_to_end(READ_SIZE_LIMIT).await.anyerr()?;
      // Untrusted bytes: a malformed frame must only cost this connection,
      // never panic (with `panic = "abort"` that would kill the node).
      let request = match Request::from_bytes(&message) {
        Ok(request) => request,
        Err(err) => {
          warn!("dropping connection from {endpoint_id}: {err}");
          conn.close(1u32.into(), b"malformed request");
          return n0_error::Ok(());
        },
      };

      let response: Response = match request {
        Request::Put(put_request) => {
          let hash =
            blake3::hash(&put_request.bytes).to_hex().as_str().to_owned();
          let len = put_request.bytes.len();
          let mut guard = store_clone.lock().unwrap();
          let already_pinned = guard.0.contains_key(&hash);
          if !already_pinned && guard.1.saturating_add(len) > MAX_STORE_BYTES {
            let message = format!(
              "error: store full ({} bytes pinned, cap {MAX_STORE_BYTES})",
              guard.1
            );
            drop(guard);
            Response::Put(PutResponse { is_err: true, message, hash })
          } else {
            if !already_pinned {
              guard.1 += len;
              guard.0.insert(hash.clone(), put_request.bytes);
            }
            drop(guard);
            println!("received PUT request for bytes with hash {hash}");
            let message = format!("pinned hash {hash}\nat endpoint ID {me}");
            Response::Put(PutResponse { is_err: false, message, hash })
          }
        },
        Request::Get(get_request) => {
          println!(
            "received GET request for bytes with hash {}",
            get_request.hash
          );
          if let Some(bytes) =
            store_clone.lock().unwrap().0.get(&get_request.hash)
          {
            let message =
              format!("retrieved bytes for hash {}", get_request.hash);
            Response::Get(GetResponse {
              is_err: false,
              message,
              hash: get_request.hash,
              bytes: bytes.clone(),
            })
          } else {
            let message =
              String::from("error: failed to retrieve bytes at {hash}");
            Response::Get(GetResponse {
              is_err: true,
              message,
              hash: get_request.hash,
              bytes: vec![],
            })
          }
        },
      };

      let response_bytes = response.to_bytes();
      println!("sending {} byte response", response_bytes.len());
      send.write_all(&response_bytes).await.anyerr()?;
      println!("response sent, finishing stream");
      // call `finish` to close the connection gracefully
      send.finish().anyerr()?;
      println!("stream finished");

      // We sent the last message, so wait for the client to close the connection once
      // it received this message.
      let res = tokio::time::timeout(Duration::from_secs(3), async move {
        let closed = conn.closed().await;
        if !matches!(closed, ConnectionError::ApplicationClosed(_)) {
          println!(
            "endpoint {endpoint_id} disconnected with an error: {closed:#}"
          );
        }
      })
      .await;
      if res.is_err() {
        println!("endpoint {endpoint_id} did not disconnect within 3 seconds");
      }
      n0_error::Ok(())
    });
  }
  // stop with SIGINT (ctrl-c)

  Ok(())
}
