use std::collections::BTreeMap;
use std::ffi::c_void;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use iroh::{Endpoint, RelayMode, SecretKey, endpoint::ConnectionError};
use n0_snafu::ResultExt;
use n0_watcher::Watcher as _;
use tracing::{debug, info, warn};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, fmt};

use crate::iroh::common::{GetResponse, PutResponse, Request, Response};
use crate::lean::{lean_box_fn, lean_except_error_string, lean_except_ok};

// An example ALPN that we are using to communicate over the `Endpoint`
const EXAMPLE_ALPN: &[u8] = b"n0/iroh/examples/magic/0";
// Maximum number of characters to read from the client. Connection automatically closed if this is exceeded
const READ_SIZE_LIMIT: usize = 100_000_000;

/// `Iroh.Serve.serve' : Unit → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn c_rs_iroh_serve() -> *mut c_void {
  // Create a Tokio runtime to block on the async function
  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  // Run the async function and block until we get the result
  match rt.block_on(serve()) {
    Ok(()) => lean_except_ok(lean_box_fn(0)),
    Err(err) => lean_except_error_string(&err.to_string()),
  }
}

// Largely taken from https://github.com/n0-computer/iroh/blob/main/iroh/examples/listen.rs
async fn serve() -> n0_snafu::Result<()> {
  // Initialize the subscriber with `RUST_LOG=info` to preserve some server logging
  tracing_subscriber::registry()
    .with(fmt::layer())
    .with(EnvFilter::new("info"))
    .init();
  let secret_key = SecretKey::generate(rand::rngs::OsRng);
  println!("public key: {}", secret_key.public());

  // Build a `Endpoint`, which uses PublicKeys as node identifiers, uses QUIC for directly connecting to other nodes, and uses the relay protocol and relay servers to holepunch direct connections between nodes when there are NATs or firewalls preventing direct connections. If no direct connection can be made, packets are relayed over the relay servers.
  let endpoint = Endpoint::builder()
        // The secret key is used to authenticate with other nodes. The PublicKey portion of this secret key is how we identify nodes, often referred to as the `node_id` in our codebase.
        .secret_key(secret_key)
        // set the ALPN protocols this endpoint will accept on incoming connections
        .alpns(vec![EXAMPLE_ALPN.to_vec()])
        // `RelayMode::Default` means that we will use the default relay servers to holepunch and relay.
        // Use `RelayMode::Custom` to pass in a `RelayMap` with custom relay urls.
        // Use `RelayMode::Disable` to disable holepunching and relaying over HTTPS
        // If you want to experiment with relaying using your own relay server, you must pass in the same custom relay url to both the `listen` code AND the `connect` code
        .relay_mode(RelayMode::Default)
        // you can choose a port to bind to, but passing in `0` will bind the socket to a random available port
        .bind()
        .await?;

  let me = endpoint.node_id();
  println!("node id: {me}");
  println!("node listening addresses:");

  let local_addrs = endpoint
    .direct_addresses()
    .initialized()
    .await
    .into_iter()
    .map(|addr| {
      let addr = addr.addr.to_string();
      println!("\t{addr}");
      addr
    })
    .collect::<Vec<_>>()
    .join(" ");
  let relay_url = endpoint.home_relay().initialized().await;
  println!("node relay server url: {relay_url}");
  println!("\nin a separate terminal run:");

  println!(
    "\tix connect put --node-id {me} --addrs \"{local_addrs}\" --relay-url {relay_url} <--input|--file> <input|/path/to/file>"
  );
  println!(
    "\tix connect get --node-id {me} --addrs \"{local_addrs}\" --relay-url {relay_url} <hash>"
  );

  // TODO: Switch to dashmap for performance or elsa/frozen map for safe append-only multithreading
  // TODO: Add a backing local file store rather than keeping data in-memory, and enable garbage
  // collection
  let store: Arc<Mutex<BTreeMap<String, Vec<u8>>>> =
    Arc::new(Mutex::new(BTreeMap::new()));
  // accept incoming connections, returns a normal QUIC connection
  while let Some(incoming) = endpoint.accept().await {
    let mut connecting = match incoming.accept() {
      Ok(connecting) => connecting,
      Err(err) => {
        warn!("incoming connection failed: {err:#}");
        // we can carry on in these cases:
        // this can be caused by retransmitted datagrams
        continue;
      },
    };
    let alpn = connecting.alpn().await?;
    let conn = connecting.await.e()?;
    let node_id = conn.remote_node_id()?;
    info!(
      "new connection from {node_id} with ALPN {}",
      String::from_utf8_lossy(&alpn),
    );
    let store_clone = store.clone();
    // spawn a task to handle reading and writing off of the connection
    tokio::spawn(async move {
      // accept a bi-directional QUIC connection
      // use the `quinn` APIs to send and recv content
      let (mut send, mut recv) = conn.accept_bi().await.e()?;
      debug!("accepted bi stream, waiting for data...");
      let message = recv.read_to_end(READ_SIZE_LIMIT).await.e()?;
      let request = Request::from_bytes(&message);

      let response: Response = match request {
        Request::Put(put_request) => {
          let hash =
            blake3::hash(&put_request.bytes).to_hex().as_str().to_owned();
          store_clone.lock().unwrap().insert(hash.clone(), put_request.bytes);
          println!("received PUT request for bytes with hash {hash}");
          let message = format!("pinned hash {hash}\nat node ID {me}");
          Response::Put(PutResponse { is_err: false, message, hash })
        },
        Request::Get(get_request) => {
          println!(
            "received GET request for bytes with hash {}",
            get_request.hash
          );
          if let Some(bytes) =
            store_clone.lock().unwrap().get(&get_request.hash)
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

      send.write_all(&response.to_bytes()).await.e()?;
      // call `finish` to close the connection gracefully
      send.finish().e()?;

      // We sent the last message, so wait for the client to close the connection once
      // it received this message.
      let res = tokio::time::timeout(Duration::from_secs(3), async move {
        let closed = conn.closed().await;
        if !matches!(closed, ConnectionError::ApplicationClosed(_)) {
          println!("node {node_id} disconnected with an error: {closed:#}");
        }
      })
      .await;
      if res.is_err() {
        println!("node {node_id} did not disconnect within 3 seconds");
      }
      Ok::<_, n0_snafu::Error>(())
    });
  }
  // stop with SIGINT (ctrl-c)

  Ok(())
}
