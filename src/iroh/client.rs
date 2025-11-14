use iroh::{Endpoint, NodeAddr, NodeId, RelayMode, RelayUrl, SecretKey};
use n0_snafu::{Result, ResultExt};
use n0_watcher::Watcher as _;
use std::ffi::{CString, c_char};
use std::net::SocketAddr;
use tracing::info;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, fmt};

use crate::iroh::common::{GetRequest, PutRequest, Request, Response};
use crate::lean::array::LeanArrayObject;
use crate::lean::as_ref_unsafe;
use crate::lean::ffi::iroh::{GetResponseFFI, PutResponseFFI};
use crate::lean::ffi::{CResult, raw_to_str, to_raw};
use crate::lean::string::LeanStringObject;

// An example ALPN that we are using to communicate over the `Endpoint`
const EXAMPLE_ALPN: &[u8] = b"n0/iroh/examples/magic/0";
// Maximum number of characters to read from the server. Connection automatically closed if this is exceeded
const READ_SIZE_LIMIT: usize = 100_000_000;

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
  node_id: *const c_char,
  addrs: &LeanArrayObject,
  relay_url: *const c_char,
  input: *const c_char,
) -> *const CResult {
  let node_id = raw_to_str(node_id);
  let addrs: Vec<String> = addrs.to_vec(|ptr| {
    let string: &LeanStringObject = as_ref_unsafe(ptr.cast());
    string.as_string()
  });
  let relay_url = raw_to_str(relay_url);
  let input = raw_to_str(input);

  let request = Request::Put(PutRequest { bytes: input.as_bytes().to_vec() });
  // Create a Tokio runtime to block on the async function
  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  // Run the async function and block until we get the result
  let c_result = match rt.block_on(connect(node_id, &addrs, relay_url, request))
  {
    Ok(response) => match response {
      Response::Put(put_response) => {
        let put_response_ffi =
          PutResponseFFI::new(&put_response.message, &put_response.hash);
        CResult { is_ok: true, data: to_raw(put_response_ffi).cast() }
      },
      _ => {
        let msg = CString::new("error: incorrect server response")
          .expect("CString::new failure");
        CResult { is_ok: false, data: msg.into_raw().cast() }
      },
    },
    Err(err) => {
      let msg = CString::new(err.to_string()).expect("CString::new failure");
      CResult { is_ok: false, data: msg.into_raw().cast() }
    },
  };

  to_raw(c_result)
}

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_get(
  node_id: *const c_char,
  addrs: &LeanArrayObject,
  relay_url: *const c_char,
  hash: *const c_char,
) -> *const CResult {
  let node_id = raw_to_str(node_id);
  let addrs: Vec<String> = addrs.to_vec(|ptr| {
    let string: &LeanStringObject = as_ref_unsafe(ptr.cast());
    string.as_string()
  });
  let relay_url = raw_to_str(relay_url);
  let hash = raw_to_str(hash);
  let request = Request::Get(GetRequest { hash: hash.to_owned() });

  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  let c_result = match rt.block_on(connect(node_id, &addrs, relay_url, request))
  {
    Ok(response) => match response {
      Response::Get(get_response) => {
        let get_response_ffi = GetResponseFFI::new(
          &get_response.message,
          &get_response.hash,
          &get_response.bytes,
        );
        CResult { is_ok: true, data: to_raw(get_response_ffi).cast() }
      },
      _ => {
        let msg = CString::new("error: incorrect server response")
          .expect("CString::new failure");
        CResult { is_ok: false, data: msg.into_raw().cast() }
      },
    },
    Err(err) => {
      let msg = CString::new(err.to_string()).expect("CString::new failure");
      CResult { is_ok: false, data: msg.into_raw().cast() }
    },
  };

  to_raw(c_result)
}

// Largely taken from https://github.com/n0-computer/iroh/blob/main/iroh/examples/connect.rs
async fn connect(
  node_id: &str,
  addrs: &[String],
  relay_url: &str,
  request: Request,
) -> Result<Response> {
  // Initialize the subscriber with `RUST_LOG=warn` to remove INFO noise for the client
  tracing_subscriber::registry()
    .with(fmt::layer())
    .with(EnvFilter::new("warn"))
    .init();
  let secret_key = SecretKey::generate(rand::rngs::OsRng);
  println!("public key: {}", secret_key.public());

  // Build a `Endpoint`, which uses PublicKeys as node identifiers, uses QUIC for directly connecting to other nodes, and uses the relay protocol and relay servers to holepunch direct connections between nodes when there are NATs or firewalls preventing direct connections. If no direct connection can be made, packets are relayed over the relay servers.
  let endpoint = Endpoint::builder()
        // The secret key is used to authenticate with other nodes. The PublicKey portion of this secret key is how we identify nodes, often referred to as the `node_id` in our codebase.
        .secret_key(secret_key)
        // Set the ALPN protocols this endpoint will accept on incoming connections
        .alpns(vec![EXAMPLE_ALPN.to_vec()])
        // `RelayMode::Default` means that we will use the default relay servers to holepunch and relay.
        // Use `RelayMode::Custom` to pass in a `RelayMap` with custom relay urls.
        // Use `RelayMode::Disable` to disable holepunching and relaying over HTTPS
        // If you want to experiment with relaying using your own relay server, you must pass in the same custom relay url to both the `listen` code AND the `connect` code
        .relay_mode(RelayMode::Default)
        // You can choose an address to bind to, but passing in `None` will bind the socket to a random available port
        .bind()
        .await?;

  let me = endpoint.node_id();
  println!("node id: {me}");
  println!("node listening addresses:");
  for local_endpoint in endpoint.direct_addresses().initialized().await {
    println!("\t{}", local_endpoint.addr)
  }

  // Build a `NodeAddr` from the node_id, relay url, and UDP addresses.
  let addr = NodeAddr::from_parts(
    node_id.parse::<NodeId>().with_context(|| "Node id parse error".into())?,
    Some(
      relay_url
        .parse::<RelayUrl>()
        .with_context(|| "Relay url parse error".into())?,
    ),
    addrs
      .iter()
      .map(|s| s.parse::<SocketAddr>().e())
      .collect::<Result<std::collections::BTreeSet<SocketAddr>>>()?,
  );

  // Attempt to connect, over the given ALPN.
  // Returns a Quinn connection.
  let conn = endpoint.connect(addr, EXAMPLE_ALPN).await?;
  info!("connected");

  // Use the Quinn API to send and recv content.
  let (mut send, mut recv) = conn.open_bi().await.e()?;

  send.write_all(&request.to_bytes()).await.e()?;

  // Call `finish` to close the send side of the connection gracefully.
  send.finish().e()?;
  let message = recv.read_to_end(READ_SIZE_LIMIT).await.e()?;
  let response = Response::from_bytes(&message);

  // We received the last message: close all connections and allow for the close
  // message to be sent.
  endpoint.close().await;

  Ok(response)
}
