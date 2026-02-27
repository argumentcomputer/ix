use iroh::{Endpoint, NodeAddr, NodeId, RelayMode, RelayUrl, SecretKey};
use n0_snafu::{Result, ResultExt};
use n0_watcher::Watcher as _;
use std::ffi::c_void;
use std::net::SocketAddr;
use tracing::info;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, fmt};

use crate::iroh::common::{GetRequest, PutRequest, Request, Response};
use crate::lean::array::LeanArrayObject;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_mut_unsafe, as_ref_unsafe, lean_alloc_ctor, lean_alloc_sarray,
  lean_ctor_set, lean_except_error_string, lean_except_ok, lean_mk_string,
  safe_cstring, sarray::LeanSArrayObject,
};

// An example ALPN that we are using to communicate over the `Endpoint`
const EXAMPLE_ALPN: &[u8] = b"n0/iroh/examples/magic/0";
// Maximum number of characters to read from the server. Connection automatically closed if this is exceeded
const READ_SIZE_LIMIT: usize = 100_000_000;

/// Build a Lean `PutResponse` structure:
/// ```
/// structure PutResponse where
///   message: String
///   hash: String
/// ```
fn mk_put_response(message: &str, hash: &str) -> *mut c_void {
  let c_message = safe_cstring(message);
  let c_hash = safe_cstring(hash);
  unsafe {
    let ctor = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(ctor, 0, lean_mk_string(c_message.as_ptr()));
    lean_ctor_set(ctor, 1, lean_mk_string(c_hash.as_ptr()));
    ctor
  }
}

/// Build a Lean `GetResponse` structure:
/// ```
/// structure GetResponse where
///   message: String
///   hash: String
///   bytes: ByteArray
/// ```
fn mk_get_response(message: &str, hash: &str, bytes: &[u8]) -> *mut c_void {
  let c_message = safe_cstring(message);
  let c_hash = safe_cstring(hash);
  unsafe {
    let byte_array = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let arr: &mut LeanSArrayObject = as_mut_unsafe(byte_array.cast());
    arr.set_data(bytes);

    let ctor = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(ctor, 0, lean_mk_string(c_message.as_ptr()));
    lean_ctor_set(ctor, 1, lean_mk_string(c_hash.as_ptr()));
    lean_ctor_set(ctor, 2, byte_array);
    ctor
  }
}

/// `Iroh.Connect.putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse`
#[unsafe(no_mangle)]
extern "C" fn c_rs_iroh_put(
  node_id: &LeanStringObject,
  addrs: &LeanArrayObject,
  relay_url: &LeanStringObject,
  input: &LeanStringObject,
) -> *mut c_void {
  let node_id = node_id.as_string();
  let addrs: Vec<String> = addrs.to_vec(|ptr| {
    let string: &LeanStringObject = as_ref_unsafe(ptr.cast());
    string.as_string()
  });
  let relay_url = relay_url.as_string();
  let input_str = input.as_string();

  let request =
    Request::Put(PutRequest { bytes: input_str.as_bytes().to_vec() });
  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  match rt.block_on(connect(&node_id, &addrs, &relay_url, request)) {
    Ok(response) => match response {
      Response::Put(put_response) => {
        lean_except_ok(mk_put_response(
          &put_response.message,
          &put_response.hash,
        ))
      },
      _ => lean_except_error_string("error: incorrect server response"),
    },
    Err(err) => lean_except_error_string(&err.to_string()),
  }
}

/// `Iroh.Connect.getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse`
#[unsafe(no_mangle)]
extern "C" fn c_rs_iroh_get(
  node_id: &LeanStringObject,
  addrs: &LeanArrayObject,
  relay_url: &LeanStringObject,
  hash: &LeanStringObject,
) -> *mut c_void {
  let node_id = node_id.as_string();
  let addrs: Vec<String> = addrs.to_vec(|ptr| {
    let string: &LeanStringObject = as_ref_unsafe(ptr.cast());
    string.as_string()
  });
  let relay_url = relay_url.as_string();
  let hash = hash.as_string();
  let request = Request::Get(GetRequest { hash: hash.clone() });

  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  match rt.block_on(connect(&node_id, &addrs, &relay_url, request)) {
    Ok(response) => match response {
      Response::Get(get_response) => {
        lean_except_ok(mk_get_response(
          &get_response.message,
          &get_response.hash,
          &get_response.bytes,
        ))
      },
      _ => lean_except_error_string("error: incorrect server response"),
    },
    Err(err) => lean_except_error_string(&err.to_string()),
  }
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
