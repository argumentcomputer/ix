use iroh::{
  Endpoint, EndpointAddr, EndpointId, RelayMode, RelayUrl, SecretKey, TransportAddr,
  endpoint::presets,
};
use n0_error::{Result, StdResultExt};
use std::net::SocketAddr;
use tracing::info;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, fmt};

use crate::iroh::common::{Request, Response};

// An example ALPN that we are using to communicate over the `Endpoint`
const EXAMPLE_ALPN: &[u8] = b"n0/iroh/examples/magic/0";
// Maximum number of characters to read from the server. Connection automatically closed if this is exceeded
const READ_SIZE_LIMIT: usize = 100_000_000;

// Largely taken from https://github.com/n0-computer/iroh/blob/main/iroh/examples/connect.rs
pub async fn connect(
  node_id: &str,
  addrs: &[String],
  relay_url: &str,
  request: Request,
) -> Result<Response> {
  // Initialize the subscriber with `RUST_LOG=warn` to remove INFO noise for the client
  let _ = tracing_subscriber::registry()
    .with(fmt::layer())
    .with(EnvFilter::new("warn"))
    .try_init();
  let secret_key = SecretKey::generate(&mut rand::rng());
  println!("public key: {}", secret_key.public());

  // Build a `Endpoint`, which uses PublicKeys as node identifiers, uses QUIC for directly connecting to other nodes, and uses the relay protocol and relay servers to holepunch direct connections between nodes when there are NATs or firewalls preventing direct connections. If no direct connection can be made, packets are relayed over the relay servers.
  let endpoint = Endpoint::builder(presets::N0)
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

  // wait for the endpoint to be online
  endpoint.online().await;

  let endpoint_addr = endpoint.addr();
  let me = endpoint.id();
  println!("endpoint id: {me}");
  println!("endpoint listening addresses:");
  for addr in endpoint_addr.ip_addrs() {
    println!("\t{addr}")
  }

  // Build a `EndpointAddr` from the endpoint_id, relay url, and UDP addresses.
  let parsed_addrs = addrs
    .iter()
    .map(|s| s.parse::<SocketAddr>().map(TransportAddr::Ip))
    .collect::<std::result::Result<Vec<_>, _>>()
    .anyerr()?;
  let relay = relay_url.parse::<RelayUrl>().anyerr()?;
  let all_addrs =
    parsed_addrs.into_iter().chain(std::iter::once(TransportAddr::Relay(relay)));
  let addr = EndpointAddr::from_parts(
    node_id.parse::<EndpointId>().anyerr()?,
    all_addrs,
  );

  // Attempt to connect, over the given ALPN.
  // Returns a Quinn connection.
  let conn = endpoint.connect(addr, EXAMPLE_ALPN).await?;
  info!("connected");

  // Use the Quinn API to send and recv content.
  let (mut send, mut recv) = conn.open_bi().await.anyerr()?;

  send.write_all(&request.to_bytes()).await.anyerr()?;

  // Call `finish` to close the send side of the connection gracefully.
  send.finish().anyerr()?;
  let message = recv.read_to_end(READ_SIZE_LIMIT).await.anyerr()?;
  let response = Response::from_bytes(&message);

  // Close the connection, then wait for the endpoint to flush.
  conn.close(0u32.into(), b"done");
  endpoint.close().await;

  Ok(response)
}
