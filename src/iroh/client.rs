//! The smallest example showing how to use iroh and [`iroh::Endpoint`] to connect to a remote node.
//!
//! We use the node ID (the PublicKey of the remote node), the direct UDP addresses, and the relay url to achieve a connection.
//!
//! This example uses the default relay servers to attempt to holepunch, and will use that relay server to relay packets if the two devices cannot establish a direct UDP connection.
//!
//! Run the `listen` example first (`iroh/examples/listen.rs`), which will give you instructions on how to run this example to watch two nodes connect and exchange bytes.
//use std::net::SocketAddr;

//use iroh::{Endpoint, NodeAddr, RelayMode, RelayUrl, SecretKey};
use iroh::{Endpoint, NodeAddr, RelayMode, SecretKey};
use n0_snafu::{Result, ResultExt};
use n0_watcher::Watcher as _;
use std::ffi::{CString, c_char};
use std::fs::File;
use std::io::Write;
//use std::path::PathBuf;
use tracing::info;

use crate::iroh::common::{GetRequest, PutRequest, Request, Response};
use crate::lean::array::LeanArrayObject;
use crate::lean::as_ref_unsafe;
use crate::lean::ffi::{CResult, raw_to_str, to_raw};
use crate::lean::string::LeanStringObject;

// An example ALPN that we are using to communicate over the `Endpoint`
const EXAMPLE_ALPN: &[u8] = b"n0/iroh/examples/magic/0";

fn lean_unbox_str(ptr: *const std::ffi::c_void) -> String {
    let string: &LeanStringObject = as_ref_unsafe(ptr.cast());
    string.as_string()
}

// TODO: Make all the params a single struct to simplify FFI
// TODO: Return hash to Lean
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
    node_id: *const c_char,
    addrs: &LeanArrayObject,
    relay_url: *const c_char,
    file_path: *const c_char,
) -> *const CResult {
    let node_id = raw_to_str(node_id);
    let addrs: Vec<String> = addrs.to_vec(lean_unbox_str);
    println!("Addrs: {addrs:?}");
    let relay_url = raw_to_str(relay_url);
    let file_path = raw_to_str(file_path);

    let contents = std::fs::read_to_string(file_path).expect("Failed to read input file from disk");
    let request = Request::Put(PutRequest {
        bytes: contents.as_bytes().to_owned(),
    });
    // Create a Tokio runtime to block on the async function
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

    // Run the async function and block until we get the result
    let c_result = match rt.block_on(connect(node_id, &addrs, relay_url, request)) {
        Ok(_) => CResult {
            is_ok: true,
            data: std::ptr::null(),
        },
        Err(err) => {
            let msg = CString::new(err.to_string()).expect("CString::new failure");
            CResult {
                is_ok: false,
                data: msg.into_raw().cast(),
            }
        }
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
    let addrs: Vec<String> = addrs.to_vec(lean_unbox_str);
    let relay_url = raw_to_str(relay_url);
    let hash = raw_to_str(hash);
    let request = Request::Get(GetRequest {
        hash: hash.to_owned(),
    });

    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

    let c_result = match rt.block_on(connect(node_id, &addrs, relay_url, request)) {
        Ok(_) => CResult {
            is_ok: true,
            data: std::ptr::null(),
        },
        Err(err) => {
            let msg = CString::new(err.to_string()).expect("CString::new failure");
            CResult {
                is_ok: false,
                data: msg.into_raw().cast(),
            }
        }
    };

    to_raw(c_result)
}

// Largely inspired by https://github.com/n0-computer/iroh/blob/main/iroh/examples/connect.rs
async fn connect(node_id: &str, addrs: &[String], relay_url: &str, request: Request) -> Result<()> {
    //async fn connect(
    //    node_id: &str,
    //    addrs: Vec<String>,
    //    //addrs: &str,
    //    relay_url: &str,
    //    request: Request,
    //) -> Result<()> {
    tracing_subscriber::fmt::init();
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
        node_id.parse()?,
        Some(relay_url.parse()?),
        //[addrs.parse().unwrap()],
        addrs.into_iter().map(|s| s.parse().unwrap()),
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
    let message = recv.read_to_end(1000).await.e()?;
    //let message = String::from_utf8(message).e()?;
    let response = Response::from_bytes(&message);
    match response {
        Response::Put(put_response) => {
            println!("{}", put_response.message);
        }
        Response::Get(get_response) => {
            println!("{}", get_response.message);
            if !get_response.is_err {
                let file_name = format!("{}.txt", get_response.hash);
                println!("Writing bytes to ./{file_name}");
                let mut file = File::create(file_name).unwrap();
                file.write_all(&get_response.bytes).unwrap();
            }
        }
    }

    // We received the last message: close all connections and allow for the close
    // message to be sent.
    endpoint.close().await;
    Ok(())
}
