use anyhow::Result;
use bytes::Bytes;
use iroh::{Endpoint, protocol::Router};
use iroh_blobs::{net_protocol::Blobs, ticket::BlobTicket};
use std::error::Error;
use std::ffi::CString;

use crate::lean::ffi::raw_to_str;
use crate::lean::{
    ffi::{CResult, c_char, to_raw},
    sarray::LeanSArrayObject,
};

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_send(bytes: &LeanSArrayObject) -> *const CResult {
    // Create a Tokio runtime to block on the async function
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

    // Run the async function and block until we get the result
    let c_result = match rt.block_on(iroh_send(bytes.data())) {
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

async fn iroh_send(bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    // Create an endpoint, it allows creating and accepting
    // connections in the iroh p2p world
    let endpoint = Endpoint::builder().discovery_n0().bind().await?;
    // We initialize the Blobs protocol in-memory
    let blobs = Blobs::memory().build(&endpoint);

    // Now we build a router that accepts blobs connections & routes them
    // to the blobs protocol.
    let router = Router::builder(endpoint)
        .accept(iroh_blobs::ALPN, blobs.clone())
        .spawn()
        .await?;

    // We use a blobs client to interact with the blobs protocol we're running locally:
    let blobs_client = blobs.client();

    println!("Hashing bytes.");

    let blob = blobs_client
        .add_bytes(Bytes::copy_from_slice(bytes))
        .await?;

    let node_id = router.endpoint().node_id();
    let ticket = BlobTicket::new(node_id.into(), blob.hash, blob.format)?;

    println!(
        "Bytes hashed. Fetch them by by running the `iroh_recv` function with\nTicket: {ticket}",
    );

    // TODO: Shut down automatically after the file has been sent at least once
    tokio::signal::ctrl_c().await?;
    router.shutdown().await?;

    Ok(())
}

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_recv(
    ticket: *const c_char,
    buffer: &mut LeanSArrayObject,
    buffer_capacity: usize,
) -> *const CResult {
    // Create a Tokio runtime to block on the async function
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

    let ticket = raw_to_str(ticket);

    // Run the async function and block until we get the result
    let c_result = match rt.block_on(iroh_recv(ticket, buffer_capacity)) {
        Ok(bytes) => {
            let data = bytes.as_ref();
            buffer.set_data(data);
            CResult {
                is_ok: true,
                data: std::ptr::null(),
            }
        }
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

async fn iroh_recv(ticket: &str, buffer_capacity: usize) -> Result<Bytes, Box<dyn Error>> {
    // Create an endpoint, it allows creating and accepting
    // connections in the iroh p2p world
    let endpoint = Endpoint::builder().discovery_n0().bind().await?;
    // We initialize the Blobs protocol in-memory
    let blobs = Blobs::memory().build(&endpoint);

    // Now we build a router that accepts blobs connections & routes them
    // to the blobs protocol.
    let router = Router::builder(endpoint)
        .accept(iroh_blobs::ALPN, blobs.clone())
        .spawn()
        .await?;

    // We use a blobs client to interact with the blobs protocol we're running locally:
    let blobs_client = blobs.client();

    println!("Ticket to download: {ticket}");

    let ticket: BlobTicket = ticket.parse()?;
    let hash = ticket.hash();

    println!("Starting download.");

    blobs_client
        .download(hash, ticket.node_addr().clone())
        .await?
        .finish()
        .await?;

    println!("Finished download.");

    let mut reader = blobs_client.read(hash).await?;
    assert!(
        buffer_capacity >= usize::try_from(reader.size()).expect("Failed to convert u64 to usize")
    );
    let bytes = reader.read_to_bytes().await?;

    println!("Finished copying.");
    router.shutdown().await?;

    Ok(bytes)
}
