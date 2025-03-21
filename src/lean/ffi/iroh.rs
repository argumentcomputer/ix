use anyhow::Result;
use iroh::{Endpoint, protocol::Router};
use iroh_blobs::{
    net_protocol::Blobs,
    rpc::client::blobs::WrapOption,
    store::{ExportFormat, ExportMode},
    ticket::BlobTicket,
    util::SetTagOption,
};
use std::error::Error;
use std::path::PathBuf;

use crate::lean::ffi::{c_char, raw_to_str};

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_send(filename: *const c_char) -> usize {
    // Create a Tokio runtime to block on the async function
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

    let path = raw_to_str(filename);
    println!("File path to send: {}", path);

    // Run the async function and get the result
    rt.block_on(iroh_send(path)).expect("Failed to send file");

    0
}

async fn iroh_send(filename: &str) -> Result<(), Box<dyn Error>> {
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
    let filename: PathBuf = filename.parse()?;
    let abs_path = std::path::absolute(&filename)?;

    println!("Hashing file.");

    // keep the file in place and link it, instead of copying it into the in-memory blobs database
    let in_place = true;
    let blob = blobs_client
        .add_from_path(abs_path, in_place, SetTagOption::Auto, WrapOption::NoWrap)
        .await?
        .finish()
        .await?;

    let node_id = router.endpoint().node_id();
    let ticket = BlobTicket::new(node_id.into(), blob.hash, blob.format)?;

    println!(
        "File hashed. Fetch the {} file by running the `iroh_recv` function with\nTicket: {ticket}",
        filename.display()
    );

    tokio::signal::ctrl_c().await?;
    router.shutdown().await?;

    Ok(())
}

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_recv(filename: *const c_char, ticket: *const c_char) -> usize {
    // Create a Tokio runtime to block on the async function
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

    let filename = raw_to_str(filename);
    let ticket = raw_to_str(ticket);

    // Run the async function and get the result
    rt.block_on(iroh_recv(filename, ticket))
        .expect("Failed to receive file");

    0
}

async fn iroh_recv(filename: &str, ticket: &str) -> Result<(), Box<dyn Error>> {
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

    println!("File path to receive: {filename}");
    println!("Ticket: {ticket}");

    let filename: PathBuf = filename.parse()?;
    let abs_path = std::path::absolute(&filename)?;

    println!("Abs path to receive: {}", abs_path.display());
    let ticket: BlobTicket = ticket.parse()?;

    println!("Starting download.");

    blobs_client
        .download(ticket.hash(), ticket.node_addr().clone())
        .await?
        .finish()
        .await?;

    println!("Finished download.");
    println!("Copying to destination.");

    blobs_client
        .export(
            ticket.hash(),
            abs_path,
            ExportFormat::Blob,
            ExportMode::Copy,
        )
        .await?
        .finish()
        .await?;

    println!("Finished copying.");
    router.shutdown().await?;

    Ok(())
}
