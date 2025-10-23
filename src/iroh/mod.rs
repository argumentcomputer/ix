//! The client, server, and common modules are enabled by the `net` feature. However, Iroh doesn't work on `aarch64-darwin`, so they are always disabled for that target.
//!
//! Lean and C don't support feature flags, so the `_client` and `_server` modules are exposed as a fallback for when the `net` feature is disabled and/or on the `aarch64-darwin` target.
//!
//! These fallback modules contain dummy functions that can still be called via Lean->C->Rust FFI, but will return an error message that Lean then prints before exiting.

#[cfg(any(
    not(feature = "net"),
    all(target_os = "macos", target_arch = "aarch64")
))]
pub mod _client;
#[cfg(any(
    not(feature = "net"),
    all(target_os = "macos", target_arch = "aarch64")
))]
pub mod _server;
#[cfg(all(
    feature = "net",
    not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod client;
#[cfg(all(
    feature = "net",
    not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod server;
#[cfg(all(
    feature = "net",
    not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod common {
    use bincode::{Decode, Encode};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
    pub enum Request {
        Put(PutRequest),
        Get(GetRequest),
    }

    impl Request {
        pub fn to_bytes(&self) -> Vec<u8> {
            bincode::encode_to_vec(self, bincode::config::standard()).unwrap()
        }
        pub fn from_bytes(bytes: &[u8]) -> Self {
            bincode::decode_from_slice(bytes, bincode::config::standard())
                .unwrap()
                .0
        }
    }

    #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
    pub struct PutRequest {
        pub bytes: Vec<u8>,
    }

    #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
    pub struct GetRequest {
        pub hash: String,
    }

    #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
    pub enum Response {
        Put(PutResponse),
        Get(GetResponse),
    }

    impl Response {
        pub fn to_bytes(&self) -> Vec<u8> {
            bincode::encode_to_vec(self, bincode::config::standard()).unwrap()
        }
        pub fn from_bytes(bytes: &[u8]) -> Self {
            bincode::decode_from_slice(bytes, bincode::config::standard())
                .unwrap()
                .0
        }
    }

    #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
    pub struct PutResponse {
        pub is_err: bool,
        pub message: String,
        pub hash: String,
    }

    #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
    pub struct GetResponse {
        pub is_err: bool,
        pub message: String,
        pub hash: String,
        pub bytes: Vec<u8>,
    }
}
