//! PBKDF2 (RFC 8018 §5.2), with HMAC as the pseudorandom function: a module
//! here for each hash function with a verified implementation.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

mod sha256;

pub use sha256::pbkdf2_hmac_sha256;
