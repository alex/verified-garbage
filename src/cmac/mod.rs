//! CMAC (NIST SP 800-38B, RFC 4493): a MAC built from a block cipher.
//!
//! Each block cipher with a verified CMAC implementation has a module of its
//! own here: [`aes`].

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

pub mod aes;

/// The key does not have a length the block cipher accepts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidKeyLength;

pub use crate::hmac::InvalidMac;
