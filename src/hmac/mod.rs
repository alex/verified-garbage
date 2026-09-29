//! HMAC (FIPS 198-1, RFC 2104), for any hash function with a verified HMAC
//! implementation.
//!
//! The construction is the same for every hash function `H` ([`HmacHash`]);
//! what each one provides, in a module of its own here, is verified
//! assembly for a key of at most one block, which computes
//! `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`).
//! The only unverified step is step 2 of FIPS 198-1 §4: a key longer than a
//! block is first hashed, with the verified hash function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::hashes::HashFunction;

mod sha256;

mod sealed {
    pub trait Sealed {}
}

/// A hash function with a verified HMAC implementation.
///
/// Its digests must be at most a block long, so that a hashed key is a valid
/// key for [`HmacHash::hmac_init`].
pub trait HmacHash: HashFunction + sealed::Sealed {
    /// The state of an HMAC computation.
    #[doc(hidden)]
    type State: Clone;
    /// Starts an HMAC computation with a key of at most `BLOCK_SIZE` bytes,
    /// using only the CPU features in `mask` (as `__with_features`).
    ///
    /// # Panics
    ///
    /// If the key is longer than a block.
    #[doc(hidden)]
    fn hmac_init(key: &[u8], mask: u32) -> Self::State;
    /// Absorbs `data`.
    #[doc(hidden)]
    fn hmac_update(state: &mut Self::State, data: &[u8]);
    /// Returns the MAC.
    #[doc(hidden)]
    fn hmac_finalize(state: Self::State) -> Self::Output;
}

/// An incremental HMAC computation with the hash function `H`.
#[derive(Clone)]
pub struct Hmac<H: HmacHash> {
    state: H::State,
}

impl<H: HmacHash> Hmac<H> {
    /// Starts an HMAC computation with `key`, of any length (a key longer
    /// than the block size is hashed first).
    pub fn new(key: &[u8]) -> Self {
        Self::__with_features(key, u32::MAX)
    }

    /// Starts an HMAC computation with `key`, using only the CPU features in
    /// `mask` (a set of `crate::cpu::Features` bits). For testing every
    /// implementation on one CPU.
    #[doc(hidden)]
    pub fn __with_features(key: &[u8], mask: u32) -> Self {
        let state = if key.len() > H::BLOCK_SIZE {
            H::hmac_init(H::digest(key).as_ref(), mask)
        } else {
            H::hmac_init(key, mask)
        };
        Hmac { state }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        H::hmac_update(&mut self.state, data);
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(self) -> H::Output {
        H::hmac_finalize(self.state)
    }

    /// The MAC of `data` with `key`.
    pub fn mac(key: &[u8], data: &[u8]) -> H::Output {
        let mut h = Self::new(key);
        h.update(data);
        h.finalize()
    }
}
