//! HMAC (FIPS 198-1, RFC 2104), for any hash function with a verified HMAC
//! implementation.
//!
//! The construction is the same for every hash function `H` ([`HmacHash`]);
//! what each one provides is verified assembly for a key of at most one
//! block. For SHA-256, `vg_hmac_sha256_init`, `vg_sha256_update` and
//! `vg_hmac_sha256_finalize` (contracts `VG.Spec.Hmac.initSha256X86_64`,
//! `VG.Spec.Sha256.updateX86_64` and `VG.Spec.Hmac.finalizeSha256X86_64`)
//! compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
//! (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-256 streaming states.
//! The only unverified step is step 2 of FIPS 198-1 §4: a key longer than a
//! block is first hashed, with the verified hash function.

use crate::asm::x86_64::hmac::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
use crate::asm::x86_64::sha256::vg_sha256_update;
use crate::hash::HashFunction;
use crate::sha256::Sha256;

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
    /// Starts an HMAC computation with a key of at most `BLOCK_SIZE` bytes.
    ///
    /// # Panics
    ///
    /// If the key is longer than a block.
    #[doc(hidden)]
    fn hmac_init(key: &[u8]) -> Self::State;
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
        let state = if key.len() > H::BLOCK_SIZE {
            H::hmac_init(H::digest(key).as_ref())
        } else {
            H::hmac_init(key)
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

/// An HMAC-SHA-256 computation: the SHA-256 streaming states for the inner
/// hash, which represents `(K₀ ⊕ ipad) ‖ text`, and the outer one, which
/// represents `K₀ ⊕ opad`, and the length of the inner message.
#[doc(hidden)]
#[derive(Clone)]
pub struct Sha256HmacState {
    inner: [u8; 96],
    outer: [u8; 96],
    /// The length of `(K₀ ⊕ ipad) ‖ text`, in bytes (modulo 2⁶⁴).
    count: u64,
}

impl sealed::Sealed for Sha256 {}

impl HmacHash for Sha256 {
    type State = Sha256HmacState;

    fn hmac_init(key: &[u8]) -> Sha256HmacState {
        assert!(key.len() <= Self::BLOCK_SIZE);
        let mut state = Sha256HmacState {
            inner: [0; 96],
            outer: [0; 96],
            count: Self::BLOCK_SIZE as u64,
        };
        let mut scratch = [0u64; 20];
        // SAFETY: `key.len()` is at most 64; `state.inner` and `state.outer`
        // are valid for reads and writes of 96 bytes, `key` for reads of
        // `key.len()` bytes and `scratch` for reads and writes of 160 bytes;
        // they are distinct objects, so they do not overlap each other or the
        // return address.
        unsafe {
            vg_hmac_sha256_init(
                &mut state.inner,
                &mut state.outer,
                key.as_ptr(),
                key.len(),
                &mut scratch,
            )
        };
        state
    }

    fn hmac_update(state: &mut Sha256HmacState, data: &[u8]) {
        let mut scratch = [0u64; 20];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `data` for reads of `data.len()` bytes and `scratch` for reads and
        // writes of 160 bytes; they are distinct objects, so they do not
        // overlap each other or the return address. `state.count` is the
        // length of the message `state.inner` represents, modulo 2⁶⁴.
        unsafe {
            vg_sha256_update(
                &mut state.inner,
                state.count,
                data.as_ptr(),
                data.len(),
                &mut scratch,
            )
        };
        state.count = state.count.wrapping_add(data.len() as u64);
    }

    fn hmac_finalize(mut state: Sha256HmacState) -> [u8; 32] {
        let mut scratch = [0u64; 30];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `state.outer` for reads of 96 bytes and `scratch` for reads and
        // writes of 240 bytes; they are distinct objects, so they do not
        // overlap each other or the return address. `state.inner` represents
        // `(K₀ ⊕ ipad) ‖ text`, of `state.count` bytes, and `state.outer`
        // represents `K₀ ⊕ opad`.
        unsafe {
            vg_hmac_sha256_finalize(&mut state.inner, &state.outer, state.count, &mut scratch)
        };
        // The MAC is in bytes 176 to 207 of `scratch`.
        let mut mac = [0u8; 32];
        for (out, word) in mac.as_chunks_mut::<8>().0.iter_mut().zip(&scratch[22..26]) {
            *out = word.to_ne_bytes();
        }
        mac
    }
}
