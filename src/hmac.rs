//! HMAC (FIPS 198-1, RFC 2104), for any hash function with a verified HMAC
//! implementation.
//!
//! The construction is the same for every hash function `H` ([`HmacHash`]);
//! what each one provides is verified assembly for a key of at most one
//! block. For SHA-256, `vg_hmac_sha256_init`, `vg_sha256_update` and
//! `vg_hmac_sha256_finalize` (contracts `VG.Spec.Hmac.initSha256Contract`,
//! `VG.Spec.Sha256.updateContract` and `VG.Spec.Hmac.finalizeSha256Contract`,
//! or `finalizeSha256OutContract` on the 32-bit targets) compute
//! `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
//! (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-256 streaming states.
//! (`vg_sha256_update` is whichever implementation `Sha256` would use on
//! this CPU, e.g. `vg_sha256_update_shani`, with the same contract.)
//! On x86-64, SHA-1, MD5, SHA-384, SHA-512, SHA-512/224 and SHA-512/256 are
//! also HMAC hash functions: `vg_hmac_<hash>_init` and
//! `vg_hmac_<hash>_finalize` (contracts `VG.Spec.Hmac.Instance.initContract`
//! and `finalizeContract` of that hash's `Instance`, e.g.
//! `VG.Spec.Hmac.sha384I`) call that hash's verified streaming functions,
//! and the text is absorbed by its `update` (`StreamingHmacState`).
//! The only unverified step is step 2 of FIPS 198-1 §4: a key longer than a
//! block is first hashed, with the verified hash function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::hmac::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
#[cfg(target_arch = "arm")]
use crate::asm::arm::hmac::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
#[cfg(target_arch = "x86")]
use crate::asm::x86::hmac::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::hmac::{
    vg_hmac_md5_finalize, vg_hmac_md5_init, vg_hmac_sha1_finalize, vg_hmac_sha1_init,
    vg_hmac_sha256_finalize, vg_hmac_sha256_init, vg_hmac_sha384_finalize, vg_hmac_sha384_init,
    vg_hmac_sha512_224_finalize, vg_hmac_sha512_224_init, vg_hmac_sha512_256_finalize,
    vg_hmac_sha512_256_init, vg_hmac_sha512_finalize, vg_hmac_sha512_init,
};
use crate::hashes::HashFunction;
use crate::hashes::sha256::{Sha256, Sha256Backend};
#[cfg(target_arch = "x86_64")]
use crate::hashes::{
    md5::Md5,
    sha1::Sha1,
    sha512::{Sha384, Sha512, Sha512_224, Sha512_256},
};

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

    /// The state of the computation.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn state(&self) -> &H::State {
        &self.state
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
impl Hmac<Sha256> {
    /// The key's two SHA-256 streaming states, for `K₀ ⊕ ipad` and then
    /// `K₀ ⊕ opad`, as `vg_hmac_sha256_init` left them (the arguments of
    /// `vg_pbkdf2_hmac_sha256_iterate`), for a computation that has not
    /// absorbed any data yet.
    pub(crate) fn sha256_key_states(&self) -> [u8; 192] {
        debug_assert_eq!(self.state.count, Sha256::BLOCK_SIZE as u64);
        let mut key = [0u8; 192];
        key[..96].copy_from_slice(&self.state.inner);
        key[96..].copy_from_slice(&self.state.outer);
        key
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
    /// The implementation of `vg_sha256_update` this CPU runs.
    backend: Sha256Backend,
}

impl sealed::Sealed for Sha256 {}

impl HmacHash for Sha256 {
    type State = Sha256HmacState;

    fn hmac_init(key: &[u8], mask: u32) -> Sha256HmacState {
        assert!(key.len() <= Self::BLOCK_SIZE);
        let mut state = Sha256HmacState {
            inner: [0; 96],
            outer: [0; 96],
            count: Self::BLOCK_SIZE as u64,
            backend: Sha256Backend::select(crate::cpu::available(mask)),
        };
        let mut scratch = [0u64; 20];
        // SAFETY: `key.len()` is at most 64; `state.inner` and `state.outer`
        // are valid for reads and writes of 96 bytes, `key` for reads of
        // `key.len()` bytes and `scratch` for reads and writes of 160 bytes;
        // they are distinct objects, so they do not overlap each other or the
        // call's stack frame, nor wrap around the address space.
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
        // overlap each other or the call's stack frame, nor wrap around the
        // address space. `state.count` is the length of the message
        // `state.inner` represents, modulo 2⁶⁴. `state.backend` was
        // selected for this CPU's features.
        unsafe {
            state.backend.update(
                &mut state.inner,
                state.count,
                data.as_ptr(),
                data.len(),
                &mut scratch,
            )
        };
        state.count = state.count.wrapping_add(data.len() as u64);
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    fn hmac_finalize(mut state: Sha256HmacState) -> [u8; 32] {
        let mut scratch = [0u64; 30];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `state.outer` for reads of 96 bytes and `scratch` for reads and
        // writes of 240 bytes; they are distinct objects, so they do not
        // overlap each other or (on x86-64) the return address. `state.inner`
        // represents `(K₀ ⊕ ipad) ‖ text`, of `state.count` bytes, and
        // `state.outer` represents `K₀ ⊕ opad`.
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

    #[cfg(any(target_arch = "arm", target_arch = "x86"))]
    fn hmac_finalize(mut state: Sha256HmacState) -> [u8; 32] {
        let mut mac = [0u8; 32];
        let mut scratch = [0u64; 30];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `state.outer` for reads of 96 bytes, `mac` for writes of 32 bytes
        // and `scratch` for reads and writes of 240 bytes; they are distinct
        // objects, so they do not overlap each other or the call's stack
        // frame, nor wrap around the address space. `state.inner` represents
        // `(K₀ ⊕ ipad) ‖ text`, of `state.count` bytes, and `state.outer`
        // represents `K₀ ⊕ opad`.
        unsafe {
            vg_hmac_sha256_finalize(
                &mut state.inner,
                &state.outer,
                state.count,
                &mut mac,
                &mut scratch,
            )
        };
        mac
    }
}

/// An HMAC computation with a hash function over verified streaming
/// primitives: the computation of the inner hash, whose message is
/// `(K₀ ⊕ ipad) ‖ text`, and the streaming state of the outer one, which
/// represents `K₀ ⊕ opad`.
#[cfg(target_arch = "x86_64")]
#[doc(hidden)]
#[derive(Clone)]
pub struct StreamingHmacState<H, const S: usize> {
    pub(crate) inner: H,
    pub(crate) outer: [u8; S],
}

/// Makes each hash function an [`HmacHash`] with its verified
/// `vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize`, given its streaming
/// state size, its working space (in 64-bit words) and its digest size.
#[cfg(target_arch = "x86_64")]
macro_rules! streaming_hmac {
    ($($hash:ident: ($init:path, $finalize:path), state: $state:literal, scratch: $scratch:literal, output: $output:literal;)*) => {$(
        impl sealed::Sealed for $hash {}

        impl HmacHash for $hash {
            type State = StreamingHmacState<$hash, $state>;

            fn hmac_init(key: &[u8], mask: u32) -> Self::State {
                assert!(key.len() <= Self::BLOCK_SIZE);
                let mut inner = [0; $state];
                let mut outer = [0; $state];
                let mut scratch = [0u64; $scratch];
                // SAFETY: `key.len()` is at most a block; `inner` and `outer`
                // are valid for reads and writes of a streaming state, `key`
                // for reads of `key.len()` bytes and `scratch` for reads and
                // writes of its size; they are distinct objects, so they do
                // not overlap each other or the call's stack frame, nor wrap
                // around the address space.
                unsafe { $init(&mut inner, &mut outer, key.as_ptr(), key.len(), &mut scratch) };
                // `inner` now represents `K₀ ⊕ ipad`, of a block.
                StreamingHmacState {
                    inner: $hash::from_state(inner, Self::BLOCK_SIZE as u64, mask),
                    outer,
                }
            }

            fn hmac_update(state: &mut Self::State, data: &[u8]) {
                state.inner.update(data);
            }

            fn hmac_finalize(state: Self::State) -> [u8; $output] {
                let (mut inner, count) = state.inner.state();
                let mut mac = [0; $output];
                let mut scratch = [0u64; $scratch];
                // SAFETY: `inner` is valid for reads and writes of a streaming
                // state, `state.outer` for reads of one, `mac` for writes of
                // a digest and `scratch` for reads and writes of its size;
                // they are distinct objects, so they do not overlap each
                // other or the call's stack frame, nor wrap around the
                // address space. `inner` represents `(K₀ ⊕ ipad) ‖ text`, of
                // `count` bytes (which the hash's `update` keeps below 2⁶⁴,
                // so the text is shorter than 2⁶⁴ − B bytes), and
                // `state.outer` represents `K₀ ⊕ opad`.
                unsafe { $finalize(&mut inner, &state.outer, count, &mut mac, &mut scratch) };
                mac
            }
        }
    )*};
}

#[cfg(target_arch = "x86_64")]
streaming_hmac! {
    Sha1: (vg_hmac_sha1_init, vg_hmac_sha1_finalize), state: 84, scratch: 56, output: 20;
    Md5: (vg_hmac_md5_init, vg_hmac_md5_finalize), state: 80, scratch: 48, output: 16;
    Sha384: (vg_hmac_sha384_init, vg_hmac_sha384_finalize), state: 192, scratch: 96, output: 48;
    Sha512: (vg_hmac_sha512_init, vg_hmac_sha512_finalize), state: 192, scratch: 96, output: 64;
    Sha512_224: (vg_hmac_sha512_224_init, vg_hmac_sha512_224_finalize), state: 192, scratch: 96, output: 28;
    Sha512_256: (vg_hmac_sha512_256_init, vg_hmac_sha512_256_finalize), state: 192, scratch: 96, output: 32;
}
