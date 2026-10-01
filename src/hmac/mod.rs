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

mod md5;
mod sha1;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

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

    /// The state of the computation (for PBKDF2's iteration, on the targets
    /// where it runs under Rust's loop).
    #[cfg(any(target_arch = "arm", target_arch = "x86"))]
    pub(crate) fn state(&self) -> &H::State {
        &self.state
    }
}

/// An HMAC computation with a hash function over verified streaming
/// primitives: the computation of the inner hash, whose message is
/// `(K₀ ⊕ ipad) ‖ text`, and the streaming state of the outer one, which
/// represents `K₀ ⊕ opad`.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
#[doc(hidden)]
#[derive(Clone)]
pub struct StreamingHmacState<H, const S: usize> {
    pub(crate) inner: H,
    pub(crate) outer: [u8; S],
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
impl<H, const S: usize> Drop for StreamingHmacState<H, S> {
    /// Wipes the outer state, which represents `K₀ ⊕ opad` (the inner hash
    /// wipes its own).
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.outer);
    }
}

/// Makes a hash function over verified streaming primitives (defined by
/// `streaming_hash!`) an [`HmacHash`], with its verified
/// `vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize` (contracts
/// `VG.Spec.Hmac.Instance.initContract` and `finalizeContract` of the hash's
/// `Instance`), given its streaming state size, the functions' working space
/// (in 64-bit words) and its digest size. The text is absorbed by the hash's
/// own `update`.
///
/// `init` and `finalize` are listed for each implementation of the hash (its
/// backend enum's variants, with the CPU features they need), and a
/// computation runs those of the implementation its hash was selected for:
/// the `match` on the backend is exhaustive, so a new implementation of the
/// hash does not compile until its HMAC functions are listed here too (see
/// "Variants and generic callers" in `lean/VerifiedGarbage/TCB/Emit.lean`),
/// and a test checks that they need no CPU feature the hash's
/// implementation was not selected for.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
macro_rules! streaming_hmac {
    (
        $hash:ident ($backend:ident) {
            $base:ident => ($init:path, $finalize:path)
            $(, $(#[$attr:meta])* $variant:ident if [$($req:path),*] => ($vinit:path, $vfinalize:path))*
            $(,)?
        },
        state: $state:literal,
        scratch: $scratch:literal,
        output: $output:literal $(,)?
    ) => {
        // The CPU features of each implementation, which `tests` checks.
        $(
            $(#[$attr])*
            const _: &[&[&str]] = &[$($req),*];
        )*

        impl super::sealed::Sealed for $hash {}

        impl super::HmacHash for $hash {
            type State = super::StreamingHmacState<$hash, $state>;

            fn hmac_init(key: &[u8]) -> Self::State {
                assert!(key.len() <= Self::BLOCK_SIZE);
                let backend = $backend::select($crate::cpu::detected());
                let init = match backend {
                    $backend::$base => $init,
                    $($(#[$attr])* $backend::$variant => $vinit,)*
                };
                let mut inner = [0; $state];
                let mut outer = [0; $state];
                let mut scratch = [0u64; $scratch];
                // SAFETY: `key.len()` is at most a block; `inner` and `outer`
                // are valid for reads and writes of a streaming state, `key`
                // for reads of `key.len()` bytes and `scratch` for reads and
                // writes of its size; they are distinct objects, so they do
                // not overlap each other or the call's stack frame, nor wrap
                // around the address space. `init` needs no CPU feature that
                // `backend` was not selected for (`tests::backend_features`).
                unsafe {
                    init(
                        &mut inner,
                        &mut outer,
                        key.as_ptr(),
                        key.len(),
                        &mut scratch,
                    )
                };
                // `inner` now represents `K₀ ⊕ ipad`, of a block.
                let state = super::StreamingHmacState {
                    inner: $hash::from_state(inner, Self::BLOCK_SIZE as u64, backend),
                    outer,
                };
                $crate::zeroize::zeroize(&mut inner);
                $crate::zeroize::zeroize(&mut outer);
                state
            }

            fn hmac_update(state: &mut Self::State, data: &[u8]) {
                state.inner.update(data);
            }

            fn hmac_finalize(state: Self::State) -> [u8; $output] {
                let finalize = match state.inner.backend() {
                    $backend::$base => $finalize,
                    $($(#[$attr])* $backend::$variant => $vfinalize,)*
                };
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
                // `state.outer` represents `K₀ ⊕ opad`. `finalize` needs no
                // CPU feature that the hash's implementation was not selected
                // for (`tests::backend_features`).
                unsafe { finalize(&mut inner, &state.outer, count, &mut mac, &mut scratch) };
                $crate::zeroize::zeroize(&mut inner);
                mac
            }
        }

        #[cfg(test)]
        mod tests {
            #[allow(unused_imports)]
            use super::*;

            /// Each implementation's `init` and `finalize` need no CPU
            /// feature that the hash's implementation is not selected for:
            /// on every set of features that selects it.
            #[test]
            fn backend_features() {
                $(
                    $(#[$attr])*
                    for bits in 0..1u32 << $crate::cpu::NAMES.len() {
                        let f = $crate::cpu::Features(bits);
                        if $backend::select(f) == $backend::$variant {
                            assert!(f.contains($crate::cpu::Features::all(&[$($req),*])));
                        }
                    }
                )*
            }
        }
    };
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
use streaming_hmac;
