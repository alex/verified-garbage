//! BLAKE2s (RFC 7693): digests of 1 to 32 bytes, unkeyed or keyed with up
//! to 32 bytes, over 32-bit words (see `blake2` for how the verified
//! functions are used).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::blake2s::{vg_blake2s_finalize, vg_blake2s_init, vg_blake2s_update};

super::blake2::blake2!(
    /// An incremental BLAKE2s computation of an `N`-byte digest.
    Blake2s {
        state: 96,
        scratch: 72,
        block: 64,
        max: 32,
        init: vg_blake2s_init,
        update: vg_blake2s_update,
        finalize: vg_blake2s_finalize,
    }
);

/// BLAKE2s with 32-byte digests.
pub type Blake2s256 = Blake2s<32>;
