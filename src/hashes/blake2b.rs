//! BLAKE2b (RFC 7693): digests of 1 to 64 bytes, unkeyed or keyed with up
//! to 64 bytes, over 64-bit words (see `blake2` for how the verified
//! functions are used).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::arch::blake2b::{vg_blake2b_finalize, vg_blake2b_init, vg_blake2b_update};

super::blake2::blake2!(
    /// An incremental BLAKE2b computation of an `N`-byte digest.
    Blake2b {
        state: 192,
        scratch: 72,
        block: 128,
        max: 64,
        init: vg_blake2b_init,
        backends: Blake2bBackend {
            Scalar => (vg_blake2b_update, vg_blake2b_finalize),
        },
    }
);

/// BLAKE2b with 64-byte digests.
pub type Blake2b512 = Blake2b<64>;
