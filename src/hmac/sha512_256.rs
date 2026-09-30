//! HMAC-SHA-512/256: `vg_hmac_sha512_256_init`, `vg_sha512_update` and
//! `vg_hmac_sha512_256_finalize` (contracts
//! `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha512_256I`,
//! `VG.Spec.Sha512.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-512/256
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-512/256's verified functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::hmac_sha512_256::{vg_hmac_sha512_256_finalize, vg_hmac_sha512_256_init};
use crate::hashes::sha512::{Sha512_256, Sha512_256Backend};

super::streaming_hmac!(
    Sha512_256 (Sha512_256Backend) {
        Scalar => (vg_hmac_sha512_256_init, vg_hmac_sha512_256_finalize),
    },
    state: 192,
    scratch: 234,
    output: 32,
);
