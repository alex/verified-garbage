//! HMAC-SHA-512/224: `vg_hmac_sha512_224_init`, `vg_sha512_update` and
//! `vg_hmac_sha512_224_finalize` (contracts
//! `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha512_224I`,
//! `VG.Spec.Sha512.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-512/224
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-512/224's verified functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::hmac_sha512_224::{vg_hmac_sha512_224_finalize, vg_hmac_sha512_224_init};
use crate::hashes::sha512::{Sha512_224, Sha512_224Backend};

super::streaming_hmac!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => (vg_hmac_sha512_224_init, vg_hmac_sha512_224_finalize),
    },
    state: 192,
    scratch: 234,
    output: 28,
);
