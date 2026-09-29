//! HMAC-SHA-1: `vg_hmac_sha1_init`, `vg_sha1_update` and
//! `vg_hmac_sha1_finalize` (contracts `VG.Spec.Hmac.Instance.initContract` of
//! `VG.Spec.Hmac.sha1I`, `VG.Spec.Sha1.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-1
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-1's verified functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::arch::hmac_sha1::{vg_hmac_sha1_finalize, vg_hmac_sha1_init};
use crate::hashes::sha1::Sha1;

super::streaming_hmac!(
    Sha1: (vg_hmac_sha1_init, vg_hmac_sha1_finalize),
    state: 84,
    scratch: 56,
    output: 20,
);
