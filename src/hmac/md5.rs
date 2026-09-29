//! HMAC-MD5: `vg_hmac_md5_init`, `vg_md5_update` and `vg_hmac_md5_finalize`
//! (contracts `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.md5I`,
//! `VG.Spec.Md5.updateContract` and `VG.Spec.Hmac.Instance.finalizeContract`)
//! compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
//! (`VG.Spec.Hmac.hmacBlockKey`), keeping the two MD5 streaming states. `init`
//! and `finalize` are the one HMAC implementation for every streaming hash
//! function, calling MD5's verified functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::arch::hmac_md5::{vg_hmac_md5_finalize, vg_hmac_md5_init};
use crate::hashes::md5::{Md5, Md5Backend};

super::streaming_hmac!(
    Md5 (Md5Backend) {
        Scalar => (vg_hmac_md5_init, vg_hmac_md5_finalize),
    },
    state: 80,
    scratch: 48,
    output: 16,
);
