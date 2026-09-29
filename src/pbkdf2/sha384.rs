//! PBKDF2-HMAC-SHA-384: the iteration is `vg_pbkdf2_hmac_sha384_iterate`
//! (contract `VG.Spec.Hmac.Instance.iterateContract` of
//! `VG.Spec.Hmac.sha384I`), the one PBKDF2 iteration for every streaming hash
//! function, calling SHA-384's verified functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::pbkdf2_sha384::vg_pbkdf2_hmac_sha384_iterate;
use crate::hashes::sha512::Sha384;

super::streaming_pbkdf2!(
    Sha384: vg_pbkdf2_hmac_sha384_iterate,
    state: 192,
    scratch: 96,
    output: 48,
);
