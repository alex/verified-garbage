//! PBKDF2-HMAC-SHA-512: the iteration is `vg_pbkdf2_hmac_sha512_iterate`
//! (contract `VG.Spec.Hmac.Instance.iterateContract` of
//! `VG.Spec.Hmac.sha512I`), the one PBKDF2 iteration for every streaming hash
//! function, calling SHA-512's verified functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::arch::pbkdf2_sha512::vg_pbkdf2_hmac_sha512_iterate;
use crate::hashes::sha512::Sha512;

super::streaming_pbkdf2!(
    Sha512: vg_pbkdf2_hmac_sha512_iterate,
    state: 192,
    scratch: 96,
    output: 64,
);
