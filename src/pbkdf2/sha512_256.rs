//! PBKDF2-HMAC-SHA-512/256: the iteration is
//! `vg_pbkdf2_hmac_sha512_256_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.sha512_256I`), the
//! one PBKDF2 iteration for every streaming hash function, calling
//! SHA-512/256's verified functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::arch::pbkdf2_sha512_256::vg_pbkdf2_hmac_sha512_256_iterate;
use crate::hashes::sha512::Sha512_256;

super::streaming_pbkdf2!(
    Sha512_256: vg_pbkdf2_hmac_sha512_256_iterate,
    state: 192,
    scratch: 96,
    output: 32,
);
