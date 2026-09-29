//! PBKDF2-HMAC-SHA-512/224: the iteration is
//! `vg_pbkdf2_hmac_sha512_224_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.sha512_224I`), the
//! one PBKDF2 iteration for every streaming hash function, calling
//! SHA-512/224's verified functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::arch::pbkdf2_sha512_224::vg_pbkdf2_hmac_sha512_224_iterate;
use crate::hashes::sha512::Sha512_224;

super::streaming_pbkdf2!(
    Sha512_224: vg_pbkdf2_hmac_sha512_224_iterate,
    state: 192,
    scratch: 96,
    output: 28,
);
