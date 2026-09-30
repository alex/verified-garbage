//! PBKDF2-HMAC-SHA-512/224: the iteration is
//! `vg_pbkdf2_hmac_sha512_224_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.sha512_224I`). On
//! x86-64 it is the one iteration for every hash function whose streaming code
//! is the generic one, calling SHA-512's verified compression function
//! directly, twice per step; on the other targets, the one iteration for every
//! streaming hash function, calling SHA-512/224's verified streaming functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::pbkdf2_sha512_224::vg_pbkdf2_hmac_sha512_224_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512_224::{
    VG_PBKDF2_HMAC_SHA512_224_ITERATE_AVX2_FEATURES, vg_pbkdf2_hmac_sha512_224_iterate_avx2,
};
use crate::hashes::sha512::{Sha512_224, Sha512_224Backend};

super::streaming_pbkdf2!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_224_iterate,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA512_224_ITERATE_AVX2_FEATURES] => vg_pbkdf2_hmac_sha512_224_iterate_avx2,
    },
    state: 192,
    scratch: 234,
    output: 28,
);
