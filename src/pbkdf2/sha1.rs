//! PBKDF2-HMAC-SHA-1: the iteration is `vg_pbkdf2_hmac_sha1_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.sha1I`), the one
//! PBKDF2 iteration for every streaming hash function, calling SHA-1's verified
//! functions.
//!
//! It follows the implementation of SHA-1 the HMAC computation runs: on x86-64
//! with the SHA extensions, `vg_pbkdf2_hmac_sha1_iterate_shani`, the same
//! verified code calling `vg_sha1_update_shani` and `vg_sha1_finalize_shani`,
//! with the same contract.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::pbkdf2_sha1::vg_pbkdf2_hmac_sha1_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha1::{
    VG_PBKDF2_HMAC_SHA1_ITERATE_SHANI_FEATURES, vg_pbkdf2_hmac_sha1_iterate_shani,
};
use crate::hashes::sha1::{Sha1, Sha1Backend};

super::streaming_pbkdf2!(
    Sha1 (Sha1Backend) {
        Scalar => vg_pbkdf2_hmac_sha1_iterate,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA1_ITERATE_SHANI_FEATURES] => vg_pbkdf2_hmac_sha1_iterate_shani,
    },
    state: 84,
    scratch: 56,
    output: 20,
);
