//! PBKDF2-HMAC-SHA-1. The whole derivation is
//! `vg_pbkdf2_hmac_sha1` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha1I`). On x86-64 and AArch64, it is the one PBKDF2
//! implementation for every Merkle–Damgård hash function, calling SHA-1's verified functions: its
//! iteration calls SHA-1's verified compression function directly, twice per
//! step. On x86-64, it follows the implementation of SHA-1 compression that
//! `Sha1` runs on this CPU (`vg_pbkdf2_hmac_sha1_shani`: the same verified code calling
//! `vg_sha1_compress_<suffix>`, with the same contract).
//!
//! On ARMv7 and x86, the whole derivation is the one for every streaming hash
//! function, calling SHA-1's verified streaming functions, HMAC-SHA-1's
//! `init` and `finalize` and `vg_pbkdf2_hmac_sha1_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for
//! every streaming hash function.
//!
//! On AArch64, the `_sha2` variants follow SHA-1 hardware dispatch.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::pbkdf2_sha1::vg_pbkdf2_hmac_sha1;
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha1::{VG_PBKDF2_HMAC_SHA1_SHA2_FEATURES, vg_pbkdf2_hmac_sha1_sha2};
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha1::{VG_PBKDF2_HMAC_SHA1_SHANI_FEATURES, vg_pbkdf2_hmac_sha1_shani};
use crate::hashes::sha1::{Sha1, Sha1Backend};

super::whole_pbkdf2!(
    Sha1 (Sha1Backend) {
        Scalar => vg_pbkdf2_hmac_sha1,
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_PBKDF2_HMAC_SHA1_SHA2_FEATURES] =>
            vg_pbkdf2_hmac_sha1_sha2,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA1_SHANI_FEATURES] => vg_pbkdf2_hmac_sha1_shani,
    },
    scratch: 140,
    output: 20,
);
