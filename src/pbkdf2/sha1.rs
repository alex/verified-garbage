//! PBKDF2-HMAC-SHA-1. On x86-64, the whole derivation is
//! `vg_pbkdf2_hmac_sha1` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha1I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-1's verified functions: it
//! follows the implementation of SHA-1 that `Sha1` runs on this CPU (e.g.
//! `vg_pbkdf2_hmac_sha1_shani`, the same verified code calling
//! `vg_sha1_compress_shani`, with the same contract). On the other
//! targets, the iteration is `vg_pbkdf2_hmac_sha1_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for
//! every streaming hash function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha1::vg_pbkdf2_hmac_sha1_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha1::{
    VG_PBKDF2_HMAC_SHA1_SHANI_FEATURES, vg_pbkdf2_hmac_sha1, vg_pbkdf2_hmac_sha1_shani,
};
use crate::hashes::sha1::{Sha1, Sha1Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Sha1 (Sha1Backend) {
        Scalar => vg_pbkdf2_hmac_sha1_iterate,
    },
    state: 84,
    scratch: 56,
    output: 20,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Sha1 (Sha1Backend) {
        Scalar => vg_pbkdf2_hmac_sha1,
        ShaNi if [VG_PBKDF2_HMAC_SHA1_SHANI_FEATURES] => vg_pbkdf2_hmac_sha1_shani,
    },
    scratch: 140,
    output: 20,
);
