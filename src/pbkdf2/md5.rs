//! PBKDF2-HMAC-MD5. On x86-64, the whole derivation is `vg_pbkdf2_hmac_md5`
//! (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of `VG.Spec.Hmac.md5I`),
//! the one PBKDF2 implementation for every Merkle–Damgård hash function,
//! calling MD5's verified functions: its iteration calls MD5's verified
//! compression function directly, twice per step.
//!
//! On the other targets, the iteration is `vg_pbkdf2_hmac_md5_iterate`
//! (contract `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration
//! for every streaming hash function, calling MD5's verified streaming
//! functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_md5::vg_pbkdf2_hmac_md5;
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_md5::vg_pbkdf2_hmac_md5_iterate;
use crate::hashes::md5::{Md5, Md5Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Md5 (Md5Backend) {
        Scalar => vg_pbkdf2_hmac_md5_iterate,
    },
    state: 80,
    scratch: 48,
    output: 16,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Md5 (Md5Backend) {
        Scalar => vg_pbkdf2_hmac_md5,
    },
    scratch: 128,
    output: 16,
);
