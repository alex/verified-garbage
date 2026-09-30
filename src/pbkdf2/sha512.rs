//! PBKDF2-HMAC-SHA-512. On x86-64, the whole derivation is
//! `vg_pbkdf2_hmac_sha512` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha512I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-512's verified functions. On the other
//! targets, the iteration is `vg_pbkdf2_hmac_sha512_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for
//! every streaming hash function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512::vg_pbkdf2_hmac_sha512;
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha512::vg_pbkdf2_hmac_sha512_iterate;
use crate::hashes::sha512::{Sha512, Sha512Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Sha512 (Sha512Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_iterate,
    },
    state: 192,
    scratch: 96,
    output: 64,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Sha512 (Sha512Backend) {
        Scalar => vg_pbkdf2_hmac_sha512,
    },
    scratch: 288,
    output: 64,
);
