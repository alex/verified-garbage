//! PBKDF2-HMAC-SHA-512/256. On x86-64, the whole derivation is
//! `vg_pbkdf2_hmac_sha512_256` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha512_256I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-512/256's verified functions. On the other
//! targets, the iteration is `vg_pbkdf2_hmac_sha512_256_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for
//! every streaming hash function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512_256::vg_pbkdf2_hmac_sha512_256;
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha512_256::vg_pbkdf2_hmac_sha512_256_iterate;
use crate::hashes::sha512::{Sha512_256, Sha512_256Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Sha512_256 (Sha512_256Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_256_iterate,
    },
    state: 192,
    scratch: 96,
    output: 32,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Sha512_256 (Sha512_256Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_256,
    },
    scratch: 288,
    output: 32,
);
