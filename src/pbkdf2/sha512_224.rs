//! PBKDF2-HMAC-SHA-512/224. On x86-64, the whole derivation is
//! `vg_pbkdf2_hmac_sha512_224` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha512_224I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-512/224's verified functions. On the other
//! targets, the iteration is `vg_pbkdf2_hmac_sha512_224_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for
//! every streaming hash function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512_224::vg_pbkdf2_hmac_sha512_224;
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha512_224::vg_pbkdf2_hmac_sha512_224_iterate;
use crate::hashes::sha512::{Sha512_224, Sha512_224Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_224_iterate,
    },
    state: 192,
    scratch: 96,
    output: 28,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_224,
    },
    scratch: 288,
    output: 28,
);
