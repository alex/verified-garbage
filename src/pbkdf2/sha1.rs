//! PBKDF2-HMAC-SHA-1: the iteration is `vg_pbkdf2_hmac_sha1_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.sha1I`), the one
//! PBKDF2 iteration for every streaming hash function, calling SHA-1's verified
//! functions.

#![cfg(target_arch = "x86_64")]

use crate::arch::pbkdf2_sha1::vg_pbkdf2_hmac_sha1_iterate;
use crate::hashes::sha1::Sha1;

super::streaming_pbkdf2!(
    Sha1: vg_pbkdf2_hmac_sha1_iterate,
    state: 84,
    scratch: 56,
    output: 20,
);
