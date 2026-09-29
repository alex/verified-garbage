//! PBKDF2-HMAC-MD5: the iteration is `vg_pbkdf2_hmac_md5_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of `VG.Spec.Hmac.md5I`), the one
//! PBKDF2 iteration for every streaming hash function, calling MD5's verified
//! functions.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::pbkdf2_md5::vg_pbkdf2_hmac_md5_iterate;
use crate::hashes::md5::Md5;

super::streaming_pbkdf2!(
    Md5: vg_pbkdf2_hmac_md5_iterate,
    state: 80,
    scratch: 48,
    output: 16,
);
