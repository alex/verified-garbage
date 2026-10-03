//! PBKDF2-HMAC-SHA-224 (RFC 8018 §5.2). The whole derivation is
//! `vg_pbkdf2_hmac_sha224` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha224I`). On x86-64 and AArch64, it is the one PBKDF2
//! implementation for every Merkle–Damgård hash function, calling
//! SHA-224's verified functions: its iteration calls SHA-256's verified
//! compression function directly, twice per step. On x86-64 and x86, it
//! follows the implementation of SHA-256 compression that `Sha224` runs on
//! this CPU (`vg_pbkdf2_hmac_sha224_shani`, and on x86-64
//! `vg_pbkdf2_hmac_sha224_avx2`: the same verified code calling
//! `vg_sha256_compress_<suffix>` (and, on x86, the streaming, HMAC and
//! iteration functions with the same suffix), with the same contract).
//! AArch64 selects `vg_pbkdf2_hmac_sha224_sha2` when the SHA-256
//! instructions are available.
//!
//! On ARMv7 and x86, the whole derivation is the one for every streaming hash
//! function, calling SHA-224's `init`, SHA-256's verified streaming
//! functions, HMAC-SHA-224's `init` and `finalize` and
//! `vg_pbkdf2_hmac_sha224_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for
//! every Merkle–Damgård hash function: each step is two calls of SHA-256's
//! verified compression function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::pbkdf2_sha224::vg_pbkdf2_hmac_sha224;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha224::{VG_PBKDF2_HMAC_SHA224_AVX2_FEATURES, vg_pbkdf2_hmac_sha224_avx2};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha224::{VG_PBKDF2_HMAC_SHA224_SHA2_FEATURES, vg_pbkdf2_hmac_sha224_sha2};
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use crate::arch::pbkdf2_sha224::{
    VG_PBKDF2_HMAC_SHA224_SHANI_FEATURES, vg_pbkdf2_hmac_sha224_shani,
};
use crate::hashes::sha224::{Sha224, Sha224Backend};

super::whole_pbkdf2!(
    Sha224 (Sha224Backend) {
        Scalar => vg_pbkdf2_hmac_sha224,
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_PBKDF2_HMAC_SHA224_SHA2_FEATURES] => vg_pbkdf2_hmac_sha224_sha2,
        #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
        ShaNi if [VG_PBKDF2_HMAC_SHA224_SHANI_FEATURES] => vg_pbkdf2_hmac_sha224_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA224_AVX2_FEATURES] => vg_pbkdf2_hmac_sha224_avx2,
    },
    scratch: 200,
    output: 28,
);
