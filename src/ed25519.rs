//! Ed25519 (RFC 8032), deterministic signatures from 32-byte seeds.
//!
//! Key derivation, signing, and verification each call one complete verified
//! assembly operation, including SHA-512, on every supported architecture.
//! x86-64 and AArch64 variants follow the selected SHA-512 backend. On
//! x86-64 CPUs with BMI2 and ADX, the `_adx` variants multiply field
//! elements with `mulx`, `adcx` and `adox`, and on those that also have
//! AVX512_IFMA and AVX512VL, verification is the `_ifma` variant, whose
//! doublings use four-lane field multiplications. Secret scratch values are
//! cleared after use.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::ed25519::{
    VG_ED25519_PUBLIC_KEY_ADX_FEATURES, VG_ED25519_SIGN_CACHED_ADX_FEATURES,
    VG_ED25519_VERIFY_ADX_FEATURES, VG_ED25519_VERIFY_IFMA_FEATURES, vg_ed25519_public_key_adx,
    vg_ed25519_public_key_avx2, vg_ed25519_public_key_avx2_adx, vg_ed25519_public_key_shani,
    vg_ed25519_public_key_shani_adx, vg_ed25519_sign_cached_adx, vg_ed25519_sign_cached_avx2,
    vg_ed25519_sign_cached_avx2_adx, vg_ed25519_sign_cached_shani,
    vg_ed25519_sign_cached_shani_adx, vg_ed25519_verify_adx, vg_ed25519_verify_avx2,
    vg_ed25519_verify_avx2_adx, vg_ed25519_verify_avx2_ifma, vg_ed25519_verify_ifma,
    vg_ed25519_verify_shani, vg_ed25519_verify_shani_adx, vg_ed25519_verify_shani_ifma,
};
use crate::arch::ed25519::{vg_ed25519_public_key, vg_ed25519_sign_cached, vg_ed25519_verify};
#[cfg(target_arch = "aarch64")]
use crate::arch::ed25519::{
    vg_ed25519_public_key_sha3, vg_ed25519_sign_cached_sha3, vg_ed25519_verify_sha3,
};
use crate::cpu::{Features, detected};
use crate::hashes::sha512::Sha512Backend;
use crate::zeroize::zeroize;

/// The field multiplications of the complete operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Field {
    /// The target's baseline ISA.
    Baseline,
    /// BMI2's `mulx` and ADX's `adcx` and `adox` (the `_adx` variants).
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `Adx`, and AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq` (on `ymm`
    /// registers, with AVX512VL) for verification's doublings (the `_ifma`
    /// variants of verification).
    #[cfg(target_arch = "x86_64")]
    Ifma,
}

impl Field {
    /// The fastest field multiplications a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Field {
        let adx = f.contains(Features::all(&[
            VG_ED25519_PUBLIC_KEY_ADX_FEATURES,
            VG_ED25519_SIGN_CACHED_ADX_FEATURES,
            VG_ED25519_VERIFY_ADX_FEATURES,
        ]));
        if adx && f.contains(Features::of(VG_ED25519_VERIFY_IFMA_FEATURES)) {
            Field::Ifma
        } else if adx {
            Field::Adx
        } else {
            Field::Baseline
        }
    }

    /// The field multiplications a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Field {
        Field::Baseline
    }
}

/// Why signature verification failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The signature has the wrong length, a noncanonical encoding, or an invalid equation.
    InvalidSignature,
}

/// An encoded Ed25519 public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    bytes: [u8; 32],
}

impl VerifyingKey {
    /// Import an encoded public key. Its encoding is checked during verification.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self { bytes: *bytes }
    }

    /// The encoded public key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Verify a pure Ed25519 signature (RFC 8032 §5.1.7).
    ///
    /// Public keys and signatures must use canonical encodings, and the
    /// signature scalar must be less than the subgroup order. This checks
    /// the uncofactored equation. The SHA-512 challenge is reduced modulo the
    /// subgroup order, following RFC 8032 §6. No additional subgroup or
    /// small-order rejection policy is imposed.
    /// Verification timing may depend on the public key, message, and signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let signature: &[u8; 64] = signature.try_into().map_err(|_| Error::InvalidSignature)?;
        let valid = verify_message(&self.bytes, message, signature);
        if valid == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

/// An Ed25519 signing key, storing its seed and derived public key.
///
/// The seed is cleared when the key is dropped. Debug output omits it.
#[derive(Clone)]
pub struct SigningKey {
    seed: [u8; 32],
    public: VerifyingKey,
}

impl core::fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl Drop for SigningKey {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
    }
}

impl SigningKey {
    /// Derive a signing key and its public key from an RFC 8032 seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        Self {
            seed: *seed,
            public: VerifyingKey {
                bytes: public_key(seed),
            },
        }
    }

    /// The original 32-byte seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The public key derived from this key's seed.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.public
    }

    /// Sign `message` deterministically using pure Ed25519 (RFC 8032 §5.1.6).
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        sign_message(&self.seed, &self.public.bytes, message)
    }
}

/// The public key of `seed` (RFC 8032 §5.1.5), with the verified
/// `vg_ed25519_public_key` including SHA-512.
fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    // SAFETY: the CPU has the features it was detected to have.
    unsafe { public_key_with(detected(), seed) }
}

/// `public_key`, with the implementations a CPU with the features `f` can run.
///
/// # Safety
///
/// The CPU has the features `f`.
unsafe fn public_key_with(f: Features, seed: &[u8; 32]) -> [u8; 32] {
    let derive = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_public_key,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx | Field::Ifma) => vg_ed25519_public_key_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_public_key_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx | Field::Ifma) => vg_ed25519_public_key_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_public_key_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx | Field::Ifma) => vg_ed25519_public_key_avx2_adx,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_public_key_sha3,
    };
    let mut public = [0u8; 32];
    let mut scratch = [0u64; 1024];
    // SAFETY: the output, seed, and scratch are distinct objects valid for
    // 32, 32, and 8192 bytes, respectively, so they overlap neither each
    // other nor the call's stack, and none wraps the address space. The
    // seed is the caller's. SHA-512's backend and the field's, selected from
    // features the CPU has, select every required CPU feature.
    unsafe { derive(&mut public, seed, &mut scratch) };
    zeroize(&mut scratch);
    public
}

fn verify_message(pk: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> u32 {
    // SAFETY: the CPU has the features it was detected to have.
    unsafe { verify_message_with(detected(), pk, message, signature) }
}

/// `verify_message`, with the implementations a CPU with the features `f`
/// can run.
///
/// # Safety
///
/// The CPU has the features `f`.
unsafe fn verify_message_with(
    f: Features,
    pk: &[u8; 32],
    message: &[u8],
    signature: &[u8; 64],
) -> u32 {
    let verify = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_verify,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx) => vg_ed25519_verify_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Ifma) => vg_ed25519_verify_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_verify_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx) => vg_ed25519_verify_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Ifma) => vg_ed25519_verify_shani_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_verify_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx) => vg_ed25519_verify_avx2_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Ifma) => vg_ed25519_verify_avx2_ifma,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_verify_sha3,
    };
    let mut scratch = [0u64; 1024];
    // SAFETY: input references are valid for their declared lengths and scratch
    // is a distinct writable object. No object overlaps the call stack, and
    // SHA-512's backend and the field's, selected from features the CPU has,
    // select every required CPU feature.
    let valid = unsafe { verify(pk, message.as_ptr(), message.len(), signature, &mut scratch) };
    zeroize(&mut scratch);
    valid
}

fn sign_message(seed: &[u8; 32], pk: &[u8; 32], message: &[u8]) -> [u8; 64] {
    // SAFETY: the CPU has the features it was detected to have, and pk is
    // seed's public key, as `sign_message_with` requires.
    unsafe { sign_message_with(detected(), seed, pk, message) }
}

/// `sign_message`, with the implementations a CPU with the features `f` can
/// run.
///
/// # Safety
///
/// The CPU has the features `f`, and `pk` is `seed`'s public key.
unsafe fn sign_message_with(
    f: Features,
    seed: &[u8; 32],
    pk: &[u8; 32],
    message: &[u8],
) -> [u8; 64] {
    let sign = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_sign_cached,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx | Field::Ifma) => vg_ed25519_sign_cached_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_sign_cached_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx | Field::Ifma) => vg_ed25519_sign_cached_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_sign_cached_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx | Field::Ifma) => vg_ed25519_sign_cached_avx2_adx,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_sign_cached_sha3,
    };
    let mut signature = [0u8; 64];
    let mut scratch = [0u64; 1024];
    // SAFETY: the input references are valid for their declared lengths.
    // Signature and scratch are distinct writable objects, disjoint from the
    // inputs and the call's stack. None wraps the address space. pk is seed's
    // public key (the caller's requirement). SHA-512's backend and the
    // field's, selected from features the CPU has, select every required CPU
    // feature.
    unsafe {
        sign(
            &mut signature,
            seed,
            pk,
            message.as_ptr(),
            message.len(),
            &mut scratch,
        )
    };
    zeroize(&mut scratch);
    signature
}

#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    use super::Sha512Backend;
    use crate::arch::ed25519::{
        VG_ED25519_PUBLIC_KEY_SHA3_FEATURES, VG_ED25519_SIGN_CACHED_SHA3_FEATURES,
        VG_ED25519_VERIFY_SHA3_FEATURES,
    };
    use crate::cpu::{Features, NAMES};

    /// Every feature set selecting SHA-512's optimized backend also supports
    /// each complete Ed25519 operation that uses that backend.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let features = Features(bits);
            match Sha512Backend::select(features) {
                Sha512Backend::Scalar => {}
                Sha512Backend::Sha3 => {
                    assert!(features.contains(Features::all(&[
                        VG_ED25519_PUBLIC_KEY_SHA3_FEATURES,
                        VG_ED25519_SIGN_CACHED_SHA3_FEATURES,
                        VG_ED25519_VERIFY_SHA3_FEATURES,
                    ])));
                }
            }
        }
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod x86_64_tests {
    use super::*;
    use crate::arch::ed25519::{
        VG_ED25519_PUBLIC_KEY_AVX2_ADX_FEATURES, VG_ED25519_PUBLIC_KEY_AVX2_FEATURES,
        VG_ED25519_PUBLIC_KEY_SHANI_ADX_FEATURES, VG_ED25519_PUBLIC_KEY_SHANI_FEATURES,
        VG_ED25519_SIGN_CACHED_AVX2_ADX_FEATURES, VG_ED25519_SIGN_CACHED_AVX2_FEATURES,
        VG_ED25519_SIGN_CACHED_SHANI_ADX_FEATURES, VG_ED25519_SIGN_CACHED_SHANI_FEATURES,
        VG_ED25519_VERIFY_AVX2_ADX_FEATURES, VG_ED25519_VERIFY_AVX2_FEATURES,
        VG_ED25519_VERIFY_AVX2_IFMA_FEATURES, VG_ED25519_VERIFY_SHANI_ADX_FEATURES,
        VG_ED25519_VERIFY_SHANI_FEATURES, VG_ED25519_VERIFY_SHANI_IFMA_FEATURES,
    };
    use crate::cpu::NAMES;

    /// The CPU features of the three operations with SHA-512's backend `s`
    /// and the field multiplications `f`.
    fn required(s: Sha512Backend, f: Field) -> [&'static [&'static str]; 3] {
        match (s, f) {
            (Sha512Backend::Scalar, Field::Baseline) => [&[], &[], &[]],
            (Sha512Backend::Scalar, Field::Adx) => [
                VG_ED25519_PUBLIC_KEY_ADX_FEATURES,
                VG_ED25519_SIGN_CACHED_ADX_FEATURES,
                VG_ED25519_VERIFY_ADX_FEATURES,
            ],
            (Sha512Backend::ShaNi, Field::Baseline) => [
                VG_ED25519_PUBLIC_KEY_SHANI_FEATURES,
                VG_ED25519_SIGN_CACHED_SHANI_FEATURES,
                VG_ED25519_VERIFY_SHANI_FEATURES,
            ],
            (Sha512Backend::ShaNi, Field::Adx) => [
                VG_ED25519_PUBLIC_KEY_SHANI_ADX_FEATURES,
                VG_ED25519_SIGN_CACHED_SHANI_ADX_FEATURES,
                VG_ED25519_VERIFY_SHANI_ADX_FEATURES,
            ],
            (Sha512Backend::Avx2, Field::Baseline) => [
                VG_ED25519_PUBLIC_KEY_AVX2_FEATURES,
                VG_ED25519_SIGN_CACHED_AVX2_FEATURES,
                VG_ED25519_VERIFY_AVX2_FEATURES,
            ],
            (Sha512Backend::Avx2, Field::Adx) => [
                VG_ED25519_PUBLIC_KEY_AVX2_ADX_FEATURES,
                VG_ED25519_SIGN_CACHED_AVX2_ADX_FEATURES,
                VG_ED25519_VERIFY_AVX2_ADX_FEATURES,
            ],
            (Sha512Backend::Scalar, Field::Ifma) => [
                VG_ED25519_PUBLIC_KEY_ADX_FEATURES,
                VG_ED25519_SIGN_CACHED_ADX_FEATURES,
                VG_ED25519_VERIFY_IFMA_FEATURES,
            ],
            (Sha512Backend::ShaNi, Field::Ifma) => [
                VG_ED25519_PUBLIC_KEY_SHANI_ADX_FEATURES,
                VG_ED25519_SIGN_CACHED_SHANI_ADX_FEATURES,
                VG_ED25519_VERIFY_SHANI_IFMA_FEATURES,
            ],
            (Sha512Backend::Avx2, Field::Ifma) => [
                VG_ED25519_PUBLIC_KEY_AVX2_ADX_FEATURES,
                VG_ED25519_SIGN_CACHED_AVX2_ADX_FEATURES,
                VG_ED25519_VERIFY_AVX2_IFMA_FEATURES,
            ],
        }
    }

    /// Each complete Ed25519 operation needs no CPU feature that SHA-512's
    /// backend and the field's are not selected for: on every set of
    /// features that selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            let r = required(Sha512Backend::select(f), Field::select(f));
            assert!(f.contains(Features::all(&r)), "{bits:#b}");
        }
    }

    /// Each operation gives the same results with every choice of
    /// implementations this CPU can run: the features of each subset of
    /// SHA-512's backends and the field's.
    #[test]
    fn every_backend() {
        let groups: [&[&str]; 4] = [
            VG_ED25519_PUBLIC_KEY_SHANI_FEATURES,
            VG_ED25519_PUBLIC_KEY_AVX2_FEATURES,
            VG_ED25519_PUBLIC_KEY_ADX_FEATURES,
            VG_ED25519_VERIFY_IFMA_FEATURES,
        ];
        let seed = [0x42; 32];
        let message = b"every backend";
        // SAFETY: no feature is needed; `public` is `seed`'s public key.
        let (public, signature) = unsafe {
            let public = public_key_with(Features(0), &seed);
            (
                public,
                sign_message_with(Features(0), &seed, &public, message),
            )
        };
        for mask in 0..1u32 << groups.len() {
            let f = groups
                .iter()
                .enumerate()
                .filter(|(i, _)| mask >> i & 1 == 1)
                .fold(Features(0), |f, (_, g)| Features(f.0 | Features::of(g).0));
            if !detected().contains(f) {
                continue;
            }
            // SAFETY: the CPU has the features `f`; `public` is `seed`'s
            // public key.
            unsafe {
                assert_eq!(public_key_with(f, &seed), public, "{mask:#b}");
                assert_eq!(
                    sign_message_with(f, &seed, &public, message),
                    signature,
                    "{mask:#b}"
                );
                assert_eq!(
                    verify_message_with(f, &public, message, &signature),
                    1,
                    "{mask:#b}"
                );
            }
        }
    }
}
