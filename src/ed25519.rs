//! Ed25519 (RFC 8032), deterministic signatures from 32-byte seeds.
//!
//! SHA-512 uses the hash API's selected backend. Scalar reduction,
//! multiply-add, and point multiplication use verified assembly with the
//! contracts in `VG.Spec.Ed25519`. On x86-64 CPUs with BMI2 and ADX, the
//! point multiplications are `vg_ed25519_scalar_base_precomputed_adx` and
//! `vg_ed25519_verify_equation_adx`, with the same contracts and faster field
//! multiplications, and on those that also have AVX512_IFMA and AVX512VL
//! verification is `vg_ed25519_verify_equation_ifma`, whose doublings use
//! four-lane field multiplications. Rust composes those primitives and clears
//! secret temporary values.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::ed25519::{
    VG_ED25519_SCALAR_BASE_PRECOMPUTED_ADX_FEATURES, VG_ED25519_VERIFY_EQUATION_ADX_FEATURES,
    VG_ED25519_VERIFY_EQUATION_IFMA_FEATURES, vg_ed25519_scalar_base_precomputed,
    vg_ed25519_scalar_base_precomputed_adx, vg_ed25519_verify_equation_adx,
    vg_ed25519_verify_equation_ifma,
};
use crate::arch::ed25519::{
    vg_ed25519_scalar_mul_add, vg_ed25519_scalar_reduce, vg_ed25519_verify_equation,
};
use crate::cpu::{Features, detected};
use crate::hashes::sha512::Sha512;
use crate::zeroize::zeroize;

/// The implementations of the point multiplications.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The target's baseline ISA.
    Baseline,
    /// BMI2's `mulx` and ADX's `adcx` and `adox` for the field multiplications.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `Adx`, and AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq` (on `ymm`
    /// registers, with AVX512VL) for verification's doublings.
    #[cfg(target_arch = "x86_64")]
    Ifma,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        let adx = f.contains(Features::of(
            VG_ED25519_SCALAR_BASE_PRECOMPUTED_ADX_FEATURES,
        )) && f.contains(Features::of(VG_ED25519_VERIFY_EQUATION_ADX_FEATURES));
        if adx && f.contains(Features::of(VG_ED25519_VERIFY_EQUATION_IFMA_FEATURES)) {
            Backend::Ifma
        } else if adx {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Backend {
        Backend::Baseline
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
    /// the uncofactored equation using the full SHA-512 challenge. It does
    /// not impose an additional subgroup or small-order rejection policy.
    /// Verification timing may depend on the public key, message, and signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let signature: &[u8; 64] = signature.try_into().map_err(|_| Error::InvalidSignature)?;
        let mut hash = Sha512::new();
        hash.update(&signature[..32]);
        hash.update(&self.bytes);
        hash.update(message);
        let challenge = hash.finalize();
        let mut scratch = [0u64; 1024];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_ed25519_verify_equation,
            // `select` chose it because the CPU has the features it needs.
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ed25519_verify_equation_adx,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_ed25519_verify_equation_ifma,
        };
        // SAFETY: the input arrays are live for their declared sizes, and
        // scratch is a distinct writable object. None wraps the address space.
        // The CPU has the features of the function `select` chose.
        let valid = unsafe { f(&self.bytes, signature, &challenge, &mut scratch) };
        zeroize(&mut scratch);
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
        let mut expanded = Sha512::digest(seed);
        let mut scalar = prune(&expanded);
        let mut scratch = [0u64; 1024];
        let public = VerifyingKey {
            bytes: scalar_base(&scalar, &mut scratch),
        };
        zeroize(&mut scratch);
        zeroize(&mut scalar);
        zeroize(&mut expanded);
        Self {
            seed: *seed,
            public,
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
        let mut expanded = Sha512::digest(&self.seed);
        let mut scalar = prune(&expanded);
        let mut nonce_hash = Sha512::new();
        nonce_hash.update(&expanded[32..]);
        nonce_hash.update(message);
        let mut nonce_digest = nonce_hash.finalize();
        let mut scratch = [0u64; 1024];
        let mut nonce = reduce(&nonce_digest, &mut scratch);
        let r = scalar_base(&nonce, &mut scratch);
        let mut challenge_hash = Sha512::new();
        challenge_hash.update(&r);
        challenge_hash.update(&self.public.bytes);
        challenge_hash.update(message);
        let mut challenge_digest = challenge_hash.finalize();
        let mut challenge = reduce(&challenge_digest, &mut scratch);
        let mut s = [0u8; 32];
        // SAFETY: the output, inputs, and scratch are distinct live objects
        // of the required sizes, with no overlap or address-space wrapping.
        unsafe { vg_ed25519_scalar_mul_add(&mut s, &nonce, &challenge, &scalar, &mut scratch) };
        let mut signature = [0u8; 64];
        signature[..32].copy_from_slice(&r);
        signature[32..].copy_from_slice(&s);
        zeroize(&mut scratch);
        zeroize(&mut expanded);
        zeroize(&mut scalar);
        zeroize(&mut nonce_digest);
        zeroize(&mut nonce);
        zeroize(&mut challenge_digest);
        zeroize(&mut challenge);
        zeroize(&mut s);
        signature
    }
}

fn prune(expanded: &[u8; 64]) -> [u8; 32] {
    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(&expanded[..32]);
    scalar[0] &= 248;
    scalar[31] &= 63;
    scalar[31] |= 64;
    scalar
}

fn scalar_base(scalar: &[u8; 32], scratch: &mut [u64; 1024]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // On x86-64 the base point's powers are precomputed.
    #[cfg(target_arch = "x86_64")]
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ed25519_scalar_base_precomputed,
        // `select` chose it because the CPU has the features it needs.
        Backend::Adx | Backend::Ifma => vg_ed25519_scalar_base_precomputed_adx,
    };
    #[cfg(not(target_arch = "x86_64"))]
    let f = match Backend::select(detected()) {
        Backend::Baseline => crate::arch::ed25519::vg_ed25519_scalar_base,
    };
    // SAFETY: the output, scalar, and scratch are distinct objects valid
    // for 32, 32, and 8192 bytes, respectively, without address-space wrapping,
    // and the CPU has the features of the function `select` chose.
    unsafe { f(&mut out, scalar, scratch) };
    out
}

fn reduce(wide: &[u8; 64], scratch: &mut [u64; 1024]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: the output, wide scalar, and scratch are distinct objects valid
    // for 32, 64, and 8192 bytes, respectively, without address-space wrapping.
    unsafe { vg_ed25519_scalar_reduce(&mut out, wide, scratch) };
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The baseline agrees with the implementation chosen for this CPU, and
    /// the choice follows the features.
    #[test]
    fn backends() {
        let key = SigningKey::from_seed(&[0x42; 32]);
        let signature = key.sign(b"backends");
        assert!(key.verifying_key().verify(b"backends", &signature).is_ok());
        assert_eq!(Backend::select(Features(0)), Backend::Baseline);
        #[cfg(target_arch = "x86_64")]
        {
            let mut out = [0u8; 32];
            let mut scratch = [0u64; 1024];
            let mut scalar = [0x24u8; 32];
            scalar[31] = 0x44;
            // SAFETY: as in `scalar_base`, and the baseline needs no CPU feature.
            unsafe { vg_ed25519_scalar_base_precomputed(&mut out, &scalar, &mut scratch) };
            assert_eq!(out, scalar_base(&scalar, &mut scratch));
            let adx = Features::of(VG_ED25519_VERIFY_EQUATION_ADX_FEATURES);
            assert_eq!(Backend::select(adx), Backend::Adx);
            assert_eq!(Backend::select(Features::of(&["bmi2"])), Backend::Baseline);
            let ifma = Features::of(VG_ED25519_VERIFY_EQUATION_IFMA_FEATURES);
            assert_eq!(Backend::select(ifma), Backend::Ifma);
            assert_eq!(
                Backend::select(Features(adx.0 | Features::of(&["avx512ifma"]).0)),
                Backend::Adx
            );
        }
    }
}
