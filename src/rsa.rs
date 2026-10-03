//! The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also the
//! signature verification primitive RSAVP1 (§5.2.2), without any padding.
//!
//! A key is made by the verified `vg_rsa_public_precompute` (contract
//! `VG.Spec.Rsa.publicPrecomputeContract`), which checks the modulus and
//! computes what Montgomery multiplication needs of it once; the operation is
//! the verified `vg_rsa_public_precomputed` (contract
//! `VG.Spec.Rsa.publicPrecomputedContract`), which checks the input, computes
//! `input^e mod n` by Montgomery multiplication, and writes it out. Their
//! timing may depend on the public key (`n` and `e`) but not on the input.
//! On a CPU with BMI2 and ADX, `vg_rsa_public_precompute_adx` and
//! `vg_rsa_public_precomputed_adx`, with the same contracts, do the same with
//! a faster Montgomery multiplication.
//! This module only checks the lengths and allocates the memory they work in.
//!
//! This is a primitive for building padding schemes (OAEP, PSS, PKCS #1
//! v1.5) on: raw RSA on its own is not a secure encryption or signature
//! scheme.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa::{
    VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES, VG_RSA_PUBLIC_PRECOMPUTED_ADX_FEATURES,
    vg_rsa_public_precompute, vg_rsa_public_precompute_adx, vg_rsa_public_precomputed,
    vg_rsa_public_precomputed_adx,
};
use crate::cpu::{Features, detected};

/// The implementations of `vg_rsa_public_precompute` and
/// `vg_rsa_public_precomputed`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline ISA.
    Baseline,
    /// Montgomery multiplication with BMI2's `mulx` and ADX's `adcx` and
    /// `adox`.
    Adx,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    fn select(f: Features) -> Backend {
        if f.contains(const { Features::of(VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES) })
            && f.contains(const { Features::of(VG_RSA_PUBLIC_PRECOMPUTED_ADX_FEATURES) })
        {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }
}

/// The shortest modulus, in bytes (512 bits).
pub const MIN_MODULUS_LEN: usize = 64;
/// The longest modulus, in bytes (8192 bits).
pub const MAX_MODULUS_LEN: usize = 1024;

/// Why an RSA operation was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The modulus is not an odd number of 512 to 8192 bits, written in
    /// as few bytes as it takes.
    InvalidModulus,
    /// The public exponent is empty or longer than the modulus.
    InvalidExponent,
    /// The input or the output is not as long as the modulus.
    InvalidLength,
    /// The input, as a number, is not less than the modulus.
    InputOutOfRange,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidModulus => "invalid RSA modulus",
            Error::InvalidExponent => "invalid RSA public exponent",
            Error::InvalidLength => "RSA input or output length is not the modulus length",
            Error::InputOutOfRange => "RSA input is not less than the modulus",
        })
    }
}

impl core::error::Error for Error {}

/// The words of working space the operations need for an `n_len`-byte
/// modulus (`VG.Spec.Rsa.scratchWords`).
fn scratch_words(n_len: usize) -> usize {
    16 * n_len
}

/// The words of a modulus' precomputed values for an `n_len`-byte modulus
/// (`VG.Spec.Rsa.precomputedWords`).
fn precomputed_words(n_len: usize) -> usize {
    2 * n_len.div_ceil(8)
}

/// An RSA public key `(n, e)`, with the values of `n` that the operation
/// needs (`VG.Spec.Rsa.publicPrecompute`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    n_len: usize,
    e: Vec<u8>,
    pre: Vec<u64>,
}

impl PublicKey {
    /// The key with the modulus `n` and the public exponent `e`, both
    /// big-endian. `n` must be odd, from 512 to 8192 bits long, with no
    /// leading zero byte; `e` must be 1 to `n.len()` bytes long.
    pub fn new(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        let k = n.len();
        if !(MIN_MODULUS_LEN..=MAX_MODULUS_LEN).contains(&k) {
            return Err(Error::InvalidModulus);
        }
        if e.is_empty() || e.len() > k {
            return Err(Error::InvalidExponent);
        }
        let mut pre = vec![0u64; precomputed_words(k)];
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_public_precompute,
            // `select` chose it because the CPU has the features it needs.
            Backend::Adx => vg_rsa_public_precompute_adx,
        };
        // SAFETY: each pointer is valid for its length (`pre` and `scratch`
        // for writes), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; the check above gives
        // `64 ≤ n_len ≤ 1024`, and `pre_len = 2 ⌈n_len / 8⌉` and
        // `scratch_len = 16 n_len`; and the CPU has the features of the
        // function `select` chose.
        let r = unsafe {
            f(
                pre.as_mut_ptr(),
                pre.len(),
                n.as_ptr(),
                k,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds only values of the public modulus, so it is
        // not destroyed. `vg_rsa_public_precompute` refuses a modulus that is
        // not valid (`VG.Spec.Rsa.modulusValid`).
        if r != 1 {
            return Err(Error::InvalidModulus);
        }
        Ok(PublicKey {
            n_len: k,
            e: e.to_vec(),
            pre,
        })
    }

    /// The length of the modulus in bytes, which is that of every input and
    /// output.
    pub fn modulus_len(&self) -> usize {
        self.n_len
    }

    /// RSAEP (RSAVP1): writes `input^e mod n` to `out`, both big-endian and
    /// [`modulus_len`](Self::modulus_len) bytes long. The input must be
    /// less than `n`; on an error `out` is left as zeros.
    pub fn public_op(&self, input: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let k = self.n_len;
        if input.len() != k || out.len() != k {
            return Err(Error::InvalidLength);
        }
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_public_precomputed,
            // `select` chose it because the CPU has the features it needs.
            Backend::Adx => vg_rsa_public_precomputed_adx,
        };
        // SAFETY: each pointer is valid for its length (`out` for writes,
        // `scratch` too), and none overlaps another or wraps around, as they
        // are distinct Rust allocations; `PublicKey::new` and the check above
        // give `64 ≤ out_len ≤ 1024`, `input_len = out_len`,
        // `pre_len = 2 ⌈out_len / 8⌉`, `1 ≤ e_len ≤ out_len`, and
        // `scratch_len = 16 out_len`; `pre` holds what
        // `vg_rsa_public_precompute` (or its variant, with the same contract)
        // wrote for the modulus, returning 1; and the CPU has the features of
        // the function `select` chose.
        let r = unsafe {
            f(
                out.as_mut_ptr(),
                k,
                self.pre.as_ptr(),
                self.pre.len(),
                self.e.as_ptr(),
                self.e.len(),
                input.as_ptr(),
                k,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds powers of the input.
        crate::zeroize::zeroize(&mut scratch);
        // `pre` holds a valid modulus' values (`PublicKey::new`), so a refusal
        // means the input is not below it.
        if r == 1 {
            Ok(())
        } else {
            Err(Error::InputOutOfRange)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    /// An odd `k`-byte modulus with its top bit set, with bytes from a
    /// simple generator so that no word is all ones.
    fn modulus(k: usize) -> Vec<u8> {
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut n: Vec<u8> = (0..k)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x as u8
            })
            .collect();
        n[0] |= 0x80;
        n[k - 1] |= 1;
        n
    }

    fn minus_one(n: &[u8]) -> Vec<u8> {
        let mut m = n.to_vec();
        // `n` is odd: only its last byte changes.
        *m.last_mut().unwrap() -= 1;
        m
    }

    /// `x` as `k` big-endian bytes.
    fn be(x: u64, k: usize) -> Vec<u8> {
        let mut v = vec![0; k];
        v[k - 8..].copy_from_slice(&x.to_be_bytes());
        v
    }

    fn op(n: &[u8], e: &[u8], x: &[u8]) -> Result<Vec<u8>, Error> {
        let mut out = vec![0xa5; n.len()];
        let r = PublicKey::new(n, e)?.public_op(x, &mut out);
        if r.is_err() {
            assert_eq!(out, vec![0; n.len()]);
        }
        r.map(|()| out)
    }

    #[test]
    fn backends() {
        assert_eq!(Backend::select(Features(0)), Backend::Baseline);
        assert_eq!(Backend::select(Features::of(&["bmi2"])), Backend::Baseline);
        assert_eq!(
            Backend::select(Features::of(VG_RSA_PUBLIC_PRECOMPUTED_ADX_FEATURES)),
            Backend::Adx
        );
    }

    /// Identities that hold for every modulus, at every length from 512 to
    /// 8192 bits, including lengths that are not a whole number of words.
    #[test]
    fn identities() {
        for k in [64, 65, 71, 72, 127, 128, 255, 256, 384, 512, 1023, 1024] {
            for n in [modulus(k), vec![0xff; k]] {
                let m1 = minus_one(&n);
                let one = be(1, k);
                assert_eq!(op(&n, &[0], &m1), Ok(one.clone()));
                assert_eq!(op(&n, &[1], &m1), Ok(m1.clone()));
                assert_eq!(op(&n, &[2], &m1), Ok(one.clone()));
                assert_eq!(op(&n, &[0, 3], &m1), Ok(m1.clone()));
                assert_eq!(op(&n, &[1], &one), Ok(one.clone()));
                assert_eq!(op(&n, &[0x41], &vec![0; k]), Ok(vec![0; k]));
                // 2^63 and 2^(8 + 63): no reduction.
                assert_eq!(op(&n, &[63], &be(2, k)), Ok(be(1 << 63, k)));
                let mut big = vec![0; k];
                big[k - 9] = 0x80;
                assert_eq!(op(&n, &[0, 71], &be(2, k)), Ok(big));
                // The input `n - 1` with a long exponent of all ones (odd).
                assert_eq!(op(&n, &vec![0xff; k], &m1), Ok(m1.clone()));
                // Out of range.
                assert_eq!(op(&n, &[3], &n), Err(Error::InputOutOfRange));
                assert_eq!(op(&n, &[3], &vec![0xff; k]), Err(Error::InputOutOfRange));
            }
            // For `n = 2^(8k) - 1`, `2^(8k) = 1` and `2^(8k + 5) = 32`.
            let n = vec![0xff; k];
            let bits = (8 * k) as u64;
            assert_eq!(op(&n, &bits.to_be_bytes(), &be(2, k)), Ok(be(1, k)));
            assert_eq!(
                op(&n, &(bits + 5).to_be_bytes()[6..], &be(2, k)),
                Ok(be(32, k))
            );
        }
    }

    #[test]
    fn invalid() {
        let n = modulus(64);
        assert_eq!(PublicKey::new(&n, &[3]).unwrap().modulus_len(), 64);
        let mut half = n.clone();
        half[0] = 0x7f;
        let mut zero = modulus(65);
        zero[0] = 0;
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        let mut ok = modulus(65);
        ok[0] = 1;
        assert!(PublicKey::new(&ok, &[3]).is_ok());
        let bad: [&[u8]; 6] = [&modulus(63), &half, &zero, &even, &modulus(1025), &[]];
        for bad in bad {
            assert_eq!(PublicKey::new(bad, &[3]), Err(Error::InvalidModulus));
        }
        assert_eq!(PublicKey::new(&n, &[]), Err(Error::InvalidExponent));
        assert_eq!(PublicKey::new(&n, &[1; 65]), Err(Error::InvalidExponent));
        assert!(PublicKey::new(&n, &[1; 64]).is_ok());
        let key = PublicKey::new(&n, &[3]).unwrap();
        let mut out = [0; 64];
        assert_eq!(key.public_op(&[0; 63], &mut out), Err(Error::InvalidLength));
        assert_eq!(
            key.public_op(&[0; 64], &mut out[..63]),
            Err(Error::InvalidLength)
        );
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidModulus,
            Error::InvalidExponent,
            Error::InvalidLength,
            Error::InputOutOfRange,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
