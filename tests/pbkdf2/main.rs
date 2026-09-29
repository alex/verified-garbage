//! PBKDF2 against its definition (RFC 8018 §5.2), computed with [`Hmac`],
//! for the hash functions without published PBKDF2 test vectors (their HMAC
//! is tested against published vectors in `tests/wycheproof/hmac.rs` and
//! `tests/rfc2202/`), and the others too, so these tests always run.

#![cfg(target_arch = "x86_64")]

use core::num::NonZeroU32;

use verified_garbage::hashes::md5::Md5;
use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha512::{Sha384, Sha512, Sha512_224, Sha512_256};
use verified_garbage::hmac::Hmac;
use verified_garbage::pbkdf2::{Pbkdf2Hash, pbkdf2_hmac};

/// `DK = T₁ ‖ T₂ ‖ …`, truncated to `len` bytes, where
/// `Tᵢ = U₁ ⊕ U₂ ⊕ … ⊕ U_c`, `U₁ = PRF (P, S ‖ INT (i))` and
/// `Uⱼ = PRF (P, Uⱼ₋₁)`.
fn reference<H: Pbkdf2Hash>(password: &[u8], salt: &[u8], c: u32, len: usize) -> Vec<u8> {
    let mut dk = Vec::new();
    let mut i = 1u32;
    while dk.len() < len {
        let mut data = salt.to_vec();
        data.extend_from_slice(&i.to_be_bytes());
        let mut u = Hmac::<H>::mac(password, &data);
        let mut t = u.clone();
        for _ in 1..c {
            u = Hmac::<H>::mac(password, u.as_ref());
            for (t, u) in t.as_mut().iter_mut().zip(u.as_ref()) {
                *t ^= u;
            }
        }
        dk.extend_from_slice(t.as_ref());
        i += 1;
    }
    dk.truncate(len);
    dk
}

/// Passwords shorter than, as long as and longer than a block, derived keys
/// of up to three blocks (the last one partial or whole), and iteration
/// counts from 1.
fn check<H: Pbkdf2Hash>() {
    let d = H::OUTPUT_SIZE;
    for plen in [0, 1, H::BLOCK_SIZE, H::BLOCK_SIZE + 1] {
        let password: Vec<u8> = (0..plen).map(|i| i as u8 ^ 0x5c).collect();
        for (c, len) in [(1, d), (2, 1), (3, d + 1), (5, 2 * d), (17, 3 * d - 1)] {
            let salt: Vec<u8> = (0..len as u8).collect();
            let mut dk = vec![0; len];
            pbkdf2_hmac::<H>(&password, &salt, NonZeroU32::new(c).unwrap(), &mut dk);
            assert_eq!(dk, reference::<H>(&password, &salt, c, len));
        }
    }
}

#[test]
fn pbkdf2_hmac_md5() {
    check::<Md5>();
}

#[test]
fn pbkdf2_hmac_sha1() {
    check::<Sha1>();
}

#[test]
fn pbkdf2_hmac_sha256() {
    check::<Sha256>();
}

#[test]
fn pbkdf2_hmac_sha384() {
    check::<Sha384>();
}

#[test]
fn pbkdf2_hmac_sha512() {
    check::<Sha512>();
}

#[test]
fn pbkdf2_hmac_sha512_224() {
    check::<Sha512_224>();
}

#[test]
fn pbkdf2_hmac_sha512_256() {
    check::<Sha512_256>();
}
