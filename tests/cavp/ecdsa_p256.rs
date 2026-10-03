//! The P-256 vectors of the FIPS 186-4 ECDSA signature verification test
//! (vectors/nist-cavp-ecdsa/SigVer.rsp): 15 each with SHA-1, SHA-224,
//! SHA-256, SHA-384 and SHA-512, each a message, a public key, a signature
//! and whether it is valid; and, for each valid one, signatures that are not
//! (another hash, `r` and `s` exchanged or out of range) and keys that are
//! not valid public keys, or are not the signer's.
//!
//! `verify_sha256_prehashed` verifies a signature of any 32-byte hash, as
//! its contract says: the leftmost 32 bytes of a longer hash, or a shorter
//! one padded on the left with zeros (FIPS 186-5 §6.4.2), as here.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ecdsa::{Error, P256, VerifyingKey};
use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::hashes::sha224::Sha224;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;

use super::unhex;

const N: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";
const P: &str = "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";

/// Each vector: the key, the hash argument, the signature, and whether it
/// is valid.
type Vector = ([u8; 65], [u8; 32], [u8; 64], bool);

/// A hash function, as a `Vec`.
type Hash = fn(&[u8]) -> Vec<u8>;

/// The hash functions of the file's sections.
const HASHES: [(&str, Hash); 5] = [
    ("SHA-1", |m| Sha1::digest(m).to_vec()),
    ("SHA-224", |m| Sha224::digest(m).to_vec()),
    ("SHA-256", |m| Sha256::digest(m).to_vec()),
    ("SHA-384", |m| Sha384::digest(m).to_vec()),
    ("SHA-512", |m| Sha512::digest(m).to_vec()),
];

/// The hash as the 32-byte argument: its leftmost 32 bytes, or padded on the
/// left with zeros.
fn digest(hash: &str, msg: &[u8]) -> [u8; 32] {
    let (_, f) = HASHES.iter().find(|(name, _)| *name == hash).unwrap();
    let h = f(msg);
    let mut d = [0; 32];
    if h.len() >= 32 {
        d.copy_from_slice(&h[..32]);
    } else {
        d[32 - h.len()..].copy_from_slice(&h);
    }
    d
}

fn vectors() -> Vec<Vector> {
    let text = include_str!("../../vectors/nist-cavp-ecdsa/SigVer.rsp");
    let mut out = Vec::new();
    for section in text.split("\n[").skip(1) {
        let (header, body) = section.split_once(']').unwrap();
        let Some(hash) = header.strip_prefix("P-256,") else {
            continue;
        };
        let fields = super::fields(body);
        assert_eq!(fields.len(), 15 * 6);
        for v in fields.chunks(6) {
            let names: Vec<&str> = v.iter().map(|(k, _)| *k).collect();
            assert_eq!(names, ["Msg", "Qx", "Qy", "R", "S", "Result"]);
            let mut q = [4; 65];
            q[1..33].copy_from_slice(&unhex(v[1].1));
            q[33..].copy_from_slice(&unhex(v[2].1));
            let mut rs = [0; 64];
            rs[..32].copy_from_slice(&unhex(v[3].1));
            rs[32..].copy_from_slice(&unhex(v[4].1));
            out.push((q, digest(hash, &unhex(v[0].1)), rs, v[5].1.starts_with('P')));
        }
    }
    assert_eq!(out.len(), 75);
    out
}

/// The 32-byte number `x + y` modulo 2²⁵⁶.
fn add(x: &[u8], y: &[u8]) -> [u8; 32] {
    let mut out = [0; 32];
    let mut carry = 0;
    for i in (0..32).rev() {
        let v = u16::from(x[i]) + u16::from(y[i]) + carry;
        out[i] = v as u8;
        carry = v >> 8;
    }
    out
}

#[test]
fn ecdsa_p256_sigver() {
    let (mut valid, mut invalid) = (0, 0);
    for (q, d, rs, ok) in vectors() {
        let result = VerifyingKey::<P256>::from_bytes(&q).verify_sha256_prehashed(&d, &rs);
        if ok {
            assert_eq!(result, Ok(()));
            valid += 1;
        } else {
            assert_eq!(result, Err(Error::InvalidSignature));
            invalid += 1;
        }
    }
    assert!(valid > 0 && invalid > 0);
}

/// For each valid vector: another hash, `r` and `s` exchanged, `r` or `s`
/// zero or `n`, and keys that are compressed, off the curve or with `x = p`
/// are refused; `−Q` is a valid key, but the signature does not verify with
/// it.
#[test]
fn ecdsa_p256_sigver_invalid() {
    let (n, p) = (unhex(N), unhex(P));
    for (q, d, rs, ok) in vectors() {
        if !ok {
            continue;
        }
        let mut bad = Vec::new();
        let mut other = d;
        other[31] ^= 1;
        bad.push((q, other, rs));
        let mut sr = [0; 64];
        sr[..32].copy_from_slice(&rs[32..]);
        sr[32..].copy_from_slice(&rs[..32]);
        bad.push((q, d, sr));
        for half in [0, 32] {
            for x in [&[0; 32][..], &n] {
                let mut out_of_range = rs;
                out_of_range[half..half + 32].copy_from_slice(x);
                bad.push((q, d, out_of_range));
            }
        }
        for lead in [0, 2, 3] {
            let mut k = q;
            k[0] = lead;
            bad.push((k, d, rs));
        }
        let mut off_curve = q;
        off_curve[64] ^= 1;
        bad.push((off_curve, d, rs));
        let mut big_x = q;
        big_x[1..33].copy_from_slice(&p);
        bad.push((big_x, d, rs));
        // `−Q = (x, p − y)`, with `p − y = p + (2²⁵⁶ − y)` modulo 2²⁵⁶ and
        // `2²⁵⁶ − y = !y + 1`.
        let not_y: Vec<u8> = q[33..].iter().map(|b| !b).collect();
        let mut one = [0; 32];
        one[31] = 1;
        let mut neg = q;
        neg[33..].copy_from_slice(&add(&p, &add(&not_y, &one)));
        bad.push((neg, d, rs));
        for (k, d, rs) in bad {
            let result = VerifyingKey::<P256>::from_bytes(&k).verify_sha256_prehashed(&d, &rs);
            assert_eq!(result, Err(Error::InvalidSignature));
        }
    }
}
