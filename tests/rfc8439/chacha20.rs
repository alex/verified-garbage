//! ChaCha20: the block function (§2.3.2, Appendix A.1), encryption (§2.4.2,
//! Appendix A.2) and Poly1305 key generation (§2.6.2, Appendix A.4), through
//! the keystream of [`ChaCha20`]. The block function's output for block
//! counter `c` is the first 64 bytes of the keystream from `c`, and the
//! Poly1305 key the first 32 from 0. The RFC's ChaCha states are not checked:
//! the API does not expose them, and the output is their serialization.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::chacha20::ChaCha20;

use super::vectors;

/// The keystream for `key` and the RFC 8439 `nonce` from block counter
/// `counter`.
fn chacha20(key: &[u8], counter: u32, nonce: &[u8]) -> ChaCha20 {
    let mut n = [0; 16];
    n[..4].copy_from_slice(&counter.to_le_bytes());
    n[4..].copy_from_slice(nonce);
    ChaCha20::new(key.try_into().unwrap(), &n)
}

/// The first `len` bytes of the keystream for `key` and `nonce` from block
/// counter `counter`.
fn keystream(key: &[u8], counter: u32, nonce: &[u8], len: usize) -> Vec<u8> {
    let mut out = vec![0; len];
    chacha20(key, counter, nonce).apply_keystream(&mut out);
    out
}

#[test]
fn rfc8439_chacha20_block() {
    let vs = vectors("2.3.2.", "2.4.");
    assert_eq!(vs.len(), 1);
    let v = &vs[0];
    let (key, nonce) = (v.bytes("Key"), v.bytes("Nonce"));
    let block = keystream(&key, v.number("o  Block Count"), &nonce, 64);
    assert_eq!(block, v.get("Serialized Block"));

    let vs = vectors("A.1.", "A.2.");
    assert_eq!(vs.len(), 5);
    for v in &vs {
        let block = keystream(v.get("Key"), v.number("Block Counter"), v.get("Nonce"), 64);
        assert_eq!(block, v.get("Keystream"));
    }
}

/// The example of §2.4.2, whose keystream is also given.
#[test]
fn rfc8439_chacha20_example() {
    let vs = vectors("2.4.2.", "2.5.");
    assert_eq!(vs.len(), 1);
    let v = &vs[0];
    let (key, nonce) = (v.bytes("Key"), v.bytes("Nonce"));
    let counter = v.number("o  Initial Counter");
    let pt = v.get("Plaintext Sunscreen");
    assert_eq!(
        keystream(&key, counter, &nonce, pt.len()),
        v.get("Keystream")
    );
    let mut data = pt.to_vec();
    chacha20(&key, counter, &nonce).apply_keystream(&mut data);
    assert_eq!(data, v.get("Ciphertext Sunscreen"));
}

/// Appendix A.2, encrypting and decrypting each vector in two pieces split
/// at every position (including all at once).
#[test]
fn rfc8439_chacha20_encryption() {
    let vs = vectors("A.2.", "A.3.");
    let lens: Vec<usize> = vs.iter().map(|v| v.get("Plaintext").len()).collect();
    assert_eq!(lens, [64, 375, 127]);
    for v in &vs {
        let (key, nonce) = (v.get("Key"), v.get("Nonce"));
        let counter = v.number("Initial Block Counter");
        let (pt, ct) = (v.get("Plaintext"), v.get("Ciphertext"));
        for (from, to) in [(pt, ct), (ct, pt)] {
            for i in 0..=from.len() {
                let mut data = from.to_vec();
                let mut c = chacha20(key, counter, nonce);
                let (a, b) = data.split_at_mut(i);
                c.apply_keystream(a);
                c.apply_keystream(b);
                assert_eq!(data, to);
            }
        }
    }
}

/// The Poly1305 key generation of §2.6.2 and Appendix A.4: the first 32
/// bytes of the keystream from block counter 0.
#[test]
fn rfc8439_chacha20_poly1305_key_generation() {
    let vs = vectors("2.6.2.", "2.7.");
    assert_eq!(vs.len(), 1);
    let v = &vs[0];
    let otk = keystream(v.get("Key"), 0, v.get("Nonce"), 32);
    assert_eq!(otk, v.get("Output bytes"));

    let vs = vectors("A.4.", "A.5.");
    assert_eq!(vs.len(), 3);
    for v in &vs {
        let otk = keystream(v.get("The ChaCha20 Key"), 0, v.get("The nonce"), 32);
        assert_eq!(otk, v.get("Poly1305 one-time key"));
    }
}
