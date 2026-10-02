//! ChaCha20-Poly1305: the example of §2.8.2 and the decryption of
//! Appendix A.5, through [`ChaCha20Poly1305`], and the steps of the
//! construction they show (the one-time Poly1305 key, the ciphertext and
//! the tag of the Poly1305 input), through [`ChaCha20`] and [`Poly1305`].

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::chacha20::ChaCha20;
use verified_garbage::chacha20poly1305::{ChaCha20Poly1305, Error};
use verified_garbage::poly1305::Poly1305;

use super::vectors;

/// An AEAD test vector, with the steps of the construction the RFC shows.
struct Vector {
    key: [u8; 32],
    nonce: [u8; 12],
    aad: Vec<u8>,
    pt: Vec<u8>,
    ct: Vec<u8>,
    tag: [u8; 16],
    /// The one-time Poly1305 key, and the input whose tag is `tag`.
    otk: Vec<u8>,
    mac_input: Vec<u8>,
}

/// §2.8.2, whose nonce is the 32-bit fixed-common part followed by the IV,
/// and Appendix A.5.
fn aead_vectors() -> [Vector; 2] {
    let vs = vectors("2.8.2.", "3.");
    assert_eq!(vs.len(), 1);
    let v = &vs[0];
    let nonce = [v.get("32-bit fixed-common part"), v.get("IV")].concat();
    let example = Vector {
        key: v.get("Key").try_into().unwrap(),
        nonce: nonce[..].try_into().unwrap(),
        aad: v.get("AAD").to_vec(),
        pt: v.get("Plaintext").to_vec(),
        ct: v.get("Ciphertext").to_vec(),
        tag: v.get("Tag").try_into().unwrap(),
        otk: v.get("Poly1305 Key").to_vec(),
        mac_input: v.get("AEAD Construction for Poly1305").to_vec(),
    };

    let vs = vectors("A.5.", "Appendix B.");
    assert_eq!(vs.len(), 1);
    let v = &vs[0];
    let decryption = Vector {
        key: v.get("The ChaCha20 Key").try_into().unwrap(),
        nonce: v.get("The nonce").try_into().unwrap(),
        aad: v.get("The AAD").to_vec(),
        pt: v.get("Plaintext").to_vec(),
        ct: v.get("Ciphertext").to_vec(),
        tag: v.get("Received Tag").try_into().unwrap(),
        otk: v.get("Poly1305 one-time key").to_vec(),
        mac_input: v.get("Poly1305 Input").to_vec(),
    };
    [example, decryption]
}

#[test]
fn rfc8439_chacha20poly1305() {
    for v in &aead_vectors() {
        let aead = ChaCha20Poly1305::new(&v.key);
        let mut data = v.pt.clone();
        assert_eq!(
            aead.encrypt_in_place(&v.nonce, &v.aad, &mut data),
            Ok(v.tag)
        );
        assert_eq!(data, v.ct);
        let res = aead.decrypt_in_place(&v.nonce, &v.aad, &mut data, &v.tag);
        assert_eq!(res, Ok(()));
        assert_eq!(data, v.pt);
    }
}

/// Changing a bit of the tag, the ciphertext or the additional data makes
/// decryption fail, and zero the data.
#[test]
fn rfc8439_chacha20poly1305_forgery() {
    for v in &aead_vectors() {
        let aead = ChaCha20Poly1305::new(&v.key);
        let mut tag = v.tag;
        tag[0] ^= 1;
        let mut ct = v.ct.clone();
        ct[0] ^= 1;
        let mut aad = v.aad.clone();
        aad[0] ^= 1;
        let forgeries = [
            (&v.aad, &v.ct, &tag),
            (&v.aad, &ct, &v.tag),
            (&aad, &v.ct, &v.tag),
        ];
        for (aad, ct, tag) in forgeries {
            let mut data = ct.clone();
            let res = aead.decrypt_in_place(&v.nonce, aad, &mut data, tag);
            assert_eq!(res, Err(Error::TagMismatch));
            assert_eq!(data, vec![0; ct.len()]);
        }
    }
}

/// The steps of the construction (§2.8): the one-time key is the first 32
/// bytes of the keystream from block counter 0, the ciphertext is the
/// plaintext XORed with the keystream from 1, and the tag is the Poly1305
/// tag of the input the RFC shows.
#[test]
fn rfc8439_chacha20poly1305_steps() {
    for v in &aead_vectors() {
        let mut nonce = [0; 16];
        nonce[4..].copy_from_slice(&v.nonce);
        let mut otk = [0; 32];
        ChaCha20::new(&v.key, &nonce).apply_keystream(&mut otk);
        assert_eq!(otk[..], v.otk[..]);
        nonce[0] = 1;
        let mut data = v.pt.clone();
        ChaCha20::new(&v.key, &nonce).apply_keystream(&mut data);
        assert_eq!(data, v.ct);
        assert_eq!(Poly1305::mac(&otk, &v.mac_input), v.tag);
    }
}
