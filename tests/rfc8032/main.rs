//! Pure Ed25519 known-answer tests from the vendored RFC 8032, section 7.1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

use verified_garbage::ed25519::{Error, SigningKey, VerifyingKey};

const TEXT: &str = include_str!("../../vectors/rfc8032/rfc8032.txt");

fn hex_lines(text: &str) -> Vec<u8> {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && line.bytes().all(|b| b.is_ascii_hexdigit()))
        .flat_map(|line| {
            assert_eq!(line.len() % 2, 0);
            (0..line.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&line[i..i + 2], 16).unwrap())
        })
        .collect()
}

#[test]
fn ed25519_vectors() {
    let section = TEXT
        .split_once("\n7.1.  Test Vectors for Ed25519\n")
        .unwrap()
        .1
        .split_once("\n7.2.  Test Vectors for Ed25519ctx\n")
        .unwrap()
        .0;
    let mut count = 0;
    for case in section.split("   -----TEST ").skip(1) {
        let (_, secret) = case.split_once("   SECRET KEY:").unwrap();
        let (secret, public) = secret.split_once("   PUBLIC KEY:").unwrap();
        let (public, message) = public.split_once("   MESSAGE (length ").unwrap();
        let (length, message) = message.split_once('\n').unwrap();
        let length: usize = length.split_whitespace().next().unwrap().parse().unwrap();
        let (message, signature) = message.split_once("   SIGNATURE:").unwrap();
        let seed: [u8; 32] = hex_lines(secret).try_into().unwrap();
        let public: [u8; 32] = hex_lines(public).try_into().unwrap();
        let message = hex_lines(message);
        let signature: [u8; 64] = hex_lines(signature).try_into().unwrap();
        assert_eq!(message.len(), length);
        let key = SigningKey::from_seed(&seed);
        assert_eq!(key.seed(), &seed);
        assert_eq!(key.verifying_key().as_bytes(), &public);
        assert_eq!(key.verifying_key(), &VerifyingKey::from_bytes(&public));
        assert_eq!(key.sign(&message), signature);
        assert_eq!(key.clone().sign(&message), signature);
        assert_eq!(key.verifying_key().verify(&message, &signature), Ok(()));
        let mut changed_message = message.clone();
        changed_message.push(0);
        assert_eq!(
            key.verifying_key().verify(&changed_message, &signature),
            Err(Error::InvalidSignature)
        );
        assert_eq!(format!("{key:?}"), "SigningKey { .. }");
        count += 1;
    }
    assert_eq!(count, 5);
}

fn rfc_seed() -> [u8; 32] {
    let section = TEXT
        .split_once("\n7.1.  Test Vectors for Ed25519\n")
        .unwrap()
        .1;
    let secret = section.split_once("   SECRET KEY:").unwrap().1;
    let secret = secret.split_once("   PUBLIC KEY:").unwrap().0;
    hex_lines(secret).try_into().unwrap()
}

#[repr(align(8))]
struct Aligned<const N: usize>([u8; N]);

#[test]
fn message_boundaries_and_unaligned_inputs() {
    let key = SigningKey::from_seed(&rfc_seed());
    let mut storage = Aligned([0u8; 258]);
    for (i, byte) in storage.0.iter_mut().enumerate() {
        *byte = (i as u8).wrapping_mul(29).wrapping_add(7);
    }
    // Signing hashes a 32-byte nonce prefix and a 64-byte challenge prefix.
    // Exercise SHA-512's 112-byte padding and 128-byte block boundaries,
    // including a second block, and messages starting at an unaligned address.
    for len in [
        0, 1, 47, 48, 49, 63, 64, 65, 79, 80, 81, 95, 96, 97, 127, 128, 129, 175, 176, 207, 208,
        223, 224, 255, 256, 257,
    ] {
        let message = &storage.0[1..1 + len];
        assert_eq!(message.as_ptr() as usize % 8, 1);
        let signature = key.sign(message);
        assert_eq!(key.sign(message), signature, "message length {len}");
        let mut signature_storage = Aligned([0u8; 65]);
        signature_storage.0[1..].copy_from_slice(&signature);
        let signature = &signature_storage.0[1..];
        assert_eq!(signature.as_ptr() as usize % 8, 1);
        assert_eq!(
            key.verifying_key().verify(message, signature),
            Ok(()),
            "message length {len}"
        );
    }
}

#[test]
fn signing_with_aliased_read_only_inputs() {
    let key = SigningKey::from_seed(&rfc_seed());
    // The message may alias either immutable key input to cached signing.
    // Separate copies must produce the same deterministic signature.
    let seed_copy = *key.seed();
    let seed_signature = key.sign(key.seed());
    assert_eq!(seed_signature, key.sign(&seed_copy));
    assert_eq!(
        key.verifying_key().verify(key.seed(), &seed_signature),
        Ok(())
    );

    let public_copy = *key.verifying_key().as_bytes();
    let public_signature = key.sign(key.verifying_key().as_bytes());
    assert_eq!(public_signature, key.sign(&public_copy));
    assert_eq!(
        key.verifying_key()
            .verify(key.verifying_key().as_bytes(), &public_signature),
        Ok(())
    );
}
