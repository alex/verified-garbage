//! Pure Ed25519 known-answer tests from the vendored RFC 8032, section 7.1.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ed25519::{SigningKey, VerifyingKey};

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
        assert_eq!(format!("{key:?}"), "SigningKey { .. }");
        count += 1;
    }
    assert_eq!(count, 5);
}
