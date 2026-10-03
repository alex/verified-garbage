//! ECDH over P-256 (`EcdhEcpointTest` vectors of
//! `ecdh_secp256r1_ecpoint_test.json`, public keys as SEC 1 octet strings).
//!
//! [`PrivateKey::diffie_hellman`] takes an uncompressed public key: a valid
//! vector must give its shared secret, an invalid one must be refused (or,
//! if not 65 bytes, cannot be passed), and the acceptable ones are
//! compressed keys, which cannot be passed either.

#![cfg(target_arch = "x86_64")]

use serde::Deserialize;
use verified_garbage::ecdh::{Error, P256, PrivateKey};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct Group {
    curve: String,
}

#[derive(Deserialize)]
struct Case {
    public: Hex,
    private: Hex,
    shared: Hex,
}

/// A private key of up to 33 bytes (Wycheproof writes them as signed
/// integers), as 32.
fn private_key(bytes: &[u8]) -> [u8; 32] {
    let bytes = bytes.strip_prefix(&[0]).unwrap_or(bytes);
    let mut d = [0; 32];
    d[32 - bytes.len()..].copy_from_slice(bytes);
    d
}

#[test]
fn ecdh_secp256r1_ecpoint_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdh_secp256r1_ecpoint_test.json");
    let (mut checked, mut refused) = (0, 0);
    for (group, test) in file.tests() {
        assert_eq!(group.params.curve, "secp256r1");
        let key = PrivateKey::<P256>::from_bytes(&private_key(&test.case.private.0));
        let Ok(public) = <[u8; 65]>::try_from(&test.case.public.0[..]) else {
            assert_ne!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
            continue;
        };
        let result = key.diffie_hellman(&public);
        match test.result {
            Expectation::Valid => {
                assert_eq!(
                    result.map(|z| z.to_vec()),
                    Ok(test.case.shared.0.clone()),
                    "tcId {}",
                    test.tc_id
                );
                checked += 1;
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(Error::InvalidKey), "tcId {}", test.tc_id);
                refused += 1;
            }
        }
    }
    assert!(checked > 0 && refused > 0);
}
