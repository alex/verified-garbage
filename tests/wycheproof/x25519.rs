//! X25519 (`XdhComp` vectors of `x25519_test.json`).
//!
//! Every vector, valid or acceptable, has the shared secret RFC 7748's
//! X25519 computes, which [`x25519`] must return. The acceptable ones are
//! public keys of small order (whose shared secret is all zero), and public
//! keys on the twist or not reduced modulo p, which RFC 7748 processes like
//! any other: [`PrivateKey::diffie_hellman`] rejects exactly the all-zero
//! shared secrets.

#![cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "arm"))]

use serde::Deserialize;
use verified_garbage::x25519::{Error, PrivateKey, x25519};

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

#[test]
fn x25519_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("x25519_test.json");
    let mut checked = 0;
    for (group, test) in file.tests() {
        assert_eq!(group.params.curve, "curve25519");
        assert_ne!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
        let private: [u8; 32] = test.case.private.0.clone().try_into().unwrap();
        let public: [u8; 32] = test.case.public.0.clone().try_into().unwrap();
        let shared: [u8; 32] = test.case.shared.0.clone().try_into().unwrap();
        assert_eq!(x25519(&private, &public), shared, "tcId {}", test.tc_id);
        let expected = if shared == [0; 32] {
            Err(Error::ZeroSharedSecret)
        } else {
            Ok(shared)
        };
        let key = PrivateKey::from_bytes(&private);
        assert_eq!(key.diffie_hellman(&public), expected, "tcId {}", test.tc_id);
        checked += 1;
    }
    assert!(checked > 0);
}
