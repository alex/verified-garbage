//! X448 (`XdhComp` vectors of `x448_test.json`).
//!
//! Every vector, valid or acceptable, has the shared secret RFC 7748's
//! X448 computes, which [`x448`] must return. The acceptable ones are
//! public keys of small order (whose shared secret is all zero), and public
//! keys on the twist or not reduced modulo p, which RFC 7748 processes like
//! any other: [`PrivateKey::diffie_hellman`] rejects exactly the all-zero
//! shared secrets. Oversized public keys fail conversion to the API's
//! fixed-size byte array.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use serde::Deserialize;
use verified_garbage::x448::{Error, PrivateKey, x448};

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
fn x448_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("x448_test.json");
    let mut checked = 0;
    for (group, test) in file.tests() {
        assert_eq!(group.params.curve, "curve448");
        checked += 1;
        let public: Result<[u8; 56], _> = test.case.public.0.clone().try_into();
        let public = match public {
            Ok(public) => public,
            Err(_) => {
                assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
                continue;
            }
        };
        assert_ne!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
        let private: [u8; 56] = test.case.private.0.clone().try_into().unwrap();
        let shared: [u8; 56] = test.case.shared.0.clone().try_into().unwrap();
        assert_eq!(x448(&private, &public), shared, "tcId {}", test.tc_id);
        let expected = if shared == [0; 56] {
            Err(Error::ZeroSharedSecret)
        } else {
            Ok(shared)
        };
        let key = PrivateKey::from_bytes(&private);
        assert_eq!(key.diffie_hellman(&public), expected, "tcId {}", test.tc_id);
    }
    assert!(checked > 0);
}
