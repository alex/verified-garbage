//! PBKDF2 (`PbkdfTest` vectors).
#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

use serde::Deserialize;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::pbkdf2::{Pbkdf2Hash, pbkdf2_hmac, pbkdf2_hmac_sha256};

use crate::harness::{self, Expectation, Fields, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Case {
    password: Hex,
    salt: Hex,
    iteration_count: u32,
    dk_len: usize,
    dk: Hex,
}

/// Every vector of `name` must derive exactly its key (the files only have
/// valid vectors), with `derive`.
fn check_with(name: &str, derive: fn(&[u8], &[u8], NonZeroU32, &mut [u8])) {
    let file = harness::load::<Fields, Case>(name);
    for (_, test) in file.tests() {
        let c = &test.case;
        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
        let mut dk = vec![0u8; c.dk_len];
        derive(
            &c.password.0,
            &c.salt.0,
            NonZeroU32::new(c.iteration_count).unwrap(),
            &mut dk,
        );
        assert_eq!(dk, c.dk.0, "tcId {}", test.tc_id);
    }
}

fn check<H: Pbkdf2Hash>(name: &str) {
    check_with(name, pbkdf2_hmac::<H>);
}

#[test]
fn pbkdf2_hmac_sha256_vectors() {
    require_vectors!();
    check_with("pbkdf2_hmacsha256_test.json", pbkdf2_hmac_sha256);
    check::<Sha256>("pbkdf2_hmacsha256_test.json");
}

#[cfg(target_arch = "x86_64")]
mod streaming {
    use verified_garbage::hashes::sha1::Sha1;
    use verified_garbage::hashes::sha512::{Sha384, Sha512};

    use super::check;
    use crate::require_vectors;

    #[test]
    fn pbkdf2_hmac_sha1_vectors() {
        require_vectors!();
        check::<Sha1>("pbkdf2_hmacsha1_test.json");
    }

    #[test]
    fn pbkdf2_hmac_sha384_vectors() {
        require_vectors!();
        check::<Sha384>("pbkdf2_hmacsha384_test.json");
    }

    #[test]
    fn pbkdf2_hmac_sha512_vectors() {
        require_vectors!();
        check::<Sha512>("pbkdf2_hmacsha512_test.json");
    }
}
