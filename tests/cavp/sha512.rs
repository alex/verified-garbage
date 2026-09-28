//! SHA-384, SHA-512, SHA-512/224 and SHA-512/256: for each, every message
//! length from 0 to 128 bytes, 128 long messages (from 227 to 12800 bytes)
//! and the Monte Carlo test.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha512::{Sha384, Sha512, Sha512_224, Sha512_256};

macro_rules! cavp {
    ($name:ident, $hash:ident, $file:literal) => {
        mod $name {
            use super::*;

            #[test]
            fn short_messages() {
                let n = check_messages(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/sha512/",
                        $file,
                        "ShortMsg.rsp"
                    )),
                    $hash::digest,
                );
                assert_eq!(n, 129);
            }

            #[test]
            fn long_messages() {
                let n = check_messages(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/sha512/",
                        $file,
                        "LongMsg.rsp"
                    )),
                    $hash::digest,
                );
                assert_eq!(n, 128);
            }

            #[test]
            fn monte_carlo() {
                check_monte_carlo(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/sha512/",
                        $file,
                        "Monte.rsp"
                    )),
                    $hash::digest,
                );
            }
        }
    };
}

cavp!(sha384, Sha384, "SHA384");
cavp!(sha512, Sha512, "SHA512");
cavp!(sha512_224, Sha512_224, "SHA512_224");
cavp!(sha512_256, Sha512_256, "SHA512_256");
