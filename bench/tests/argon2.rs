//! Differential complete derivations against OpenSSL, including H′ boundaries.

#![cfg(all(target_arch = "x86_64", feature = "openssl-argon2"))]

use verified_garbage::argon2::{Params, Variant, derive_keyed};

type Oracle = fn(
    Option<&openssl::lib_ctx::LibCtxRef>,
    &[u8],
    &[u8],
    Option<&[u8]>,
    Option<&[u8]>,
    u32,
    u32,
    u32,
    &mut [u8],
) -> Result<(), openssl::error::ErrorStack>;

#[test]
fn matches_openssl() {
    for (variant, oracle) in [
        (Variant::Argon2d, openssl::kdf::argon2d as Oracle),
        (Variant::Argon2i, openssl::kdf::argon2i),
        (Variant::Argon2id, openssl::kdf::argon2id),
    ] {
        for (lanes, memory) in [(1, 8), (1, 9), (2, 16), (3, 25), (2, 1040)] {
            for iterations in [1, 2] {
                for length in [4, 32, 64, 65, 96, 128] {
                    for (password, secret, ad) in [
                        (&b""[..], &b""[..], &b""[..]),
                        (&b"password"[..], &b"secret"[..], &b"associated data"[..]),
                    ] {
                        let mut expected = vec![0; length];
                        oracle(
                            None,
                            password,
                            b"saltsalt",
                            Some(ad),
                            Some(secret),
                            iterations,
                            lanes,
                            memory,
                            &mut expected,
                        )
                        .unwrap();
                        let mut actual = vec![0; length];
                        derive_keyed(
                            &Params {
                                variant,
                                iterations,
                                memory_kib: memory,
                                lanes,
                            },
                            password,
                            b"saltsalt",
                            secret,
                            ad,
                            usize::MAX,
                            &mut actual,
                        )
                        .unwrap();
                        assert_eq!(
                            actual, expected,
                            "{variant:?}, lanes={lanes}, memory={memory}, passes={iterations}, length={length}"
                        );
                    }
                }
            }
        }
    }
}
