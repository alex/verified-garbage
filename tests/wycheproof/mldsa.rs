//! The Wycheproof tests of ML-DSA, for each parameter set: the `MlDsaSign`
//! vectors of `mldsa_*_sign_seed_test.json` (private keys given as seeds)
//! and the `MlDsaVerify` vectors of `mldsa_*_verify_test.json`. The API
//! keeps a private key as its seed, so `mldsa_*_sign_noseed_test.json`,
//! which gives expanded private keys, does not apply.
//!
//! Signing is checked deterministic (`sign_deterministic`, for the vectors
//! without `rnd`) and, with `μ` given, with the vector's randomness (the
//! hidden `sign_internal`); every signature is verified. Invalid vectors
//! are seeds of the wrong length, which the types do not represent, and
//! context strings longer than 255 bytes, which are refused.

#![cfg(target_arch = "x86_64")]

/// Defines the tests of the parameter set `$n` (`"44"`), of the module
/// `$module` and its key types.
macro_rules! mldsa_tests {
    ($n:literal, $module:ident, $SigningKey:ident, $VerifyingKey:ident) => {
        use serde::Deserialize;
        use verified_garbage::$module::{Error, $SigningKey, $VerifyingKey};

        use crate::harness::{self, Expectation, Hex};
        use crate::require_vectors;

        type Sig = [u8; $VerifyingKey::SIGNATURE_SIZE];

        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase")]
        struct SignGroup {
            private_seed: Hex,
            #[serde(default)]
            public_key: Option<Hex>,
        }

        #[derive(Deserialize)]
        struct Sign {
            #[serde(default)]
            msg: Option<Hex>,
            #[serde(default)]
            ctx: Option<Hex>,
            #[serde(default)]
            mu: Option<Hex>,
            #[serde(default)]
            rnd: Option<Hex>,
            #[serde(default)]
            sig: Option<Hex>,
        }

        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase")]
        struct VerifyGroup {
            public_key: Hex,
        }

        #[derive(Deserialize)]
        struct Verify {
            msg: Hex,
            #[serde(default)]
            ctx: Option<Hex>,
            sig: Hex,
        }

        #[test]
        fn sign_seed() {
            require_vectors!();
            let file =
                harness::load::<SignGroup, Sign>(concat!("mldsa_", $n, "_sign_seed_test.json"));
            for (g, test) in file.tests() {
                let c = &test.case;
                let id = test.tc_id;
                let Ok(seed) = <[u8; 32]>::try_from(&g.params.private_seed.0[..]) else {
                    assert_eq!(test.result, Expectation::Invalid, "tcId {id}");
                    continue;
                };
                let key = $SigningKey::from_seed(&seed).unwrap();
                let pk = g.params.public_key.as_ref().map(|pk| &pk.0[..]);
                assert_eq!(pk, Some(&key.verifying_key().as_bytes()[..]), "tcId {id}");
                let ctx = c.ctx.as_ref().map_or(&[][..], |x| &x.0[..]);
                if test.result == Expectation::Valid {
                    let sig: Sig = c.sig.as_ref().unwrap().0[..].try_into().unwrap();
                    let rnd: [u8; 32] = c
                        .rnd
                        .as_ref()
                        .map_or([0; 32], |r| r.0[..].try_into().unwrap());
                    // Every valid vector gives `μ`; some (`Internal`) give no message.
                    let mu: [u8; 64] = c.mu.as_ref().unwrap().0[..].try_into().unwrap();
                    assert_eq!(key.sign_internal(&mu, &rnd), Ok(sig), "tcId {id}");
                    assert_eq!(key.verifying_key().verify_internal(&mu, &sig), Ok(()));
                    if let Some(msg) = &c.msg {
                        if c.rnd.is_none() {
                            assert_eq!(key.sign_deterministic(&msg.0, ctx), Ok(sig), "tcId {id}");
                        }
                        assert_eq!(key.verifying_key().verify(&msg.0, ctx, &sig), Ok(()));
                    }
                } else {
                    // The only invalid vectors with a seed of the right length
                    // have context strings longer than 255 bytes.
                    assert_eq!(test.result, Expectation::Invalid, "tcId {id}");
                    let msg = &c.msg.as_ref().unwrap().0;
                    assert!(ctx.len() > 255, "tcId {id}");
                    assert_eq!(key.sign_deterministic(msg, ctx), Err(Error::ContextTooLong));
                }
            }
        }

        #[test]
        fn verify() {
            require_vectors!();
            let file =
                harness::load::<VerifyGroup, Verify>(concat!("mldsa_", $n, "_verify_test.json"));
            for (g, test) in file.tests() {
                let c = &test.case;
                let id = test.tc_id;
                let pk = <[u8; $VerifyingKey::SIZE]>::try_from(&g.params.public_key.0[..]);
                let sig = <Sig>::try_from(&c.sig.0[..]);
                let ctx = c.ctx.as_ref().map_or(&[][..], |x| &x.0[..]);
                // Keys and signatures of the wrong length are not represented.
                let ok = match (pk, sig) {
                    (Ok(pk), Ok(sig)) => {
                        $VerifyingKey::from_bytes(&pk).verify(&c.msg.0, ctx, &sig) == Ok(())
                    }
                    _ => false,
                };
                assert_eq!(ok, test.result == Expectation::Valid, "tcId {id}");
            }
        }
    };
}

pub(crate) use mldsa_tests;
