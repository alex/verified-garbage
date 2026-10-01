//! NIST CAVP ECB vectors, with unmodified sources under vectors/.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use std::collections::BTreeMap;

use verified_garbage::triple_des_ecb::{Error, TripleDesEcb};

use super::unhex;

fn check(key: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = TripleDesEcb::new(key).unwrap();
    let parity: Vec<_> = key.iter().map(|byte| byte ^ 1).collect();
    let parity_ctx = TripleDesEcb::new(&parity).unwrap();
    for (operation, input, expected) in [
        (
            TripleDesEcb::encrypt as fn(&TripleDesEcb, &mut [u8]) -> Result<(), Error>,
            plaintext,
            ciphertext,
        ),
        (
            TripleDesEcb::decrypt as fn(&TripleDesEcb, &mut [u8]) -> Result<(), Error>,
            ciphertext,
            plaintext,
        ),
    ] {
        for key_ctx in [&ctx, &parity_ctx] {
            let mut output = input.to_vec();
            operation(key_ctx, &mut output).unwrap();
            assert_eq!(output, expected);
        }
        if split {
            for offset in (0..=input.len()).step_by(8) {
                let mut output = input.to_vec();
                operation(&ctx, &mut []).unwrap();
                operation(&ctx, &mut output[..offset]).unwrap();
                operation(&ctx, &mut []).unwrap();
                operation(&ctx, &mut output[offset..]).unwrap();
                assert_eq!(output, expected);
            }
            let mut output = input.to_vec();
            for block in output.chunks_mut(8) {
                operation(&ctx, block).unwrap();
            }
            assert_eq!(output, expected);
        }
    }
}

fn check_file(text: &str, stream: bool) -> usize {
    let mut count = 0;
    for record in text.replace('\r', "").split("\n\n") {
        let fields: BTreeMap<_, _> = record
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        if !fields.contains_key("COUNT") {
            continue;
        }
        let key = if let Some(key) = fields.get("KEYs") {
            let key = unhex(key);
            key.repeat(3)
        } else {
            let mut key = unhex(fields["KEY1"]);
            key.extend(unhex(fields["KEY2"]));
            key.extend(unhex(fields["KEY3"]));
            key
        };
        let plaintext = unhex(fields["PLAINTEXT"]);
        let ciphertext = unhex(fields["CIPHERTEXT"]);
        check(&key, &plaintext, &ciphertext, stream);
        if key[..8] == key[16..] {
            check(&key[..16], &plaintext, &ciphertext, stream);
        }
        count += 1;
    }
    count
}

#[test]
fn nist_ecb() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp-tdes-kat/TECBsubtab.rsp"),
            38,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-tdes-kat/TECBpermop.rsp"),
            64,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-tdes-kat/TECBvarkey.rsp"),
            112,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-tdes-kat/TECBvartext.rsp"),
            128,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-tdes-kat/TECBinvperm.rsp"),
            128,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-tdes-mmt/TECBMMT2.rsp"),
            10,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-tdes-mmt/TECBMMT3.rsp"),
            20,
            true,
        ),
    ];
    let mut total = 0;
    for (text, expected, stream) in files {
        let count = check_file(text, stream);
        assert_eq!(count, expected);
        total += count;
    }
    assert_eq!(total, 500);
}

#[test]
fn limits_and_empty_input() {
    for len in 0..=33 {
        let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
        if len == 16 || len == 24 {
            let ctx = TripleDesEcb::new(&key).unwrap();
            ctx.encrypt(&mut []).unwrap();
            ctx.decrypt(&mut []).unwrap();
            for n in 1usize..24 {
                if n.is_multiple_of(8) {
                    continue;
                }
                let mut buffer = vec![0x5a; n];
                assert_eq!(ctx.encrypt(&mut buffer), Err(Error::IncompleteBlock));
                assert_eq!(buffer, vec![0x5a; n]);
                assert_eq!(ctx.decrypt(&mut buffer), Err(Error::IncompleteBlock));
                assert_eq!(buffer, vec![0x5a; n]);
            }
        } else {
            assert!(matches!(
                TripleDesEcb::new(&key),
                Err(Error::InvalidKeyLength)
            ));
        }
    }
}
