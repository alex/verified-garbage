//! NIST CAVP ECB vectors, with unmodified sources under vectors/.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use std::collections::BTreeMap;

use verified_garbage::triple_des_ecb::{Direction, Error, TripleDesEcb};

use super::unhex;

fn check(key: &[u8], plaintext: &[u8], ciphertext: &[u8], stream: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    for (direction, input, expected) in [
        (Direction::Encrypt, plaintext, ciphertext),
        (Direction::Decrypt, ciphertext, plaintext),
    ] {
        let mut ctx = TripleDesEcb::init(key, direction).unwrap();
        assert_eq!(ctx.update(input), expected);
        assert!(ctx.finalize().unwrap().is_empty());
        let parity: Vec<_> = key.iter().map(|byte| byte ^ 1).collect();
        let mut ctx = TripleDesEcb::init(&parity, direction).unwrap();
        assert_eq!(ctx.update(input), expected);
        assert!(ctx.finalize().unwrap().is_empty());
        if stream {
            for split in 0..=input.len() {
                let mut ctx = TripleDesEcb::init(key, direction).unwrap();
                assert!(ctx.update(&[]).is_empty());
                let mut output = ctx.update(&input[..split]);
                assert_eq!(output.len(), split / 8 * 8);
                assert!(ctx.update(&[]).is_empty());
                output.extend(ctx.update(&input[split..]));
                output.extend(ctx.finalize().unwrap());
                assert_eq!(output, expected);
            }
            let mut ctx = TripleDesEcb::init(key, direction).unwrap();
            let output: Vec<_> = input.chunks(1).flat_map(|byte| ctx.update(byte)).collect();
            assert_eq!(output, expected);
            assert!(ctx.finalize().unwrap().is_empty());
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
    for direction in [Direction::Encrypt, Direction::Decrypt] {
        for len in 0..=33 {
            let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
            if len == 16 || len == 24 {
                let mut ctx = TripleDesEcb::init(&key, direction).unwrap();
                assert!(ctx.update(&[]).is_empty());
                assert!(ctx.finalize().unwrap().is_empty());
                for n in 1..8 {
                    let mut ctx = TripleDesEcb::init(&key, direction).unwrap();
                    assert!(ctx.update(&[0; 7][..n]).is_empty());
                    assert_eq!(ctx.finalize(), Err(Error::IncompleteBlock));
                }
            } else {
                assert!(matches!(
                    TripleDesEcb::init(&key, direction),
                    Err(Error::InvalidKeyLength)
                ));
            }
        }
    }
}
