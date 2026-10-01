//! Published RC2 vectors; unmodified sources and provenance live under vectors/.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "arm", target_arch = "aarch64"),
    feature = "alloc"
))]

use std::collections::BTreeMap;

use verified_garbage::rc2_cbc::{Direction, Error, Rc2Cbc};

use super::unhex;

fn fields(text: &str) -> BTreeMap<&str, &str> {
    text.lines()
        .filter_map(|line| line.trim().split_once(" = "))
        .collect()
}

fn check(key: &[u8], iv: &[u8], bits: usize, plaintext: &[u8], ciphertext: &[u8]) {
    assert_eq!(plaintext.len(), ciphertext.len());
    for (direction, input, expected) in [
        (Direction::Encrypt, plaintext, ciphertext),
        (Direction::Decrypt, ciphertext, plaintext),
    ] {
        for split in 0..=input.len() {
            let mut ctx = Rc2Cbc::init_with_effective_bits(key, iv, direction, bits).unwrap();
            assert!(ctx.update(&[]).is_empty());
            let mut output = ctx.update(&input[..split]);
            assert_eq!(output.len(), split / 8 * 8);
            assert!(ctx.update(&[]).is_empty());
            output.extend(ctx.update(&input[split..]));
            output.extend(ctx.finalize().unwrap());
            assert_eq!(output, expected);
        }
        let mut ctx = Rc2Cbc::init_with_effective_bits(key, iv, direction, bits).unwrap();
        let output: Vec<_> = input.chunks(1).flat_map(|byte| ctx.update(byte)).collect();
        assert_eq!(output, expected);
        assert!(ctx.finalize().unwrap().is_empty());
    }
}

#[test]
fn rfc2268() {
    let text = include_str!("../../vectors/rfc2268/rfc2268.txt");
    let excerpt = text
        .split("5. Test vectors")
        .nth(1)
        .unwrap()
        .split("6. RC2 Algorithm Object Identifier")
        .next()
        .unwrap();
    let mut count = 0;
    for record in excerpt.split("   Key length (bytes) = ").skip(1) {
        let f = fields(record);
        let key_lines = record.split("   Key = ").nth(1).unwrap();
        let mut lines = key_lines.lines();
        let mut key_hex = lines.next().unwrap().to_owned();
        for line in lines.take_while(|line| line.starts_with("         ")) {
            key_hex.push_str(line.trim());
        }
        let key = unhex(&key_hex.replace(' ', ""));
        assert_eq!(
            key.len(),
            record
                .lines()
                .next()
                .unwrap()
                .trim()
                .parse::<usize>()
                .unwrap()
        );
        let bits = f["Effective key length (bits)"].parse().unwrap();
        // A single CBC block with a zero IV is exactly the RFC's block-cipher operation.
        check(
            &key,
            &[0; 8],
            bits,
            &unhex(&f["Plaintext"].replace(' ', "")),
            &unhex(&f["Ciphertext"].replace(' ', "")),
        );
        count += 1;
    }
    assert_eq!(count, 8);
}

#[test]
fn openssl_cbc() {
    let text = include_str!("../../vectors/openssl-rc2/evpciph_rc2.txt");
    let mut count = 0;
    for record in text.split("\n\n") {
        let f = fields(record);
        let Some(cipher) = f.get("Cipher").filter(|name| name.ends_with("CBC")) else {
            continue;
        };
        let default_bits = match *cipher {
            "RC2-40-CBC" => 40,
            "RC2-64-CBC" => 64,
            name => {
                assert_eq!(name, "RC2-CBC");
                128
            }
        };
        let bits = f
            .get("KeyBits")
            .map_or(default_bits, |value| value.parse().unwrap());
        check(
            &unhex(f["Key"]),
            &unhex(f["IV"]),
            bits,
            &unhex(f["Plaintext"]),
            &unhex(f["Ciphertext"]),
        );
        count += 1;
    }
    assert_eq!(count, 7);
}

#[test]
fn cryptography_cbc_and_default_bits() {
    let f = fields(include_str!("../../vectors/cryptography-rc2/rc2-cbc.txt"));
    let key = unhex(f["Key"]);
    let iv = unhex(f["IV"]);
    let plaintext = unhex(f["Plaintext"]);
    let ciphertext = unhex(f["Ciphertext"]);
    check(&key, &iv, 128, &plaintext, &ciphertext);
    for (direction, input, expected) in [
        (Direction::Encrypt, &plaintext, &ciphertext),
        (Direction::Decrypt, &ciphertext, &plaintext),
    ] {
        let mut ctx = Rc2Cbc::init(&key, &iv, direction).unwrap();
        assert_eq!(ctx.update(input), *expected);
        assert!(ctx.finalize().unwrap().is_empty());
    }
}

#[test]
fn invalid_parameters() {
    let key = [0; 16];
    let iv = [0; 8];
    for key in [&[][..], &[0; 129][..]] {
        assert_eq!(
            Rc2Cbc::init(key, &iv, Direction::Encrypt).err(),
            Some(Error::InvalidKeyLength)
        );
    }
    for bits in [0, 1025, usize::MAX] {
        assert_eq!(
            Rc2Cbc::init_with_effective_bits(&key, &iv, Direction::Encrypt, bits).err(),
            Some(Error::InvalidEffectiveBits)
        );
    }
    for iv in [&[][..], &[0; 7][..], &[0; 9][..]] {
        assert_eq!(
            Rc2Cbc::init(&key, iv, Direction::Encrypt).err(),
            Some(Error::InvalidIvLength)
        );
    }
}

#[test]
fn empty_and_incomplete() {
    for direction in [Direction::Encrypt, Direction::Decrypt] {
        let mut ctx = Rc2Cbc::init(&[0; 16], &[0; 8], direction).unwrap();
        assert!(ctx.update(&[]).is_empty());
        assert!(ctx.finalize().unwrap().is_empty());
        for length in 1..16 {
            if length == 8 {
                continue;
            }
            let mut ctx = Rc2Cbc::init(&[0; 16], &[0; 8], direction).unwrap();
            assert_eq!(ctx.update(&vec![0; length]).len(), length / 8 * 8);
            assert_eq!(ctx.finalize(), Err(Error::IncompleteBlock));
        }
    }
}

#[test]
fn boundary_key_sizes_roundtrip() {
    // Generated inputs test round trips, not published known answers.
    let input: Vec<u8> = (0..40).collect();
    for len in [1, 8, 128] {
        let key: Vec<u8> = (0..len).map(|i| i as u8).collect();
        for bits in [1, 7, 8, 9, 63, 64, 65, 1023, 1024] {
            let mut enc =
                Rc2Cbc::init_with_effective_bits(&key, &[1; 8], Direction::Encrypt, bits).unwrap();
            let ciphertext = enc.update(&input);
            assert!(enc.finalize().unwrap().is_empty());
            let mut dec =
                Rc2Cbc::init_with_effective_bits(&key, &[1; 8], Direction::Decrypt, bits).unwrap();
            assert_eq!(dec.update(&ciphertext), input);
            assert!(dec.finalize().unwrap().is_empty());
        }
    }
}
