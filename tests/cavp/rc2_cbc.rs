//! Published RC2 vectors; unmodified sources and provenance live under vectors/.

#![cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "arm",
        target_arch = "aarch64",
        target_arch = "x86"
    ),
    feature = "alloc"
))]

use std::collections::BTreeMap;

use verified_garbage::rc2_cbc::{Error, Rc2CbcDecryptor, Rc2CbcEncryptor};

use super::unhex;

/// What [`Rc2CbcEncryptor`] and [`Rc2CbcDecryptor`] both have, so that
/// each test runs in both directions.
trait Cbc: Sized {
    fn new(key: &[u8], iv: &[u8]) -> Result<Self, Error>;
    fn with_bits(key: &[u8], iv: &[u8], bits: usize) -> Result<Self, Error>;
    fn update(&mut self, data: &[u8]) -> Vec<u8>;
    fn finalize(self) -> Result<Vec<u8>, Error>;
}

macro_rules! cbc {
    ($t:ty) => {
        impl Cbc for $t {
            fn new(key: &[u8], iv: &[u8]) -> Result<Self, Error> {
                <$t>::new(key, iv)
            }
            fn with_bits(key: &[u8], iv: &[u8], bits: usize) -> Result<Self, Error> {
                <$t>::new_with_effective_bits(key, iv, bits)
            }
            fn update(&mut self, data: &[u8]) -> Vec<u8> {
                <$t>::update(self, data)
            }
            fn finalize(self) -> Result<Vec<u8>, Error> {
                <$t>::finalize(self)
            }
        }
    };
}
cbc!(Rc2CbcEncryptor);
cbc!(Rc2CbcDecryptor);

fn fields(text: &str) -> BTreeMap<&str, &str> {
    text.lines()
        .filter_map(|line| line.trim().split_once(" = "))
        .collect()
}

/// `C` turns `input` into `expected`, split at every point and a byte at a
/// time.
fn check_one<C: Cbc>(key: &[u8], iv: &[u8], bits: usize, input: &[u8], expected: &[u8]) {
    for split in 0..=input.len() {
        let mut ctx = C::with_bits(key, iv, bits).unwrap();
        assert!(ctx.update(&[]).is_empty());
        let mut output = ctx.update(&input[..split]);
        assert_eq!(output.len(), split / 8 * 8);
        assert!(ctx.update(&[]).is_empty());
        output.extend(ctx.update(&input[split..]));
        output.extend(ctx.finalize().unwrap());
        assert_eq!(output, expected);
    }
    let mut ctx = C::with_bits(key, iv, bits).unwrap();
    let output: Vec<_> = input.chunks(1).flat_map(|byte| ctx.update(byte)).collect();
    assert_eq!(output, expected);
    assert!(ctx.finalize().unwrap().is_empty());
}

fn check(key: &[u8], iv: &[u8], bits: usize, plaintext: &[u8], ciphertext: &[u8]) {
    assert_eq!(plaintext.len(), ciphertext.len());
    check_one::<Rc2CbcEncryptor>(key, iv, bits, plaintext, ciphertext);
    check_one::<Rc2CbcDecryptor>(key, iv, bits, ciphertext, plaintext);
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
    let mut ctx = Rc2CbcEncryptor::new(&key, &iv).unwrap();
    assert_eq!(ctx.update(&plaintext), ciphertext);
    assert!(ctx.finalize().unwrap().is_empty());
    let mut ctx = Rc2CbcDecryptor::new(&key, &iv).unwrap();
    assert_eq!(ctx.update(&ciphertext), plaintext);
    assert!(ctx.finalize().unwrap().is_empty());
}

fn invalid_parameters_of<C: Cbc>() {
    let key = [0; 16];
    let iv = [0; 8];
    for key in [&[][..], &[0; 129][..]] {
        assert_eq!(C::new(key, &iv).err(), Some(Error::InvalidKeyLength));
    }
    for bits in [0, 1025, usize::MAX] {
        assert_eq!(
            C::with_bits(&key, &iv, bits).err(),
            Some(Error::InvalidEffectiveBits)
        );
    }
    for iv in [&[][..], &[0; 7][..], &[0; 9][..]] {
        assert_eq!(C::new(&key, iv).err(), Some(Error::InvalidIvLength));
    }
}

#[test]
fn invalid_parameters() {
    invalid_parameters_of::<Rc2CbcEncryptor>();
    invalid_parameters_of::<Rc2CbcDecryptor>();
}

fn empty_and_incomplete_of<C: Cbc>() {
    let mut ctx = C::new(&[0; 16], &[0; 8]).unwrap();
    assert!(ctx.update(&[]).is_empty());
    assert!(ctx.finalize().unwrap().is_empty());
    for length in 1..16 {
        if length == 8 {
            continue;
        }
        let mut ctx = C::new(&[0; 16], &[0; 8]).unwrap();
        assert_eq!(ctx.update(&vec![0; length]).len(), length / 8 * 8);
        assert_eq!(ctx.finalize(), Err(Error::IncompleteBlock));
    }
}

#[test]
fn empty_and_incomplete() {
    empty_and_incomplete_of::<Rc2CbcEncryptor>();
    empty_and_incomplete_of::<Rc2CbcDecryptor>();
}

#[test]
fn boundary_key_sizes_roundtrip() {
    // Generated inputs test round trips, not published known answers.
    let input: Vec<u8> = (0..40).collect();
    for len in [1, 8, 128] {
        let key: Vec<u8> = (0..len).map(|i| i as u8).collect();
        for bits in [1, 7, 8, 9, 63, 64, 65, 1023, 1024] {
            let mut enc = Rc2CbcEncryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            let ciphertext = enc.update(&input);
            assert!(enc.finalize().unwrap().is_empty());
            let mut dec = Rc2CbcDecryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            assert_eq!(dec.update(&ciphertext), input);
            assert!(dec.finalize().unwrap().is_empty());
        }
    }
}
