//! Published RC2 vectors; unmodified sources and provenance live under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86"
))]

use std::collections::BTreeMap;

use verified_garbage::rc2_cbc::{Error, Rc2CbcDecryptor, Rc2CbcEncryptor};

use super::unhex;

/// What [`Rc2CbcEncryptor`] and [`Rc2CbcDecryptor`] both have, so that
/// each test runs in both directions.
trait Cbc: Sized {
    fn new(key: &[u8], iv: &[u8]) -> Result<Self, Error>;
    fn with_bits(key: &[u8], iv: &[u8], bits: usize) -> Result<Self, Error>;
    fn output_len(&self, input_len: usize) -> usize;
    fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error>;
    fn finalize(self) -> Result<(), Error>;
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
            fn output_len(&self, input_len: usize) -> usize {
                <$t>::output_len(self, input_len)
            }
            fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
                <$t>::update(self, input, output)
            }
            fn finalize(self) -> Result<(), Error> {
                <$t>::finalize(self)
            }
        }
    };
}
cbc!(Rc2CbcEncryptor);
cbc!(Rc2CbcDecryptor);

/// A byte the tests fill output buffers with, to see what an update writes.
const UNWRITTEN: u8 = 0xa5;

/// Updates `ctx` with `input` into a buffer of `output_len` and `extra`
/// more bytes, and returns what it wrote. First, if the update writes
/// anything, checks that a buffer one byte shorter fails with
/// `OutputTooSmall`, writing nothing and changing nothing (so the update
/// after it still produces the right output).
fn feed<C: Cbc>(ctx: &mut C, input: &[u8], extra: usize) -> Vec<u8> {
    let len = ctx.output_len(input.len());
    assert!(len <= input.len() + 7);
    if len > 0 {
        let mut short = vec![UNWRITTEN; len - 1];
        assert_eq!(ctx.update(input, &mut short), Err(Error::OutputTooSmall));
        assert!(short.iter().all(|&b| b == UNWRITTEN));
        assert_eq!(ctx.output_len(input.len()), len);
    }
    let mut output = vec![UNWRITTEN; len + extra];
    assert_eq!(ctx.update(input, &mut output), Ok(len));
    assert!(output[len..].iter().all(|&b| b == UNWRITTEN));
    output.truncate(len);
    output
}

fn fields(text: &str) -> BTreeMap<&str, &str> {
    text.lines()
        .filter_map(|line| line.trim().split_once(" = "))
        .collect()
}

/// `C` turns `input` into `expected`, split at every point and in chunks
/// of several sizes (a byte at a time, among others), into outputs exactly
/// as long as it writes and with room to spare.
fn check_one<C: Cbc>(key: &[u8], iv: &[u8], bits: usize, input: &[u8], expected: &[u8]) {
    for extra in [0, 1, 7] {
        for split in 0..=input.len() {
            let mut ctx = C::with_bits(key, iv, bits).unwrap();
            assert!(feed(&mut ctx, &[], extra).is_empty());
            let mut output = feed(&mut ctx, &input[..split], extra);
            assert_eq!(output.len(), split / 8 * 8);
            assert!(feed(&mut ctx, &[], extra).is_empty());
            output.extend(feed(&mut ctx, &input[split..], extra));
            ctx.finalize().unwrap();
            assert_eq!(output, expected);
        }
        for chunk in [1, 3, 8, 13] {
            let mut ctx = C::with_bits(key, iv, bits).unwrap();
            let output: Vec<_> = input
                .chunks(chunk)
                .flat_map(|part| feed(&mut ctx, part, extra))
                .collect();
            assert_eq!(output, expected);
            ctx.finalize().unwrap();
        }
    }
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
    let mut output = vec![0; plaintext.len()];
    let mut ctx = Rc2CbcEncryptor::new(&key, &iv).unwrap();
    assert_eq!(ctx.update(&plaintext, &mut output), Ok(plaintext.len()));
    assert_eq!(output, ciphertext);
    ctx.finalize().unwrap();
    let mut ctx = Rc2CbcDecryptor::new(&key, &iv).unwrap();
    assert_eq!(ctx.update(&ciphertext, &mut output), Ok(ciphertext.len()));
    assert_eq!(output, plaintext);
    ctx.finalize().unwrap();
}

/// A failed update changes nothing: after an output one byte too short,
/// the same update with enough room produces the known answer.
fn output_too_small_of<C: Cbc>(key: &[u8], iv: &[u8], input: &[u8], expected: &[u8]) {
    let mut ctx = C::new(key, iv).unwrap();
    let mut output = vec![UNWRITTEN; input.len()];
    // Five bytes pending complete no block, so they need no room.
    assert_eq!(ctx.update(&input[..5], &mut []), Ok(0));
    assert_eq!(ctx.output_len(3), 8);
    for len in [0, 7] {
        assert_eq!(
            ctx.update(&input[5..8], &mut output[..len]),
            Err(Error::OutputTooSmall)
        );
    }
    assert!(output.iter().all(|&b| b == UNWRITTEN));
    assert_eq!(ctx.update(&input[5..8], &mut output[..8]), Ok(8));
    assert_eq!(
        ctx.update(&input[8..], &mut output[8..]),
        Ok(input.len() - 8)
    );
    assert_eq!(output, expected);
    ctx.finalize().unwrap();
}

#[test]
fn output_too_small() {
    let f = fields(include_str!("../../vectors/cryptography-rc2/rc2-cbc.txt"));
    let key = unhex(f["Key"]);
    let iv = unhex(f["IV"]);
    let plaintext = unhex(f["Plaintext"]);
    let ciphertext = unhex(f["Ciphertext"]);
    output_too_small_of::<Rc2CbcEncryptor>(&key, &iv, &plaintext, &ciphertext);
    output_too_small_of::<Rc2CbcDecryptor>(&key, &iv, &ciphertext, &plaintext);
}

fn output_len_of<C: Cbc>() {
    let mut ctx = C::new(&[0; 16], &[0; 8]).unwrap();
    for (input_len, len) in [(0, 0), (1, 0), (7, 0), (8, 8), (15, 8), (16, 16), (17, 16)] {
        assert_eq!(ctx.output_len(input_len), len);
    }
    assert_eq!(ctx.output_len(usize::MAX), usize::MAX - 7);
    assert_eq!(ctx.update(&[0; 5], &mut []), Ok(0));
    for (input_len, len) in [(0, 0), (2, 0), (3, 8), (10, 8), (11, 16)] {
        assert_eq!(ctx.output_len(input_len), len);
    }
    // Five pending bytes and `usize::MAX` more overflow: saturated.
    assert_eq!(ctx.output_len(usize::MAX), usize::MAX);
    assert_eq!(ctx.output_len(usize::MAX - 5), usize::MAX - 7);
}

#[test]
fn output_len() {
    output_len_of::<Rc2CbcEncryptor>();
    output_len_of::<Rc2CbcDecryptor>();
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
    let ctx = C::new(&[0; 16], &[0; 8]).unwrap();
    assert_eq!(ctx.finalize(), Ok(()));
    let mut ctx = C::new(&[0; 16], &[0; 8]).unwrap();
    assert_eq!(ctx.update(&[], &mut []), Ok(0));
    assert_eq!(ctx.finalize(), Ok(()));
    for length in 1..16 {
        if length == 8 {
            continue;
        }
        let mut ctx = C::new(&[0; 16], &[0; 8]).unwrap();
        let mut output = vec![0; length + 7];
        assert_eq!(
            ctx.update(&vec![0; length], &mut output),
            Ok(length / 8 * 8)
        );
        assert_eq!(ctx.finalize(), Err(Error::IncompleteBlock));
    }
    // A partial block completed by a later update is not incomplete.
    let mut ctx = C::new(&[0; 16], &[0; 8]).unwrap();
    let mut output = [0; 8];
    assert_eq!(ctx.update(&[0; 3], &mut output), Ok(0));
    assert_eq!(ctx.update(&[0; 5], &mut output), Ok(8));
    assert_eq!(ctx.finalize(), Ok(()));
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
            let mut ciphertext = [0; 40];
            let mut enc = Rc2CbcEncryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            assert_eq!(enc.update(&input, &mut ciphertext), Ok(40));
            enc.finalize().unwrap();
            let mut plaintext = [0; 40];
            let mut dec = Rc2CbcDecryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            assert_eq!(dec.update(&ciphertext, &mut plaintext), Ok(40));
            assert_eq!(plaintext[..], input[..]);
            dec.finalize().unwrap();
        }
    }
}
