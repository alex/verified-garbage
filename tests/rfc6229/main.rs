//! All RFC 6229 §2 answers, read from the byte-for-byte vendored RFC.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::rc4::{Error, Rc4};

const TEXT: &str = include_str!("../../vectors/rfc6229/rfc6229.txt");

fn unhex(text: &str) -> Vec<u8> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(hex.len() % 2, 0);
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn every_published_answer_and_streaming_split() {
    let mut keys = 0;
    let mut answers = 0;
    for record in TEXT.split(" Key length: ").skip(1) {
        let bits: usize = record.split_once(" bits.").unwrap().0.parse().unwrap();
        let key = record
            .lines()
            .find_map(|line| line.trim().strip_prefix("key: 0x"))
            .map(unhex)
            .unwrap();
        assert_eq!(bits, key.len() * 8);
        let mut stream = vec![0; 4112];
        let mut cipher = Rc4::new(&key).unwrap();
        cipher.apply_keystream(&mut []);
        cipher.apply_keystream(&mut stream);
        cipher.apply_keystream(&mut []);
        cipher.finalize();
        let mut count = 0;
        for line in record.lines().map(str::trim) {
            if !line.starts_with("DEC") {
                continue;
            }
            let (position, bytes) = line.split_once(':').unwrap();
            let offset: usize = position.split_whitespace().nth(1).unwrap().parse().unwrap();
            let expected = unhex(bytes);
            assert_eq!(expected.len(), 16);
            assert_eq!(&stream[offset..offset + 16], expected);
            let mut cipher = Rc4::new(&key).unwrap();
            let mut skipped = vec![0; offset];
            cipher.apply_keystream(&mut skipped);
            let mut decrypted = expected;
            cipher.apply_keystream(&mut decrypted);
            assert_eq!(decrypted, [0; 16]);
            count += 1;
        }
        assert_eq!(count, 18);
        for split in 0..=32 {
            let mut actual = [0; 32];
            let mut cipher = Rc4::new(&key).unwrap();
            cipher.apply_keystream(&mut actual[..split]);
            cipher.apply_keystream(&mut []);
            cipher.apply_keystream(&mut actual[split..]);
            assert_eq!(actual, stream[..32]);
        }
        for split in [0, 1, 255, 256, 257, 4096, 4112] {
            let mut actual = vec![0; stream.len()];
            let mut cipher = Rc4::new(&key).unwrap();
            cipher.apply_keystream(&mut actual[..split]);
            cipher.apply_keystream(&mut []);
            cipher.apply_keystream(&mut actual[split..]);
            assert_eq!(actual, stream);
        }
        let mut actual = vec![0; stream.len()];
        let mut cipher = Rc4::new(&key).unwrap();
        for byte in &mut actual {
            cipher.apply_keystream(core::slice::from_mut(byte));
        }
        assert_eq!(actual, stream);
        keys += 1;
        answers += count;
    }
    assert_eq!(keys, 14);
    assert_eq!(answers, 252);
}

/// Independent scalar reference for generated boundary inputs, not a
/// source of known-answer vectors. Public APIs always use verified assembly.
fn reference(key: &[u8], data: &mut [u8]) {
    let mut table: Vec<u8> = (0..=255).collect();
    let mut j = 0u8;
    for i in 0..256 {
        j = j.wrapping_add(table[i]).wrapping_add(key[i % key.len()]);
        table.swap(i, usize::from(j));
    }
    let mut i = 0u8;
    j = 0;
    for byte in data {
        i = i.wrapping_add(1);
        j = j.wrapping_add(table[usize::from(i)]);
        table.swap(usize::from(i), usize::from(j));
        let idx = table[usize::from(i)].wrapping_add(table[usize::from(j)]);
        *byte ^= table[usize::from(idx)];
    }
}

#[test]
fn generated_key_boundaries_and_round_trips() {
    assert_eq!(Rc4::new(&[]).err(), Some(Error::InvalidKeyLength));
    assert_eq!(Rc4::new(&[0; 257]).err(), Some(Error::InvalidKeyLength));
    for length in [1, 2, 255, 256] {
        let key: Vec<u8> = (0..length).map(|i| (i * 37) as u8).collect();
        let original: Vec<u8> = (0..513).map(|i| (i * 19 + 7) as u8).collect();
        let mut expected = original.clone();
        reference(&key, &mut expected);
        let mut data = original.clone();
        let mut cipher = Rc4::new(&key).unwrap();
        cipher.apply_keystream(&mut data);
        assert_eq!(data, expected);
        let mut cipher = Rc4::new(&key).unwrap();
        for chunk in data.chunks_mut(17) {
            cipher.apply_keystream(chunk);
        }
        assert_eq!(data, original);
        cipher.finalize();
    }
}
