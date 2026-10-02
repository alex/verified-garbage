//! AES-GCM: every vector of the GCM files (read at run time: they are 17
//! MB), encryption with an external IV and decryption, for 128-, 192- and
//! 256-bit keys.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::aes_gcm::{AesGcm, Error};

use super::unhex;

/// The records of a CAVP response file with bracketed section headers (as
/// the GCM files have): each is the `key = value` fields from a `Count` line
/// to the next blank line, and whether it has a bare `FAIL` line.
fn records(text: &str) -> Vec<(Vec<(&str, &str)>, bool)> {
    text.split("\r\n\r\n")
        .flat_map(|chunk| chunk.split("\n\n"))
        .map(|chunk| {
            chunk
                .lines()
                .map(str::trim)
                .filter(|l| !l.is_empty())
                .collect::<Vec<_>>()
        })
        .filter(|lines| lines.first().is_some_and(|l| l.starts_with("Count = ")))
        .map(|lines| {
            let fail = lines.contains(&"FAIL");
            let fields = lines
                .iter()
                .filter(|l| **l != "FAIL")
                .map(|l| l.split_once(" =").map(|(k, v)| (k, v.trim())).unwrap())
                .collect();
            (fields, fail)
        })
        .collect()
}

/// The value of the field `key` of a record.
fn field<'a>(fields: &[(&str, &'a str)], key: &str) -> &'a str {
    fields
        .iter()
        .find(|(k, _)| *k == key)
        .unwrap_or_else(|| panic!("no {key}"))
        .1
}

/// Decrypts `data` with `tag`, whose length the vector gives: the API takes
/// it as a type parameter, so each length §5.2.1.2 allows is a separate call.
fn decrypt(key: &AesGcm, iv: &[u8], aad: &[u8], data: &mut [u8], tag: &[u8]) -> Result<(), Error> {
    match tag.len() {
        4 => key.decrypt_in_place_truncated::<4>(iv, aad, data, tag.try_into().unwrap()),
        8 => key.decrypt_in_place_truncated::<8>(iv, aad, data, tag.try_into().unwrap()),
        12 => key.decrypt_in_place_truncated::<12>(iv, aad, data, tag.try_into().unwrap()),
        13 => key.decrypt_in_place_truncated::<13>(iv, aad, data, tag.try_into().unwrap()),
        14 => key.decrypt_in_place_truncated::<14>(iv, aad, data, tag.try_into().unwrap()),
        15 => key.decrypt_in_place_truncated::<15>(iv, aad, data, tag.try_into().unwrap()),
        // Panics on any other length.
        _ => key.decrypt_in_place(iv, aad, data, tag.try_into().unwrap()),
    }
}

/// Encryption with an external IV must give the ciphertext and the tag
/// (truncated to its length), and decryption must return the plaintext or,
/// for a `FAIL` vector, reject the tag.
#[test]
fn aes_gcm() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("vectors/nist-cavp/gcm");
    let (mut encrypted, mut decrypted, mut failed) = (0, 0, 0);
    for bits in [128, 192, 256] {
        let text = std::fs::read_to_string(dir.join(format!("gcmEncryptExtIV{bits}.rsp"))).unwrap();
        for (r, fail) in records(&text) {
            assert!(!fail);
            let key = AesGcm::new(&unhex(field(&r, "Key"))).unwrap();
            let tag = unhex(field(&r, "Tag"));
            let mut buf = unhex(field(&r, "PT"));
            let t = key
                .encrypt_in_place(&unhex(field(&r, "IV")), &unhex(field(&r, "AAD")), &mut buf)
                .unwrap();
            assert_eq!(buf, unhex(field(&r, "CT")));
            assert_eq!(t[..tag.len()], tag);
            encrypted += 1;
        }
        let text = std::fs::read_to_string(dir.join(format!("gcmDecrypt{bits}.rsp"))).unwrap();
        for (r, fail) in records(&text) {
            let key = AesGcm::new(&unhex(field(&r, "Key"))).unwrap();
            let mut buf = unhex(field(&r, "CT"));
            let tag = unhex(field(&r, "Tag"));
            let result = decrypt(
                &key,
                &unhex(field(&r, "IV")),
                &unhex(field(&r, "AAD")),
                &mut buf,
                &tag,
            );
            if fail {
                assert!(result.is_err());
                failed += 1;
            } else {
                result.unwrap();
                assert_eq!(buf, unhex(field(&r, "PT")));
            }
            decrypted += 1;
        }
    }
    assert_eq!((encrypted, decrypted), (3 * 7875, 3 * 7875));
    assert!(0 < failed && failed < decrypted);
}
