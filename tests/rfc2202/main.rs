//! The HMAC-MD5 test cases of RFC 2202 (Section 2), which Wycheproof does
//! not have (HMAC-SHA-1, the RFC's other hash function, is tested with
//! Wycheproof's vectors, in `tests/wycheproof/hmac_sha1.rs`).
//!
//! The RFC is vendored under `vectors/rfc2202/` (see `vectors/sources/`
//! for where it comes from) and compiled into the test binary, so these tests
//! always run. Test case 5's truncated MAC is compared with the start of the
//! computed one.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::hashes::md5::Md5;
use verified_garbage::hmac::Hmac;

const RFC: &str = include_str!("../../vectors/rfc2202/rfc2202.txt");

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "{s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// A value: `0x<hex>`, `0x<hh> repeated <n> times`, or a quoted string.
fn value(v: &str) -> Vec<u8> {
    if let Some(s) = v.strip_prefix('"') {
        return s.strip_suffix('"').expect("unterminated string").into();
    }
    let hex = v.strip_prefix("0x").expect("bad value");
    match hex.split_once(" repeated ") {
        Some((b, n)) => {
            let n = n.strip_suffix(" times").expect("bad count");
            unhex(b).repeat(n.parse().unwrap())
        }
        None => unhex(hex),
    }
}

/// A test case: the key, the data and the (possibly truncated) MAC.
struct Case {
    key: Vec<u8>,
    data: Vec<u8>,
    mac: Vec<u8>,
}

/// The test cases of the section of the RFC between the lines `start` and
/// `stop`. A field starts at the beginning of a line (`name =  value`, or
/// `name  value`), and an indented line, or one of a single word, continues
/// the previous one's value; the page footers and headers are skipped.
fn cases(start: &str, stop: &str) -> Vec<Case> {
    let mut groups: Vec<(String, Vec<(String, String)>)> = Vec::new();
    let section = RFC
        .lines()
        .skip_while(|l| *l != start)
        .skip(1)
        .take_while(|l| *l != stop)
        .filter(|l| !l.contains("[Page ") && !l.starts_with("RFC 2202"));
    for l in section {
        if l.trim().is_empty() {
            continue;
        }
        if l.starts_with(' ') || !l.contains(' ') {
            let (_, v) = groups.last_mut().unwrap().1.last_mut().unwrap();
            v.push(' ');
            v.push_str(l.trim());
            continue;
        }
        let (name, rest) = l.split_once(' ').unwrap();
        let rest = rest.trim_start();
        let rest = rest.strip_prefix('=').unwrap_or(rest).trim().to_string();
        if name == "test_case" {
            groups.push((rest, Vec::new()));
        } else {
            groups.last_mut().unwrap().1.push((name.to_string(), rest));
        }
    }
    let mut out = Vec::new();
    for (n, fields) in &groups {
        assert_eq!(*n, (out.len() + 1).to_string());
        let get = |name: &str| {
            let (_, v) = fields.iter().find(|(f, _)| f == name).unwrap();
            v.as_str()
        };
        let case = Case {
            key: value(get("key")),
            data: value(get("data")),
            mac: value(get("digest")),
        };
        assert_eq!(case.key.len(), get("key_len").parse::<usize>().unwrap());
        assert_eq!(case.data.len(), get("data_len").parse::<usize>().unwrap());
        out.push(case);
    }
    assert_eq!(out.len(), 7);
    out
}

/// Checks the cases, at once and one byte at a time, with each
/// implementation this CPU can run.
#[test]
fn hmac_md5() {
    for c in cases("2. Test Cases for HMAC-MD5", "3. Test Cases for HMAC-SHA-1") {
        let full = Hmac::<Md5>::mac(&c.key, &c.data);
        assert_eq!(full.as_ref().len(), Md5::OUTPUT_SIZE);
        assert_eq!(&full.as_ref()[..c.mac.len()], &c.mac[..]);
        for mask in [u32::MAX, 0] {
            let mut h = Hmac::<Md5>::__with_features(&c.key, mask);
            for byte in &c.data {
                h.update(core::slice::from_ref(byte));
            }
            assert_eq!(h.finalize().as_ref(), full.as_ref());
        }
    }
}
