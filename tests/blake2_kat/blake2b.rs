//! BLAKE2b-512: the 256 unkeyed and 256 keyed vectors, in one call and split
//! into two pieces at every position.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

use verified_garbage::hashes::HashFunction;
use verified_garbage::hashes::blake2b::{Blake2b, Blake2b512};

use super::vectors;

#[test]
fn blake2b_kat() {
    let vs = vectors("blake2b");
    assert_eq!(vs.len(), 512);
    let mut keyed = 0;
    for v in &vs {
        if v.key.is_empty() {
            assert_eq!(Blake2b512::digest(&v.input)[..], v.out[..]);
            assert_eq!(
                <Blake2b512 as HashFunction>::digest(&v.input)[..],
                v.out[..]
            );
        } else {
            assert_eq!(v.key.len(), 64);
            keyed += 1;
        }
        assert_eq!(Blake2b512::digest_keyed(&v.key, &v.input)[..], v.out[..]);
    }
    assert_eq!(keyed, 256);
}

#[test]
fn blake2b_kat_split() {
    for v in &vectors("blake2b") {
        for i in 0..=v.input.len() {
            let mut h = Blake2b::<64>::new_keyed(&v.key);
            h.update(&v.input[..i]);
            h.update(&v.input[i..]);
            assert_eq!(h.finalize()[..], v.out[..]);
        }
    }
}

/// `Default` is `new`, and `HashFunction`'s methods are the type's own.
#[test]
fn blake2b_default_and_trait() {
    let v = &vectors("blake2b")[200];
    assert!(v.key.is_empty());
    let mut h = Blake2b512::default();
    h.update(&v.input);
    assert_eq!(h.finalize()[..], v.out[..]);
    let mut h = <Blake2b512 as HashFunction>::new();
    HashFunction::update(&mut h, &v.input);
    assert_eq!(HashFunction::finalize(h)[..], v.out[..]);
    assert_eq!(<Blake2b512 as HashFunction>::OUTPUT_SIZE, 64);
    assert_eq!(<Blake2b512 as HashFunction>::BLOCK_SIZE, 128);
    assert_eq!(Blake2b::<20>::OUTPUT_SIZE, 20);
    assert_eq!(Blake2b512::BLOCK_SIZE, 128);
    assert_eq!(Blake2b512::MAX_SIZE, 64);
}

#[test]
#[should_panic(expected = "key too long")]
fn blake2b_key_too_long() {
    Blake2b512::new_keyed(&[0; 65]);
}
