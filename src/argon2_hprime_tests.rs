//! Machine-code checks for Argon2's internal variable-length hash.
#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86"))]

use crate::arch::argon2::vg_argon2_hprime;
use crate::hashes::blake2b::{Blake2b, Blake2bBackend};

#[repr(C)]
struct Scratch {
    before: [u64; 8],
    data: [u64; 2048],
    after: [u64; 8],
}

fn check(input: &[u8], expected: &[u8]) {
    let mut original = [0; 1024];
    original[..input.len()].copy_from_slice(input);
    let backend = Blake2bBackend::select(crate::cpu::detected());
    for fill in [0, u64::MAX, 0xa5a5_a5a5_a5a5_a5a5] {
        let mut scratch = Scratch {
            before: [0x1234_5678_9abc_def0; 8],
            data: [fill; 2048],
            after: [0xfedc_ba98_7654_3210; 8],
        };
        let mut out = [0xa5; 4192];
        let result = &mut out[16..16 + expected.len()];
        // SAFETY: lengths satisfy H′'s bounds, allocations are separate,
        // scratch has 2048 words, and dispatch uses the detected backend.
        unsafe {
            match backend {
                Blake2bBackend::Scalar => vg_argon2_hprime(
                    input.as_ptr(),
                    input.len(),
                    result.as_mut_ptr(),
                    result.len(),
                    &mut scratch.data,
                ),
            }
        }
        assert_eq!(result, expected);
        assert_eq!(&out[..16], &[0xa5; 16]);
        assert_eq!(&out[16 + expected.len()..32 + expected.len()], &[0xa5; 16]);
        assert_eq!(scratch.before, [0x1234_5678_9abc_def0; 8]);
        assert_eq!(scratch.after, [0xfedc_ba98_7654_3210; 8]);
        assert_eq!(input, &original[..input.len()]);
    }
}

fn short<const N: usize>(input: &[u8]) {
    // This is an equivalence check against the public BLAKE2b API,
    // not an embedded known-answer vector.
    let mut hash = Blake2b::<N>::new();
    hash.update(&(N as u32).to_le_bytes());
    hash.update(input);
    check(input, &hash.finalize());
}

fn long<const LAST: usize>(input: &[u8], prefixes: usize) {
    let length = 32 * prefixes + LAST;
    let mut first = Blake2b::<64>::new();
    first.update(&(length as u32).to_le_bytes());
    first.update(input);
    let mut digest = first.finalize();
    let mut expected = [0; 4160];
    let mut cursor = 0;
    for _ in 1..prefixes {
        expected[cursor..cursor + 32].copy_from_slice(&digest[..32]);
        cursor += 32;
        digest = Blake2b::<64>::digest(&digest);
    }
    expected[cursor..cursor + 32].copy_from_slice(&digest[..32]);
    expected[cursor + 32..length].copy_from_slice(&Blake2b::<LAST>::digest(&digest));
    check(input, &expected[..length]);
}

#[test]
fn hprime_matches_blake2b_composition() {
    // H′ prepends four bytes, so test both sides of the resulting
    // BLAKE2b block boundaries as well as ordinary 128-byte boundaries.
    for length in [
        0, 1, 3, 4, 123, 124, 125, 127, 128, 129, 251, 252, 253, 255, 256, 257, 1024,
    ] {
        let data: [u8; 1024] = core::array::from_fn(|i| (i as u8).wrapping_mul(71));
        let input = &data[..length];
        short::<1>(input);
        short::<2>(input);
        short::<3>(input);
        short::<4>(input);
        short::<16>(input);
        short::<31>(input);
        short::<32>(input);
        short::<33>(input);
        short::<63>(input);
        short::<64>(input);
        for prefixes in [1, 2, 3, 30, 31, 128] {
            long::<33>(input, prefixes);
            long::<47>(input, prefixes);
            long::<63>(input, prefixes);
            long::<64>(input, prefixes);
        }
    }
}
