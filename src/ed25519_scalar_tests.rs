//! Differential tests of the verified scalar-reduction building block.
#![cfg(target_arch = "x86_64")]

use crate::arch::ed25519::vg_ed25519_scalar_reduce;

// A byte-at-a-time reference with repeated subtraction, independent of
// the assembly's bit-at-a-time carry/borrow and mask implementation.
fn reference(wide: &[u8; 64]) -> [u8; 32] {
    // RFC 8032 section 5.1: L = 2^252 + 27742317777372353535851937790883648493.
    let mut order = [0u8; 33];
    order[..16].copy_from_slice(&27742317777372353535851937790883648493u128.to_le_bytes());
    order[31] = 1 << 4;
    let mut rem = [0u8; 33];
    for byte in wide.iter().rev() {
        rem.copy_within(..32, 1);
        rem[0] = *byte;
        while rem.iter().rev().cmp(order.iter().rev()).is_ge() {
            let mut borrow = 0i16;
            for (r, l) in rem.iter_mut().zip(order) {
                let d = i16::from(*r) - i16::from(l) - borrow;
                *r = d as u8;
                borrow = i16::from(d < 0);
            }
        }
    }
    rem[..32].try_into().unwrap()
}

fn check(wide: &[u8; 64]) {
    let mut out = [0u8; 32];
    let mut scratch = [0u64; 1024];
    // SAFETY: all three arrays have the required sizes and are disjoint.
    unsafe { vg_ed25519_scalar_reduce(&mut out, wide, &mut scratch) };
    assert_eq!(out, reference(wide));
}

#[test]
fn scalar_reduction_generated_inputs() {
    check(&[0; 64]);
    check(&[u8::MAX; 64]);
    for multiple in 1..=4u128 {
        for delta in -1..=1i128 {
            let mut wide = [0u8; 64];
            let low = (multiple * 27742317777372353535851937790883648493) as i128 + delta;
            wide[..16].copy_from_slice(&low.to_le_bytes());
            wide[31] = (multiple as u8) << 4;
            check(&wide);
        }
    }
    for bit in 0..512 {
        let mut wide = [0u8; 64];
        wide[bit / 8] = 1 << (bit % 8);
        check(&wide);
    }
    // Reproducible generated differential cases, not known-answer vectors.
    let mut state = 1u64;
    for _ in 0..128 {
        let mut wide = [0u8; 64];
        for byte in &mut wide {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *byte = state as u8;
        }
        check(&wide);
    }
}
