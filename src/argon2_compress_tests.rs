//! Machine-code checks for the internal Argon2 compression primitive.
#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::argon2::vg_argon2_compress;

#[repr(C)]
struct Guard<const N: usize> {
    before: [u64; 8],
    data: [u64; N],
    after: [u64; 8],
}

impl<const N: usize> Guard<N> {
    fn new(fill: u64) -> Self {
        Self {
            before: [u64::MAX; 8],
            data: [fill; N],
            after: [u64::MAX; 8],
        }
    }

    fn check(&self) {
        assert_eq!(self.before, [u64::MAX; 8]);
        assert_eq!(self.after, [u64::MAX; 8]);
    }
}

fn compress(x: &[u64; 128], y: &[u64; 128], fill: u64) -> [u64; 128] {
    let original_x = *x;
    let original_y = *y;
    let mut out = Guard::<128>::new(fill);
    let mut scratch = Guard::<512>::new(!fill);
    // SAFETY: correctly sized, separate allocations meet the emitted contract.
    unsafe { vg_argon2_compress(x, y, &mut out.data, &mut scratch.data) };
    assert_eq!(*x, original_x);
    assert_eq!(*y, original_y);
    out.check();
    scratch.check();
    out.data
}

#[test]
fn compression_depends_on_input_xor() {
    // These are algebraic properties of G(X,Y), not embedded known-answer
    // vectors: equal inputs cancel, and applying the same mask to each
    // input preserves X XOR Y. Exercise every rotation and both word halves.
    for shift in 0..64 {
        let x = core::array::from_fn(|i| (i as u64).wrapping_mul(u64::MAX).rotate_left(shift));
        let y = core::array::from_fn(|i| (i as u64 + 1).rotate_right(shift));
        let mask: [u64; 128] = core::array::from_fn(|i| 1 << (i % 64));
        let masked_x = core::array::from_fn(|i| x[i] ^ mask[i]);
        let masked_y = core::array::from_fn(|i| y[i] ^ mask[i]);
        let out = compress(&x, &y, shift as u64);
        assert!(out.iter().any(|&word| word != 0));
        assert_eq!(out, compress(&y, &x, u64::MAX));
        assert_eq!(out, compress(&masked_x, &masked_y, 0));
        assert_eq!(compress(&x, &x, u64::MAX), [0; 128]);
    }
}
