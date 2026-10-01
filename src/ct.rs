//! Constant-time comparison, for the checks of MACs and tags that the Rust
//! code around the verified primitives does.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::ct::vg_ct_eq;

/// Whether `a` and `b` are equal. The verified comparison leaks only their
/// pointers and lengths; it does not branch on their contents.
pub(crate) fn eq(a: &[u8], b: &[u8]) -> bool {
    // SAFETY: both slices are readable for their lengths and cannot wrap.
    // The buffers may overlap. Live slices lie outside the callee’s stack frame.
    unsafe { vg_ct_eq(a.as_ptr(), a.len(), b.as_ptr(), b.len()) != 0 }
}

#[cfg(test)]
mod tests {
    use super::eq;

    #[test]
    fn compares() {
        assert!(eq(&[], &[]));
        assert!(eq(&[1, 2, 3], &[1, 2, 3]));
        assert!(!eq(&[1, 2, 3], &[1, 2, 4]));
        assert!(!eq(&[0, 2, 3], &[1, 2, 3]));
        assert!(!eq(&[1, 2, 3], &[1, 2]));
        assert!(!eq(&[], &[0]));
        assert!(!eq(&[0], &[]));
    }

    #[test]
    fn overlaps_and_each_difference() {
        let bytes = [0xa5; 257];
        for len in [0, 1, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 255, 256] {
            assert!(eq(&bytes[..len], &bytes[..len]));
            assert!(eq(&bytes[..len], &bytes[1..=len]));
            let mut changed = bytes;
            for i in 0..len {
                for bit in 0..8 {
                    changed[i] ^= 1 << bit;
                    assert!(!eq(&bytes[..len], &changed[..len]));
                    changed[i] ^= 1 << bit;
                }
            }
        }
    }
}
