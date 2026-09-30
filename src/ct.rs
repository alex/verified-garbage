//! Constant-time comparison, for the checks of MACs and tags that the Rust
//! code around the verified primitives does.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

/// Whether `a` and `b` are equal. Their lengths are public (slices of
/// different lengths are unequal); their contents are compared in a time
/// that does not depend on where, or whether, they differ: every byte's
/// difference is ORed together, and `black_box` keeps the compiler from
/// stopping at the first one.
pub(crate) fn eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let diff = a.iter().zip(b).fold(0u8, |acc, (x, y)| acc | (x ^ y));
    core::hint::black_box(diff) == 0
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
    }
}
