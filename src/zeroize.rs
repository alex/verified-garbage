//! Wiping secrets from memory the library owns.
//!
//! What is wiped:
//!
//! * ML-KEM, ML-DSA, Ed25519, X25519 and X448 wipe their private keys when
//!   they are dropped, and the intermediate values and working space of
//!   each operation (FIPS 203 §3.3, FIPS 204 §3.6.3).
//! * Every other object holding key material (the ciphers, AEADs and MACs,
//!   and the hash functions, whose state represents the key under HMAC,
//!   PBKDF2 or keyed BLAKE2) wipes it when it is dropped.
//!
//! What is not: the working space (`scratch`) of the symmetric algorithms'
//! calls, and the copies of states the Rust code makes on the stack when
//! it moves or copies them (e.g. the context of each ChaCha20-Poly1305
//! call, which holds the key, or the blocks of PBKDF2 and scrypt), which
//! the next calls overwrite; and anything once it has been returned to the
//! caller (e.g. a MAC, a derived key or a shared secret), whose wiping is
//! the caller's.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

mod sealed {
    pub trait Sealed {}
}

/// An integer type: the value whose bytes are all zero is 0.
pub(crate) trait Int: Copy + sealed::Sealed {}

macro_rules! int {
    ($($t:ty),*) => {
        $(
            impl sealed::Sealed for $t {}
            impl Int for $t {}
        )*
    };
}
int!(u8, u16, u32, u64, i16, i32, i64);

/// Overwrites `x` with zeros using the verified assembly primitive. Its
/// opaque call prevents the compiler from removing the stores.
pub(crate) fn zeroize<T: Int>(x: &mut [T]) {
    // SAFETY: `x` is writable for its entire byte length, cannot wrap, and
    // lies outside the callee’s stack frame. All-zero bytes are valid for T.
    unsafe {
        crate::arch::zeroize::vg_zeroize(x.as_mut_ptr().cast::<u8>(), core::mem::size_of_val(x));
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

#[cfg(test)]
mod tests {
    use super::zeroize;

    #[test]
    fn zeroizes() {
        // Bytes before, between and after aligned words, at every offset.
        for start in 0..8 {
            for end in start..=25 {
                let mut words = [u64::MAX; 4];
                // SAFETY: `words` is 32 bytes, and any bytes are a valid `u8`.
                let bytes = unsafe { &mut *words.as_mut_ptr().cast::<[u8; 32]>() };
                zeroize(&mut bytes[start..end]);
                for (i, b) in bytes.iter().enumerate() {
                    assert_eq!(*b == 0, (start..end).contains(&i));
                }
            }
        }
        let mut y = [u64::MAX; 3];
        zeroize(&mut y);
        assert_eq!(y, [0; 3]);
        let mut z = [-1i16; 5];
        zeroize(&mut z);
        assert_eq!(z, [0; 5]);
    }
}
