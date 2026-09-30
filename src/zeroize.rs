//! Wiping secrets from memory the library owns.
//!
//! What is wiped:
//!
//! * ML-KEM, ML-DSA, Ed25519, X25519 and X448 wipe their private keys when
//!   they are dropped, and the intermediate values and working space of
//!   each operation (FIPS 203 §3.3, FIPS 204 §3.6.3).
//! * The key objects of the symmetric algorithms wipe their key material
//!   when they are dropped: [`AesGcm`](crate::aes_gcm::AesGcm) its key
//!   schedule and hash subkey, [`AesGcmStream`](crate::aes_gcm::AesGcmStream)
//!   also its keystream, partial block and GHASH state,
//!   [`ChaCha20`](crate::chacha20::ChaCha20) its state and keystream,
//!   [`ChaCha20Poly1305`](crate::chacha20poly1305::ChaCha20Poly1305) its
//!   key, [`Poly1305`](crate::poly1305::Poly1305) its state (which holds its
//!   key), and the
//!   hash functions (whose state, under HMAC, PBKDF2 or keyed BLAKE2,
//!   represents the key) and [`Hmac`](crate::hmac::Hmac) their streaming
//!   states.
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

/// Overwrites `x` with zeros in a way the compiler does not remove.
pub(crate) fn zeroize<T: Copy + Default>(x: &mut [T]) {
    for v in x.iter_mut() {
        // SAFETY: `v` is a valid, aligned, unique reference.
        unsafe { core::ptr::write_volatile(v, T::default()) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

#[cfg(test)]
mod tests {
    use super::zeroize;

    #[test]
    fn zeroizes() {
        let mut x = [1u8, 2, 3];
        zeroize(&mut x);
        assert_eq!(x, [0; 3]);
    }
}
