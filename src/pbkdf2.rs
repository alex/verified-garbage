//! PBKDF2 (RFC 8018 §5.2) with HMAC as the pseudorandom function, for any
//! hash function with a verified HMAC ([`HmacHash`]).
//!
//! Every HMAC computation is the verified one ([`Hmac`]); this module only
//! chains them and XORs their outputs, as RFC 8018 §5.2 describes.

use core::num::NonZeroU32;

use crate::hmac::{Hmac, HmacHash};

/// Fills `out` with the key derived from `password` and `salt` with
/// `iterations` iterations of PBKDF2 with HMAC-`H`.
///
/// # Panics
///
/// If `out` is longer than (2³² − 1) · `H::OUTPUT_SIZE` bytes ("derived key
/// too long" in RFC 8018).
pub fn pbkdf2_hmac<H: HmacHash>(
    password: &[u8],
    salt: &[u8],
    iterations: NonZeroU32,
    out: &mut [u8],
) {
    let prf = Hmac::<H>::new(password);
    for (i, block) in out.chunks_mut(H::OUTPUT_SIZE).enumerate() {
        let index = u32::try_from(i + 1).expect("PBKDF2 derived key too long");
        // U₁ = PRF(P, S ‖ INT(i)), Uⱼ = PRF(P, Uⱼ₋₁), T = U₁ ⊕ … ⊕ U_c.
        let mut mac = prf.clone();
        mac.update(salt);
        mac.update(&index.to_be_bytes());
        let mut u = mac.finalize();
        let mut t = u.clone();
        for _ in 1..iterations.get() {
            let mut mac = prf.clone();
            mac.update(u.as_ref());
            u = mac.finalize();
            for (t, u) in t.as_mut().iter_mut().zip(u.as_ref()) {
                *t ^= u;
            }
        }
        block.copy_from_slice(&t.as_ref()[..block.len()]);
    }
}
