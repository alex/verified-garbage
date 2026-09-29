//! ChaCha20-Poly1305 (RFC 8439 §2.8), with a 96-bit nonce.
//!
//! Encryption and decryption are the verified assembly functions
//! `vg_chacha20_poly1305_seal` and `vg_chacha20_poly1305_open` (contracts
//! `VG.Spec.ChaCha20Poly1305.sealContract` and `openContract`), which compose
//! the verified ChaCha20 and Poly1305 functions themselves; this module only
//! lays out their context (the key, the nonce and the tag) and checks the
//! length limit.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::chacha20poly1305::{vg_chacha20_poly1305_open, vg_chacha20_poly1305_seal};

/// The largest plaintext RFC 8439 allows (`P_MAX`, §2.8): 2³² − 1 blocks of
/// 64 bytes, as the block counter starts at 1.
const P_MAX: u64 = (1 << 38) - 64;

/// Whether `len` bytes exceed `P_MAX`.
fn too_long(len: usize) -> bool {
    len as u64 > P_MAX
}

/// The tag did not authenticate the message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidTag;

/// The AEAD with a key.
#[derive(Clone)]
pub struct ChaCha20Poly1305 {
    key: [u8; 32],
}

impl ChaCha20Poly1305 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a nonce, in bytes.
    pub const NONCE_SIZE: usize = 12;
    /// The size of a tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// The AEAD with the key `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        ChaCha20Poly1305 { key: *key }
    }

    /// The context of the assembly functions: the key, the nonce and the tag
    /// (`VG.Spec.ChaCha20Poly1305.sealContract`), then working space.
    fn ctx(&self, nonce: &[u8; 12], tag: &[u8; 16]) -> [u64; 128] {
        let mut ctx = [0u64; 128];
        let words = |b: &[u8]| -> [u64; 2] {
            core::array::from_fn(|i| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap()))
        };
        ctx[..2].copy_from_slice(&words(&self.key[..16]));
        ctx[2..4].copy_from_slice(&words(&self.key[16..]));
        ctx[4] = u64::from_le_bytes(nonce[..8].try_into().unwrap());
        ctx[5] = u64::from(u32::from_le_bytes(nonce[8..].try_into().unwrap()));
        ctx[6..8].copy_from_slice(&words(tag));
        ctx
    }

    /// Encrypts `data` in place, with the nonce `nonce` and the additional
    /// data `aad`, and returns the tag.
    ///
    /// # Panics
    ///
    /// If `data` is longer than RFC 8439's `P_MAX` (2³⁸ − 64 bytes).
    pub fn encrypt_in_place(&self, nonce: &[u8; 12], aad: &[u8], data: &mut [u8]) -> [u8; 16] {
        assert!(!too_long(data.len()), "message too long");
        let mut ctx = self.ctx(nonce, &[0; 16]);
        // SAFETY: `ctx` is valid for reads and writes of 1024 bytes, `aad`
        // for reads of `aad.len()` bytes and `data` for reads and writes of
        // `data.len()` bytes; they are distinct objects (`aad` is a shared
        // borrow and `data` a unique one), so they do not overlap each other
        // or anything on the stack (the return address, any arguments, and
        // the stack below the stack pointer the calls use), and do not wrap
        // around the end of the address space.
        unsafe {
            vg_chacha20_poly1305_seal(
                &mut ctx,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
            )
        };
        let mut tag = [0; 16];
        tag[..8].copy_from_slice(&ctx[6].to_le_bytes());
        tag[8..].copy_from_slice(&ctx[7].to_le_bytes());
        tag
    }

    /// Decrypts `data` in place, with the nonce `nonce` and the additional
    /// data `aad`, if `tag` authenticates it; otherwise returns
    /// [`InvalidTag`] and zeroes `data`.
    ///
    /// # Panics
    ///
    /// If `data` is longer than RFC 8439's `P_MAX` (2³⁸ − 64 bytes).
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), InvalidTag> {
        assert!(!too_long(data.len()), "message too long");
        let mut ctx = self.ctx(nonce, tag);
        // SAFETY: as in `encrypt_in_place`.
        let ok = unsafe {
            vg_chacha20_poly1305_open(
                &mut ctx,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            data.fill(0);
            Err(InvalidTag)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ChaCha20Poly1305, InvalidTag, P_MAX, too_long};

    /// Decryption undoes encryption, and rejects any change to the data, the
    /// additional data, the nonce or the tag, zeroing the data.
    #[test]
    fn round_trip() {
        let aead = ChaCha20Poly1305::new(&core::array::from_fn(|i| i as u8));
        let nonce = [7; 12];
        let aad = [1, 2, 3];
        for len in [0, 1, 15, 16, 17, 63, 64, 65, 200] {
            let msg: [u8; 200] = core::array::from_fn(|i| (i * 13) as u8);
            let msg = &msg[..len];
            let mut buf = [0u8; 200];
            let data = &mut buf[..len];
            data.copy_from_slice(msg);
            let tag = aead.encrypt_in_place(&nonce, &aad, data);
            let mut copy = [0u8; 200];
            let copy = &mut copy[..len];
            copy.copy_from_slice(data);
            assert_eq!(aead.decrypt_in_place(&nonce, &aad, copy, &tag), Ok(()));
            assert_eq!(copy, msg);
            let mut bad_tag = tag;
            bad_tag[0] ^= 1;
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&nonce, &aad, copy, &bad_tag),
                Err(InvalidTag)
            );
            assert!(copy.iter().all(|&b| b == 0));
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&[8; 12], &aad, copy, &tag),
                Err(InvalidTag)
            );
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&nonce, &aad[..2], copy, &tag),
                Err(InvalidTag)
            );
            if len > 0 {
                copy.copy_from_slice(data);
                copy[len - 1] ^= 0x80;
                assert_eq!(
                    aead.decrypt_in_place(&nonce, &aad, copy, &tag),
                    Err(InvalidTag)
                );
            }
        }
    }

    /// `P_MAX` bytes are allowed and one more are not (a 32-bit length is
    /// always allowed).
    #[test]
    fn length_limit() {
        assert!(!too_long(0));
        assert!(!too_long(usize::try_from(P_MAX).unwrap_or(usize::MAX)));
        if let Ok(len) = usize::try_from(P_MAX + 1) {
            assert!(too_long(len));
        }
    }
}
