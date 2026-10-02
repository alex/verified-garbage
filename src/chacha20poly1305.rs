//! ChaCha20-Poly1305 (RFC 8439 §2.8), with a 96-bit nonce.
//!
//! Encryption and decryption are the verified assembly functions
//! `vg_chacha20_poly1305_seal` and `vg_chacha20_poly1305_open` (contracts
//! `VG.Spec.ChaCha20Poly1305.sealContract` and `openContract`), which compose
//! the verified ChaCha20 and Poly1305 functions themselves; this module only
//! lays out their context (the key, the nonce and the tag) and checks the
//! length limit.
//!
//! They are emitted once for each implementation of `vg_chacha20_xor`
//! (`crate::chacha20::Backend`), each calling it and the implementation of
//! `vg_poly1305_blocks` for the same CPUs: on x86-64, CPUs with AVX-512F and
//! AVX2 run `vg_chacha20_poly1305_seal_avx512` and
//! `vg_chacha20_poly1305_open_avx512` (with `vg_chacha20_xor_avx512` and
//! `vg_poly1305_blocks_avx512`), and other CPUs with AVX2
//! `vg_chacha20_poly1305_seal_avx2` and `vg_chacha20_poly1305_open_avx2`.
//! On AArch64, CPUs with AdvSIMD (the baseline) run
//! `vg_chacha20_poly1305_seal_neon` and `vg_chacha20_poly1305_open_neon`,
//! which XOR the keystream into the data with `vg_chacha20_xor_neon`; like
//! every variant, they compute the one-time Poly1305 key with the scalar
//! `vg_chacha20_block`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::chacha20poly1305::{
    VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES, VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES,
    vg_chacha20_poly1305_open_avx2, vg_chacha20_poly1305_open_avx512,
    vg_chacha20_poly1305_seal_avx2, vg_chacha20_poly1305_seal_avx512,
};
use crate::arch::chacha20poly1305::{vg_chacha20_poly1305_open, vg_chacha20_poly1305_seal};
#[cfg(target_arch = "aarch64")]
use crate::arch::chacha20poly1305::{
    vg_chacha20_poly1305_open_neon, vg_chacha20_poly1305_seal_neon,
};
use crate::chacha20::Backend;
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The best implementation a CPU with the features `f` can run (`open`'s
/// instances need the same features as `seal`'s, see the tests).
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    Backend::select_for(
        f,
        VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES,
        VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES,
    )
}

/// The best implementation a CPU with the features `f` can run.
#[cfg(not(target_arch = "x86_64"))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// The largest plaintext RFC 8439 allows (`P_MAX`, §2.8): 2³² − 1 blocks of
/// 64 bytes, as the block counter starts at 1.
const P_MAX: u64 = (1 << 38) - 64;

/// Checks that a text of `len` bytes is at most `P_MAX` long.
fn check_len(len: usize) -> Result<(), Error> {
    if len as u64 > P_MAX {
        return Err(Error::InvalidTextLength);
    }
    Ok(())
}

/// Why a ChaCha20-Poly1305 operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The plaintext or ciphertext is longer than `2^38 − 64` bytes (RFC
    /// 8439's `P_MAX`, §2.8).
    InvalidTextLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

/// The AEAD with a key.
#[derive(Clone)]
pub struct ChaCha20Poly1305 {
    key: [u8; 32],
    /// The implementations of `vg_chacha20_xor` and `vg_poly1305_blocks` the
    /// functions called call.
    backend: Backend,
}

impl Drop for ChaCha20Poly1305 {
    /// Wipes the key.
    fn drop(&mut self) {
        zeroize(&mut self.key);
    }
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
        ChaCha20Poly1305 {
            key: *key,
            backend: select(detected()),
        }
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
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; 16], Error> {
        // Check the length before encrypting anything.
        check_len(data.len())?;
        let mut ctx = self.ctx(nonce, &[0; 16]);
        let seal = match self.backend {
            Backend::Scalar => vg_chacha20_poly1305_seal,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_chacha20_poly1305_seal_neon,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_chacha20_poly1305_seal_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_chacha20_poly1305_seal_avx512,
        };
        // SAFETY: `ctx` is valid for reads and writes of 1024 bytes, `aad`
        // for reads of `aad.len()` bytes and `data` for reads and writes of
        // `data.len()` bytes; they are distinct objects (`aad` is a shared
        // borrow and `data` a unique one), so they do not overlap each other
        // or anything on the stack (the return address, any arguments, and
        // the stack below the stack pointer the calls use), and do not wrap
        // around the end of the address space. The CPU has the features of
        // the implementation selected (see `features` in the tests).
        unsafe {
            seal(
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
        Ok(tag)
    }

    /// Decrypts `data` in place, with the nonce `nonce` and the additional
    /// data `aad`, if `tag` authenticates it; otherwise returns
    /// [`Error::TagMismatch`] and zeroes `data`.
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        check_len(data.len())?;
        let mut ctx = self.ctx(nonce, tag);
        let open = match self.backend {
            Backend::Scalar => vg_chacha20_poly1305_open,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_chacha20_poly1305_open_neon,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_chacha20_poly1305_open_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_chacha20_poly1305_open_avx512,
        };
        // SAFETY: as in `encrypt_in_place`.
        let ok = unsafe {
            open(
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
            // `open`'s contract leaves `data` unspecified when the tag is
            // wrong (it may hold the decryption of the forged ciphertext):
            // this, not the verified code, keeps it from being released.
            data.fill(0);
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, ChaCha20Poly1305, Error, P_MAX, check_len, select};
    #[cfg(target_arch = "x86_64")]
    use crate::cpu::Features;
    use crate::cpu::detected;

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
            let tag = aead.encrypt_in_place(&nonce, &aad, data).unwrap();
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
                Err(Error::TagMismatch)
            );
            assert!(copy.iter().all(|&b| b == 0));
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&[8; 12], &aad, copy, &tag),
                Err(Error::TagMismatch)
            );
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&nonce, &aad[..2], copy, &tag),
                Err(Error::TagMismatch)
            );
            if len > 0 {
                copy.copy_from_slice(data);
                copy[len - 1] ^= 0x80;
                assert_eq!(
                    aead.decrypt_in_place(&nonce, &aad, copy, &tag),
                    Err(Error::TagMismatch)
                );
            }
        }
    }

    /// `P_MAX` bytes are allowed and one more are not (a 32-bit length is
    /// always allowed), which no test can reach with real buffers.
    #[test]
    fn length_limit() {
        assert_eq!(check_len(0), Ok(()));
        let max = usize::try_from(P_MAX).unwrap_or(usize::MAX);
        assert_eq!(check_len(max), Ok(()));
        if let Ok(len) = usize::try_from(P_MAX + 1) {
            assert_eq!(check_len(len), Err(Error::InvalidTextLength));
        }
    }

    /// Every implementation gives the same ciphertext and tag as the scalar
    /// one, and decrypts what any of them encrypted.
    #[test]
    fn implementations_agree() {
        let key = core::array::from_fn(|i| (i * 7) as u8);
        let mut scalar = ChaCha20Poly1305::new(&key);
        scalar.backend = Backend::Scalar;
        let best = ChaCha20Poly1305::new(&key);
        assert_eq!(best.backend, select(detected()));
        let nonce = [9; 12];
        let aad = [4; 20];
        for len in [
            0, 63, 64, 65, 255, 256, 257, 319, 320, 321, 511, 512, 513, 1000, 1023, 1024, 1025,
            2100,
        ] {
            let msg: [u8; 2100] = core::array::from_fn(|i| (i * 31) as u8);
            let mut a = msg;
            let mut b = msg;
            let tag = scalar.encrypt_in_place(&nonce, &aad, &mut a[..len]);
            assert_eq!(best.encrypt_in_place(&nonce, &aad, &mut b[..len]), tag);
            let tag = tag.unwrap();
            assert_eq!(a, b);
            assert_eq!(
                best.decrypt_in_place(&nonce, &aad, &mut a[..len], &tag),
                Ok(())
            );
            assert_eq!(
                scalar.decrypt_in_place(&nonce, &aad, &mut b[..len], &tag),
                Ok(())
            );
            assert_eq!(a, msg);
            assert_eq!(b, msg);
        }
    }

    /// The functions called for each implementation need the features of
    /// both `vg_chacha20_xor`'s and `vg_poly1305_blocks`'s for the same CPUs,
    /// `open`'s the same as `seal`'s, and `select` chooses by them.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn features() {
        use crate::arch::chacha20::{
            VG_CHACHA20_XOR_AVX2_FEATURES, VG_CHACHA20_XOR_AVX512_FEATURES,
        };
        use crate::arch::chacha20poly1305::{
            VG_CHACHA20_POLY1305_OPEN_AVX2_FEATURES, VG_CHACHA20_POLY1305_OPEN_AVX512_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES, VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES,
        };
        use crate::arch::poly1305::{
            VG_POLY1305_BLOCKS_AVX2_FEATURES, VG_POLY1305_BLOCKS_AVX512_FEATURES,
        };
        let avx2 = Features::all(&[
            VG_CHACHA20_XOR_AVX2_FEATURES,
            VG_POLY1305_BLOCKS_AVX2_FEATURES,
        ]);
        let avx512 = Features::all(&[
            VG_CHACHA20_XOR_AVX512_FEATURES,
            VG_POLY1305_BLOCKS_AVX512_FEATURES,
        ]);
        assert_eq!(Features::of(VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES), avx2);
        assert_eq!(Features::of(VG_CHACHA20_POLY1305_OPEN_AVX2_FEATURES), avx2);
        assert_eq!(
            Features::of(VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES),
            avx512
        );
        assert_eq!(
            Features::of(VG_CHACHA20_POLY1305_OPEN_AVX512_FEATURES),
            avx512
        );
        assert_eq!(select(avx2), Backend::Avx2);
        assert_eq!(select(avx512), Backend::Avx512);
        // AVX-512F alone is not enough: the AVX-512 instances' Poly1305
        // calls its AVX2 implementation.
        assert_eq!(
            select(Features::of(VG_CHACHA20_XOR_AVX512_FEATURES)),
            Backend::Scalar
        );
        assert_eq!(select(Features::of(&["avx"])), Backend::Scalar);
    }
}
