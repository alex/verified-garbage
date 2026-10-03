//! AES-CMAC (NIST SP 800-38B, RFC 4493) with 128-, 192- and 256-bit AES
//! keys and the full 16-byte MAC.
//!
//! The computation is the verified assembly for the target architecture,
//! on a streaming state this module holds without looking into it:
//! `vg_cmac_aes_init` (contract `VG.Spec.Cmac.aesInitContract`) expands the
//! key into the state, `vg_cmac_aes_absorb` (`VG.Spec.Cmac.aesAbsorbContract`)
//! absorbs data, holding back the message's last bytes, and
//! `vg_cmac_aes_finish` (`VG.Spec.Cmac.aesFinishContract`) writes the MAC.
//! This module keeps the number of rounds and the length of the message so
//! far, which the state does not store, and compares MACs.
//!
//! It follows the implementation of AES (`crate::aes::Backend`): on x86-64,
//! CPUs with AES-NI and SSSE3 run the `_aesni` functions instead, which have
//! the same contracts: the same verified CMAC code, calling
//! `vg_aes_expand_key_aesni` and `vg_aes_ctr32_aesni` rather than
//! `vg_aes_expand_key` and `vg_aes_ctr32`, and CPUs with VAES and AVX2 too
//! the `_vaes` functions, calling `vg_aes_ctr32_vaes` (which, for CMAC's
//! single blocks, runs `vg_aes_ctr32_aesni`'s code). On AArch64, CPUs with the AES
//! extension run the `_aes` functions, calling `vg_aes_expand_key_aes` and
//! `vg_aes_ctr32_aes`. Updates longer than 32 bytes use `_aes_cbc`, whose
//! whole-block chaining keeps the round keys and chaining value in vector
//! registers. On x86, CPUs with AES-NI run the `_aesni` functions; SSSE3
//! is not required. ARMv7 has only the scalar implementation.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use super::{InvalidKeyLength, InvalidMac};
use crate::aes::Backend;
#[cfg(target_arch = "aarch64")]
use crate::arch::cmac_aes::{
    VG_CMAC_AES_ABSORB_AES_CBC_FEATURES, VG_CMAC_AES_ABSORB_AES_FEATURES,
    VG_CMAC_AES_FINISH_AES_FEATURES, VG_CMAC_AES_INIT_AES_FEATURES, vg_cmac_aes_absorb_aes,
    vg_cmac_aes_absorb_aes_cbc, vg_cmac_aes_finish_aes, vg_cmac_aes_init_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::cmac_aes::{
    VG_CMAC_AES_ABSORB_AESNI_FEATURES, VG_CMAC_AES_FINISH_AESNI_FEATURES,
    VG_CMAC_AES_INIT_AESNI_FEATURES, vg_cmac_aes_absorb_aesni, vg_cmac_aes_finish_aesni,
    vg_cmac_aes_init_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::cmac_aes::{
    VG_CMAC_AES_ABSORB_VAES_FEATURES, VG_CMAC_AES_FINISH_VAES_FEATURES,
    VG_CMAC_AES_INIT_VAES_FEATURES, vg_cmac_aes_absorb_vaes, vg_cmac_aes_finish_vaes,
    vg_cmac_aes_init_vaes,
};
use crate::arch::cmac_aes::{vg_cmac_aes_absorb, vg_cmac_aes_finish, vg_cmac_aes_init};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// The streaming state, in 64-bit words.
const STATE: usize = 38;

/// The working space of the streaming functions, in 64-bit words.
const SCRATCH: usize = 288;

/// The best implementation of AES a CPU with the features `f` can run, with
/// the CMAC functions for it.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_CMAC_AES_INIT_AESNI_FEATURES,
        VG_CMAC_AES_ABSORB_AESNI_FEATURES,
        VG_CMAC_AES_FINISH_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the CMAC functions for it.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const VAES: Features = Features::all(&[
        VG_CMAC_AES_INIT_VAES_FEATURES,
        VG_CMAC_AES_ABSORB_VAES_FEATURES,
        VG_CMAC_AES_FINISH_VAES_FEATURES,
    ]);
    const AESNI: Features = Features::all(&[
        VG_CMAC_AES_INIT_AESNI_FEATURES,
        VG_CMAC_AES_ABSORB_AESNI_FEATURES,
        VG_CMAC_AES_FINISH_AESNI_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the CMAC functions for it.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_CMAC_AES_INIT_AES_FEATURES,
        VG_CMAC_AES_ABSORB_AES_FEATURES,
        VG_CMAC_AES_ABSORB_AES_CBC_FEATURES,
        VG_CMAC_AES_FINISH_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The best implementation a CPU with the features `f` can run: there is
/// only one here.
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// An incremental AES-CMAC computation.
///
/// A computation that has absorbed nothing yet can be cloned to MAC several
/// messages with the same key without expanding it again.
///
/// Messages are limited to 2⁶⁴ − 1 bytes.
#[derive(Clone)]
pub struct AesCmac {
    /// The streaming state (`VG.Spec.Cmac.Repr`): the key schedule, the
    /// subkeys, the chaining value and the bytes held back.
    state: [u64; STATE],
    /// The number of rounds of AES for the key.
    rounds: usize,
    /// The length of the message the state represents, in bytes.
    count: u64,
    /// The implementation this CPU runs.
    backend: Backend,
}

impl Drop for AesCmac {
    /// Wipes the streaming state, which holds the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl AesCmac {
    /// The size of the MAC, in bytes.
    pub const MAC_SIZE: usize = 16;

    /// Starts an AES-CMAC computation with `key`, which must be 16, 24 or 32
    /// bytes long (AES-128, AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut c = AesCmac {
            state: [0; STATE],
            rounds: key.len() / 4 + 6,
            count: 0,
            backend: select(detected()),
        };
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let f = match c.backend {
            Backend::Scalar => vg_cmac_aes_init,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => vg_cmac_aes_init_aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => vg_cmac_aes_init_vaes,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => vg_cmac_aes_init_aes,
        };
        // SAFETY: `c.state` is valid for reads and writes of 304 bytes,
        // `key` for reads of `key.len()` bytes, which is 16, 24 or 32, and
        // `scratch` for reads and writes of 2304 bytes. `c.state` and
        // `scratch` are locals and `key` a borrow, so none overlaps another,
        // the return address (on x86-64 and x86), the arguments on the stack
        // (on 32-bit ARM and x86) or the stack below them that the calls
        // use, and none wraps around the end of the address space. The CPU
        // has the features of the implementation selected. `scratch` is
        // uninitialized: it is only working space, and the contract's result
        // does not depend on what it holds.
        unsafe { f(&mut c.state, key.as_ptr(), key.len(), scratch.as_mut_ptr()) };
        Ok(c)
    }

    /// Absorbs `data`.
    ///
    /// # Panics
    ///
    /// If the message reaches 2⁶⁴ bytes.
    pub fn update(&mut self, data: &[u8]) {
        let count = self
            .count
            .checked_add(data.len() as u64)
            .expect("message too long");
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let f = match self.backend {
            Backend::Scalar => vg_cmac_aes_absorb,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => vg_cmac_aes_absorb_aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => vg_cmac_aes_absorb_vaes,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => {
                if data.len() > 32 {
                    vg_cmac_aes_absorb_aes_cbc
                } else {
                    vg_cmac_aes_absorb_aes
                }
            }
        };
        // SAFETY: `self.state` is valid for reads and writes of 304 bytes,
        // `data` for reads of `data.len()` bytes and `scratch`
        // (uninitialized working space, as in `new`) for reads and writes of
        // 2304 bytes. `self.state` is a mutable borrow, `data` a borrow and
        // `scratch` a local, so none overlaps another, the return address
        // (on x86-64 and x86), the arguments on the stack (on 32-bit ARM and
        // x86) or the stack below them that the calls use, and none wraps
        // around the end of the address space. `self.rounds` is 10, 12 or
        // 14, that of the key `new` was given. The state represents a
        // message of `self.count` bytes, which with `data` is shorter than
        // 2⁶⁴ bytes, as the contract's postcondition requires. The CPU has
        // the features of the implementation selected.
        unsafe {
            f(
                &mut self.state,
                self.rounds,
                self.count,
                data.as_ptr(),
                data.len(),
                scratch.as_mut_ptr(),
            )
        };
        self.count = count;
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(mut self) -> [u8; 16] {
        let mut mac = [0; 16];
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let f = match self.backend {
            Backend::Scalar => vg_cmac_aes_finish,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => vg_cmac_aes_finish_aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => vg_cmac_aes_finish_vaes,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => vg_cmac_aes_finish_aes,
        };
        // SAFETY: `self.state` is valid for reads and writes of 304 bytes,
        // `mac` for writes of 16 and `scratch` (uninitialized working space,
        // as in `new`) for reads and writes of 2304. `self.state` is owned
        // and `mac` and `scratch` are locals, so none overlaps another, the
        // return address (on x86-64 and x86), the arguments on the stack (on
        // 32-bit ARM and x86) or the stack below them that the calls use,
        // and none wraps around the end of the address space. `self.rounds`
        // is 10, 12 or 14, that of the key `new` was given, and the state
        // represents a message of `self.count` bytes, as the contract's
        // postcondition requires. The CPU has the features of the
        // implementation selected.
        unsafe {
            f(
                &mut self.state,
                self.rounds,
                self.count,
                &mut mac,
                scratch.as_mut_ptr(),
            )
        };
        mac
    }

    /// Checks that `mac` is the MAC of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `mac`
    /// differs from it (its length is public). `mac` must be the whole MAC,
    /// of [`MAC_SIZE`](Self::MAC_SIZE) bytes; a truncated one is rejected.
    pub fn verify(self, mac: &[u8]) -> Result<(), InvalidMac> {
        if crate::ct::eq(&self.finalize(), mac) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
    }

    /// The MAC of `data` with `key`, which must be 16, 24 or 32 bytes long.
    pub fn mac(key: &[u8], data: &[u8]) -> Result<[u8; 16], InvalidKeyLength> {
        let mut c = Self::new(key)?;
        c.update(data);
        Ok(c.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCmac, Backend, select};
    use crate::cmac::InvalidKeyLength;
    use crate::cpu::{Features, detected};

    /// Keys of other lengths are rejected.
    #[test]
    fn key_lengths() {
        for len in [0, 15, 17, 23, 25, 31, 33, 64] {
            assert_eq!(AesCmac::new(&[0; 64][..len]).err(), Some(InvalidKeyLength));
            assert_eq!(
                AesCmac::mac(&[0; 64][..len], b"").err(),
                Some(InvalidKeyLength)
            );
        }
    }

    /// Absorbing a message in two pieces, split anywhere, gives the MAC of
    /// the whole, also from a clone of a computation that absorbed nothing.
    #[test]
    fn splits() {
        let key = [0x2b; 16];
        let msg: [u8; 50] = core::array::from_fn(|i| i as u8);
        let fresh = AesCmac::new(&key).unwrap();
        for len in 0..=msg.len() {
            let mac = AesCmac::mac(&key, &msg[..len]).unwrap();
            for split in 0..=len {
                let mut c = fresh.clone();
                c.update(&msg[..split]);
                c.update(&msg[split..len]);
                assert_eq!(c.finalize(), mac, "{split} of {len}");
            }
        }
    }

    /// Absorbing a message a byte at a time gives the MAC of the whole.
    #[test]
    fn bytes() {
        let key = [0x2b; 32];
        let msg: [u8; 70] = core::array::from_fn(|i| (3 * i) as u8);
        let mut c = AesCmac::new(&key).unwrap();
        for b in msg {
            c.update(&[b]);
        }
        assert_eq!(c.finalize(), AesCmac::mac(&key, &msg).unwrap());
    }

    /// The bulk AES loop agrees with the baseline for every key width,
    /// around block boundaries, and when short updates surround a bulk one.
    #[test]
    fn bulk() {
        let key: [u8; 32] = core::array::from_fn(|i| (11 * i + 3) as u8);
        let msg: [u8; 4097] = core::array::from_fn(|i| (i.wrapping_mul(7) ^ (i >> 8)) as u8);
        for key_len in [16, 24, 32] {
            let fresh = AesCmac::new(&key[..key_len]).unwrap();
            let mut scalar = fresh.clone();
            scalar.backend = Backend::Scalar;
            for len in [
                0, 1, 15, 16, 17, 31, 32, 33, 47, 48, 49, 255, 256, 257, 4096, 4097,
            ] {
                let mut reference = scalar.clone();
                reference.update(&msg[..len]);
                let expected = reference.finalize();
                assert_eq!(
                    AesCmac::mac(&key[..key_len], &msg[..len]).unwrap(),
                    expected
                );
                for chunk in [1, 16, 31, 32, 33, 63, 257] {
                    let mut c = fresh.clone();
                    for part in msg[..len].chunks(chunk) {
                        c.update(part);
                        c.update(&[]);
                    }
                    assert_eq!(c.finalize(), expected, "{key_len}/{len}/{chunk}");
                }
            }
        }
    }

    /// A message of 2⁶⁴ bytes or more is refused.
    #[test]
    #[should_panic(expected = "message too long")]
    fn too_long() {
        let mut c = AesCmac::new(&[0; 16]).unwrap();
        c.count = u64::MAX;
        c.update(b"x");
    }

    /// The implementation chosen for each set of features: AES's, with the
    /// CMAC functions for it.
    #[test]
    fn backend() {
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(select(Features::of(&["aes", "ssse3"])), Backend::AesNi);
            assert_eq!(select(Features::of(&["aes"])), Backend::Scalar);
            assert_eq!(
                select(Features::of(&["aes", "avx", "avx2", "ssse3", "vaes"])),
                Backend::Vaes
            );
        }
        #[cfg(target_arch = "x86")]
        {
            assert_eq!(select(Features::of(&["aes"])), Backend::AesNi);
            assert_eq!(select(Features::of(&["ssse3"])), Backend::Scalar);
        }
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features::of(&["aes"])), Backend::Aes);
        assert_eq!(select(Features(0)), Backend::Scalar);
        let best = AesCmac::new(&[0; 16]).unwrap().backend;
        assert_eq!(best, select(detected()));
    }
}
