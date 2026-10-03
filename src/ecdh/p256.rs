//! ECDH over P-256 (`vg_ecdh_p256`), and public keys
//! (`vg_ec_p256_public_key`).

#![cfg(target_arch = "x86_64")]

use super::{Error, P256, PrivateKey};
use crate::arch::ec_p256::vg_ec_p256_public_key;
use crate::arch::ecdh_p256::vg_ecdh_p256;
use crate::zeroize::zeroize;

impl PrivateKey<P256> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        let mut out = [0; 65];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 65 bytes, `self.d`
        // for reads of 32 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p256_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// The shared secret with the peer whose public key is `peer`
    /// (uncompressed, `04 ‖ x ‖ y`): the x-coordinate of `dQ`, 32 bytes,
    /// most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`, or `peer`
    /// is not a valid public key (SP 800-56A §5.6.2.3.3).
    pub fn diffie_hellman(&self, peer: &[u8; 65]) -> Result<[u8; 32], Error> {
        let mut out = [0; 32];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 32 bytes, `self.d`
        // for reads of 32, `peer` for reads of 65 and `scratch` for reads
        // and writes of 8192; `out` and `scratch` are distinct objects from
        // each other and the others, so none overlaps another or the call's
        // stack frame, and, as Rust objects, none wraps around the address
        // space.
        let ok = unsafe { vg_ecdh_p256(&mut out, &self.d, peer, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}
