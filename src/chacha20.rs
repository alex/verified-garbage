//! ChaCha20 (RFC 8439), with the 16-byte nonce of OpenSSL and
//! pyca/cryptography.
//!
//! The block function is the verified assembly primitive `vg_chacha20_block`
//! (contract `VG.Spec.ChaCha20.blockX86_64`); this module builds the state
//! (RFC 8439 §2.3), XORs the keystream into the data (§2.4) and advances the
//! block counter.
//!
//! The 16-byte nonce is the initial block counter (4 bytes, little-endian)
//! followed by the 12-byte RFC 8439 nonce, i.e. state words 12–15. As in
//! OpenSSL (and the original ChaCha), words 12 and 13 together are a 64-bit
//! block counter: when word 12 wraps around, word 13 is incremented. This
//! agrees with RFC 8439, whose counter is only word 12, for the first
//! 2³² − (initial counter) blocks.

/// The constants `"expand 32-byte k"` (RFC 8439 §2.3).
const CONSTANTS: [u32; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

/// The 64 bytes of keystream for `state`.
fn block(state: &[u32; 16]) -> [u8; 64] {
    let mut buf = [0u32; 64];
    // SAFETY: `state` is valid for reads of 64 bytes and `buf` for reads and
    // writes of 256 bytes; they are distinct objects, so they do not overlap
    // each other or the return address.
    unsafe { crate::asm::x86_64::chacha20::vg_chacha20_block(state, &mut buf) };
    let mut out = [0u8; 64];
    for (o, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&buf[..16]) {
        *o = word.to_le_bytes();
    }
    out
}

/// The little-endian words of `bytes`.
fn words<const N: usize>(bytes: &[u8]) -> [u32; N] {
    core::array::from_fn(|i| u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()))
}

/// A ChaCha20 keystream, applied incrementally.
pub struct ChaCha20 {
    state: [u32; 16],
    keystream: [u8; 64],
    /// How many bytes of `keystream` have been used.
    used: usize,
}

impl ChaCha20 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a nonce (initial block counter and RFC 8439 nonce), in bytes.
    pub const NONCE_SIZE: usize = 16;

    /// Starts the keystream for `key` and `nonce` (the initial block counter,
    /// little-endian, followed by the 12-byte RFC 8439 nonce).
    pub fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        let mut state = [0u32; 16];
        state[..4].copy_from_slice(&CONSTANTS);
        state[4..12].copy_from_slice(&words::<8>(key));
        let mut c = ChaCha20 {
            state,
            keystream: [0; 64],
            used: 64,
        };
        c.reset_nonce(nonce);
        c
    }

    /// Restarts the keystream, with the same key, for `nonce`.
    pub fn reset_nonce(&mut self, nonce: &[u8; 16]) {
        self.state[12..].copy_from_slice(&words::<4>(nonce));
        self.used = 64;
    }

    /// XORs the next `data.len()` bytes of the keystream into `data`
    /// (encrypting or decrypting it).
    pub fn apply_keystream(&mut self, data: &mut [u8]) {
        for byte in data {
            if self.used == 64 {
                self.keystream = block(&self.state);
                self.used = 0;
                // Advance the 64-bit block counter in words 12 and 13.
                let counter =
                    (u64::from(self.state[13]) << 32 | u64::from(self.state[12])).wrapping_add(1);
                self.state[12] = counter as u32;
                self.state[13] = (counter >> 32) as u32;
            }
            *byte ^= self.keystream[self.used];
            self.used += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ChaCha20;

    fn unhex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, o) in out.iter_mut().enumerate() {
            *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    /// A fixed key, `00:01:…:1f`.
    fn key() -> [u8; 32] {
        core::array::from_fn(|i| i as u8)
    }

    /// A 16-byte nonce from an RFC 8439 block counter and nonce.
    fn nonce(counter: u32, nonce: &[u8; 12]) -> [u8; 16] {
        let mut n = [0u8; 16];
        n[..4].copy_from_slice(&counter.to_le_bytes());
        n[4..].copy_from_slice(nonce);
        n
    }

    /// The first `N` bytes of keystream.
    fn keystream<const N: usize>(key: &[u8; 32], nonce: &[u8; 16]) -> [u8; N] {
        let mut out = [0u8; N];
        ChaCha20::new(key, nonce).apply_keystream(&mut out);
        out
    }

    /// Applying the keystream in two pieces, or a byte at a time, is the
    /// same as applying it at once, for every split around block boundaries.
    #[test]
    fn incremental() {
        let n = nonce(7, &[3; 12]);
        let expected = keystream::<200>(&key(), &n);
        for split in 0..=200 {
            let mut data = [0u8; 200];
            let mut c = ChaCha20::new(&key(), &n);
            c.apply_keystream(&mut data[..split]);
            c.apply_keystream(&mut data[split..]);
            assert_eq!(data, expected);
        }
        let mut data = [0u8; 200];
        let mut c = ChaCha20::new(&key(), &n);
        for byte in data.chunks_mut(1) {
            c.apply_keystream(byte);
        }
        assert_eq!(data, expected);
    }

    /// `reset_nonce` restarts the keystream.
    #[test]
    fn reset_nonce() {
        let (n1, n2) = (nonce(0, &[1; 12]), nonce(5, &[2; 12]));
        let mut c = ChaCha20::new(&key(), &n1);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        c.reset_nonce(&n2);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        assert_eq!(data, keystream::<100>(&key(), &n2));
    }

    /// The block counter carries from word 12 into word 13, and wraps around
    /// (modulo 2⁶⁴) without touching words 14 and 15.
    #[test]
    fn counter_carry() {
        let ks = keystream::<128>(
            &key(),
            &nonce(0xffff_ffff, &unhex("0900000011223344aabbccdd")),
        );
        let next = keystream::<64>(&key(), &nonce(0, &unhex("0a00000011223344aabbccdd")));
        assert_eq!(ks[64..], next);

        let ks = keystream::<128>(
            &key(),
            &nonce(0xffff_ffff, &unhex("ffffffff11223344aabbccdd")),
        );
        let next = keystream::<64>(&key(), &nonce(0, &unhex("0000000011223344aabbccdd")));
        assert_eq!(ks[64..], next);
    }
}
