//! HMAC (RFC 2104, FIPS 198-1), for any [`HashFunction`].

use crate::hash::HashFunction;

/// Absorbs the key (at most one block, zero-padded to a block) XORed with
/// `pad` into `h`.
fn absorb_padded_key<H: HashFunction>(h: &mut H, key: &[u8], pad: u8) {
    let mut chunk = [0u8; 16];
    for start in (0..H::BLOCK_SIZE).step_by(chunk.len()) {
        let n = (H::BLOCK_SIZE - start).min(chunk.len());
        for (i, c) in chunk[..n].iter_mut().enumerate() {
            *c = key.get(start + i).copied().unwrap_or(0) ^ pad;
        }
        h.update(&chunk[..n]);
    }
}

/// An incremental HMAC computation with the hash function `H`.
#[derive(Clone)]
pub struct Hmac<H: HashFunction> {
    /// `H` after absorbing `K₀ ⊕ ipad`.
    inner: H,
    /// `H` after absorbing `K₀ ⊕ opad`.
    outer: H,
}

impl<H: HashFunction> Hmac<H> {
    /// Starts an HMAC computation with `key`, of any length (a key longer
    /// than the block size is hashed first).
    pub fn new(key: &[u8]) -> Self {
        let hashed;
        let key = if key.len() > H::BLOCK_SIZE {
            hashed = H::digest(key);
            hashed.as_ref()
        } else {
            key
        };
        let mut inner = H::new();
        absorb_padded_key(&mut inner, key, 0x36);
        let mut outer = H::new();
        absorb_padded_key(&mut outer, key, 0x5c);
        Hmac { inner, outer }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        self.inner.update(data);
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(self) -> H::Output {
        let mut outer = self.outer;
        outer.update(self.inner.finalize().as_ref());
        outer.finalize()
    }

    /// The MAC of `data` with `key`.
    pub fn mac(key: &[u8], data: &[u8]) -> H::Output {
        let mut h = Self::new(key);
        h.update(data);
        h.finalize()
    }
}
