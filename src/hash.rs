//! Hash functions, as used by the constructions that are generic over them
//! (HMAC, PBKDF2).

/// A hash function with an incremental interface.
pub trait HashFunction: Clone {
    /// The size of a digest, in bytes.
    const OUTPUT_SIZE: usize;
    /// The size of the input blocks, in bytes (the `B` of HMAC).
    const BLOCK_SIZE: usize;
    /// A digest: `OUTPUT_SIZE` bytes.
    type Output: AsRef<[u8]> + AsMut<[u8]> + Clone;

    /// Starts a new computation.
    fn new() -> Self;
    /// Absorbs `data`.
    fn update(&mut self, data: &[u8]);
    /// Returns the digest of everything absorbed.
    fn finalize(self) -> Self::Output;

    /// The digest of `data`.
    fn digest(data: &[u8]) -> Self::Output {
        let mut h = Self::new();
        h.update(data);
        h.finalize()
    }
}
