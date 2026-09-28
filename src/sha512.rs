//! SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4).
//!
//! The whole computation is verified assembly: `vg_sha384_init`,
//! `vg_sha512_init`, `vg_sha512_224_init` or `vg_sha512_256_init`, then
//! `vg_sha512_update` and `vg_sha512_finalize` (contracts
//! `VG.Spec.Sha512.initX86_64`, `updateX86_64` and `finalizeX86_64`) maintain
//! a streaming state that represents the message absorbed so far
//! (`VG.Spec.Sha512.Repr`: the hash value of its whole blocks, from the
//! function's initial hash value, and its remaining bytes), and pad it and
//! output the final hash value. The four functions share that state and
//! differ only in their initial hash value and in how much of the final hash
//! value is their digest. This module only keeps the state together with the
//! message length, which the contracts take as an argument, and takes the
//! digest's bytes from the final hash value.

use crate::asm::x86_64::sha512::{
    vg_sha384_init, vg_sha512_224_init, vg_sha512_256_init, vg_sha512_finalize, vg_sha512_init,
    vg_sha512_update,
};

/// The streaming state shared by the four functions.
#[derive(Clone)]
struct Core {
    /// The streaming state, representing the message so far.
    state: [u8; 192],
    /// The message length so far, in bytes.
    length: u64,
}

impl Core {
    /// Absorbs `data`.
    ///
    /// # Panics
    ///
    /// If the message reaches 2⁶⁴ bytes, which `vg_sha512_finalize` does not
    /// support.
    fn update(&mut self, data: &[u8]) {
        let length = self
            .length
            .checked_add(data.len() as u64)
            .expect("SHA-512 message too long");
        let mut scratch = [0u64; 28];
        // SAFETY: `self.state` is valid for reads and writes of 192 bytes,
        // `data` for reads of `data.len()` bytes and `scratch` for reads and
        // writes of 224 bytes; they are distinct objects, so they do not
        // overlap each other or the return address, and do not wrap around
        // the end of the address space. `self.length` is the length of the
        // message `self.state` represents.
        unsafe {
            vg_sha512_update(
                &mut self.state,
                self.length,
                data.as_ptr(),
                data.len(),
                &mut scratch,
            )
        };
        self.length = length;
    }

    /// Pads the message (FIPS 180-4 §5.1.2) and returns the final hash value
    /// `H⁽ᴺ⁾`, 64 bytes.
    fn finalize(mut self) -> [u8; 64] {
        let mut out = [0; 64];
        let mut scratch = [0u64; 28];
        // SAFETY: `self.state` is valid for reads and writes of 192 bytes,
        // `out` for writes of 64 bytes and `scratch` for reads and writes of
        // 224 bytes; they are distinct objects, so they do not overlap each
        // other or the return address, and do not wrap around the end of the
        // address space. `self.length` is the exact length of the message
        // `self.state` represents (`update` never lets it wrap).
        unsafe { vg_sha512_finalize(&mut self.state, self.length, &mut out, &mut scratch) };
        out
    }
}

/// Defines a public hash function: `$init` starts it, and its digest is the
/// first `$n` bytes of the final hash value.
macro_rules! sha512_variant {
    ($(#[$doc:meta])* $name:ident, $init:ident, $n:literal) => {
        $(#[$doc])*
        ///
        /// Messages are limited to 2⁶⁴ − 1 bytes.
        #[derive(Clone)]
        pub struct $name(Core);

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $name {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = $n;
            /// The size of a message block, in bytes.
            pub const BLOCK_SIZE: usize = 128;

            /// Starts a new computation.
            pub fn new() -> Self {
                let mut state = [0; 192];
                // SAFETY: `state` is valid for writes of 192 bytes, and is a
                // distinct object from the return address; as a Rust object,
                // it does not wrap around the end of the address space.
                unsafe { $init(&mut state) };
                $name(Core { state, length: 0 })
            }

            /// Absorbs `data`.
            ///
            /// # Panics
            ///
            /// If the message reaches 2⁶⁴ bytes.
            pub fn update(&mut self, data: &[u8]) {
                self.0.update(data)
            }

            /// Pads the message (FIPS 180-4 §5.1.2) and returns its digest.
            pub fn finalize(self) -> [u8; $n] {
                let mut digest = [0; $n];
                digest.copy_from_slice(&self.0.finalize()[..$n]);
                digest
            }

            /// The digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; $n] {
                let mut h = Self::new();
                h.update(data);
                h.finalize()
            }
        }

        impl crate::hash::HashFunction for $name {
            const OUTPUT_SIZE: usize = $name::OUTPUT_SIZE;
            const BLOCK_SIZE: usize = $name::BLOCK_SIZE;
            type Output = [u8; $n];

            fn new() -> Self {
                $name::new()
            }

            fn update(&mut self, data: &[u8]) {
                $name::update(self, data)
            }

            fn finalize(self) -> [u8; $n] {
                $name::finalize(self)
            }
        }
    };
}

sha512_variant!(
    /// An incremental SHA-384 computation (FIPS 180-4 §6.5).
    Sha384,
    vg_sha384_init,
    48
);
sha512_variant!(
    /// An incremental SHA-512 computation (FIPS 180-4 §6.4).
    Sha512,
    vg_sha512_init,
    64
);
sha512_variant!(
    /// An incremental SHA-512/224 computation (FIPS 180-4 §6.6).
    Sha512_224,
    vg_sha512_224_init,
    28
);
sha512_variant!(
    /// An incremental SHA-512/256 computation (FIPS 180-4 §6.7).
    Sha512_256,
    vg_sha512_256_init,
    32
);

#[cfg(test)]
mod tests {
    use super::{Sha384, Sha512, Sha512_224, Sha512_256};

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha512::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha512::default();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize(), expected);
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize(), expected);
            }
        }
    }

    #[test]
    fn sizes() {
        assert_eq!(
            [
                Sha384::OUTPUT_SIZE,
                Sha512::OUTPUT_SIZE,
                Sha512_224::OUTPUT_SIZE,
                Sha512_256::OUTPUT_SIZE
            ],
            [48, 64, 28, 32]
        );
        assert_eq!(
            [
                Sha384::BLOCK_SIZE,
                Sha512::BLOCK_SIZE,
                Sha512_224::BLOCK_SIZE,
                Sha512_256::BLOCK_SIZE
            ],
            [128; 4]
        );
    }

    /// The `HashFunction` implementations are the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hash::HashFunction;
        fn check<H: HashFunction + Default>(digest: fn(&[u8]) -> H::Output) {
            let msg = [0x5a; 300];
            let mut h = <H as Default>::default();
            HashFunction::update(&mut h, &msg[..100]);
            HashFunction::update(&mut h, &msg[100..]);
            assert_eq!(h.finalize().as_ref(), digest(&msg).as_ref());
            assert_eq!(
                <H as HashFunction>::digest(&msg).as_ref(),
                digest(&msg).as_ref()
            );
            assert_eq!(digest(&msg).as_ref().len(), H::OUTPUT_SIZE);
            assert_eq!(H::BLOCK_SIZE, 128);
        }
        check::<Sha384>(Sha384::digest);
        check::<Sha512>(Sha512::digest);
        check::<Sha512_224>(Sha512_224::digest);
        check::<Sha512_256>(Sha512_256::digest);
    }
}
