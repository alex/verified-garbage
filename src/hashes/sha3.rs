//! SHA3-224, SHA3-256, SHA3-384 and SHA3-512, and the extendable-output
//! functions SHAKE128 and SHAKE256 (FIPS 202).
//!
//! `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` for the target
//! architecture (contracts `VG.Spec.Sha3.absorbContract`, `padContract` and
//! `squeezeContract`) maintain a Keccak state that represents the message
//! absorbed so far (`VG.Spec.Sha3.Repr`: the state after its whole blocks,
//! with its remaining bytes XORed in), pad it and squeeze the output. The
//! Rust types only keep that state together with the position in the
//! current block, which the contracts take as an argument.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::sha3::{vg_keccak_absorb, vg_keccak_pad, vg_keccak_squeeze};

#[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
use crate::arch::sha3::{
    VG_KECCAK_ABSORB_SHA3_FEATURES, VG_KECCAK_PAD_SHA3_FEATURES, VG_KECCAK_SQUEEZE_SHA3_FEATURES,
    vg_keccak_absorb_sha3, vg_keccak_pad_sha3, vg_keccak_squeeze_sha3,
};

/// The selected permutation, shared by every phase of a sponge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    Scalar,
    #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
    Sha3,
}

impl Backend {
    pub(crate) fn detected() -> Self {
        // The draft hardware implementation has no measured bulk speedup yet.
        // Keep production/default selection scalar; the existing test feature
        // permits an explicit, CPU-checked SHA-3 selection for validation.
        #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
        {
            static BACKEND: std::sync::OnceLock<Backend> = std::sync::OnceLock::new();
            *BACKEND.get_or_init(|| {
                let features = crate::cpu::detected();
                let requested = std::env::var("VG_CPU_FEATURES")
                    .unwrap_or_default()
                    .split(',')
                    .any(|name| name == "sha3");
                if requested
                    && features.contains(crate::cpu::Features::all(&[
                        VG_KECCAK_ABSORB_SHA3_FEATURES,
                        VG_KECCAK_PAD_SHA3_FEATURES,
                        VG_KECCAK_SQUEEZE_SHA3_FEATURES,
                    ]))
                {
                    return Self::Sha3;
                }
                Self::Scalar
            })
        }
        #[cfg(not(all(target_arch = "aarch64", feature = "cpu-features-env")))]
        Self::Scalar
    }
}

/// The domain-separation suffix of SHA-3 and the first bit of the padding
/// (FIPS 202 §6.1 and Appendix B.2).
const SHA3_SUFFIX: u32 = 0x06;
/// The domain-separation suffix of SHAKE and the first bit of the padding
/// (FIPS 202 §6.2 and Appendix B.2).
const SHAKE_SUFFIX: u32 = 0x1f;

/// A Keccak sponge with a rate of `RATE` bytes, absorbing a message.
///
/// `RATE` is always one of the rates of FIPS 202 (72, 104, 136, 144 or 168
/// bytes), and `pos` is the message length modulo `RATE`.
#[derive(Clone)]
struct Sponge<const RATE: usize> {
    /// The state, representing the message so far for `RATE`.
    state: [u64; 25],
    /// The length of the message so far, modulo `RATE`.
    pos: usize,
    backend: Option<Backend>,
}

impl<const RATE: usize> Sponge<RATE> {
    /// The sponge of the empty message: the all-zero state.
    const fn new() -> Self {
        Sponge {
            state: [0; 25],
            pos: 0,
            backend: None,
        }
    }

    /// Select lazily so the public constructors remain `const`.
    fn backend(&mut self) -> Backend {
        *self.backend.get_or_insert_with(Backend::detected)
    }

    /// Absorbs `data`.
    fn absorb(&mut self, data: &[u8]) {
        let backend = self.backend();
        let mut scratch = [0u64; 80];
        // SAFETY: `RATE` is one of the rates of FIPS 202 and `self.pos` is
        // less than it, and is the length modulo `RATE` of the message that
        // `self.state` represents. `self.state` is valid for reads and
        // writes of 200 bytes, `data` for reads of `data.len()` bytes and
        // `scratch` for reads and writes of 640 bytes; they are distinct
        // objects, so they do not overlap each other or the stack below the
        // stack pointer. The result is the new length modulo `RATE`. Backend
        // selection checks every CPU feature required by the hardware variant.
        self.pos = unsafe {
            match backend {
                Backend::Scalar => vg_keccak_absorb(
                    &mut self.state,
                    RATE,
                    self.pos,
                    data.as_ptr(),
                    data.len(),
                    &mut scratch,
                ),
                #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
                Backend::Sha3 => vg_keccak_absorb_sha3(
                    &mut self.state,
                    RATE,
                    self.pos,
                    data.as_ptr(),
                    data.len(),
                    &mut scratch,
                ),
            }
        };
    }

    /// Pads the message with the domain-separation suffix `suffix`, ready
    /// to squeeze its output.
    fn pad(mut self, suffix: u32) -> Squeezer<RATE> {
        let backend = self.backend();
        let mut scratch = [0u64; 80];
        // SAFETY: as in `absorb`: `RATE` is one of the rates of FIPS 202 and
        // `self.pos` is less than it, and is the length modulo `RATE` of the
        // message `self.state` represents; `self.state` and `scratch` are
        // distinct objects valid for reads and writes of their sizes. Backend
        // selection checked every CPU feature required by the chosen variant.
        unsafe {
            match backend {
                Backend::Scalar => {
                    vg_keccak_pad(&mut self.state, RATE, self.pos, suffix, &mut scratch)
                }
                #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
                Backend::Sha3 => {
                    vg_keccak_pad_sha3(&mut self.state, RATE, self.pos, suffix, &mut scratch)
                }
            }
        };
        Squeezer {
            state: self.state,
            pos: 0,
            backend,
        }
    }
}

impl<const RATE: usize> Drop for Sponge<RATE> {
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.state);
    }
}

/// A Keccak sponge with a rate of `RATE` bytes, squeezing output.
///
/// `RATE` is always one of the rates of FIPS 202, `pos ≤ RATE`, and the
/// output from `state` from byte `pos` on is the rest of the output.
#[derive(Clone)]
struct Squeezer<const RATE: usize> {
    /// The state.
    state: [u64; 25],
    /// The position of the next byte of output in the output of `state`.
    pos: usize,
    backend: Backend,
}

impl<const RATE: usize> Drop for Squeezer<RATE> {
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.state);
    }
}

impl<const RATE: usize> Squeezer<RATE> {
    /// Writes the next `out.len()` bytes of output to `out`.
    fn squeeze(&mut self, out: &mut [u8]) {
        let mut scratch = [0u64; 80];
        // SAFETY: `RATE` is one of the rates of FIPS 202 and `self.pos` is at
        // most `RATE`. `self.state` is valid for reads and writes of 200
        // bytes, `out` for writes of `out.len()` bytes and `scratch` for
        // reads and writes of 640 bytes; they are distinct objects, so they
        // do not overlap each other or the stack below the stack pointer.
        // The state left and the result continue the output. The backend was
        // selected only after checking every required CPU feature.
        self.pos = unsafe {
            match self.backend {
                Backend::Scalar => vg_keccak_squeeze(
                    &mut self.state,
                    RATE,
                    self.pos,
                    out.as_mut_ptr(),
                    out.len(),
                    &mut scratch,
                ),
                #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
                Backend::Sha3 => vg_keccak_squeeze_sha3(
                    &mut self.state,
                    RATE,
                    self.pos,
                    out.as_mut_ptr(),
                    out.len(),
                    &mut scratch,
                ),
            }
        };
    }
}

/// Defines a SHA-3 hash function with a rate of `$rate` bytes and
/// `$output`-byte digests.
macro_rules! sha3 {
    ($(#[$doc:meta])* $name:ident { rate: $rate:literal, output: $output:literal $(,)? }) => {
        $(#[$doc])*
        #[derive(Clone)]
        pub struct $name(Sponge<$rate>);

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $name {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = $output;
            /// The rate of the sponge, in bytes (the block size of HMAC).
            pub const BLOCK_SIZE: usize = $rate;

            /// Starts a new computation.
            pub const fn new() -> Self {
                $name(Sponge::new())
            }

            /// Absorbs `data`.
            pub fn update(&mut self, data: &[u8]) {
                self.0.absorb(data);
            }

            /// Pads the message and returns its digest.
            pub fn finalize(self) -> [u8; $output] {
                let mut digest = [0; $output];
                self.0.pad(SHA3_SUFFIX).squeeze(&mut digest);
                digest
            }

            /// The digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; $output] {
                let mut h = Self::new();
                h.update(data);
                h.finalize()
            }
        }

        impl super::HashFunction for $name {
            const OUTPUT_SIZE: usize = $name::OUTPUT_SIZE;
            const BLOCK_SIZE: usize = $name::BLOCK_SIZE;
            type Output = [u8; $output];

            fn new() -> Self {
                $name::new()
            }

            fn update(&mut self, data: &[u8]) {
                $name::update(self, data)
            }

            fn finalize(self) -> [u8; $output] {
                $name::finalize(self)
            }
        }
    };
}

/// Defines a SHAKE extendable-output function with a rate of `$rate` bytes,
/// and the reader of its output.
macro_rules! shake {
    ($(#[$doc:meta])* $name:ident, $(#[$rdoc:meta])* $reader:ident { rate: $rate:literal $(,)? }) => {
        $(#[$doc])*
        #[derive(Clone)]
        pub struct $name(Sponge<$rate>);

        $(#[$rdoc])*
        #[derive(Clone)]
        pub struct $reader(Squeezer<$rate>);

        impl $reader {
            /// Writes the next `out.len()` bytes of output to `out`.
            pub fn squeeze(&mut self, out: &mut [u8]) {
                self.0.squeeze(out);
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $name {
            /// The rate of the sponge, in bytes.
            pub const BLOCK_SIZE: usize = $rate;

            /// Starts a new computation.
            pub const fn new() -> Self {
                $name(Sponge::new())
            }

            /// Absorbs `data`.
            pub fn update(&mut self, data: &[u8]) {
                self.0.absorb(data);
            }

            /// Pads the message and returns a reader of its output, which
            /// can be squeezed in pieces.
            pub fn finalize_xof(self) -> $reader {
                $reader(self.0.pad(SHAKE_SUFFIX))
            }

            /// Pads the message and fills `out` with the first `out.len()`
            /// bytes of output.
            pub fn finalize(self, out: &mut [u8]) {
                self.finalize_xof().squeeze(out);
            }

            /// Fills `out` with the first `out.len()` bytes of output for
            /// `data`.
            pub fn digest(data: &[u8], out: &mut [u8]) {
                let mut h = Self::new();
                h.update(data);
                h.finalize(out);
            }
        }
    };
}

sha3!(
    /// An incremental SHA3-224 computation.
    Sha3_224 { rate: 144, output: 28 }
);
sha3!(
    /// An incremental SHA3-256 computation.
    Sha3_256 { rate: 136, output: 32 }
);
sha3!(
    /// An incremental SHA3-384 computation.
    Sha3_384 { rate: 104, output: 48 }
);
sha3!(
    /// An incremental SHA3-512 computation.
    Sha3_512 { rate: 72, output: 64 }
);
shake!(
    /// An incremental SHAKE128 computation.
    Shake128,
    /// The output of SHAKE128, squeezed in pieces.
    Shake128Reader { rate: 168 }
);
shake!(
    /// An incremental SHAKE256 computation.
    Shake256,
    /// The output of SHAKE256, squeezed in pieces.
    Shake256Reader { rate: 136 }
);

#[cfg(test)]
mod tests {
    use super::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256};
    use crate::hashes::HashFunction;

    /// Every way of splitting a message into two updates, or into single
    /// bytes after the split, gives the same digest as one update, for
    /// every length up to past two blocks, through `HashFunction`.
    fn incremental<H: HashFunction>() {
        let msg: [u8; 300] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in
            (0..msg.len())
                .step_by(7)
                .chain([H::BLOCK_SIZE - 1, H::BLOCK_SIZE, 2 * H::BLOCK_SIZE])
        {
            let expected = H::digest(&msg[..len]);
            for split in (0..=len).step_by(5) {
                let mut h = H::new();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize().as_ref(), expected.as_ref());
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize().as_ref(), expected.as_ref());
            }
        }
    }

    #[test]
    fn sha3_incremental() {
        incremental::<Sha3_224>();
        incremental::<Sha3_256>();
        incremental::<Sha3_384>();
        incremental::<Sha3_512>();
    }

    #[test]
    fn sha3_default() {
        assert_eq!(Sha3_224::default().finalize(), Sha3_224::digest(b""));
        assert_eq!(Sha3_256::default().finalize(), Sha3_256::digest(b""));
        assert_eq!(Sha3_384::default().finalize(), Sha3_384::digest(b""));
        assert_eq!(Sha3_512::default().finalize(), Sha3_512::digest(b""));
    }

    /// Splitting the message, and the output length: a prefix of a longer
    /// output is the shorter output.
    #[test]
    fn shake_incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        let mut long = [0u8; 500];
        Shake128::digest(&msg, &mut long);
        for split in (0..=msg.len()).step_by(13) {
            let mut h = Shake128::default();
            h.update(&msg[..split]);
            h.update(&msg[split..]);
            let mut out = [0u8; 337];
            h.finalize(&mut out);
            assert_eq!(out[..], long[..337]);
        }
        let mut long = [0u8; 500];
        Shake256::digest(&msg, &mut long);
        for split in (0..=msg.len()).step_by(13) {
            let mut h = Shake256::default();
            h.update(&msg[..split]);
            h.update(&msg[split..]);
            let mut out = [0u8; 273];
            h.finalize(&mut out);
            assert_eq!(out[..], long[..273]);
        }
    }

    /// Output squeezed in pieces of every size from 0 to 300 bytes is the
    /// output squeezed at once.
    #[test]
    fn shake_reader() {
        let mut long = [0u8; 2000];
        Shake128::digest(b"abc", &mut long);
        for piece in 0..300 {
            let mut r = Shake128::default().clone();
            r.update(b"abc");
            let mut r = r.finalize_xof();
            let mut out = [0u8; 2000];
            for chunk in out.chunks_mut(piece.max(1)) {
                r.clone().squeeze(&mut []);
                r.squeeze(chunk);
            }
            assert_eq!(out, long);
        }
        let mut long = [0u8; 2000];
        Shake256::digest(b"abc", &mut long);
        for piece in 1..300 {
            let mut h = Shake256::new();
            h.update(b"abc");
            let mut r = h.finalize_xof();
            let mut out = [0u8; 2000];
            for chunk in out.chunks_mut(piece) {
                r.squeeze(chunk);
            }
            assert_eq!(out, long);
        }
    }
}
