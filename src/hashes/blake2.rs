//! The Rust types of BLAKE2b and BLAKE2s (RFC 7693), shared by `blake2b` and
//! `blake2s`.
//!
//! `vg_blake2{b,s}_init`, `vg_blake2{b,s}_update` and
//! `vg_blake2{b,s}_finalize` for the target architecture (contracts
//! `VG.Spec.Blake2.initBContract`, … `finalizeSContract`) maintain a
//! streaming state that represents the data absorbed so far
//! (`VG.Spec.Blake2.Repr`: the hash state after all its blocks but the last,
//! followed by that last block, which the final compression needs to know
//! about). The Rust types only keep that state together with the length of
//! the data, which the contracts take as an argument.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

/// Defines a BLAKE2 hash function with blocks of `$block` bytes (sixteen
/// words of `$block / 16` bytes) over verified streaming primitives:
///
/// * `init(state: *mut [u8; STATE], outlen: usize, key: *const u8, keylen: usize)`
///   makes `state` represent the key block (none for an empty key), hashed
///   from the initial state for an `outlen`-byte digest;
/// * `update(state, count: u64, data: *const u8, len: usize, scratch: *mut [u64; SCRATCH])`
///   absorbs `len` bytes into a state representing data of `count` bytes;
/// * `finalize(state, count: u64, out: *mut [u8; MAX], scratch)` writes the
///   final hash value, whose first `outlen` bytes are the digest.
///
/// Every region is a distinct Rust object, so none overlaps another, the
/// return address (on x86-64 and x86), the arguments on the stack (on 32-bit
/// ARM and x86) or the stack below them that the call uses, and none wraps
/// around the end of the address space; the length is kept exactly
/// (`update` panics rather than let it reach 2⁶⁴ bytes).
macro_rules! blake2 {
    (
        $(#[$doc:meta])*
        $name:ident {
            state: $state:literal,
            scratch: $scratch:literal,
            block: $block:literal,
            max: $max:literal,
            init: $init:path,
            backends: $backend:ident {
                $base:ident => ($update:path, $finalize:path)
                $(, $(#[$attr:meta])* $variant:ident if [$($req:path),*] => ($vupdate:path, $vfinalize:path))*
                $(,)?
            } $(,)?
        }
    ) => {
        /// The implementations of the streaming primitives.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(crate) enum $backend {
            /// For the baseline ISA.
            $base,
            $(
                $(#[$attr])*
                /// Needing CPU features.
                $variant,
            )*
        }

        impl $backend {
            /// The best implementation a CPU with the features `f` can run.
            pub(crate) fn select(f: $crate::cpu::Features) -> Self {
                $(
                    $(#[$attr])*
                    if f.contains($crate::cpu::Features::all(&[$($req),*])) {
                        return Self::$variant;
                    }
                )*
                let _ = f;
                Self::$base
            }

            /// `update`.
            ///
            /// # Safety
            ///
            /// As for the artifacts; the CPU must have the features of the
            /// implementation (as `select` guarantees).
            pub(crate) unsafe fn update(
                self,
                state: &mut [u8; $state],
                count: u64,
                data: *const u8,
                len: usize,
                scratch: &mut [u64; $scratch],
            ) {
                // SAFETY: the caller's obligations.
                unsafe {
                    match self {
                        Self::$base => $update(state, count, data, len, scratch),
                        $($(#[$attr])* Self::$variant => $vupdate(state, count, data, len, scratch),)*
                    }
                }
            }

            /// `finalize`.
            ///
            /// # Safety
            ///
            /// As for the artifacts; the CPU must have the features of the
            /// implementation (as `select` guarantees).
            pub(crate) unsafe fn finalize(
                self,
                state: &mut [u8; $state],
                count: u64,
                out: &mut [u8; $max],
                scratch: &mut [u64; $scratch],
            ) {
                // SAFETY: the caller's obligations.
                unsafe {
                    match self {
                        Self::$base => $finalize(state, count, out, scratch),
                        $($(#[$attr])* Self::$variant => $vfinalize(state, count, out, scratch),)*
                    }
                }
            }
        }

        $(#[$doc])*
        ///
        /// `N` is the size of the digest, 1 to
        #[doc = concat!(stringify!($max), " bytes (a compile-time error otherwise).")]
        /// Keys are at most as long as the largest digest, and data (after
        /// a key block, for keyed hashing) is limited to 2⁶⁴ − 1 bytes.
        #[derive(Clone)]
        pub struct $name<const N: usize = $max> {
            /// The streaming state, representing the data so far.
            state: [u8; $state],
            /// The length of the data so far (the key block included), in
            /// bytes.
            length: u64,
            /// The implementation this CPU runs.
            backend: $backend,
        }

        impl<const N: usize> Drop for $name<N> {
            /// Wipes the streaming state (which represents the key, if any).
            fn drop(&mut self) {
                $crate::zeroize::zeroize(&mut self.state);
            }
        }

        impl<const N: usize> Default for $name<N> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<const N: usize> $name<N> {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = N;
            /// The size of a block, in bytes.
            pub const BLOCK_SIZE: usize = $block;
            /// The largest digest and key, in bytes.
            pub const MAX_SIZE: usize = $max;

            /// Starts a new (unkeyed) computation.
            pub fn new() -> Self {
                Self::new_keyed(&[])
            }

            /// Starts a new computation keyed with `key` (RFC 7693 §2.9), or
            /// unkeyed if `key` is empty.
            ///
            /// # Panics
            ///
            #[doc = concat!("If `key` is longer than ", stringify!($max), " bytes.")]
            pub fn new_keyed(key: &[u8]) -> Self {
                const { assert!(1 <= N && N <= $max, "unsupported digest size") };
                assert!(key.len() <= $max, "key too long");
                let mut state = [0; $state];
                // SAFETY: `1 ≤ N ≤ MAX` and `key.len() ≤ MAX`. `state` is
                // valid for writes of its size and `key` for reads of
                // `key.len()` bytes; they are distinct objects, so they do
                // not overlap each other, the return address (on x86-64 and
                // x86) or the arguments on the stack (on x86), and do not
                // wrap around the end of the address space.
                unsafe { $init(&mut state, N, key.as_ptr(), key.len()) };
                // The key block is the first block of the data.
                let length = if key.is_empty() { 0 } else { $block };
                let backend = $backend::select($crate::cpu::detected());
                $name { state, length, backend }
            }

            /// Absorbs `data`.
            ///
            /// # Panics
            ///
            /// If the data reaches 2⁶⁴ bytes.
            pub fn update(&mut self, data: &[u8]) {
                let length = self
                    .length
                    .checked_add(data.len() as u64)
                    .expect("data too long");
                let mut scratch = [0u64; $scratch];
                // SAFETY: `self.state` is valid for reads and writes of its
                // size, `data` for reads of `data.len()` bytes and `scratch`
                // for reads and writes of its size; they are distinct
                // objects, so they do not overlap each other, the return
                // address (on x86-64 and x86), the arguments on the stack
                // (on 32-bit ARM and x86) or the stack below them that the
                // call uses, and do not wrap around the end of the address
                // space. `self.length` is the length of the data
                // `self.state` represents, and adding `data.len()` to it
                // does not reach 2⁶⁴.
                unsafe {
                    self.backend.update(
                        &mut self.state,
                        self.length,
                        data.as_ptr(),
                        data.len(),
                        &mut scratch,
                    )
                };
                self.length = length;
            }

            /// Returns the digest of the data.
            pub fn finalize(mut self) -> [u8; N] {
                let mut out = [0; $max];
                let mut scratch = [0u64; $scratch];
                // SAFETY: `self.state` is valid for reads and writes of its
                // size, `out` for writes of its size and `scratch` for reads
                // and writes of its size; they are distinct objects, so they
                // do not overlap each other, the return address (on x86-64
                // and x86), the arguments on the stack (on 32-bit ARM and
                // x86) or the stack below them that the call uses, and do not
                // wrap around the end of the address space. `self.length` is
                // the exact length, less than 2⁶⁴, of the data `self.state`
                // represents.
                unsafe { self.backend.finalize(&mut self.state, self.length, &mut out, &mut scratch) };
                let mut digest = [0; N];
                digest.copy_from_slice(&out[..N]);
                digest
            }

            /// Checks that `mac` is the digest of the data (its MAC, if the
            /// computation is keyed), in constant time: the time taken does
            /// not depend on where, or whether, `mac` differs from it (its
            /// length is public). `mac` must be the whole digest, of `N`
            /// bytes; a truncated one is rejected.
            pub fn verify(self, mac: &[u8]) -> Result<(), $crate::hmac::InvalidMac> {
                if $crate::ct::eq(&self.finalize(), mac) {
                    Ok(())
                } else {
                    Err($crate::hmac::InvalidMac)
                }
            }

            /// The (unkeyed) digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; N] {
                let mut h = Self::new();
                h.update(data);
                h.finalize()
            }

            /// The digest of `data` keyed with `key` (a MAC; RFC 7693 §2.9).
            ///
            /// # Panics
            ///
            #[doc = concat!("If `key` is longer than ", stringify!($max), " bytes.")]
            pub fn digest_keyed(key: &[u8], data: &[u8]) -> [u8; N] {
                let mut h = Self::new_keyed(key);
                h.update(data);
                h.finalize()
            }
        }

        impl<const N: usize> super::HashFunction for $name<N> {
            const OUTPUT_SIZE: usize = N;
            const BLOCK_SIZE: usize = $block;
            type Output = [u8; N];

            fn new() -> Self {
                $name::new()
            }

            fn update(&mut self, data: &[u8]) {
                $name::update(self, data)
            }

            fn finalize(self) -> [u8; N] {
                $name::finalize(self)
            }
        }
    };
}

pub(super) use blake2;

#[cfg(test)]
mod tests {
    use super::super::blake2b::Blake2b;
    use super::super::blake2s::Blake2s;
    use crate::hmac::InvalidMac;

    /// `verify`, run by a computation of `mac`, accepts `mac` and rejects
    /// any other: one with a bit flipped in its first, a middle or its last
    /// byte, a truncated MAC, an empty one and a longer one.
    fn check<const N: usize>(mac: [u8; N], verify: impl Fn(&[u8]) -> Result<(), InvalidMac>) {
        assert_eq!(verify(&mac), Ok(()));
        for i in [0, N / 2, N - 1] {
            let mut bad = mac;
            bad[i] ^= 1;
            assert_eq!(verify(&bad), Err(InvalidMac));
        }
        assert_eq!(verify(&mac[..N - 1]), Err(InvalidMac));
        assert_eq!(verify(&[]), Err(InvalidMac));
        let mut longer = [0u8; 65];
        longer[..N].copy_from_slice(&mac);
        assert_eq!(verify(&longer[..N + 1]), Err(InvalidMac));
    }

    /// `verify`, keyed and unkeyed, for the largest digest and a smaller
    /// one.
    #[test]
    fn verify() {
        let (key, data) = (b"key", b"data");
        macro_rules! sizes {
            ($($hash:ident<$n:literal>),*) => {$(
                check($hash::<$n>::digest_keyed(key, data), |m| {
                    let mut h = $hash::<$n>::new_keyed(key);
                    h.update(data);
                    h.verify(m)
                });
                check($hash::<$n>::digest(data), |m| {
                    let mut h = $hash::<$n>::new();
                    h.update(data);
                    h.verify(m)
                });
            )*};
        }
        sizes!(Blake2b<64>, Blake2b<20>, Blake2s<32>, Blake2s<16>);
    }
}
