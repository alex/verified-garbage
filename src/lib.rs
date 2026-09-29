//! An experimental, formally verified cryptography library, implemented
//! entirely by LLMs.
//!
//! The cryptographic primitives are assembly that has been formally verified
//! in Lean (see `lean/README.md` for what is proven and what has to be
//! trusted). They live in naked functions in the generated `asm` module, and
//! the public APIs compose them.

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod asm;
mod cpu;

// The verified assembly of the architecture being compiled for:
// `crate::arch::<module>` is `crate::asm::<target>::<module>`, so a module
// that runs the same functions on every architecture it supports imports
// them once (and supporting another architecture changes only its
// `#![cfg(...)]`).
#[cfg(target_arch = "aarch64")]
use asm::aarch64 as arch;
#[cfg(target_arch = "arm")]
use asm::arm as arch;
#[cfg(target_arch = "x86")]
use asm::x86 as arch;
#[cfg(target_arch = "x86_64")]
use asm::x86_64 as arch;

// The 32-bit x86 model's baseline is i686 with SSE2 (see
// `lean/VerifiedGarbage/TCB/X86/Isa.lean`): older CPUs' `mul` is not constant
// time.
#[cfg(all(target_arch = "x86", not(target_feature = "sse2")))]
compile_error!("32-bit x86 needs an i686 target with SSE2 (e.g. i686-unknown-linux-gnu)");

pub mod aes_gcm;
pub mod chacha20;
pub mod chacha20poly1305;
pub mod hashes;
pub mod hmac;
pub mod pbkdf2;
pub mod poly1305;
pub mod scrypt;

#[cfg(test)]
mod tests {
    /// The pipeline self-test artifact (`VG.Spec.Selftest.addContract`).
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn selftest_add_x86_64() {
        let cases = [
            (0, 0),
            (1, 2),
            (u64::MAX, 1),
            (u64::MAX, u64::MAX),
            (0x8000_0000_0000_0000, 0x8000_0000_0000_0000),
            (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
        ];
        for (a, b) in cases {
            // SAFETY: the contract has no preconditions.
            let r = unsafe { crate::asm::x86_64::selftest::vg_selftest_add(a, b) };
            assert_eq!(r, a.wrapping_add(b));
        }
    }
}
