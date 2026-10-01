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
#[cfg(feature = "cpu-features-env")]
extern crate std;

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

// The ISA models are little-endian, and the contracts assume the pointer
// width of each architecture's calling convention: the verified assembly is
// compiled only where both hold (each target's `rustCfg`, in
// `lean/VerifiedGarbage/TCB/<Target>/Target.lean`), not on aarch64_be, armeb
// or x32. This `compile_error!` and those below each mirror a condition of a
// `rustCfg`.
#[cfg(any(
    all(
        any(target_arch = "aarch64", target_arch = "arm"),
        target_endian = "big"
    ),
    all(
        any(target_arch = "aarch64", target_arch = "x86_64"),
        target_pointer_width = "32"
    ),
))]
compile_error!(
    "the verified assembly needs a little-endian target with its architecture's usual pointer width (not, e.g., aarch64_be or x32)"
);

// The 32-bit x86 model's baseline is i686 with SSE2 (see
// `lean/VerifiedGarbage/TCB/X86/Isa.lean`): older CPUs' `mul` is not constant
// time.
#[cfg(all(target_arch = "x86", not(target_feature = "sse2")))]
compile_error!("32-bit x86 needs an i686 target with SSE2 (e.g. i686-unknown-linux-gnu)");

// The x86-64 model's baseline includes SSE2, as the System V psABI's does,
// but `x86_64-unknown-none` and `x86_64-unknown-uefi` turn it off (and the
// Rust code there would not save the SSE registers the functions use, some of
// which UEFI's calling convention makes callee-saved).
#[cfg(all(target_arch = "x86_64", not(target_feature = "sse2")))]
compile_error!(
    "x86-64 needs a target with SSE2 (not, e.g., x86_64-unknown-none or x86_64-unknown-uefi)"
);

// The AArch64 model's baseline includes AdvSIMD (NEON), which
// `aarch64-unknown-none-softfloat` turns off.
#[cfg(all(target_arch = "aarch64", not(target_feature = "neon")))]
compile_error!("AArch64 needs a target with NEON (not, e.g., aarch64-unknown-none-softfloat)");

// The ARM model's calling convention is AAPCS; Apple's 32-bit ARM targets use
// APCS (armv7s-apple-ios) or AAPCS16 (armv7k-apple-watchos), which pass some
// arguments elsewhere.
#[cfg(all(target_arch = "arm", target_vendor = "apple"))]
compile_error!("32-bit ARM needs an AAPCS target (not Apple's armv7s or armv7k)");

mod aes;
pub mod aes_gcm;
pub mod chacha20;
pub mod chacha20poly1305;
pub mod cmac;
mod ct;
pub mod ed25519;
pub mod hashes;
pub mod hmac;
pub mod mldsa44;
pub mod mldsa65;
pub mod mldsa87;
mod mldsa_common;
pub mod mlkem1024;
pub mod mlkem768;
pub mod pbkdf2;
pub mod poly1305;
pub mod rc2_cbc;
pub mod triple_des_ecb;
pub mod scrypt;
pub mod x25519;
pub mod x448;
mod zeroize;

#[cfg(test)]
mod argon2_compress_tests;

#[cfg(test)]
mod argon2_hprime_tests;

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
