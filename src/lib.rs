//! An experimental, formally verified cryptography library, implemented
//! entirely by LLMs.
//!
//! All cryptographic code in this crate is assembly that has been formally
//! verified in Lean: see `lean/README.md` for what is proven and what has to
//! be trusted. The assembly lives in naked functions in the generated
//! `asm` module; everything else in the crate is safe Rust wrapping it.

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

mod asm;

#[cfg(test)]
mod tests {
    /// The pipeline self-test artifact (`VG.Spec.Selftest.addX86_64`).
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
            let r = unsafe { crate::asm::x86_64::vg_selftest_add(a, b) };
            assert_eq!(r, a.wrapping_add(b), "vg_selftest_add({a:#x}, {b:#x})");
        }
    }
}
