//! CPU features, for choosing among implementations of a primitive.
//!
//! Some artifacts use instructions beyond their target's baseline ISA. Lean
//! checks which CPU features those need, and the emitter lists them in a
//! generated `<NAME>_FEATURES` constant next to the function (and in its
//! `# Safety` section): the function may only be called on a CPU that has
//! all of them. They are detected once: with `cpuid` on x86 and x86-64; on AArch64,
//! by asking the operating system with the `cpu-features-env` feature (which
//! links `std`), and otherwise from the target features the code was
//! compiled for. Each object that can use such a function chooses its
//! implementation when it is created, from the features detected.
//!
//! With the `cpu-features-env` Cargo feature, the environment variable
//! `VG_CPU_FEATURES` restricts the features detected, so that tests and
//! benchmarks can run every implementation on one machine: `none`, or a
//! comma-separated list of the names in [`NAMES`] (e.g. `aes,pclmulqdq`).
//! Unset or empty, it restricts nothing. It can only remove features, so it
//! can never choose code the CPU cannot run, and it names only features
//! this library knows: anything else panics, rather than quietly testing
//! another configuration. (On AArch64, FEAT_SHA3's Keccak, which is not
//! faster, is chosen only when it names `sha3`.)

use core::sync::atomic::{AtomicU32, Ordering};

/// The features detection knows, by their Rust `target_feature` names: bit
/// `i` of a [`Features`] is `NAMES[i]`.
pub(crate) const NAMES: [&str; 17] = [
    "ssse3",
    "sha",
    "aes",
    "pclmulqdq",
    "avx",
    "avx2",
    "bmi1",
    "bmi2",
    "avx512f",
    "sha512",
    "sha2",
    "sha3",
    "adx",
    "avx512ifma",
    "avx512vl",
    "neon",
    "sve2",
];

/// The bit of a feature detection does not know, which is never detected.
const UNKNOWN: u32 = 1 << 31;

/// A set of CPU features.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Features(pub(crate) u32);

impl Features {
    /// The features named in `names` (a generated `_FEATURES` constant).
    #[cfg_attr(
        not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")),
        allow(dead_code)
    )]
    pub(crate) fn of(names: &[&str]) -> Features {
        Features(names.iter().fold(0, |acc, n| {
            acc | NAMES
                .iter()
                .position(|m| m == n)
                .map_or(UNKNOWN, |i| 1 << i)
        }))
    }

    /// The features named in any of `lists`.
    #[cfg_attr(
        not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")),
        allow(dead_code)
    )]
    pub(crate) fn all(lists: &[&[&str]]) -> Features {
        Features(
            lists
                .iter()
                .fold(0, |acc, names| acc | Features::of(names).0),
        )
    }

    /// Whether every feature of `other` is in `self`.
    #[cfg_attr(
        not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")),
        allow(dead_code)
    )]
    pub(crate) fn contains(self, other: Features) -> bool {
        self.0 & other.0 == other.0
    }
}

/// The detected features, with [`DETECTED_INIT`] set once they are known.
static DETECTED: AtomicU32 = AtomicU32::new(0);
const DETECTED_INIT: u32 = 1 << 30;

/// The features of this CPU, restricted by `VG_CPU_FEATURES` (see the
/// module's documentation). (Detection is idempotent, so threads racing to
/// do it store the same value, and `Relaxed` is enough.)
pub(crate) fn detected() -> Features {
    let mut f = DETECTED.load(Ordering::Relaxed);
    if f & DETECTED_INIT == 0 {
        f = (runtime() & allowed()) | DETECTED_INIT;
        DETECTED.store(f, Ordering::Relaxed);
    }
    Features(f & !DETECTED_INIT)
}

/// The features `VG_CPU_FEATURES` allows.
///
/// # Panics
///
/// If it names a feature not in [`NAMES`].
#[cfg(feature = "cpu-features-env")]
fn allowed() -> u32 {
    let names = std::env::var("VG_CPU_FEATURES").unwrap_or_default();
    parse(&names).expect("VG_CPU_FEATURES names a CPU feature this library does not know")
}

/// Every feature: without the `cpu-features-env` Cargo feature, nothing
/// restricts them.
#[cfg(not(feature = "cpu-features-env"))]
fn allowed() -> u32 {
    u32::MAX
}

/// The features a value of `VG_CPU_FEATURES` allows (every one if it is
/// empty, none if it is `none`), or `None` if it names an unknown one.
#[cfg(feature = "cpu-features-env")]
fn parse(names: &str) -> Option<u32> {
    match names {
        "" => Some(u32::MAX),
        "none" => Some(0),
        _ => names.split(',').try_fold(0, |acc, n| {
            NAMES.iter().position(|m| *m == n).map(|i| acc | 1 << i)
        }),
    }
}

/// Asks the CPU (Intel SDM Vol. 2A, CPUID: leaf 1 ECX bit 9 is SSSE3, bit 25
/// AES, bit 1 PCLMULQDQ, bit 27 OSXSAVE and bit 28 AVX; leaf 7 sub-leaf 0 EBX
/// bit 29 is SHA, bit 5 AVX2, bit 3 BMI1, bit 8 BMI2, bit 16 AVX512F, bit 19
/// ADX, bit 21 AVX512_IFMA and bit 31 AVX512VL, and its EAX the highest
/// sub-leaf; leaf 7 sub-leaf 1 EAX bit 0 is SHA512; AMD reports them in the
/// same bits). AVX, AVX2 and SHA512 (whose instructions are VEX.256-encoded, so
/// also need AVX, Intel SDM Vol. 2, "VSHA512RNDS2") also need the operating
/// system to save the `ymm` registers: XCR0 bits 1 and 2, read with `xgetbv`
/// only if OSXSAVE says it may be (Intel SDM Vol. 1, §14.3, "Detection of Intel
/// AVX Instructions"); AVX512F, AVX512_IFMA and AVX512VL (whose instructions
/// are EVEX-encoded) also need the opmask and `zmm` state, XCR0 bits 5, 6 and 7
/// (§15.2, "Detection of AVX-512 Foundation Instructions", and §15.4 for the
/// other AVX-512 instruction groups).
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn runtime() -> u32 {
    #[cfg(target_arch = "x86")]
    use core::arch::x86::{__cpuid, __cpuid_count, _xgetbv};
    #[cfg(target_arch = "x86_64")]
    use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};
    // SAFETY: the i686 and x86-64 target baselines have `cpuid`, and leaves
    // 0 and 1; leaf 7 is read only if leaf 0 says it exists (and its
    // sub-leaf 1 only if sub-leaf 0 says that exists), and `xgetbv` only if
    // OSXSAVE says the operating system has enabled it.
    #[allow(unused_unsafe)]
    unsafe {
        let max = __cpuid(0).eax;
        let ecx = __cpuid(1).ecx;
        let ssse3 = (ecx >> 9) & 1;
        let aes = (ecx >> 25) & 1;
        let pclmulqdq = (ecx >> 1) & 1;
        let osxsave = (ecx >> 27) & 1 == 1;
        let xcr0 = if osxsave { _xgetbv(0) } else { 0 };
        let ymm = u32::from(xcr0 & 0b110 == 0b110);
        let zmm = u32::from(xcr0 & 0b1110_0110 == 0b1110_0110);
        let avx = (ecx >> 28) & ymm;
        let (sub, ebx) = if max >= 7 {
            let l = __cpuid_count(7, 0);
            (l.eax, l.ebx)
        } else {
            (0, 0)
        };
        let eax1 = if max >= 7 && sub >= 1 {
            __cpuid_count(7, 1).eax
        } else {
            0
        };
        let sha = (ebx >> 29) & 1;
        let avx2 = (ebx >> 5) & avx;
        let bmi1 = (ebx >> 3) & 1;
        let bmi2 = (ebx >> 8) & 1;
        let avx512f = (ebx >> 16) & avx & zmm;
        let sha512 = eax1 & avx;
        let adx = (ebx >> 19) & 1;
        let avx512ifma = (ebx >> 21) & avx & zmm;
        let avx512vl = (ebx >> 31) & avx & zmm;
        ssse3
            | (sha << 1)
            | (aes << 2)
            | (pclmulqdq << 3)
            | (avx << 4)
            | (avx2 << 5)
            | (bmi1 << 6)
            | (bmi2 << 7)
            | (avx512f << 8)
            | (sha512 << 9)
            | (adx << 12)
            | (avx512ifma << 13)
            | (avx512vl << 14)
    }
}

/// AArch64 feature groups, using the same Rust names as the generated
/// artifacts: `aes` covers FEAT_AES and FEAT_PMULL, `sha2` covers FEAT_SHA1
/// and FEAT_SHA256, `sha3` covers FEAT_SHA512 and FEAT_SHA3, and `sve2` is
/// FEAT_SVE2.
#[cfg(target_arch = "aarch64")]
fn runtime() -> u32 {
    (u32::from(aarch64_aes()) * Features::of(&["aes"]).0)
        | (u32::from(aarch64_sha2()) * Features::of(&["sha2"]).0)
        | (u32::from(aarch64_sha3()) * Features::of(&["sha3"]).0)
        | (u32::from(aarch64_sve2()) * Features::of(&["sve2"]).0)
        // AdvSIMD is the AArch64 baseline used by the verified ISA.
        // Keep a mask bit so tests and benchmarks can select scalar code.
        | Features::of(&["neon"]).0
}

/// Whether the CPU has FEAT_AES and FEAT_PMULL, asked of the operating
/// system through `std`, which the `cpu-features-env` feature links.
#[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
fn aarch64_aes() -> bool {
    std::arch::is_aarch64_feature_detected!("aes")
}

/// Whether the compiler was told every CPU running this code has FEAT_AES
/// and FEAT_PMULL (as `aarch64-apple-darwin` and `-C target-feature=+aes`
/// do): without `std`, this `no_std` crate cannot ask the operating system.
#[cfg(all(target_arch = "aarch64", not(feature = "cpu-features-env")))]
fn aarch64_aes() -> bool {
    cfg!(target_feature = "aes")
}

/// Whether both SHA-1 and SHA-256 instructions are available.
#[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
fn aarch64_sha2() -> bool {
    std::arch::is_aarch64_feature_detected!("sha2")
}

/// Without `std`, use only features guaranteed by the compilation target.
#[cfg(all(target_arch = "aarch64", not(feature = "cpu-features-env")))]
fn aarch64_sha2() -> bool {
    cfg!(target_feature = "sha2")
}

/// Whether both SHA-512 and SHA-3 instructions are available.
#[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
fn aarch64_sha3() -> bool {
    std::arch::is_aarch64_feature_detected!("sha3")
}

/// Without `std`, use only features guaranteed by the compilation target.
#[cfg(all(target_arch = "aarch64", not(feature = "cpu-features-env")))]
fn aarch64_sha3() -> bool {
    cfg!(target_feature = "sha3")
}

/// Whether the CPU has FEAT_SVE2, asked of the operating system (which also
/// says whether it has enabled SVE for this process).
#[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
fn aarch64_sve2() -> bool {
    std::arch::is_aarch64_feature_detected!("sve2")
}

/// Without `std`, use only features guaranteed by the compilation target.
#[cfg(all(target_arch = "aarch64", not(feature = "cpu-features-env")))]
fn aarch64_sve2() -> bool {
    cfg!(target_feature = "sve2")
}

/// No features are detected on the other targets yet.
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
fn runtime() -> u32 {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn of_names() {
        assert_eq!(Features::of(&[]), Features(0));
        assert_eq!(Features::of(&["sha", "ssse3"]), Features(0b11));
        assert_eq!(Features::of(&["pclmulqdq", "aes"]), Features(0b1100));
        assert_eq!(Features::of(&["avx", "avx2"]), Features(0b11_0000));
        assert_eq!(Features::of(&["bmi2", "bmi1"]), Features(0b1100_0000));
        assert_eq!(Features::of(&["avx", "avx512f"]), Features(0b1_0001_0000));
        assert_eq!(
            Features::of(&["avx", "avx2", "sha512"]),
            Features(0b10_0011_0000)
        );
        assert_eq!(
            Features::of(&["bmi2", "adx"]),
            Features((1 << 12) | (1 << 7))
        );
        assert_eq!(
            Features::of(&["avx512vl", "avx512ifma"]),
            Features((1 << 14) | (1 << 13))
        );
        assert_eq!(Features::of(&["avx512bw"]), Features(UNKNOWN));
        assert_eq!(Features::of(&["sha2"]), Features(1 << 10));
        assert_eq!(Features::of(&["sha3"]), Features(1 << 11));
        assert_eq!(Features::of(&["neon"]), Features(1 << 15));
        assert_eq!(Features::of(&["sve2"]), Features(1 << 16));
        assert_eq!(
            Features::all(&[&["sha"], &[], &["ssse3", "sha"]]),
            Features(0b11)
        );
    }

    #[test]
    fn unknown_is_never_detected() {
        assert!(!detected().contains(Features(UNKNOWN)));
    }

    /// Detection returns the CPU's features, restricted as
    /// `VG_CPU_FEATURES` says.
    #[test]
    fn detected_is_allowed() {
        assert_eq!(detected(), Features(runtime() & allowed()));
    }

    #[cfg(feature = "cpu-features-env")]
    #[test]
    fn parse_names() {
        assert_eq!(parse(""), Some(u32::MAX));
        assert_eq!(parse("none"), Some(0));
        assert_eq!(parse("sha"), Some(0b10));
        assert_eq!(parse("aes,pclmulqdq,ssse3"), Some(0b1101));
        assert_eq!(parse("avx,avx2"), Some(0b11_0000));
        assert_eq!(parse("bmi1,bmi2"), Some(0b1100_0000));
        assert_eq!(parse("avx512f"), Some(0b1_0000_0000));
        assert_eq!(parse("sha512"), Some(0b10_0000_0000));
        assert_eq!(parse("sha2"), Some(1 << 10));
        assert_eq!(parse("sha3"), Some(1 << 11));
        assert_eq!(parse("neon,sve2"), Some((1 << 15) | (1 << 16)));
        assert_eq!(parse("sha2,sha3"), Some((1 << 10) | (1 << 11)));
        assert_eq!(parse("adx"), Some(1 << 12));
        for bad in ["avx512bw", "aes,", "aes,none", " aes", "AES"] {
            assert_eq!(parse(bad), None, "{bad}");
        }
    }
}
