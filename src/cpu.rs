//! CPU features, for choosing among implementations of a primitive.
//!
//! Some artifacts use instructions beyond their target's baseline ISA. Lean
//! checks which CPU features those need, and the emitter lists them in a
//! generated `<NAME>_FEATURES` constant next to the function (and in its
//! `# Safety` section): the function may only be called on a CPU that has
//! all of them. They are detected once, with `cpuid`. Each object that can
//! use such a function chooses its implementation when it is created, from
//! the features detected.
//!
//! With the `cpu-features-env` Cargo feature, the environment variable
//! `VG_CPU_FEATURES` restricts the features detected, so that tests and
//! benchmarks can run every implementation on one machine: `none`, or a
//! comma-separated list of the names in [`NAMES`] (e.g. `aes,pclmulqdq`).
//! Unset or empty, it restricts nothing. It can only remove features, so it
//! can never choose code the CPU cannot run, and it names only features
//! this library knows: anything else panics, rather than quietly testing
//! another configuration.

use core::sync::atomic::{AtomicU32, Ordering};

/// The features detection knows, by their Rust `target_feature` names: bit
/// `i` of a [`Features`] is `NAMES[i]`.
const NAMES: [&str; 6] = ["ssse3", "sha", "aes", "pclmulqdq", "avx", "avx2"];

/// The bit of a feature detection does not know, which is never detected.
const UNKNOWN: u32 = 1 << 31;

/// A set of CPU features.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Features(pub(crate) u32);

impl Features {
    /// The features named in `names` (a generated `_FEATURES` constant).
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    pub(crate) fn of(names: &[&str]) -> Features {
        Features(names.iter().fold(0, |acc, n| {
            acc | NAMES
                .iter()
                .position(|m| m == n)
                .map_or(UNKNOWN, |i| 1 << i)
        }))
    }

    /// The features named in any of `lists`.
    // Only the x86-64 artifacts need features so far.
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    pub(crate) fn all(lists: &[&[&str]]) -> Features {
        Features(
            lists
                .iter()
                .fold(0, |acc, names| acc | Features::of(names).0),
        )
    }

    /// Whether every feature of `other` is in `self`.
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
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
/// bit 29 is SHA and bit 5 AVX2; AMD reports them in the same bits). AVX and
/// AVX2 also need the operating system to save the `ymm` registers: XCR0
/// bits 1 and 2, read with `xgetbv` only if OSXSAVE says it may be (Intel SDM
/// Vol. 1, §14.3, "Detection of Intel AVX Instructions").
#[cfg(target_arch = "x86_64")]
fn runtime() -> u32 {
    use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};
    // SAFETY: every x86-64 CPU has `cpuid`, and leaves 0 and 1; leaf 7 is
    // read only if leaf 0 says it exists, and `xgetbv` only if OSXSAVE says
    // the operating system has enabled it.
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
        let avx = (ecx >> 28) & ymm;
        let ebx = if max >= 7 { __cpuid_count(7, 0).ebx } else { 0 };
        let sha = (ebx >> 29) & 1;
        let avx2 = (ebx >> 5) & avx;
        ssse3 | (sha << 1) | (aes << 2) | (pclmulqdq << 3) | (avx << 4) | (avx2 << 5)
    }
}

/// No features are detected on the other targets yet.
#[cfg(not(target_arch = "x86_64"))]
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
        assert_eq!(Features::of(&["avx512f"]), Features(UNKNOWN));
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
        for bad in ["avx512f", "aes,", "aes,none", " aes", "AES"] {
            assert_eq!(parse(bad), None, "{bad}");
        }
    }
}
