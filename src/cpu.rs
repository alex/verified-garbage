//! CPU features, for choosing among implementations of a primitive.
//!
//! Some artifacts use instructions beyond their target's baseline ISA. Lean
//! checks which CPU features those need, and the emitter lists them in a
//! generated `<NAME>_FEATURES` constant next to the function (and in its
//! `# Safety` section): the function may only be called on a CPU that has
//! all of them. They are detected once, with `cpuid`. Each object that can
//! use such a function chooses its implementation when it is created, from
//! the features detected, restricted by a mask; the mask (all ones, except
//! in tests) can only remove features, so it can never choose code the CPU
//! cannot run.

use core::sync::atomic::{AtomicU32, Ordering};

/// The features detection knows, by their Rust `target_feature` names: bit
/// `i` of a [`Features`] is `NAMES[i]`.
const NAMES: [&str; 4] = ["ssse3", "sha", "aes", "pclmulqdq"];

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

/// The features of this CPU. (Detection is idempotent, so threads racing to
/// do it store the same value, and `Relaxed` is enough.)
pub(crate) fn detected() -> Features {
    let mut f = DETECTED.load(Ordering::Relaxed);
    if f & DETECTED_INIT == 0 {
        f = runtime() | DETECTED_INIT;
        DETECTED.store(f, Ordering::Relaxed);
    }
    Features(f & !DETECTED_INIT)
}

/// The features of this CPU that are in `mask`.
pub(crate) fn available(mask: u32) -> Features {
    Features(detected().0 & mask)
}

/// Asks the CPU (Intel SDM Vol. 2A, CPUID: leaf 1 ECX bit 9 is SSSE3, bit 25
/// AES and bit 1 PCLMULQDQ; leaf 7 sub-leaf 0 EBX bit 29 is SHA; AMD reports
/// them in the same bits).
#[cfg(target_arch = "x86_64")]
fn runtime() -> u32 {
    use core::arch::x86_64::{__cpuid, __cpuid_count};
    // SAFETY: every x86-64 CPU has `cpuid`, and leaves 0 and 1; leaf 7 is
    // read only if leaf 0 says it exists.
    #[allow(unused_unsafe)]
    unsafe {
        let max = __cpuid(0).eax;
        let ecx = __cpuid(1).ecx;
        let ssse3 = (ecx >> 9) & 1;
        let aes = (ecx >> 25) & 1;
        let pclmulqdq = (ecx >> 1) & 1;
        let sha = if max >= 7 {
            (__cpuid_count(7, 0).ebx >> 29) & 1
        } else {
            0
        };
        ssse3 | (sha << 1) | (aes << 2) | (pclmulqdq << 3)
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
        assert_eq!(Features::of(&["avx512f"]), Features(UNKNOWN));
        assert_eq!(
            Features::all(&[&["sha"], &[], &["ssse3", "sha"]]),
            Features(0b11)
        );
    }

    #[test]
    fn unknown_is_never_available() {
        assert!(!available(u32::MAX).contains(Features(UNKNOWN)));
        assert!(!detected().contains(Features(UNKNOWN)));
    }

    #[test]
    fn masking_only_removes() {
        let all = detected();
        assert_eq!(available(u32::MAX), all);
        assert_eq!(available(0), Features(0));
        for mask in 0..16 {
            assert!(all.contains(available(mask)));
        }
    }
}
