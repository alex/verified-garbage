//! Wycheproof (<https://github.com/C2SP/wycheproof>) tests.
//!
//! The vectors are read from the checkout named by `WYCHEPROOF_ROOT`; if it
//! is not set, the tests are skipped (CI always sets it).
//!
//! Every algorithm gets a module here that loads its test vector files with
//! [`harness::load`] and checks each vector against the crate's public API.
//! A `valid` vector must produce exactly the expected result, an `invalid`
//! one must be rejected, and for an `acceptable` one either outcome is fine
//! (but a result, if produced, must be the expected one).

mod harness;
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
mod hmac;
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
mod pbkdf2;

use harness::Fields;

/// Every test vector file parses, and is internally consistent. This keeps
/// the harness honest as the Wycheproof vectors are updated.
#[test]
fn all_vector_files_are_well_formed() {
    require_vectors!();
    let files = harness::all_files().unwrap();
    assert!(!files.is_empty());
    for name in &files {
        let file = harness::load::<Fields, Fields>(name);
        assert!(!file.schema.is_empty(), "{name}: missing schema");
    }
}
