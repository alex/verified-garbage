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

mod aes_gcm;
mod chacha20;
mod chacha20poly1305;
mod harness;
mod hmac;
mod hmac_sha1;
mod hmac_sha256;
mod hmac_sha384;
mod hmac_sha512;
mod hmac_sha512_224;
mod hmac_sha512_256;
mod pbkdf2;
mod pbkdf2_sha1;
mod pbkdf2_sha256;
mod pbkdf2_sha384;
mod pbkdf2_sha512;

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
