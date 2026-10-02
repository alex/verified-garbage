//! NIST ACVP (<https://github.com/usnistgov/ACVP-Server>) known-answer tests.
//!
//! The `internalProjection.json` files of the test vector sets are vendored
//! under `vectors/nist-acvp/` (see `vectors/sources/` for where each one comes
//! from) and compiled into the test binary, so these tests always run.

mod hmac;
mod hmac_sha384;
mod hmac_sha512;
mod hmac_sha512_224;
mod hmac_sha512_256;
mod mldsa;
mod mldsa44;
mod mldsa65;
mod mldsa87;
mod mlkem1024;
mod mlkem768;
