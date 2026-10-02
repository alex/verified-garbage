# DSA development

The specification in `lean/VerifiedGarbage/Spec/Dsa.lean` covers the six
operations in [issue #1](https://github.com/pyca/verified-garbage/issues/1).
It transcribes the historical DSA equations and parameter construction from
[FIPS 186-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf),
§§4.1–4.7 and Appendices A.1.1.2, A.2.1, B.1.2 and B.2.2.

The spec takes already-hashed digest bytes and represents signatures as
integer pairs. It truncates the digest to its leftmost N bits, accepts
shorter digests without shifting their value, rejects zero or out-of-range
signature components, and validates public subgroup membership. Component
import checks the parameter sizes, exact primality, group order, scalar
ranges, and private/public consistency. Signing and key generation require
validated parameters; signature verification checks the public projection.

Parameter generation selects (1024,160), (2048,256), or (3072,256) from the
requested p bit length. Import also accepts (2048,224). SHA-1 and SHA-256
are used in the respective default parameter constructions, with wraparound
seed addition and the specified 4L counter bound. A.2.1 generates g from a
separate h tape. Parameter provenance validation is outside this interface.
Exact primality is a mathematical specification, not a practical large-prime
testing implementation.

Pure randomized operations consume finite candidate tapes. Production
wrappers must supply independent uniform candidates from OS randomness,
retry on exhaustion, and handle RNG failure. Private scalars and nonces are
sampled uniformly by rejection in [1,q-1]; signing retries if r or s is zero.
These tapes are an explicit model of randomness, not new public API arguments.
The mathematical spec's control flow does not constitute a constant-time
implementation. Signature encoding and prehash API checks remain separate.

The spec and its limb contracts are a trust change. Implementation proofs
must be reviewed separately after the spec is reviewed and merged, as
required by `AGENTS.md`. No ISA model changes are needed for the initial
limb primitives. There is no public Rust DSA API or architecture support yet.

Known answers are read directly from the vendored NIST CAVP archive files;
`vectors/sources/nist-cavp-dsa.toml` records the source URL and archive hash.
Specification tests check all 300 signing vectors, 300 verification vectors,
and 15 parameter-generation candidates for the default size/hash combinations,
plus synthetic properties for zero-component retries and boundary handling.
The spec passes the standard-axiom and compiler-override audits.
