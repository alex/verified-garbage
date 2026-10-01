# Verified Garbage

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="logo-dark.svg">
  <img src="logo.svg" alt="Verified Garbage logo" width="280">
</picture>

Verified Garbage is an experimental cryptography library, implemented entirely by LLMs. All of the cryptography primitives are formally verified using Lean.

Its aims are, in order:

1. Security
2. Correctness
3. Performance

The library is implemented in Lean, assembly, and Rust.

It targets: x86 (i686 with SSE2), x86-64, ARMv7, ARM64, and PPC64le.

The crate refuses to build for configurations its ISA models do not
describe: big-endian ARM and ARM64, x32, x86 or x86-64 without SSE2 (e.g.
`i586-*`, `x86_64-unknown-none`, the UEFI targets), ARM64 without NEON
(`aarch64-unknown-none-softfloat`), and Apple's 32-bit ARM targets, which do
not use AAPCS. Rust has no `cfg` for some other assumptions, so they are
yours to keep:

* On 32-bit x86, don't build with nightly's `-Zregparm`, which moves
  `extern "C"` arguments from the stack to registers.
* ARMv7 code does word loads and stores at unaligned addresses. Hosted
  targets allow them; bare-metal code (e.g. `armv7a-none-eabi*`, built
  `+strict-align`) must turn off alignment checking and run with the MMU
  on, with its buffers in Normal memory: otherwise an unaligned access
  faults or, on some cores, is UNPREDICTABLE.
* Only ARMv7 and later are supported on 32-bit ARM; older targets
  (`arm-*`, `armv5te-*`, …) are rejected only because the code does not
  assemble for them.

## Algorithms

<!-- BEGIN ci/algorithms_table.py: edit docs/algorithms/, then run it -->

### Hashes

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>BLAKE2b</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>BLAKE2s</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>MD5</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>SHA-1</td>

<td>✅</td>

<td>✅ SHA extensions</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>SHA-256</td>

<td>✅</td>

<td>✅ SHA extensions, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, SHAKE256</td>

<td>✅</td>

<td>✅ lane complementing</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>SHA-384, SHA-512, SHA-512/224, SHA-512/256</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### MACs

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>AES-CMAC (128-, 192- and 256-bit keys)</td>

<td>✅</td>

<td>✅ AES-NI</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

</tr>

<tr>

<td>HMAC-MD5</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>HMAC-SHA-1</td>

<td>✅</td>

<td>✅ SHA extensions</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>HMAC-SHA-256</td>

<td>✅</td>

<td>✅ SHA extensions, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>HMAC-SHA-384</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>HMAC-SHA-512/224</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>HMAC-SHA-512/256</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>HMAC-SHA-512</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>Poly1305</td>

<td>✅</td>

<td>✅ AVX2</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### Ciphers

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>ChaCha20</td>

<td>✅</td>

<td>✅ AVX-512F, AVX2</td>

<td>✅ NEON</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>RC2-CBC</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### AEADs

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>AES-GCM (128-, 192- and 256-bit keys)</td>

<td>✅</td>

<td>✅ AES-NI, PCLMULQDQ; GHASH with <code>mul</code></td>

<td>✅ AES, PMULL</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ChaCha20-Poly1305</td>

<td>✅</td>

<td>✅ AVX-512F, AVX2</td>

<td>✅ NEON</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### KDFs

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>Argon2d</td>

<td>✅</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

</tr>

<tr>

<td>Argon2i</td>

<td>✅</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

</tr>

<tr>

<td>Argon2id</td>

<td>✅</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

<td>❌</td>

</tr>

<tr>

<td>PBKDF2-HMAC-MD5</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>PBKDF2-HMAC-SHA-1</td>

<td>✅</td>

<td>✅ SHA extensions</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>PBKDF2-HMAC-SHA-256</td>

<td>✅</td>

<td>✅ SHA extensions, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>PBKDF2-HMAC-SHA-384</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>PBKDF2-HMAC-SHA-512/224</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>PBKDF2-HMAC-SHA-512/256</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>PBKDF2-HMAC-SHA-512</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>scrypt</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### KEMs

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>ML-KEM-1024</td>

<td>✅</td>

<td>✅ AVX2; SSE2 polynomial arithmetic</td>

<td>✅ SHA extensions; NEON polynomial arithmetic</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ML-KEM-768</td>

<td>✅</td>

<td>✅ AVX2; SSE2 polynomial arithmetic</td>

<td>✅ SHA extensions; NEON polynomial arithmetic</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### Key agreement

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>X25519</td>

<td>✅</td>

<td>✅ AVX-512 IFMA, AVX-512VL, AVX2, BMI2, ADX</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>X448</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

### Signatures

<table>

<tr>

<th>Algorithm</th>

<th>Spec landed</th>

<th>x86-64</th>

<th>ARM64</th>

<th>ARMv7</th>

<th>x86</th>

</tr>

<tr>

<td>Ed25519</td>

<td>✅</td>

<td>✅ SHA512, AVX2, BMI1, BMI2</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ML-DSA-44</td>

<td>✅</td>

<td>✅</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ML-DSA-65</td>

<td>✅</td>

<td>✅</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ML-DSA-87</td>

<td>✅</td>

<td>✅</td>

<td>✅ SHA extensions</td>

<td>✅</td>

<td>✅</td>

</tr>

</table>

<!-- END ci/algorithms_table.py -->

The tables are generated from the code by `ci/algorithms_table.py`.

* **Spec landed**: the algorithm's specification, transcribed from its
  standard, is in `lean/VerifiedGarbage/Spec/`.
* **x86-64**, **ARM64**, **ARMv7**, **x86**: ✅ when verified assembly and a
  public Rust API exist on that architecture (PPC64le is not started yet),
  followed by how it has been optimized, if it has (e.g. with SHA-NI or
  NEON). Where an optimization needs CPU features beyond the architecture's
  baseline, the features are detected at run time, and CPUs without them
  run the straightforward scalar code that every other implementation is.

Our goal is to implement all the cryptographic algorithms that are used by the Python pyca/cryptography library.

## How it works

* Each primitive is written in assembly, as a program over a Lean model of the
  target ISA, and proven in Lean to be correct against a specification, memory
  safe, and constant time (scrypt's ROMix is the exception its standard
  makes: it reads memory at indices derived from the password, and its
  contract declares that it leaks them and nothing else secret; see also
  [what the constant-time guarantee assumes](#what-the-constant-time-guarantee-assumes)).
  See [`lean/README.md`](lean/README.md) for the
  layout, the pipeline, and exactly what has to be trusted.
* Constant time means that the sequence of instructions and memory
  addresses does not depend on secrets; that each instruction's own timing
  does not depend on its data is an assumption about the CPU, recorded in
  each ISA model (`lean/VerifiedGarbage/TCB/<ISA>/Isa.lean`). On x86 and
  x86-64 it rests on Intel's data operand independent timing guidance,
  which covers only Intel Core and Atom processors (not AMD's, VIA's or
  the Pentium 4's), holds on Intel processors from Ice Lake (Atom:
  Gracemont) on only if the operating system has set the DOITM bit, which
  user code cannot, and does not list the `VSHA512*` instructions that
  SHA-512 uses on CPUs with the SHA512 extension.
* The proven assembly is emitted into [`src/asm/`](src/asm/) (one directory
  per architecture) as Rust naked functions (`naked_asm!`); there is no build
  script and no separate assembler step.
* The public APIs are Rust that composes these verified primitives (see
  [what is not verified](#what-is-not-verified)).
* The public APIs are tested against the [Wycheproof](https://github.com/C2SP/wycheproof)
  test vectors (`tests/wycheproof/`).

### What the constant-time guarantee assumes

* **AArch64 needs PSTATE.DIT set.** Arm specifies that the modelled
  instructions take a time independent of their data only while PSTATE.DIT
  (Data Independent Timing, `FEAT_DIT`) is 1; with DIT = 0, "the
  architecture makes no statement about the timing properties of any
  instructions" (Arm ARM, `DIT`). The proofs assume DIT = 1
  (`lean/VerifiedGarbage/TCB/AArch64/Isa.lean`), but nothing in this library
  sets it, and nothing guarantees that it is set when it runs. On AArch64,
  the constant-time guarantee therefore holds only if the application sets
  DIT on each thread that calls this library, around the calls, as Apple's
  [Writing ARM64 code for Apple platforms](https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms#Enable-DIT-for-constant-time-cryptographic-operations)
  tells cryptographic code to: with `timingsafe_enable_if_supported` and
  `timingsafe_restore_if_supported` (macOS 15.2, iOS 18.2 and later), or
  elsewhere `msr DIT, #1` (allowed at EL0 on CPUs with `FEAT_DIT`, which
  Linux reports as `HWCAP_DIT` and macOS as `hw.optional.arm.FEAT_DIT`),
  restoring the previous value afterwards. On CPUs without `FEAT_DIT`, Arm
  makes no timing statement at all.
* **Some leaks are hashes of secrets.** A constant-time theorem says that the
  code's secret-dependent behaviour (branches and memory addresses) is a
  function of what its contract says it may leak. For most functions that
  is nothing secret; a few leak values computed from secrets by SHAKE:
  ML-DSA key generation leaks `ρ` (from `H(ξ ‖ k ‖ ℓ)`) and which
  half-bytes of the `ρ′`-derived stream `ExpandS` rejects; ML-DSA signing
  leaks each iteration's commitment hash `c̃`, whether it was rejected, and
  the hint of the signature;
  ML-KEM key generation leaks `ρ` (from `G(d ‖ k)`)
  (`Spec/MlDsa/Contract.lean`, `Spec/MlKem/Contract.lean`). `ρ` is part of
  the public key and the last `c̃` and the hint of the signature, and the others are
  pseudorandom outputs of SHAKE that are never revealed, so these leaks are
  not believed to reveal anything useful about the secret. But since
  such a leak is (nearly) a one-to-one function of the secret input, "equal
  leaks imply equal timing" relates very few pairs of inputs: these theorems
  guarantee much less than "independent of the secret", and what the leak
  reveals is an argument about SHAKE, outside the proofs.

### What is not verified

The public APIs are Rust around the verified functions, and that Rust is
tested, not proven. Most of it only lays out buffers and selects an
implementation, but in some algorithms it does part of the cryptography:

* **AES-GCM**: only the key expansion, the CTR32 keystream over whole blocks
  and GHASH over whole blocks are verified. The mode around them is Rust
  (`src/aes_gcm.rs`): the pre-counter block `J0`, the final partial block,
  the zero padding and the length block, the length limits, and the
  comparison of the tag (a constant-time OR of byte differences, not a
  verified primitive). ChaCha20-Poly1305 and ML-KEM, in contrast, are
  verified end to end.
* **ML-DSA**: the verified functions take the message representative `μ`.
  Binding it to the public key, the context string and the message
  (`μ = H(tr ‖ M′)`, with `M′ = 0 ‖ |ctx| ‖ ctx ‖ M` and `tr = H(pk)`: FIPS
  204's `formatMessage`, `messageRep` and `pkTr`) is Rust
  (`src/mldsa_common.rs`) over the verified SHAKE256.
* **ChaCha20-Poly1305 decryption** is in place, and when the tag is wrong
  the verified function's contract leaves the data unspecified (it may
  already hold the decryption); it is the Rust wrapper that then zeroes it,
  so that no unauthenticated plaintext is released.
* **HMAC** with a key longer than a block hashes it first, in Rust (with the
  verified hash).

## Development

```sh
git clone https://github.com/C2SP/wycheproof
WYCHEPROOF_ROOT=$PWD/wycheproof cargo test   # without it, the Wycheproof tests are skipped

cd lean
lake exe cache get                   # prebuilt Mathlib
lake build                           # check all proofs
lake env lean --run Emit.lean        # regenerate src/asm/ after changing lean/VerifiedGarbage/Artifacts/
```

To benchmark against OpenSSL (through rust-openssl; needs its headers), and
to compare a branch with a checkout of `main`, as CI does for every pull
request that changes the library:

```sh
(cd bench && cargo bench)
python3 ci/bench_compare.py path/to/main-checkout .
```

CI checks every proof, that `src/asm/` is exactly what Lean generates, and the
import discipline of the Lean directories (`ci/check_lean_imports.py`); it
builds and runs the Rust tests natively on each target architecture, and
requires 100% line coverage of the Rust code, merged across all of them.

## Credits

This project is inspired by:

- [Graviola](https://github.com/ctz/graviola/)
- [s2n-bignum](https://github.com/awslabs/s2n-bignum)
- [Bobby Powers](https://bpowers.net/)
- [HACS Workshop](https://www.hacs-workshop.org)
