# Verified Garbage

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

<td>❌</td>

<td>❌</td>

</tr>

<tr>

<td>BLAKE2s</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>❌</td>

<td>❌</td>

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

<td>✅</td>

<td>✅</td>

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

<td>✅</td>

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

<td>✅</td>

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

<td>✅ NEON polynomial arithmetic</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ML-KEM-768</td>

<td>✅</td>

<td>✅ AVX2; SSE2 polynomial arithmetic</td>

<td>✅ NEON polynomial arithmetic</td>

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

<td>✅ BMI2, ADX</td>

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

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

</tr>

<tr>

<td>ML-DSA-44</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>❌</td>

</tr>

<tr>

<td>ML-DSA-65</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>❌</td>

</tr>

<tr>

<td>ML-DSA-87</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>✅</td>

<td>❌</td>

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
  contract declares that it leaks them and nothing else secret). See [`lean/README.md`](lean/README.md) for the
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
* The public APIs are Rust that composes these verified primitives.
* The public APIs are tested against the [Wycheproof](https://github.com/C2SP/wycheproof)
  test vectors (`tests/wycheproof/`).

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
