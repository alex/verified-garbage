# Verified Garbage

Verified Garbage is an experimental cryptography library, implemented entirely by LLMs. All of the cryptography primitives are formally verified using Lean.

Its aims are, in order:

1. Security
2. Correctness
3. Performance

The library is implemented in Lean, assembly, and Rust.

It targets: x86 (i686 with SSE2), x86-64, ARMv7, ARM64, and PPC64le.

## Algorithms

| Algorithm | Spec landed | Supported | Optimized |
|---|---|---|---|
| SHA-256 | ✅ | ✅ | x86-64 (SHA extensions) |
| SHA-384, SHA-512, SHA-512/224, SHA-512/256 | ✅ | x86-64, ARM64, ARMv7 | ❌ |
| HMAC-SHA-256 | ✅ | ✅ | x86-64 (SHA extensions) |
| PBKDF2-HMAC-SHA-256 | ✅ | x86-64, ARM64 | ❌ |
| ChaCha20 | ✅ | x86-64, ARM64, ARMv7 | ❌ |
| Poly1305 | ✅ | x86-64 | ❌ |
| ChaCha20-Poly1305 | ✅ | ❌ | ❌ |
| SHA-1 | ✅ | x86-64, ARM64 | ❌ |
| MD5 | ✅ | x86-64, ARM64 | ❌ |
| SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, SHAKE256 | ✅ | x86-64, ARM64 | ❌ |
| AES-GCM (128-, 192- and 256-bit keys) | ✅ | ❌ | ❌ |
| scrypt | ✅ | x86-64 | ❌ |

* **Spec landed**: the algorithm's specification, transcribed from its
  standard, is in `lean/VerifiedGarbage/Spec/`.
* **Supported**: verified assembly and a public Rust API exist on these
  architectures (✅: x86, x86-64, ARMv7 and ARM64; PPC64le is not started
  yet).
* **Optimized**: the implementations have been tuned for performance (e.g.
  with SHA-NI or NEON) on these architectures. Where that needs CPU features
  beyond the architecture's baseline, the features are detected at run time,
  and CPUs without them run the straightforward scalar code that every
  other implementation is.

Our goal is to implement all the cryptographic algorithms that are used by the Python pyca/cryptography library.

## How it works

* Each primitive is written in assembly, as a program over a Lean model of the
  target ISA, and proven in Lean to be correct against a specification, memory
  safe, and constant time (scrypt's ROMix is the exception its standard
  makes: it reads memory at indices derived from the password, and its
  contract declares that it leaks them and nothing else secret). See [`lean/README.md`](lean/README.md) for the
  layout, the pipeline, and exactly what has to be trusted.
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
lake env lean --run Emit.lean        # regenerate src/asm/ after changing Artifacts.lean
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
