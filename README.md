# Verified Garbage

Verified Garbage is an experimental cryptography library, implemented entirely by LLMs. All of the cryptography primitives are formally verified using Lean.

It's aims are, in order:

1. Security
2. Correctness
3. Performance

The library is implemented in Lean, assembly, and Rust.

It targets: x86, x86-64, ARMv7, ARM64, and PPC64le.

## Algorithms

There will eventually be a table with all the algorithms here.

Our goal is to implement all the cryptographic algorithms that are used by the Python pyca/cryptography library.

## How it works

* Each primitive is written in assembly, as a program over a Lean model of the
  target ISA, and proven in Lean to be correct against a specification, memory
  safe, and constant time. See [`lean/README.md`](lean/README.md) for the
  layout, the pipeline, and exactly what has to be trusted.
* The proven assembly is emitted into [`src/asm/`](src/asm/) as Rust naked
  functions (`naked_asm!`); there is no build script and no separate
  assembler step. The rest of the crate is safe Rust around those functions.
* The public API is tested against the [Wycheproof](https://github.com/C2SP/wycheproof)
  test vectors (`tests/wycheproof/`, vectors in the `vendor/wycheproof`
  submodule).

## Development

```sh
git submodule update --init          # Wycheproof vectors
cargo test

cd lean
lake exe cache get                   # prebuilt Mathlib
lake build                           # check all proofs
lake env lean --run Emit.lean        # regenerate src/asm/ after changing Artifacts.lean
```

CI checks every proof, that `src/asm/` is exactly what Lean generates, that no
assembly exists outside `src/asm/` (`ci/check_structure.py`), and runs the
Rust tests on x86-64 and AArch64.
