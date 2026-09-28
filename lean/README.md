# Lean: specifications, implementations and proofs

The cryptographic primitives (e.g. a block function or a field
multiplication) are assembly written in Lean as structured programs over a
Lean model of each ISA, proven correct in Lean, and printed into `src/asm/`
as Rust naked functions. The crate's public APIs are Rust that composes those
primitives: this directory verifies the primitives, not the Rust around them.

## Layout

```
VerifiedGarbage/
  TCB/          Trusted computing base: definitions only, Lean core only
    Mem.lean        byte-addressed memory, regions
    Code.lean       structured programs, calls and stack frames, big-step semantics
                    with leakage, constant time
    Print.lean      lowering of structured control flow to labels and branches, of
                    calls to call instructions, and of frames to push and pop
    Sig.lean        Rust signatures and calling conventions (`Abi`)
    Artifact.lean   Target, Contract, `Verified`, `Artifact`: what "verified" means;
                    `Sig.contract`: the contract obligations a signature implies
    Rust.lean       rendering artifacts as Rust naked functions; checks that every
                    call is of the artifact whose code the model runs for it, and
                    that each artifact declares the CPU features its code needs
    Axioms.lean     `#assert_standard_axioms`
    Emit.lean       what is emitted (`Artifacts.lean` and every registration file
                    under `Artifacts/`), and writing or checking `src/asm/`
    X86_64/         ISA model, printer, System V ABI target
  Spec/         Algorithm specifications and contracts (trusted, must be reviewed)
  Impl/         Implementations: `Prog`s over an ISA model (untrusted)
  Proof/        Proofs and intermediate proof artifacts (untrusted)
    Framework/      generic lemmas: determinism, WP rules, memory frames, inlining
                    verified code, and a taint-tracking checker that proves
                    constant time by evaluation
  Artifacts/      The registry: one registration file per algorithm and target,
                  each listing the artifacts it emits
  Artifacts.lean  An empty list, which the emitter still reads; add nothing to it
VerifiedGarbageTest/  Golden tests for the (unverified) printers and calling conventions
Emit.lean       Renders every artifact into `../src/asm/` (see `TCB/Emit.lean`)
```

`ci/check_lean_imports.py` enforces the import discipline between these
directories: `TCB/` imports only Lean core and itself; `Spec/` and `Impl/`
never import proofs.

## The pipeline

1. **Spec** — `Spec/<Alg>.lean` defines the algorithm as a readable Lean
   function transcribed from the standard, and `Spec/<Alg>/Contract.lean`
   each function's Rust signature (`Sig`) and its `Contract`, for every
   target at once: `Sig.contract` derives from the signature and the
   target's calling convention where the arguments are, the permitted memory
   regions, disjointness and which arguments are public, and the contract
   adds a postcondition (in terms of the spec) and any further precondition.
   Each function's `Api` gives its Rust module, name and signature, and its
   documentation, but for what the emitter derives from the signature.
2. **Impl** — `Impl/<Alg>/<Target>.lean` defines the code as a `Prog`.
3. **Proof** — `Proof/<Alg>/…` proves `Verified target code contract`:
   termination without faults (hence memory safety), the postcondition,
   the ABI obligations (callee-saved registers etc.), constant time (up to
   anything the contract declares the function may leak), and
   satisfiability of the precondition.
4. **Registry** — the registration files `Artifacts/<Alg>/<Target>.lean`
   list every `Artifact`, bundling target, Rust name and signature, code,
   contract and proof: mostly a function's `Api`, with the stack its contract
   gives its calls (`stack`) and any notes on the implementation. An
   `Artifact` cannot be built
   without the proof, and the emitter's `#assert_standard_axioms` rejects
   `sorry`, `native_decide` and any non-standard axiom anywhere in them.
5. **Emit** — `Emit.lean` renders the registry into `src/asm/<target>/<module>.rs`,
   adding to each function's `# Safety` section what its contract requires of
   where its buffers are, which depends on the target's calling convention
   and the stack it uses (`Sig.layoutDoc`, from the same signature, `stack`
   and `writeArgs` as the contract, as `Artifact.ofSig` proves).
   CI fails if the checked-in files differ from what Lean generates, so the
   Rust crate contains exactly the verified code.

A function can call another (`Code.call name body`): the model runs the
callee's code `body` between the call and return instructions, so the
caller's proof covers it, and the emitter only emits the call if `name` is
the artifact whose code is `body`. A caller's proof can use the callee's
`Verified` proof rather than go through its code again.

Code saves registers on the stack, or passes arguments on the stack, in a
stack frame (`Code.frame push body pop`): the push moves the stack pointer
down, stores registers and makes those bytes a writable region; the pop
faults unless the stack pointer and regions are as the push left them, loads
one register and removes the region. Frames are nested by construction, so
the stack pointer is always back where it was, and the stack a function's
calls and frames use is part of its contract (`Sig.contract`'s `stack`).

Instructions outside a target's baseline ISA (e.g. SHA-NI) name the CPU
features they need (`ISA.requires`, transcribed from the vendor manual). An
artifact using them declares those features (`Artifact.features`), the
emitter checks the declaration is exact, and the generated function's
`# Safety` section makes their presence the caller's obligation. The Rust
that calls it checks for them first, using the generated `<NAME>_FEATURES`
constant.

## What you need to trust

* `TCB/` — in particular the ISA models, which must match the vendor manuals
  (including the CPU features each instruction requires), and the printers,
  which must print what the models mean.
* For each artifact: its contract in `Spec/` (and the algorithm spec it
  refers to), its `sig` and `doc` (its `Api` in `Spec/`, and any notes its
  registration file adds), and `TCB/Emit.lean`, which decides what is emitted.
* Lean's kernel, and the assembler in `rustc`/LLVM.

Everything in `Impl/` and `Proof/` is checked by Lean and need not be read.

To keep review of the trusted parts focused, new specs, additions to the TCB,
and new implementations are never combined in one PR: an implementation is
only proven against a spec and TCB that were reviewed and merged beforehand.

## Building

```sh
lake exe cache get                  # download prebuilt Mathlib
lake build                          # check every proof, run the axiom audit and golden tests
lake env lean --run Emit.lean       # regenerate ../src/asm
lake env lean --run Emit.lean --check
```
