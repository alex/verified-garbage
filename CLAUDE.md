# Guidance for agents working on this repository

This library is written entirely by LLMs, so these rules are what keep it
trustworthy. Read `lean/README.md` first.

## Hard rules

* **All assembly comes from Lean.** Never write `asm!`, `naked_asm!`,
  `global_asm!`, naked functions, `extern` blocks or a `build.rs` by hand, and
  never edit `src/asm/` by hand. Add an entry to
  `lean/VerifiedGarbage/Artifacts.lean` and run `lake env lean --run Emit.lean`
  in `lean/`.
* **No unverified shortcuts in proofs.** No `sorry`, `admit`, `native_decide`,
  `bv_decide` or new `axiom`s in anything `Artifacts.lean` depends on.
  `lake build` enforces this (warnings are errors, and
  `#assert_standard_axioms` audits the registry); never work around it.
* **Changes to `lean/VerifiedGarbage/TCB/` or `Spec/` are trust changes.**
  Keep them minimal, call them out explicitly in the PR description, and
  justify each ISA semantics change by citing the vendor manual (e.g. Intel SDM
  pseudocode). Never weaken a model, contract or `Verified` to make a proof go
  through: fix the proof or the code.
* Never add instructions with operand-dependent timing (e.g. `div`) to an ISA
  model.
* `TCB/` holds definitions only and imports only Lean core; lemmas go in
  `Proof/`. `Spec/` and `Impl/` never import `Proof/`.

## Adding a primitive

1. `Spec/<Alg>.lean`: the algorithm, transcribed from the standard, plus a
   `Contract` per target. Choose `pub` honestly: only lengths and pointers are
   public unless the algorithm says otherwise.
2. `Impl/<Alg>/<Target>.lean`: the code.
3. `Proof/<Alg>/…`: the proof of `Verified`.
4. An `Artifact` in `Artifacts.lean`, whose `rustSig` and `doc` match the
   contract (the doc must state every caller obligation).
5. Regenerate `src/asm/`, write a safe Rust API around it, and run it against
   the Wycheproof vectors in `tests/wycheproof/`.

## Checks to run before pushing

```sh
(cd lean && lake build && lake env lean --run Emit.lean --check)
python3 ci/check_structure.py
cargo fmt --check && cargo clippy --all-targets -- -D warnings && cargo test
```
