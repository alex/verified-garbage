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
* **One kind of change per PR.** New specs (`Spec/`), additions to the TCB
  (`TCB/`), and new implementations (`Impl/` + `Proof/` + the `Artifacts.lean`
  entry) must never be in the same PR. Trusted changes get reviewed on their
  own, and an implementation is only ever proven against a spec and TCB that
  have already been reviewed and merged.
* **100% test coverage.** CI merges the line coverage of the Rust code
  (`src/` and `tests/`) from every platform and fails below 100%. Add tests
  or delete dead code; only exclude lines that genuinely cannot run, between
  `// NO-COVERAGE-START` and `// NO-COVERAGE-END`, with a comment saying why.
* **Known-answer tests need clear provenance.** Never type test vectors into
  a test. Use Wycheproof (`tests/wycheproof/`), or vendor the published
  files byte for byte into a directory under `vectors/`, with a `[[source]]`
  for that directory in `vectors/sources.toml` saying where they came from
  (`ci/check_vectors.py` checks it), and read them from there.
* Never add instructions with operand-dependent timing (e.g. `div`) to an ISA
  model.
* `TCB/` holds definitions only and imports only Lean core; lemmas go in
  `Proof/`. `Spec/` and `Impl/` never import `Proof/`.

## Adding a primitive

This takes at least two PRs (see "One kind of change per PR"): step 1 alone,
then steps 2–5 together. Any TCB additions the primitive needs (e.g. new
instructions in an ISA model) go in their own PR before either.

1. `Spec/<Alg>.lean`: the algorithm, transcribed from the standard, with no
   target-specific imports; and `Spec/<Alg>/<Target>.lean`: its `Contract` on
   each target. Choose `pub` honestly: only lengths and pointers are public
   unless the algorithm says otherwise.
2. `Impl/<Alg>/<Target>.lean`: the code.
3. `Proof/<Alg>/…`: the proof of `Verified`.
4. An `Artifact` in `Artifacts.lean` (its `module` names the file under
   `src/asm/<target>/`), whose `rustSig` and `doc` match the
   contract (the doc must state every caller obligation).
5. Regenerate `src/asm/`, build the public Rust API on top of the primitive,
   and test it against the Wycheproof vectors in `tests/wycheproof/` (set
   `WYCHEPROOF_ROOT` to a checkout of C2SP/wycheproof).

## Keeping proofs fast

Lean's kernel re-checks every proof term, and it is a slow evaluator: most
of the build time used to be the kernel, not tactics. Avoid these patterns
(each has cost tens of seconds in one proof):

* **Constant time:** use `VG.Taint.constantTime … (by taint_decide)`, never
  `decide +kernel` on a taint check: `taint_decide` precomputes loop
  invariants so the kernel does not search for them.
* **Symbolic execution:** step blocks with the ISA's `runBlock_cons`,
  `runStep_some` and `runBlock_nil` (`Proof/Framework/<ISA>/Exec.lean`), never
  `simp [runBlock]`, which runs the rest of the block from an unknown state
  after every instruction.
* **One symbolic execution per code shape:** don't case-split (e.g.
  `interval_cases` on a register rotation) and run the same block once per
  case; generalize what differs (see `round_ok` and `round_nodup`).
* **Properties of every instruction:** prove `(instrs c).all p` with
  `rw [← Code.allInstrs_eq]; decide +kernel`, not `decide +kernel` directly.
* **Failing unfolding:** `rfl`, `trivial`, `congr 1`, `exact` and `simpa` on
  goals about symbolic memory or hash values can unfold definitions (down
  to `BitVec` internals) for seconds before failing or succeeding. Close
  such goals with explicit lemmas (`congrArg`, `rw`), and try the tactic
  that works first rather than in `first | rfl | …`.

To find what is slow, profile one file per declaration (time under
`[Kernel]` is the kernel checking the term):

```sh
lake env lean -DElab.async=false -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 \
  VerifiedGarbage/Proof/….lean
```

## Checks to run before pushing

```sh
(cd lean && lake build && lake env lean --run Emit.lean --check)
python3 ci/check_lean_imports.py
python3 ci/check_vectors.py
cargo fmt --check && cargo clippy --all-targets -- -D warnings
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test
```

Coverage on this platform (CI merges it across all of them; the merge needs
`pip install -r ci/requirements-coverage.txt`):

```sh
export RUSTFLAGS=-Cinstrument-coverage LLVM_PROFILE_FILE='.rust-cov/cov-%p-%m.profraw'
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test
python3 ci/export_rust_coverage.py .rust-cov   # writes <uuid>.lcov
python3 ci/merge_rust_coverage.py .            # reports; fails under 100%
```
