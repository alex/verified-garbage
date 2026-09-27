import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Proof.Selftest.X86_64

/-!
# The artifact registry

**The single entry point.** Every function emitted into the Rust crate is an
entry of `artifacts`, and `Emit.lean` emits exactly this list. An
`Artifact` bundles

* the target and the Rust name and signature of the function,
* the implementation (`Impl/`),
* the contract it satisfies (`Spec/`), and
* the proof of `Verified` for them (`Proof/`),

so nothing can be emitted without a proof. The `#assert_standard_axioms`
check below then ensures none of those proofs relies on `sorry`,
`native_decide` or any axiom beyond Lean's standard three.

To add a function: write its spec and contract under `Spec/`, the code under
`Impl/`, the proof under `Proof/`, and append an entry here. Then run
`lake build && lake env lean --run Emit.lean` (in `lean/`) and commit the
regenerated `src/asm/`.

**Review note**: `rustSig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "selftest"
    name := "vg_selftest_add"
    rustSig := "(a: u64, b: u64) -> u64"
    doc := "Pipeline self-test: returns `a.wrapping_add(b)`.\n\n\
      Contract: `VG.Spec.Selftest.addX86_64`. No safety requirements."
    code := Impl.Selftest.X86_64.add
    contract := Spec.Selftest.addX86_64
    verified := Proof.Selftest.X86_64.add_verified }
]

#assert_standard_axioms artifacts

end VG
