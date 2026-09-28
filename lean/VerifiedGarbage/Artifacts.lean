import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Rust

/-!
# The old artifact registry

Every artifact is now listed in the registration file of its algorithm and
target, `Artifacts/<Alg>/<Target>.lean` (see `TCB/Emit.lean`), so that
parallel changes add files rather than all appending to one list. This list
is empty and stays empty: add nothing to it. `TCB/Emit.lean` still emits it
after the registration files, until a change to the TCB drops it.
-/

namespace VG

def artifacts : List Artifact := []

#assert_standard_axioms artifacts

end VG
