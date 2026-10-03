import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
The comb's 32 constant-time table selections as literals (`materialize_table`):
the literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read them rather than build the selections
from the tables again.
-/

namespace VG

materialize_table Impl.Ed25519.X86_64.combSelect 32

end VG
