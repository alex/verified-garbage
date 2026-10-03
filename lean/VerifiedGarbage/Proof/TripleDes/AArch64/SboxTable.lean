import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
The code of the eight S-boxes as literals (`materialize_table`): the
literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read it rather than run the register
allocator that writes it again.
-/

namespace VG

materialize_table Impl.TripleDes.AArch64.sboxCode 8

end VG
