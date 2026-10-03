import VerifiedGarbage.Impl.TripleDes.X86.Sbox
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
The code of the eight S-boxes as literals (`materialize_table`): the
literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read it rather than run the register
allocator that writes it again.
-/

namespace VG

materialize_table Impl.TripleDes.X86.sboxCode 8

end VG
