import VerifiedGarbage.Impl.Aes.AArch64.Ctr32
import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
import VerifiedGarbage.Impl.Aes.AArch64.Aese

/-!
# The implementations of `vg_aes_ctr32` on AArch64

A function that calls `vg_aes_ctr32` (AES-CMAC's) takes the implementation it
calls, a `Ctr32`, and is emitted once for each (`Generic/AesCtr32/AArch64/`).
One that also expands the key (streaming AES-CMAC's `init`) calls the
implementation of `vg_aes_expand_key` that goes with it, an `ExpandKey`.
-/

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- An implementation of `vg_aes_ctr32` to call: its symbol and its code. -/
structure Ctr32 where
  name : String
  code : Prog isa

def Ctr32.scalar : Ctr32 := ⟨"vg_aes_ctr32", ctr32⟩
def Ctr32.aese : Ctr32 := ⟨"vg_aes_ctr32_aes", Aese.ctr32⟩

/-- An implementation of `vg_aes_expand_key` to call: its symbol and its code. -/
structure ExpandKey where
  name : String
  code : Prog isa

def ExpandKey.scalar : ExpandKey := ⟨"vg_aes_expand_key", expandKey⟩
def ExpandKey.aese : ExpandKey := ⟨"vg_aes_expand_key_aes", Aese.expandKey⟩

end VG.Impl.Aes.AArch64
