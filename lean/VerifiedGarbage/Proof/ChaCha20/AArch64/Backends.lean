import VerifiedGarbage.Proof.ChaCha20.AArch64.Variant
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Block

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

private theorem keeps_of_check {c : Prog isa} {rs : List Reg}
    (h : (c.allInstrs fun i => rs.all fun r => dstOf i != some r) = true) :
    ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  rw [Code.allInstrs_eq] at h
  intro r hr i hi
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using h'

namespace BlockImpl

def scalar : BlockImpl where
  callee := .scalar
  features := []
  ok := block_correct
  noFrames := by lit_decide
  keeps := keeps_of_check (by lit_decide)
  xorKeeps := keeps_of_check (by lit_decide)
  xorNoFrames := by lit_decide
  xorTaint := ⟨_, by taint_decide⟩
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

/-- Four 32-bit NEON lanes, using only baseline AdvSIMD instructions. -/
def neon : BlockImpl where
  callee := ⟨"vg_chacha20_block_neon", Impl.ChaCha20.AArch64.Neon.block, "_neon"⟩
  features := []
  ok := Neon.block_correct
  noFrames := by lit_decide
  keeps := keeps_of_check (by lit_decide)
  xorKeeps := keeps_of_check (by lit_decide)
  xorNoFrames := by lit_decide
  xorTaint := ⟨_, by taint_decide⟩
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

end BlockImpl
end VG.Proof.ChaCha20.AArch64
