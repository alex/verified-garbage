import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitBlock
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearMemory

/-! # Matrix cells and the memory preserved by initialization calls -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

theorem clearMem_block (m : Mem) (p : Addr) (blocks k : Nat)
    (bound : 1024 * blocks < 2 ^ 64) (hk : k < blocks) :
    blockAt (clearMem m p (128 * blocks)) (p + BitVec.ofNat 64 (1024 * k)) = zeroBlock := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, zeroBlock, Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 1024 * k + 8 * j = 8 * (128 * k + j) by omega]
  exact clearMem_word m p (128 * blocks) (128 * k + j) (by omega) (by omega)

theorem blockAt_frame {m m' : Mem} {rs : List Region} (frame : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  rw [← Proof.Argon2.parseBlock_bytesAt, ← Proof.Argon2.parseBlock_bytesAt]
  apply congrArg parseBlock
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  exact frame.bytes (R := ⟨p, 1024⟩) sep (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi

theorem BlockDone.h0 {s t : State} {column : Nat} (h : BlockDone s t column)
    (ready : BlockReady s) : bytesAt t.mem (s.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .x19, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ready.frameOutput.sub_left (Region.sub_prefix (by decide))
  · exact ready.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact ready.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem BlockDone.block {s t : State} {column : Nat} (h : BlockDone s t column) :
    blockAt t.mem (s.gpr .x22) = parseBlock
      (Proof.Argon2.initialBytes (bytesAt s.mem (s.gpr .x19) 64) (s.gpr .x20).toNat column) :=
  Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ h.digest

end VG.Proof.Argon2.AArch64.MemoryInit
