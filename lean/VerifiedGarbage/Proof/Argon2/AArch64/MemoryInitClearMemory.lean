import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy

/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

def clearMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | n + 1 => (clearMem m p n).writeW (p + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)

theorem clearMem_frame (m : Mem) (p : Addr) (n : Nat) (bound : 8 * n < 2 ^ 64) :
    Frame [⟨p, 8 * n⟩] m (clearMem m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    have smaller : Frame [⟨p, 8 * (n + 1)⟩] m (clearMem m p n) :=
      (ih (by omega)).sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
    exact smaller.writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains_base _ (by omega) (by omega))

theorem clearMem_word (m : Mem) (p : Addr) (n j : Nat)
    (bound : 8 * n < 2 ^ 64) (hj : j < n) :
    (clearMem m p n).readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [clearMem]
    by_cases eq : j = n
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact ih (by omega) (by omega)
      · exact Offset.sep p (by omega) (by omega) (by omega)

end VG.Proof.Argon2.AArch64.MemoryInit
