import VerifiedGarbage.Proof.X448.X86.Save

/-!
# X448 on x86 (32-bit): restoring the callee-saved registers

The address is retained in eax so edi can be restored after the other saved
registers.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def restoreRegs : List Reg := [.eax, .ebx, .esi, .ebp, .edi]

theorem restore_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 32}
    (hsv : Saved base g s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ p ∈ savedSlots, t.gpr p.1 = g p.1) ∧ t.mem = s.mem ∧ Keeps restoreRegs s t := by
  rw [show restore = .mov .eax (.reg .edi) ::
    (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) from rfl]
  refine wp_mov rfl fun t ht => ?_
  have hb : (t.gpr .eax).setWidth 64 = base := by rw [ht.gpr]; exact hs.edi
  refine Spill.restore_ofNat_ok _ (n := 16) (by decide) (by rw [ht.gpr]; have := hs.nowrap; omega)
    (by decide) (fun p h => by
      rw [hb, ht.rd, ht.wr]; exact hs.read (by have := savedSlots_bound p (by revert p h; decide); omega))
    (by rw [hb, ht.mem]; exact hsv.sub (by decide)) fun u hu => WP.block_nil ⟨fun p h => hu.gpr p (by
      revert p h; decide), by rw [hu.mem, ht.mem], fun r hr => ?_, by rw [hu.rd, ht.rd], by rw [hu.wr, ht.wr]⟩
  simp only [restoreRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [hu.other r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), ht.other r hr.1]

end VG.Proof.X448.X86
