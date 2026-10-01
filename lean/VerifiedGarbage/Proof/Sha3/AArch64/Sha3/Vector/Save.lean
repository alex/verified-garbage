import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

structure SaveInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  ptr : Ptrs s₀ s
  vec : s.v = s₀.v
  frame : Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s.mem
  vals : ∀ i < k, s.mem.read (s₀.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 = s₀.v (vreg (8+i))

theorem save_ok (s₀ : VG.AArch64.State) (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s' =>
      Ptrs s₀ s' ∧ s'.v = s₀.v ∧ Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s'.mem ∧ Saved s₀ s'.mem := by
  have hh : WP isa (.block save) s₀ (SaveInv s₀ 8) := by
    refine wp_range_flatMap (M := isa) (SaveInv s₀) (fun i s hi hs => ?_)
      8 (Nat.le_refl _) s₀ ⟨Ptrs.refl _,rfl,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
    unfold saveReg
    refine WP.cons (exec_strq ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hs.ptr.wr,hs.ptr.x1]
      exact hp.in_wr (.inr rfl) (scratch_contains s₀ hi)
    · refine ⟨⟨hs.ptr.x0,hs.ptr.x1,hs.ptr.rd,hs.ptr.wr,hs.ptr.sp⟩,hs.vec,?_,fun j hj => ?_⟩
      · change Frame _ _ (s.mem.write _ 16 _)
        rw [hs.ptr.x1]
        exact hs.frame.write (by simp) _ (scratch_contains s₀ hi)
      · change (s.mem.write _ 16 _).read _ 16 = _
        rw [hs.ptr.x1,hs.vec]
        by_cases he : j = i
        · subst j
          exact read_write16 _ _ _
        · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
          exact hs.vals j (by omega)
  exact hh.mono fun s' h => ⟨h.ptr,h.vec,h.frame,h.vals⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector
