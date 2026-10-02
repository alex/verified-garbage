import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (toNat_sub_n)

theorem phaseAdvance_ok {σ s : State} {n : Nat} (hn : n < 6) (h : Phase σ n 2 s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.advance) s (Phase σ (n+1) 0) := by
  refine WP.mono (advance_ok s) fun t ⟨ht,hptr,hct⟩ => ?_
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp) ht.rd ht.wr ht.sp
    (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),
    (ht.get .x22).trans h.x22,(ht.get .x23).trans h.x23,fun k hk => ?_,?_,fun p hp => ?_,fun k hk j hj => ?_⟩
  · rw [hptr k hk,h.ptrs k hk]
    unfold bufAt at'
    rw [show (168 : BitVec 64) = BitVec.ofNat 64 168 from rfl,Offset.add_add]
    exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by omega)
  · rw [hct,toNat_sub_n (by rw [h.count]; change 1 ≤ 6-n; omega),h.count]
    change 6-n-1 = 6-(n+1)
    omega
  · rw [ht.mem]
    have hs := h.states p hp
    simpa only [ite_eq_left hp,ite_eq_right (Nat.not_lt_zero _)] using hs
  · rw [ht.mem]
    apply h.out k hk j
    simpa only [Nat.mul_zero,ite_eq_left hk,ite_eq_right (Nat.not_lt_zero _)] using hj
end VG.Proof.MlDsa.AArch64.Sample.Rej4
