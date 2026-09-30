import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem canonicalY_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hy : fe s.mem x 96 < 2 ^ 255) :
    WP isa (.block canonicalY) s fun t => FieldKeep x s t ∧
      env t.mem x = env s.mem x ∧ wd t.mem x 32 = wd s.mem x 32 ∧
      t.zf = some (decide (fe s.mem x 96 < Spec.X25519.P)) := by
  rw [canonicalY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setAcc_ok (s := s) 19) fun a ⟨ka, ma, aa⟩ => ?_
  rw [WP.block_append_iff]
  have ca := ka.ctx hc
  refine WP.mono (cols_ok ca (fun k => [.addM (96 + 4 * k)]) 8 (by decide)
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [aa]; decide)) fun b ⟨kb, fb, vb, _⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hk], .inl (by simp only [T]; omega_using [hk])⟩
  · rw [colv_addM]; have := wv_lt a.mem x (96 + 4 * k); omega_using [this]
  have nn : num (fun k => colv a.mem x [.addM (96 + 4 * k)]) 8 = fe s.mem x 96 := by
    rw [ma]; exact num_congr fun k _ => colv_addM _ _ _
  rw [nn, aa, show (19 : BitVec 32).toNat = 19 from rfl] at vb
  have vsum : fe b.mem x T = fe s.mem x 96 + 19 := by
    change fe b.mem x T + (2 ^ 32) ^ 8 * acc b = _ at vb
    have hb : acc b = 0 := by
      rcases Nat.eq_zero_or_pos (acc b) with h | h
      · exact h
      · have hh := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h
        omega_using [hy, vb, hh]
    rw [hb, Nat.mul_zero, Nat.add_zero] at vb
    omega_using [vb]
  have cb := kb.ctx ca
  refine Wp.wp_ldm cb.edi (cb.inRW (by decide) (by decide)) fun c hcl => ?_
  refine Wp.wp_shr (by decide) fun d hd _ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have kt : Keep b t := (updKeep hcl).trans ((updKeep hd).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩)
  have mt : t.mem = b.mem := by rw [ht.mem, hd.mem, hcl.mem]
  have ff : Frame [sub x T 32] s.mem t.mem := by rw [mt]; rw [ma] at fb; exact fb
  have envt : env t.mem x = env s.mem x := by
    funext i
    apply congrArg VG.Proof.X25519.toFe
    have ii := i.isLt
    exact fe_frame1 ff hc.fit (by decide) (by simp only [offset]; omega_using [ii])
      (Or.inl (by simp only [offset, T]; omega_using [ii]))
  refine ⟨⟨ka.trans (kb.trans kt), frameWiden ff hc.fit (by decide) (by decide) (by decide)⟩,
    envt, wd_frame1 ff hc.fit (by decide) (by decide) (Or.inl (by decide)), ?_⟩
  have top := (fold_top (f := fun k => wv b.mem x (T + 4 * k)) fun _ _ => wv_lt _ _ _).2
  change fe b.mem x T / 2 ^ 255 = wv b.mem x (T + 28) / 2 ^ 31 at top
  rw [vsum] at top
  have flag : (d.gpr .eax).toNat = (fe s.mem x 96 + 19) / 2 ^ 255 := by
    rw [hd.gpr, shr31_toNat, hcl.gpr]
    exact top.symm
  rw [zt, BitVec.and_self]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  change (d.gpr .eax == 0) = true ↔ decide (fe s.mem x 96 < Spec.X25519.P) = true
  rw [beq_iff_eq, decide_eq_true_eq]
  have hz : d.gpr .eax = 0 ↔ (d.gpr .eax).toNat = 0 :=
    ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  rw [hz, flag]
  simp only [Spec.X25519.P]
  omega_using [hy]

end VG.Proof.Ed25519.X86
