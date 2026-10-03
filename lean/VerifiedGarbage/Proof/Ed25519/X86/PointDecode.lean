import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame
import VerifiedGarbage.Proof.Ed25519.X86.RecoverPoint

/-! Merged from `Proof.Ed25519.X86.DecodeY`. -/
section
/-! Merged from `Proof.Ed25519.X86.CanonicalY`. -/
section
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
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem decodeY_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block decodeY) s fun t => MulKeep x s t ∧
      fe t.mem x 96 = fe s.mem x 96 % 2 ^ 255 ∧
      wd t.mem x 32 = BitVec.ofNat 32 (fe s.mem x 96 / 2 ^ 255) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_shr (by decide) fun b hb _ => ?_
  have kb : IKeep x s b := (IKeep.of_counter ha).trans (IKeep.of_counter hb)
  have cb := kb.ctx hc
  refine Wp.wp_stm cb.edi (cb.inW (by decide) (by decide)) fun c hcw => ?_
  have kc : ScalarKeep s c := ⟨by rw [hcw.gpr, kb.edi], by rw [hcw.gpr, kb.esp], hcw.rd.trans kb.rd, hcw.wr.trans kb.wr⟩
  have cc := kc.ctx hc
  have mc : c.mem = s.mem.writeW (addr x 32) (b.gpr .esi) := by rw [hcw.mem, hb.mem, ha.mem]
  have fc : Frame [sub x 32 4] s.mem c.mem := by
    rw [mc]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine Wp.wp_ldm cc.edi (cc.inRW (by decide) (by decide)) fun d hd => ?_
  refine Wp.wp_andi fun e he => ?_
  have ce := ((updKeep hd).trans (updKeep he)).ctx cc
  refine Wp.wp_stm ce.edi (ce.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have kt : Keep c t := ((updKeep hd).trans (updKeep he)).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩
  have mt : t.mem = c.mem.writeW (addr x 124) (e.gpr .eax) := by rw [ht.mem, he.mem, hd.mem]
  have ft : Frame [sub x 124 4] c.mem t.mem := by
    rw [mt]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  have top : wd c.mem x 124 = wd s.mem x 124 := wd_frame1 fc hc.fit (by decide) (by decide) (Or.inr (by decide))
  have ev : (e.gpr .eax).toNat = wv s.mem x 124 % 2 ^ 31 := by
    rw [he.gpr, hd.gpr, low31_toNat]
    change wv c.mem x 124 % 2 ^ 31 = _
    rw [wv, top]
  have sv : b.gpr .esi = BitVec.ofNat 32 (fe s.mem x 96 / 2 ^ 255) := by
    apply BitVec.eq_of_toNat_eq
    rw [hb.gpr, shr31_toNat, ha.gpr, BitVec.toNat_ofNat]
    have hh := (fold_top (f := fun k => wv s.mem x (96 + 4 * k)) fun _ _ => wv_lt _ _ _).2
    change fe s.mem x 96 / 2 ^ 255 = wv s.mem x 124 / 2 ^ 31 at hh
    rw [hh]
    exact (Nat.mod_eq_of_lt (by have hw := wv_lt s.mem x 124; omega_using [hw])).symm
  refine ⟨⟨kt.edi.trans kc.edi, kt.esp.trans kc.esp, kt.rd.trans kc.rd, kt.wr.trans kc.wr,
    (frameWiden fc hc.fit (by decide) (by decide) (by decide)).trans
      (frameWiden ft hc.fit (by decide) (by decide) (by decide))⟩, ?_, ?_⟩
  · rw [mt, fe_last_write _ _ hc.fit, ev]
    have nl : num (fun j => wv c.mem x (96 + 4 * j)) 7 = num (fun j => wv s.mem x (96 + 4 * j)) 7 :=
      num_congr fun j hj => congrArg BitVec.toNat
        (wd_frame1 fc hc.fit (by decide) (by omega_using [hj]) (Or.inr (by omega_using [hj])))
    rw [nl]
    exact (fold_top (f := fun k => wv s.mem x (96 + 4 * k)) fun _ _ => wv_lt _ _ _).1.symm
  · rw [wd_frame1 ft hc.fit (by decide) (by decide) (Or.inl (by decide)), mc, wd_write_self, sv]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def decodeNumber (n : Nat) : Option Spec.Ed25519.Point :=
  if h : n % 2 ^ 255 < Spec.X25519.P then
    (Spec.Ed25519.recoverX ⟨n % 2 ^ 255, h⟩ (n / 2 ^ 255 == 1)).map
      (fun x => recoveredPoint x ⟨n % 2 ^ 255, h⟩)
  else none

theorem pointDecode_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointDecode s fun t => MulKeep x s t ∧ DecodeResult x (decodeNumber (fe s.mem x 96)) t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun b ⟨kb, eb, bb, zb⟩ => ?_
  have km := ka.trans (MulKeep.of_ikeep ca (IKeep.of_field kb))
  apply WP.ite (decide (fe s.mem x 96 % 2 ^ 255 < Spec.X25519.P)) (by rw [ya] at zb; exact zb)
  · intro hh
    have hh' := of_decide_eq_true hh
    have ey : env b.mem x 1 = (⟨fe s.mem x 96 % 2 ^ 255, hh'⟩ : Spec.X25519.Fe) := by
      rw [eb]
      change VG.Proof.X25519.toFe (fe a.mem x 96) = _
      rw [ya]
      apply Fin.ext
      exact Nat.mod_eq_of_lt hh'
    have ebits : wd b.mem x 32 = signWord (fe s.mem x 96 / 2 ^ 255 == 1) := by
      rw [bb, ba]
      have hn : fe s.mem x 96 / 2 ^ 255 ≤ 1 := by have := fe_lt s.mem x 96; omega_using [this]
      rcases (by omega_using [hn] : fe s.mem x 96 / 2 ^ 255 = 0 ∨ fe s.mem x 96 / 2 ^ 255 = 1) with h | h <;>
        rw [h] <;> rfl
    refine WP.mono (recoverPoint_ok (km.ctx hc) _ ebits) fun t ⟨kt, tr⟩ => ?_
    refine ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) kt), ?_⟩
    rw [ey] at tr
    simpa only [decodeNumber, dite_eq_left hh'] using tr
  · intro hh
    have hh' := of_decide_eq_false hh
    refine WP.mono (recoverInvalid_ok b x) fun t ⟨kt, tr⟩ => ?_
    exact ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) (IKeep.of_field kt)), by
      simpa only [decodeNumber, dite_eq_right hh'] using tr⟩

end VG.Proof.Ed25519.X86
