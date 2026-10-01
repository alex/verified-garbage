import VerifiedGarbage.Proof.Ed25519.X86.CanonicalY
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign
import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame

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
