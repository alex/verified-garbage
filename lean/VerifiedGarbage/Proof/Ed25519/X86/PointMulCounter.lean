import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Ed25519.X86.PointMulFrame

/-! Public batch countdown, leaving all coordinate values unchanged. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem counter28_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (h : Frame [sub x 28 4] m m') : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h hx (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

theorem batchBegin_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (n : Nat)
    (hb : wd s.mem x 28 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block batchBegin) s fun t => BatchKeep x s t ∧
      t.gpr .esi = BitVec.ofNat 32 n ∧ wd t.mem x 28 = BitVec.ofNat 32 n ∧
      Frame [sub x 28 4] s.mem t.mem := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  refine Wp.wp_subi fun v hv _ _ => ?_
  have bv : v.gpr .esi = BitVec.ofNat 32 n := by
    rw [hv.gpr, hu.gpr]
    change wd s.mem x 28 - 1 = _
    rw [hb, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have cv := ((IKeep.of_counter hu).trans (IKeep.of_counter hv)).ctx hc
  refine Wp.wp_stm cv.edi (cv.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have mt : t.mem = s.mem.writeW (addr x 28) (BitVec.ofNat 32 n) := by rw [ht.mem, hv.mem, hu.mem, bv]
  have ft : Frame [sub x 28 4] s.mem t.mem := by
    rw [mt]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨BatchKeep.of_counter hc ?_ ?_ ?_ ?_ ft, ?_, ?_, ft⟩
  · rw [ht.gpr, hv.other .edi (by decide), hu.other .edi (by decide)]
  · rw [ht.gpr, hv.other .esp (by decide), hu.other .esp (by decide)]
  · rw [ht.rd, hv.rd, hu.rd]
  · rw [ht.wr, hv.wr, hu.wr]
  · rw [ht.gpr]; exact bv
  · rw [mt, wd_write_self]

theorem batchTest_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (n : Nat) (hn : n < 32)
    (hb : wd s.mem x 28 = BitVec.ofNat 32 n) :
    WP isa (.block batchTest) s fun t => IKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some (!decide (n = 0)) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨(IKeep.of_counter hu).trans ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩, by rw [ht.mem, hu.mem], ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hu.gpr]
  change some (!(wd s.mem x 28 == 0)) = _
  rw [hb, Wp.ofNat_beq_zero (by omega)]

theorem mulCounterInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      Keep s t ∧ Frame [sub x 28 4] s.mem t.mem ∧ wd t.mem x 28 = BitVec.ofNat 32 count := by
  refine Wp.wp_movi fun u hu => ?_
  have cu := (updKeep hu).ctx hc
  refine Wp.wp_stm cu.edi (cu.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨(updKeep hu).trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_, ?_⟩
  · rw [ht.mem, hu.mem]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, wd_write_self, hu.gpr]

end VG.Proof.Ed25519.X86
