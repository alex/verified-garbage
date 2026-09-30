import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.Ed25519.X86.PointPowersFrame

/-! Untrusted: the public checkpoint counter occupies bytes24 through27. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (sc)

theorem word_sub_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  rw [show (0 : BitVec 32) + BitVec.ofNat 32 b = BitVec.ofNat 32 b from BitVec.zero_add _]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using ht
  · exact congrArg (BitVec.ofNat 32)

theorem powersLoad_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block [.mov .esi (.mem (sc 24))]) s fun t =>
      IKeep x s t ∧ t.mem = s.mem ∧ t.gpr .esi = wd s.mem x 24 := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  exact ⟨IKeep.of_counter ht, ht.mem, ht.gpr⟩

theorem powersNext_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (j count o n : Nat)
    (hj : j + 1 < 2 ^ 32) (hcount : count < 2 ^ 32) (hv : wd s.mem x 24 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      PowersKeep x o n s t ∧ wd t.mem x 24 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne t = some (!decide (j + 1 = count)) ∧
      Frame [sub x 24 4] s.mem t.mem := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun t ht => ?_
  refine Wp.wp_addi fun u hu => ?_
  have eu : u.gpr .esi = BitVec.ofNat 32 (j + 1) := by
    rw [hu.gpr, ht.gpr]
    change wd s.mem x 24 + 1 = _
    rw [hv, BitVec.ofNat_add]; rfl
  have cu := (IKeep.of_counter ht).trans (IKeep.of_counter hu) |>.ctx hc
  refine Wp.wp_stm cu.edi (cu.inW (by decide) (by decide)) fun v hv' => ?_
  refine Wp.wp_cmpi fun w hw _ hz => WP.block_nil ?_
  have hm : w.mem = s.mem.writeW (addr x 24) (BitVec.ofNat 32 (j + 1)) := by
    rw [hw.mem, hv'.mem, hu.mem, ht.mem, eu]
  have fr : Frame [sub x 24 4] s.mem w.mem := by
    rw [hm]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨PowersKeep.of_counter o n ?_ ?_ ?_ ?_ fr, ?_, ?_, fr⟩
  · rw [hw.gpr, hv'.gpr, hu.other .edi (by decide), ht.other .edi (by decide)]
  · rw [hw.gpr, hv'.gpr, hu.other .esp (by decide), ht.other .esp (by decide)]
  · rw [hw.rd, hv'.rd, hu.rd, ht.rd]
  · rw [hw.wr, hv'.wr, hu.wr, ht.wr]
  · rw [hm, wd_write_self]
  · show w.zf.map (!·) = _
    rw [hz, hv'.gpr, eu, word_sub_eq hj hcount]; rfl

theorem powersInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o n : Nat) :
    WP isa (.block [.mov .eax (.imm 0), .store (sc 24) .eax]) s fun t =>
      PowersKeep x o n s t ∧ wd t.mem x 24 = 0 ∧ Frame [sub x 24 4] s.mem t.mem := by
  refine Wp.wp_movi fun t ht => ?_
  have ct := (updKeep ht).ctx hc
  refine Wp.wp_stm ct.edi (ct.inW (by decide) (by decide)) fun u hu => WP.block_nil ?_
  have hm : u.mem = s.mem.writeW (addr x 24) (0 : BitVec 32) := by rw [hu.mem, ht.mem, ht.gpr]
  have hf : Frame [sub x 24 4] s.mem u.mem := by
    rw [hm]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨PowersKeep.of_counter o n ?_ ?_ ?_ ?_ hf, ?_, hf⟩
  · rw [hu.gpr, ht.other .edi (by decide)]
  · rw [hu.gpr, ht.other .esp (by decide)]
  · rw [hu.rd, ht.rd]
  · rw [hu.wr, ht.wr]
  · rw [hm, wd_write_self]

theorem counter_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (h : Frame [sub x 24 4] m m') : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h hx (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.X86
