import VerifiedGarbage.Proof.Argon2.AArch64.InitialStart
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finalize

/-! # H₀: finalize BLAKE2b and copy the digest into the derivation frame -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

structure Finished (s t : State) : Prop where
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x20 → r ≠ .x22 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x24, 832⟩, below (s.sp) 16, ⟨s.gpr .x19, 64⟩] s.mem t.mem

theorem finishCount_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.mov .x1 .x20].flatten) s fun t =>
      t.gpr .x1 = s.gpr .x20 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  refine (Instructions.mov_ok s .x1 .x20).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r hr _ => keeps.regs r ?_, keeps.rd, keeps.wr, keeps.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem finishOutput_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.mov .x22 .x19,
      Impl.Argon2.AArch64.Instructions.imm .x8 64].flatten) s fun t =>
      t.gpr .x22 = s.gpr .x19 ∧ t.gpr .x8 = 64 ∧ t.mem = s.mem ∧ Keeps s t := by
  rw [List.flatten_cons, List.flatten_cons, List.flatten_nil,
    List.append_nil, WP.block_append_iff]
  refine (Instructions.mov_ok s .x22 .x19).mono ?_
  rintro a ⟨value, ka⟩
  have im := SegmentSetup.register_ok a .x8 64 (by decide)
  change WP isa (.block (Impl.Argon2.AArch64.Instructions.imm .x8 64)) a _ at im
  refine im.mono ?_
  rintro t ⟨count, kt⟩
  refine ⟨(kt.regs .x22 (by decide)).trans value, count, kt.mem.trans ka.mem,
    fun r hr _ h22 => ?_, kt.sp.trans ka.sp, kt.rd.trans ka.rd, kt.wr.trans ka.wr, ?_⟩
  · have h8 : r ≠ .x8 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (kt.regs r (by simpa only [List.mem_singleton] using h8)).trans
      (ka.regs r (by simpa only [List.mem_singleton] using h22))
  · rw [kt.mem, ka.mem]; exact Frame.refl _ _

theorem finish_ok (v : HPrime.Backend) (s : State) (h : Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (finish v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x19) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      Finished s t := by
  unfold finish
  refine WP.seq ((finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .x24) d := by
    rw [memA, ka.x24]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.stackMinimum hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.finalize_frame _ _ frameU⟩
  have ksu := ka.trans ku
  refine WP.seq ((finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have outW : ∀ i < 64, InRegions w.wr (w.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.x19]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]; exact hi)⟩
  have sepW : (⟨w.gpr .x24 + 768, 64⟩ : Region).Disjoint ⟨w.gpr .x22, 64⟩ := by
    rw [dstW, ← kw.x19]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  have sourceLength : (bytesAt w.mem (w.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.sp.trans ksw.sp, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .x22 = s.gpr .x19 := dstW.trans ksu.x19
    rw [ht.mem]
    conv_lhs => arg 2; rw [← dst]
    have copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .x22)
      (bytesAt w.mem (w.gpr .x24 + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.x24, ku.x24]
    exact digestU
  · have hrax : r ≠ .x8 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .x3 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .x2 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r hrax hrcx hrdx h14).trans (ksw.regs r hr h12 h14)
  · apply Frame.trans (ksw.frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))))
    apply ht.frame.mono
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [dstW, ksu.x19]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end VG.Proof.Argon2.AArch64.Initial
