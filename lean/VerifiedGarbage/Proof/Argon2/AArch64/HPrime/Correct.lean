import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.First
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Restore
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-! # H′: functional correctness of the complete ARM64 program -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (v : Backend) (s : State) (pre : localContract.pre s) :
    WP isa (code v.hash) s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := pre
  have work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  have sp := ha.sp
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  have dataA : Covers [⟨a.gpr .x20, (a.gpr .x21).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have dwA : (⟨a.gpr .x20, (a.gpr .x21).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  have swA : (below (a.sp) 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  have sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x20, (a.gpr .x21).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  have inputA : bytesAt a.mem (a.gpr .x20) (a.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .x1).toNat ≤ 2 ^ 64 by omega) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  have headA : bytesAt a.mem (a.gpr .x24 + 832) 4 = Spec.Argon2.le32 (a.gpr .x23).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  have spaceA : Space a (s.gpr .x3).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA (by rw [sp]; exact hsp) workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  have spaceB := spaceA.keeps kb
  have countB : b.gpr .x23 = BitVec.ofNat 64 (s.gpr .x3).toNat := by
    rw [kb.regs _ (by decide) (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have digestB' : (bytesAt b.mem (b.gpr .x24 + 768) 64).take (min (s.gpr .x3).toNat 64) =
      Spec.Argon2.H (min (s.gpr .x3).toNat 64)
        (Spec.Argon2.le32 (s.gpr .x3).toNat ++ bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) := by
    rw [kb.x24]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok v b (s.gpr .x3).toNat
    (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  have baseB : b.gpr .x24 = s.gpr .x4 := kb.x24.trans ha.workspace
  have spB : b.sp = s.sp := kb.sp.trans sp
  have dstB : b.gpr .x22 = s.gpr .x2 := (kb.regs _ (by decide) (by decide)).trans ha.output
  have wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  have frame : Frame [⟨s.gpr .x4, 832⟩, stackR s, outputR s] a.mem x.mem := by
    have fb : Frame [⟨s.gpr .x4, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    have bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    have keep : x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .x4 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact setupMem_saved s r d hr
  have baseX := hx.x24.trans baseB
  have spX := hx.sp.trans spB
  have readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX (by
    intro r hr
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h30 : r ≠ .x30 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h22 : r ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h23 : r ≠ .x23 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [hx.regs r hp h30 h22 h23, kb.regs r hp h30]
    exact ha.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) h22 h23) readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    have setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 64 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_keepsV (v : Backend) : (code v.hash).allInstrs keepsV = true := by
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.AArch64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.AArch64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.AArch64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.allInstrs]
  rw [v.initV, v.updateV, v.finalizeV]
  decide +kernel

theorem code_correct (v : Backend) (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa (code v.hash) s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, _⟩ := code_wp v s pre
  exact ⟨tr, t, run, ⟨regs, VG.AArch64.Exec.sp run,
    VG.AArch64.Exec.preservedV run (code_keepsV v)⟩, post⟩

end VG.Proof.Argon2.AArch64.HPrime
