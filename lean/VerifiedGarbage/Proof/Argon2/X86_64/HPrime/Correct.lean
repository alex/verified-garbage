import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.First
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Restore
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-! # H′: functional correctness of the complete x86-64 program -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (v : Proof.Blake2.X86_64.Backend) (s : State) (pre : localContract.pre s) :
    WP isa (code (hash v)) s fun t => localContract.post s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, dw, ow, sd, so, sw, _, _⟩ := pre
  have work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  have sp : a.gpr .rsp = s.gpr .rsp := ha.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  have dataA : Covers [⟨a.gpr .r12, (a.gpr .r13).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have dwA : (⟨a.gpr .r12, (a.gpr .r13).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  have sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .r12, (a.gpr .r13).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  have inputA : bytesAt a.mem (a.gpr .r12) (a.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .rsi).toNat ≤ 2 ^ 64 by omega) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 56 ≤ 16384))
  have headA : bytesAt a.mem (a.gpr .rbx + 832) 4 = Spec.Argon2.le32 (a.gpr .r15).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  have spaceA : Space a (s.gpr .rcx).toNat := by
    refine ⟨by omega, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  have spaceB := spaceA.keeps kb
  have countB : b.gpr .r15 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have digestB' : (bytesAt b.mem (b.gpr .rbx + 768) 64).take (min (s.gpr .rcx).toNat 64) =
      Spec.Argon2.H (min (s.gpr .rcx).toNat 64)
        (Spec.Argon2.le32 (s.gpr .rcx).toNat ++ bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) := by
    rw [kb.rbx]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok v b (s.gpr .rcx).toNat
    (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  have baseB : b.gpr .rbx = s.gpr .r8 := kb.rbx.trans ha.workspace
  have spB : b.gpr .rsp = s.gpr .rsp := kb.rsp.trans sp
  have dstB : b.gpr .r14 = s.gpr .rdx := (kb.regs _ (by decide)).trans ha.output
  have wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  have frame : Frame [⟨s.gpr .r8, 832⟩, stackR s, outputR s] a.mem x.mem := by
    have fb : Frame [⟨s.gpr .r8, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    have bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    have keep : x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact setupMem_saved s r d hr
  have baseX := hx.rbx.trans baseB
  have spX := hx.rsp.trans spB
  have readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX spX readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    have setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 56 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (code (hash v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have init : (hash v).init.allInstrs (fun i => !loadsMxcsr i) = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (hash v).update.allInstrs (fun i => !loadsMxcsr i) = true := v.updateMxcsr
  have finalize : (hash v).finalize.allInstrs (fun i => !loadsMxcsr i) = true := v.finalizeMxcsr
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.X86_64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.X86_64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.X86_64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.allInstrs]
  rw [init, update, finalize]
  decide +kernel

theorem code_correct (v : Proof.Blake2.X86_64.Backend) (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa (code (hash v)) s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, frame⟩ := code_wp v s pre
  refine ⟨tr, t, run, abiPreserved_of_exec (code_mxcsr v) run ⟨regs, ?_⟩, post⟩
  apply frame.readW (r := retR s) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, retOut, retWork⟩ := pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact retOut
  · exact retWork
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.HPrime
