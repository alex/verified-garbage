import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall

/-! A verified H′ call initializes one 1024-byte memory block. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)
open VG.Spec.Blake2 (bytesAt)

structure CallReady (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  input : Covers [⟨s.gpr .x0, 72⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .x2, 1024⟩] s.wr
  work : (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .x0, 72⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  outputWork : (⟨s.gpr .x2, 1024⟩ : Region).Disjoint ⟨s.gpr .x4, 16384⟩
  stackInput : (below s.sp 16).Disjoint ⟨s.gpr .x0, 72⟩
  stackOutput : (below s.sp 16).Disjoint ⟨s.gpr .x2, 1024⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x4, 16384⟩

structure Called (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .x2) 1024 = Spec.Argon2.hPrime 1024 (bytesAt s.mem (s.gpr .x0) 72)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩, below s.sp 16] s.mem t.mem

theorem hPrime_call_hyps (s : State) (h : CallReady s)
    (inputLength : s.gpr .x1 = 72) (outputLength : s.gpr .x3 = 1024) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .x0, 72⟩]
      [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩]) ∧
    Covers [⟨s.gpr .x0, 72⟩, ⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .x2, 1024⟩, ⟨s.gpr .x4, 16384⟩] s.wr := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp,
      g _ (by decide : Reg.x0 ∉ linkRegs), g _ (by decide : Reg.x1 ∉ linkRegs),
      g _ (by decide : Reg.x2 ∉ linkRegs), g _ (by decide : Reg.x3 ∉ linkRegs),
      g _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp,
      inputLength, outputLength]
    exact ⟨rfl, rfl, by decide, by decide, by decide, h.stackMinimum,
      h.inputWork, h.outputWork, h.stackInput, h.stackOutput, h.stackWork⟩
  · intro p n hp
    rcases hp with ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · exact ⟨_, List.mem_append_right _ h.work, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, h.work, hc⟩

theorem hPrime_depth (v : HPrime.Backend) : (code v.hash).aarch64Depth = 1 := by
  simp only [code, Impl.Argon2.AArch64.HPrime.first,
    Impl.Argon2.AArch64.HPrime.chooseLength, Impl.Argon2.AArch64.HPrime.init,
    Impl.Argon2.AArch64.HPrime.absorbFixed, Impl.Argon2.AArch64.HPrime.update,
    Impl.Argon2.AArch64.HPrime.absorbInput, Impl.Argon2.AArch64.HPrime.finishInput,
    Impl.Argon2.AArch64.HPrime.finalize, Impl.Argon2.AArch64.HPrime.finishOutput,
    Impl.Argon2.AArch64.HPrime.extendDigest, Impl.Argon2.AArch64.HPrime.emitPrefix,
    Impl.Argon2.AArch64.HPrime.copy, Impl.Argon2.AArch64.HPrime.chain,
    Impl.Argon2.AArch64.HPrime.next, Impl.Argon2.AArch64.HPrime.copyRemaining,
    Code.aarch64Depth, v.ok.initDepth, v.ok.updateDepth, v.ok.finalizeDepth]
  rfl

theorem hPrime_call_ok (v : HPrime.Backend) (name : String)
    (s : State) (h : CallReady s) (inputLength : s.gpr .x1 = 72)
    (outputLength : s.gpr .x3 = 1024) :
    WP isa (.call name (code v.hash)) s (Called s) := by
  obtain ⟨pre, cover, writes⟩ := hPrime_call_hyps s h inputLength outputLength
  refine WP.callF (k := HPrime.localContract) (HPrime.code_correct v) pre cover writes ?_
    (by rw [hPrime_depth]; decide)
  intro t rd wr sp frame regs digest
  change bytesAt t.mem (s.callEntry.gpr .x2) (s.callEntry.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.callEntry.gpr .x3).toNat
      (bytesAt s.mem (s.callEntry.gpr .x0) (s.callEntry.gpr .x1).toNat) at digest
  rw [State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), inputLength, outputLength,
    show (72 : Addr).toNat = 72 from rfl,
    show (1024 : Addr).toNat = 1024 from rfl] at digest
  refine ⟨digest, ?_, sp, rd, wr, ?_⟩
  · intro r hr
    have preserved : r ∈ VG.AArch64.preserved ∧ r ≠ .x30 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact regs r preserved.1 preserved.2
  · simpa only [hPrime_depth, Nat.mul_one, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.MemoryInit
