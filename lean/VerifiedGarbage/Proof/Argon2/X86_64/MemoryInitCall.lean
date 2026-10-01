import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit

/-! # A verified H′ call to initialize a memory block -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp (code (HPrime.hash v)) := by
  have all (c : Prog isa) (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi; simp only [h i hi, Bool.not_false]
  have hi := all _ (HPrime.hash_ok v).initNoSp
  have hu := all _ (HPrime.hash_ok v).updateNoSp
  have hf := all _ (HPrime.hash_ok v).finalizeNoSp
  have check : (code (HPrime.hash v)).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    simp only [code, setup, saved, first, chooseLength, init, initArgs, absorbFixed,
      fixedArgs, update, updateArgs, absorbInput, inputArgs, finishInput, finalize,
      finalizeArgs, finishOutput, extendDigest, emitPrefix, copy, copyByte, chain,
      next, copyRemaining, restore, Code.allInstrs]
    rw [hi, hu, hf]
    decide +kernel
  rw [Code.allInstrs_eq, List.all_eq_true] at check
  intro i hi
  simpa only [Bool.not_eq_true'] using check i hi

theorem hPrime_depth (v : Proof.Blake2.X86_64.Backend) : (code (HPrime.hash v)).depth = 2 := by
  simp only [code, first, chooseLength, init, absorbFixed, update, absorbInput,
    finishInput, finalize, finishOutput, extendDigest, emitPrefix, copy, chain,
    next, copyRemaining, Code.depth, (HPrime.hash_ok v).initDepth,
    (HPrime.hash_ok v).updateDepth, (HPrime.hash_ok v).finalizeDepth]
  rfl

structure CallReady (s : State) : Prop where
  input : Covers [⟨s.gpr .rdi, 72⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, 1024⟩] s.wr
  work : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨s.gpr .rdi, 72⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  outputWork : (⟨s.gpr .rdx, 1024⟩ : Region).Disjoint ⟨s.gpr .r8, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 72⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 1024⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r8, 16384⟩

structure Called (s t : State) : Prop where
  digest : bytesAt t.mem (s.gpr .rdx) 1024 = Spec.Argon2.hPrime 1024 (bytesAt s.mem (s.gpr .rdi) 72)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩, below (s.gpr .rsp) 24] s.mem t.mem

theorem hPrime_call_hyps (s : State) (h : CallReady s)
    (inputLength : s.gpr .rsi = 72) (outputLength : s.gpr .rcx = 1024) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 72⟩]
      [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩]) ∧
    Covers [⟨s.gpr .rdi, 72⟩, ⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .r8, 16384⟩] s.wr := by
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have inner := below_callee (s.gpr .rsp) 16
  have ret := below_sub (sp := s.gpr .rsp) (by decide : 8 ≤ 24) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      HPrime.stackR, HPrime.retR, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_rsp, inputLength, outputLength]
    exact ⟨rfl, rfl, by decide, by decide, by decide, h.inputWork, h.outputWork,
      h.stackInput.sub_left inner, h.stackOutput.sub_left inner, h.stackWork.sub_left inner,
      h.stackOutput.sub_left ret, h.stackWork.sub_left ret⟩
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

theorem hPrime_call_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (h : CallReady s) (inputLength : s.gpr .rsi = 72)
    (outputLength : s.gpr .rcx = 1024) :
    WP isa (.call name (code (HPrime.hash v))) s (Called s) := by
  obtain ⟨pre, cover, writes⟩ := hPrime_call_hyps s h inputLength outputLength
  refine WP.call (k := HPrime.localContract) (HPrime.code_correct v) (hPrime_nosp v)
    (by rw [hPrime_depth]; decide) pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, digest⟩
  have inputBytes : bytesAt s.callEntry.mem (s.gpr .rdi) 72 = bytesAt s.mem (s.gpr .rdi) 72 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact Proof.MdStream.X86_64.callEntry_byte s (h.stackInput.sub_left
      (below_sub (by decide) (by decide))) (show (72 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine ⟨?_, regs, rd, wr, ?_⟩
  · change bytesAt u.mem (s.callEntry.gpr .rdx) (s.callEntry.gpr .rcx).toNat =
      Spec.Argon2.hPrime (s.callEntry.gpr .rcx).toNat
        (bytesAt s.callEntry.mem (s.callEntry.gpr .rdi) (s.callEntry.gpr .rsi).toNat) at digest
    rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      memU, inputLength, outputLength,
      show (72 : Addr).toNat = 72 from rfl,
      show (1024 : Addr).toNat = 1024 from rfl, inputBytes] at digest
    exact digest
  · rw [hPrime_depth] at frame
    exact frame

end VG.Proof.Argon2.X86_64.MemoryInit
