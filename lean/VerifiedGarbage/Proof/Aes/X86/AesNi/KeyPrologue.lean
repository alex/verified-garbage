import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (EPre keyP keyLen ekSchP ekArgR)

structure KeySetup (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

structure KeyReady (s₀ s : State) : Prop extends KeySetup s₀ s where
  eax : s.gpr .eax = keyP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = ekSchP s₀
  callee : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r

structure KeyStart (s₀ s : State) : Prop extends KeyReady s₀ s where
  zf : s.zf = some (decide (arg s₀ 1 = 24#32))

theorem KeySetup.setReg {s₀ s : State} (h : KeySetup s₀ s) (d : Reg) (v : BitVec 32)
    (hd : .esp ≠ d) : KeySetup s₀ (s.setReg d v) :=
  ⟨by rw [gpr_setReg_of_ne _ _ hd]; exact h.esp,
    (mem_setReg _ _ _).trans h.mem, (rd_setReg _ _ _).trans h.rd,
    (wr_setReg _ _ _).trans h.wr⟩

theorem key_arg_contains {s : State} (hp : EPre s) {i : Nat} (hi : i < 4) :
    (ekArgR s).Contains (argAddr s i) 4 := by
  have hf := hp.fSp
  change (⟨addr (s.gpr .esp) 4, 16⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4
  rw [addr_eq (by omega), addr_eq (by omega)]
  rw [show (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) =
      ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) + BitVec.ofNat 64 (4 * i) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  exact Offset.contains_base _ (by omega) (by omega)

theorem key_arg_exec {s₀ s : State} (hp : EPre s₀) (hs : KeySetup s₀ s)
    {i : Nat} (hi : i < 4) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hs.esp]
  have hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
    refine ⟨ekArgR s₀, ?_, key_arg_contains hp hi⟩
    simp only [hs.rd, hp.rd, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_true, true_or]
  simp only [exec, readSrc, State.load32, he, hin, ite_true, hs.mem, arg, Option.map_some]

def keyHead : List Instr :=
  [.mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
    .mov .edx (.mem (argOp 2)), .alu .cmp .ecx (.imm 24)]

theorem keyHead_ok (s₀ : State) (hp : EPre s₀) :
    WP isa (.block keyHead) s₀ (KeyStart s₀) := by
  have h₀ : KeySetup s₀ s₀ := ⟨rfl, rfl, rfl, rfl⟩
  have h₁ := h₀.setReg .eax (arg s₀ 0) (by decide)
  have h₂ := h₁.setReg .ecx (arg s₀ 1) (by decide)
  apply WP.of_runBlock
  simp only [keyHead]
  rw [runBlock_cons, key_arg_exec hp h₀ (by decide), runStep_some,
    runBlock_cons, key_arg_exec hp h₁ (by decide), runStep_some,
    runBlock_cons, key_arg_exec hp h₂ (by decide), runStep_some]
  simp (config := {decide := true}) only [runBlock_cons, exec, execAlu, readSrc,
    gpr_setReg, Option.bind_some, ite_true, ite_false, runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · simp only [mem_arithFlags, mem_setReg]
  · simp only [rd_arithFlags, rd_setReg]
  · simp only [wr_arithFlags, wr_setReg]
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · intro r h1 h2 h3
    simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ite_false]
  · rw [zf_arithFlags]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
    rw [show (0 : BitVec 32) + 24 = 24#32 by decide]

end VG.Proof.Aes.X86.AesNi
