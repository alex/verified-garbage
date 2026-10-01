import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd

theorem KeyReady.arithFlags {s₀ s : State} (hs : KeyReady s₀ s)
    (v : BitVec 32) (c o : Bool) : KeyReady s₀ (VG.X86.arithFlags s v c o) :=
  ⟨⟨hs.esp, hs.mem, hs.rd, hs.wr⟩, hs.eax, hs.ecx, hs.edx, hs.callee⟩

theorem keyCmp32_ok {s₀ s : State} (hs : KeyReady s₀ s) :
    WP isa (.block [.alu .cmp .ecx (.imm 32)]) s fun s' =>
      KeyReady s₀ s' ∧ s'.zf = some (decide (arg s₀ 1 = 32#32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hs.arithFlags _ _ _, ?_⟩
  rw [zf_arithFlags, hs.ecx]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  rw [show (0 : BitVec 32) + 32 = 32#32 by decide]

end VG.Proof.Aes.X86.AesNi
