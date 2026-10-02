import VerifiedGarbage.Proof.Aes.X86.AesNi.Counters

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp ctrLoad)

/-- Reload the cached prefix, make any distinct lanes, and restore the public
schedule pointer from immutable arguments. -/
theorem ctrLoad_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (h7 : .xmm7 ∉ regs)
    (hp : InRegions (s.rd ++ s.wr) (s.ea (at_ .ebp 16)) 16)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) :
    WP isa (.block (ctrLoad regs)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] = counterLane
        (s.gpr .ebx + BitVec.ofNat 32 k) (s.mem.readW (s.ea (at_ .ebp 16)) 128)) ∧
      s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 regs.length ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp 0)) 32 ∧
      CounterFrame (.xmm7 :: regs) s s' := by
  rw [ctrLoad, WP.block_append_iff, WP.block_append_iff]
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm7 (s.mem.readW (s.ea (at_ .ebp 16)) 128), by
    simp only [isa, exec, State.load128, hp, ite_true, Option.map_some], ?_⟩
  rw [WP.block_nil_iff]
  refine WP.mono (counters_ok regs _ hnd h7) fun s₁ ⟨hv, hc, hf⟩ => ?_
  have ea : s₁.ea (argOp 0) = s.ea (argOp 0) := by
    rw [ea_mk, ea_mk]
    change addr (s₁.gpr .esp) 4 = addr (s.gpr .esp) 4
    rw [hf.gpr .esp (by decide) (by decide), gpr_setXmm]
  have ha₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.ea (argOp 0)) 4 := by
    rw [ea, hf.rd, hf.wr, rd_setXmm, wr_setXmm]
    exact ha
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg .eax (s₁.mem.readW (s₁.ea (argOp 0)) 32), by
    simp only [isa, exec, readSrc, State.load32, ha₁, ite_true, Option.map_some], ?_⟩
  apply WP.block_nil
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [xmm_setReg, hv k hk, gpr_setXmm, xmm_setXmm_self]
  · rw [gpr_setReg_of_ne _ _ (by decide), hc, gpr_setXmm]
  · rw [gpr_setReg_self, ea, hf.mem, mem_setXmm]
  · refine ⟨fun r h1 h2 => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [gpr_setReg_of_ne _ _ h1, hf.gpr r h1 h2, gpr_setXmm]
    · rw [mem_setReg, hf.mem, mem_setXmm]
    · rw [rd_setReg, hf.rd, rd_setXmm]
    · rw [wr_setReg, hf.wr, wr_setXmm]
    · simp only [List.mem_cons, not_or] at hr
      rw [xmm_setReg, hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

end VG.Proof.Aes.X86.AesNi
