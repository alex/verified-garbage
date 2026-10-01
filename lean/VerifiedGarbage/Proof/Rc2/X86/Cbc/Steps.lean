import VerifiedGarbage.Proof.Rc2.X86.Cbc.PairIO
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.X86.KeySteps

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

def temps : List Reg := [.eax, .edx]

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat)
    (srcSep : src ≠ .eax) (dstSep : dst ≠ .eax ∧ dst ≠ .edx)
    (srcFit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (dstFit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr src) + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (addr32 (s.gpr dst) + BitVec.ofNat 64 b) 8) :
    WP isa (.block (Impl.Rc2.X86.Cbc.copy64 src dst a b)) s (fun s' =>
      Keep temps {s with
        mem := s.mem.writeW (addr32 (s.gpr dst) + BitVec.ofNat 64 b)
          (s.mem.readW (addr32 (s.gpr src) + BitVec.ofNat 64 a) 64)} s') := by
  change WP isa (.block (([.mov .eax (.mem (memOp src a)), .mov .edx (.mem (memOp src (a + 4)))] : List Instr) ++
    [.store (memOp dst b) .eax, .store (memOp dst (b + 4)) .edx])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .eax .edx src a (by decide) srcSep srcFit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
  obtain ⟨s₂, run₂, keep₂⟩ := storePair_ok s₁ .eax .edx dst b
    (by rw [ptr]; exact dstFit) (by rw [keep₁.wr, ptr]; exact writable)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · intro r hr
    exact (keep₂.reg r (by simp)).trans (keep₁.reg r hr)
  · rw [keep₂.mem, ptr, hi₁, lo₁, keep₁.mem, ← Offset.add_ofNat_add_ofNat, ← read64_pair]
  · exact keep₂.rd.trans keep₁.rd
  · exact keep₂.wr.trans keep₁.wr

theorem exec_xorMem (s : State) (t n : Reg) (off : Nat)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (addr32 (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.alu .xor t (.mem (memOp n off))) s =
      some ((arithFlags s (s.gpr t ^^^ s.mem.readW (addr32 (s.gpr n) + BitVec.ofNat 64 off) 32) false false).setReg t
          (s.gpr t ^^^ s.mem.readW (addr32 (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  simp only [exec, execAlu, readSrc, memOp, State.ea]
  rw [← addr32, addr_add fit]
  simp only [State.load32, h, ite_true, Option.bind_some]

theorem xorPair_ok (s : State) (iv : Reg) (ivSep : iv ≠ .eax ∧ iv ≠ .edx)
    (fit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (addr32 (s.gpr iv)) 8) :
    ∃ s', runBlock isa [.alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4))] s = some s' ∧
      s'.gpr .eax = s.gpr .eax ^^^ s.mem.readW (addr32 (s.gpr iv)) 32 ∧
      s'.gpr .edx = s.gpr .edx ^^^ s.mem.readW (addr32 (s.gpr iv) + BitVec.ofNat 64 4) 32 ∧
      Keep temps s s' := by
  obtain ⟨rd0, rd4⟩ := halves rd
  rw [runBlock_cons, exec_xorMem s .eax iv 0 (by omega) (by simpa only [BitVec.add_zero] using rd0), runStep_some]
  rw [runBlock_cons, exec_xorMem _ .edx iv 4
    (by simp only [gpr_setReg, gpr_arithFlags, ivSep.1, ite_false]; omega)
    (by simpa only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, gpr_setReg, gpr_arithFlags, ivSep.1, ite_false] using rd4),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, BitVec.add_zero]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, ivSep.1, mem_setReg, mem_arithFlags]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem xor64_ok (s : State) (dst iv : Reg)
    (dstSep : dst ∉ temps) (ivSep : iv ∉ temps)
    (dstFit : (s.gpr dst).toNat + 8 ≤ 2 ^ 32) (ivFit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (readDst : InRegions (s.rd ++ s.wr) (addr32 (s.gpr dst)) 8)
    (readIv : InRegions (s.rd ++ s.wr) (addr32 (s.gpr iv)) 8)
    (writable : InRegions s.wr (addr32 (s.gpr dst)) 8) :
    WP isa (.block (Impl.Rc2.X86.Cbc.xor64 dst iv)) s (fun s' =>
      Keep temps {s with mem := (s.mem.writeW (addr32 (s.gpr dst))
        (s.mem.readW (addr32 (s.gpr dst)) 64 ^^^ s.mem.readW (addr32 (s.gpr iv)) 64))} s') := by
  have ds : dst ≠ .eax ∧ dst ≠ .edx := by simpa only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep
  have vs : iv ≠ .eax ∧ iv ≠ .edx := by simpa only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or] using ivSep
  change WP isa (.block (([.mov .eax (.mem (memOp dst 0)), .mov .edx (.mem (memOp dst 4))] : List Instr) ++
    (([.alu .xor .eax (.mem (memOp iv 0)), .alu .xor .edx (.mem (memOp iv 4))] : List Instr) ++
      [.store (memOp dst 0) .eax, .store (memOp dst 4) .edx]))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .eax .edx dst 0 (by decide) ds.1
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have iv₁ := keep₁.reg iv ivSep
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := xorPair_ok s₁ iv vs
    (by rw [iv₁]; exact ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; exact readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have keep : Keep temps s s₂ := keep₁.trans keep₂
  have ptr := keep.reg dst dstSep
  obtain ⟨s₃, run₃, keep₃⟩ := storePair_ok s₂ .eax .edx dst 0
    (by rw [ptr]; simpa using dstFit) (by rw [keep.wr, ptr]; simpa using writable)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨fun r hr => (keep₃.reg r (by simp)).trans (keep.reg r hr), ?_, keep₃.rd.trans keep.rd, keep₃.wr.trans keep.wr⟩
  rw [keep₃.mem, keep.mem, ptr, BitVec.add_zero, hi₂, lo₂, hi₁, lo₁, keep₁.mem, iv₁]
  simp only [Nat.zero_add, BitVec.add_zero]
  rw [pair_xor, ← read64_pair, ← read64_pair]

def zeroCount (s : State) : Option Bool := s.zf

theorem eval_zeroCount (s : State) : eval .e s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86.Cbc.advance s = some s' ∧
      s'.gpr .esi = s.gpr .esi + 8 ∧ s'.gpr .edi = s.gpr .edi - 1 ∧
      s'.zf = some ((s.gpr .edi - 1) == 0) ∧ Keep [.esi, .edi] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.X86.Cbc.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86.Cbc
