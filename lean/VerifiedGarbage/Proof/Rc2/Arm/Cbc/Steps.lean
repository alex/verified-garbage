import VerifiedGarbage.Proof.Rc2.Arm.Cbc.PairIO
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

def temps : List Reg := [.r12, .r3, .r6, .r7]

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat)
    (srcSep : src ≠ .r12) (dstSep : dst ≠ .r12 ∧ dst ≠ .r3)
    (srcFit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (dstFit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 b) 8)
    (ha : a + 4 < 4096 := by decide) (hb : b + 4 < 4096 := by decide) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.copy64 src dst a b)) s (fun s' =>
      Keep temps {s with
        mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b)
          (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 64)} s') := by
  change WP isa (.block (([.ldr .r12 src a, .ldr .r3 src (a + 4)] : List Instr) ++
    [.str .r12 dst b, .str .r3 dst (b + 4)])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .r12 .r3 src a (by decide) srcSep ha srcFit readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg dst (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using dstSep)
  obtain ⟨s₂, run₂, keep₂⟩ := storePair_ok s₁ .r12 .r3 dst b hb
    (by rw [ptr]; exact dstFit) (by rw [keep₁.wr, ptr]; exact writable)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · intro r hr
    exact (keep₂.reg r (by simp)).trans (keep₁.reg r (by
      intro h; exact hr (by simp only [temps, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)))
  · rw [keep₂.mem, ptr, hi₁, lo₁, keep₁.mem, ← Offset.add_ofNat_add_ofNat, ← read64_pair]
  · exact keep₂.rd.trans keep₁.rd
  · exact keep₂.wr.trans keep₁.wr

theorem xorPair_ok (s : State) :
    ∃ s', runBlock isa [.dp .eor .r12 .r12 (.reg .r6), .dp .eor .r3 .r3 (.reg .r7)] s = some s' ∧
      s'.gpr .r12 = s.gpr .r12 ^^^ s.gpr .r6 ∧ s'.gpr .r3 = s.gpr .r3 ^^^ s.gpr .r7 ∧
      Keep [.r12, .r3] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some, runBlock_nil, gpr_setReg]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

theorem xor64_ok (s : State) (dst iv : Reg)
    (dstSep : dst ∉ temps) (ivSep : iv ∉ temps)
    (dstFit : (s.gpr dst).toNat + 8 ≤ 2 ^ 32) (ivFit : (s.gpr iv).toNat + 8 ≤ 2 ^ 32)
    (readDst : InRegions (s.rd ++ s.wr) (State.addr (s.gpr dst)) 8)
    (readIv : InRegions (s.rd ++ s.wr) (State.addr (s.gpr iv)) 8)
    (writable : InRegions s.wr (State.addr (s.gpr dst)) 8) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.xor64 dst iv)) s (fun s' =>
      Keep temps {s with
        mem := s.mem.writeW (State.addr (s.gpr dst))
          (s.mem.readW (State.addr (s.gpr dst)) 64 ^^^ s.mem.readW (State.addr (s.gpr iv)) 64)} s') := by
  have ds : dst ≠ .r12 ∧ dst ≠ .r3 ∧ dst ≠ .r6 ∧ dst ≠ .r7 := by simpa [temps] using dstSep
  have vs : iv ≠ .r12 ∧ iv ≠ .r3 ∧ iv ≠ .r6 ∧ iv ≠ .r7 := by simpa [temps] using ivSep
  change WP isa (.block (([.ldr .r12 dst 0, .ldr .r3 dst 4] : List Instr) ++
    (([.ldr .r6 iv 0, .ldr .r7 iv 4] : List Instr) ++
      (([.dp .eor .r12 .r12 (.reg .r6), .dp .eor .r3 .r3 (.reg .r7)] : List Instr) ++
        [.str .r12 dst 0, .str .r3 dst 4])))) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, keep₁⟩ := loadPair_ok s .r12 .r3 dst 0 (by decide) ds.1 (by decide)
    (by simpa using dstFit) (by simpa using readDst)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have iv₁ := keep₁.reg iv (by simp [vs.1, vs.2.1])
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, lo₂, hi₂, keep₂⟩ := loadPair_ok s₁ .r6 .r7 iv 0 (by decide) vs.2.2.1 (by decide)
    (by rw [iv₁]; simpa using ivFit) (by rw [keep₁.rd, keep₁.wr, iv₁]; simpa using readIv)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, lo₃, hi₃, keep₃⟩ := xorPair_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : Keep temps s s₃ :=
    ((keep₁.weaken (by simp [temps])).trans (keep₂.weaken (by simp [temps]))).trans
      (keep₃.weaken (by simp [temps]))
  have ptr := keep.reg dst dstSep
  obtain ⟨s₄, run₄, keep₄⟩ := storePair_ok s₃ .r12 .r3 dst 0 (by decide)
    (by rw [ptr]; simpa using dstFit) (by rw [keep.wr, ptr]; simpa using writable)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  refine ⟨fun r hr => (keep₄.reg r (by simp)).trans (keep.reg r hr), ?_,
    keep₄.rd.trans keep.rd, keep₄.wr.trans keep.wr⟩
  rw [keep₄.mem, keep.mem, ptr, BitVec.add_zero, hi₃, lo₃, lo₂, hi₂,
    keep₂.reg .r12 (by decide), keep₂.reg .r3 (by decide), lo₁, hi₁, keep₁.mem, iv₁]
  simp only [Nat.zero_add, BitVec.add_zero]
  rw [pair_xor, ← read64_pair, ← read64_pair]

def zeroCount (s : State) : Option Bool := some s.z

theorem eval_zeroCount (s : State) : eval .eq s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.Arm.Cbc.advance s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      zeroCount s' = some ((s.gpr .r5 - 1) == 0) ∧ Keep [.r1, .r5] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.Arm.Cbc.advance, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, ite_true, gpr_setReg, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg_self]
  · change some ((s.gpr .r5 - 1 - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_subFlags, gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

end VG.Proof.Rc2.Arm.Cbc
