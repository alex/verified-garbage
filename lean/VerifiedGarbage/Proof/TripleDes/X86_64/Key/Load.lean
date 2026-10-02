import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.X86_64.BlockIO
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (offset_nat)

theorem readKey_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (memOp .rdi offset)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 offset)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, State.ea, memOp, offset_nat, hr, ite_true, Option.map_some,
      gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg_self]
    exact (decodeBlock_readW s.mem _).symm
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

def loadTail (component : Nat) : List Instr :=
  [rr .r12 .rbx, .shift .shr .r12 28, rr .r13 .rbx,
    .alu .and .r13 (.imm 0x0fffffff), imm .r14 0, rr .r15 .rdx,
    .alu .add .r15 (.imm (BitVec.ofNat 32 (128 * component)))]

theorem componentOffset_word : ∀ c < 3,
    (BitVec.ofNat 32 (128 * c)).signExtend 64 = BitVec.ofNat 64 (128 * c) := by decide

theorem loadTail_ok (s : State) (component : Nat) (hc : component < 3) (x : BitVec 56)
    (hx : s.gpr .rbx = x.setWidth 64) :
    ∃ s', runBlock isa (loadTail component) s = some s' ∧
      s'.gpr .r12 = ((x >>> 28).setWidth 28).setWidth 64 ∧
      s'.gpr .r13 = (x.setWidth 28).setWidth 64 ∧ s'.gpr .r14 = 0 ∧
      s'.gpr .r15 = s.gpr .rdx + BitVec.ofNat 64 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [Reg.r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [loadTail, rr, imm, runBlock_cons, runStep_some, exec,
      execShift, readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.split28_upper x
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx]
    change x.setWidth 64 &&& 0x0fffffff = _
    rw [VG.Proof.TripleDes.mask28]
    exact congrArg (BitVec.setWidth 64) (by simp only [BitVec.setWidth_setWidth_of_le x (by decide : 28 ≤ 64)])
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [componentOffset_word component hc]
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
  · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
  · simp only [wr_setReg, wr_arithFlags, wr_setFlags]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .r12 = ((x >>> 28).setWidth 28).setWidth 64
  d : s'.gpr .r13 = (x.setWidth 28).setWidth 64
  counter : s'.gpr .r14 = 0
  ptr : s'.gpr .r15 = s.gpr .rdx + BitVec.ofNat 64 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (Impl.TripleDes.X86_64.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 offset)))) component s) := by
  have code : Impl.TripleDes.X86_64.Key.load offset component =
      (([.mov .rax (.mem (memOp .rdi offset)), .bswap .rax] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp) ++ loadTail component := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, key₁, mem₁, rd₁, wr₁, reg₁⟩ := readKey_ok s offset hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [key₁] at word₂
  obtain ⟨s₃, run₃, c₃, d₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hc _ word₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃, d₃, counter₃, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · have rdx₂ : s₂.gpr .rdx = s.gpr .rdx :=
      (reg₂ .rdx (by decide +kernel)).trans (reg₁ .rdx (by decide))
    rw [rdx₂] at ptr₃
    exact ptr₃
  · intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp],
        r ∉ [Reg.r12, .r13, .r14, .r15] ∧ r ≠ .rax := by decide
    have hcheck : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp],
        ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true := by decide +kernel
    exact (reg₃ r (unused r hr).1).trans ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2))

end VG.Proof.TripleDes.X86_64.Key
