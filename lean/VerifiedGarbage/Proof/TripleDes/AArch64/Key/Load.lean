import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.BlockIO
import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def keyKept : List Reg := [.x0, .x1, .x2, .x3, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem readKey_ok (s : State) (offset : Nat) (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8) :
    ∃ s', runBlock isa [.ldr .x .x4 .x0 offset, .rev .x4 .x4] s = some s' ∧
      s'.gpr .x4 = Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [runBlock_cons, exec_ldr_x ho hr, runStep_some, runBlock_nil,
      exec_rev, State.read, BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, BitVec.setWidth_eq]
    exact (decodeBlock_readW s.mem _).symm
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

def loadTail (component : Nat) : List Instr :=
  [.lsr .x .x19 .x5 28, rr .x20 .x5] ++ mask .x20 28 ++
    [imm .x21 0, .addImm .x .x22 .x2 (128 * component)]

theorem loadTail_ok (s : State) (component : Nat) (hc : component < 3) (x : BitVec 56)
    (hx : s.gpr .x5 = x.setWidth 64) :
    ∃ s', runBlock isa (loadTail component) s = some s' ∧
      s'.gpr .x19 = ((x >>> 28).setWidth 28).setWidth 64 ∧
      s'.gpr .x20 = (x.setWidth 28).setWidth 64 ∧ s'.gpr .x21 = 0 ∧
      s'.gpr .x22 = s.gpr .x2 + BitVec.ofNat 64 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [Reg.x19, .x20, .x21, .x22] → s'.gpr r = s.gpr r) := by
  have hb : 128 * component < 4096 := by omega
  refine ⟨_, by
    simp only [loadTail, rr, imm, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, hb,
      show (28 : Nat) < 64 from by decide, show (36 : Nat) < 64 from by decide,
      show (0 : Nat) < 64 from by decide, show (0 : Nat) < 4096 from by decide,
      Nat.mul_zero, ite_true, State.read, BitVec.setWidth_eq, gpr_write,
      BitVec.add_zero, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hx]; exact VG.Proof.TripleDes.split28_upper x
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hx, mask_word _ 28 (by decide) (by decide), BitVec.setWidth_setWidth_of_le x (by decide : 28 ≤ 64)]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .x19 = ((x >>> 28).setWidth 28).setWidth 64
  d : s'.gpr .x20 = (x.setWidth 28).setWidth 64
  counter : s'.gpr .x21 = 0
  ptr : s'.gpr .x22 = s.gpr .x2 + BitVec.ofNat 64 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (Impl.TripleDes.AArch64.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset)))) component s) := by
  have code : Impl.TripleDes.AArch64.Key.load offset component =
      (([.ldr .x .x4 .x0 offset, .rev .x4 .x4] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7) ++ loadTail component := by
    simp only [Impl.TripleDes.AArch64.Key.load, loadTail, List.append_assoc]
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, key₁, mem₁, rd₁, wr₁, reg₁⟩ := readKey_ok s offset ho hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, _, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [key₁] at word₂
  obtain ⟨s₃, run₃, c₃, d₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hc _ word₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃, d₃, counter₃, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · have rdx₂ : s₂.gpr .x2 = s.gpr .x2 :=
      (reg₂ .x2 (by decide +kernel)).trans (reg₁ .x2 (by decide))
    rw [rdx₂] at ptr₃
    exact ptr₃
  · intro r hr
    have unused : ∀ r ∈ keyKept,
        r ∉ [Reg.x19, .x20, .x21, .x22] ∧ r ≠ .x4 := by decide
    have hcheck : ∀ r ∈ keyKept,
        ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    exact (reg₃ r (unused r hr).1).trans ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2))

end VG.Proof.TripleDes.AArch64.Key
