import VerifiedGarbage.Proof.TripleDes.Arm.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.Arm.Bytes
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def keyKept : List Reg := [.r0, .r1, .r2, .r3]

theorem readKey_ok (s : State) (offset : Nat) (ho : offset + 4 < 4096)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    ∃ s', runBlock isa [.ldr .r4 .r0 offset, .ldr .r5 .r0 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] s = some s' ∧
      s'.gpr .r4 = rev (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset)) 32) ∧
      s'.gpr .r5 = rev (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4))) 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset)) 4 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4))) 4 := by
    simpa only [Nat.mul_one] using hr 1 (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show offset < 4096 from by omega, h0, show offset + 4 < 4096 from ho, ite_true, State.load32,
      gpr_setReg, reduceCtorEq, ite_false, rd_setReg, wr_setReg, h1,
      Option.map_some, mem_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r h4 h5; simp only [gpr_setReg, h4, h5, ite_false]

def loadTail (component : Nat) : List Instr :=
  [imm .r9 0, .dp .add .r8 .r2 (.imm (BitVec.ofNat 32 (128 * component)))]

theorem loadTail_ok (s : State) (component : Nat) (hc : component < 3) :
    ∃ s', runBlock isa (loadTail component) s = some s' ∧
      s'.gpr .r9 = 0 ∧ s'.gpr .r8 = s.gpr .r2 + BitVec.ofNat 32 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → s'.gpr r = s.gpr r) := by
  have henc : encodable (BitVec.ofNat 32 (128 * component)) = true := by
    have finite : ∀ c < 3, encodable (BitVec.ofNat 32 (128 * c)) = true := by decide
    exact finite component hc
  refine ⟨_, by
    simp (config := {decide := true}) only [loadTail, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, henc, ite_true, gpr_setReg,
      ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [gpr_setReg_self]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r h9 h8; simp only [gpr_setReg, h9, h8, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .r10 = ((x >>> 28).setWidth 28).setWidth 32
  d : s'.gpr .r11 = (x.setWidth 28).setWidth 32
  counter : s'.gpr .r9 = 0
  ptr : s'.gpr .r8 = s.gpr .r2 + BitVec.ofNat 32 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset + 4 < 4096)
    (fit : (s.gpr .r0).toNat + offset + 8 ≤ 2 ^ 32)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    WP isa (.block (Impl.TripleDes.Arm.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset))))) component s) := by
  have code : Impl.TripleDes.Arm.Key.load offset component =
      (([.ldr .r4 .r0 offset, .ldr .r5 .r0 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr) ++ loadTail component := by
    simp only [Impl.TripleDes.Arm.Key.load, loadTail, List.append_assoc]
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, mem₁, rd₁, wr₁, reg₁⟩ := readKey_ok s offset ho hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, _, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₁ : packedInput 64 32 (s₁.gpr .r5) (s₁.gpr .r4) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem
        (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset))) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    have ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4)) =
        State.addr (s.gpr .r0 + BitVec.ofNat 32 offset) + 4 := by
      rw [addr_add (by omega_using [fit]), addr_add (by omega_using [fit]),
        ← VG.Offset.add_ofNat_add_ofNat]
      rfl
    rw [ha]
  rw [key₁] at lo₂ hi₂
  obtain ⟨s₃, run₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hc
  refine WP.of_runBlock ⟨s₃, run₃, ⟨(reg₃ .r10 (by decide) (by decide)).trans hi₂,
    (reg₃ .r11 (by decide) (by decide)).trans lo₂, counter₃, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [ptr₃, reg₂ .r2 (by decide +kernel), reg₁ .r2 (by decide) (by decide)]
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .r9 ∧ r ≠ .r8 ∧ r ≠ .r4 ∧ r ≠ .r5 := by decide
    have hcheck : ∀ r ∈ keyKept,
        ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    exact (reg₃ r (unused r hr).1 (unused r hr).2.1).trans
      ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2.2.1 (unused r hr).2.2.2))

end VG.Proof.TripleDes.Arm.Key
