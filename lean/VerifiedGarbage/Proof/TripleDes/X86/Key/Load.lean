import VerifiedGarbage.Proof.TripleDes.X86.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.TripleDes.X86.RoundStep
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

def keyArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 1) 32

def scheduleArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 3) 32

def keyAddr (s : State) (offset : Nat) : BitVec 64 :=
  (keyArg s + BitVec.ofNat 32 offset).setWidth 64

theorem readKey_ok (s : State) (offset : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadHead offset) s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (keyAddr s offset) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (keyAddr s (offset + 4)) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, keyAddr, keyArg, wordAddr, addr] at h0
  simp only [Nat.mul_one, keyAddr, keyArg, wordAddr, addr] at h1
  simp only [wordAddr, addr] at harg
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.loadHead, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.load32, State.ea, memOp, harg, h0, h1, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

def loadMem (s : State) (component : Nat) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 5) (0 : BitVec 32)).writeW
    (wordAddr (s.gpr .ebp) 4) (scheduleArg s + BitVec.ofNat 32 (128 * component))

theorem loadTail_ok (s : State) (component : Nat) (hok : Ok sboxCfg s)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadTail component) s = some s' ∧
      s'.gpr .esi = s.gpr .ebx ∧ s'.gpr .edi = s.gpr .eax ∧
      s'.mem = loadMem s component ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  simp only [wordAddr, addr, sboxCfg] at hw4 hw5
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.loadTail, rr, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load32, State.store32, State.ea,
      memOp, hw4, hw5, hr, ite_true, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r ha hd hs hi
    simp only [gpr_setReg, gpr_arithFlags, ha, hd, hs, hi, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .esi = ((x >>> 28).setWidth 28).setWidth 32
  d : s'.gpr .edi = (x.setWidth 28).setWidth 32
  counter : roundCount s' = 0
  ptr : roundKeyPtr s' = scheduleArg s + BitVec.ofNat 32 (128 * component)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  base : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : Frame [workRegion s] s.mem s'.mem

theorem loadMem_frame (s : State) (component : Nat)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Frame [workRegion s] s.mem (loadMem s component) := by
  have h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h5).writeW
    (List.mem_singleton_self _) _ h4

theorem load_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (fit : (keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (keyAddr s offset)))) component s) := by
  rw [Impl.TripleDes.X86.Key.load, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := readKey_ok s offset (harg 1 (by decide)) hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₁ : packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (keyAddr s offset)) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    have ha : keyAddr s (offset + 4) = keyAddr s offset + 4 := by
      change VG.Proof.Rc2.X86.addr32 (keyArg s + BitVec.ofNat 32 (offset + 4)) =
        VG.Proof.Rc2.X86.addr32 (keyArg s + BitVec.ofNat 32 offset) + 4
      rw [VG.Proof.Rc2.X86.addr_add (by omega), VG.Proof.Rc2.X86.addr_add (by omega)]
      rw [← VG.Offset.add_ofNat_add_ofNat]
      rfl
    rw [ha]
  rw [key₁] at lo₂ hi₂
  have base₂ : s₂.gpr .ebp = s.gpr .ebp :=
    (reg₂ .ebp (by decide +kernel)).trans (keep₁.reg .ebp (by decide))
  have sp₂' : s₂.gpr .esp = s.gpr .esp := sp₂.trans (keep₁.reg .esp (by decide))
  have hok₂ : Ok sboxCfg s₂ := hok.congr base₂ base₂ (rd₂.trans keep₁.rd) (wr₂.trans keep₁.wr)
  have hr₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 3) 4 := by
    rw [sp₂', rd₂, wr₂, keep₁.rd, keep₁.wr]
    exact harg 3 (by decide)
  obtain ⟨s₃, run₃, c₃, d₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hok₂ hr₂
  have base₃ : s₃.gpr .ebp = s.gpr .ebp := (reg₃ .ebp (by decide) (by decide)
    (by decide) (by decide)).trans base₂
  have sp₃ : s₃.gpr .esp = s.gpr .esp := (reg₃ .esp (by decide) (by decide)
    (by decide) (by decide)).trans sp₂'
  have sched₂ : scheduleArg s₂ = scheduleArg s := by
    unfold scheduleArg
    rw [sp₂', mem₂, keep₁.mem]
  have hm : s₃.mem = loadMem s component := by
    rw [mem₃, loadMem, base₂, sched₂, mem₂, keep₁.mem]
    rfl
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃.trans hi₂, d₃.trans lo₂, ?_, ?_,
    rd₃.trans (rd₂.trans keep₁.rd), wr₃.trans (wr₂.trans keep₁.wr), base₃, sp₃, ?_⟩⟩
  · unfold roundCount
    rw [base₃, hm, loadMem, Mem.readW_writeW_sep (counter_ptr_sep s hok.fit) (by decide),
      Mem.readW_writeW_self32]
  · unfold roundKeyPtr
    rw [base₃, hm, loadMem, Mem.readW_writeW_self32]
  · rw [hm]
    exact loadMem_frame s component hok.fit

end VG.Proof.TripleDes.X86.Key
