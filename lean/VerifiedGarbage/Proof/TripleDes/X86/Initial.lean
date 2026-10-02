import VerifiedGarbage.Impl.TripleDes.X86.Block
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

def dataArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 2) 32

def readHead : List Instr :=
  [.mov .edx (.mem (memOp .esp 8)), .mov .edi (.mem (memOp .edx 0)),
    .mov .esi (.mem (memOp .edx 4)), .bswap .edi, .bswap .esi]

theorem readHead_ok (s : State)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (dataArg s) i) 4) :
    ∃ s', runBlock isa readHead s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (wordAddr (dataArg s) 0) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (wordAddr (dataArg s) 1) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  simp only [wordAddr, addr, dataArg] at harg h0 h1
  refine ⟨_, by
    simp only [readHead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.ea, memOp, harg, h0, h1, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx) s = some s' ∧
      s'.gpr .eax = (Spec.TripleDes.permute Spec.TripleDes.ip
        (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.ip (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .esi .edi .eax .ebx (instrs initialPermutation.lit) initialPermutation_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx = instrs initialPermutation.lit :=
    congrArg instrs initialPermutation.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

structure InitialPost (x : BitVec 64) (s s' : State) : Prop where
  l : s'.gpr .esi = (x >>> 32).setWidth 32
  r : s'.gpr .edi = x.setWidth 32
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp

theorem blockLoad_ok (s : State)
    (fit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (dataArg s) i) 4) :
    WP isa (.block blockLoad) s (InitialPost (Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (dataArg s))))) s) := by
  have code : blockLoad = (readHead ++
      permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx) ++
      [rr .esi .ebx, rr .edi .eax] := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := readHead_ok s harg hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := ip_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have input : packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (dataArg s))) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    rw [show wordAddr (dataArg s) 0 = addr32 (dataArg s) from by simp [wordAddr, addr, addr32],
      show wordAddr (dataArg s) 1 = addr32 (dataArg s) + 4 from addr_eq (by omega)]
  rw [input] at lo₂ hi₂
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some,
      gpr_setReg, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, mem₂.trans keep₁.mem, rd₂.trans keep₁.rd, wr₂.trans keep₁.wr,
    ?_, ?_⟩
  · exact hi₂
  · exact lo₂
  · exact (reg₂ .ebp (by decide +kernel)).trans (keep₁.reg .ebp (by decide))
  · exact sp₂.trans (keep₁.reg .esp (by decide))

end VG.Proof.TripleDes.X86
