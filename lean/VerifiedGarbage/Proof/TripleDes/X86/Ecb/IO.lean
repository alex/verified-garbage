import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Loop

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

theorem subtract_zero (x : BitVec 32) : x - (0 : BitVec 32) = x := by bv_omega

def savedMem (s : State) : Mem :=
  (((s.mem.writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 512) (s.gpr .ebp)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 516) (s.gpr .ebx)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 520) (s.gpr .esi)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 524) (s.gpr .edi)

theorem save_ok (s : State) (fit : (s.gpr .eax).toNat + 1024 ≤ 2 ^ 32)
    (hw : ∀ k ∈ [512, 516, 520, 524], InRegions s.wr (addr (s.gpr .eax) k) 4) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  have h0 := hw 512 (by decide)
  have h1 := hw 516 (by decide)
  have h2 := hw 520 (by decide)
  have h3 := hw 524 (by decide)
  simp only [addr] at h0 h1 h2 h3
  refine ⟨_, by
    change runBlock isa [.store (memOp .eax 512) .ebp, .store (memOp .eax 516) .ebx,
      .store (memOp .eax 520) .esi, .store (memOp .eax 524) .edi] s = _
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea,
      memOp, h0, h1, h2, h3, ite_true]
    rfl, ?_⟩
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl⟩
  change (((s.mem.writeW (addr (s.gpr .eax) 512) (s.gpr .ebp)).writeW
    (addr (s.gpr .eax) 516) (s.gpr .ebx)).writeW
    (addr (s.gpr .eax) 520) (s.gpr .esi)).writeW
    (addr (s.gpr .eax) 524) (s.gpr .edi) = savedMem s
  unfold savedMem
  rw [addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 512 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 516 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 520 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 524 < 2 ^ 32)]
  rfl

theorem savedMem_frame (s : State) :
    Frame [⟨addr32 (s.gpr .eax), 1024⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide) (by decide))

theorem setup_ok (s : State)
    (hr : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.setup s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .ebx = arg s 0 ∧ s'.gpr .esi = arg s 1 ∧
      s'.gpr .edi = arg s 2 ∧ isa.eval .e s' = some (arg s 2 == 0) ∧
      Keep [.ebp, .ebx, .esi, .edi] s s' := by
  have h0 := hr 1 (by decide)
  have h1 := hr 2 (by decide)
  have h2 := hr 3 (by decide)
  simp only [wordAddr, addr] at h0 h1 h2
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Ecb.setup, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load32, State.ea, memOp, h0, h1, h2, ite_true,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact (argument_word s 0).symm
  · exact (argument_word s 1).symm
  · exact (argument_word s 2).symm
  · change some (((s.mem.readW (wordAddr (s.gpr .esp) 3) 32) - (0 : BitVec 32)) == (0 : BitVec 32)) = _
    rw [← argument_word s 2]
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (subtract_zero (arg s 2))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem restore_ok (original s : State)
    (hr : ∀ k ∈ [512, 516, 520, 524], InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) k) 4)
    (hv : ∀ i < 4, s.mem.readW (addr (s.gpr .ebp) (512 + 4 * i)) 32 = original.gpr (savedReg i)) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.restore s = some s' ∧
      (∀ r ∈ savedRegs, s'.gpr r = original.gpr r) ∧
      Keep (.eax :: savedRegs) s s' := by
  have h0 := hr 512 (by decide)
  have h1 := hr 516 (by decide)
  have h2 := hr 520 (by decide)
  have h3 := hr 524 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  simp only [addr] at h0 h1 h2 h3
  refine ⟨_, by
    change runBlock isa [rr .eax .ebp, .mov .ebp (.mem (memOp .eax 512)),
      .mov .ebx (.mem (memOp .eax 516)), .mov .esi (.mem (memOp .eax 520)),
      .mov .edi (.mem (memOp .eax 524))] s = _
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.ea, memOp, h0, h1, h2, h3, ite_true, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_⟩
  · intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.TripleDes.X86.Ecb
