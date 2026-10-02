import VerifiedGarbage.Proof.Aes.X86.AesNi.Setup
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP scrR ctrR argR)
open VG.Impl.Aes.X86.AesNi (at_ argOp savedRegs)

theorem arg_exec {s₀ s : State} (hp : CPre s₀) (hs : Setup s₀ s)
    {i : Nat} (hi : i < 6) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hs.esp]
  have hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
    refine ⟨argR s₀, ?_, arg_contains hp hi⟩
    simp only [hs.rd, hp.rd, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_true, true_or]
  have hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
    hs.frame.readW (arg_contains hp hi)
      (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r; exact hp.aB) (by decide)
  simp only [exec, readSrc, State.load32, he, hin, ite_true, hm, Option.map_some]

def saveMem (s : State) : Mem :=
  (((s.mem.writeW (addr (scrP s) 0) (s.gpr .ebx)).writeW (addr (scrP s) 4)
    (s.gpr .esi)).writeW (addr (scrP s) 8) (s.gpr .edi)).writeW
    (addr (scrP s) 12) (s.gpr .ebp)

theorem saveMem_saved (s : State) (hp : CPre s) : Saved s (saveMem s) := by
  constructor <;> simp only [saveMem]
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · exact Mem.readW_writeW_self32 _ _ _

theorem saveMem_frame (s : State) (hp : CPre s) : Frame [scrR s] s.mem (saveMem s) := by
  have f0 := (Frame.refl [scrR s] s.mem).writeW (v := s.gpr .ebx)
    (List.mem_singleton_self _) (scratch_contains hp (d := 0) (n := 4) (by decide))
  have f4 := f0.writeW (v := s.gpr .esi) (List.mem_singleton_self _)
    (scratch_contains hp (d := 4) (n := 4) (by decide))
  have f8 := f4.writeW (v := s.gpr .edi) (List.mem_singleton_self _)
    (scratch_contains hp (d := 8) (n := 4) (by decide))
  exact f8.writeW (v := s.gpr .ebp) (List.mem_singleton_self _)
    (scratch_contains hp (d := 12) (n := 4) (by decide))

def saveHead : List Instr := [.mov .eax (.mem (argOp 5))] ++
  savedRegs.map (fun (r, d) => .store (at_ .eax d) r)

theorem saveHead_ok (s₀ : State) (hp : CPre s₀) :
    WP isa (.block saveHead) s₀ fun s =>
      Setup s₀ s ∧ s.gpr .eax = scrP s₀ ∧
      (∀ r, r ≠ .eax → s.gpr r = s₀.gpr r) ∧ s.mem = saveMem s₀ := by
  have hs : Setup s₀ s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  have h0 := scratch_in hp (d := 0) (n := 4) (by decide)
  have h4 := scratch_in hp (d := 4) (n := 4) (by decide)
  have h8 := scratch_in hp (d := 8) (n := 4) (by decide)
  have h12 := scratch_in hp (d := 12) (n := 4) (by decide)
  dsimp only [addr, scrP] at h0 h4 h8 h12
  apply WP.of_runBlock
  simp only [saveHead, List.cons_append, List.nil_append]
  rw [runBlock_cons, arg_exec hp hs (i := 5) (by decide) .eax, runStep_some]
  simp (config := {decide := true}) only [savedRegs, List.map_cons, List.map_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea, at_,
    gpr_setReg, mem_setReg, wr_setReg, ite_true, ite_false, h0, h4, h8, h12,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, saveMem_frame _ hp⟩
  · intro r hr
    simp only [hr, ite_false]


structure Loaded (s₀ s : State) : Prop extends Setup s₀ s where
  eax : s.gpr .eax = schP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = ctrP s₀
  esi : s.gpr .esi = datP s₀
  edi : s.gpr .edi = arg s₀ 4
  ebp : s.gpr .ebp = scrP s₀

def loadArgs : List Instr :=
  [.mov .ebp (.reg .eax), .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
   .mov .edx (.mem (argOp 2)), .mov .esi (.mem (argOp 3)), .mov .edi (.mem (argOp 4))]

theorem loadArgs_ok {s₀ s : State} (hp : CPre s₀) (hs : Setup s₀ s)
    (hb : s.gpr .eax = scrP s₀) :
    WP isa (.block loadArgs) s fun s' => Loaded s₀ s' ∧ s'.mem = s.mem := by
  unfold loadArgs
  rw [WP.block_cons_iff]
  let s₁ := s.setReg .ebp (s.gpr .eax)
  refine ⟨s₁, rfl, ?_⟩
  have hs₁ := hs.setReg .ebp (s.gpr .eax) (by decide)
  rw [WP.block_cons_iff]
  let s₂ := s₁.setReg .eax (arg s₀ 0)
  refine ⟨s₂, arg_exec hp hs₁ (i := 0) (by decide) .eax, ?_⟩
  have hs₂ := hs₁.setReg .eax (arg s₀ 0) (by decide)
  rw [WP.block_cons_iff]
  let s₃ := s₂.setReg .ecx (arg s₀ 1)
  refine ⟨s₃, arg_exec hp hs₂ (i := 1) (by decide) .ecx, ?_⟩
  have hs₃ := hs₂.setReg .ecx (arg s₀ 1) (by decide)
  rw [WP.block_cons_iff]
  let s₄ := s₃.setReg .edx (arg s₀ 2)
  refine ⟨s₄, arg_exec hp hs₃ (i := 2) (by decide) .edx, ?_⟩
  have hs₄ := hs₃.setReg .edx (arg s₀ 2) (by decide)
  rw [WP.block_cons_iff]
  let s₅ := s₄.setReg .esi (arg s₀ 3)
  refine ⟨s₅, arg_exec hp hs₄ (i := 3) (by decide) .esi, ?_⟩
  have hs₅ := hs₄.setReg .esi (arg s₀ 3) (by decide)
  rw [WP.block_cons_iff]
  let s₆ := s₅.setReg .edi (arg s₀ 4)
  refine ⟨s₆, arg_exec hp hs₅ (i := 4) (by decide) .edi, ?_⟩
  refine WP.block_nil ⟨⟨hs₅.setReg .edi (arg s₀ 4) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  all_goals
    dsimp only [s₆, s₅, s₄, s₃, s₂, s₁]
    simp (config := {decide := true}) only [gpr_setReg, ite_true, ite_false]
  exact hb


theorem Saved.writePrefix {s₀ : State} {m : Mem} (hp : CPre s₀) (h : Saved s₀ m)
    (v : BitVec 128) : Saved s₀ (m.writeW (addr (scrP s₀) 16) v) := by
  constructor
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide)]
    exact h.ebx
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide)]
    exact h.esi
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide)]
    exact h.edi
  · rw [Mem.readW_writeW_sep (scratch_sep hp (by decide) (by decide) (by decide)) (by decide)]
    exact h.ebp

def counterSetup : List Instr :=
  [.mov .ebx (.mem (at_ .edx 12)), .bswap .ebx,
   .movdquLoad .xmm7 (at_ .edx 0), .xop (.shift .pslldq .xmm7 4),
   .xop (.shift .psrldq .xmm7 4), .movdquStore (at_ .ebp 16) .xmm7,
   .alu .cmp .edi (.imm 6)]

theorem counterSetup_ok {s₀ s : State} (hp : CPre s₀) (hs : Loaded s₀ s)
    (saved : Saved s₀ s.mem) : WP isa (.block counterSetup) s (Start s₀) := by
  have hc0 : InRegions (s.rd ++ s.wr) (addr (ctrP s₀) 0) 16 := by
    refine inRegions_wr ⟨ctrR s₀, ?_, ctr_contains hp (by decide)⟩
    simp only [hs.wr, hp.wr, List.mem_cons, true_or]
  have hc12 : InRegions (s.rd ++ s.wr) (addr (ctrP s₀) 12) 4 := by
    refine inRegions_wr ⟨ctrR s₀, ?_, ctr_contains hp (by decide)⟩
    simp only [hs.wr, hp.wr, List.mem_cons, true_or]
  have hb16 : InRegions s.wr (addr (scrP s₀) 16) 16 := by
    rw [hs.wr]; exact scratch_in hp (by decide)
  have ctr0 : s.mem.readW (addr (ctrP s₀) 0) 128 =
      s₀.mem.readW ((ctrP s₀).setWidth 64) 128 := by
    rw [VG.Proof.Aes.X86.addr_zero]
    exact hs.frame.readW (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hp.dCB) (by decide)
  have ctr12 : s.mem.readW (addr (ctrP s₀) 12) 32 =
      s₀.mem.readW (addr (ctrP s₀) 12) 32 :=
    hs.frame.readW (ctr_contains hp (by decide))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hp.dCB) (by decide)
  dsimp only [addr] at hc0 hc12 hb16 ctr0 ctr12
  apply WP.of_runBlock
  simp (config := {decide := true}) only [counterSetup, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load32, State.load128, State.store128, XOp.exec, execAlu,
    State.ea, at_, gpr_setReg, gpr_setXmm, xmm_setReg, xmm_setXmm,
    mem_setReg, mem_setXmm, rd_setReg, wr_setReg, wr_setXmm,
    ite_true, ite_false, hs.edx, hs.ebp, hc0, hc12, hb16,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.esp
    · simp only [rd_arithFlags, rd_setXmm, rd_setReg]; exact hs.rd
    · simp only [wr_arithFlags]; exact hs.wr
    · change Frame [scrR s₀] s₀.mem (s.mem.writeW (addr (scrP s₀) 16)
        (XShiftOp.eval .psrldq (XShiftOp.eval .pslldq (s.mem.readW (addr (ctrP s₀) 0) 128) 4) 4))
      exact hs.frame.writeW (List.mem_singleton_self _) _ (scratch_contains hp (by decide))
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.eax
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.ecx
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.edx
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.esi
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]
    rw [hs.edi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.ebp
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_true]
    rw [ctr12]; exact VG.Proof.Aes.X86.icb_lo _ hp.fC
  · exact saved.writePrefix hp _
  · change (s.mem.writeW (addr (scrP s₀) 16)
        (XShiftOp.eval .psrldq (XShiftOp.eval .pslldq (s.mem.readW (addr (ctrP s₀) 0) 128) 4) 4)).readW
        (addr (scrP s₀) 16) 128 = _
    rw [Mem.readW_writeW_self _ _ 16 _ (by decide), cache_prefix]
    dsimp only [addr]
    rw [ctr0]
  · simp only [cf_arithFlags, hs.edi]
    rfl
  · simp only [zf_arithFlags, hs.edi]
    apply congrArg some
    simp only [beq_eq_decide, BitVec.sub_eq_iff_eq_add]
    apply decide_eq_decide.mpr
    constructor
    · intro h; exact congrArg BitVec.toNat h
    · intro h; exact BitVec.eq_of_toNat_eq h

theorem prologue_eq : Impl.Aes.X86.AesNi.prologue = saveHead ++ loadArgs ++ counterSetup := rfl

theorem prologue_ok (s₀ : State) (hp : CPre s₀) :
    WP isa (.block Impl.Aes.X86.AesNi.prologue) s₀ (Start s₀) := by
  rw [prologue_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveHead_ok s₀ hp) fun s₁ ⟨h₁, ptr₁, _, mem₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadArgs_ok hp h₁ ptr₁) fun s₂ ⟨h₂, mem₂⟩ => ?_
  apply counterSetup_ok hp h₂
  rw [mem₂, mem₁]; exact saveMem_saved _ hp

end VG.Proof.Aes.X86.AesNi
