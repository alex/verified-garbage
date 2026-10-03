import VerifiedGarbage.Proof.Aes.X86.AesNi.Context
import VerifiedGarbage.Proof.Framework.X86.Spill

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP scrR ctrR argR)
open VG.Impl.Aes.X86.AesNi (at_ argOp savedRegs)

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scrP s₀)) s₀.gpr savedRegs

theorem savedRegs_bound : ∀ p ∈ savedRegs, p.2 + 4 ≤ 16 := by decide

structure Setup (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem

structure Start (s₀ s : State) : Prop extends Setup s₀ s where
  eax : s.gpr .eax = schP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = ctrP s₀
  esi : s.gpr .esi = datP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 (nBlk s₀)
  ebp : s.gpr .ebp = scrP s₀
  ebx : s.gpr .ebx = (Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)).extractLsb' 0 32
  saved : Saved s₀ s.mem
  scratchPrefix : s.mem.readW (addr (scrP s₀) 16) 128 =
    (0 : BitVec 32) ++ (s₀.mem.readW ((ctrP s₀).setWidth 64) 128).extractLsb' 0 96
  cf : s.cf = some (decide (nBlk s₀ < 6))
  zf : s.zf = some (decide (nBlk s₀ = 6))

theorem scratch_contains {s : State} (hp : CPre s) {d n : Nat} (h : d + n ≤ 2048) (hn : 0 < n := by decide) :
    (scrR s).Contains (addr (scrP s) d) n := by
  rw [addr_eq (by have hf := hp.fB; omega)]
  exact Offset.contains_base _ h (by omega)

theorem scratch_in {s : State} (hp : CPre s) {d n : Nat} (h : d + n ≤ 2048) (hn : 0 < n := by decide) :
    InRegions s.wr (addr (scrP s) d) n := by
  refine ⟨scrR s, ?_, scratch_contains hp h hn⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false, or_true]

theorem scratch_sep {s : State} (hp : CPre s) {d n e k : Nat}
    (hd : d + n ≤ 2048) (he : e + k ≤ 2048) (h : d + n ≤ e ∨ e + k ≤ d) (hn : 0 < n := by decide) (hk : 0 < k := by decide) :
    Mem.Sep (addr (scrP s) d) n (addr (scrP s) e) k := by
  have hf := hp.fB
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem arg_contains {s : State} (hp : CPre s) {i : Nat} (hi : i < 6) :
    (argR s).Contains (argAddr s i) 4 := by
  have hf := hp.fSp
  change (⟨addr (s.gpr .esp) 4, 24⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4
  rw [addr_eq (by omega), addr_eq (by omega)]
  rw [show (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) =
      ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) + BitVec.ofNat 64 (4 * i) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  exact Offset.contains_base _ (by omega) (by omega)


theorem Setup.setReg {s₀ s : State} (h : Setup s₀ s) (d : Reg) (v : BitVec 32)
    (hd : .esp ≠ d) : Setup s₀ (s.setReg d v) :=
  ⟨by rw [gpr_setReg_of_ne _ _ hd]; exact h.esp,
    (rd_setReg _ _ _).trans h.rd, (wr_setReg _ _ _).trans h.wr,
    by rw [mem_setReg]; exact h.frame⟩


theorem ctr_contains {s : State} (hp : CPre s) {d n : Nat} (h : d + n ≤ 16)
    (hn : 0 < n := by decide) : (ctrR s).Contains (addr (ctrP s) d) n := by
  rw [addr_eq (by have hf := hp.fC; omega)]
  exact Offset.contains_base _ h (by omega)


end VG.Proof.Aes.X86.AesNi
